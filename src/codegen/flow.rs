//! Control flow: blocks and statements, `if`, the loop primitive, jumps,
//! `match`, and `try`/`catch`/`finally` (and `defer`) by LSB §4.3's
//! canonical lowering.

use alloc::vec::Vec;

use bytecode_lang::{Const, Inst, IntTy, Label, Reg, ValType};
use hir_lang::{
    BindMode, BinderId, Block, Expr, ExprId, ItemKind, List, NodeRef, OpKind, Pat, PatId, Res,
    Stmt, StmtId,
};
use intern_lang::Lookup;

use super::{Dst, Gen, Leave, Rel, Step, Task, Val};
use crate::error::{CompileError, Unsupported};
use crate::func::{Exit, Fin, Target, TryState};
use crate::unit::Slot;

impl<L: Lookup> Gen<'_, '_, L> {
    // ------------------------------------------------------------ blocks

    pub(crate) fn block(&mut self, e: ExprId, b: Block, dst: Dst) -> Result<(), CompileError> {
        let hir = self.cx.hir;
        let stmts = hir.list(b.stmts);
        let defers = stmts
            .iter()
            .filter(|&&s| matches!(hir.stmt(s), Stmt::Defer(_)))
            .count();
        if b.label.is_none() && defers == 0 {
            self.tasks.push(Task::ScopeClose);
            match b.tail {
                Some(t) => self.tasks.push(Task::Expr(t, dst)),
                None => self.nil_task(dst),
            }
            for &s in stmts.iter().rev() {
                self.tasks.push(Task::Stmt(s));
            }
            self.tasks.push(Task::ScopeOpen);
            return Ok(());
        }
        // A labeled block (a `break` target) or one with `defer`s: its value
        // goes to one register.
        let r = match dst {
            Dst::Reg(r) => r,
            _ => self.fx.temp(ValType::Dyn),
        };
        let end = self.label();
        let target = b.label.map(|label| {
            let id = self.fx.next_target;
            self.fx.next_target += 1;
            Target {
                label: Some(label),
                is_loop: false,
                brk: end,
                cont: end,
                result: r,
                fin_depth: self.fx.fins.len(),
                id,
            }
        });
        // Pushed in reverse.
        match dst {
            Dst::Any | Dst::Temp => self.tasks.push(Task::Push(Val {
                reg: r,
                rel: Rel::Temp,
            })),
            Dst::Discard => self.tasks.push(Task::Free(r)),
            Dst::Reg(_) => {}
        }
        self.tasks.push(Task::ScopeClose);
        if target.is_some() {
            self.tasks.push(Task::Bind(end));
            self.tasks.push(Task::TargetPop);
        }
        for _ in 0..defers {
            self.tasks.push(Task::TryEnd);
            self.tasks.push(Task::TryBodyEnd);
        }
        match b.tail {
            Some(t) => self.tasks.push(Task::Expr(t, Dst::Reg(r))),
            None => self.tasks.push(Task::Emit(Inst::LoadNil { dst: r })),
        }
        for &s in stmts.iter().rev() {
            match *hir.stmt(s) {
                Stmt::Defer(d) => self.tasks.push(Task::Step(Step::DeferBegin {
                    s,
                    body: d,
                    result: r,
                })),
                _ => self.tasks.push(Task::Stmt(s)),
            }
        }
        if let Some(t) = target {
            self.tasks.push(Task::TargetPush(t));
        }
        self.tasks.push(Task::ScopeOpen);
        let _ = e;
        Ok(())
    }

    /// Schedules a `nil` delivered to `dst`.
    pub(crate) fn nil_task(&mut self, dst: Dst) {
        match dst {
            Dst::Discard => {}
            Dst::Reg(r) => self.tasks.push(Task::Emit(Inst::LoadNil { dst: r })),
            Dst::Any | Dst::Temp => {
                let r = self.fx.temp(ValType::Dyn);
                self.tasks.push(Task::Push(Val {
                    reg: r,
                    rel: Rel::Temp,
                }));
                self.tasks.push(Task::Emit(Inst::LoadNil { dst: r }));
            }
        }
    }

    pub(crate) fn stmt(&mut self, s: StmtId) -> Result<(), CompileError> {
        let node = NodeRef::Stmt(s);
        self.at(node);
        let hir = self.cx.hir;
        match *hir.stmt(s) {
            Stmt::Expr(e) => self.tasks.push(Task::Expr(e, Dst::Discard)),
            Stmt::Item(_) => {}
            Stmt::Let {
                pat, init, else_, ..
            } => match *hir.pat(pat) {
                Pat::Bind {
                    binder,
                    mode: BindMode::Value,
                    sub: None,
                } => {
                    let slot = self.alloc_binder(binder);
                    match (slot, init) {
                        (Slot::Reg(r), Some(init)) => {
                            let t = self.store_expr_tasks(init, r);
                            self.sched(t);
                        }
                        (Slot::Reg(r), None) => self.emit(Inst::LoadNil { dst: r }),
                        (Slot::Cell(c), Some(init)) => {
                            let dup = self.needs_dup(init);
                            self.sched([
                                Task::Expr(init, Dst::Any),
                                Task::NewCell { cell: c, dup },
                            ]);
                        }
                        (Slot::Cell(c), None) => {
                            let n = self.fx.temp(ValType::Dyn);
                            self.emit(Inst::LoadNil { dst: n });
                            self.emit(Inst::NewRef { dst: c, src: n });
                            self.fx.release(n);
                        }
                        (Slot::Global(_) | Slot::GlobalCell(_) | Slot::Place(_), _) => {}
                    }
                }
                Pat::Wild => {
                    if let Some(init) = init {
                        self.tasks.push(Task::Expr(init, Dst::Discard));
                    }
                }
                _ => match init {
                    Some(init) => self.sched([
                        Task::Expr(init, Dst::Temp),
                        Task::LetPat { pat, else_, node },
                    ]),
                    None => {
                        // A declaration: every binder starts as nil.
                        let r = self.fx.temp(ValType::Dyn);
                        self.emit(Inst::LoadNil { dst: r });
                        self.vals.push(Val {
                            reg: r,
                            rel: Rel::Temp,
                        });
                        self.let_pat(pat, else_, node);
                    }
                },
            },
            Stmt::Static { binder, init, .. } => {
                self.cx.statics += 1;
                let name = alloc::format!("<static#{}>", self.cx.statics);
                let global = self.cx.mb.global(&name, ValType::Dyn, true, None);
                if self.cx.is_cell(binder) {
                    // Shared by reference: the global holds a cell, made the
                    // first time the statement runs; the variable is that
                    // cell, loaded once the statement ran.
                    let slot = self.alloc_binder(binder);
                    let k = self.cx.mb.constant(Const::Bool(false));
                    let mut fname = name.clone();
                    fname.push_str("$init");
                    let flag = self.cx.mb.global(&fname, ValType::Bool, true, Some(k));
                    let b = self.fx.temp(ValType::Bool);
                    let done = self.label();
                    self.emit(Inst::GetGlobal {
                        dst: b,
                        global: flag,
                    });
                    self.jump_on(b, done, true);
                    self.fx.release(b);
                    let init_task = match init {
                        Some(init) => Task::Expr(init, Dst::Any),
                        None => {
                            let r = self.fx.temp(ValType::Dyn);
                            self.emit(Inst::LoadNil { dst: r });
                            Task::Push(Val {
                                reg: r,
                                rel: Rel::Temp,
                            })
                        }
                    };
                    let load = match slot {
                        Slot::Cell(c) => Task::Emit(Inst::GetGlobal { dst: c, global }),
                        _ => Task::Emit(Inst::Nop {}),
                    };
                    self.sched([
                        init_task,
                        Task::Step(Step::StaticCell { global, flag, done }),
                        load,
                    ]);
                    return Ok(());
                }
                self.cx.set_slot(binder, Slot::Global(global));
                if let Some(init) = init {
                    let k = self.cx.mb.constant(Const::Bool(false));
                    let mut fname = name.clone();
                    fname.push_str("$init");
                    let flag = self.cx.mb.global(&fname, ValType::Bool, true, Some(k));
                    let b = self.fx.temp(ValType::Bool);
                    let done = self.label();
                    self.emit(Inst::GetGlobal {
                        dst: b,
                        global: flag,
                    });
                    self.jump_on(b, done, true);
                    self.fx.release(b);
                    self.sched([
                        Task::Expr(init, Dst::Any),
                        Task::Step(Step::StaticInit { global, flag, done }),
                    ]);
                }
            }
            Stmt::Global { binder, path } => {
                let pnode = NodeRef::Path(path);
                let p = hir.path(path);
                let item = match p.res {
                    Res::Def(_) => self.cx.local_item(p.res, pnode)?,
                    Res::Unresolved | Res::Err => {
                        return Err(CompileError::Unresolved {
                            node: pnode,
                            span: self.cx.span(pnode),
                        });
                    }
                    _ => return Err(self.cx.unsupported(Unsupported::TypeDirected, pnode)),
                };
                let g = item
                    .filter(|&i| matches!(hir.item(i).kind, ItemKind::Global { .. }))
                    .and_then(|i| self.cx.global_slot(i));
                match g {
                    // A global shared by reference: the variable is its cell.
                    Some(Slot::GlobalCell(gl)) => match self.alloc_binder(binder) {
                        Slot::Cell(c) => self.emit(Inst::GetGlobal { dst: c, global: gl }),
                        _ => self.cx.set_slot(binder, Slot::GlobalCell(gl)),
                    },
                    Some(g) => self.cx.set_slot(binder, g),
                    None => {
                        return Err(CompileError::NotAssignable {
                            node: pnode,
                            span: self.cx.span(pnode),
                        });
                    }
                }
            }
            Stmt::Defer(d) => {
                // Only reached outside a block's statement list (never, for
                // valid HIR); run it immediately.
                self.tasks.push(Task::Expr(d, Dst::Discard));
            }
            Stmt::Err => {
                return Err(CompileError::ErrorNode {
                    node,
                    span: self.cx.span(node),
                });
            }
        }
        Ok(())
    }

    /// Destructures the popped value of a `let`; on no match, runs `else_`
    /// or raises `TypeError` at the statement.
    pub(crate) fn let_pat(&mut self, pat: PatId, else_: Option<ExprId>, node: NodeRef) {
        let v = self.pop();
        let fail = self.label();
        let ok = self.label();
        let mut tail: Vec<Task> = alloc::vec![
            Task::Pat {
                pat,
                v: v.reg,
                fail
            },
            Task::Jump(ok),
            Task::Bind(fail),
        ];
        match else_ {
            Some(e) => tail.push(Task::Expr(e, Dst::Discard)),
            None => {
                tail.push(Task::At(node));
                tail.push(Task::Step(Step::RaiseTypeError));
            }
        }
        tail.push(Task::Bind(ok));
        tail.push(Task::Push(v));
        tail.push(Task::Deliver {
            dst: Dst::Discard,
            dup: false,
        });
        for t in tail.into_iter().rev() {
            self.tasks.push(t);
        }
    }

    // ------------------------------------------------------------ conditions

    /// Jumps to `label` when `e` is truthy (`when`) or falsy (`!when`).
    pub(crate) fn cond(&mut self, e: ExprId, label: Label, when: bool) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        let hir = self.cx.hir;
        match *hir.expr(e) {
            Expr::Op { op, args }
                if matches!(
                    op.kind,
                    OpKind::Eq | OpKind::Ne | OpKind::Lt | OpKind::Le | OpKind::Gt | OpKind::Ge
                ) && hir.list(args).len() == 2 =>
            {
                let list = hir.list(args);
                let (a, b) = (list.first().copied(), list.get(1).copied());
                if let (Some(a), Some(b)) = (a, b) {
                    let d = self.operand_dst(list, 0);
                    self.sched([
                        Task::Expr(a, d),
                        Task::Expr(b, Dst::Any),
                        Task::CondCmp {
                            op: op.kind,
                            label,
                            when,
                            node,
                        },
                    ]);
                }
            }
            Expr::Lit(hir_lang::Lit::Bool(v)) => {
                if v == when {
                    self.tasks.push(Task::Jump(label));
                }
            }
            _ => self.sched([
                Task::Expr(e, Dst::Any),
                Task::CondTruthy { label, when, node },
            ]),
        }
        Ok(())
    }

    pub(crate) fn if_expr(&mut self, cond: ExprId, then: ExprId, else_: Option<ExprId>, dst: Dst) {
        let result = self.result_of(dst);
        let rdst = result.map_or(Dst::Discard, Dst::Reg);
        let lelse = self.label();
        let lend = self.label();
        let mut ts: Vec<Task> = alloc::vec![
            Task::Cond {
                e: cond,
                label: lelse,
                when: false,
            },
            Task::Expr(then, rdst),
            Task::Jump(lend),
            Task::Bind(lelse),
        ];
        match (else_, result) {
            (Some(x), _) => ts.push(Task::Expr(x, rdst)),
            (None, Some(r)) => ts.push(Task::Emit(Inst::LoadNil { dst: r })),
            (None, None) => {}
        }
        ts.push(Task::Bind(lend));
        if let (Some(r), Dst::Any | Dst::Temp) = (result, dst) {
            ts.push(Task::Push(Val {
                reg: r,
                rel: Rel::Temp,
            }));
        }
        for t in ts.into_iter().rev() {
            self.tasks.push(t);
        }
    }

    // ------------------------------------------------------------ loops, jumps

    pub(crate) fn loop_expr(
        &mut self,
        e: ExprId,
        label: Option<BinderId>,
        body: ExprId,
        step: Option<ExprId>,
        dst: Dst,
    ) {
        let node = NodeRef::Expr(e);
        let r = match dst {
            Dst::Reg(r) => r,
            _ => self.fx.temp(ValType::Dyn),
        };
        self.emit(Inst::LoadNil { dst: r });
        let (top, cont, brk) = (self.label(), self.label(), self.label());
        let id = self.fx.next_target;
        self.fx.next_target += 1;
        let t = Target {
            label,
            is_loop: true,
            brk,
            cont,
            result: r,
            fin_depth: self.fx.fins.len(),
            id,
        };
        let mut ts: Vec<Task> = alloc::vec![
            Task::TargetPush(t),
            Task::Bind(top),
            Task::Expr(body, Dst::Discard),
            Task::Bind(cont),
        ];
        if let Some(s) = step {
            ts.push(Task::Expr(s, Dst::Discard));
        }
        // Fuel is charged once per iteration (LSB V-CF6).
        ts.push(Task::At(node));
        ts.push(Task::Emit(Inst::Safepoint {}));
        ts.push(Task::Jump(top));
        ts.push(Task::TargetPop);
        ts.push(Task::Bind(brk));
        match dst {
            Dst::Any | Dst::Temp => ts.push(Task::Push(Val {
                reg: r,
                rel: Rel::Temp,
            })),
            Dst::Discard => ts.push(Task::Free(r)),
            Dst::Reg(_) => {}
        }
        for t in ts.into_iter().rev() {
            self.tasks.push(t);
        }
    }

    /// The labeled target, or the innermost loop.
    fn find_target(&self, label: Option<BinderId>) -> Option<Target> {
        self.fx
            .targets
            .iter()
            .rev()
            .find(|t| match label {
                Some(l) => t.label == Some(l),
                None => t.is_loop,
            })
            .copied()
    }

    pub(crate) fn break_expr(
        &mut self,
        e: ExprId,
        label: Option<BinderId>,
        value: Option<ExprId>,
        dst: Dst,
    ) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        let Some(t) = self.find_target(label) else {
            return Err(CompileError::ErrorNode {
                node,
                span: self.cx.span(node),
            });
        };
        let leave = Leave::Break(t.id);
        self.dummy_after(dst);
        match value {
            Some(v) => {
                let dup = self.needs_dup(v);
                self.sched([
                    Task::Expr(v, Dst::Any),
                    Task::Deliver { dst: Dst::Any, dup },
                    Task::Leave {
                        leave,
                        value: true,
                        node,
                    },
                ]);
            }
            None => self.tasks.push(Task::Leave {
                leave,
                value: false,
                node,
            }),
        }
        Ok(())
    }

    pub(crate) fn continue_expr(
        &mut self,
        e: ExprId,
        label: Option<BinderId>,
        dst: Dst,
    ) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        let Some(t) = self.find_target(label).filter(|t| t.is_loop) else {
            return Err(CompileError::ErrorNode {
                node,
                span: self.cx.span(node),
            });
        };
        self.dummy_after(dst);
        self.tasks.push(Task::Leave {
            leave: Leave::Continue(t.id),
            value: false,
            node,
        });
        Ok(())
    }

    pub(crate) fn return_expr(&mut self, e: ExprId, value: Option<ExprId>, dst: Dst) {
        let node = NodeRef::Expr(e);
        self.dummy_after(dst);
        match value {
            Some(v) => {
                // A `finally` between here and the frame's end may still
                // write the variable: then even a local must be copied.
                let dup = if self.fx.fins.is_empty() {
                    self.ret_dup(v)
                } else {
                    self.needs_dup(v)
                };
                self.sched([
                    Task::Expr(v, Dst::Any),
                    Task::Deliver { dst: Dst::Any, dup },
                    Task::Leave {
                        leave: Leave::Return,
                        value: true,
                        node,
                    },
                ]);
            }
            None => self.tasks.push(Task::Leave {
                leave: Leave::Return,
                value: false,
                node,
            }),
        }
    }

    /// Schedules the (unreachable) value of a jump expression.
    fn dummy_after(&mut self, dst: Dst) {
        if matches!(dst, Dst::Any | Dst::Temp) {
            let r = self.fx.temp(ValType::Dyn);
            self.tasks.push(Task::Push(Val {
                reg: r,
                rel: Rel::Temp,
            }));
        }
    }

    // ------------------------------------------------------------ match

    pub(crate) fn match_arms(
        &mut self,
        e: ExprId,
        result: Option<Reg>,
        dst: Dst,
    ) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        let hir = self.cx.hir;
        let Expr::Match { arms, .. } = *hir.expr(e) else {
            return Ok(());
        };
        let s = self.pop();
        let rdst = result.map_or(Dst::Discard, Dst::Reg);
        let end = self.label();
        let mut ts: Vec<Task> = Vec::new();
        for arm in hir.list(arms) {
            let next = self.label();
            ts.push(Task::ScopeOpen);
            ts.push(Task::Pat {
                pat: arm.pat,
                v: s.reg,
                fail: next,
            });
            if let Some(g) = arm.guard {
                ts.push(Task::Cond {
                    e: g,
                    label: next,
                    when: false,
                });
            }
            ts.push(Task::Expr(arm.body, rdst));
            ts.push(Task::At(node));
            ts.push(Task::Jump(end));
            ts.push(Task::Bind(next));
            ts.push(Task::ScopeClose);
        }
        // No arm matched: `NoMatch` (E0200) with the scrutinee as payload
        // (HIR §8.10).
        ts.push(Task::At(node));
        ts.push(Task::Push(Val {
            reg: s.reg,
            rel: Rel::Keep,
        }));
        ts.push(Task::Step(Step::RaiseNoMatch));
        ts.push(Task::Bind(end));
        ts.push(Task::Push(s));
        ts.push(Task::Deliver {
            dst: Dst::Discard,
            dup: false,
        });
        if let (Some(r), Dst::Any | Dst::Temp) = (result, dst) {
            ts.push(Task::Push(Val {
                reg: r,
                rel: Rel::Temp,
            }));
        }
        for t in ts.into_iter().rev() {
            self.tasks.push(t);
        }
        Ok(())
    }

    // ------------------------------------------------------------ try

    pub(crate) fn try_expr(
        &mut self,
        e: ExprId,
        body: ExprId,
        catches: List<hir_lang::Arm>,
        finally: Option<ExprId>,
        dst: Dst,
    ) {
        let node = NodeRef::Expr(e);
        let result = self.result_of(dst);
        let has_catch = !self.cx.hir.list(catches).is_empty();
        self.try_begin(node, result, has_catch, finally);
        let rdst = result.map_or(Dst::Discard, Dst::Reg);
        let mut ts: Vec<Task> = alloc::vec![Task::Expr(body, rdst), Task::TryBodyEnd, Task::TryEnd];
        if let (Some(r), Dst::Any | Dst::Temp) = (result, dst) {
            ts.push(Task::Push(Val {
                reg: r,
                rel: Rel::Temp,
            }));
        }
        for t in ts.into_iter().rev() {
            self.tasks.push(t);
        }
    }

    /// Opens a `try` (or a `defer`, a `try` with only a `finally`): the
    /// completion registers and the region starts.
    pub(crate) fn try_begin(
        &mut self,
        node: NodeRef,
        result: Option<Reg>,
        has_catch: bool,
        finally: Option<ExprId>,
    ) {
        let e = match node {
            NodeRef::Expr(e) => Some(e),
            _ => None,
        };
        let fin = finally.map(|_| {
            let kind = self.fx.temp(ValType::I8);
            let value = self.fx.temp(ValType::Dyn);
            let entry = self.label();
            self.fx.fins.push(Fin {
                kind,
                value,
                entry,
                exits: Vec::new(),
                node,
            });
            let start = self.label();
            self.bind(start);
            let pc = self.fx.f.pc();
            (start, pc, self.label(), self.label())
        });
        let catch = has_catch.then(|| {
            let start = self.label();
            self.bind(start);
            let pc = self.fx.f.pc();
            let c = self.fx.temp(ValType::Dyn);
            (start, pc, self.label(), self.label(), c)
        });
        let end = self.label();
        self.fx.tries.push(TryState {
            e,
            node,
            result,
            catch,
            fin,
            finally,
            end,
        });
    }

    /// The protected body ended normally.
    pub(crate) fn try_body_end(&mut self) -> Result<(), CompileError> {
        let Some(st) = self.fx.tries.last().copied() else {
            return Ok(());
        };
        self.at(st.node);
        self.try_normal_exit();
        if let Some((_, _, end, handler, c)) = st.catch {
            self.bind(end);
            self.bind(handler);
            // The catch arms: the first whose pattern (and guard) matches
            // handles the error; none does, rethrow.
            let Some(e) = st.e else {
                return Ok(());
            };
            let Expr::Try { catches, .. } = *self.cx.hir.expr(e) else {
                return Ok(());
            };
            let rdst = st.result.map_or(Dst::Discard, Dst::Reg);
            let mut ts: Vec<Task> = Vec::new();
            for arm in self.cx.hir.list(catches) {
                let next = self.label();
                ts.push(Task::ScopeOpen);
                ts.push(Task::Pat {
                    pat: arm.pat,
                    v: c,
                    fail: next,
                });
                if let Some(g) = arm.guard {
                    ts.push(Task::Cond {
                        e: g,
                        label: next,
                        when: false,
                    });
                }
                ts.push(Task::Expr(arm.body, rdst));
                ts.push(Task::At(st.node));
                ts.push(Task::TryNormalExit);
                ts.push(Task::Bind(next));
                ts.push(Task::ScopeClose);
            }
            ts.push(Task::At(st.node));
            ts.push(Task::TryRethrow);
            for t in ts.into_iter().rev() {
                self.tasks.push(t);
            }
        }
        Ok(())
    }

    /// Leaves the innermost `try`'s body or a catch arm normally: completion
    /// kind 0 and the `finally`, or straight to the end.
    pub(crate) fn try_normal_exit(&mut self) {
        let Some(st) = self.fx.tries.last().copied() else {
            return;
        };
        match (st.fin, self.fx.fins.last()) {
            (Some(_), Some(fin)) => {
                let (kind, entry) = (fin.kind, fin.entry);
                self.emit(Inst::LoadInt {
                    dst: kind,
                    val: 0,
                    ty: IntTy::I8,
                });
                self.jmp(entry);
            }
            _ => self.jmp(st.end),
        }
    }

    pub(crate) fn try_rethrow(&mut self) {
        if let Some((_, _, _, _, c)) = self.fx.tries.last().and_then(|s| s.catch) {
            self.emit(Inst::Throw { src: c });
        }
    }

    /// Closes the innermost `try`: registers its regions (the catch region
    /// nested in, so listed before, the `finally` region) and emits the
    /// single `finally` copy.
    pub(crate) fn try_end(&mut self) -> Result<(), CompileError> {
        let Some(st) = self.fx.tries.pop() else {
            return Ok(());
        };
        self.at(st.node);
        if let Some((start, pc, end, handler, c)) = st.catch {
            // The `end` label was bound after the body's normal exit, so the
            // region holds at least that jump.
            let _ = pc;
            self.fx.f.try_region(start, end, handler, c);
            self.fx.release(c);
        }
        let Some((start, pc, end, handler)) = st.fin else {
            self.bind(st.end);
            return Ok(());
        };
        if self.fx.f.pc() == pc {
            self.emit(Inst::Nop {});
        }
        self.bind(end);
        let Some(fin) = self.fx.fins.pop() else {
            return Ok(());
        };
        self.fx.f.try_region(start, end, handler, fin.value);
        // Anything raised in the body or a catch arm: kind 2, the error is
        // already in the value register.
        self.bind(handler);
        self.emit(Inst::LoadInt {
            dst: fin.kind,
            val: 2,
            ty: IntTy::I8,
        });
        self.bind(fin.entry);
        let body = st.finally;
        let end_label = st.end;
        self.tasks
            .push(Task::FinDispatch(fin, st.result, end_label));
        if let Some(b) = body {
            self.tasks.push(Task::Expr(b, Dst::Discard));
        }
        Ok(())
    }

    /// After the `finally` body: continue the pending completion.
    pub(crate) fn fin_dispatch(
        &mut self,
        fin: Fin,
        result: Option<Reg>,
        end: Label,
    ) -> Result<(), CompileError> {
        let _ = result;
        self.at(fin.node);
        let l_return = self.label();
        let l_throw = self.label();
        let l_normal = self.label();
        let exits: Vec<(Exit, Label)> = fin.exits.iter().map(|&x| (x, self.label())).collect();
        let mut targets = alloc::vec![l_normal, l_return, l_throw];
        targets.extend(exits.iter().map(|&(_, l)| l));
        let _ = self.fx.f.switch(IntTy::I8, fin.kind, &targets, l_normal);
        self.fx.dead = true;
        self.fx.origins.push(self.fx.node);
        self.cx.emitted += 1;
        let value = Val {
            reg: fin.value,
            rel: Rel::Keep,
        };
        self.bind(l_return);
        self.leave(Leave::Return, Some(value), fin.node)?;
        self.bind(l_throw);
        self.at(fin.node);
        self.emit(Inst::Throw { src: fin.value });
        for (exit, l) in exits {
            self.bind(l);
            self.at(fin.node);
            match exit {
                Exit::Return => self.leave(Leave::Return, Some(value), fin.node)?,
                Exit::Break(id, has_value) => {
                    self.leave(Leave::Break(id), has_value.then_some(value), fin.node)?;
                }
                Exit::Continue(id) => self.leave(Leave::Continue(id), None, fin.node)?,
            }
        }
        self.bind(l_normal);
        self.bind(end);
        self.fx.release(fin.kind);
        self.fx.release(fin.value);
        Ok(())
    }

    /// `defer d`: the rest of the block runs in a `try` whose `finally` is
    /// `d`.
    pub(crate) fn defer_begin(&mut self, s: StmtId, body: ExprId, result: Reg) {
        let node = NodeRef::Stmt(s);
        self.at(node);
        self.try_begin(node, Some(result), false, Some(body));
    }
}
