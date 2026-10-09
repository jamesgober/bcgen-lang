//! Expressions: values, paths, collections, operations, closures, and the
//! strict forms whose children are all evaluated before one instruction.

use alloc::vec::Vec;

use bytecode_lang::{Inst, Reg, ValType};
use hir_lang::{
    Block, CaptureMode, Closure, DefaultEval, Effects, Expr, ExprId, Intrinsic, ItemKind, Lit,
    Member, NodeRef, Res,
};
use intern_lang::Lookup;

use super::{Dst, Gen, Rel, Step, Task, Val};
use crate::error::{CompileError, Unsupported};
use crate::unit::{Cap, Job, MAX_PARAMS, Slot};

impl<L: Lookup> Gen<'_, '_, L> {
    /// The expression produces a value no variable or container also holds,
    /// so storing it needs no copy. A cast can be the identity, and a bound
    /// hook may return one of its operands, so with hooks only literals,
    /// closures, and collection literals count.
    pub(crate) fn fresh(&self, e: ExprId) -> bool {
        match self.cx.hir.expr(e) {
            Expr::Lit(_)
            | Expr::Closure(_)
            | Expr::Tuple(_)
            | Expr::Array(_)
            | Expr::Repeat { .. }
            | Expr::Record { .. }
            | Expr::Map(_) => true,
            Expr::Op { .. }
            | Expr::Call { .. }
            | Expr::MethodCall { .. }
            | Expr::DynMethodCall { .. }
            | Expr::Intrinsic { .. } => self.cx.opts.hooks().is_empty(),
            _ => false,
        }
    }

    /// The value of `e` may also be held by a variable or a container
    /// (`locals_ok`: a plain local variable does not count, because it dies
    /// with the frame). Looks through `if`, `match`, and block tails, up to a
    /// small budget, then assumes it may.
    fn may_share(&self, e: ExprId, locals_ok: bool) -> bool {
        let hir = self.cx.hir;
        let mut stack: Vec<ExprId> = alloc::vec![e];
        let mut budget = 64u32;
        while let Some(e) = stack.pop() {
            if budget == 0 {
                return true;
            }
            budget -= 1;
            match *hir.expr(e) {
                Expr::Block(Block {
                    tail, label: None, ..
                }) => stack.extend(tail),
                Expr::If { then, else_, .. } => {
                    stack.push(then);
                    stack.extend(else_);
                }
                Expr::Match { arms, .. } => stack.extend(hir.list(arms).iter().map(|a| a.body)),
                Expr::Path(p) if locals_ok => match hir.path(p).res {
                    Res::Local(b) if matches!(self.cx.slot(b), Some(Slot::Reg(_))) => {}
                    _ => return true,
                },
                // Jumps produce no value here.
                Expr::Break { .. } | Expr::Continue { .. } | Expr::Return(_) | Expr::Throw(_) => {}
                _ if self.fresh(e) => {}
                _ => return true,
            }
        }
        false
    }

    /// Storing the value of `e` must copy arrays (PHP value semantics).
    pub(crate) fn needs_dup(&self, e: ExprId) -> bool {
        self.php() && self.may_share(e, false)
    }

    /// Returning the value of `e` must copy arrays: unless it is fresh, or a
    /// plain local variable (which dies with the frame).
    pub(crate) fn ret_dup(&self, e: ExprId) -> bool {
        self.php() && self.may_share(e, true)
    }

    /// Evaluating `e` cannot write a variable (so an earlier operand may stay
    /// in its variable's register).
    pub(crate) fn simple(&self, e: ExprId) -> bool {
        matches!(self.cx.hir.expr(e), Expr::Lit(_) | Expr::Path(_))
    }

    /// The destination for operand `i` of `list`: a variable's register is
    /// fine when every later operand is simple.
    pub(crate) fn operand_dst(&self, list: &[ExprId], i: usize) -> Dst {
        if list.iter().skip(i + 1).all(|&e| self.simple(e)) {
            Dst::Any
        } else {
            Dst::Temp
        }
    }

    /// Schedules the evaluation of `e` into register `r`, copying arrays
    /// when the value is shared.
    pub(crate) fn store_expr_tasks(&mut self, e: ExprId, r: Reg) -> [Task; 2] {
        if self.needs_dup(e) {
            [
                Task::Expr(e, Dst::Any),
                Task::Deliver {
                    dst: Dst::Reg(r),
                    dup: true,
                },
            ]
        } else {
            [Task::Expr(e, Dst::Reg(r)), Task::At(self.fx.node)]
        }
    }

    /// Forms that write their result register before all their code has
    /// run (a loop clears it first; a `finally` or `defer` runs after the
    /// value is in it), so they must not write a register the caller owns.
    fn writes_early(&self, e: ExprId) -> bool {
        let hir = self.cx.hir;
        match *hir.expr(e) {
            Expr::Loop { .. }
            | Expr::Try {
                finally: Some(_), ..
            } => true,
            Expr::Block(b) => {
                b.label.is_some()
                    || hir
                        .list(b.stmts)
                        .iter()
                        .any(|&s| matches!(hir.stmt(s), hir_lang::Stmt::Defer(_)))
            }
            _ => false,
        }
    }

    /// Expands one expression.
    pub(crate) fn expand(&mut self, e: ExprId, dst: Dst) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        self.at(node);
        let hir = self.cx.hir;
        if let Dst::Reg(r) = dst {
            if self.writes_early(e) {
                self.sched([
                    Task::Expr(e, Dst::Temp),
                    Task::Deliver {
                        dst: Dst::Reg(r),
                        dup: false,
                    },
                ]);
                return Ok(());
            }
        }
        match *hir.expr(e) {
            Expr::Lit(lit) => {
                if dst != Dst::Discard {
                    let r = self.result_reg(dst);
                    self.load_lit(r, lit, node)?;
                    self.produced(r, dst);
                } else {
                    // A literal has no effect, but must still be valid.
                    let _ = self.cx.lit_const(lit, node)?;
                }
            }
            Expr::Path(p) => self.path_read(p, node, dst)?,
            Expr::Tuple(elems) | Expr::Array(elems) => {
                let list = hir.list(elems);
                if list.is_empty() && matches!(hir.expr(e), Expr::Tuple(_)) {
                    // `()` is unit, the dynamic `nil`.
                    if dst != Dst::Discard {
                        let r = self.result_reg(dst);
                        self.emit(Inst::LoadNil { dst: r });
                        self.produced(r, dst);
                    }
                    return Ok(());
                }
                let map = self.new_map();
                self.tasks.push(Task::Step(Step::MapDone { map, dst }));
                for &x in list.iter().rev() {
                    let dup = self.needs_dup(x);
                    self.tasks.push(Task::MapPush { map, dup, node });
                    self.tasks.push(Task::Expr(x, Dst::Any));
                }
            }
            Expr::Repeat { elem, count } => {
                // The element is stored: copied once if shared (the copies
                // in the new array may share it; writes through them
                // separate).
                let dup = self.needs_dup(elem);
                self.sched([
                    Task::Expr(elem, Dst::Any),
                    Task::Deliver {
                        dst: Dst::Temp,
                        dup,
                    },
                    Task::Expr(count, Dst::Any),
                    Task::Step(Step::Repeat { dst, node }),
                ]);
            }
            Expr::Record { path, fields, base } => {
                if path.is_some() {
                    return Err(self.cx.unsupported(Unsupported::Record, node));
                }
                let map = self.new_map();
                self.tasks.push(Task::Step(Step::Record {
                    e,
                    map,
                    has_base: base.is_some(),
                    dst,
                }));
                if let Some(b) = base {
                    self.tasks.push(Task::Expr(b, Dst::Temp));
                }
                for f in hir.list(fields).iter().rev() {
                    let dup = self.needs_dup(f.value);
                    self.tasks.push(Task::MapSetName {
                        map,
                        name: f.name.sym,
                        dup,
                        node,
                    });
                    self.tasks.push(Task::Expr(f.value, Dst::Any));
                }
            }
            Expr::Map(entries) => {
                let map = self.new_map();
                self.tasks.push(Task::Step(Step::MapDone { map, dst }));
                for en in hir.list(entries).iter().rev() {
                    let dup = self.needs_dup(en.value);
                    match en.key {
                        Some(k) => {
                            self.tasks.push(Task::MapSet { map, dup, node });
                            self.tasks.push(Task::Expr(en.value, Dst::Any));
                            self.tasks.push(Task::CoerceKey(node));
                            let kd = if self.simple(en.value) {
                                Dst::Any
                            } else {
                                Dst::Temp
                            };
                            self.tasks.push(Task::Expr(k, kd));
                        }
                        None => {
                            self.tasks.push(Task::MapPush { map, dup, node });
                            self.tasks.push(Task::Expr(en.value, Dst::Any));
                        }
                    }
                }
            }
            Expr::Call { callee, args } => self.call(e, callee, args, dst)?,
            Expr::MethodCall {
                receiver,
                method,
                args,
                ..
            } => self.method_call(e, receiver, Some(method.sym), None, args, dst),
            Expr::DynMethodCall {
                receiver,
                name,
                args,
            } => self.method_call(e, receiver, None, Some(name), args, dst),
            Expr::Field { base, .. } => {
                self.sched([Task::Expr(base, Dst::Any), Task::Finish(e, dst)]);
            }
            Expr::DynField { base, name } => {
                let d = if self.simple(name) {
                    Dst::Any
                } else {
                    Dst::Temp
                };
                self.sched([
                    Task::Expr(base, d),
                    Task::Expr(name, Dst::Any),
                    Task::Finish(e, dst),
                ]);
            }
            Expr::Index { base, index } => {
                let d = if self.simple(index) {
                    Dst::Any
                } else {
                    Dst::Temp
                };
                self.sched([
                    Task::Expr(base, d),
                    Task::Expr(index, Dst::Any),
                    Task::CoerceKey(node),
                    Task::Finish(e, dst),
                ]);
            }
            Expr::VarVar(_) => return Err(self.cx.unsupported(Unsupported::VarVar, node)),
            Expr::Append(_) => {
                return Err(CompileError::NotAssignable {
                    node,
                    span: self.cx.span(node),
                });
            }
            Expr::Op { args, .. } => {
                let list = hir.list(args);
                self.tasks.push(Task::Finish(e, dst));
                for i in (0..list.len()).rev() {
                    let d = self.operand_dst(list, i);
                    if let Some(&x) = list.get(i) {
                        self.tasks.push(Task::Expr(x, d));
                    }
                }
            }
            Expr::Cast { expr, .. } => {
                self.sched([Task::Expr(expr, Dst::Any), Task::Finish(e, dst)]);
            }
            Expr::Assign { target, op, value } => self.assign(e, target, op, value, dst)?,
            Expr::RefAssign { target, source } => self.ref_assign(e, target, source, dst)?,
            Expr::Deref(_) | Expr::Borrow { .. } => {
                return Err(self.cx.unsupported(Unsupported::Reference, node));
            }
            Expr::Block(b) => self.block(e, b, dst)?,
            Expr::If { cond, then, else_ } => self.if_expr(cond, then, else_, dst),
            Expr::Match { scrutinee, arms: _ } => {
                let result = self.result_of(dst);
                self.sched([
                    Task::Expr(scrutinee, Dst::Temp),
                    Task::MatchArms { e, result, dst },
                ]);
            }
            Expr::Loop { label, body, step } => self.loop_expr(e, label, body, step, dst),
            Expr::Break { label, value } => self.break_expr(e, label, value, dst)?,
            Expr::Continue { label } => self.continue_expr(e, label, dst)?,
            Expr::Return(value) => self.return_expr(e, value, dst),
            Expr::Closure(c) => self.closure(e, c, dst)?,
            Expr::Throw(x) => {
                self.sched([Task::Expr(x, Dst::Any), Task::Finish(e, dst)]);
            }
            Expr::Try {
                body,
                catches,
                finally,
            } => self.try_expr(e, body, catches, finally, dst),
            Expr::Await(_) | Expr::Yield(_) | Expr::Spawn(_) => {
                return Err(self.cx.unsupported(Unsupported::Coroutine, node));
            }
            Expr::Asm(_) => return Err(self.cx.unsupported(Unsupported::Asm, node)),
            Expr::Intrinsic { kind, args, .. } => {
                let Intrinsic::Named(name) = kind else {
                    return Err(self.cx.unsupported(Unsupported::Intrinsic, node));
                };
                let list = hir.list(args);
                let arity = self.intrinsic_arity(name, node)?;
                if list.len() != arity {
                    return Err(CompileError::IntrinsicArity {
                        node,
                        span: self.cx.span(node),
                        expected: u32::try_from(arity).unwrap_or(u32::MAX),
                    });
                }
                self.tasks.push(Task::Finish(e, dst));
                for i in (0..list.len()).rev() {
                    let d = self.operand_dst(list, i);
                    if let Some(&x) = list.get(i) {
                        self.tasks.push(Task::Expr(x, d));
                    }
                }
            }
            Expr::Err => {
                return Err(CompileError::ErrorNode {
                    node,
                    span: self.cx.span(node),
                });
            }
        }
        Ok(())
    }

    /// The register a value-producing control form writes, if its value is
    /// used.
    pub(crate) fn result_of(&mut self, dst: Dst) -> Option<Reg> {
        match dst {
            Dst::Discard => None,
            Dst::Reg(r) => Some(r),
            Dst::Any | Dst::Temp => Some(self.fx.temp(ValType::Dyn)),
        }
    }

    /// A new empty map in a `ref map` temporary.
    pub(crate) fn new_map(&mut self) -> Reg {
        let ty = self.map_ty();
        let m = self.fx.temp(ty);
        let tr = self.map_ref();
        self.emit(Inst::NewMap { dst: m, ty: tr });
        m
    }

    pub(crate) fn map_done(&mut self, map: Reg, dst: Dst) {
        match dst {
            Dst::Discard => {}
            Dst::Reg(r) => self.emit(Inst::Mov { dst: r, src: map }),
            Dst::Any | Dst::Temp => {
                let t = self.fx.temp(ValType::Dyn);
                self.emit(Inst::Mov { dst: t, src: map });
                self.vals.push(Val {
                    reg: t,
                    rel: Rel::Temp,
                });
            }
        }
        self.fx.release(map);
    }

    /// Loads a literal into a `dyn` register.
    pub(crate) fn load_lit(&mut self, r: Reg, lit: Lit, node: NodeRef) -> Result<(), CompileError> {
        if let Lit::Int(i) = lit {
            if let Some(v) = crate::unit::int_value(i) {
                if let Ok(val) = i32::try_from(v) {
                    self.emit(Inst::DLoadInt { dst: r, val });
                    return Ok(());
                }
            }
        }
        match self.cx.lit_const(lit, node)? {
            None => self.emit(Inst::LoadNil { dst: r }),
            Some(k) => {
                let k = self.cx.mb.constant(k);
                self.emit(Inst::DLoadConst { dst: r, k });
            }
        }
        Ok(())
    }

    /// Reads a path as a value.
    fn path_read(
        &mut self,
        p: hir_lang::PathId,
        node: NodeRef,
        dst: Dst,
    ) -> Result<(), CompileError> {
        let path = *self.cx.hir.path(p);
        if path.unresolved > 0 {
            return Err(match path.res {
                Res::Unresolved | Res::Err => CompileError::Unresolved {
                    node,
                    span: self.cx.span(node),
                },
                _ => self.cx.unsupported(Unsupported::TypeDirected, node),
            });
        }
        match path.res {
            Res::Local(b) => match self.cx.slot(b) {
                Some(Slot::Reg(r)) => {
                    self.deliver(
                        Val {
                            reg: r,
                            rel: Rel::Keep,
                        },
                        dst,
                        false,
                    );
                }
                Some(Slot::Cell(c)) => {
                    if dst != Dst::Discard {
                        let r = self.result_reg(dst);
                        self.emit(Inst::CellGet { dst: r, cell: c });
                        self.produced(r, dst);
                    }
                }
                Some(s @ (Slot::Global(_) | Slot::GlobalCell(_))) => {
                    if dst != Dst::Discard {
                        let r = self.result_reg(dst);
                        self.read_slot(s, r);
                        self.produced(r, dst);
                    }
                }
                None => {
                    let kind = self.cx.hir.binder(b).map(|b| b.kind);
                    return Err(match kind {
                        Some(k) if !k.is_value() || k == hir_lang::BinderKind::Capture => {
                            self.cx.unsupported(Unsupported::TypeDirected, node)
                        }
                        _ => CompileError::Unresolved {
                            node,
                            span: self.cx.span(node),
                        },
                    });
                }
            },
            Res::Def(_) => {
                let item = self.cx.local_item(path.res, node)?;
                let Some(item) = item else {
                    return Ok(());
                };
                match self.cx.hir.item(item).kind {
                    ItemKind::Fn(_) => {
                        let Some(f) = self.cx.dyn_entry(item) else {
                            return Err(self.cx.unsupported(Unsupported::ExternValue, node));
                        };
                        if dst != Dst::Discard {
                            let r = self.result_reg(dst);
                            self.emit(Inst::MakeClosure { dst: r, func: f });
                            self.produced(r, dst);
                        }
                    }
                    ItemKind::Global { .. } | ItemKind::Const { .. } => {
                        let Some(slot) = self.cx.global_slot(item) else {
                            return Ok(());
                        };
                        if dst != Dst::Discard {
                            let r = self.result_reg(dst);
                            self.read_slot(slot, r);
                            self.produced(r, dst);
                        }
                    }
                    ItemKind::Class(_) | ItemKind::Impl(_) | ItemKind::Interface(_) => {
                        return Err(self.cx.unsupported(Unsupported::Class, node));
                    }
                    ItemKind::Record(_) | ItemKind::Sum(_) => {
                        return Err(self.cx.unsupported(Unsupported::Record, node));
                    }
                    _ => return Err(self.cx.unsupported(Unsupported::TypeDirected, node)),
                }
            }
            Res::Extern(_) => return Err(self.cx.unsupported(Unsupported::ExternValue, node)),
            Res::Prim(_) => return Err(self.cx.unsupported(Unsupported::TypeDirected, node)),
            Res::Unresolved | Res::Err => {
                return Err(CompileError::Unresolved {
                    node,
                    span: self.cx.span(node),
                });
            }
        }
        Ok(())
    }

    /// The strict forms, once their children are on the value stack.
    pub(crate) fn finish(&mut self, e: ExprId, dst: Dst) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        self.at(node);
        let hir = self.cx.hir;
        match *hir.expr(e) {
            Expr::Op { op, args } => {
                let n = hir.list(args).len();
                let vals = self.pop_n(n);
                let regs: Vec<Reg> = vals.iter().map(|v| v.reg).collect();
                let r = self.result_reg(dst);
                super::ops::emit_op(self, op, &regs, r, node)?;
                for v in vals {
                    self.release(v);
                }
                self.produced(r, dst);
            }
            Expr::Cast { ty, policy, .. } => {
                let v = self.pop();
                let r = self.result_reg(dst);
                super::ops::emit_cast(self, ty, policy, v.reg, r, node)?;
                self.release(v);
                self.produced(r, dst);
            }
            Expr::Field { member, .. } => {
                let base = self.pop();
                let r = self.result_reg(dst);
                match member {
                    Member::Named(sym) => {
                        let name = self.name_ref(sym);
                        self.emit(Inst::GetProp {
                            dst: r,
                            obj: base.reg,
                            name,
                        });
                    }
                    Member::Index(i) => {
                        let k = self.fx.temp(ValType::Dyn);
                        self.load_dyn_int(k, i64::from(i));
                        self.emit(Inst::DGetIndex {
                            dst: r,
                            obj: base.reg,
                            key: k,
                        });
                        self.fx.release(k);
                    }
                }
                self.release(base);
                self.produced(r, dst);
            }
            Expr::DynField { .. } | Expr::Index { .. } => {
                let key = self.pop();
                let base = self.pop();
                let r = self.result_reg(dst);
                self.emit(Inst::DGetIndex {
                    dst: r,
                    obj: base.reg,
                    key: key.reg,
                });
                self.release(key);
                self.release(base);
                self.produced(r, dst);
            }
            Expr::Throw(_) => {
                let v = self.pop();
                self.emit(Inst::Throw { src: v.reg });
                self.release(v);
                self.dummy(dst);
            }
            Expr::Intrinsic {
                kind: Intrinsic::Named(name),
                args,
                ..
            } => {
                let n = hir.list(args).len();
                let vals = self.pop_n(n);
                let r = self.result_reg(dst);
                self.intrinsic(name, &vals, r, node)?;
                for v in vals {
                    self.release(v);
                }
                self.produced(r, dst);
            }
            _ => {}
        }
        Ok(())
    }

    /// Pops `n` values, in push order.
    pub(crate) fn pop_n(&mut self, n: usize) -> Vec<Val> {
        let at = self.vals.len().saturating_sub(n);
        self.vals.split_off(at)
    }

    /// The value of an expression that never completes (`throw`, `break`,
    /// `return`): code after it is unreachable, but the value stack must
    /// still balance.
    pub(crate) fn dummy(&mut self, dst: Dst) {
        if matches!(dst, Dst::Any | Dst::Temp) {
            let r = self.fx.temp(ValType::Dyn);
            self.vals.push(Val {
                reg: r,
                rel: Rel::Temp,
            });
        }
    }

    // ------------------------------------------------------------ intrinsics

    fn intrinsic_arity(
        &self,
        name: hir_lang::Symbol,
        node: NodeRef,
    ) -> Result<usize, CompileError> {
        let n = self.cx.names.resolve_with(name, |s| match s {
            "concat" => 2,
            "len" | "truthy" | "lnot" | "type_of" | "iter" | "iter_next" => 1,
            _ => 0,
        });
        match n {
            Some(n) if n > 0 => Ok(n),
            _ => Err(self.cx.unsupported(Unsupported::Intrinsic, node)),
        }
    }

    /// The named intrinsics: the dynamic instructions without an OPS
    /// operation (`concat`, `len`, `truthy`, `lnot`, `type_of`) and
    /// iteration (`iter`, `iter_next`).
    fn intrinsic(
        &mut self,
        name: hir_lang::Symbol,
        args: &[Val],
        r: Reg,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let text = self.cx.text(name);
        let a = args.first().map_or(Reg(0), |v| v.reg);
        let b = args.get(1).map_or(Reg(0), |v| v.reg);
        match text.as_str() {
            "concat" => self.emit(Inst::DConcat {
                dst: r,
                lhs: a,
                rhs: b,
            }),
            "len" => {
                let n = self.fx.temp(ValType::I64);
                self.emit(Inst::DLen { dst: n, src: a });
                self.emit(Inst::ToDyn {
                    dst: r,
                    src: n,
                    from: bytecode_lang::Prim::I64,
                });
                self.fx.release(n);
            }
            "truthy" | "lnot" => {
                let t = self.fx.temp(ValType::Bool);
                if text == "truthy" {
                    self.emit(Inst::DTruthy { dst: t, src: a });
                } else {
                    self.emit(Inst::DLNot { dst: t, src: a });
                }
                self.emit(Inst::ToDyn {
                    dst: r,
                    src: t,
                    from: bytecode_lang::Prim::Bool,
                });
                self.fx.release(t);
            }
            "type_of" => {
                let t = self.fx.temp(ValType::U8);
                self.emit(Inst::TypeOf { dst: t, src: a });
                self.emit(Inst::ToDyn {
                    dst: r,
                    src: t,
                    from: bytecode_lang::Prim::U8,
                });
                self.fx.release(t);
            }
            "iter" => {
                // PHP iterates a snapshot: a copy-on-write `dup` first.
                if self.php() {
                    let t = self.fx.temp(ValType::Dyn);
                    self.dup_into(t, a);
                    self.emit(Inst::DIterNew { dst: r, src: t });
                    self.fx.release(t);
                } else {
                    self.emit(Inst::DIterNew { dst: r, src: a });
                }
            }
            "iter_next" => {
                // nil when done, else the pair [key, value].
                let has = self.fx.temp(ValType::Bool);
                let v = self.fx.temp(ValType::Dyn);
                let k = self.fx.temp(ValType::Dyn);
                let done = self.label();
                let end = self.label();
                self.emit(Inst::IterNext {
                    has,
                    iter: a,
                    val: v,
                });
                self.jump_on(has, done, false);
                self.emit(Inst::IterKey { dst: k, iter: a });
                let m = self.new_map();
                self.emit(Inst::MapPush { map: m, src: k });
                if self.php() {
                    self.dup_into(v, v);
                }
                self.emit(Inst::MapPush { map: m, src: v });
                self.emit(Inst::Mov { dst: r, src: m });
                self.fx.release(m);
                self.jmp(end);
                self.bind(done);
                self.emit(Inst::LoadNil { dst: r });
                self.bind(end);
                self.fx.release(k);
                self.fx.release(v);
                self.fx.release(has);
            }
            _ => return Err(self.cx.unsupported(Unsupported::Intrinsic, node)),
        }
        Ok(())
    }

    // ------------------------------------------------------------ repeat, record

    pub(crate) fn repeat_finish(&mut self, dst: Dst, node: NodeRef) {
        self.at(node);
        let count = self.pop();
        let elem = self.pop();
        // A count that is not an integer is a type error; one below 1 gives
        // an empty array.
        let n = self.fx.temp(ValType::I64);
        self.emit(Inst::FromDyn {
            dst: n,
            src: count.reg,
            to: bytecode_lang::Prim::I64,
        });
        let m = self.new_map();
        let i = self.fx.temp(ValType::I64);
        let one = self.fx.temp(ValType::I64);
        let more = self.fx.temp(ValType::Bool);
        self.load_i64(i, 0);
        self.load_i64(one, 1);
        let top = self.label();
        let done = self.label();
        self.bind(top);
        self.emit(Inst::ILt {
            dst: more,
            lhs: i,
            rhs: n,
            ty: bytecode_lang::IntTy::I64,
        });
        self.jump_on(more, done, false);
        self.emit(Inst::MapPush {
            map: m,
            src: elem.reg,
        });
        self.emit(Inst::IAdd {
            dst: i,
            lhs: i,
            rhs: one,
            op: bytecode_lang::IntOp::new(bytecode_lang::IntTy::I64),
        });
        self.emit(Inst::Safepoint {});
        self.jmp(top);
        self.bind(done);
        for r in [n, i, one, more] {
            self.fx.release(r);
        }
        self.release(count);
        self.release(elem);
        self.map_done(m, dst);
    }

    pub(crate) fn record_finish(&mut self, e: ExprId, map: Reg, has_base: bool, dst: Dst) {
        self.at(NodeRef::Expr(e));
        if !has_base {
            self.map_done(map, dst);
            return;
        }
        // `{ fields.., ..base }`: a copy of `base` with the fields set over it.
        let base = self.pop();
        let out = self.map_ty();
        let out = self.fx.temp(out);
        let tr = self.map_ref();
        // `cast` admits nil, which is not a record: test the kind instead.
        let b = self.fx.temp(ValType::Bool);
        let ok = self.label();
        self.emit(Inst::IsType {
            dst: b,
            src: base.reg,
            ty: tr,
        });
        self.jump_on(b, ok, true);
        self.raise_type_error();
        self.bind(ok);
        self.emit(Inst::Cast {
            dst: out,
            src: base.reg,
            ty: tr,
        });
        self.emit(Inst::Dup { dst: out, src: out });
        // Overwrite with the fields, in order.
        let it = ValType::Ref(self.cx.types.iter);
        let it = self.fx.temp(it);
        let has = self.fx.temp(ValType::Bool);
        let k = self.fx.temp(ValType::Dyn);
        let v = self.fx.temp(ValType::Dyn);
        let top = self.label();
        let done = self.label();
        self.emit(Inst::IterNew { dst: it, src: map });
        self.bind(top);
        self.emit(Inst::IterNext {
            has,
            iter: it,
            val: v,
        });
        self.jump_on(has, done, false);
        self.emit(Inst::IterKey { dst: k, iter: it });
        self.emit(Inst::MapSet {
            map: out,
            key: k,
            src: v,
        });
        self.emit(Inst::Safepoint {});
        self.jmp(top);
        self.bind(done);
        for r in [b, it, has, k, v, map] {
            self.fx.release(r);
        }
        self.release(base);
        self.map_done(out, dst);
    }

    // ------------------------------------------------------------ closures

    fn closure(&mut self, e: ExprId, c: Closure, dst: Dst) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        let hir = self.cx.hir;
        if c.effects.contains(Effects::ASYNC) || c.effects.contains(Effects::YIELD) {
            return Err(self.cx.unsupported(Unsupported::Coroutine, node));
        }
        let params = hir.list(c.params);
        if params.len() > MAX_PARAMS {
            return Err(CompileError::TooManyParams {
                node,
                span: self.cx.span(node),
                limit: MAX_PARAMS as u32,
            });
        }
        if params
            .iter()
            .any(|&p| hir.param(p).kind == hir_lang::ParamKind::Receiver)
        {
            return Err(self.cx.unsupported(Unsupported::Class, node));
        }
        // Captures: (inside target, source in this frame).
        let mut caps: Vec<Cap> = Vec::new();
        let mut sources: Vec<Option<Slot>> = Vec::new();
        let mut aliases: Vec<(hir_lang::BinderId, Slot)> = Vec::new();
        if let Some(b) = c.self_binder {
            caps.push(Cap::SelfCell(b));
            sources.push(None);
        }
        for cap in hir.list(c.captures) {
            let pnode = NodeRef::Path(cap.outer);
            let outer = hir.path(cap.outer);
            let src = match outer.res {
                Res::Local(ob) => self.cx.slot(ob),
                Res::Def(_) => {
                    let item = self.cx.local_item(outer.res, pnode)?;
                    match item.map(|i| (i, hir.item(i).kind)) {
                        Some((i, ItemKind::Global { .. } | ItemKind::Const { .. })) => {
                            self.cx.global_slot(i)
                        }
                        _ => return Err(self.cx.unsupported(Unsupported::TypeDirected, pnode)),
                    }
                }
                Res::Unresolved | Res::Err => {
                    return Err(CompileError::Unresolved {
                        node: pnode,
                        span: self.cx.span(pnode),
                    });
                }
                _ => return Err(self.cx.unsupported(Unsupported::TypeDirected, pnode)),
            };
            let Some(src) = src else {
                return Err(CompileError::Unresolved {
                    node: pnode,
                    span: self.cx.span(pnode),
                });
            };
            match (cap.mode, src) {
                (CaptureMode::ByValue | CaptureMode::Infer, _) => {
                    caps.push(Cap::Value(cap.binder));
                    sources.push(Some(src));
                }
                (_, Slot::Global(_) | Slot::GlobalCell(_)) => aliases.push((cap.binder, src)),
                (_, Slot::Cell(_)) => {
                    caps.push(Cap::Cell(cap.binder));
                    sources.push(Some(src));
                }
                (_, Slot::Reg(_)) => {
                    // Not marked shared: the analysis marks every by-reference
                    // source, so this is a variable it could not see; share
                    // its value.
                    caps.push(Cap::Value(cap.binder));
                    sources.push(Some(src));
                }
            }
        }
        let implicit = self.cx.an.captures.get(&e).cloned().unwrap_or_default();
        for b in implicit {
            let Some(src) = self.cx.slot(b) else {
                continue;
            };
            match (c.implicit, src) {
                // By value: a copy at creation, whatever holds the variable.
                (Some(CaptureMode::ByValue), _) => {
                    caps.push(Cap::Value(b));
                    sources.push(Some(src));
                }
                (_, Slot::Global(_) | Slot::GlobalCell(_)) => aliases.push((b, src)),
                (_, Slot::Reg(_)) => {
                    caps.push(Cap::Value(b));
                    sources.push(Some(src));
                }
                (_, Slot::Cell(_)) => {
                    caps.push(Cap::Cell(b));
                    sources.push(Some(src));
                }
            }
        }
        let mut once_defaults: Vec<(usize, ExprId)> = Vec::new();
        if c.defaults == DefaultEval::Once {
            for (i, &p) in params.iter().enumerate() {
                if let Some(d) = hir.param(p).default {
                    caps.push(Cap::Once(i));
                    sources.push(None);
                    once_defaults.push((i, d));
                }
            }
        }
        // Declare the closure's function with its capture layout.
        self.cx.closures += 1;
        let mut name = alloc::string::String::from("<closure#");
        name.push_str(&alloc::format!("{}>", self.cx.closures));
        let mut f = self
            .cx
            .mb
            .function(&name, &[ValType::Dyn, ValType::Dyn], &[ValType::Dyn]);
        let mut shape: Vec<ValType> = alloc::vec![ValType::Dyn];
        for cap in &caps {
            let ty = match cap {
                Cap::Value(_) | Cap::Once(_) => ValType::Dyn,
                Cap::Cell(_) | Cap::SelfCell(_) => self.cell_ty(),
            };
            let _ = f.capture(ty);
            shape.push(ty);
        }
        let func = f.id();
        self.queue(Job::Closure {
            e,
            f,
            caps: caps.clone(),
            aliases,
        });
        // Fill the capture window.
        let win = self.fx.window(&shape);
        let mut self_cell = None;
        let php = self.php();
        let mut once_slots: Vec<(Reg, ExprId)> = Vec::new();
        for (i, (cap, src)) in caps.iter().zip(sources.iter()).enumerate() {
            let slot = crate::func::FnCx::slot(win.1, i + 1);
            match (cap, src) {
                (Cap::SelfCell(_), _) => {
                    let n = self.fx.temp(ValType::Dyn);
                    self.emit(Inst::LoadNil { dst: n });
                    let ty = self.cell_ref();
                    self.emit(Inst::NewCell {
                        dst: slot,
                        src: n,
                        ty,
                    });
                    self.fx.release(n);
                    self_cell = Some(slot);
                }
                (Cap::Value(_), Some(Slot::Reg(r))) => {
                    if php {
                        self.dup_into(slot, *r);
                    } else {
                        self.emit(Inst::Mov { dst: slot, src: *r });
                    }
                }
                (Cap::Value(_), Some(Slot::Cell(c))) => {
                    self.emit(Inst::CellGet {
                        dst: slot,
                        cell: *c,
                    });
                    if php {
                        self.dup_into(slot, slot);
                    }
                }
                (Cap::Value(_), Some(s @ (Slot::Global(_) | Slot::GlobalCell(_)))) => {
                    self.read_slot(*s, slot);
                    if php {
                        self.dup_into(slot, slot);
                    }
                }
                (Cap::Cell(_), Some(Slot::Cell(c))) => {
                    self.emit(Inst::Mov { dst: slot, src: *c });
                }
                (Cap::Once(p), _) => {
                    if let Some(&(_, d)) = once_defaults.iter().find(|(i, _)| i == p) {
                        once_slots.push((slot, d));
                    }
                }
                _ => {}
            }
        }
        self.tasks.push(Task::Step(Step::MakeClosure {
            e,
            win,
            func,
            self_cell,
            dst,
        }));
        for (slot, d) in once_slots.into_iter().rev() {
            let t = self.store_expr_tasks(d, slot);
            self.tasks.push(t[1].clone());
            self.tasks.push(t[0].clone());
        }
        Ok(())
    }

    pub(crate) fn make_closure(
        &mut self,
        e: ExprId,
        win: (u32, Reg),
        func: bytecode_lang::FuncId,
        self_cell: Option<Reg>,
        dst: Dst,
    ) {
        self.at(NodeRef::Expr(e));
        self.emit(Inst::MakeClosure { dst: win.1, func });
        if let Some(c) = self_cell {
            self.emit(Inst::CellSet {
                cell: c,
                src: win.1,
            });
        }
        self.deliver(
            Val {
                reg: win.1,
                rel: Rel::Win(win.0),
            },
            dst,
            false,
        );
    }
}
