//! Code generation for one function: an explicit task stack (no recursion
//! over the HIR, at any depth) and a value stack of the registers that hold
//! evaluated operands.
//!
//! A task either emits code or expands into more tasks. `Task::Expr(e, dst)`
//! evaluates `e`: when it completes it has pushed exactly one [`Val`] if
//! `dst` is [`Dst::Any`] or [`Dst::Temp`], and none for [`Dst::Reg`] (the
//! value is in that register) or [`Dst::Discard`]. Continuation tasks pop the
//! values their children pushed.

mod call;
mod coro;
mod entry;
mod expr;
mod flow;
mod intrinsic;
mod ops;
mod pat;
mod place;

use alloc::vec::Vec;

use bytecode_lang::{Const, Inst, IntTy, Kind, Label, Reg, ValType};
use hir_lang::{BinderId, ExprId, NodeRef, OpKind, PatId, StmtId, Symbol};
use intern_lang::Lookup;

use crate::error::CompileError;
use crate::func::{Exit, Fin, FnCx, Scoped, Target};
use crate::options::ArraySemantics;
use crate::unit::{Cx, Job, Slot};

pub(crate) use entry::run_job;

/// Where an expression's value goes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Dst {
    /// Nowhere: evaluate for effect.
    Discard,
    /// Any register, possibly a variable's own (read it before anything can
    /// write that variable).
    Any,
    /// A register no variable owns.
    Temp,
    /// This register (only written once every operand is evaluated).
    Reg(Reg),
}

/// How a value's register is given back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Rel {
    /// Not at all: a variable's register.
    Keep,
    /// To the temporary pool.
    Temp,
    /// The whole window of this shape, of which the register is the base.
    Win(u32),
}

/// An evaluated operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Val {
    pub(crate) reg: Reg,
    pub(crate) rel: Rel,
}

/// A request to leave the current code through a jump.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Leave {
    Return,
    Break(u32),
    Continue(u32),
}

/// A unit of work.
#[derive(Clone, Debug)]
pub(crate) enum Task {
    Expr(ExprId, Dst),
    Stmt(StmtId),
    At(NodeRef),
    Bind(Label),
    Jump(Label),
    Emit(Inst),
    Push(Val),
    Free(Reg),
    /// Opens a scope: binders allocated until the matching close are freed
    /// there.
    ScopeOpen,
    ScopeClose,
    /// Pops a value and delivers it to `dst`, copying arrays if `dup`.
    Deliver {
        dst: Dst,
        dup: bool,
    },
    /// Pops a key and pushes it normalized (PHP key coercion).
    CoerceKey(NodeRef),
    /// Pops a value and appends it to the map in `map`.
    MapPush {
        map: Reg,
        dup: bool,
        node: NodeRef,
    },
    /// Pops a value, then a key, and sets the entry in `map`.
    MapSet {
        map: Reg,
        dup: bool,
        node: NodeRef,
    },
    /// Pops a value and sets it under the string key `name` in `map`.
    MapSetName {
        map: Reg,
        name: Symbol,
        dup: bool,
        node: NodeRef,
    },
    /// Pops a value and stores a new reference holding it into `cell`.
    NewCell {
        cell: Reg,
        dup: bool,
    },
    /// Pops the children of a strict form and emits the form.
    Finish(ExprId, Dst),
    /// Jumps to `label` when the condition `e` is (`when`) true.
    Cond {
        e: ExprId,
        label: Label,
        when: bool,
    },
    /// Pops a value; jumps on its truthiness.
    CondTruthy {
        label: Label,
        when: bool,
        node: NodeRef,
    },
    /// Pops two values; jumps on their comparison.
    CondCmp {
        op: OpKind,
        label: Label,
        when: bool,
        node: NodeRef,
    },
    TargetPush(Target),
    TargetPop,
    /// Leaves through a jump; pops the value first if `value`.
    Leave {
        leave: Leave,
        value: bool,
        node: NodeRef,
    },
    /// The end of a `try` body (or of the code a `defer` protects).
    TryBodyEnd,
    /// One catch arm finished normally.
    TryNormalExit,
    /// All catch arms tried: rethrow.
    TryRethrow,
    /// The end of the `try`: regions, the `finally` copy, the dispatch.
    TryEnd,
    /// After a `finally` body: dispatch on the pending completion.
    FinDispatch(Fin, Option<Reg>, Label),
    /// Pops the scrutinee and schedules the arms.
    MatchArms {
        e: ExprId,
        result: Option<Reg>,
        dst: Dst,
    },
    /// Tests pattern `pat` against `v`; jumps to `fail` if it does not match.
    Pat {
        pat: PatId,
        v: Reg,
        fail: Label,
    },
    /// Pops the value of a `let` and destructures it.
    LetPat {
        pat: PatId,
        else_: Option<ExprId>,
        node: NodeRef,
    },
    /// Binds `b` to the value in `v`.
    BindVal {
        b: BinderId,
        v: Reg,
    },
    /// Continues generating a construct in steps (calls, places, closures).
    Step(Step),
}

/// Multi-step constructs: the state each step needs.
#[derive(Clone, Debug)]
pub(crate) enum Step {
    /// Calls and method calls (see `call.rs`).
    Call(call::CallStep),
    /// Assignment to a place chain (see `place.rs`).
    Place(place::PlaceStep),
    /// Coroutines: `yield`, `yield from`, `await`, `spawn` (see `coro.rs`).
    Coro(coro::CoroStep),
    /// A named intrinsic whose operands are in a host-call window (see
    /// `intrinsic.rs`).
    Intrinsic(intrinsic::IntrinsicStep),
    /// Closure creation (see `expr.rs`).
    MakeClosure {
        e: ExprId,
        win: (u32, Reg),
        func: bytecode_lang::FuncId,
        self_cell: Option<Reg>,
        dst: Dst,
    },
    /// The second half of `static $x = init` (see `flow.rs`).
    StaticInit {
        global: bytecode_lang::GlobalId,
        flag: bytecode_lang::GlobalId,
        done: Label,
    },
    /// The second half of a shared `static $x = init`: a new reference.
    StaticCell {
        global: bytecode_lang::GlobalId,
        flag: bytecode_lang::GlobalId,
        done: Label,
    },
    /// Stores the popped value into a global.
    SetGlobal(bytecode_lang::GlobalId),
    /// Stores a new reference holding the popped value into a global.
    SetGlobalCell(bytecode_lang::GlobalId),
    /// Returns the popped value from the function.
    Ret,
    /// A parameter's default when the presence mask lacks it (see
    /// `entry.rs`).
    ParamBind { index: usize, reg: Reg },
    /// Finishes a `repeat` (see `expr.rs`).
    Repeat { dst: Dst, node: NodeRef },
    /// Finishes an anonymous record (see `expr.rs`).
    Record {
        e: ExprId,
        map: Reg,
        has_base: bool,
        dst: Dst,
    },
    /// Finishes a map or array literal: moves the map into a `dyn` value.
    MapDone { map: Reg, dst: Dst },
    /// `defer`: the rest of the block becomes a `try` with this `finally`.
    DeferBegin {
        s: StmtId,
        body: ExprId,
        result: Reg,
    },
    /// Raises `TypeError` at the current node.
    RaiseTypeError,
    /// Raises `NoMatch` (E0200) with the popped scrutinee as its payload.
    RaiseNoMatch,
}

/// The generator of one function.
pub(crate) struct Gen<'c, 'a, L: Lookup> {
    pub(crate) cx: &'c mut Cx<'a, L>,
    pub(crate) fx: FnCx,
    pub(crate) tasks: Vec<Task>,
    pub(crate) vals: Vec<Val>,
    pub(crate) params: Option<entry::Params>,
    /// Evaluated places: `let_place` aliases and the places assignments,
    /// reference assignments, and place arguments are using.
    pub(crate) places: Vec<place::EvPlace>,
}

impl<'c, 'a, L: Lookup> Gen<'c, 'a, L> {
    pub(crate) fn new(cx: &'c mut Cx<'a, L>, fx: FnCx) -> Self {
        Gen {
            cx,
            fx,
            tasks: Vec::new(),
            vals: Vec::new(),
            params: None,
            places: Vec::new(),
        }
    }

    // ------------------------------------------------------------ driving

    /// Runs tasks until none are left.
    pub(crate) fn run(&mut self) -> Result<(), CompileError> {
        let limit = self.cx.opts.max_instructions();
        while let Some(t) = self.tasks.pop() {
            self.step(t)?;
            if self.cx.emitted > limit {
                return Err(CompileError::BudgetExceeded { limit });
            }
        }
        Ok(())
    }

    fn step(&mut self, t: Task) -> Result<(), CompileError> {
        match t {
            Task::Expr(e, dst) => self.expand(e, dst)?,
            Task::Stmt(s) => self.stmt(s)?,
            Task::At(node) => self.at(node),
            Task::Bind(l) => self.bind(l),
            Task::Jump(l) => self.jmp(l),
            Task::Emit(inst) => self.emit(inst),
            Task::Push(v) => self.vals.push(v),
            Task::Free(r) => self.fx.release(r),
            Task::ScopeOpen => self.fx.scopes.push(self.fx.scoped.len()),
            Task::ScopeClose => self.scope_close(),
            Task::Deliver { dst, dup } => {
                let v = self.pop();
                self.deliver(v, dst, dup);
            }
            Task::CoerceKey(node) => {
                self.at(node);
                let k = self.pop();
                let k = self.coerce_key(k);
                self.vals.push(k);
            }
            Task::MapPush { map, dup, node } => {
                self.at(node);
                let v = self.pop();
                let v = self.transfer(v, dup);
                self.emit(Inst::MapPush { map, src: v.reg });
                self.release(v);
            }
            Task::MapSet { map, dup, node } => {
                self.at(node);
                let v = self.pop();
                let k = self.pop();
                let v = self.transfer(v, dup);
                self.emit(Inst::MapSet {
                    map,
                    key: k.reg,
                    src: v.reg,
                });
                self.release(v);
                self.release(k);
            }
            Task::MapSetName {
                map,
                name,
                dup,
                node,
            } => {
                self.at(node);
                let v = self.pop();
                let v = self.transfer(v, dup);
                let k = self.load_name(name);
                self.emit(Inst::MapSet {
                    map,
                    key: k,
                    src: v.reg,
                });
                self.fx.release(k);
                self.release(v);
            }
            Task::NewCell { cell, dup } => {
                let v = self.pop();
                let v = self.transfer(v, dup);
                self.emit(Inst::NewRef {
                    dst: cell,
                    src: v.reg,
                });
                self.release(v);
            }
            Task::Finish(e, dst) => self.finish(e, dst)?,
            Task::Cond { e, label, when } => self.cond(e, label, when)?,
            Task::CondTruthy { label, when, node } => {
                self.at(node);
                let v = self.pop();
                let b = self.fx.temp(ValType::Bool);
                self.emit(Inst::DTruthy { dst: b, src: v.reg });
                self.release(v);
                self.jump_on(b, label, when);
                self.fx.release(b);
            }
            Task::CondCmp {
                op,
                label,
                when,
                node,
            } => {
                self.at(node);
                let rhs = self.pop();
                let lhs = self.pop();
                let b = self.fx.temp(ValType::Bool);
                ops::emit_cmp(self, op, b, lhs.reg, rhs.reg);
                self.release(rhs);
                self.release(lhs);
                self.jump_on(b, label, when);
                self.fx.release(b);
            }
            Task::TargetPush(t) => self.fx.targets.push(t),
            Task::TargetPop => {
                let _ = self.fx.targets.pop();
            }
            Task::Leave { leave, value, node } => {
                self.at(node);
                let v = if value { Some(self.pop()) } else { None };
                self.leave(leave, v, node)?;
            }
            Task::TryBodyEnd => self.try_body_end()?,
            Task::TryNormalExit => self.try_normal_exit(),
            Task::TryRethrow => self.try_rethrow(),
            Task::TryEnd => self.try_end()?,
            Task::FinDispatch(fin, result, end) => self.fin_dispatch(fin, result, end)?,
            Task::MatchArms { e, result, dst } => self.match_arms(e, result, dst)?,
            Task::Pat { pat, v, fail } => self.pat(pat, v, fail)?,
            Task::LetPat { pat, else_, node } => self.let_pat(pat, else_, node),
            Task::BindVal { b, v } => self.bind_binder(b, v),
            Task::Step(s) => self.step_multi(s)?,
        }
        Ok(())
    }

    fn step_multi(&mut self, s: Step) -> Result<(), CompileError> {
        match s {
            Step::Call(c) => self.call_step(c),
            Step::Place(p) => self.place_step(p),
            Step::Coro(c) => self.coro_step(c),
            Step::Intrinsic(i) => self.intrinsic_step(i),
            Step::MakeClosure {
                e,
                win,
                func,
                self_cell,
                dst,
            } => {
                self.make_closure(e, win, func, self_cell, dst);
                Ok(())
            }
            Step::StaticInit { global, flag, done } => {
                let v = self.pop();
                let v = self.transfer(v, self.php());
                self.emit(Inst::SetGlobal { global, src: v.reg });
                self.release(v);
                let t = self.fx.temp(ValType::Bool);
                self.emit(Inst::LoadBool { dst: t, val: true });
                self.emit(Inst::SetGlobal {
                    global: flag,
                    src: t,
                });
                self.fx.release(t);
                self.bind(done);
                Ok(())
            }
            Step::StaticCell { global, flag, done } => {
                let v = self.pop();
                let v = self.transfer(v, self.php());
                let ct = self.cell_ty();
                let c = self.fx.temp(ct);
                self.emit(Inst::NewRef { dst: c, src: v.reg });
                self.emit(Inst::SetGlobal { global, src: c });
                self.fx.release(c);
                self.release(v);
                let t = self.fx.temp(ValType::Bool);
                self.emit(Inst::LoadBool { dst: t, val: true });
                self.emit(Inst::SetGlobal {
                    global: flag,
                    src: t,
                });
                self.fx.release(t);
                self.bind(done);
                Ok(())
            }
            Step::SetGlobalCell(g) => {
                let v = self.pop();
                let ct = self.cell_ty();
                let c = self.fx.temp(ct);
                self.emit(Inst::NewRef { dst: c, src: v.reg });
                self.emit(Inst::SetGlobal { global: g, src: c });
                self.fx.release(c);
                self.release(v);
                Ok(())
            }
            Step::SetGlobal(g) => {
                let v = self.pop();
                self.emit(Inst::SetGlobal {
                    global: g,
                    src: v.reg,
                });
                self.release(v);
                Ok(())
            }
            Step::Ret => {
                let v = self.pop();
                self.emit(Inst::Ret { src: v.reg });
                self.release(v);
                Ok(())
            }
            Step::ParamBind { index, reg } => self.param_bind(index, reg),
            Step::Repeat { dst, node } => {
                self.repeat_finish(dst, node);
                Ok(())
            }
            Step::Record {
                e,
                map,
                has_base,
                dst,
            } => {
                self.record_finish(e, map, has_base, dst);
                Ok(())
            }
            Step::MapDone { map, dst } => {
                self.map_done(map, dst);
                Ok(())
            }
            Step::DeferBegin { s, body, result } => {
                self.defer_begin(s, body, result);
                Ok(())
            }
            Step::RaiseTypeError => {
                self.raise_type_error();
                Ok(())
            }
            Step::RaiseNoMatch => {
                let v = self.pop();
                self.emit(Inst::Raise {
                    src: v.reg,
                    kind: bytecode_lang::ErrorKind::NoMatch,
                });
                self.release(v);
                Ok(())
            }
        }
    }

    /// Pushes tasks so that they run in the order given.
    pub(crate) fn sched<const N: usize>(&mut self, tasks: [Task; N]) {
        for t in tasks.into_iter().rev() {
            self.tasks.push(t);
        }
    }

    // ------------------------------------------------------------ emitting

    pub(crate) fn emit(&mut self, inst: Inst) {
        let _ = self.fx.emit(inst);
        self.cx.emitted += 1;
    }

    /// Attributes the following instructions to `node`, and points the line
    /// table at its span.
    pub(crate) fn at(&mut self, node: NodeRef) {
        self.fx.node = node;
        if self.fx.located == Some(node) {
            return;
        }
        self.fx.located = Some(node);
        let span = self.cx.span(node);
        let (file, line, column) = match self.cx.locator {
            Some(l) => {
                let at = l.locate(span);
                (self.cx.mb.string(at.file), at.line, at.column)
            }
            None => (self.cx.file, 0, span.start().to_u32()),
        };
        self.fx.f.set_location(file, line, column);
    }

    pub(crate) fn label(&mut self) -> Label {
        self.fx.f.label()
    }

    pub(crate) fn bind(&mut self, l: Label) {
        self.fx.f.bind(l);
    }

    pub(crate) fn jmp(&mut self, l: Label) {
        self.fx.origins.push(self.fx.node);
        self.cx.emitted += 1;
        let _ = self.fx.f.jmp(l);
    }

    pub(crate) fn jump_on(&mut self, cond: Reg, l: Label, when: bool) {
        self.fx.origins.push(self.fx.node);
        self.cx.emitted += 1;
        if when {
            let _ = self.fx.f.jmp_if(cond, l);
        } else {
            let _ = self.fx.f.jmp_if_not(cond, l);
        }
    }

    /// Whether array copies are values (PHP).
    pub(crate) fn php(&self) -> bool {
        self.cx.opts.arrays() == ArraySemantics::Php
    }

    pub(crate) fn map_ref(&mut self) -> bytecode_lang::TypeRef {
        let t = self.cx.types.map;
        self.fx.f.type_ref(t)
    }

    pub(crate) fn map_ty(&self) -> ValType {
        ValType::Ref(self.cx.types.map)
    }

    pub(crate) fn cell_ty(&self) -> ValType {
        ValType::Ref(self.cx.types.cell)
    }

    // ------------------------------------------------------------ values

    pub(crate) fn pop(&mut self) -> Val {
        debug_assert!(!self.vals.is_empty(), "value stack underflow");
        self.vals.pop().unwrap_or(Val {
            reg: Reg(0),
            rel: Rel::Keep,
        })
    }

    pub(crate) fn release(&mut self, v: Val) {
        match v.rel {
            Rel::Keep => {}
            Rel::Temp => self.fx.release(v.reg),
            Rel::Win(shape) => self.fx.release_window(shape, v.reg),
        }
    }

    /// The register an expression writes its result to.
    pub(crate) fn result_reg(&mut self, dst: Dst) -> Reg {
        match dst {
            Dst::Reg(r) => r,
            _ => self.fx.temp(ValType::Dyn),
        }
    }

    /// Completes an expression whose result is in `r` (from
    /// [`result_reg`](Self::result_reg)).
    pub(crate) fn produced(&mut self, r: Reg, dst: Dst) {
        match dst {
            Dst::Any | Dst::Temp => self.vals.push(Val {
                reg: r,
                rel: Rel::Temp,
            }),
            Dst::Discard => self.fx.release(r),
            Dst::Reg(_) => {}
        }
    }

    /// Delivers an evaluated value to `dst`; with `dup`, an array is copied
    /// on the way (PHP value semantics).
    pub(crate) fn deliver(&mut self, v: Val, dst: Dst, dup: bool) {
        match dst {
            Dst::Discard => self.release(v),
            Dst::Any if !dup => self.vals.push(v),
            Dst::Any | Dst::Temp => {
                // A temporary or a call window is no variable's register.
                if v.rel != Rel::Keep && self.fx.type_of(v.reg) == ValType::Dyn {
                    if dup {
                        self.dup_into(v.reg, v.reg);
                    }
                    self.vals.push(v);
                } else {
                    let t = self.fx.temp(ValType::Dyn);
                    if dup {
                        self.dup_into(t, v.reg);
                    } else {
                        self.emit(Inst::Mov { dst: t, src: v.reg });
                    }
                    self.release(v);
                    self.vals.push(Val {
                        reg: t,
                        rel: Rel::Temp,
                    });
                }
            }
            Dst::Reg(r) => {
                if dup {
                    self.dup_into(r, v.reg);
                } else if v.reg != r {
                    self.emit(Inst::Mov { dst: r, src: v.reg });
                }
                self.release(v);
            }
        }
    }

    /// The value with arrays copied when `dup` is set, in a register the
    /// caller may hand on.
    pub(crate) fn transfer(&mut self, v: Val, dup: bool) -> Val {
        if !dup {
            return v;
        }
        if v.rel == Rel::Temp && self.fx.type_of(v.reg) == ValType::Dyn {
            self.dup_into(v.reg, v.reg);
            return v;
        }
        let t = self.fx.temp(ValType::Dyn);
        self.dup_into(t, v.reg);
        self.release(v);
        Val {
            reg: t,
            rel: Rel::Temp,
        }
    }

    /// `dst = src`, copying the array if `src` holds one (an O(1)
    /// copy-on-write `dup` in the VM).
    pub(crate) fn dup_into(&mut self, dst: Reg, src: Reg) {
        if dst != src {
            self.emit(Inst::Mov { dst, src });
        }
        let b = self.fx.temp(ValType::Bool);
        let done = self.label();
        self.emit(Inst::IsKind {
            dst: b,
            src,
            kind: Kind::Map,
        });
        self.jump_on(b, done, false);
        self.emit(Inst::Dup { dst, src });
        self.bind(done);
        self.fx.release(b);
    }

    /// Raises `TypeError` (E0100) with a nil payload at the current node.
    pub(crate) fn raise_type_error(&mut self) {
        self.raise_kind(bytecode_lang::ErrorKind::TypeError);
    }

    /// Raises a runtime error of `kind` with a nil payload (`raise`).
    pub(crate) fn raise_kind(&mut self, kind: bytecode_lang::ErrorKind) {
        let n = self.fx.temp(ValType::Dyn);
        self.emit(Inst::LoadNil { dst: n });
        self.emit(Inst::Raise { src: n, kind });
        self.fx.release(n);
    }

    /// Loads an `i64` constant into a typed register.
    pub(crate) fn load_i64(&mut self, dst: Reg, v: i64) {
        match i32::try_from(v) {
            Ok(val) => self.emit(Inst::LoadInt {
                dst,
                val,
                ty: IntTy::I64,
            }),
            Err(_) => {
                let k = self.cx.mb.constant(Const::Int(v));
                self.emit(Inst::LoadConst { dst, k });
            }
        }
    }

    /// Loads a dynamic integer.
    pub(crate) fn load_dyn_int(&mut self, dst: Reg, v: i64) {
        match i32::try_from(v) {
            Ok(val) => self.emit(Inst::DLoadInt { dst, val }),
            Err(_) => {
                let k = self.cx.mb.constant(Const::Int(v));
                self.emit(Inst::DLoadConst { dst, k });
            }
        }
    }

    /// A new `dyn` temporary holding the string `name`.
    pub(crate) fn load_name(&mut self, name: Symbol) -> Reg {
        let text = self.cx.text(name);
        let s = self.cx.mb.string(&text);
        let k = self.cx.mb.constant(Const::Str(s));
        let r = self.fx.temp(ValType::Dyn);
        self.emit(Inst::DLoadConst { dst: r, k });
        r
    }

    /// The per-function name reference of a symbol (for property access).
    pub(crate) fn name_ref(&mut self, name: Symbol) -> bytecode_lang::NameRef {
        let text = self.cx.text(name);
        let s = self.cx.mb.string(&text);
        self.fx.f.name_ref(s)
    }

    // ------------------------------------------------------------ binders

    /// Allocates the variable `b` in the innermost open scope (a shared
    /// variable's register holds its reference).
    pub(crate) fn alloc_binder(&mut self, b: BinderId) -> Slot {
        let cell = self.cx.is_cell(b);
        let ty = if cell { self.cell_ty() } else { ValType::Dyn };
        let reg = self.fx.temp(ty);
        let start = self.label();
        self.bind(start);
        self.fx.scoped.push(Scoped {
            binder: b,
            reg,
            start,
        });
        let slot = if cell {
            Slot::Cell(reg)
        } else {
            Slot::Reg(reg)
        };
        self.cx.set_slot(b, slot);
        slot
    }

    /// Binds `b` to the value in `v`: the variable's first binding allocates
    /// it; a shared variable gets a new reference (a new variable per
    /// binding).
    pub(crate) fn bind_binder(&mut self, b: BinderId, v: Reg) {
        let slot = match self.cx.slot(b) {
            Some(s) => s,
            None => self.alloc_binder(b),
        };
        let dup = self.php();
        match slot {
            Slot::Reg(r) => {
                if dup {
                    self.dup_into(r, v);
                } else if r != v {
                    self.emit(Inst::Mov { dst: r, src: v });
                }
            }
            Slot::Cell(c) => {
                let t = self.fx.temp(ValType::Dyn);
                if dup {
                    self.dup_into(t, v);
                } else {
                    self.emit(Inst::Mov { dst: t, src: v });
                }
                self.emit(Inst::NewRef { dst: c, src: t });
                self.fx.release(t);
            }
            Slot::Global(_) | Slot::GlobalCell(_) => {
                let t = self.fx.temp(ValType::Dyn);
                if dup {
                    self.dup_into(t, v);
                } else {
                    self.emit(Inst::Mov { dst: t, src: v });
                }
                self.write_var(slot, t);
                self.fx.release(t);
            }
            // Patterns never bind a place alias.
            Slot::Place(_) => {}
        }
    }

    /// Reads a variable's value into `dst` (an alias: see
    /// [`read_slot_at`](Self::read_slot_at)).
    pub(crate) fn read_var(&mut self, slot: Slot, dst: Reg) {
        match slot {
            Slot::Reg(r) => {
                if r != dst {
                    self.emit(Inst::Mov { dst, src: r });
                }
            }
            Slot::Cell(c) => self.emit(Inst::CellGet { dst, cell: c }),
            Slot::Global(g) => self.emit(Inst::GetGlobal { dst, global: g }),
            Slot::GlobalCell(g) => {
                let ct = self.cell_ty();
                let c = self.fx.temp(ct);
                self.emit(Inst::GetGlobal { dst: c, global: g });
                self.emit(Inst::CellGet { dst, cell: c });
                self.fx.release(c);
            }
            Slot::Place(_) => {}
        }
    }

    /// Writes a variable (an alias: see
    /// [`write_slot_at`](Self::write_slot_at)).
    pub(crate) fn write_var(&mut self, slot: Slot, src: Reg) {
        match slot {
            Slot::Reg(r) => {
                if r != src {
                    self.emit(Inst::Mov { dst: r, src });
                }
            }
            Slot::Cell(c) => self.emit(Inst::CellSet { cell: c, src }),
            Slot::Global(g) => self.emit(Inst::SetGlobal { global: g, src }),
            Slot::GlobalCell(g) => {
                let ct = self.cell_ty();
                let c = self.fx.temp(ct);
                self.emit(Inst::GetGlobal { dst: c, global: g });
                self.emit(Inst::CellSet { cell: c, src });
                self.fx.release(c);
            }
            Slot::Place(_) => {}
        }
    }

    /// Closes the innermost scope: frees its variables and records their
    /// live ranges in the debug table.
    pub(crate) fn scope_close(&mut self) {
        let Some(mark) = self.fx.scopes.pop() else {
            return;
        };
        if self.fx.scoped.len() <= mark {
            return;
        }
        // The scope's value may be one of its own variables (a block whose
        // tail names a local): move it out before the register is freed.
        if let Some(top) = self.vals.last().copied() {
            let freed = self
                .fx
                .scoped
                .get(mark..)
                .is_some_and(|s| s.iter().any(|x| x.reg == top.reg));
            if top.rel == Rel::Keep && freed {
                let t = self.fx.temp(ValType::Dyn);
                self.emit(Inst::Mov {
                    dst: t,
                    src: top.reg,
                });
                if let Some(v) = self.vals.last_mut() {
                    *v = Val {
                        reg: t,
                        rel: Rel::Temp,
                    };
                }
            }
        }
        let end = self.label();
        self.bind(end);
        let closing: Vec<Scoped> = self.fx.scoped.drain(mark..).collect();
        for s in closing {
            let name = self
                .cx
                .hir
                .binder(s.binder)
                .map(|b| self.cx.text(b.name.sym))
                .unwrap_or_default();
            let name = self.cx.mb.string(&name);
            self.fx.f.local(s.reg, name, s.start, end);
            self.fx.release(s.reg);
        }
    }

    // ------------------------------------------------------------ jumps

    /// Emits a jump that leaves to `leave`, through every `finally` between
    /// here and its target. `value` is the return or break value.
    pub(crate) fn leave(
        &mut self,
        leave: Leave,
        value: Option<Val>,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let (exit, target_depth, target) = match leave {
            Leave::Return => (Exit::Return, 0, None),
            Leave::Break(id) | Leave::Continue(id) => {
                let Some(t) = self.fx.targets.iter().rev().find(|t| t.id == id).copied() else {
                    return Ok(());
                };
                let exit = match leave {
                    Leave::Break(_) => Exit::Break(id, value.is_some()),
                    _ => Exit::Continue(id),
                };
                (exit, t.fin_depth, Some(t))
            }
        };
        let depth = self.fx.fins.len();
        if depth == target_depth {
            match (leave, target) {
                (Leave::Return, _) => {
                    let v = match value {
                        Some(v) => v,
                        None => {
                            let r = self.fx.temp(ValType::Dyn);
                            self.emit(Inst::LoadNil { dst: r });
                            Val {
                                reg: r,
                                rel: Rel::Temp,
                            }
                        }
                    };
                    self.emit(Inst::Ret { src: v.reg });
                    self.release(v);
                }
                (Leave::Break(_), Some(t)) => {
                    match value {
                        Some(v) => {
                            if v.reg != t.result {
                                self.emit(Inst::Mov {
                                    dst: t.result,
                                    src: v.reg,
                                });
                            }
                            self.release(v);
                        }
                        // A `break` without a value makes the target nil.
                        None => self.emit(Inst::LoadNil { dst: t.result }),
                    }
                    self.jmp(t.brk);
                }
                (Leave::Continue(_), Some(t)) => self.jmp(t.cont),
                _ => {}
            }
            return Ok(());
        }
        // Through the innermost `finally`: record the exit, set the pending
        // completion, run the `finally`.
        let Some(fin) = self.fx.fins.last_mut() else {
            return Ok(());
        };
        let n = match fin.exits.iter().position(|&x| x == exit) {
            Some(n) => n,
            None => {
                fin.exits.push(exit);
                fin.exits.len() - 1
            }
        };
        let (kind, val_reg, entry, fin_node) = (fin.kind, fin.value, fin.entry, fin.node);
        let code = match exit {
            Exit::Return => 1,
            _ => 3 + n,
        };
        let code = match i8::try_from(code) {
            Ok(c) => i32::from(c),
            Err(_) => {
                return Err(CompileError::TooManyJumps {
                    node: fin_node,
                    span: self.cx.span(fin_node),
                });
            }
        };
        let _ = node;
        self.emit(Inst::LoadInt {
            dst: kind,
            val: code,
            ty: IntTy::I8,
        });
        match value {
            Some(v) => {
                if v.reg != val_reg {
                    self.emit(Inst::Mov {
                        dst: val_reg,
                        src: v.reg,
                    });
                }
                self.release(v);
            }
            None if exit == Exit::Return => self.emit(Inst::LoadNil { dst: val_reg }),
            None => {}
        }
        self.jmp(entry);
        Ok(())
    }

    /// Queues a job (a closure body, a dynamic entry).
    pub(crate) fn queue(&mut self, job: Job) {
        self.cx.jobs.push_back(job);
    }
}
