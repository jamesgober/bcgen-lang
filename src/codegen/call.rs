//! Calls.
//!
//! **The calling convention.** A function item or closure compiles to one
//! LSB function whose signature is each parameter in a register (`dyn`, or a
//! reference for a by-reference parameter) plus an `i64` presence mask when
//! a parameter has a default, and which carries its **parameter list** (LSB
//! §5.15). A call of a known function arranges its arguments at compile
//! time, by the same binding rules, and `call`s it with a window; every
//! other call (a function value, a method, a known function given spreads or
//! arguments that do not bind) is a dynamic call, `dcall` or `dcall_shape`
//! with a call shape, which the VM binds through the callee's list, raising
//! `ArgumentError` (E0114) when they do not bind. Host functions take their
//! arguments positionally (`call_import`).
//!
//! A place argument (PHP `f($a['k'])`) gives a by-reference parameter a
//! reference to the place: decided at compile time for a known callee, and
//! at run time with `dparam_ref` for a dynamic one, the place's operands
//! evaluated once either way.

use alloc::vec::Vec;

use bytecode_lang::{ArgKind as LArgKind, CallShape, FuncId, ImportId, Inst, Reg, ValType};
use hir_lang::{Arg, ArgKind, ExprId, ItemKind, List, NodeRef, ParamKind, Res, Symbol};
use intern_lang::Lookup;

use super::place::PlaceStep;
use super::{Dst, Gen, Rel, Step, Task, Val};
use crate::error::{CompileError, Unsupported};
use crate::func::FnCx;
use crate::unit::{MAX_ARITY, PInfo};

/// What a direct call runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Direct {
    /// The function (`call`).
    Call(FuncId),
    /// A generator's coroutine body (`coro_new`): the call makes the
    /// coroutine without running it.
    Coro(FuncId),
}

/// Which parameter a place argument of a dynamic call may bind to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ArgAt {
    /// The positional argument at this 0-based position.
    Pos(i64),
    /// The named argument of this name.
    Name(Symbol),
}

/// The continuation steps of a call.
#[derive(Clone, Debug)]
pub(crate) enum CallStep {
    /// A direct call: the arguments are in the window.
    DirectFinish {
        target: Direct,
        win: (u32, Reg),
        argc: u8,
        rest: Option<(Reg, usize)>,
        rest_named: Option<(Reg, usize)>,
        dst: Dst,
        node: NodeRef,
    },
    /// A host call: the arguments are in the window.
    ImportFinish {
        import: ImportId,
        win: (u32, Reg),
        argc: u8,
        dst: Dst,
        node: NodeRef,
    },
    /// The callee (and, for a method, the receiver below it) is on the value
    /// stack: allocate the window and evaluate the arguments into it.
    ValueBegin {
        args: List<Arg>,
        recv: bool,
        dst: Dst,
        node: NodeRef,
    },
    /// The arguments are in the window: the dynamic call.
    ValueFinish {
        win: (u32, Reg),
        kinds: Vec<LArgKind>,
        recv: bool,
        dst: Dst,
        node: NodeRef,
    },
    /// A place argument of a dynamic call, its operands evaluated into place
    /// `idx`: a reference to it when the callee takes that argument by
    /// reference, else its value.
    PlaceArg {
        idx: u32,
        callee: Reg,
        at: ArgAt,
        slot: Reg,
        node: NodeRef,
    },
    /// Looks up a method on the receiver (on the stack) by name.
    Method { name: Symbol, node: NodeRef },
    /// Pops a method name and looks it up on the receiver below it.
    DynMethod { node: NodeRef },
}

/// Where an argument of a direct call goes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum To {
    /// Parameter `n`.
    Param(usize),
    /// The rest parameter, positionally (under the next integer key).
    Rest,
    /// The rest parameter, under its name (PHP 8.1: no named rest).
    RestNamedInRest(Symbol),
    /// The named rest parameter, under its name.
    RestNamed(Symbol),
}

/// Matches arguments to parameters at compile time by LSB §5.15's binding
/// rules (the ones the VM applies to a dynamic call); `None` if the call
/// must bind at run time (a spread, a by-reference rest parameter) or does
/// not bind (the VM then raises `ArgumentError` at the call).
fn arrange(params: &[PInfo], args: &[Arg]) -> Option<(Vec<To>, u64)> {
    let mut filled = alloc::vec![false; params.len()];
    let positional: Vec<usize> = (0..params.len())
        .filter(|&i| params.get(i).is_some_and(PInfo::positional))
        .collect();
    let rest = params.iter().position(|p| p.kind == ParamKind::Rest);
    let rest_named = params.iter().position(|p| p.kind == ParamKind::RestNamed);
    if params.iter().any(|p| p.rest() && p.by_ref) {
        return None;
    }
    let mut next = 0usize;
    let mut named_seen = false;
    let mut out = Vec::with_capacity(args.len());
    for a in args {
        match a.kind {
            ArgKind::Positional => {
                if named_seen {
                    return None;
                }
                match positional.get(next) {
                    Some(&j) => {
                        next += 1;
                        *filled.get_mut(j)? = true;
                        out.push(To::Param(j));
                    }
                    None => {
                        let r = rest?;
                        *filled.get_mut(r)? = true;
                        out.push(To::Rest);
                    }
                }
            }
            ArgKind::Named(id) => {
                named_seen = true;
                match params
                    .iter()
                    .position(|p| p.nameable() && p.name == Some(id.sym))
                {
                    Some(j) => {
                        let f = filled.get_mut(j)?;
                        if *f {
                            return None;
                        }
                        *f = true;
                        out.push(To::Param(j));
                    }
                    None => match (rest_named, rest) {
                        (Some(r), _) => {
                            *filled.get_mut(r)? = true;
                            out.push(To::RestNamed(id.sym));
                        }
                        (None, Some(r)) => {
                            *filled.get_mut(r)? = true;
                            out.push(To::RestNamedInRest(id.sym));
                        }
                        (None, None) => return None,
                    },
                }
            }
            ArgKind::Spread | ArgKind::SpreadNamed => return None,
        }
    }
    let mut mask = 0u64;
    for (i, p) in params.iter().enumerate() {
        let f = filled.get(i).copied().unwrap_or(false);
        if p.required() && !f {
            return None;
        }
        if f && i < 64 {
            mask |= 1 << i;
        }
    }
    Some((out, mask))
}

impl<L: Lookup> Gen<'_, '_, L> {
    /// A call expression.
    pub(crate) fn call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        args: List<Arg>,
        dst: Dst,
    ) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        let hir = self.cx.hir;
        if let hir_lang::Expr::Path(p) = *hir.expr(callee) {
            let path = *hir.path(p);
            let cnode = NodeRef::Expr(callee);
            if path.unresolved == 0 {
                match path.res {
                    Res::Extern(sym) => {
                        let (module, name) = self.cx.host_name(sym);
                        return self.import_call(&module, &name, args, dst, node);
                    }
                    Res::Def(_) => {
                        if let Some(item) = self.cx.local_item(path.res, cnode)? {
                            if let ItemKind::Fn(def) = hir.item(item).kind {
                                if def.body.is_none() {
                                    let it = *hir.item(item);
                                    let name =
                                        it.name.map(|n| self.cx.text(n.sym)).unwrap_or_default();
                                    let module = match def.abi {
                                        Some(a) => self.cx.text(a),
                                        None => {
                                            alloc::string::String::from(self.cx.opts.host_module())
                                        }
                                    };
                                    return self.import_call(&module, &name, args, dst, node);
                                }
                                return self.direct_call(item, args, dst, node);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        // A function value.
        self.sched([
            Task::Expr(callee, Dst::Temp),
            Task::Step(Step::Call(CallStep::ValueBegin {
                args,
                recv: false,
                dst,
                node,
            })),
        ]);
        Ok(())
    }

    /// `receiver.method(args)` or `receiver->$name(args)`: the method is
    /// looked up on the receiver (`get_prop`, or a dynamic index for a
    /// computed name) and called with the receiver as its first argument.
    pub(crate) fn method_call(
        &mut self,
        e: ExprId,
        receiver: ExprId,
        name: Option<Symbol>,
        dyn_name: Option<ExprId>,
        args: List<Arg>,
        dst: Dst,
    ) {
        let node = NodeRef::Expr(e);
        let begin = Task::Step(Step::Call(CallStep::ValueBegin {
            args,
            recv: true,
            dst,
            node,
        }));
        match (name, dyn_name) {
            (Some(name), _) => self.sched([
                Task::Expr(receiver, Dst::Temp),
                Task::Step(Step::Call(CallStep::Method { name, node })),
                begin,
            ]),
            (None, Some(n)) => self.sched([
                Task::Expr(receiver, Dst::Temp),
                Task::Expr(n, Dst::Any),
                Task::Step(Step::Call(CallStep::DynMethod { node })),
                begin,
            ]),
            (None, None) => {}
        }
    }

    fn import_call(
        &mut self,
        module: &str,
        name: &str,
        args: List<Arg>,
        dst: Dst,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let list = self.cx.hir.list(args);
        if list.iter().any(|a| a.kind != ArgKind::Positional) {
            return Err(self.cx.unsupported(Unsupported::ExternArgs, node));
        }
        if list.len() > MAX_ARITY {
            return Err(self.too_many_args(node));
        }
        let argc = u8::try_from(list.len()).unwrap_or(u8::MAX);
        let import = self.cx.import(module, name, argc);
        let shape = alloc::vec![ValType::Dyn; list.len() + 1];
        let win = self.fx.window(&shape);
        self.tasks
            .push(Task::Step(Step::Call(CallStep::ImportFinish {
                import,
                win,
                argc,
                dst,
                node,
            })));
        for (i, a) in list.iter().enumerate().rev() {
            let slot = FnCx::slot(win.1, i + 1);
            let t = self.store_expr_tasks(a.value, slot);
            self.tasks.push(t[1].clone());
            self.tasks.push(t[0].clone());
        }
        Ok(())
    }

    pub(crate) fn too_many_args(&self, node: NodeRef) -> CompileError {
        CompileError::TooManyArgs {
            node,
            span: self.cx.span(node),
            limit: MAX_ARITY as u32,
        }
    }

    fn direct_call(
        &mut self,
        item: hir_lang::ItemId,
        args: List<Arg>,
        dst: Dst,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let hir = self.cx.hir;
        let list = hir.list(args);
        let Some(info) = self.cx.fns.get(&item).cloned() else {
            return Ok(());
        };
        let Some(callable) = info.callable else {
            return Ok(());
        };
        let Some((dests, mask)) = arrange(&info.params, list) else {
            // Spreads, or arguments that do not bind: a dynamic call of the
            // function value binds them at run time (or raises
            // `ArgumentError` there).
            let f = self.fx.temp(ValType::Dyn);
            self.emit(Inst::MakeClosure {
                dst: f,
                func: callable,
            });
            self.vals.push(Val {
                reg: f,
                rel: Rel::Temp,
            });
            return self.call_step(CallStep::ValueBegin {
                args,
                recv: false,
                dst,
                node,
            });
        };
        let target = match info.gen_body {
            Some(g) => Direct::Coro(g),
            None => Direct::Call(callable),
        };
        let mut shape: Vec<ValType> = alloc::vec![ValType::Dyn];
        shape.extend_from_slice(&info.sig);
        let win = self.fx.window(&shape);
        let n = info.params.len();
        // Absent parameters are nil; the mask says which are present.
        for i in 0..n {
            let filled = i < 64 && mask & (1 << i) != 0;
            let is_rest = info.params.get(i).is_some_and(PInfo::rest);
            if !filled && !is_rest {
                self.emit(Inst::LoadNil {
                    dst: FnCx::slot(win.1, i + 1),
                });
            }
        }
        if info.has_mask {
            let m = FnCx::slot(win.1, n + 1);
            self.load_i64(m, mask as i64);
        }
        let mut rest = None;
        let mut rest_named = None;
        for (i, p) in info.params.iter().enumerate() {
            match p.kind {
                ParamKind::Rest => rest = Some((self.new_map(), i)),
                ParamKind::RestNamed => rest_named = Some((self.new_map(), i)),
                _ => {}
            }
        }
        let argc = u8::try_from(info.sig.len()).unwrap_or(u8::MAX);
        self.tasks
            .push(Task::Step(Step::Call(CallStep::DirectFinish {
                target,
                win,
                argc,
                rest,
                rest_named,
                dst,
                node,
            })));
        let mut ts: Vec<Task> = Vec::with_capacity(list.len() * 2);
        for (a, to) in list.iter().zip(dests.iter()) {
            match *to {
                To::Param(j) => {
                    let slot = FnCx::slot(win.1, j + 1);
                    let by_ref = info.params.get(j).is_some_and(|p| p.by_ref);
                    if by_ref && a.place {
                        // A reference to the caller's place.
                        let (pts, idx) = self.place_tasks(a.value, true)?;
                        ts.extend(pts);
                        ts.push(Task::Step(Step::Place(PlaceStep::Ref { idx, node })));
                        ts.push(Task::Deliver {
                            dst: Dst::Reg(slot),
                            dup: false,
                        });
                        ts.push(Task::Step(Step::Place(PlaceStep::Drop { idx })));
                    } else if by_ref {
                        // A value: a temporary reference (LSB §5.15 step 5).
                        let dup = self.needs_dup(a.value);
                        ts.push(Task::Expr(a.value, Dst::Any));
                        ts.push(Task::NewCell { cell: slot, dup });
                    } else {
                        ts.extend(self.store_expr_tasks(a.value, slot));
                    }
                }
                To::Rest => {
                    if let Some((map, _)) = rest {
                        let dup = self.needs_dup(a.value);
                        ts.push(Task::Expr(a.value, Dst::Any));
                        ts.push(Task::MapPush { map, dup, node });
                    }
                }
                To::RestNamed(name) | To::RestNamedInRest(name) => {
                    let into = if matches!(to, To::RestNamed(_)) {
                        rest_named
                    } else {
                        rest
                    };
                    if let Some((map, _)) = into {
                        let dup = self.needs_dup(a.value);
                        ts.push(Task::Expr(a.value, Dst::Any));
                        ts.push(Task::MapSetName {
                            map,
                            name,
                            dup,
                            node,
                        });
                    }
                }
            }
        }
        self.sched_all(ts);
        Ok(())
    }

    /// Schedules the arguments of a dynamic call whose callee (and receiver)
    /// are on the value stack.
    fn value_begin(
        &mut self,
        args: List<Arg>,
        recv: bool,
        dst: Dst,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let list = self.cx.hir.list(args);
        let n = list.len() + usize::from(recv);
        if n > MAX_ARITY {
            return Err(self.too_many_args(node));
        }
        let callee = self.vals.last().copied().map_or(Reg(0), |v| v.reg);
        let shape = alloc::vec![ValType::Dyn; n + 1];
        let win = self.fx.window(&shape);
        let mut kinds: Vec<LArgKind> = Vec::with_capacity(n);
        if recv {
            // The receiver is the first argument; it lies below the callee.
            let at = self.vals.len().saturating_sub(2);
            if let Some(&r) = self.vals.get(at) {
                let slot = FnCx::slot(win.1, 1);
                if self.php() {
                    self.dup_into(slot, r.reg);
                } else {
                    self.emit(Inst::Mov {
                        dst: slot,
                        src: r.reg,
                    });
                }
            }
            kinds.push(LArgKind::Positional);
        }
        let mut pos = i64::from(recv);
        let mut spread = false;
        let mut ts: Vec<Task> = Vec::with_capacity(list.len() * 2);
        for (i, a) in list.iter().enumerate() {
            let slot = FnCx::slot(win.1, i + 1 + usize::from(recv));
            let at = match a.kind {
                ArgKind::Positional => {
                    kinds.push(LArgKind::Positional);
                    pos += 1;
                    // After a spread the position is known only at run
                    // time: such a place argument is passed by value.
                    (!spread).then_some(ArgAt::Pos(pos - 1))
                }
                ArgKind::Named(id) => {
                    let text = self.cx.text(id.sym);
                    let s = self.cx.mb.string(&text);
                    kinds.push(LArgKind::Named(s));
                    Some(ArgAt::Name(id.sym))
                }
                ArgKind::Spread | ArgKind::SpreadNamed => {
                    kinds.push(if a.kind == ArgKind::Spread {
                        LArgKind::Spread
                    } else {
                        LArgKind::SpreadNamed
                    });
                    spread = true;
                    // The container is only read (its elements bind).
                    ts.push(Task::Expr(a.value, Dst::Reg(slot)));
                    ts.push(Task::At(node));
                    continue;
                }
            };
            match (a.place, at) {
                (true, Some(at)) => {
                    let (pts, idx) = self.place_tasks(a.value, true)?;
                    ts.extend(pts);
                    ts.push(Task::Step(Step::Call(CallStep::PlaceArg {
                        idx,
                        callee,
                        at,
                        slot,
                        node,
                    })));
                }
                _ => ts.extend(self.store_expr_tasks(a.value, slot)),
            }
        }
        ts.push(Task::Step(Step::Call(CallStep::ValueFinish {
            win,
            kinds,
            recv,
            dst,
            node,
        })));
        self.sched_all(ts);
        Ok(())
    }

    pub(crate) fn call_step(&mut self, s: CallStep) -> Result<(), CompileError> {
        match s {
            CallStep::DirectFinish {
                target,
                win,
                argc,
                rest,
                rest_named,
                dst,
                node,
            } => {
                self.at(node);
                for (map, i) in [rest, rest_named].into_iter().flatten() {
                    self.emit(Inst::Mov {
                        dst: FnCx::slot(win.1, i + 1),
                        src: map,
                    });
                    self.fx.release(map);
                }
                match target {
                    Direct::Call(func) => self.emit(Inst::Call {
                        dst: win.1,
                        func,
                        argc,
                    }),
                    Direct::Coro(func) => self.emit(Inst::CoroNew {
                        dst: win.1,
                        func,
                        argc,
                    }),
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
            CallStep::ImportFinish {
                import,
                win,
                argc,
                dst,
                node,
            } => {
                self.at(node);
                self.emit(Inst::CallImport {
                    dst: win.1,
                    import,
                    argc,
                });
                self.deliver(
                    Val {
                        reg: win.1,
                        rel: Rel::Win(win.0),
                    },
                    dst,
                    false,
                );
            }
            CallStep::ValueBegin {
                args,
                recv,
                dst,
                node,
            } => {
                self.at(node);
                self.value_begin(args, recv, dst, node)?;
            }
            CallStep::ValueFinish {
                win,
                kinds,
                recv,
                dst,
                node,
            } => {
                self.at(node);
                let callee = self.pop();
                let argc = u8::try_from(kinds.len()).unwrap_or(u8::MAX);
                if kinds.iter().all(|k| *k == LArgKind::Positional) {
                    self.emit(Inst::DCall {
                        dst: win.1,
                        callee: callee.reg,
                        argc,
                    });
                } else if CallShape::new(kinds.clone()).validate().is_ok() {
                    let shape = self.fx.f.call_shape(&kinds);
                    self.emit(Inst::DCallShape {
                        dst: win.1,
                        callee: callee.reg,
                        shape,
                    });
                } else {
                    // A positional or spread argument after a named one:
                    // what the binder raises (LSB §5.15 step 3a), once every
                    // argument was evaluated.
                    self.raise_kind(bytecode_lang::ErrorKind::ArgumentError);
                }
                self.release(callee);
                if recv {
                    let r = self.pop();
                    self.release(r);
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
            CallStep::PlaceArg {
                idx,
                callee,
                at,
                slot,
                node,
            } => {
                self.at(node);
                let b = self.fx.temp(ValType::Bool);
                match at {
                    ArgAt::Pos(p) => {
                        let r = self.fx.temp(ValType::I64);
                        self.load_i64(r, p);
                        self.emit(Inst::DParamRef {
                            dst: b,
                            callee,
                            pos: r,
                        });
                        self.fx.release(r);
                    }
                    ArgAt::Name(name) => {
                        let n = self.name_ref(name);
                        self.emit(Inst::DParamRefNamed {
                            dst: b,
                            callee,
                            name: n,
                        });
                    }
                }
                let by_val = self.label();
                let done = self.label();
                self.jump_on(b, by_val, false);
                self.fx.release(b);
                self.tasks
                    .push(Task::Step(Step::Place(PlaceStep::Drop { idx })));
                self.tasks.push(Task::Bind(done));
                // By value: the place's current value, copied (PHP).
                self.tasks.push(Task::Deliver {
                    dst: Dst::Reg(slot),
                    dup: self.php(),
                });
                self.tasks
                    .push(Task::Step(Step::Place(PlaceStep::Read { idx, node })));
                self.tasks.push(Task::Bind(by_val));
                self.tasks.push(Task::Jump(done));
                self.tasks.push(Task::Deliver {
                    dst: Dst::Reg(slot),
                    dup: false,
                });
                self.tasks
                    .push(Task::Step(Step::Place(PlaceStep::Ref { idx, node })));
            }
            CallStep::Method { name, node } => {
                self.at(node);
                let recv = self.vals.last().copied().unwrap_or(Val {
                    reg: Reg(0),
                    rel: Rel::Keep,
                });
                let f = self.fx.temp(ValType::Dyn);
                let name = self.name_ref(name);
                self.emit(Inst::GetProp {
                    dst: f,
                    obj: recv.reg,
                    name,
                });
                self.vals.push(Val {
                    reg: f,
                    rel: Rel::Temp,
                });
            }
            CallStep::DynMethod { node } => {
                self.at(node);
                let name = self.pop();
                let recv = self.vals.last().copied().unwrap_or(Val {
                    reg: Reg(0),
                    rel: Rel::Keep,
                });
                let f = self.fx.temp(ValType::Dyn);
                self.emit(Inst::DGetIndex {
                    dst: f,
                    obj: recv.reg,
                    key: name.reg,
                });
                self.release(name);
                self.vals.push(Val {
                    reg: f,
                    rel: Rel::Temp,
                });
            }
        }
        Ok(())
    }

    /// Tests presence bit `i` of `mask` into the `bool` register `b`.
    pub(crate) fn test_bit(&mut self, mask: Reg, i: usize, b: Reg) {
        let bit = self.fx.temp(ValType::I64);
        let zero = self.fx.temp(ValType::I64);
        let v = 1i64.wrapping_shl(u32::try_from(i).unwrap_or(63));
        self.load_i64(bit, v);
        self.load_i64(zero, 0);
        self.emit(Inst::IAnd {
            dst: bit,
            lhs: mask,
            rhs: bit,
            op: bytecode_lang::IntOp::new(bytecode_lang::IntTy::I64),
        });
        self.emit(Inst::INe {
            dst: b,
            lhs: bit,
            rhs: zero,
            ty: bytecode_lang::IntTy::I64,
        });
        self.fx.release(zero);
        self.fx.release(bit);
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use hir_lang::{Arg, ArgKind, ExprId, Ident, ParamId, ParamKind, PatId, Span, Symbol};

    use super::{To, arrange};
    use crate::unit::PInfo;

    fn sym(i: u32) -> Symbol {
        Symbol::from_u32(i + 1).unwrap_or_else(|| panic!("symbol"))
    }

    fn param(i: u32, kind: ParamKind, default: bool) -> PInfo {
        PInfo {
            id: ParamId::from_index(i as usize).unwrap_or_else(|| panic!("id")),
            kind,
            name: Some(sym(i)),
            by_ref: false,
            default: default.then(|| ExprId::from_index(0).unwrap_or_else(|| panic!("id"))),
            pat: PatId::from_index(0).unwrap_or_else(|| panic!("id")),
        }
    }

    fn pos() -> Arg {
        Arg::positional(ExprId::from_index(0).unwrap_or_else(|| panic!("id")))
    }

    fn named(i: u32) -> Arg {
        Arg {
            kind: ArgKind::Named(Ident::new(sym(i), Span::empty(0))),
            ..pos()
        }
    }

    #[test]
    fn positional_named_rest_and_defaults() {
        let ps = [
            param(0, ParamKind::Normal, false),
            param(1, ParamKind::Normal, true),
            param(2, ParamKind::Rest, false),
            param(3, ParamKind::NamedOnly, true),
        ];
        let (to, mask) =
            arrange(&ps, &[pos(), pos(), pos(), named(3)]).unwrap_or_else(|| panic!("fits"));
        assert_eq!(to, [To::Param(0), To::Param(1), To::Rest, To::Param(3)]);
        // The rest parameter's bit is set when it received an argument.
        assert_eq!(mask, 0b1111);
        // A default may be omitted; a required parameter may not.
        assert!(arrange(&ps, &[pos()]).is_some());
        assert!(arrange(&ps, &[named(3)]).is_none());
        // An unknown name goes to the rest map when there is no named rest.
        let (to, _) = arrange(&ps, &[pos(), named(9)]).unwrap_or_else(|| panic!("fits"));
        assert_eq!(to, [To::Param(0), To::RestNamedInRest(sym(9))]);
    }

    #[test]
    fn duplicates_unknown_names_and_spreads_bind_at_run_time() {
        let ps = [
            param(0, ParamKind::Normal, false),
            param(1, ParamKind::PositionalOnly, true),
        ];
        // A positional argument after a named one.
        assert!(arrange(&ps, &[named(0), pos()]).is_none());
        // A positional-only parameter cannot be named.
        assert!(arrange(&ps, &[pos(), named(1)]).is_none());
        // Too many positionals without a rest.
        assert!(arrange(&ps, &[pos(), pos(), pos()]).is_none());
        let spread = Arg {
            kind: ArgKind::Spread,
            ..pos()
        };
        assert!(arrange(&ps, &[spread]).is_none());
        let empty: Vec<Arg> = Vec::new();
        assert!(arrange(&[], &empty).is_some());
    }
}
