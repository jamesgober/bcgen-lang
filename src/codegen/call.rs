//! Calls.
//!
//! **The calling convention.** A function item compiles to a direct-call
//! function taking each parameter in a register (`dyn`, or a cell for a
//! by-reference parameter) plus an `i64` presence mask when a parameter has
//! a default; a call of a known function arranges its arguments at compile
//! time and `call`s it with a window (LSB §1.3). Every function *value*
//! (closures, function items used as values) takes one convention instead:
//! an argument packet `(positional: map, named: map or nil)`, unpacked by
//! the callee's prologue, so a dynamic call (`dcall`, whose arity LSB checks
//! exactly) works whatever the callee's parameters are. Host functions take
//! their arguments positionally (`call_import`).

use alloc::vec::Vec;

use bytecode_lang::{FuncId, ImportId, Inst, Kind, Label, Reg, ValType};
use hir_lang::{Arg, ArgKind, ExprId, ItemKind, List, NodeRef, Res, Symbol};
use intern_lang::Lookup;

use super::{Dst, Gen, Rel, Step, Task, Val};
use crate::error::{CompileError, Unsupported};
use crate::func::FnCx;
use crate::unit::{PInfo, Slot};

/// How a packet call reaches its callee.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Via {
    /// Through a function value on the value stack (`dcall`); `recv` when a
    /// method's receiver lies below it.
    Value { recv: bool },
    /// Directly to a function item's dynamic entry.
    Direct(FuncId),
}

/// The continuation steps of a call.
#[derive(Clone, Debug)]
pub(crate) enum CallStep {
    /// A direct call: the arguments are in the window.
    DirectFinish {
        func: FuncId,
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
    /// The callee (and receiver) are evaluated: build the packet.
    PacketBegin {
        args: List<Arg>,
        via: Via,
        dst: Dst,
        node: NodeRef,
    },
    /// The packet is built: call.
    PacketFinish {
        pos: Reg,
        named: Option<Reg>,
        via: Via,
        dst: Dst,
        node: NodeRef,
    },
    /// Pops a sequence and appends its values to the packet.
    Spread { pos: Reg, node: NodeRef },
    /// Pops a map and adds its string-keyed entries as named arguments.
    SpreadNamed { named: Reg, node: NodeRef },
    /// Looks up a method on the receiver (on the stack) by name.
    Method { name: Symbol, node: NodeRef },
    /// Pops a method name and looks it up on the receiver below it.
    DynMethod { node: NodeRef },
}

/// Where an argument of a direct call goes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum To {
    Param(usize),
    Rest,
    RestNamed(Symbol),
}

/// Matches arguments to parameters at compile time, by the rules the
/// dynamic prologue applies at run time; `None` if they do not match (the
/// call then goes through the packet, whose prologue raises the error).
fn arrange(params: &[PInfo], args: &[Arg]) -> Option<(Vec<To>, u64)> {
    let mut filled = alloc::vec![false; params.len()];
    let positional: Vec<usize> = (0..params.len())
        .filter(|&i| params.get(i).is_some_and(PInfo::positional))
        .collect();
    let rest = params.iter().any(|p| p.kind == hir_lang::ParamKind::Rest);
    let rest_named = params
        .iter()
        .any(|p| p.kind == hir_lang::ParamKind::RestNamed);
    let mut next = 0usize;
    let mut out = Vec::with_capacity(args.len());
    for a in args {
        match a.kind {
            ArgKind::Positional => match positional.get(next) {
                Some(&j) => {
                    next += 1;
                    // A named argument earlier in the list may have filled
                    // it: the error the packet prologue raises.
                    let f = filled.get_mut(j)?;
                    if *f {
                        return None;
                    }
                    *f = true;
                    out.push(To::Param(j));
                }
                None if rest => out.push(To::Rest),
                None => return None,
            },
            ArgKind::Named(id) => {
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
                    None if rest_named => out.push(To::RestNamed(id.sym)),
                    None => return None,
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
            Task::Step(Step::Call(CallStep::PacketBegin {
                args,
                via: Via::Value { recv: false },
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
        let begin = Task::Step(Step::Call(CallStep::PacketBegin {
            args,
            via: Via::Value { recv: true },
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
        if list.iter().any(|a| a.kind != ArgKind::Positional) || list.len() > usize::from(u8::MAX) {
            return Err(self.cx.unsupported(Unsupported::ExternArgs, node));
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
        let Some(func) = info.body else {
            return Ok(());
        };
        let arranged = arrange(&info.params, list);
        let Some((dests, mask)) = arranged else {
            // Spreads, or arguments that do not fit: the dynamic entry binds
            // them at run time (and raises the error, if any).
            let Some(entry) = self.cx.dyn_entry(item) else {
                return Ok(());
            };
            self.packet_args(args, Via::Direct(entry), dst, node)?;
            return Ok(());
        };
        let mut shape: Vec<ValType> = alloc::vec![ValType::Dyn];
        shape.extend_from_slice(&info.sig);
        let win = self.fx.window(&shape);
        let n = info.params.len();
        // Absent parameters are nil; the mask says which are present.
        for i in 0..n {
            let filled = i < 64 && mask & (1 << i) != 0;
            let is_rest = info.params.get(i).is_some_and(|p| {
                matches!(
                    p.kind,
                    hir_lang::ParamKind::Rest | hir_lang::ParamKind::RestNamed
                )
            });
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
                hir_lang::ParamKind::Rest => rest = Some((self.new_map(), i)),
                hir_lang::ParamKind::RestNamed => rest_named = Some((self.new_map(), i)),
                _ => {}
            }
        }
        let argc = u8::try_from(info.sig.len()).unwrap_or(u8::MAX);
        self.tasks
            .push(Task::Step(Step::Call(CallStep::DirectFinish {
                func,
                win,
                argc,
                rest,
                rest_named,
                dst,
                node,
            })));
        for (a, to) in list.iter().zip(dests.iter()).rev() {
            match *to {
                To::Param(j) => {
                    let slot = FnCx::slot(win.1, j + 1);
                    let by_ref = info.params.get(j).is_some_and(|p| p.by_ref);
                    if by_ref {
                        match self.place_cell(a)? {
                            Some(c) => self.push_cell_into(c, slot),
                            None if a.place => {
                                return Err(self
                                    .cx
                                    .unsupported(Unsupported::RefPlace, NodeRef::Expr(a.value)));
                            }
                            None => {
                                let dup = self.needs_dup(a.value);
                                self.tasks.push(Task::NewCell { cell: slot, dup });
                                self.tasks.push(Task::Expr(a.value, Dst::Any));
                            }
                        }
                    } else {
                        let t = self.store_expr_tasks(a.value, slot);
                        self.tasks.push(t[1].clone());
                        self.tasks.push(t[0].clone());
                    }
                }
                To::Rest => {
                    if let Some((map, _)) = rest {
                        let dup = self.needs_dup(a.value);
                        self.tasks.push(Task::MapPush { map, dup, node });
                        self.tasks.push(Task::Expr(a.value, Dst::Any));
                    }
                }
                To::RestNamed(name) => {
                    if let Some((map, _)) = rest_named {
                        let dup = self.needs_dup(a.value);
                        self.tasks.push(Task::MapSetName {
                            map,
                            name,
                            dup,
                            node,
                        });
                        self.tasks.push(Task::Expr(a.value, Dst::Any));
                    }
                }
            }
        }
        Ok(())
    }

    /// The variable a place argument shares by reference, if it is one that
    /// lives in a cell (a shared local, or a global or static shared by
    /// reference).
    fn place_cell(&self, a: &Arg) -> Result<Option<Slot>, CompileError> {
        if !a.place {
            return Ok(None);
        }
        let hir = self.cx.hir;
        if let hir_lang::Expr::Path(p) = *hir.expr(a.value) {
            let res = hir.path(p).res;
            let slot = match res {
                Res::Local(b) => self.cx.slot(b),
                Res::Def(_) => match self.cx.local_item(res, NodeRef::Path(p))? {
                    Some(i) if matches!(hir.item(i).kind, ItemKind::Global { .. }) => {
                        self.cx.global_slot(i)
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some(s @ (Slot::Cell(_) | Slot::GlobalCell(_))) = slot {
                return Ok(Some(s));
            }
        }
        Ok(None)
    }

    /// Schedules moving a shared variable's cell into `dst`.
    fn push_cell_into(&mut self, slot: Slot, dst: Reg) {
        match slot {
            Slot::Cell(c) => self.tasks.push(Task::Emit(Inst::Mov { dst, src: c })),
            Slot::GlobalCell(g) => self
                .tasks
                .push(Task::Emit(Inst::GetGlobal { dst, global: g })),
            Slot::Reg(_) | Slot::Global(_) => {}
        }
    }

    /// Schedules the packet of a call whose callee (and receiver) are, or
    /// will be, on the value stack.
    fn packet_args(
        &mut self,
        args: List<Arg>,
        via: Via,
        dst: Dst,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let list = self.cx.hir.list(args);
        let pos = self.new_map();
        if let Via::Value { recv: true } = via {
            // The receiver is the first argument; it lies below the callee.
            let at = self.vals.len().saturating_sub(2);
            if let Some(&r) = self.vals.get(at) {
                let dup = self.php();
                let t = self.fx.temp(ValType::Dyn);
                if dup {
                    self.dup_into(t, r.reg);
                } else {
                    self.emit(Inst::Mov { dst: t, src: r.reg });
                }
                self.emit(Inst::MapPush { map: pos, src: t });
                self.fx.release(t);
            }
        }
        let named = if list
            .iter()
            .any(|a| matches!(a.kind, ArgKind::Named(_) | ArgKind::SpreadNamed))
        {
            Some(self.new_map())
        } else {
            None
        };
        self.tasks
            .push(Task::Step(Step::Call(CallStep::PacketFinish {
                pos,
                named,
                via,
                dst,
                node,
            })));
        for a in list.iter().rev() {
            match a.kind {
                ArgKind::Positional => match self.place_cell(a)? {
                    // A shared variable passed as a place: its cell, so a
                    // by-reference parameter aliases it.
                    Some(c) => {
                        let cell_ty = self.cell_ty();
                        let t = self.fx.temp(cell_ty);
                        self.tasks.push(Task::Free(t));
                        self.tasks
                            .push(Task::Emit(Inst::MapPush { map: pos, src: t }));
                        self.push_cell_into(c, t);
                    }
                    None => {
                        let dup = self.needs_dup(a.value);
                        self.tasks.push(Task::MapPush {
                            map: pos,
                            dup,
                            node,
                        });
                        self.tasks.push(Task::Expr(a.value, Dst::Any));
                    }
                },
                ArgKind::Named(id) => {
                    let map = named.unwrap_or(pos);
                    let dup = self.needs_dup(a.value);
                    match self.place_cell(a)? {
                        Some(c) => {
                            let cell_ty = self.cell_ty();
                            let t = self.fx.temp(cell_ty);
                            self.tasks.push(Task::MapSetName {
                                map,
                                name: id.sym,
                                dup: false,
                                node,
                            });
                            self.tasks.push(Task::Push(Val {
                                reg: t,
                                rel: Rel::Temp,
                            }));
                            self.push_cell_into(c, t);
                        }
                        None => {
                            self.tasks.push(Task::MapSetName {
                                map,
                                name: id.sym,
                                dup,
                                node,
                            });
                            self.tasks.push(Task::Expr(a.value, Dst::Any));
                        }
                    }
                }
                ArgKind::Spread => {
                    self.tasks
                        .push(Task::Step(Step::Call(CallStep::Spread { pos, node })));
                    self.tasks.push(Task::Expr(a.value, Dst::Temp));
                }
                ArgKind::SpreadNamed => {
                    let named = named.unwrap_or(pos);
                    self.tasks
                        .push(Task::Step(Step::Call(CallStep::SpreadNamed {
                            named,
                            node,
                        })));
                    self.tasks.push(Task::Expr(a.value, Dst::Temp));
                }
            }
        }
        Ok(())
    }

    pub(crate) fn call_step(&mut self, s: CallStep) -> Result<(), CompileError> {
        match s {
            CallStep::DirectFinish {
                func,
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
                self.emit(Inst::Call {
                    dst: win.1,
                    func,
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
            CallStep::PacketBegin {
                args,
                via,
                dst,
                node,
            } => {
                self.at(node);
                self.packet_args(args, via, dst, node)?;
            }
            CallStep::PacketFinish {
                pos,
                named,
                via,
                dst,
                node,
            } => {
                self.at(node);
                let win = self.fx.window(&[ValType::Dyn, ValType::Dyn, ValType::Dyn]);
                self.emit(Inst::Mov {
                    dst: FnCx::slot(win.1, 1),
                    src: pos,
                });
                match named {
                    Some(m) => self.emit(Inst::Mov {
                        dst: FnCx::slot(win.1, 2),
                        src: m,
                    }),
                    None => self.emit(Inst::LoadNil {
                        dst: FnCx::slot(win.1, 2),
                    }),
                }
                match via {
                    Via::Direct(func) => self.emit(Inst::Call {
                        dst: win.1,
                        func,
                        argc: 2,
                    }),
                    Via::Value { recv } => {
                        let callee = self.pop();
                        self.emit(Inst::DCall {
                            dst: win.1,
                            callee: callee.reg,
                            argc: 2,
                        });
                        self.release(callee);
                        if recv {
                            let r = self.pop();
                            self.release(r);
                        }
                    }
                }
                self.fx.release(pos);
                if let Some(m) = named {
                    self.fx.release(m);
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
            CallStep::Spread { pos, node } => {
                self.at(node);
                let v = self.pop();
                self.spread(pos, v.reg, false);
                self.release(v);
            }
            CallStep::SpreadNamed { named, node } => {
                self.at(node);
                let v = self.pop();
                self.spread(named, v.reg, true);
                self.release(v);
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

    /// Appends the values of the collection in `src` to the packet map
    /// `into` (`named`: its string-keyed entries, as named arguments; a key
    /// that is not a string is a `TypeError`).
    fn spread(&mut self, into: Reg, src: Reg, named: bool) {
        let it = self.fx.temp(ValType::Dyn);
        let has = self.fx.temp(ValType::Bool);
        let v = self.fx.temp(ValType::Dyn);
        let top = self.label();
        let done = self.label();
        self.emit(Inst::DIterNew { dst: it, src });
        self.bind(top);
        self.emit(Inst::IterNext {
            has,
            iter: it,
            val: v,
        });
        self.jump_on(has, done, false);
        if self.php() {
            self.dup_into(v, v);
        }
        if named {
            let k = self.fx.temp(ValType::Dyn);
            let ok = self.label();
            self.emit(Inst::IterKey { dst: k, iter: it });
            self.emit(Inst::IsKind {
                dst: has,
                src: k,
                kind: Kind::Str,
            });
            self.jump_on(has, ok, true);
            self.raise_type_error();
            self.bind(ok);
            self.emit(Inst::MapSet {
                map: into,
                key: k,
                src: v,
            });
            self.fx.release(k);
        } else {
            self.emit(Inst::MapPush { map: into, src: v });
        }
        self.emit(Inst::Safepoint {});
        self.jmp(top);
        self.bind(done);
        self.fx.release(v);
        self.fx.release(has);
        self.fx.release(it);
    }

    /// Unpacks an argument packet into parameter registers, by the same rules
    /// [`arrange`] applies at compile time:
    /// positional arguments fill the positional parameters in order, extra
    /// ones go to the rest parameter (else `TypeError`); named arguments fill
    /// the named-capable parameter of that name (twice is a `TypeError`), or
    /// the named rest parameter (else `TypeError`); a required parameter
    /// left empty is a `TypeError`. `mask` receives the presence bits.
    pub(crate) fn unpack(
        &mut self,
        params: &[PInfo],
        pos: Reg,
        named: Reg,
        dests: &[Reg],
        mask: Reg,
    ) {
        let place = self.cx.an.place_args;
        let map_ty = self.map_ty();
        let tr = self.map_ref();
        let m = self.fx.temp(map_ty);
        let npos = self.fx.temp(ValType::I64);
        let b = self.fx.temp(ValType::Bool);
        let k = self.fx.temp(ValType::I64);
        let kd = self.fx.temp(ValType::Dyn);
        let v = self.fx.temp(ValType::Dyn);
        let bit = self.fx.temp(ValType::I64);
        let zero = self.fx.temp(ValType::I64);
        self.emit(Inst::Cast {
            dst: m,
            src: pos,
            ty: tr,
        });
        self.emit(Inst::MapLen { dst: npos, map: m });
        self.load_i64(mask, 0);
        self.load_i64(zero, 0);
        let positional: Vec<usize> = (0..params.len())
            .filter(|&i| params.get(i).is_some_and(PInfo::positional))
            .collect();
        for (j, &pi) in positional.iter().enumerate() {
            let skip = self.label();
            self.load_i64(k, j as i64);
            self.emit(Inst::ILt {
                dst: b,
                lhs: k,
                rhs: npos,
                ty: bytecode_lang::IntTy::I64,
            });
            self.jump_on(b, skip, false);
            self.load_dyn_int(kd, j as i64);
            self.emit(Inst::MapGet {
                dst: v,
                map: m,
                key: kd,
            });
            let by_ref = params.get(pi).is_some_and(|p| p.by_ref);
            let dest = dests.get(pi).copied().unwrap_or(Reg(0));
            self.normalize(v, dest, by_ref, place, b);
            self.set_bit(mask, bit, pi);
            self.bind(skip);
        }
        // Extra positional arguments.
        let np = positional.len() as i64;
        let rest = params
            .iter()
            .position(|p| p.kind == hir_lang::ParamKind::Rest);
        self.load_i64(k, np);
        match rest {
            Some(ri) => {
                let rm = self.new_map();
                let top = self.label();
                let done = self.label();
                let one = self.fx.temp(ValType::I64);
                self.load_i64(one, 1);
                self.bind(top);
                self.emit(Inst::ILt {
                    dst: b,
                    lhs: k,
                    rhs: npos,
                    ty: bytecode_lang::IntTy::I64,
                });
                self.jump_on(b, done, false);
                self.emit(Inst::ToDyn {
                    dst: kd,
                    src: k,
                    from: bytecode_lang::Prim::I64,
                });
                self.emit(Inst::MapGet {
                    dst: v,
                    map: m,
                    key: kd,
                });
                let t = self.fx.temp(ValType::Dyn);
                self.normalize(v, t, false, place, b);
                self.emit(Inst::MapPush { map: rm, src: t });
                self.fx.release(t);
                self.emit(Inst::IAdd {
                    dst: k,
                    lhs: k,
                    rhs: one,
                    op: bytecode_lang::IntOp::new(bytecode_lang::IntTy::I64),
                });
                self.emit(Inst::Safepoint {});
                self.jmp(top);
                self.bind(done);
                self.fx.release(one);
                if let Some(&d) = dests.get(ri) {
                    self.emit(Inst::Mov { dst: d, src: rm });
                }
                self.fx.release(rm);
            }
            None => {
                let ok = self.label();
                self.emit(Inst::IGt {
                    dst: b,
                    lhs: npos,
                    rhs: k,
                    ty: bytecode_lang::IntTy::I64,
                });
                self.jump_on(b, ok, false);
                self.raise_type_error();
                self.bind(ok);
            }
        }
        // Named arguments.
        let rest_named = params
            .iter()
            .position(|p| p.kind == hir_lang::ParamKind::RestNamed);
        let rnm = rest_named.map(|_| self.new_map());
        let none = self.label();
        self.emit(Inst::IsKind {
            dst: b,
            src: named,
            kind: Kind::Nil,
        });
        self.jump_on(b, none, true);
        let nm = self.fx.temp(map_ty);
        let it_ty = ValType::Ref(self.cx.types.iter);
        let it = self.fx.temp(it_ty);
        let key = self.fx.temp(ValType::Dyn);
        let ks = self.fx.temp(ValType::Str);
        let s = self.fx.temp(ValType::Str);
        self.emit(Inst::Cast {
            dst: nm,
            src: named,
            ty: tr,
        });
        self.emit(Inst::IterNew { dst: it, src: nm });
        let top = self.label();
        let next = self.label();
        let bad = self.label();
        self.bind(top);
        self.emit(Inst::IterNext {
            has: b,
            iter: it,
            val: v,
        });
        self.jump_on(b, none, false);
        self.emit(Inst::IterKey { dst: key, iter: it });
        self.emit(Inst::IsKind {
            dst: b,
            src: key,
            kind: Kind::Str,
        });
        self.jump_on(b, bad, false);
        self.emit(Inst::FromDyn {
            dst: ks,
            src: key,
            to: bytecode_lang::Prim::Str,
        });
        let mut matches: Vec<(usize, Label)> = Vec::new();
        for (pi, p) in params.iter().enumerate() {
            if !p.nameable() {
                continue;
            }
            let Some(name) = p.name else { continue };
            let text = self.cx.text(name);
            let sid = self.cx.mb.string(&text);
            let kc = self.cx.mb.constant(bytecode_lang::Const::Str(sid));
            self.emit(Inst::LoadConst { dst: s, k: kc });
            self.emit(Inst::StrEq {
                dst: b,
                lhs: ks,
                rhs: s,
            });
            let l = self.label();
            self.jump_on(b, l, true);
            matches.push((pi, l));
        }
        match rnm {
            Some(rm) => {
                let t = self.fx.temp(ValType::Dyn);
                self.normalize(v, t, false, place, b);
                self.emit(Inst::MapSet {
                    map: rm,
                    key,
                    src: t,
                });
                self.fx.release(t);
                self.jmp(next);
            }
            None => self.jmp(bad),
        }
        for (pi, l) in matches {
            self.bind(l);
            // Already filled (positionally or by an earlier name): an error.
            self.load_bit(bit, pi);
            self.emit(Inst::IAnd {
                dst: k,
                lhs: mask,
                rhs: bit,
                op: bytecode_lang::IntOp::new(bytecode_lang::IntTy::I64),
            });
            self.emit(Inst::INe {
                dst: b,
                lhs: k,
                rhs: zero,
                ty: bytecode_lang::IntTy::I64,
            });
            self.jump_on(b, bad, true);
            let by_ref = params.get(pi).is_some_and(|p| p.by_ref);
            let dest = dests.get(pi).copied().unwrap_or(Reg(0));
            self.normalize(v, dest, by_ref, place, b);
            self.emit(Inst::IOr {
                dst: mask,
                lhs: mask,
                rhs: bit,
                op: bytecode_lang::IntOp::new(bytecode_lang::IntTy::I64),
            });
            self.jmp(next);
        }
        self.bind(next);
        self.emit(Inst::Safepoint {});
        self.jmp(top);
        self.bind(bad);
        self.raise_type_error();
        self.jmp(none);
        self.bind(none);
        if let (Some(ri), Some(rm)) = (rest_named, rnm) {
            if let Some(&d) = dests.get(ri) {
                self.emit(Inst::Mov { dst: d, src: rm });
            }
            self.fx.release(rm);
        }
        // Required parameters.
        for (pi, p) in params.iter().enumerate() {
            if !p.required() {
                continue;
            }
            let ok = self.label();
            self.load_bit(bit, pi);
            self.emit(Inst::IAnd {
                dst: k,
                lhs: mask,
                rhs: bit,
                op: bytecode_lang::IntOp::new(bytecode_lang::IntTy::I64),
            });
            self.emit(Inst::INe {
                dst: b,
                lhs: k,
                rhs: zero,
                ty: bytecode_lang::IntTy::I64,
            });
            self.jump_on(b, ok, true);
            self.raise_type_error();
            self.bind(ok);
        }
        for r in [s, ks, key, it, nm, zero, bit, v, kd, k, b, npos, m] {
            self.fx.release(r);
        }
    }

    /// Moves an argument into its parameter register: a by-reference
    /// parameter takes the caller's cell (or a new cell around a value); a
    /// by-value one takes the value (out of the cell, copied, when a caller
    /// passed a shared variable as a place).
    fn normalize(&mut self, v: Reg, dest: Reg, by_ref: bool, place: bool, b: Reg) {
        let tr = self.cell_ref();
        if by_ref {
            let wrap = self.label();
            let done = self.label();
            self.emit(Inst::IsType {
                dst: b,
                src: v,
                ty: tr,
            });
            self.jump_on(b, wrap, false);
            self.emit(Inst::Cast {
                dst: dest,
                src: v,
                ty: tr,
            });
            self.jmp(done);
            self.bind(wrap);
            self.emit(Inst::NewCell {
                dst: dest,
                src: v,
                ty: tr,
            });
            self.bind(done);
        } else if place {
            let plain = self.label();
            let done = self.label();
            self.emit(Inst::IsType {
                dst: b,
                src: v,
                ty: tr,
            });
            self.jump_on(b, plain, false);
            let cell_ty = self.cell_ty();
            let c = self.fx.temp(cell_ty);
            self.emit(Inst::Cast {
                dst: c,
                src: v,
                ty: tr,
            });
            self.emit(Inst::CellGet { dst: dest, cell: c });
            self.fx.release(c);
            if self.php() {
                self.dup_into(dest, dest);
            }
            self.jmp(done);
            self.bind(plain);
            self.emit(Inst::Mov { dst: dest, src: v });
            self.bind(done);
        } else {
            self.emit(Inst::Mov { dst: dest, src: v });
        }
    }

    fn load_bit(&mut self, bit: Reg, i: usize) {
        let v = 1i64.wrapping_shl(u32::try_from(i).unwrap_or(63));
        self.load_i64(bit, v);
    }

    fn set_bit(&mut self, mask: Reg, bit: Reg, i: usize) {
        self.load_bit(bit, i);
        self.emit(Inst::IOr {
            dst: mask,
            lhs: mask,
            rhs: bit,
            op: bytecode_lang::IntOp::new(bytecode_lang::IntTy::I64),
        });
    }

    /// Tests presence bit `i` of `mask` into the `bool` register `b`.
    pub(crate) fn test_bit(&mut self, mask: Reg, i: usize, b: Reg) {
        let bit = self.fx.temp(ValType::I64);
        let zero = self.fx.temp(ValType::I64);
        self.load_bit(bit, i);
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
        assert_eq!(mask, 0b1011);
        // A default may be omitted; a required parameter may not.
        assert!(arrange(&ps, &[pos()]).is_some());
        assert!(arrange(&ps, &[named(3)]).is_none());
    }

    #[test]
    fn duplicates_unknown_names_and_spreads_go_through_the_packet() {
        let ps = [
            param(0, ParamKind::Normal, false),
            param(1, ParamKind::PositionalOnly, true),
        ];
        // Named then positional for the same parameter.
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
