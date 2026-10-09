//! Function jobs: direct-call bodies, dynamic entries, closures, the start
//! and entry functions, and the PHP key helper; parameter defaults and
//! binding.

use alloc::vec::Vec;

use bytecode_lang::{Const, Inst, IntOp, IntTy, Kind, Reg, ValType};
use hir_lang::{BindMode, DefaultEval, Expr, ExprId, ItemKind, NodeRef, Pat};
use intern_lang::Lookup;

use super::{Dst, Gen, Rel, Step, Task, Val};
use crate::error::{CompileError, Unsupported};
use crate::func::FnCx;
use crate::unit::{Cap, Cx, Job, PInfo, Slot};

/// Where a parameter's default comes from when it is evaluated once.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Once {
    Global(bytecode_lang::GlobalId),
    Reg(Reg),
}

/// The parameters of the function being generated.
pub(crate) struct Params {
    pub(crate) list: Vec<PInfo>,
    pub(crate) regs: Vec<Reg>,
    pub(crate) mask: Option<Reg>,
    pub(crate) once: Vec<Option<Once>>,
    pub(crate) per_call: bool,
}

/// Generates one queued function.
pub(crate) fn run_job<L: Lookup>(cx: &mut Cx<'_, L>, job: Job) -> Result<(), CompileError> {
    cx.epoch = cx.epoch.wrapping_add(1);
    let hir = cx.hir;
    let root = NodeRef::Item(hir.root());
    match job {
        Job::Body { item, f } => {
            let node = NodeRef::Item(item);
            let Some(info) = cx.fns.get(&item).cloned() else {
                return Ok(());
            };
            let ItemKind::Fn(def) = hir.item(item).kind else {
                return Ok(());
            };
            let fx = FnCx::new(f, &info.sig, node);
            let mut g = Gen::new(cx, fx);
            g.at(node);
            let n = info.params.len();
            let regs: Vec<Reg> = (0..n)
                .map(|i| Reg(u16::try_from(i).unwrap_or(u16::MAX)))
                .collect();
            let mask = info
                .has_mask
                .then(|| Reg(u16::try_from(n).unwrap_or(u16::MAX)));
            let once = info.once.iter().map(|o| o.map(Once::Global)).collect();
            let params = Params {
                list: info.params.clone(),
                regs,
                mask,
                once,
                per_call: def.defaults == DefaultEval::PerCall,
            };
            g.body(params, def.body, node)?;
            g.finish_fn()
        }
        Job::DynEntry { item, f } => {
            let node = NodeRef::Item(item);
            let Some(info) = cx.fns.get(&item).cloned() else {
                return Ok(());
            };
            let Some(body) = info.body else {
                return Ok(());
            };
            let fx = FnCx::new(f, &[ValType::Dyn, ValType::Dyn], node);
            let mut g = Gen::new(cx, fx);
            g.at(node);
            let mut shape = alloc::vec![ValType::Dyn];
            shape.extend_from_slice(&info.sig);
            let win = g.fx.window(&shape);
            let n = info.params.len();
            let dests: Vec<Reg> = (0..n).map(|i| FnCx::slot(win.1, i + 1)).collect();
            let mask = g.fx.temp(ValType::I64);
            g.unpack(&info.params, Reg(0), Reg(1), &dests, mask);
            if info.has_mask {
                g.emit(Inst::Mov {
                    dst: FnCx::slot(win.1, n + 1),
                    src: mask,
                });
            }
            let argc = u8::try_from(info.sig.len()).unwrap_or(u8::MAX);
            g.emit(Inst::Call {
                dst: win.1,
                func: body,
                argc,
            });
            g.emit(Inst::Ret { src: win.1 });
            g.finish_fn()
        }
        Job::Closure {
            e,
            f,
            caps,
            aliases,
        } => {
            let node = NodeRef::Expr(e);
            let Expr::Closure(c) = *hir.expr(e) else {
                return Ok(());
            };
            let fx = FnCx::new(f, &[ValType::Dyn, ValType::Dyn], node);
            let mut g = Gen::new(cx, fx);
            g.at(node);
            let plist: Vec<PInfo> = hir
                .list(c.params)
                .iter()
                .map(|&p| PInfo::of(hir, p))
                .collect();
            let mut once: Vec<Option<Once>> = alloc::vec![None; plist.len()];
            let php = g.php();
            for (i, cap) in caps.iter().enumerate() {
                let idx = bytecode_lang::UpvalIdx(u16::try_from(i).unwrap_or(u16::MAX));
                match *cap {
                    Cap::Value(b) => {
                        let r = g.fx.temp(ValType::Dyn);
                        g.emit(Inst::GetUpval { dst: r, idx });
                        // Each call starts from the captured value.
                        if php {
                            g.dup_into(r, r);
                        }
                        if g.cx.is_cell(b) {
                            let ct = g.cell_ty();
                            let c = g.fx.temp(ct);
                            let ty = g.cell_ref();
                            g.emit(Inst::NewCell { dst: c, src: r, ty });
                            g.fx.release(r);
                            g.cx.set_slot(b, Slot::Cell(c));
                        } else {
                            g.cx.set_slot(b, Slot::Reg(r));
                        }
                    }
                    Cap::Cell(b) | Cap::SelfCell(b) => {
                        let ct = g.cell_ty();
                        let c = g.fx.temp(ct);
                        g.emit(Inst::GetUpval { dst: c, idx });
                        g.cx.set_slot(b, Slot::Cell(c));
                    }
                    Cap::Once(p) => {
                        let r = g.fx.temp(ValType::Dyn);
                        g.emit(Inst::GetUpval { dst: r, idx });
                        if let Some(o) = once.get_mut(p) {
                            *o = Some(Once::Reg(r));
                        }
                    }
                }
            }
            for (b, slot) in aliases {
                match slot {
                    // The cell a shared global or static holds never
                    // changes: load it once.
                    Slot::GlobalCell(gl) => {
                        let ct = g.cell_ty();
                        let c = g.fx.temp(ct);
                        g.emit(Inst::GetGlobal { dst: c, global: gl });
                        g.cx.set_slot(b, Slot::Cell(c));
                    }
                    _ => g.cx.set_slot(b, slot),
                }
            }
            let mut regs: Vec<Reg> = Vec::with_capacity(plist.len());
            for p in &plist {
                let ty = p.reg_type(&g.cx.types);
                regs.push(g.fx.temp(ty));
            }
            let mask = g.fx.temp(ValType::I64);
            g.unpack(&plist, Reg(0), Reg(1), &regs, mask);
            let params = Params {
                list: plist,
                regs,
                mask: Some(mask),
                once,
                per_call: c.defaults == DefaultEval::PerCall,
            };
            g.body(params, Some(c.body), node)?;
            g.finish_fn()
        }
        Job::Start { f, result } => {
            let fx = FnCx::new(f, &[], root);
            let mut g = Gen::new(cx, fx);
            g.at(root);
            g.start(result)?;
            g.finish_fn()
        }
        Job::Entry { f } => {
            let fx = FnCx::new(f, &[], root);
            let mut g = Gen::new(cx, fx);
            g.at(root);
            let body = match hir.item(hir.root()).kind {
                ItemKind::Module { body, .. } => body,
                _ => None,
            };
            let params = Params {
                list: Vec::new(),
                regs: Vec::new(),
                mask: None,
                once: Vec::new(),
                per_call: true,
            };
            g.body(params, body, root)?;
            g.finish_fn()
        }
        Job::Getter { f, global } => {
            let fx = FnCx::new(f, &[], root);
            let mut g = Gen::new(cx, fx);
            g.at(root);
            let r = g.fx.temp(ValType::Dyn);
            match global {
                Some(gl) => g.emit(Inst::GetGlobal { dst: r, global: gl }),
                None => g.emit(Inst::LoadNil { dst: r }),
            }
            g.emit(Inst::Ret { src: r });
            g.finish_fn()
        }
        Job::PhpKey { f } => {
            let fx = FnCx::new(f, &[ValType::Dyn], root);
            let mut g = Gen::new(cx, fx);
            g.at(root);
            g.php_key_body();
            g.finish_fn()
        }
    }
}

impl<L: Lookup> Gen<'_, '_, L> {
    /// Adds the finished function to the module, with its origin table.
    fn finish_fn(self) -> Result<(), CompileError> {
        let Gen { cx, fx, .. } = self;
        let FnCx { f, origins, .. } = fx;
        let id = cx.mb.add_function(f)?;
        let _ = cx.origins.insert(id.0, origins);
        Ok(())
    }

    /// The parameters' defaults and patterns, then the body, then `ret`.
    fn body(
        &mut self,
        params: Params,
        body: Option<ExprId>,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let mut ts: Vec<Task> = Vec::new();
        for i in 0..params.list.len() {
            ts.push(Task::Step(Step::ParamBind {
                index: i,
                reg: params.regs.get(i).copied().unwrap_or(Reg(0)),
            }));
        }
        self.params = Some(params);
        match body {
            Some(b) => {
                let dup = self.ret_dup(b);
                ts.push(Task::Expr(b, Dst::Any));
                if dup {
                    ts.push(Task::Deliver {
                        dst: Dst::Any,
                        dup: true,
                    });
                }
            }
            None => {
                let r = self.fx.temp(ValType::Dyn);
                ts.push(Task::Emit(Inst::LoadNil { dst: r }));
                ts.push(Task::Push(Val {
                    reg: r,
                    rel: Rel::Temp,
                }));
            }
        }
        ts.push(Task::At(node));
        ts.push(Task::Step(Step::Ret));
        for t in ts.into_iter().rev() {
            self.tasks.push(t);
        }
        self.run()
    }

    /// Parameter `index`: its default when absent, then its pattern.
    pub(crate) fn param_bind(&mut self, index: usize, reg: Reg) -> Result<(), CompileError> {
        let Some(params) = self.params.as_ref() else {
            return Ok(());
        };
        let Some(p) = params.list.get(index).copied() else {
            return Ok(());
        };
        let mask = params.mask;
        let once = params.once.get(index).copied().flatten();
        let per_call = params.per_call;
        let node = NodeRef::Param(p.id);
        self.at(node);
        let mut ts: Vec<Task> = Vec::new();
        if let (Some(d), Some(mask)) = (p.default, mask) {
            let b = self.fx.temp(ValType::Bool);
            let present = self.label();
            self.test_bit(mask, index, b);
            self.jump_on(b, present, true);
            self.fx.release(b);
            let _ = per_call;
            match once {
                Some(o) => {
                    let t = self.fx.temp(ValType::Dyn);
                    match o {
                        Once::Global(gl) => self.emit(Inst::GetGlobal { dst: t, global: gl }),
                        Once::Reg(r) => self.emit(Inst::Mov { dst: t, src: r }),
                    }
                    if self.php() {
                        self.dup_into(t, t);
                    }
                    if p.by_ref {
                        let ty = self.cell_ref();
                        self.emit(Inst::NewCell {
                            dst: reg,
                            src: t,
                            ty,
                        });
                    } else {
                        self.emit(Inst::Mov { dst: reg, src: t });
                    }
                    self.fx.release(t);
                    ts.push(Task::Bind(present));
                }
                None => {
                    if p.by_ref {
                        let dup = self.needs_dup(d);
                        ts.push(Task::Expr(d, Dst::Any));
                        ts.push(Task::NewCell { cell: reg, dup });
                    } else {
                        let t = self.store_expr_tasks(d, reg);
                        ts.extend(t);
                    }
                    ts.push(Task::Bind(present));
                }
            }
        }
        // The pattern.
        let hir = self.cx.hir;
        ts.push(Task::At(node));
        match *hir.pat(p.pat) {
            Pat::Bind {
                binder,
                mode: BindMode::Value,
                sub: None,
            } => {
                if p.by_ref {
                    self.cx.set_slot(binder, Slot::Cell(reg));
                } else if self.cx.is_cell(binder) {
                    let ct = self.cell_ty();
                    let c = self.fx.temp(ct);
                    self.cx.set_slot(binder, Slot::Cell(c));
                    ts.push(Task::Push(Val {
                        reg,
                        rel: Rel::Keep,
                    }));
                    ts.push(Task::NewCell {
                        cell: c,
                        dup: false,
                    });
                } else {
                    self.cx.set_slot(binder, Slot::Reg(reg));
                }
            }
            _ if p.by_ref => return Err(self.cx.unsupported(Unsupported::Reference, node)),
            _ => {
                let fail = self.label();
                let ok = self.label();
                ts.push(Task::Pat {
                    pat: p.pat,
                    v: reg,
                    fail,
                });
                ts.push(Task::Jump(ok));
                ts.push(Task::Bind(fail));
                ts.push(Task::At(node));
                ts.push(Task::Step(Step::RaiseTypeError));
                ts.push(Task::Bind(ok));
            }
        }
        for t in ts.into_iter().rev() {
            self.tasks.push(t);
        }
        Ok(())
    }

    /// The start function: initializers and once-evaluated defaults in
    /// canonical order, nested module bodies, then the body (`Start` mode).
    fn start(&mut self, result: Option<bytecode_lang::GlobalId>) -> Result<(), CompileError> {
        let hir = self.cx.hir;
        let mut ts: Vec<Task> = Vec::new();
        for &item in &self.cx.an.inits {
            let node = NodeRef::Item(item);
            match hir.item(item).kind {
                ItemKind::Global { init, .. } if self.cx.an.cell_globals.contains(&item) => {
                    // Shared by reference: a cell holding the initial value.
                    let Some(&g) = self.cx.globals.get(&item) else {
                        continue;
                    };
                    ts.push(Task::At(node));
                    match init {
                        Some(e) => {
                            let dup = self.needs_dup(e);
                            ts.push(Task::Expr(e, Dst::Any));
                            if dup {
                                ts.push(Task::Deliver {
                                    dst: Dst::Any,
                                    dup: true,
                                });
                            }
                        }
                        None => {
                            let r = self.fx.temp(ValType::Dyn);
                            ts.push(Task::Emit(Inst::LoadNil { dst: r }));
                            ts.push(Task::Push(Val {
                                reg: r,
                                rel: Rel::Temp,
                            }));
                        }
                    }
                    ts.push(Task::Step(Step::SetGlobalCell(g)));
                }
                ItemKind::Global { init: Some(e), .. } | ItemKind::Const { value: Some(e), .. } => {
                    if matches!(hir.expr(e), Expr::Lit(_)) {
                        continue;
                    }
                    let Some(&g) = self.cx.globals.get(&item) else {
                        continue;
                    };
                    let dup = self.needs_dup(e);
                    ts.push(Task::At(node));
                    ts.push(Task::Expr(e, Dst::Any));
                    if dup {
                        ts.push(Task::Deliver {
                            dst: Dst::Any,
                            dup: true,
                        });
                    }
                    ts.push(Task::Step(Step::SetGlobal(g)));
                }
                ItemKind::Fn(def) => {
                    let Some(info) = self.cx.fns.get(&item) else {
                        continue;
                    };
                    for (i, &p) in hir.list(def.params).iter().enumerate() {
                        let (Some(d), Some(Some(g))) = (hir.param(p).default, info.once.get(i))
                        else {
                            continue;
                        };
                        ts.push(Task::At(NodeRef::Param(p)));
                        ts.push(Task::Expr(d, Dst::Any));
                        ts.push(Task::Step(Step::SetGlobal(*g)));
                    }
                }
                ItemKind::Module { body: Some(b), .. } if item != hir.root() => {
                    ts.push(Task::Expr(b, Dst::Discard));
                }
                _ => {}
            }
        }
        if let Some(g) = result {
            if let ItemKind::Module { body: Some(b), .. } = hir.item(hir.root()).kind {
                let dup = self.needs_dup(b);
                ts.push(Task::Expr(b, Dst::Any));
                if dup {
                    ts.push(Task::Deliver {
                        dst: Dst::Any,
                        dup: true,
                    });
                }
                ts.push(Task::Step(Step::SetGlobal(g)));
            }
        }
        ts.push(Task::At(NodeRef::Item(hir.root())));
        ts.push(Task::Emit(Inst::RetVoid {}));
        for t in ts.into_iter().rev() {
            self.tasks.push(t);
        }
        self.run()
    }

    /// `<php_key>(k)`: PHP's array-key normalization (see
    /// [`KeyCoercion::Php`](crate::KeyCoercion::Php)).
    fn php_key_body(&mut self) {
        let k = Reg(0);
        let b = self.fx.temp(ValType::Bool);
        let r = self.fx.temp(ValType::Dyn);
        let (lstr, lflt, lbool, lnil, keep) = (
            self.label(),
            self.label(),
            self.label(),
            self.label(),
            self.label(),
        );
        for (kind, l) in [
            (Kind::Str, lstr),
            (Kind::Float, lflt),
            (Kind::Bool, lbool),
            (Kind::Nil, lnil),
        ] {
            self.emit(Inst::IsKind {
                dst: b,
                src: k,
                kind,
            });
            self.jump_on(b, l, true);
        }
        self.bind(keep);
        self.emit(Inst::Ret { src: k });
        // Floats truncate toward zero, saturating; NaN is 0.
        self.bind(lflt);
        let f = self.fx.temp(ValType::F64);
        let i = self.fx.temp(ValType::I64);
        self.emit(Inst::FromDyn {
            dst: f,
            src: k,
            to: bytecode_lang::Prim::F64,
        });
        let sat =
            bytecode_lang::Policy::new().with_float_to_int(bytecode_lang::FloatToInt::Saturate);
        self.emit(Inst::F64ToInt {
            dst: i,
            src: f,
            op: IntOp::new(IntTy::I64).with_policy(sat),
        });
        self.emit(Inst::ToDyn {
            dst: r,
            src: i,
            from: bytecode_lang::Prim::I64,
        });
        self.emit(Inst::Ret { src: r });
        // Booleans are 0 and 1.
        self.bind(lbool);
        self.emit(Inst::FromDyn {
            dst: b,
            src: k,
            to: bytecode_lang::Prim::Bool,
        });
        self.emit(Inst::BoolToInt {
            dst: i,
            src: b,
            ty: IntTy::I64,
        });
        self.emit(Inst::ToDyn {
            dst: r,
            src: i,
            from: bytecode_lang::Prim::I64,
        });
        self.emit(Inst::Ret { src: r });
        // null is "".
        self.bind(lnil);
        let empty = self.cx.mb.string("");
        let kc = self.cx.mb.constant(Const::Str(empty));
        self.emit(Inst::DLoadConst { dst: r, k: kc });
        self.emit(Inst::Ret { src: r });
        // A string holding a canonical decimal i64 is that integer.
        self.bind(lstr);
        let s = self.fx.temp(ValType::Str);
        let n = self.fx.temp(ValType::I64);
        let pos = self.fx.temp(ValType::I64);
        let one = self.fx.temp(ValType::I64);
        let t = self.fx.temp(ValType::I64);
        let c = self.fx.temp(ValType::U8);
        let lim = self.fx.temp(ValType::U8);
        let neg = self.fx.temp(ValType::Bool);
        let acc = self.fx.temp(ValType::I64);
        let op = IntOp::new(IntTy::I64);
        let wrap = IntOp::new(IntTy::I64)
            .with_policy(bytecode_lang::Policy::new().with_overflow(bytecode_lang::Overflow::Wrap));
        self.emit(Inst::FromDyn {
            dst: s,
            src: k,
            to: bytecode_lang::Prim::Str,
        });
        self.emit(Inst::StrLen { dst: n, s });
        self.load_i64(one, 1);
        self.load_i64(pos, 0);
        self.load_i64(acc, 0);
        self.emit(Inst::LoadBool {
            dst: neg,
            val: false,
        });
        // Empty, or longer than any i64 ("-9223372036854775808" is 20).
        self.load_i64(t, 0);
        self.emit(Inst::IEq {
            dst: b,
            lhs: n,
            rhs: t,
            ty: IntTy::I64,
        });
        self.jump_on(b, keep, true);
        self.load_i64(t, 20);
        self.emit(Inst::IGt {
            dst: b,
            lhs: n,
            rhs: t,
            ty: IntTy::I64,
        });
        self.jump_on(b, keep, true);
        // An optional '-', not alone.
        let digits = self.label();
        self.emit(Inst::StrByte {
            dst: c,
            s,
            idx: pos,
        });
        self.emit(Inst::LoadInt {
            dst: lim,
            val: i32::from(b'-'),
            ty: IntTy::U8,
        });
        self.emit(Inst::IEq {
            dst: b,
            lhs: c,
            rhs: lim,
            ty: IntTy::U8,
        });
        self.jump_on(b, digits, false);
        self.emit(Inst::LoadBool {
            dst: neg,
            val: true,
        });
        self.emit(Inst::IAdd {
            dst: pos,
            lhs: pos,
            rhs: one,
            op,
        });
        self.emit(Inst::IEq {
            dst: b,
            lhs: pos,
            rhs: n,
            ty: IntTy::I64,
        });
        self.jump_on(b, keep, true);
        self.bind(digits);
        // No leading zero, except "0" itself.
        let first_ok = self.label();
        self.emit(Inst::StrByte {
            dst: c,
            s,
            idx: pos,
        });
        self.emit(Inst::LoadInt {
            dst: lim,
            val: i32::from(b'0'),
            ty: IntTy::U8,
        });
        self.emit(Inst::IEq {
            dst: b,
            lhs: c,
            rhs: lim,
            ty: IntTy::U8,
        });
        self.jump_on(b, first_ok, false);
        // "0" (not "-0", not "01").
        self.emit(Inst::BNot { dst: b, src: neg });
        self.jump_on(b, keep, false);
        self.emit(Inst::IEq {
            dst: b,
            lhs: n,
            rhs: one,
            ty: IntTy::I64,
        });
        self.jump_on(b, keep, false);
        self.emit(Inst::DLoadInt { dst: r, val: 0 });
        self.emit(Inst::Ret { src: r });
        self.bind(first_ok);
        // Accumulate negatively, so i64::MIN fits; any overflow or non-digit
        // keeps the string.
        let top = self.label();
        let end = self.label();
        let min10 = self.fx.temp(ValType::I64);
        let ten = self.fx.temp(ValType::I64);
        let d = self.fx.temp(ValType::I64);
        self.load_i64(min10, i64::MIN / 10);
        self.load_i64(ten, 10);
        self.bind(top);
        self.emit(Inst::ILt {
            dst: b,
            lhs: pos,
            rhs: n,
            ty: IntTy::I64,
        });
        self.jump_on(b, end, false);
        self.emit(Inst::StrByte {
            dst: c,
            s,
            idx: pos,
        });
        self.emit(Inst::LoadInt {
            dst: lim,
            val: i32::from(b'0'),
            ty: IntTy::U8,
        });
        self.emit(Inst::ILt {
            dst: b,
            lhs: c,
            rhs: lim,
            ty: IntTy::U8,
        });
        self.jump_on(b, keep, true);
        self.emit(Inst::LoadInt {
            dst: lim,
            val: i32::from(b'9'),
            ty: IntTy::U8,
        });
        self.emit(Inst::IGt {
            dst: b,
            lhs: c,
            rhs: lim,
            ty: IntTy::U8,
        });
        self.jump_on(b, keep, true);
        self.emit(Inst::Zext {
            dst: d,
            src: c,
            pair: bytecode_lang::IntPair::new(IntTy::U8, IntTy::I64),
        });
        self.load_i64(t, i64::from(b'0'));
        self.emit(Inst::ISub {
            dst: d,
            lhs: d,
            rhs: t,
            op,
        });
        // acc * 10 - d must stay >= i64::MIN.
        self.emit(Inst::ILt {
            dst: b,
            lhs: acc,
            rhs: min10,
            ty: IntTy::I64,
        });
        self.jump_on(b, keep, true);
        self.emit(Inst::IMul {
            dst: acc,
            lhs: acc,
            rhs: ten,
            op: wrap,
        });
        self.load_i64(t, i64::MIN);
        self.emit(Inst::IAdd {
            dst: t,
            lhs: t,
            rhs: d,
            op: wrap,
        });
        self.emit(Inst::ILt {
            dst: b,
            lhs: acc,
            rhs: t,
            ty: IntTy::I64,
        });
        self.jump_on(b, keep, true);
        self.emit(Inst::ISub {
            dst: acc,
            lhs: acc,
            rhs: d,
            op,
        });
        self.emit(Inst::IAdd {
            dst: pos,
            lhs: pos,
            rhs: one,
            op,
        });
        self.emit(Inst::Safepoint {});
        self.jmp(top);
        self.bind(end);
        let done = self.label();
        self.jump_on(neg, done, true);
        // Positive: -acc, which overflows only for i64::MIN.
        self.load_i64(t, i64::MIN);
        self.emit(Inst::IEq {
            dst: b,
            lhs: acc,
            rhs: t,
            ty: IntTy::I64,
        });
        self.jump_on(b, keep, true);
        self.emit(Inst::INeg {
            dst: acc,
            src: acc,
            op,
        });
        self.bind(done);
        self.emit(Inst::ToDyn {
            dst: r,
            src: acc,
            from: bytecode_lang::Prim::I64,
        });
        self.emit(Inst::Ret { src: r });
    }
}
