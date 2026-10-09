//! Patterns: a simple sequential decision procedure (each pattern tested in
//! order, failing to a label). Decision trees (match-lang) arrive in 0.5.
//!
//! In the dynamic profile a tuple or slice pattern matches an array (a map)
//! by its integer keys `0..n` (and `len-m..len` for a suffix), a record
//! pattern matches a map by its string keys, a literal matches by `deq` (the
//! language's equality, its hook included), a range by class (numbers with
//! numbers, chars with chars) and order, and a type test by dynamic kind.

use bytecode_lang::{Inst, IntOp, IntTy, Kind, Label, Reg, ValType};
use hir_lang::{BindMode, ItemKind, Lit, NodeRef, Pat, PatId, Prim, Res, Ty, TyId};
use intern_lang::Lookup;

use super::{Gen, Task};
use crate::error::{CompileError, Unsupported};

impl<L: Lookup> Gen<'_, '_, L> {
    /// Tests `pat` against the value in `v`; jumps to `fail` when it does not
    /// match, binding its variables when it does.
    pub(crate) fn pat(&mut self, pat: PatId, v: Reg, fail: Label) -> Result<(), CompileError> {
        let node = NodeRef::Pat(pat);
        self.at(node);
        let hir = self.cx.hir;
        match *hir.pat(pat) {
            Pat::Wild => {}
            Pat::Bind { binder, mode, sub } => {
                if mode != BindMode::Value {
                    return Err(self.cx.unsupported(Unsupported::Reference, node));
                }
                match sub {
                    // `x @ sub`: bind once the sub-pattern matched.
                    Some(sp) => self.sched([
                        Task::Pat { pat: sp, v, fail },
                        Task::At(node),
                        Task::BindVal { b: binder, v },
                    ]),
                    None => self.bind_binder(binder, v),
                }
            }
            Pat::Ident { binder, path } => {
                let res = hir.path(path).res;
                match self.const_value(res, NodeRef::Path(path))? {
                    Some(g) => {
                        let t = self.fx.temp(ValType::Dyn);
                        self.read_slot(g, t);
                        self.eq_or_fail(v, t, fail);
                        self.fx.release(t);
                    }
                    None => self.bind_binder(binder, v),
                }
            }
            Pat::Lit(lit) => {
                let t = self.fx.temp(ValType::Dyn);
                self.load_lit(t, lit, node)?;
                self.eq_or_fail(v, t, fail);
                self.fx.release(t);
            }
            Pat::Path(path) => {
                let pnode = NodeRef::Path(path);
                let res = hir.path(path).res;
                match self.const_value(res, pnode)? {
                    Some(g) => {
                        let t = self.fx.temp(ValType::Dyn);
                        self.read_slot(g, t);
                        self.eq_or_fail(v, t, fail);
                        self.fx.release(t);
                    }
                    None => return Err(self.cx.unsupported(Unsupported::Pattern, pnode)),
                }
            }
            Pat::Range { lo, hi, inclusive } => self.range(v, lo, hi, inclusive, fail, node)?,
            Pat::Tuple { elems, rest } => {
                let elems = hir.list(elems);
                self.sequence(v, elems, rest.map(|r| r as usize), None, fail);
            }
            Pat::Slice { prefix, rest } => {
                let prefix = hir.list(prefix);
                match rest {
                    None => self.sequence(v, prefix, None, None, fail),
                    Some(r) => {
                        let suffix = hir.list(r.suffix);
                        let mut all: alloc::vec::Vec<PatId> = prefix.to_vec();
                        all.extend_from_slice(suffix);
                        self.sequence(v, &all, Some(prefix.len()), Some(r.bind), fail);
                    }
                }
            }
            Pat::Record { path, fields, rest } => {
                if path.is_some() {
                    return Err(self.cx.unsupported(Unsupported::Record, node));
                }
                let fields = hir.list(fields);
                let m = self.map_or_fail(v, fail);
                if !rest {
                    let len = self.len_check(m, fields.len(), false, fail);
                    self.fx.release(len);
                }
                let b = self.fx.temp(ValType::Bool);
                let mut subs: alloc::vec::Vec<(PatId, Reg)> = alloc::vec::Vec::new();
                for f in fields {
                    let k = self.load_name(f.name.sym);
                    self.emit(Inst::MapHas {
                        dst: b,
                        map: m,
                        key: k,
                    });
                    self.jump_on(b, fail, false);
                    let e = self.fx.temp(ValType::Dyn);
                    self.emit(Inst::MapGet {
                        dst: e,
                        map: m,
                        key: k,
                    });
                    self.fx.release(k);
                    subs.push((f.pat, e));
                }
                self.fx.release(b);
                self.sub_tests(&subs, m, fail);
            }
            Pat::Or(alts) => {
                let alts = hir.list(alts);
                let ok = self.label();
                let mut ts: alloc::vec::Vec<Task> = alloc::vec::Vec::new();
                for (i, &a) in alts.iter().enumerate() {
                    if i + 1 == alts.len() {
                        ts.push(Task::Pat { pat: a, v, fail });
                    } else {
                        let next = self.label();
                        ts.push(Task::Pat {
                            pat: a,
                            v,
                            fail: next,
                        });
                        ts.push(Task::At(node));
                        ts.push(Task::Jump(ok));
                        ts.push(Task::Bind(next));
                    }
                }
                ts.push(Task::Bind(ok));
                for t in ts.into_iter().rev() {
                    self.tasks.push(t);
                }
            }
            Pat::TypeTest { ty, pat: sub } => {
                self.type_test(v, ty, fail, node)?;
                if let Some(sp) = sub {
                    self.tasks.push(Task::Pat { pat: sp, v, fail });
                }
            }
            Pat::Ctor { .. } => return Err(self.cx.unsupported(Unsupported::Record, node)),
            Pat::Ref { .. } => return Err(self.cx.unsupported(Unsupported::Reference, node)),
            Pat::Err => {
                return Err(CompileError::ErrorNode {
                    node,
                    span: self.cx.span(node),
                });
            }
        }
        Ok(())
    }

    /// The global holding a constant a pattern path names, or `None` when
    /// the path binds (a bare identifier that is not a constant).
    fn const_value(
        &mut self,
        res: Res,
        node: NodeRef,
    ) -> Result<Option<crate::unit::Slot>, CompileError> {
        match res {
            Res::Def(_) => {
                let Some(item) = self.cx.local_item(res, node)? else {
                    return Ok(None);
                };
                match self.cx.hir.item(item).kind {
                    ItemKind::Const { .. } | ItemKind::Global { .. } => {
                        Ok(self.cx.global_slot(item))
                    }
                    ItemKind::Record(_) | ItemKind::Sum(_) => {
                        Err(self.cx.unsupported(Unsupported::Record, node))
                    }
                    _ => Err(self.cx.unsupported(Unsupported::Pattern, node)),
                }
            }
            Res::Extern(_) | Res::Prim(_) => Err(self.cx.unsupported(Unsupported::Pattern, node)),
            Res::Local(_) | Res::Unresolved | Res::Err => Ok(None),
        }
    }

    fn eq_or_fail(&mut self, v: Reg, t: Reg, fail: Label) {
        let b = self.fx.temp(ValType::Bool);
        self.emit(Inst::DEq {
            dst: b,
            lhs: v,
            rhs: t,
        });
        self.jump_on(b, fail, false);
        self.fx.release(b);
    }

    /// Fails unless `v` is a map; returns it as a `ref map` temporary.
    fn map_or_fail(&mut self, v: Reg, fail: Label) -> Reg {
        let ty = self.map_ty();
        let tr = self.map_ref();
        let b = self.fx.temp(ValType::Bool);
        self.emit(Inst::IsType {
            dst: b,
            src: v,
            ty: tr,
        });
        self.jump_on(b, fail, false);
        self.fx.release(b);
        let m = self.fx.temp(ty);
        self.emit(Inst::Cast {
            dst: m,
            src: v,
            ty: tr,
        });
        m
    }

    /// Fails unless the map's length is `n` (or at least `n`).
    fn len_check(&mut self, m: Reg, n: usize, at_least: bool, fail: Label) -> Reg {
        let len = self.fx.temp(ValType::I64);
        let k = self.fx.temp(ValType::I64);
        let b = self.fx.temp(ValType::Bool);
        self.emit(Inst::MapLen { dst: len, map: m });
        self.load_i64(k, i64::try_from(n).unwrap_or(i64::MAX));
        self.emit(if at_least {
            Inst::IGe {
                dst: b,
                lhs: len,
                rhs: k,
                ty: IntTy::I64,
            }
        } else {
            Inst::IEq {
                dst: b,
                lhs: len,
                rhs: k,
                ty: IntTy::I64,
            }
        });
        self.jump_on(b, fail, false);
        self.fx.release(b);
        self.fx.release(k);
        len
    }

    /// Schedules the sub-pattern tests on extracted elements, then frees the
    /// elements and the map.
    fn sub_tests(&mut self, subs: &[(PatId, Reg)], m: Reg, fail: Label) {
        self.tasks.push(Task::Free(m));
        for &(_, e) in subs.iter().rev() {
            self.tasks.push(Task::Free(e));
        }
        for &(p, e) in subs.iter().rev() {
            self.tasks.push(Task::Pat { pat: p, v: e, fail });
        }
    }

    /// A tuple or slice pattern: `pats` with a rest at position `rest`
    /// (prefix before it, suffix after), the rest bound to `bind` when given.
    fn sequence(
        &mut self,
        v: Reg,
        pats: &[PatId],
        rest: Option<usize>,
        bind: Option<Option<PatId>>,
        fail: Label,
    ) {
        let m = self.map_or_fail(v, fail);
        let n = pats.len();
        let len = self.len_check(m, n, rest.is_some(), fail);
        let b = self.fx.temp(ValType::Bool);
        let kd = self.fx.temp(ValType::Dyn);
        let ki = self.fx.temp(ValType::I64);
        let mut subs: alloc::vec::Vec<(PatId, Reg)> = alloc::vec::Vec::new();
        let split = rest.unwrap_or(n);
        for (i, &p) in pats.iter().enumerate() {
            if i < split {
                self.load_dyn_int(kd, i as i64);
            } else {
                // Suffix element i: key len - (n - i).
                self.load_i64(ki, (n - i) as i64);
                self.emit(Inst::ISub {
                    dst: ki,
                    lhs: len,
                    rhs: ki,
                    op: IntOp::new(IntTy::I64),
                });
                self.emit(Inst::ToDyn {
                    dst: kd,
                    src: ki,
                    from: bytecode_lang::Prim::I64,
                });
            }
            self.emit(Inst::MapHas {
                dst: b,
                map: m,
                key: kd,
            });
            self.jump_on(b, fail, false);
            let e = self.fx.temp(ValType::Dyn);
            self.emit(Inst::MapGet {
                dst: e,
                map: m,
                key: kd,
            });
            subs.push((p, e));
        }
        // The rest, as a new array of the middle elements.
        if let Some(Some(rp)) = bind {
            let out = self.new_map();
            let end = self.fx.temp(ValType::I64);
            let one = self.fx.temp(ValType::I64);
            let e = self.fx.temp(ValType::Dyn);
            self.load_i64(one, 1);
            self.load_i64(ki, (n - split) as i64);
            self.emit(Inst::ISub {
                dst: end,
                lhs: len,
                rhs: ki,
                op: IntOp::new(IntTy::I64),
            });
            self.load_i64(ki, split as i64);
            let top = self.label();
            let done = self.label();
            self.bind(top);
            self.emit(Inst::ILt {
                dst: b,
                lhs: ki,
                rhs: end,
                ty: IntTy::I64,
            });
            self.jump_on(b, done, false);
            self.emit(Inst::ToDyn {
                dst: kd,
                src: ki,
                from: bytecode_lang::Prim::I64,
            });
            self.emit(Inst::MapHas {
                dst: b,
                map: m,
                key: kd,
            });
            self.jump_on(b, fail, false);
            self.emit(Inst::MapGet {
                dst: e,
                map: m,
                key: kd,
            });
            self.emit(Inst::MapPush { map: out, src: e });
            self.emit(Inst::IAdd {
                dst: ki,
                lhs: ki,
                rhs: one,
                op: IntOp::new(IntTy::I64),
            });
            self.emit(Inst::Safepoint {});
            self.jmp(top);
            self.bind(done);
            let r = self.fx.temp(ValType::Dyn);
            self.emit(Inst::Mov { dst: r, src: out });
            self.fx.release(out);
            self.fx.release(e);
            self.fx.release(one);
            self.fx.release(end);
            subs.push((rp, r));
        }
        self.fx.release(ki);
        self.fx.release(kd);
        self.fx.release(b);
        self.fx.release(len);
        self.sub_tests(&subs, m, fail);
    }

    /// A range pattern: the value and the bounds are of one class (numbers,
    /// or chars) and in order; a NaN is in no range.
    fn range(
        &mut self,
        v: Reg,
        lo: Option<PatId>,
        hi: Option<PatId>,
        inclusive: bool,
        fail: Label,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let hir = self.cx.hir;
        let mut bounds: [Option<Reg>; 2] = [None, None];
        for (i, p) in [lo, hi].into_iter().enumerate() {
            let Some(p) = p else { continue };
            let pnode = NodeRef::Pat(p);
            let t = self.fx.temp(ValType::Dyn);
            match *hir.pat(p) {
                Pat::Lit(lit @ (Lit::Int(_) | Lit::Float(_) | Lit::Char(_))) => {
                    self.load_lit(t, lit, pnode)?;
                }
                Pat::Path(path) => {
                    match self.const_value(hir.path(path).res, NodeRef::Path(path))? {
                        Some(g) => self.read_slot(g, t),
                        None => return Err(self.cx.unsupported(Unsupported::Pattern, pnode)),
                    }
                }
                _ => return Err(self.cx.unsupported(Unsupported::Pattern, pnode)),
            }
            if let Some(slot) = bounds.get_mut(i) {
                *slot = Some(t);
            }
        }
        self.at(node);
        let b = self.fx.temp(ValType::Bool);
        let c = self.fx.temp(ValType::Bool);
        for t in bounds.iter().flatten().copied() {
            // Same class: both numbers, or both chars.
            let num = self.label();
            let ok = self.label();
            self.emit(Inst::IsKind {
                dst: b,
                src: t,
                kind: Kind::Char,
            });
            self.jump_on(b, num, false);
            self.emit(Inst::IsKind {
                dst: c,
                src: v,
                kind: Kind::Char,
            });
            self.jump_on(c, fail, false);
            self.jmp(ok);
            self.bind(num);
            self.emit(Inst::IsKind {
                dst: c,
                src: v,
                kind: Kind::Int,
            });
            self.emit(Inst::IsKind {
                dst: b,
                src: v,
                kind: Kind::Float,
            });
            self.emit(Inst::BOr {
                dst: c,
                lhs: c,
                rhs: b,
            });
            self.jump_on(c, fail, false);
            self.emit(Inst::IsKind {
                dst: c,
                src: t,
                kind: Kind::Int,
            });
            self.emit(Inst::IsKind {
                dst: b,
                src: t,
                kind: Kind::Float,
            });
            self.emit(Inst::BOr {
                dst: c,
                lhs: c,
                rhs: b,
            });
            self.jump_on(c, fail, false);
            self.bind(ok);
        }
        if let Some(l) = bounds.first().copied().flatten() {
            self.emit(Inst::DLe {
                dst: b,
                lhs: l,
                rhs: v,
            });
            self.jump_on(b, fail, false);
        }
        if let Some(h) = bounds.get(1).copied().flatten() {
            self.emit(if inclusive {
                Inst::DLe {
                    dst: b,
                    lhs: v,
                    rhs: h,
                }
            } else {
                Inst::DLt {
                    dst: b,
                    lhs: v,
                    rhs: h,
                }
            });
            self.jump_on(b, fail, false);
        }
        self.fx.release(c);
        self.fx.release(b);
        for t in bounds.into_iter().flatten() {
            self.fx.release(t);
        }
        Ok(())
    }

    /// The dynamic kinds a type stands for, as a test on `v`.
    fn type_test(
        &mut self,
        v: Reg,
        ty: TyId,
        fail: Label,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let hir = self.cx.hir;
        let (ty, nullable) = match *hir.ty(ty) {
            Ty::Nullable(inner) => (inner, true),
            _ => (ty, false),
        };
        let kinds: &[Kind] = match *hir.ty(ty) {
            Ty::Any | Ty::Infer => return Ok(()),
            Ty::Tuple(_) | Ty::Array { .. } | Ty::Slice(_) => &[Kind::Map],
            Ty::Prim(p) => prim_kinds(p),
            Ty::Path(p) => match hir.path(p).res {
                Res::Prim(p) => prim_kinds(p),
                _ => return Err(self.cx.unsupported(Unsupported::Pattern, node)),
            },
            _ => return Err(self.cx.unsupported(Unsupported::Pattern, node)),
        };
        let ok = self.label();
        let b = self.fx.temp(ValType::Bool);
        if nullable {
            self.emit(Inst::IsKind {
                dst: b,
                src: v,
                kind: Kind::Nil,
            });
            self.jump_on(b, ok, true);
        }
        for &k in kinds {
            self.emit(Inst::IsKind {
                dst: b,
                src: v,
                kind: k,
            });
            self.jump_on(b, ok, true);
        }
        self.jmp(fail);
        self.bind(ok);
        self.fx.release(b);
        Ok(())
    }
}

fn prim_kinds(p: Prim) -> &'static [Kind] {
    match p {
        Prim::Bool => &[Kind::Bool],
        Prim::F32 | Prim::F64 => &[Kind::Float],
        Prim::Char => &[Kind::Char],
        Prim::Str => &[Kind::Str],
        _ => &[Kind::Int],
    }
}
