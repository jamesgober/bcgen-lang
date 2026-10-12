//! Places: assignment, `let_place` aliases, and PHP references.
//!
//! A place whose root is not a plain variable (an index, property, or append
//! chain, or a `let_place` alias) is handled in two halves. First its
//! **operands** are evaluated once, left to right (the root when it is a
//! value, then every index key and dynamic member name), into registers: an
//! *evaluated place* ([`EvPlace`]). Then any number of accesses run over
//! those registers: a read, a write (PHP auto-vivification and separation
//! with `dsep_*`, LSB §5.16), a reference to the place (`dref_*`, LSB §5.17),
//! or binding the place to a reference (`dbind_*`). `let_place` keeps the
//! evaluated place alive for its body (HIR §8.2), so no operand is ever
//! recomputed; an assignment, a reference assignment, and a place argument
//! use one for the duration of their own code.

use alloc::vec::Vec;

use bytecode_lang::{Inst, Kind, Reg, ValType};
use hir_lang::{BinderId, Expr, ExprId, ItemKind, Member, NodeRef, Op, Res, Symbol};
use intern_lang::Lookup;

use super::{Dst, Gen, Rel, Step, Task, Val};
use crate::error::{CompileError, Unsupported};
use crate::options::KeyCoercion;
use crate::unit::Slot;

/// One step of a place chain, from the root outward.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PStep {
    /// `[key]`: the key is an operand (normalized).
    Index,
    /// `->$name`: the name is an operand (not normalized).
    DynProp,
    /// `.name`.
    Prop(Symbol),
    /// `.0`.
    Elem(u32),
    /// `[]`.
    Append,
}

impl PStep {
    /// Whether the step has a key operand.
    fn keyed(self) -> bool {
        matches!(self, PStep::Index | PStep::DynProp)
    }
}

/// Where a place chain starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Root {
    /// A variable or global (written back when a write creates the array).
    Slot(Slot),
    /// Any other expression, evaluated once to a register.
    Value,
    /// A reference in a register: a late-bound static property
    /// (`static::$x`), whose accessor returns its reference.
    Cell,
}

/// Where an operand of a place comes from.
#[derive(Clone, Copy, Debug)]
enum Src {
    /// An expression, evaluated now (`index`: a key PHP normalizes).
    Expr { e: ExprId, index: bool },
    /// A register an enclosing `let_place` already holds.
    Reg(Reg),
    /// The reference of the late-bound static property `name`.
    Late { name: Symbol, node: NodeRef },
}

/// A place whose operands are evaluated: the root value (for a value root)
/// and the key of each keyed step, in registers.
#[derive(Clone, Debug, Default)]
pub(crate) struct EvPlace {
    root: Option<Root>,
    root_val: Option<Val>,
    steps: Vec<PStep>,
    keys: Vec<Val>,
}

/// The continuation steps of assignments and place uses.
#[derive(Clone, Debug)]
pub(crate) enum PlaceStep {
    /// `x op= v` for a variable in a register: `old` holds its value from
    /// before `v` was evaluated.
    LocalCompound {
        op: Op,
        old: Reg,
        own_old: bool,
        reg: Reg,
        dst: Dst,
        node: NodeRef,
    },
    /// `x = v` / `x op= v` for a reference, global, or alias variable.
    Store {
        slot: Slot,
        op: Option<Op>,
        old: Option<Reg>,
        dup: bool,
        dst: Dst,
        node: NodeRef,
    },
    /// Pops a place's evaluated operands into place `idx`.
    Bind {
        idx: u32,
        root: Root,
        root_val: bool,
        steps: Vec<PStep>,
        nkeys: usize,
    },
    /// Makes `binder` name place `idx` (`let_place`).
    Alias { binder: BinderId, idx: u32 },
    /// Pushes the value of place `idx`.
    Read { idx: u32, node: NodeRef },
    /// Combines the old value (below) with the assigned one (on top).
    Combine { op: Op, node: NodeRef },
    /// Writes the value on top of the stack to place `idx`.
    Write {
        idx: u32,
        dup: bool,
        dst: Dst,
        node: NodeRef,
    },
    /// Pushes a reference to place `idx`.
    Ref { idx: u32, node: NodeRef },
    /// Pops a reference and makes place `idx` an alias of it; the value of
    /// the reference assignment goes to `dst`.
    BindRef { idx: u32, dst: Dst, node: NodeRef },
    /// Frees place `idx`'s operand registers.
    Drop { idx: u32 },
}

impl<L: Lookup> Gen<'_, '_, L> {
    /// The late-bound static property a path names (`static::$x`), if it
    /// names one.
    pub(crate) fn late_static(&self, e: ExprId) -> Result<Option<Symbol>, CompileError> {
        let Expr::Path(p) = *self.cx.hir.expr(e) else {
            return Ok(None);
        };
        match self.member_path(p, super::class::Want::Value)? {
            Some(super::class::MemberRef::Late { name }) => Ok(Some(name)),
            _ => Ok(None),
        }
    }

    /// The slot a path names as an assignment target.
    pub(crate) fn place_slot(&mut self, e: ExprId) -> Result<Option<Slot>, CompileError> {
        let node = NodeRef::Expr(e);
        let hir = self.cx.hir;
        let Expr::Path(p) = *hir.expr(e) else {
            return Ok(None);
        };
        match self.member_path(p, super::class::Want::Value)? {
            Some(super::class::MemberRef::Value {
                global,
                is_static: true,
                denied,
            }) => {
                if let Some(d) = denied {
                    self.raise_denied(d);
                }
                return Ok(Some(Slot::GlobalCell(global)));
            }
            Some(super::class::MemberRef::Late { .. }) => return Ok(None),
            Some(super::class::MemberRef::Missing { class, ns, name }) => {
                // PHP raises where the write runs; the code after it is
                // unreachable but needs a slot.
                let msg = self.missing_msg(class, ns, name);
                self.raise_msg(&msg);
                return Ok(Some(Slot::Global(self.cx.scratch_global())));
            }
            Some(_) => {
                return Err(CompileError::NotAssignable {
                    node,
                    span: self.cx.span(node),
                });
            }
            None => {}
        }
        let path = *hir.path(p);
        if path.unresolved > 0 {
            return Err(self.cx.unsupported(Unsupported::TypeDirected, node));
        }
        match path.res {
            Res::Local(b) => Ok(self.cx.slot(b)),
            Res::Def(_) => {
                let item = self.cx.local_item(path.res, node)?;
                match item.map(|i| (i, hir.item(i).kind)) {
                    Some((i, ItemKind::Global { .. })) => Ok(self.cx.global_slot(i)),
                    _ => Err(CompileError::NotAssignable {
                        node,
                        span: self.cx.span(node),
                    }),
                }
            }
            Res::Unresolved | Res::Err => Err(CompileError::Unresolved {
                node,
                span: self.cx.span(node),
            }),
            _ => Err(CompileError::NotAssignable {
                node,
                span: self.cx.span(node),
            }),
        }
    }

    pub(crate) fn assign(
        &mut self,
        e: ExprId,
        target: ExprId,
        op: Option<Op>,
        value: ExprId,
        dst: Dst,
    ) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        let tnode = NodeRef::Expr(target);
        let hir = self.cx.hir;
        let dup = self.needs_dup(value);
        let late = self.late_static(target)?.is_some();
        if let (Expr::Path(_), false) = (*hir.expr(target), late) {
            let Some(slot) = self.place_slot(target)? else {
                return Err(CompileError::Unresolved {
                    node: tnode,
                    span: self.cx.span(tnode),
                });
            };
            match (slot, op) {
                (Slot::Reg(r), None) => {
                    let t = self.store_expr_tasks(value, r);
                    self.sched([
                        t[0].clone(),
                        t[1].clone(),
                        Task::Push(Val {
                            reg: r,
                            rel: Rel::Keep,
                        }),
                        Task::Deliver { dst, dup: false },
                    ]);
                }
                (Slot::Reg(r), Some(op)) => {
                    // The old value is read before `value` runs.
                    let (old, own_old) = if self.simple(value) {
                        (r, false)
                    } else {
                        let t = self.fx.temp(ValType::Dyn);
                        self.emit(Inst::Mov { dst: t, src: r });
                        (t, true)
                    };
                    self.sched([
                        Task::Expr(value, Dst::Any),
                        Task::Step(Step::Place(PlaceStep::LocalCompound {
                            op,
                            old,
                            own_old,
                            reg: r,
                            dst,
                            node,
                        })),
                    ]);
                }
                (slot, op) => {
                    let old = match op {
                        Some(_) => {
                            let t = self.fx.temp(ValType::Dyn);
                            self.read_slot_at(slot, t, node)?;
                            Some(t)
                        }
                        None => None,
                    };
                    self.sched([
                        Task::Expr(value, Dst::Any),
                        Task::Step(Step::Place(PlaceStep::Store {
                            slot,
                            op,
                            old,
                            dup,
                            dst,
                            node,
                        })),
                    ]);
                }
            }
            return Ok(());
        }
        if op.is_some() && last_step(target, hir) == Some(PStep::Append) {
            return Err(CompileError::NotAssignable {
                node: tnode,
                span: self.cx.span(tnode),
            });
        }
        let (mut ts, idx) = self.place_tasks(target, false)?;
        if let Some(op) = op {
            ts.push(Task::Step(Step::Place(PlaceStep::Read { idx, node })));
            ts.push(Task::Expr(value, Dst::Any));
            ts.push(Task::Step(Step::Place(PlaceStep::Combine { op, node })));
        } else {
            ts.push(Task::Expr(value, Dst::Any));
        }
        ts.push(Task::Step(Step::Place(PlaceStep::Write {
            idx,
            dup: dup && op.is_none(),
            dst,
            node,
        })));
        ts.push(Task::Step(Step::Place(PlaceStep::Drop { idx })));
        self.sched_all(ts);
        Ok(())
    }

    /// `let_place binder = place in body`.
    pub(crate) fn let_place(
        &mut self,
        binder: BinderId,
        place: ExprId,
        body: ExprId,
        dst: Dst,
    ) -> Result<(), CompileError> {
        let (mut ts, idx) = self.place_tasks(place, false)?;
        ts.push(Task::Step(Step::Place(PlaceStep::Alias { binder, idx })));
        ts.push(Task::Expr(body, dst));
        ts.push(Task::Step(Step::Place(PlaceStep::Drop { idx })));
        self.sched_all(ts);
        Ok(())
    }

    /// `target = &source`: the target place becomes an alias of the source
    /// place's reference (made on first use: `dref_*`, or the variable's own
    /// reference). Operands are evaluated target first, then source (PHP's
    /// order).
    pub(crate) fn ref_assign(
        &mut self,
        e: ExprId,
        target: ExprId,
        source: ExprId,
        dst: Dst,
    ) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        let (mut ts, ti) = self.place_tasks(target, true)?;
        let (ss, si) = self.place_tasks(source, true)?;
        ts.extend(ss);
        ts.push(Task::Step(Step::Place(PlaceStep::Ref { idx: si, node })));
        ts.push(Task::Step(Step::Place(PlaceStep::BindRef {
            idx: ti,
            dst,
            node,
        })));
        ts.push(Task::Step(Step::Place(PlaceStep::Drop { idx: si })));
        ts.push(Task::Step(Step::Place(PlaceStep::Drop { idx: ti })));
        self.sched_all(ts);
        Ok(())
    }

    /// Schedules the evaluation of a place's operands; returns the tasks
    /// (ending with the step that stores them) and the place's index.
    /// `for_ref`: the place will be referenced or bound, which an appended
    /// element cannot be.
    pub(crate) fn place_tasks(
        &mut self,
        target: ExprId,
        for_ref: bool,
    ) -> Result<(Vec<Task>, u32), CompileError> {
        let node = NodeRef::Expr(target);
        let (root, root_src, steps, keys) = self.chain(target)?;
        if for_ref && steps.last() == Some(&PStep::Append) {
            return Err(self.cx.unsupported(Unsupported::RefPlace, node));
        }
        let mut ts: Vec<Task> = Vec::with_capacity(keys.len() * 2 + 2);
        if let Some(src) = root_src {
            ts.push(match src {
                Src::Expr { e, .. } => Task::Expr(e, Dst::Temp),
                Src::Reg(reg) => Task::Push(Val {
                    reg,
                    rel: Rel::Keep,
                }),
                Src::Late { name, node } => {
                    Task::Step(Step::Class(super::class::ClassStep::LateRef { name, node }))
                }
            });
        }
        for k in &keys {
            match *k {
                Src::Expr { e, index } => {
                    ts.push(Task::Expr(e, Dst::Temp));
                    if index {
                        ts.push(Task::CoerceKey(node));
                    }
                }
                Src::Reg(reg) => ts.push(Task::Push(Val {
                    reg,
                    rel: Rel::Keep,
                })),
                Src::Late { .. } => {}
            }
        }
        let idx = u32::try_from(self.places.len()).unwrap_or(u32::MAX);
        self.places.push(EvPlace::default());
        ts.push(Task::Step(Step::Place(PlaceStep::Bind {
            idx,
            root,
            root_val: root_src.is_some(),
            steps,
            nkeys: keys.len(),
        })));
        Ok((ts, idx))
    }

    /// Decomposes a place into its root, its steps (root first), and its
    /// operands in evaluation order. A `let_place` alias inside the chain is
    /// spliced in with the operands it already holds.
    #[allow(clippy::type_complexity)]
    fn chain(
        &mut self,
        target: ExprId,
    ) -> Result<(Root, Option<Src>, Vec<PStep>, Vec<Src>), CompileError> {
        let hir = self.cx.hir;
        let mut steps: Vec<PStep> = Vec::new();
        let mut keys: Vec<Src> = Vec::new();
        let mut cur = target;
        let (root, root_src, prefix) = loop {
            let node = NodeRef::Expr(cur);
            match *hir.expr(cur) {
                Expr::Index { base, index } => {
                    steps.push(PStep::Index);
                    keys.push(Src::Expr {
                        e: index,
                        index: true,
                    });
                    cur = base;
                }
                Expr::DynField { base, name } => {
                    steps.push(PStep::DynProp);
                    keys.push(Src::Expr {
                        e: name,
                        index: false,
                    });
                    cur = base;
                }
                Expr::Field { base, member, .. } => {
                    steps.push(match member {
                        Member::Named(s) => PStep::Prop(s),
                        Member::Index(i) => PStep::Elem(i),
                    });
                    cur = base;
                }
                Expr::Append(base) => {
                    steps.push(PStep::Append);
                    cur = base;
                }
                Expr::Path(_) if self.late_static(cur)?.is_some() => {
                    let name = self.late_static(cur)?;
                    let Some(name) = name else {
                        break (Root::Value, None, None);
                    };
                    break (Root::Cell, Some(Src::Late { name, node }), None);
                }
                Expr::Path(_) => match self.place_slot(cur) {
                    Ok(Some(Slot::Place(i))) => {
                        let alias = self.places.get(i as usize).cloned().unwrap_or_default();
                        let root = alias.root.unwrap_or(Root::Value);
                        let src = alias.root_val.map(|v| Src::Reg(v.reg));
                        break (root, src, Some(alias));
                    }
                    Ok(Some(s)) => break (Root::Slot(s), None, None),
                    Ok(None) => {
                        return Err(CompileError::Unresolved {
                            node,
                            span: self.cx.span(node),
                        });
                    }
                    // A path that is not a variable (a function, a
                    // constant): an ordinary value root.
                    Err(CompileError::NotAssignable { .. }) => {
                        break (
                            Root::Value,
                            Some(Src::Expr {
                                e: cur,
                                index: false,
                            }),
                            None,
                        );
                    }
                    Err(e) => return Err(e),
                },
                Expr::VarVar(_) => return Err(self.cx.unsupported(Unsupported::VarVar, node)),
                Expr::Deref(_) => return Err(self.cx.unsupported(Unsupported::Reference, node)),
                Expr::Err => {
                    return Err(CompileError::ErrorNode {
                        node,
                        span: self.cx.span(node),
                    });
                }
                _ => {
                    break (
                        Root::Value,
                        Some(Src::Expr {
                            e: cur,
                            index: false,
                        }),
                        None,
                    );
                }
            }
        };
        steps.reverse();
        keys.reverse();
        if let Some(alias) = prefix {
            let mut all_steps = alias.steps.clone();
            all_steps.extend(steps);
            let mut all_keys: Vec<Src> = alias.keys.iter().map(|v| Src::Reg(v.reg)).collect();
            all_keys.extend(keys);
            return Ok((root, root_src, all_steps, all_keys));
        }
        Ok((root, root_src, steps, keys))
    }

    /// Schedules tasks so they run in the order given.
    pub(crate) fn sched_all(&mut self, ts: Vec<Task>) {
        for t in ts.into_iter().rev() {
            self.tasks.push(t);
        }
    }

    /// Takes an evaluated place out of its slot for an access (no copy of
    /// its vectors); [`put_place`](Self::put_place) puts it back.
    fn take_place(&mut self, idx: u32) -> EvPlace {
        match self.places.get_mut(idx as usize) {
            Some(p) => core::mem::take(p),
            None => EvPlace::default(),
        }
    }

    fn put_place(&mut self, idx: u32, p: EvPlace) {
        if let Some(slot) = self.places.get_mut(idx as usize) {
            *slot = p;
        }
    }

    pub(crate) fn place_step(&mut self, p: PlaceStep) -> Result<(), CompileError> {
        match p {
            PlaceStep::LocalCompound {
                op,
                old,
                own_old,
                reg,
                dst,
                node,
            } => {
                self.at(node);
                let v = self.pop();
                super::ops::emit_op(self, op, &[old, v.reg], reg, node)?;
                self.release(v);
                if own_old {
                    self.fx.release(old);
                }
                self.deliver(
                    Val {
                        reg,
                        rel: Rel::Keep,
                    },
                    dst,
                    false,
                );
            }
            PlaceStep::Store {
                slot,
                op,
                old,
                dup,
                dst,
                node,
            } => {
                self.at(node);
                let v = self.pop();
                let v = match (op, old) {
                    (Some(op), Some(old)) => {
                        let r = self.fx.temp(ValType::Dyn);
                        super::ops::emit_op(self, op, &[old, v.reg], r, node)?;
                        self.release(v);
                        self.fx.release(old);
                        Val {
                            reg: r,
                            rel: Rel::Temp,
                        }
                    }
                    _ => self.transfer(v, dup),
                };
                self.write_slot_at(slot, v.reg, node)?;
                self.deliver(v, dst, false);
            }
            PlaceStep::Bind {
                idx,
                root,
                root_val,
                steps,
                nkeys,
            } => {
                let keys = self.pop_n(nkeys);
                let root_val = if root_val { Some(self.pop()) } else { None };
                if let Some(slot) = self.places.get_mut(idx as usize) {
                    *slot = EvPlace {
                        root: Some(root),
                        root_val,
                        steps,
                        keys,
                    };
                }
            }
            PlaceStep::Alias { binder, idx } => self.cx.set_slot(binder, Slot::Place(idx)),
            PlaceStep::Read { idx, node } => {
                self.at(node);
                let r = self.fx.temp(ValType::Dyn);
                let p = self.take_place(idx);
                let done = self.place_read(&p, r, node);
                self.put_place(idx, p);
                done?;
                self.vals.push(Val {
                    reg: r,
                    rel: Rel::Temp,
                });
            }
            PlaceStep::Combine { op, node } => {
                self.at(node);
                let v = self.pop();
                let old = self.pop();
                let r = self.fx.temp(ValType::Dyn);
                super::ops::emit_op(self, op, &[old.reg, v.reg], r, node)?;
                self.release(v);
                self.release(old);
                self.vals.push(Val {
                    reg: r,
                    rel: Rel::Temp,
                });
            }
            PlaceStep::Write {
                idx,
                dup,
                dst,
                node,
            } => {
                self.at(node);
                let v = self.pop();
                let v = self.transfer(v, dup);
                let p = self.take_place(idx);
                let r = self.place_write(&p, v.reg, node);
                self.put_place(idx, p);
                r?;
                self.deliver(v, dst, false);
            }
            PlaceStep::Ref { idx, node } => {
                self.at(node);
                let ct = self.cell_ty();
                let r = self.fx.temp(ct);
                let p = self.take_place(idx);
                let done = self.place_ref(&p, r, node);
                self.put_place(idx, p);
                done?;
                self.vals.push(Val {
                    reg: r,
                    rel: Rel::Temp,
                });
            }
            PlaceStep::BindRef { idx, dst, node } => {
                self.at(node);
                let src = self.pop();
                let p = self.take_place(idx);
                let r = self.place_bind(&p, src.reg, node);
                self.put_place(idx, p);
                r?;
                if dst != Dst::Discard {
                    let r = self.result_reg(dst);
                    self.emit(Inst::CellGet {
                        dst: r,
                        cell: src.reg,
                    });
                    self.produced(r, dst);
                }
                self.release(src);
            }
            PlaceStep::Drop { idx } => {
                let p = match self.places.get_mut(idx as usize) {
                    Some(slot) => core::mem::take(slot),
                    None => EvPlace::default(),
                };
                for k in p.keys {
                    self.release(k);
                }
                if let Some(r) = p.root_val {
                    self.release(r);
                }
            }
        }
        Ok(())
    }

    // ------------------------------------------------------------ accesses

    /// The key of a step as a `dyn` register, and whether the caller frees
    /// it.
    fn step_key(&mut self, s: PStep, keys: &[Val], ki: &mut usize) -> Option<(Reg, bool)> {
        match s {
            PStep::Index | PStep::DynProp => {
                let k = keys.get(*ki).map_or(Reg(0), |v| v.reg);
                *ki += 1;
                Some((k, false))
            }
            PStep::Elem(n) => {
                let k = self.fx.temp(ValType::Dyn);
                self.load_dyn_int(k, i64::from(n));
                Some((k, true))
            }
            PStep::Prop(_) | PStep::Append => None,
        }
    }

    /// Loads the root of a chain into a new temporary.
    fn load_root(&mut self, p: &EvPlace, node: NodeRef) -> Result<Reg, CompileError> {
        let cur = self.fx.temp(ValType::Dyn);
        match (p.root, p.root_val) {
            (Some(Root::Slot(s)), _) => self.read_slot_at(s, cur, node)?,
            (Some(Root::Cell), Some(v)) => self.emit(Inst::CellGet {
                dst: cur,
                cell: v.reg,
            }),
            (_, Some(v)) => self.emit(Inst::Mov {
                dst: cur,
                src: v.reg,
            }),
            _ => self.emit(Inst::LoadNil { dst: cur }),
        }
        Ok(cur)
    }

    /// `dst = place` (no auto-vivification: a missing key raises, or goes
    /// to the `get_index` hook, as a read does).
    pub(crate) fn place_read(
        &mut self,
        p: &EvPlace,
        dst: Reg,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let cur = self.load_root(p, node)?;
        let mut ki = 0usize;
        for &s in &p.steps {
            if s == PStep::Append {
                return Err(CompileError::NotAssignable {
                    node,
                    span: self.cx.span(node),
                });
            }
            match (s, self.step_key(s, &p.keys, &mut ki)) {
                (PStep::Prop(name), _) => self.prop_get(cur, cur, name),
                (PStep::Index, Some((k, own))) => {
                    self.index_read(cur, cur, k);
                    if own {
                        self.fx.release(k);
                    }
                }
                (PStep::DynProp, Some((k, _))) => {
                    self.dyn_access(crate::unit::DynOp::Get, cur, cur, k, None);
                }
                (_, Some((k, own))) => {
                    self.emit(Inst::DGetIndex {
                        dst: cur,
                        obj: cur,
                        key: k,
                    });
                    if own {
                        self.fx.release(k);
                    }
                }
                (_, None) => {}
            }
        }
        self.emit(Inst::Mov { dst, src: cur });
        self.fx.release(cur);
        Ok(())
    }

    /// The container the last step of a place writes into, in a new
    /// temporary: the root, then every step but the last, creating missing
    /// or null intermediate arrays and separating shared ones under PHP
    /// arrays (LSB §5.16).
    fn place_container(&mut self, p: &EvPlace, node: NodeRef) -> Result<Reg, CompileError> {
        let php = self.php();
        let cur = self.load_root(p, node)?;
        let b = self.fx.temp(ValType::Bool);
        if php {
            // Writing into null creates the array (auto-vivification).
            let have = self.label();
            self.emit(Inst::IsKind {
                dst: b,
                src: cur,
                kind: Kind::Nil,
            });
            self.jump_on(b, have, false);
            let m = self.new_map();
            self.emit(Inst::Mov { dst: cur, src: m });
            self.fx.release(m);
            match (p.root, p.root_val) {
                (Some(Root::Slot(s)), _) => self.write_slot_at(s, cur, node)?,
                (Some(Root::Cell), Some(v)) => self.emit(Inst::CellSet {
                    cell: v.reg,
                    src: cur,
                }),
                _ => {}
            }
            self.bind(have);
        }
        let mut ki = 0usize;
        let last = p.steps.len().saturating_sub(1);
        for (i, &s) in p.steps.iter().enumerate() {
            if i == last {
                break;
            }
            let key = self.step_key(s, &p.keys, &mut ki);
            self.descend(s, cur, key.map(|(k, _)| k), b, php);
            if let Some((k, true)) = key {
                self.fx.release(k);
            }
        }
        self.fx.release(b);
        Ok(cur)
    }

    /// Moves `cur` one intermediate step down a write chain.
    fn descend(&mut self, s: PStep, cur: Reg, key: Option<Reg>, b: Reg, php: bool) {
        if s == PStep::Append {
            // `$a[][...] = v`: a new array appended to a map.
            let map_ty = self.map_ty();
            let tr = self.map_ref();
            let bad = self.label();
            let done = self.label();
            self.emit(Inst::IsType {
                dst: b,
                src: cur,
                ty: tr,
            });
            self.jump_on(b, bad, false);
            let m = self.fx.temp(map_ty);
            self.emit(Inst::Cast {
                dst: m,
                src: cur,
                ty: tr,
            });
            let n = self.new_map();
            self.emit(Inst::MapPush { map: m, src: n });
            self.emit(Inst::Mov { dst: cur, src: n });
            self.fx.release(n);
            self.fx.release(m);
            self.jmp(done);
            self.bind(bad);
            self.raise_type_error();
            self.bind(done);
            return;
        }
        if !php {
            // Shared references: read the child as an expression would.
            match (s, key) {
                (PStep::Prop(name), _) => self.prop_get(cur, cur, name),
                (_, Some(k)) => self.emit(Inst::DGetIndex {
                    dst: cur,
                    obj: cur,
                    key: k,
                }),
                (_, None) => {}
            }
            return;
        }
        // PHP: separate the child if another container may share it, and
        // create it when it is absent or null.
        let child = self.fx.temp(ValType::Dyn);
        let have = self.label();
        match (s, key) {
            (PStep::Prop(name), _) => {
                self.select(cur, crate::class::Ns::Prop, name, |g, n| {
                    let set = g.label();
                    g.emit(Inst::DSepProp {
                        dst: child,
                        obj: cur,
                        name: n,
                    });
                    g.emit(Inst::IsKind {
                        dst: b,
                        src: child,
                        kind: Kind::Nil,
                    });
                    g.jump_on(b, set, false);
                    let m = g.new_map();
                    g.emit(Inst::Mov { dst: child, src: m });
                    g.fx.release(m);
                    g.emit(Inst::SetProp {
                        obj: cur,
                        name: n,
                        src: child,
                    });
                    g.bind(set);
                });
            }
            (_, Some(k)) => {
                self.emit(Inst::DSepIndex {
                    dst: child,
                    obj: cur,
                    key: k,
                });
                self.emit(Inst::IsKind {
                    dst: b,
                    src: child,
                    kind: Kind::Nil,
                });
                self.jump_on(b, have, false);
                let m = self.new_map();
                self.emit(Inst::Mov { dst: child, src: m });
                self.fx.release(m);
                self.emit(Inst::DSetIndex {
                    obj: cur,
                    key: k,
                    src: child,
                });
            }
            (_, None) => {}
        }
        self.bind(have);
        self.emit(Inst::Mov {
            dst: cur,
            src: child,
        });
        self.fx.release(child);
    }

    /// `place = v`.
    pub(crate) fn place_write(
        &mut self,
        p: &EvPlace,
        v: Reg,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let Some(&last) = p.steps.last() else {
            return match (p.root, p.root_val) {
                (Some(Root::Slot(s)), _) => self.write_slot_at(s, v, node),
                (Some(Root::Cell), Some(c)) => {
                    self.emit(Inst::CellSet {
                        cell: c.reg,
                        src: v,
                    });
                    Ok(())
                }
                _ => Err(CompileError::NotAssignable {
                    node,
                    span: self.cx.span(node),
                }),
            };
        };
        let cur = self.place_container(p, node)?;
        let mut ki = p.steps.iter().filter(|s| s.keyed()).count();
        if last.keyed() {
            ki -= 1;
        }
        match (last, self.step_key(last, &p.keys, &mut ki)) {
            (PStep::Prop(name), _) => self.prop_set(cur, name, v),
            (PStep::DynProp, Some((k, _))) => {
                let t = self.fx.temp(ValType::Dyn);
                self.dyn_access(crate::unit::DynOp::Set, t, cur, k, Some(v));
                self.fx.release(t);
            }
            (PStep::Append, _) => {
                let map_ty = self.map_ty();
                let tr = self.map_ref();
                let b = self.fx.temp(ValType::Bool);
                let bad = self.label();
                let done = self.label();
                self.emit(Inst::IsType {
                    dst: b,
                    src: cur,
                    ty: tr,
                });
                self.jump_on(b, bad, false);
                let m = self.fx.temp(map_ty);
                self.emit(Inst::Cast {
                    dst: m,
                    src: cur,
                    ty: tr,
                });
                self.emit(Inst::MapPush { map: m, src: v });
                self.fx.release(m);
                self.jmp(done);
                self.bind(bad);
                self.raise_type_error();
                self.bind(done);
                self.fx.release(b);
            }
            (_, Some((k, own))) => {
                self.emit(Inst::DSetIndex {
                    obj: cur,
                    key: k,
                    src: v,
                });
                if own {
                    self.fx.release(k);
                }
            }
            (_, None) => {}
        }
        self.fx.release(cur);
        Ok(())
    }

    /// `dst = &place`: the variable's reference, or a reference to the slot
    /// (`dref_*`: the slot becomes a reference slot, LSB §5.17).
    pub(crate) fn place_ref(
        &mut self,
        p: &EvPlace,
        dst: Reg,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let Some(&last) = p.steps.last() else {
            return match (p.root, p.root_val) {
                (Some(Root::Slot(Slot::Cell(c))), _) => {
                    self.emit(Inst::Mov { dst, src: c });
                    Ok(())
                }
                (Some(Root::Slot(Slot::GlobalCell(g))), _) => {
                    self.emit(Inst::GetGlobal { dst, global: g });
                    Ok(())
                }
                (Some(Root::Cell), Some(c)) => {
                    self.emit(Inst::Mov { dst, src: c.reg });
                    Ok(())
                }
                _ => Err(self.cx.unsupported(Unsupported::RefPlace, node)),
            };
        };
        let cur = self.place_container(p, node)?;
        let mut ki = p.steps.iter().filter(|s| s.keyed()).count();
        if last.keyed() {
            ki -= 1;
        }
        match (last, self.step_key(last, &p.keys, &mut ki)) {
            (PStep::Prop(name), _) => self.prop_ref(dst, cur, name),
            (_, Some((k, own))) => {
                self.emit(Inst::DRefIndex {
                    dst,
                    obj: cur,
                    key: k,
                });
                if own {
                    self.fx.release(k);
                }
            }
            _ => return Err(self.cx.unsupported(Unsupported::RefPlace, node)),
        }
        self.fx.release(cur);
        Ok(())
    }

    /// Makes the place an alias of the reference in `src`: a variable now
    /// names it; a slot becomes it (`dbind_*`).
    fn place_bind(&mut self, p: &EvPlace, src: Reg, node: NodeRef) -> Result<(), CompileError> {
        let Some(&last) = p.steps.last() else {
            return match p.root {
                Some(Root::Slot(Slot::Cell(c))) => {
                    self.emit(Inst::Mov { dst: c, src });
                    Ok(())
                }
                Some(Root::Slot(Slot::GlobalCell(g))) => {
                    self.emit(Inst::SetGlobal { global: g, src });
                    Ok(())
                }
                Some(Root::Cell) => Err(self.cx.unsupported(Unsupported::StaticRef, node)),
                _ => Err(self.cx.unsupported(Unsupported::RefPlace, node)),
            };
        };
        let cur = self.place_container(p, node)?;
        let mut ki = p.steps.iter().filter(|s| s.keyed()).count();
        if last.keyed() {
            ki -= 1;
        }
        match (last, self.step_key(last, &p.keys, &mut ki)) {
            (PStep::Prop(name), _) => self.prop_bind(cur, name, src),
            (_, Some((k, own))) => {
                self.emit(Inst::DBindIndex {
                    obj: cur,
                    key: k,
                    src,
                });
                if own {
                    self.fx.release(k);
                }
            }
            _ => return Err(self.cx.unsupported(Unsupported::RefPlace, node)),
        }
        self.fx.release(cur);
        Ok(())
    }

    /// Reads a variable, an alias included.
    pub(crate) fn read_slot_at(
        &mut self,
        slot: Slot,
        dst: Reg,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        match slot {
            Slot::Place(i) => {
                let p = self.take_place(i);
                let r = self.place_read(&p, dst, node);
                self.put_place(i, p);
                r
            }
            s => {
                self.read_var(s, dst);
                Ok(())
            }
        }
    }

    /// Writes a variable, an alias included.
    pub(crate) fn write_slot_at(
        &mut self,
        slot: Slot,
        src: Reg,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        match slot {
            Slot::Place(i) => {
                let p = self.take_place(i);
                let r = self.place_write(&p, src, node);
                self.put_place(i, p);
                r
            }
            s => {
                self.write_var(s, src);
                Ok(())
            }
        }
    }

    /// Normalizes a map key (PHP key coercion): integers pass; anything else
    /// goes through the module's `<php_key>` function.
    pub(crate) fn coerce_key(&mut self, k: Val) -> Val {
        if self.cx.opts.keys() != KeyCoercion::Php {
            return k;
        }
        let out = self.fx.temp(ValType::Dyn);
        let b = self.fx.temp(ValType::Bool);
        let done = self.label();
        self.emit(Inst::Mov {
            dst: out,
            src: k.reg,
        });
        self.emit(Inst::IsKind {
            dst: b,
            src: k.reg,
            kind: Kind::Int,
        });
        self.jump_on(b, done, true);
        let f = self.cx.php_key();
        let win = self.fx.window(&[ValType::Dyn, ValType::Dyn]);
        self.emit(Inst::Mov {
            dst: crate::func::FnCx::slot(win.1, 1),
            src: k.reg,
        });
        self.emit(Inst::Call {
            dst: win.1,
            func: f,
            argc: 1,
        });
        self.emit(Inst::Mov {
            dst: out,
            src: win.1,
        });
        self.fx.release_window(win.0, win.1);
        self.bind(done);
        self.fx.release(b);
        self.release(k);
        Val {
            reg: out,
            rel: Rel::Temp,
        }
    }
}

/// The last step of a place expression (without resolving aliases): what an
/// `Append` check needs before anything is evaluated.
fn last_step(e: ExprId, hir: &hir_lang::Hir) -> Option<PStep> {
    match *hir.expr(e) {
        Expr::Append(_) => Some(PStep::Append),
        Expr::Index { .. } => Some(PStep::Index),
        Expr::DynField { .. } => Some(PStep::DynProp),
        Expr::Field { member, .. } => Some(match member {
            Member::Named(s) => PStep::Prop(s),
            Member::Index(i) => PStep::Elem(i),
        }),
        _ => None,
    }
}
