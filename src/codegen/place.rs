//! Assignment to places: variables, globals, and chains of index, property,
//! and append steps, with PHP's auto-vivification and copy-on-write
//! separation under [`ArraySemantics::Php`](crate::ArraySemantics::Php).

use alloc::vec::Vec;

use bytecode_lang::{Inst, Kind, Reg, ValType};
use hir_lang::{Expr, ExprId, ItemKind, Member, NodeRef, Op, Res, Symbol};
use intern_lang::Lookup;

use super::{Dst, Gen, Rel, Step, Task, Val};
use crate::error::{CompileError, Unsupported};
use crate::options::KeyCoercion;
use crate::unit::Slot;

/// One step of a place chain, from the root outward.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PStep {
    /// `[key]`: the key is on the value stack (normalized).
    Index,
    /// `->$name`: the name is on the value stack (not normalized).
    DynProp,
    /// `.name`.
    Prop(Symbol),
    /// `.0`.
    Elem(u32),
    /// `[]`.
    Append,
}

/// Where a place chain starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Root {
    /// A variable or global (written back when a write creates the array).
    Slot(Slot),
    /// Any other expression, evaluated to a temporary (on the value stack).
    Value,
}

/// The continuation steps of assignments.
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
    /// `x = v` / `x op= v` for a cell or global variable.
    Store {
        slot: Slot,
        op: Option<Op>,
        old: Option<Reg>,
        dup: bool,
        dst: Dst,
        node: NodeRef,
    },
    /// Reads the current value at the end of a chain (compound assignment).
    ChainRead {
        root: Root,
        steps: Vec<PStep>,
        node: NodeRef,
    },
    /// Combines the old value (below) with the assigned one (on top).
    Combine { op: Op, node: NodeRef },
    /// Writes the value on top of the stack through the chain.
    ChainWrite {
        root: Root,
        steps: Vec<PStep>,
        dup: bool,
        dst: Dst,
        node: NodeRef,
    },
}

impl<L: Lookup> Gen<'_, '_, L> {
    /// The slot a path names as an assignment target.
    fn place_slot(&self, e: ExprId) -> Result<Option<Slot>, CompileError> {
        let node = NodeRef::Expr(e);
        let hir = self.cx.hir;
        let Expr::Path(p) = *hir.expr(e) else {
            return Ok(None);
        };
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
        match *hir.expr(target) {
            Expr::Path(_) => {
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
                        let old = op.map(|_| {
                            let t = self.fx.temp(ValType::Dyn);
                            self.read_slot(slot, t);
                            t
                        });
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
            }
            Expr::Index { .. } | Expr::Field { .. } | Expr::DynField { .. } | Expr::Append(_) => {
                let (root, root_expr, steps, keys) = self.chain(target)?;
                if op.is_some() && steps.contains(&PStep::Append) {
                    return Err(CompileError::NotAssignable {
                        node: tnode,
                        span: self.cx.span(tnode),
                    });
                }
                let mut ts: Vec<Task> = Vec::new();
                if let Some(re) = root_expr {
                    ts.push(Task::Expr(re, Dst::Temp));
                }
                for (k, is_index) in keys {
                    ts.push(Task::Expr(k, Dst::Temp));
                    if is_index {
                        ts.push(Task::CoerceKey(node));
                    }
                }
                if let Some(op) = op {
                    ts.push(Task::Step(Step::Place(PlaceStep::ChainRead {
                        root,
                        steps: steps.clone(),
                        node,
                    })));
                    ts.push(Task::Expr(value, Dst::Any));
                    ts.push(Task::Step(Step::Place(PlaceStep::Combine { op, node })));
                } else {
                    ts.push(Task::Expr(value, Dst::Any));
                }
                ts.push(Task::Step(Step::Place(PlaceStep::ChainWrite {
                    root,
                    steps,
                    dup: dup && op.is_none(),
                    dst,
                    node,
                })));
                for t in ts.into_iter().rev() {
                    self.tasks.push(t);
                }
            }
            Expr::VarVar(_) => return Err(self.cx.unsupported(Unsupported::VarVar, tnode)),
            Expr::Deref(_) => return Err(self.cx.unsupported(Unsupported::Reference, tnode)),
            Expr::Err => {
                return Err(CompileError::ErrorNode {
                    node: tnode,
                    span: self.cx.span(tnode),
                });
            }
            _ => {
                return Err(CompileError::NotAssignable {
                    node: tnode,
                    span: self.cx.span(tnode),
                });
            }
        }
        Ok(())
    }

    /// Decomposes a place into its root and steps (root first), with the
    /// key expressions to evaluate in order (and whether each is an index
    /// key, which PHP normalizes).
    #[allow(clippy::type_complexity)]
    fn chain(
        &self,
        target: ExprId,
    ) -> Result<(Root, Option<ExprId>, Vec<PStep>, Vec<(ExprId, bool)>), CompileError> {
        let hir = self.cx.hir;
        let mut steps: Vec<PStep> = Vec::new();
        let mut keys: Vec<(ExprId, bool)> = Vec::new();
        let mut cur = target;
        let root = loop {
            match *hir.expr(cur) {
                Expr::Index { base, index } => {
                    steps.push(PStep::Index);
                    keys.push((index, true));
                    cur = base;
                }
                Expr::DynField { base, name } => {
                    steps.push(PStep::DynProp);
                    keys.push((name, false));
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
                Expr::Path(_) => match self.place_slot(cur) {
                    Ok(Some(s)) => break (Root::Slot(s), None),
                    Ok(None) => {
                        let node = NodeRef::Expr(cur);
                        return Err(CompileError::Unresolved {
                            node,
                            span: self.cx.span(node),
                        });
                    }
                    // A path that is not a variable (a function, a
                    // constant): an ordinary value root.
                    Err(CompileError::NotAssignable { .. }) => break (Root::Value, Some(cur)),
                    Err(e) => return Err(e),
                },
                _ => break (Root::Value, Some(cur)),
            }
        };
        steps.reverse();
        keys.reverse();
        Ok((root.0, root.1, steps, keys))
    }

    pub(crate) fn ref_assign(
        &mut self,
        e: ExprId,
        target: ExprId,
        source: ExprId,
        dst: Dst,
    ) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        let t = self.place_slot(target).ok().flatten();
        let s = self.place_slot(source).ok().flatten();
        match (t, s) {
            (Some(Slot::Cell(tc)), Some(s @ (Slot::Cell(_) | Slot::GlobalCell(_)))) => {
                // The target variable now names the source's cell.
                if let Some((sc, owned)) = self.cell_of(s) {
                    self.emit(Inst::Mov { dst: tc, src: sc });
                    if owned {
                        self.fx.release(sc);
                    }
                }
                if dst != Dst::Discard {
                    let r = self.result_reg(dst);
                    self.emit(Inst::CellGet { dst: r, cell: tc });
                    self.produced(r, dst);
                }
                Ok(())
            }
            _ => Err(self.cx.unsupported(Unsupported::RefPlace, node)),
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
                self.write_slot(slot, v.reg);
                self.deliver(v, dst, false);
            }
            PlaceStep::ChainRead { root, steps, node } => {
                self.at(node);
                let nkeys = steps
                    .iter()
                    .filter(|s| matches!(s, PStep::Index | PStep::DynProp))
                    .count();
                let base = self.vals.len().saturating_sub(nkeys);
                let keys: Vec<Reg> = self
                    .vals
                    .get(base..)
                    .map_or(Vec::new(), |v| v.iter().map(|v| v.reg).collect());
                let root_val = match root {
                    Root::Value => self.vals.get(base.saturating_sub(1)).map(|v| v.reg),
                    Root::Slot(_) => None,
                };
                let cur = self.fx.temp(ValType::Dyn);
                match (root, root_val) {
                    (Root::Slot(s), _) => self.read_slot(s, cur),
                    (Root::Value, Some(r)) => self.emit(Inst::Mov { dst: cur, src: r }),
                    (Root::Value, None) => self.emit(Inst::LoadNil { dst: cur }),
                }
                let mut ki = 0usize;
                for s in &steps {
                    match *s {
                        PStep::Index | PStep::DynProp => {
                            let k = keys.get(ki).copied().unwrap_or(Reg(0));
                            ki += 1;
                            self.emit(Inst::DGetIndex {
                                dst: cur,
                                obj: cur,
                                key: k,
                            });
                        }
                        PStep::Elem(i) => {
                            let k = self.fx.temp(ValType::Dyn);
                            self.load_dyn_int(k, i64::from(i));
                            self.emit(Inst::DGetIndex {
                                dst: cur,
                                obj: cur,
                                key: k,
                            });
                            self.fx.release(k);
                        }
                        PStep::Prop(name) => {
                            let n = self.name_ref(name);
                            self.emit(Inst::GetProp {
                                dst: cur,
                                obj: cur,
                                name: n,
                            });
                        }
                        PStep::Append => {}
                    }
                }
                self.vals.push(Val {
                    reg: cur,
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
            PlaceStep::ChainWrite {
                root,
                steps,
                dup,
                dst,
                node,
            } => {
                self.at(node);
                let v = self.pop();
                let v = self.transfer(v, dup);
                let nkeys = steps
                    .iter()
                    .filter(|s| matches!(s, PStep::Index | PStep::DynProp))
                    .count();
                let keys = self.pop_n(nkeys);
                let root_val = match root {
                    Root::Value => Some(self.pop()),
                    Root::Slot(_) => None,
                };
                self.chain_write(root, root_val.map(|r| r.reg), &steps, &keys, v.reg);
                for k in keys {
                    self.release(k);
                }
                if let Some(r) = root_val {
                    self.release(r);
                }
                self.deliver(v, dst, false);
            }
        }
        Ok(())
    }

    /// Writes `v` through the chain.
    fn chain_write(
        &mut self,
        root: Root,
        root_val: Option<Reg>,
        steps: &[PStep],
        keys: &[Val],
        v: Reg,
    ) {
        let php = self.php();
        let map_ty = self.map_ty();
        let tr = self.map_ref();
        let cur = self.fx.temp(ValType::Dyn);
        let b = self.fx.temp(ValType::Bool);
        match (root, root_val) {
            (Root::Slot(s), _) => self.read_slot(s, cur),
            (Root::Value, Some(r)) => self.emit(Inst::Mov { dst: cur, src: r }),
            (Root::Value, None) => self.emit(Inst::LoadNil { dst: cur }),
        }
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
            if let Root::Slot(s) = root {
                self.write_slot(s, cur);
            }
            self.bind(have);
        }
        let mut ki = 0usize;
        let last = steps.len().saturating_sub(1);
        for (i, s) in steps.iter().enumerate() {
            // The key of a keyed step, as a `dyn` value.
            let (key, own) = match *s {
                PStep::Index | PStep::DynProp => {
                    let k = keys.get(ki).map_or(Reg(0), |v| v.reg);
                    ki += 1;
                    (Some(k), false)
                }
                PStep::Elem(n) => {
                    let k = self.fx.temp(ValType::Dyn);
                    self.load_dyn_int(k, i64::from(n));
                    (Some(k), true)
                }
                PStep::Prop(name) => (Some(self.load_name(name)), true),
                PStep::Append => (None, false),
            };
            if i == last {
                match (*s, key) {
                    (PStep::Prop(name), _) => {
                        let n = self.name_ref(name);
                        self.emit(Inst::SetProp {
                            obj: cur,
                            name: n,
                            src: v,
                        });
                    }
                    (PStep::Append, _) => {
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
                    }
                    (_, Some(k)) => self.emit(Inst::DSetIndex {
                        obj: cur,
                        key: k,
                        src: v,
                    }),
                    (_, None) => {}
                }
            } else {
                self.chain_step(*s, cur, key, b, php);
            }
            if own {
                if let Some(k) = key {
                    self.fx.release(k);
                }
            }
        }
        self.fx.release(b);
        self.fx.release(cur);
    }

    /// Moves `cur` one intermediate step down a write chain: to the child
    /// array, creating it when absent or null (PHP), separating it from any
    /// copy that shares it (PHP), and storing it back into its container.
    fn chain_step(&mut self, s: PStep, cur: Reg, key: Option<Reg>, b: Reg, php: bool) {
        let map_ty = self.map_ty();
        let tr = self.map_ref();
        if !php {
            // Shared references: read the child as an expression would.
            match (s, key) {
                (PStep::Prop(name), _) => {
                    let n = self.name_ref(name);
                    self.emit(Inst::GetProp {
                        dst: cur,
                        obj: cur,
                        name: n,
                    });
                    return;
                }
                (PStep::Append, _) => {}
                (_, Some(k)) => {
                    self.emit(Inst::DGetIndex {
                        dst: cur,
                        obj: cur,
                        key: k,
                    });
                    return;
                }
                (_, None) => return,
            }
        }
        let other = self.label();
        let done = self.label();
        self.emit(Inst::IsType {
            dst: b,
            src: cur,
            ty: tr,
        });
        self.jump_on(b, other, false);
        let m = self.fx.temp(map_ty);
        self.emit(Inst::Cast {
            dst: m,
            src: cur,
            ty: tr,
        });
        match (s, key) {
            (PStep::Append, _) => {
                // `$a[][...] = v`: a new array appended.
                let n = self.new_map();
                self.emit(Inst::MapPush { map: m, src: n });
                self.emit(Inst::Mov { dst: cur, src: n });
                self.fx.release(n);
            }
            (_, Some(k)) if php => {
                let sep = self.label();
                let child = self.fx.temp(ValType::Dyn);
                self.emit(Inst::MapFind {
                    dst: child,
                    map: m,
                    key: k,
                });
                self.emit(Inst::IsKind {
                    dst: b,
                    src: child,
                    kind: Kind::Nil,
                });
                self.jump_on(b, sep, false);
                let n = self.new_map();
                self.emit(Inst::Mov { dst: child, src: n });
                self.fx.release(n);
                self.emit(Inst::MapSet {
                    map: m,
                    key: k,
                    src: child,
                });
                self.emit(Inst::Mov {
                    dst: cur,
                    src: child,
                });
                self.jmp(done);
                self.bind(sep);
                let keep = self.label();
                self.emit(Inst::IsKind {
                    dst: b,
                    src: child,
                    kind: Kind::Map,
                });
                self.jump_on(b, keep, false);
                self.emit(Inst::Dup {
                    dst: child,
                    src: child,
                });
                self.emit(Inst::MapSet {
                    map: m,
                    key: k,
                    src: child,
                });
                self.bind(keep);
                self.emit(Inst::Mov {
                    dst: cur,
                    src: child,
                });
                self.fx.release(child);
            }
            (_, _) => {}
        }
        self.fx.release(m);
        self.jmp(done);
        // Not a map: the dynamic instructions (and their hooks) decide.
        self.bind(other);
        match (s, key) {
            (PStep::Prop(name), _) => {
                let n = self.name_ref(name);
                self.emit(Inst::GetProp {
                    dst: cur,
                    obj: cur,
                    name: n,
                });
            }
            (PStep::Append, _) => self.raise_type_error(),
            (_, Some(k)) => self.emit(Inst::DGetIndex {
                dst: cur,
                obj: cur,
                key: k,
            }),
            (_, None) => {}
        }
        self.bind(done);
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
