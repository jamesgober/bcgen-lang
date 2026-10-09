//! One walk over the unit before code generation: which items exist, which
//! variables must live in cells, and what each closure captures.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec;
use alloc::vec::Vec;

use hir_lang::{
    BinderId, CaptureMode, Control, Event, Expr, ExprId, Hir, IdKind, ItemId, ItemKind, NodeRef,
    Pat, Res,
};

/// What code generation needs to know about the whole unit up front.
pub(crate) struct Analysis {
    /// Per binder: the variable is shared (captured by reference, aliased by
    /// a reference assignment, passed by reference, or a by-reference
    /// parameter), so it lives in a cell.
    pub(crate) cell: Vec<bool>,
    /// Per closure: the outer value binders it uses (implicit captures,
    /// transitively through nested closures), in first-use order.
    pub(crate) captures: BTreeMap<ExprId, Vec<BinderId>>,
    /// Function items, in canonical (pre)order.
    pub(crate) fns: Vec<ItemId>,
    /// Global and constant items, in canonical order.
    pub(crate) globals: Vec<ItemId>,
    /// Items the start function may need to run code for (globals,
    /// constants, functions with once-evaluated defaults, nested modules),
    /// in canonical order.
    pub(crate) inits: Vec<ItemId>,
    /// Nested modules with a body, in canonical order (their bodies run in
    /// the start function).
    pub(crate) module_bodies: Vec<ItemId>,
    /// The first item kind with code this release does not compile.
    pub(crate) unsupported_item: Option<ItemId>,
    /// Some argument is passed as a place, so by-value parameters of
    /// dynamically called functions must unwrap cells.
    pub(crate) place_args: bool,
    /// Global items shared by reference (through a `global` alias, a place
    /// argument, or a reference assignment): their storage is a cell.
    pub(crate) cell_globals: BTreeSet<ItemId>,
}

impl Analysis {
    pub(crate) fn new(hir: &Hir) -> Self {
        let mut a = Analysis {
            cell: vec![false; hir.count(IdKind::Binder)],
            captures: BTreeMap::new(),
            fns: Vec::new(),
            globals: Vec::new(),
            module_bodies: Vec::new(),
            inits: Vec::new(),
            unsupported_item: None,
            place_args: false,
            cell_globals: BTreeSet::new(),
        };
        let mut aliases: Vec<(BinderId, hir_lang::PathId)> = Vec::new();
        let mut by_ref_closures: BTreeSet<ExprId> = BTreeSet::new();
        let mut closures = false;
        hir.walk_from(NodeRef::Item(hir.root()), |event| {
            match event {
                Event::Enter(NodeRef::Item(id)) => a.item(hir, id),
                Event::Enter(NodeRef::Param(id)) => {
                    let p = hir.param(id);
                    if p.by_ref {
                        if let Pat::Bind { binder, .. } = *hir.pat(p.pat) {
                            a.mark(binder);
                        }
                    }
                }
                Event::Enter(NodeRef::Expr(id)) => {
                    closures |= matches!(hir.expr(id), Expr::Closure(_));
                    a.expr(hir, id, &mut by_ref_closures);
                }
                Event::Enter(NodeRef::Stmt(id)) => {
                    if let hir_lang::Stmt::Global { binder, path } = *hir.stmt(id) {
                        aliases.push((binder, path));
                    }
                }
                _ => {}
            }
            Control::Continue
        });
        if closures {
            for (closure, binders) in hir.all_implicit_captures() {
                if by_ref_closures.contains(&closure) {
                    for &b in &binders {
                        a.mark(b);
                    }
                }
                if !binders.is_empty() {
                    let _ = a.captures.insert(closure, binders);
                }
            }
        }
        for (b, p) in aliases {
            if a.cell.get(b.index()).copied().unwrap_or(false) {
                a.mark_global(hir, hir.path(p).res);
            }
        }
        a
    }

    /// Marks the global item a resolution names (in this unit) as shared.
    fn mark_global(&mut self, hir: &Hir, res: Res) {
        if let Res::Def(d) = res {
            if d.unit() == hir.unit() {
                if let hir_lang::Def::Item(i) = d.def() {
                    if matches!(hir.item(i).kind, ItemKind::Global { .. }) {
                        let _ = self.cell_globals.insert(i);
                    }
                }
            }
        }
    }

    fn mark(&mut self, b: BinderId) {
        if let Some(slot) = self.cell.get_mut(b.index()) {
            *slot = true;
        }
    }

    fn mark_path_local(&mut self, hir: &Hir, e: ExprId) {
        if let Expr::Path(p) = *hir.expr(e) {
            match hir.path(p).res {
                Res::Local(b) => self.mark(b),
                res => self.mark_global(hir, res),
            }
        }
    }

    fn item(&mut self, hir: &Hir, id: ItemId) {
        if matches!(
            hir.item(id).kind,
            ItemKind::Fn(_)
                | ItemKind::Global { .. }
                | ItemKind::Const { .. }
                | ItemKind::Module { .. }
        ) {
            self.inits.push(id);
        }
        match hir.item(id).kind {
            ItemKind::Fn(_) => self.fns.push(id),
            ItemKind::Global { .. } | ItemKind::Const { .. } => self.globals.push(id),
            ItemKind::Module { body: Some(_), .. } if id != hir.root() => {
                self.module_bodies.push(id);
            }
            ItemKind::Class(_) | ItemKind::Impl(_) | ItemKind::MixinUse(_)
                if self.unsupported_item.is_none() =>
            {
                self.unsupported_item = Some(id);
            }
            _ => {}
        }
    }

    fn expr(&mut self, hir: &Hir, id: ExprId, by_ref_closures: &mut BTreeSet<ExprId>) {
        match *hir.expr(id) {
            Expr::Closure(c) => {
                if let Some(b) = c.self_binder {
                    self.mark(b);
                }
                for cap in hir.list(c.captures) {
                    if matches!(cap.mode, CaptureMode::ByRef | CaptureMode::ByMutRef) {
                        if let Res::Local(b) = hir.path(cap.outer).res {
                            self.mark(b);
                        }
                        self.mark(cap.binder);
                    }
                }
                // Implicit captures by reference (or inferred, which the
                // dynamic profile takes by reference) share the variable.
                if matches!(
                    c.implicit,
                    Some(CaptureMode::ByRef | CaptureMode::ByMutRef | CaptureMode::Infer)
                ) {
                    let _ = by_ref_closures.insert(id);
                }
            }
            Expr::RefAssign { target, source } => {
                self.mark_path_local(hir, target);
                self.mark_path_local(hir, source);
            }
            Expr::Call { args, .. }
            | Expr::MethodCall { args, .. }
            | Expr::DynMethodCall { args, .. } => {
                for arg in hir.list(args) {
                    if arg.place {
                        self.place_args = true;
                        self.mark_path_local(hir, arg.value);
                    }
                }
            }
            _ => {}
        }
    }
}
