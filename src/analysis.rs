//! One walk over the unit before code generation: which items exist, which
//! variables must live in LSB references, and what each closure captures.

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
    /// parameter), so it lives in an LSB reference.
    pub(crate) cell: Vec<bool>,
    /// Per closure: the outer value binders it uses (implicit captures,
    /// transitively through nested closures), in first-use order.
    pub(crate) captures: BTreeMap<ExprId, Vec<BinderId>>,
    /// Function items that are not class members, in canonical (pre)order.
    pub(crate) fns: Vec<ItemId>,
    /// Global and constant items that are not class members, in canonical
    /// order.
    pub(crate) globals: Vec<ItemId>,
    /// Class and interface items (mixins included), in canonical order.
    pub(crate) classes: Vec<ItemId>,
    /// Items declared directly in a class or interface: methods, static
    /// properties, constants, aliases, mixin uses.
    pub(crate) members: BTreeSet<ItemId>,
    /// Items the start function may need to run code for (globals,
    /// constants, functions with once-evaluated defaults, nested modules,
    /// classes), in canonical order.
    pub(crate) inits: Vec<ItemId>,
    /// Nested modules with a body, in canonical order (their bodies run in
    /// the start function).
    pub(crate) module_bodies: Vec<ItemId>,
    /// The first `impl` block (this release does not compile them).
    pub(crate) unsupported_item: Option<ItemId>,
    /// Global items shared by reference (through a `global` alias, a place
    /// argument, or a reference assignment): their storage is a reference.
    pub(crate) cell_globals: BTreeSet<ItemId>,
    /// `let_place` aliases: the place each `Place` binder names, so marking
    /// an alias as shared marks the variable behind it.
    places: BTreeMap<BinderId, ExprId>,
}

impl Analysis {
    pub(crate) fn new(hir: &Hir) -> Self {
        let mut a = Analysis {
            cell: vec![false; hir.count(IdKind::Binder)],
            captures: BTreeMap::new(),
            fns: Vec::new(),
            globals: Vec::new(),
            classes: Vec::new(),
            members: BTreeSet::new(),
            module_bodies: Vec::new(),
            inits: Vec::new(),
            unsupported_item: None,
            cell_globals: BTreeSet::new(),
            places: BTreeMap::new(),
        };
        let mut aliases: Vec<(BinderId, hir_lang::PathId)> = Vec::new();
        let mut by_ref_closures: BTreeSet<ExprId> = BTreeSet::new();
        let mut closures = false;
        // The items enclosing the walk's position.
        let mut items: Vec<ItemId> = Vec::new();
        hir.walk_from(NodeRef::Item(hir.root()), |event| {
            match event {
                Event::Enter(NodeRef::Item(id)) => {
                    let in_class = items.last().is_some_and(|&p| {
                        matches!(
                            hir.item(p).kind,
                            ItemKind::Class(_) | ItemKind::Interface(_)
                        )
                    });
                    if in_class {
                        let _ = a.members.insert(id);
                    }
                    a.item(hir, id, in_class);
                    items.push(id);
                }
                Event::Leave(NodeRef::Item(_)) => {
                    let _ = items.pop();
                }
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
        // The walk is pre-order, so a nested module's entry precedes the
        // declarations inside it (and those of the modules after it). Its
        // body is code that reads them, so it must run after every
        // initializer, not at the module's own position: otherwise
        // `namespace A; class S { const C = [1]; } echo S::C;` reads the
        // constant before the start function computes it. A stable partition
        // (linear) keeps each group in canonical order.
        let (decls, bodies): (Vec<ItemId>, Vec<ItemId>) = a
            .inits
            .iter()
            .partition(|&&id| !matches!(hir.item(id).kind, ItemKind::Module { body: Some(_), .. }));
        a.inits = decls;
        a.inits.extend(bodies);
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

    /// Marks the variable a place names (when it is a variable) as shared:
    /// through `let_place` aliases to the variable behind them (bounded by
    /// the number of aliases, so a malformed cycle cannot loop).
    fn mark_path_local(&mut self, hir: &Hir, e: ExprId) {
        let mut e = e;
        for _ in 0..=self.places.len() {
            let Expr::Path(p) = *hir.expr(e) else {
                return;
            };
            match hir.path(p).res {
                Res::Local(b) => match self.places.get(&b) {
                    Some(&place) => e = place,
                    None => {
                        self.mark(b);
                        return;
                    }
                },
                res => {
                    self.mark_global(hir, res);
                    return;
                }
            }
        }
    }

    fn item(&mut self, hir: &Hir, id: ItemId, member: bool) {
        let kind = hir.item(id).kind;
        if member {
            // Class members are declared by the class table; their
            // initializers run with their class's.
            return;
        }
        if matches!(
            kind,
            ItemKind::Fn(_)
                | ItemKind::Global { .. }
                | ItemKind::Const { .. }
                | ItemKind::Module { .. }
                | ItemKind::Class(_)
                | ItemKind::Interface(_)
        ) {
            self.inits.push(id);
        }
        match kind {
            ItemKind::Fn(_) => self.fns.push(id),
            ItemKind::Global { .. } | ItemKind::Const { .. } => self.globals.push(id),
            ItemKind::Module { body: Some(_), .. } if id != hir.root() => {
                self.module_bodies.push(id);
            }
            ItemKind::Class(_) | ItemKind::Interface(_) => self.classes.push(id),
            ItemKind::Impl(_) if self.unsupported_item.is_none() => {
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
            Expr::LetPlace { binder, place, .. } => {
                let _ = self.places.insert(binder, place);
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
                        self.mark_path_local(hir, arg.value);
                    }
                }
            }

            _ => {}
        }
    }
}
