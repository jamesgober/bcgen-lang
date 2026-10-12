//! The class table: every class, interface, and mixin (PHP trait) of the
//! unit, with its parent, interfaces, and effective members, built once
//! before code generation.
//!
//! **Flattening.** A class's *effective own* members are its own members
//! followed by those of the mixins it uses (HIR `MixinUse`, expanded here
//! because HIR leaves it to the consumer): every mixin member not excluded by
//! an `insteadof` rule and not already defined, plus the aliases `as` rules
//! add (a rule with only a visibility changes the imported member). A mixin
//! that uses mixins is flattened first; a mixin cycle is an error. The first
//! definition of a name wins, as resolve-lang's member tables do. Mixin
//! members are compiled once per using class, so `self::` in them is the
//! using class and their static properties are the using class's own.
//!
//! **LSB names.** Properties keep their plain names, so records, hooks, and
//! hosts see `x`; everything callable gets a name no property can have:
//!
//! | member | public, protected | private (declared in `C`) |
//! |---|---|---|
//! | property | `x` | `C::$x` |
//! | method | `m()` | `C::m()` |
//! | static property accessor | `$x()` | `C::$x()` |
//! | constant accessor | `const X()` | `C::const X()` |
//!
//! plus the synthetic methods `::new` (allocate and initialize), `::test`
//! (the class's `instanceof`), and `::is I` (a marker for interface `I`).
//! Private members are separate per declaring class (PHP's mangling), so a
//! parent's private `$x` and a child's public `$x` are two slots.
//!
//! **Visibility.** Access through a static path is decided here, at compile
//! time. Access through an object is decided at run time by a [`Plan`]: the
//! scope's own private member first (`has_prop`), then a test of the
//! object's class against every class whose visible member of that name the
//! scope may not reach (deepest first), then the public name.
//!
//! Every walk over the class graph is iterative and bounded: inheritance
//! chains by [`MAX_DEPTH`], everything else by the size of the unit, charged
//! to the instruction budget where it produces module data.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use hir_lang::{
    Def, FieldId, Hir, ItemId, ItemKind, MixinAction, NodeRef, ParamKind, Res, Symbol, Ty, TyId,
    Vis,
};
use intern_lang::Lookup;

use crate::error::{ClassProblem, CompileError, Unsupported};

/// A dense class index.
pub(crate) type ClassId = u32;

/// The deepest inheritance chain: bvm-lang's `MAX_INHERITANCE_DEPTH`.
pub(crate) const MAX_DEPTH: u32 = 256;

/// The most property slots one class's instances have (LSB field slots are
/// 16 bits).
pub(crate) const MAX_FIELDS: usize = 1 << 16;

/// What a class-like item is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CKind {
    Class,
    Interface,
    Mixin,
}

/// A method in a member table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MethodM {
    /// The name in this class (an alias's new name).
    pub(crate) name: Symbol,
    /// The `Fn` item (a mixin's, for an imported method).
    pub(crate) item: ItemId,
    pub(crate) vis: Vis,
    /// No receiver parameter.
    pub(crate) is_static: bool,
    /// Has a body (abstract and interface methods do not).
    pub(crate) body: bool,
}

/// An instance property in a member table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PropM {
    pub(crate) name: Symbol,
    pub(crate) field: FieldId,
    pub(crate) vis: Vis,
}

/// A static property (a `Global` member) or constant (a `Const` member).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ItemM {
    pub(crate) name: Symbol,
    pub(crate) item: ItemId,
    pub(crate) vis: Vis,
}

/// One class, interface, or mixin.
#[derive(Clone, Debug)]
pub(crate) struct ClassDecl {
    pub(crate) item: ItemId,
    pub(crate) kind: CKind,
    /// The source name.
    pub(crate) text: String,
    /// The unique LSB struct name.
    pub(crate) lsb: String,
    pub(crate) parent: Option<ClassId>,
    /// 1 for a class without a parent.
    pub(crate) depth: u32,
    pub(crate) is_abstract: bool,
    /// Implemented interfaces (a class) or parent interfaces (an
    /// interface), as written.
    pub(crate) direct: Vec<ClassId>,
    /// Effective own members (own, then mixin-imported), in order.
    pub(crate) methods: Vec<MethodM>,
    pub(crate) props: Vec<PropM>,
    pub(crate) statics: Vec<ItemM>,
    pub(crate) consts: Vec<ItemM>,
    /// Name -> position in the lists above, per namespace.
    index: BTreeMap<(Ns, Symbol), usize>,
}

impl ClassDecl {
    pub(crate) fn method(&self, name: Symbol) -> Option<&MethodM> {
        self.methods.get(*self.index.get(&(Ns::Method, name))?)
    }

    pub(crate) fn prop(&self, name: Symbol) -> Option<&PropM> {
        self.props.get(*self.index.get(&(Ns::Prop, name))?)
    }

    pub(crate) fn static_prop(&self, name: Symbol) -> Option<&ItemM> {
        self.statics.get(*self.index.get(&(Ns::Static, name))?)
    }

    pub(crate) fn constant(&self, name: Symbol) -> Option<&ItemM> {
        self.consts.get(*self.index.get(&(Ns::Const, name))?)
    }

    fn set(&mut self, m: Members) {
        self.methods = m.methods;
        self.props = m.props;
        self.statics = m.statics;
        self.consts = m.consts;
        self.index = m.index;
    }

    fn take(&mut self) -> Members {
        Members {
            methods: core::mem::take(&mut self.methods),
            props: core::mem::take(&mut self.props),
            statics: core::mem::take(&mut self.statics),
            consts: core::mem::take(&mut self.consts),
            index: core::mem::take(&mut self.index),
        }
    }

    pub(crate) fn instantiable(&self) -> bool {
        self.kind == CKind::Class && !self.is_abstract
    }
}

/// One property slot of an instance.
#[derive(Clone, Debug)]
pub(crate) struct FieldSlot {
    /// The LSB field name (mangled when private).
    pub(crate) lsb: String,
    /// The default and the class whose scope evaluates it.
    pub(crate) default: Option<(hir_lang::ExprId, ClassId)>,
}

/// A member namespace.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Ns {
    Prop,
    Method,
    Static,
    Const,
}

/// What a run-time class test decides for an access.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Outcome {
    /// The public name serves it.
    Ok,
    /// A protected member the scope may not reach, declared in this class.
    Protected(ClassId),
    /// Only a private member another class declared.
    Private(ClassId),
}

/// How an access through an object (or a late-bound class) picks its LSB
/// name and checks visibility at run time.
#[derive(Clone, Debug, Default)]
pub(crate) struct Plan {
    /// The scope declares a private member of this name: tried first.
    pub(crate) private: Option<ClassId>,
    /// Classes to test, deepest first, with what each decides; empty when
    /// every class the unit declares serves the public name.
    pub(crate) checks: Vec<(ClassId, Outcome)>,
    /// When set, `checks` covers only the objects that are instances of
    /// this class (the scope): any other object goes through the name's
    /// shared outside check (`ClassTable::outside`), so that a plan's size
    /// follows the scope's own lineage, not every declaration in the unit.
    pub(crate) inside: Option<ClassId>,
    /// The declarations the plan looked at (what building it cost).
    pub(crate) work: u64,
}

/// What a class test decides for an object that is not an instance of the
/// accessing scope (see `Plan::inside`): the same for every scope, except
/// that a protected member's scope test runs at run time.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Check {
    /// The public name serves it.
    Ok,
    /// Denied whatever the scope.
    Deny(Outcome),
    /// A protected member: allowed when the scope descends from `key` (the
    /// declaring class, or a method's prototype root), else denied as
    /// declared in `decl`.
    Protected { key: ClassId, decl: ClassId },
}

/// Declarations of one name up to which a plan lists them all inline;
/// beyond, a scope's plan covers its own lineage only (`Plan::inside`).
const INLINE_DECLS: usize = 4;

/// The unit's classes.
#[derive(Clone, Debug, Default)]
pub(crate) struct ClassTable {
    pub(crate) classes: Vec<ClassDecl>,
    pub(crate) by_item: BTreeMap<ItemId, ClassId>,
    /// Source name -> the classes of that name (namespaces can repeat one).
    names: BTreeMap<Symbol, Vec<ClassId>>,
    /// Member item → the class, interface, or mixin declaring it.
    pub(crate) owner: BTreeMap<ItemId, ClassId>,
    /// Per class: the interfaces it implements directly (its own list and
    /// their parents, transitively), not those its parent implements.
    pub(crate) ifaces: Vec<Vec<ClassId>>,
    /// Per class: the instance layout, the parent's slots first.
    pub(crate) layout: Vec<Vec<FieldSlot>>,
    /// Per namespace and name: the classes declaring a member of it.
    pub(crate) decls: BTreeMap<(Ns, Symbol), Vec<ClassId>>,
    /// The names every class declares public: no access to them needs a
    /// check, whatever the scope.
    public_only: BTreeSet<(Ns, Symbol)>,
    /// Per class: its interval in a preorder of the inheritance forest, so
    /// "descends from" is two comparisons.
    pre: Vec<u32>,
    post: Vec<u32>,
    /// Per class: the classes extending it.
    children: Vec<Vec<ClassId>>,
}

/// The receiver parameter test: a method is an instance method exactly when
/// its first parameter is a `Receiver`.
pub(crate) fn has_receiver(hir: &Hir, def: &hir_lang::FnDef) -> bool {
    hir.list(def.params)
        .first()
        .is_some_and(|&p| hir.param(p).kind == ParamKind::Receiver)
}

impl ClassTable {
    /// Builds the table for `items` (every class and interface item of the
    /// unit, in canonical order). `charge` counts data written to the
    /// module (layouts, interface closures) against the budget.
    pub(crate) fn build<L: Lookup>(
        hir: &Hir,
        names: &L,
        items: &[ItemId],
        charge: &mut dyn FnMut(u64) -> Result<(), CompileError>,
    ) -> Result<ClassTable, CompileError> {
        let mut t = ClassTable::default();
        let mut used: BTreeMap<String, u32> = BTreeMap::new();
        for (i, &item) in items.iter().enumerate() {
            let id = ClassId::try_from(i).unwrap_or(ClassId::MAX);
            let it = *hir.item(item);
            let (kind, is_abstract) = match it.kind {
                ItemKind::Class(c) if c.mixin => (CKind::Mixin, true),
                ItemKind::Class(c) => (CKind::Class, c.is_abstract),
                _ => (CKind::Interface, true),
            };
            let text = it
                .name
                .and_then(|n| names.resolve_with(n.sym, |t| String::from(t)))
                .unwrap_or_default();
            let lsb = unique(&mut used, &text);
            let _ = t.by_item.insert(item, id);
            if let Some(n) = it.name {
                t.names.entry(n.sym).or_default().push(id);
            }
            t.classes.push(ClassDecl {
                item,
                kind,
                text,
                lsb,
                parent: None,
                depth: 1,
                is_abstract,
                direct: Vec::new(),
                methods: Vec::new(),
                props: Vec::new(),
                statics: Vec::new(),
                consts: Vec::new(),
                index: BTreeMap::new(),
            });
        }
        t.link(hir)?;
        t.depths(hir)?;
        t.flatten(hir, charge)?;
        t.interfaces(hir, charge)?;
        t.layouts(hir, names, charge)?;
        t.index();
        Ok(t)
    }

    pub(crate) fn get(&self, c: ClassId) -> Option<&ClassDecl> {
        self.classes.get(c as usize)
    }

    pub(crate) fn len(&self) -> usize {
        self.classes.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.classes.is_empty()
    }

    /// The class a type term names, if it is one of the unit's.
    pub(crate) fn of_ty(&self, hir: &Hir, ty: TyId) -> Result<Option<ClassId>, CompileError> {
        let node = NodeRef::Ty(ty);
        let Ty::Path(p) = *hir.ty(ty) else {
            return Ok(None);
        };
        self.of_res(hir, hir.path(p).res, node)
    }

    /// The class a resolution names, if it is one of the unit's.
    pub(crate) fn of_res(
        &self,
        hir: &Hir,
        res: Res,
        node: NodeRef,
    ) -> Result<Option<ClassId>, CompileError> {
        match res {
            Res::Def(d) if d.unit() == hir.unit() => match d.def() {
                Def::Item(i) => Ok(self.by_item.get(&i).copied()),
                Def::Variant(_) => Ok(None),
            },
            Res::Def(_) => Err(CompileError::Unsupported {
                feature: Unsupported::ForeignUnit,
                node,
                span: hir.origin(node).span,
            }),
            Res::Unresolved | Res::Err => Err(CompileError::Unresolved {
                node,
                span: hir.origin(node).span,
            }),
            _ => Ok(None),
        }
    }

    fn problem(hir: &Hir, problem: ClassProblem, node: NodeRef) -> CompileError {
        CompileError::Class {
            problem,
            node,
            span: hir.origin(node).span,
        }
    }

    /// Parents and interface lists.
    fn link(&mut self, hir: &Hir) -> Result<(), CompileError> {
        for c in 0..self.classes.len() {
            let Some(item) = self.classes.get(c).map(|d| d.item) else {
                continue;
            };
            let node = NodeRef::Item(item);
            let (bases, direct) = match hir.item(item).kind {
                ItemKind::Class(def) => (hir.list(def.bases), hir.list(def.interfaces)),
                ItemKind::Interface(def) => (&[][..], hir.list(def.supers)),
                _ => continue,
            };
            if bases.len() > 1 {
                return Err(CompileError::Unsupported {
                    feature: Unsupported::MultipleInheritance,
                    node,
                    span: hir.origin(node).span,
                });
            }
            let kind = self.classes.get(c).map(|d| d.kind);
            let mut parent = None;
            if let Some(&b) = bases.first() {
                let Some(p) = self.of_ty(hir, b)? else {
                    return Err(Self::problem(hir, ClassProblem::NotAClass, NodeRef::Ty(b)));
                };
                let pk = self.get(p).map(|d| d.kind);
                if pk != Some(CKind::Class) || kind != Some(CKind::Class) {
                    return Err(Self::problem(hir, ClassProblem::NotAClass, NodeRef::Ty(b)));
                }
                parent = Some(p);
            }
            let mut ifs = Vec::with_capacity(direct.len());
            for &ty in direct {
                match self.of_ty(hir, ty)? {
                    Some(i) if self.get(i).map(|d| d.kind) == Some(CKind::Interface) => {
                        ifs.push(i);
                    }
                    _ => {
                        return Err(Self::problem(
                            hir,
                            ClassProblem::NotAnInterface,
                            NodeRef::Ty(ty),
                        ));
                    }
                }
            }
            if let Some(d) = self.classes.get_mut(c) {
                d.parent = parent;
                d.direct = ifs;
            }
        }
        Ok(())
    }

    /// Depths along parent chains, iteratively; a cycle or a chain deeper
    /// than [`MAX_DEPTH`] is an error.
    fn depths(&mut self, hir: &Hir) -> Result<(), CompileError> {
        let n = self.classes.len();
        // 0 unvisited, 1 on the current chain, 2 done.
        let mut state = alloc::vec![0u8; n];
        let mut chain: Vec<ClassId> = Vec::new();
        for start in 0..n {
            if state.get(start).copied() != Some(0) {
                continue;
            }
            chain.clear();
            let mut cur = Some(ClassId::try_from(start).unwrap_or(ClassId::MAX));
            // Walk up to a done class (or the top), marking the chain.
            while let Some(c) = cur {
                match state.get(c as usize).copied() {
                    Some(0) => {
                        if let Some(s) = state.get_mut(c as usize) {
                            *s = 1;
                        }
                        chain.push(c);
                        cur = self.get(c).and_then(|d| d.parent);
                    }
                    Some(1) => {
                        let item = self.get(c).map_or(hir.root(), |d| d.item);
                        return Err(Self::problem(hir, ClassProblem::Cycle, NodeRef::Item(item)));
                    }
                    _ => break,
                }
            }
            let mut depth = cur.and_then(|c| self.get(c)).map_or(0, |d| d.depth);
            for &c in chain.iter().rev() {
                depth += 1;
                if depth > MAX_DEPTH {
                    let item = self.get(c).map_or(hir.root(), |d| d.item);
                    return Err(Self::problem(
                        hir,
                        ClassProblem::TooDeep { limit: MAX_DEPTH },
                        NodeRef::Item(item),
                    ));
                }
                if let Some(d) = self.classes.get_mut(c as usize) {
                    d.depth = depth;
                }
                if let Some(s) = state.get_mut(c as usize) {
                    *s = 2;
                }
            }
        }
        Ok(())
    }

    /// Own members, then mixins flattened in dependency order.
    fn flatten(
        &mut self,
        hir: &Hir,
        charge: &mut dyn FnMut(u64) -> Result<(), CompileError>,
    ) -> Result<(), CompileError> {
        let n = self.classes.len();
        let mut uses: Vec<Vec<ItemId>> = alloc::vec![Vec::new(); n];
        for c in 0..n {
            let Some(item) = self.classes.get(c).map(|d| d.item) else {
                continue;
            };
            let (members, fields) = match hir.item(item).kind {
                ItemKind::Class(def) => (hir.list(def.items), hir.list(def.fields)),
                ItemKind::Interface(def) => (hir.list(def.items), &[][..]),
                _ => continue,
            };
            let mut d = Members::default();
            for &m in members {
                let it = *hir.item(m);
                let _ = self
                    .owner
                    .insert(m, ClassId::try_from(c).unwrap_or(ClassId::MAX));
                let Some(name) = it.name.map(|n| n.sym) else {
                    if let ItemKind::MixinUse(_) = it.kind {
                        if let Some(u) = uses.get_mut(c) {
                            u.push(m);
                        }
                    }
                    continue;
                };
                match it.kind {
                    ItemKind::Fn(def) => d.method(MethodM {
                        name,
                        item: m,
                        vis: it.vis,
                        is_static: !has_receiver(hir, &def),
                        body: def.body.is_some(),
                    }),
                    ItemKind::Global { .. } => d.statics_add(ItemM {
                        name,
                        item: m,
                        vis: it.vis,
                    }),
                    ItemKind::Const { .. } => d.consts_add(ItemM {
                        name,
                        item: m,
                        vis: it.vis,
                    }),
                    _ => {}
                }
            }
            for &f in fields {
                let fd = hir.field(f);
                if let Some(name) = fd.name {
                    d.prop(PropM {
                        name: name.sym,
                        field: f,
                        vis: fd.vis,
                    });
                }
            }
            if let Some(decl) = self.classes.get_mut(c) {
                decl.set(d);
            }
        }
        // Dependency order over mixin uses: a container is expanded after
        // every mixin it uses (iterative DFS; a cycle is an error).
        let order = self.mixin_order(hir, &uses)?;
        for c in order {
            let Some(list) = uses.get(c as usize) else {
                continue;
            };
            for &u in list {
                self.apply_use(hir, c, u, charge)?;
            }
        }
        Ok(())
    }

    /// The mixins a use item names.
    fn used_mixins(&self, hir: &Hir, u: ItemId) -> Result<Vec<ClassId>, CompileError> {
        let ItemKind::MixinUse(def) = hir.item(u).kind else {
            return Ok(Vec::new());
        };
        let mut out = Vec::new();
        for &ty in hir.list(def.mixins) {
            match self.of_ty(hir, ty)? {
                Some(m) if self.get(m).map(|d| d.kind) == Some(CKind::Mixin) => out.push(m),
                _ => return Err(Self::problem(hir, ClassProblem::NotAMixin, NodeRef::Ty(ty))),
            }
        }
        Ok(out)
    }

    fn mixin_order(&self, hir: &Hir, uses: &[Vec<ItemId>]) -> Result<Vec<ClassId>, CompileError> {
        let n = self.classes.len();
        let mut state = alloc::vec![0u8; n];
        let mut order: Vec<ClassId> = Vec::with_capacity(n);
        // (class, its mixins, next index)
        let mut stack: Vec<(ClassId, Vec<ClassId>, usize)> = Vec::new();
        for start in 0..n {
            let start = ClassId::try_from(start).unwrap_or(ClassId::MAX);
            if state.get(start as usize).copied() != Some(0) {
                continue;
            }
            let deps = self.deps(hir, uses, start)?;
            if let Some(s) = state.get_mut(start as usize) {
                *s = 1;
            }
            stack.push((start, deps, 0));
            while let Some(top) = stack.last_mut() {
                let (c, next) = (top.0, top.2);
                match top.1.get(next).copied() {
                    Some(m) => {
                        top.2 += 1;
                        match state.get(m as usize).copied() {
                            Some(0) => {
                                let deps = self.deps(hir, uses, m)?;
                                if let Some(s) = state.get_mut(m as usize) {
                                    *s = 1;
                                }
                                stack.push((m, deps, 0));
                            }
                            Some(1) => {
                                let item = self.get(m).map_or(hir.root(), |d| d.item);
                                return Err(Self::problem(
                                    hir,
                                    ClassProblem::Cycle,
                                    NodeRef::Item(item),
                                ));
                            }
                            _ => {}
                        }
                    }
                    None => {
                        if let Some(s) = state.get_mut(c as usize) {
                            *s = 2;
                        }
                        order.push(c);
                        let _ = stack.pop();
                    }
                }
            }
        }
        Ok(order)
    }

    fn deps(
        &self,
        hir: &Hir,
        uses: &[Vec<ItemId>],
        c: ClassId,
    ) -> Result<Vec<ClassId>, CompileError> {
        let mut out = Vec::new();
        for &u in uses.get(c as usize).map_or(&[][..], Vec::as_slice) {
            out.extend(self.used_mixins(hir, u)?);
        }
        Ok(out)
    }

    /// Imports the members of the mixins `u` uses into class `c`, applying
    /// its rules. Every imported member is charged to the budget (a chain of
    /// mixins each using the last copies members cumulatively).
    fn apply_use(
        &mut self,
        hir: &Hir,
        c: ClassId,
        u: ItemId,
        charge: &mut dyn FnMut(u64) -> Result<(), CompileError>,
    ) -> Result<(), CompileError> {
        let ItemKind::MixinUse(def) = hir.item(u).kind else {
            return Ok(());
        };
        let mixins = self.used_mixins(hir, u)?;
        let rules = hir.list(def.rules);
        // `T::m insteadof U, V`: U's and V's `m` are not imported.
        let mut excluded: BTreeSet<(ClassId, Symbol)> = BTreeSet::new();
        for r in rules {
            if let MixinAction::Insteadof(others) = r.action {
                for &o in hir.list(others) {
                    if let Some(oc) = self.of_ty(hir, o)? {
                        let _ = excluded.insert((oc, r.method.sym));
                    }
                }
            }
        }
        let mut methods: Vec<MethodM> = Vec::new();
        // The mixin each imported method comes from: PHP keys `as` rules on
        // the providing trait (`fn->common.scope`), not on the method item
        // (two mixins can carry the same item, one importing it from the
        // other).
        let mut origin: Vec<ClassId> = Vec::new();
        let mut props: Vec<PropM> = Vec::new();
        let mut statics: Vec<ItemM> = Vec::new();
        let mut consts: Vec<ItemM> = Vec::new();
        for &m in &mixins {
            let Some(d) = self.get(m) else { continue };
            charge((d.methods.len() + d.props.len() + d.statics.len() + d.consts.len()) as u64)?;
            for meth in &d.methods {
                if !excluded.contains(&(m, meth.name)) {
                    methods.push(*meth);
                    origin.push(m);
                }
            }
            props.extend_from_slice(&d.props);
            statics.extend_from_slice(&d.statics);
            consts.extend_from_slice(&d.consts);
        }
        // Imported methods by name, for visibility-only rules; and the first
        // used mixin that has each name, for unqualified aliases (PHP
        // resolves those to the one trait having the method).
        let mut by_name: BTreeMap<Symbol, Vec<usize>> = BTreeMap::new();
        for (i, m) in methods.iter().enumerate() {
            by_name.entry(m.name).or_default().push(i);
        }
        let mut provider: BTreeMap<Symbol, ClassId> = BTreeMap::new();
        for &m in &mixins {
            if let Some(d) = self.get(m) {
                for meth in &d.methods {
                    let _ = provider.entry(meth.name).or_insert(m);
                }
            }
        }
        // `[T::]m as [vis] [alias]`.
        for r in rules {
            let MixinAction::Alias { name, vis } = r.action else {
                continue;
            };
            let from = match r.from {
                Some(ty) => self.of_ty(hir, ty)?,
                None => None,
            };
            // The mixin's own method, as declared (an alias copies the
            // trait's method, not a copy another rule already changed).
            let Some(from) = from.or_else(|| provider.get(&r.method.sym).copied()) else {
                continue;
            };
            let Some(found) = self.get(from).and_then(|d| d.method(r.method.sym)).copied() else {
                continue;
            };
            match name {
                Some(alias) => {
                    methods.push(MethodM {
                        name: alias.sym,
                        vis: vis.unwrap_or(found.vis),
                        ..found
                    });
                    origin.push(from);
                }
                None => {
                    if let (Some(v), Some(list)) = (vis, by_name.get(&r.method.sym)) {
                        for &i in list {
                            if origin.get(i) == Some(&from) {
                                if let Some(meth) = methods.get_mut(i) {
                                    meth.vis = v;
                                }
                            }
                        }
                    }
                }
            }
        }
        let Some(decl) = self.classes.get_mut(c as usize) else {
            return Ok(());
        };
        let mut d = decl.take();
        for m in methods {
            d.method(m);
        }
        for p in props {
            d.prop(p);
        }
        for s in statics {
            d.statics_add(s);
        }
        for k in consts {
            d.consts_add(k);
        }
        decl.set(d);
        Ok(())
    }

    /// Each class's directly implemented interfaces, closed over interface
    /// parents (iterative, with a visited set, so cycles end).
    fn interfaces(
        &mut self,
        hir: &Hir,
        charge: &mut dyn FnMut(u64) -> Result<(), CompileError>,
    ) -> Result<(), CompileError> {
        let n = self.classes.len();
        let mut out: Vec<Vec<ClassId>> = alloc::vec![Vec::new(); n];
        let mut seen: BTreeSet<ClassId> = BTreeSet::new();
        let mut stack: Vec<ClassId> = Vec::new();
        for (c, slot) in out.iter_mut().enumerate() {
            let Some(d) = self.classes.get(c) else {
                continue;
            };
            if d.kind == CKind::Mixin {
                continue;
            }
            seen.clear();
            stack.clear();
            stack.extend(d.direct.iter().rev());
            if d.kind == CKind::Interface {
                // An interface implements itself (its token's `::test`).
                stack.push(ClassId::try_from(c).unwrap_or(ClassId::MAX));
            }
            while let Some(i) = stack.pop() {
                if !seen.insert(i) {
                    continue;
                }
                slot.push(i);
                if let Some(id) = self.get(i) {
                    stack.extend(id.direct.iter().rev());
                }
            }
            charge(slot.len() as u64)?;
        }
        let _ = hir;
        self.ifaces = out;
        Ok(())
    }

    /// Instance layouts in parent-first order (parents have smaller depth).
    fn layouts<L: Lookup>(
        &mut self,
        hir: &Hir,
        names: &L,
        charge: &mut dyn FnMut(u64) -> Result<(), CompileError>,
    ) -> Result<(), CompileError> {
        let n = self.classes.len();
        let mut order: Vec<ClassId> = (0..n)
            .map(|c| ClassId::try_from(c).unwrap_or(ClassId::MAX))
            .collect();
        order.sort_by_key(|&c| (self.get(c).map_or(0, |d| d.depth), c));
        let mut layout: Vec<Vec<FieldSlot>> = alloc::vec![Vec::new(); n];
        for c in order {
            let Some(d) = self.get(c) else { continue };
            if d.kind != CKind::Class {
                continue;
            }
            let mut slots: Vec<FieldSlot> = match d.parent {
                Some(p) => layout.get(p as usize).cloned().unwrap_or_default(),
                None => Vec::new(),
            };
            let mut at: BTreeMap<String, usize> = slots
                .iter()
                .enumerate()
                .map(|(i, s)| (s.lsb.clone(), i))
                .collect();
            for p in &d.props {
                let text = names
                    .resolve_with(p.name, |t| String::from(t))
                    .unwrap_or_default();
                let lsb = if p.vis == Vis::Private {
                    let mut s = d.lsb.clone();
                    s.push_str("::$");
                    s.push_str(&text);
                    s
                } else {
                    text
                };
                let default = hir.field(p.field).default.map(|e| (e, c));
                match at.get(&lsb).and_then(|&i| slots.get_mut(i)) {
                    // A redeclaration takes over the slot (and its default).
                    Some(s) => s.default = default,
                    None => {
                        let _ = at.insert(lsb.clone(), slots.len());
                        slots.push(FieldSlot { lsb, default });
                    }
                }
            }
            if slots.len() > MAX_FIELDS {
                return Err(Self::problem(
                    hir,
                    ClassProblem::TooManyFields {
                        limit: MAX_FIELDS as u32,
                    },
                    NodeRef::Item(d.item),
                ));
            }
            charge(slots.len() as u64)?;
            if let Some(l) = layout.get_mut(c as usize) {
                *l = slots;
            }
        }
        self.layout = layout;
        Ok(())
    }

    /// Who declares what, and the deepest-first order.
    fn index(&mut self) {
        for (c, d) in self.classes.iter().enumerate() {
            let c = ClassId::try_from(c).unwrap_or(ClassId::MAX);
            let names: Vec<(Ns, Symbol)> = d
                .props
                .iter()
                .map(|p| (Ns::Prop, p.name))
                .chain(
                    d.methods
                        .iter()
                        .filter(|m| m.body)
                        .map(|m| (Ns::Method, m.name)),
                )
                .chain(d.statics.iter().map(|s| (Ns::Static, s.name)))
                .chain(d.consts.iter().map(|k| (Ns::Const, k.name)))
                .collect();
            for key in names {
                let list = self.decls.entry(key).or_default();
                if list.last() != Some(&c) {
                    list.push(c);
                }
            }
        }
        for (&(ns, name), list) in &self.decls {
            let public = list.iter().all(|&c| {
                self.get(c).is_none_or(|d| {
                    d.kind != CKind::Class || d.vis_of(ns, name) == Some(Vis::Public)
                })
            });
            if public {
                let _ = self.public_only.insert((ns, name));
            }
        }
        self.intervals();
        // Preorder, so that a class's descendants among them are a range.
        let pre = &self.pre;
        for list in self.decls.values_mut() {
            list.sort_by_key(|&c| (pre.get(c as usize).copied().unwrap_or(u32::MAX), c));
        }
    }

    /// Preorder intervals over the inheritance forest (iterative DFS).
    fn intervals(&mut self) {
        let n = self.classes.len();
        let mut children: Vec<Vec<ClassId>> = alloc::vec![Vec::new(); n];
        let mut roots: Vec<ClassId> = Vec::new();
        for (c, d) in self.classes.iter().enumerate() {
            let c = ClassId::try_from(c).unwrap_or(ClassId::MAX);
            match d.parent.and_then(|p| children.get_mut(p as usize)) {
                Some(list) => list.push(c),
                None => roots.push(c),
            }
        }
        let mut pre = alloc::vec![0u32; n];
        let mut post = alloc::vec![0u32; n];
        let mut clock = 0u32;
        let mut stack: Vec<(ClassId, usize)> = Vec::new();
        for r in roots {
            stack.push((r, 0));
            if let Some(x) = pre.get_mut(r as usize) {
                *x = clock;
            }
            clock += 1;
            while let Some(top) = stack.last_mut() {
                let (c, i) = (top.0, top.1);
                match children.get(c as usize).and_then(|l| l.get(i)).copied() {
                    Some(k) => {
                        top.1 += 1;
                        if let Some(x) = pre.get_mut(k as usize) {
                            *x = clock;
                        }
                        clock += 1;
                        stack.push((k, 0));
                    }
                    None => {
                        if let Some(x) = post.get_mut(c as usize) {
                            *x = clock;
                        }
                        let _ = stack.pop();
                    }
                }
            }
        }
        self.pre = pre;
        self.post = post;
        self.children = children;
    }

    // ------------------------------------------------------------ queries

    /// The classes named `name`.
    pub(crate) fn by_name(&self, name: Symbol) -> &[ClassId] {
        self.names.get(&name).map_or(&[], Vec::as_slice)
    }

    /// `c` and its ancestors, nearest first.
    pub(crate) fn chain(&self, c: ClassId) -> impl Iterator<Item = ClassId> + '_ {
        let mut cur = Some(c);
        let mut steps = 0u32;
        core::iter::from_fn(move || {
            let c = cur?;
            steps += 1;
            if steps > MAX_DEPTH + 1 {
                return None;
            }
            cur = self.get(c).and_then(|d| d.parent);
            Some(c)
        })
    }

    /// Whether `a` is `b` or descends from it.
    pub(crate) fn descends(&self, a: ClassId, b: ClassId) -> bool {
        match (
            self.pre.get(a as usize),
            self.pre.get(b as usize),
            self.post.get(b as usize),
        ) {
            (Some(&pa), Some(&pb), Some(&qb)) => pb <= pa && pa < qb,
            _ => false,
        }
    }

    /// PHP's "related" test for protected members: one class is the other or
    /// an ancestor of it.
    pub(crate) fn related(&self, a: Option<ClassId>, b: ClassId) -> bool {
        a.is_some_and(|a| self.descends(a, b) || self.descends(b, a))
    }

    /// The method `name` as `c` sees it: (the class whose table holds it,
    /// the member), nearest first.
    pub(crate) fn find_method(&self, c: ClassId, name: Symbol) -> Option<(ClassId, MethodM)> {
        self.chain(c)
            .find_map(|x| self.get(x).and_then(|d| d.method(name)).map(|m| (x, *m)))
    }

    /// The static property `name` as `c` sees it.
    pub(crate) fn find_static(&self, c: ClassId, name: Symbol) -> Option<(ClassId, ItemM)> {
        self.chain(c).find_map(|x| {
            self.get(x)
                .and_then(|d| d.static_prop(name))
                .map(|m| (x, *m))
        })
    }

    /// The constant `name` as `c` sees it: the class chain, then the
    /// interfaces of each class on it.
    pub(crate) fn find_const(&self, c: ClassId, name: Symbol) -> Option<(ClassId, ItemM)> {
        if let Some(found) = self
            .chain(c)
            .find_map(|x| self.get(x).and_then(|d| d.constant(name)).map(|m| (x, *m)))
        {
            return Some(found);
        }
        self.chain(c).find_map(|x| {
            self.ifaces
                .get(x as usize)?
                .iter()
                .find_map(|&i| self.get(i).and_then(|d| d.constant(name)).map(|m| (i, *m)))
        })
    }

    /// The nearest non-private declaration of `name` in namespace `ns` on
    /// `c`'s chain: its visibility, the class a protected check relates the
    /// scope to (for a method the topmost class of the overriding chain,
    /// PHP's prototype root; for anything else the declaring class, PHP's
    /// `property_info->ce`), and the declaring class.
    fn visible(&self, c: ClassId, ns: Ns, name: Symbol) -> Option<(Vis, ClassId, ClassId)> {
        let mut found: Option<(Vis, ClassId, ClassId)> = None;
        for x in self.chain(c) {
            let Some(vis) = self.get(x).and_then(|d| d.vis_of(ns, name)) else {
                continue;
            };
            if vis == Vis::Private {
                continue;
            }
            match found {
                None => found = Some((vis, x, x)),
                Some((v, _, decl)) if ns == Ns::Method => found = Some((v, x, decl)),
                Some(_) => break,
            }
        }
        found
    }

    /// The nearest private declaration of `name` in `ns` on `c`'s chain by a
    /// class other than `scope`.
    fn private_elsewhere(
        &self,
        c: ClassId,
        ns: Ns,
        name: Symbol,
        scope: Option<ClassId>,
    ) -> Option<ClassId> {
        self.chain(c).find(|&x| {
            Some(x) != scope && self.get(x).and_then(|d| d.vis_of(ns, name)) == Some(Vis::Private)
        })
    }

    /// Whether `scope` declares a private member `name` in `ns`.
    pub(crate) fn scope_private(&self, scope: Option<ClassId>, ns: Ns, name: Symbol) -> bool {
        scope
            .and_then(|s| self.get(s))
            .and_then(|d| d.vis_of(ns, name))
            == Some(Vis::Private)
    }

    /// What an access to `name` in `ns` from `scope` does with an object of
    /// class `c` that is not an instance of the scope's private member.
    pub(crate) fn outcome(
        &self,
        c: ClassId,
        ns: Ns,
        name: Symbol,
        scope: Option<ClassId>,
    ) -> Outcome {
        match self.visible(c, ns, name) {
            Some((Vis::Protected, key, decl)) => {
                if self.related(scope, key) {
                    Outcome::Ok
                } else {
                    Outcome::Protected(decl)
                }
            }
            Some(_) => Outcome::Ok,
            None => match self.private_elsewhere(c, ns, name, scope) {
                Some(p) => Outcome::Private(p),
                None => Outcome::Ok,
            },
        }
    }

    /// The run-time plan for accessing `name` in `ns` from `scope`.
    pub(crate) fn plan(&self, scope: Option<ClassId>, ns: Ns, name: Symbol) -> Plan {
        let narrow = scope.filter(|&s| {
            self.get(s).is_some_and(|d| d.kind == CKind::Class)
                && self
                    .decls
                    .get(&(ns, name))
                    .is_some_and(|l| l.len() > INLINE_DECLS)
        });
        match narrow {
            Some(s) => self.plan_inside(s, ns, name),
            None => self.plan_full(scope, ns, name),
        }
    }

    /// A plan listing every declaration of the name.
    pub(crate) fn plan_full(&self, scope: Option<ClassId>, ns: Ns, name: Symbol) -> Plan {
        let private = self
            .scope_private(scope, ns, name)
            .then_some(scope)
            .flatten();
        let decls = match self.decls.get(&(ns, name)) {
            Some(decls) if !self.public_only(ns, name) => decls,
            _ => {
                return Plan {
                    private,
                    checks: Vec::new(),
                    inside: None,
                    work: 1,
                };
            }
        };
        // Every class declaring the name decides for itself and its
        // descendants that do not redeclare it; deepest first, the first
        // match is the object's nearest declaring ancestor.
        let checks: Vec<(ClassId, Outcome)> = decls
            .iter()
            .filter(|&&c| self.get(c).is_some_and(|d| d.kind == CKind::Class))
            .map(|&c| (c, self.outcome(c, ns, name, scope)))
            .collect();
        let checks = self.finish_checks(checks, ns, name, |_| true);
        Plan {
            private,
            checks,
            inside: None,
            work: decls.len() as u64,
        }
    }

    /// A plan for the instances of `scope` only: an instance's nearest
    /// declaring ancestor is on the scope's chain or below the scope, so
    /// only those declarations are listed.
    fn plan_inside(&self, scope: ClassId, ns: Ns, name: Symbol) -> Plan {
        let s = Some(scope);
        let private = self.scope_private(s, ns, name).then_some(scope);
        if self.public_only(ns, name) {
            return Plan {
                private,
                checks: Vec::new(),
                inside: None,
                work: 1,
            };
        }
        let decls = self.decls.get(&(ns, name)).map_or(&[][..], Vec::as_slice);
        let is_class = |c: ClassId| self.get(c).is_some_and(|d| d.kind == CKind::Class);
        let mut lineage: Vec<ClassId> = self
            .chain(scope)
            .filter(|&x| is_class(x) && self.get(x).is_some_and(|d| d.vis_of(ns, name).is_some()))
            .collect();
        if let (Some(&lo), Some(&hi)) =
            (self.pre.get(scope as usize), self.post.get(scope as usize))
        {
            let pre_of = |c: ClassId| self.pre.get(c as usize).copied().unwrap_or(u32::MAX);
            let from = decls.partition_point(|&c| pre_of(c) <= lo);
            lineage.extend(
                decls
                    .get(from..)
                    .unwrap_or(&[])
                    .iter()
                    .take_while(|&&c| pre_of(c) < hi)
                    .filter(|&&c| is_class(c)),
            );
        }
        let work = lineage.len() as u64 + 1;
        let checks: Vec<(ClassId, Outcome)> = lineage
            .iter()
            .map(|&c| (c, self.outcome(c, ns, name, s)))
            .collect();
        let checks = self.finish_checks(checks, ns, name, |k| self.related(s, k));
        Plan {
            private,
            checks,
            inside: Some(scope),
            work,
        }
    }

    /// Adds the private-property pass-throughs (children of a class whose
    /// outcome is private, among those `keep` accepts), orders the checks
    /// deepest first, and drops the trailing passes.
    fn finish_checks(
        &self,
        mut checks: Vec<(ClassId, Outcome)>,
        ns: Ns,
        name: Symbol,
        keep: impl Fn(ClassId) -> bool,
    ) -> Vec<(ClassId, Outcome)> {
        if ns == Ns::Prop {
            // PHP reports a private property only on an instance of the
            // declaring class itself; on a subclass's instance it is an
            // undefined (dynamic) property (`zend_get_property_offset`).
            let extra: Vec<(ClassId, Outcome)> = checks
                .iter()
                .filter(|(_, o)| matches!(o, Outcome::Private(_)))
                .flat_map(|&(c, _)| self.children.get(c as usize).into_iter().flatten())
                .filter(|&&k| keep(k) && self.get(k).is_some_and(|d| d.vis_of(ns, name).is_none()))
                .map(|&k| (k, Outcome::Ok))
                .collect();
            checks.extend(extra);
        }
        if checks.iter().all(|(_, o)| *o == Outcome::Ok) {
            checks.clear();
        } else {
            checks
                .sort_by_key(|&(c, _)| (core::cmp::Reverse(self.get(c).map_or(0, |d| d.depth)), c));
            // Trailing passes decide nothing the fall-through would not.
            while checks.last().is_some_and(|(_, o)| *o == Outcome::Ok) {
                let _ = checks.pop();
            }
        }
        checks
    }

    /// The shared check of `name` in `ns` for an object that is not an
    /// instance of the accessing scope: every declaration, deepest first.
    /// Off the scope's lineage an outcome no longer depends on the scope,
    /// except for a protected member, whose `key` the scope must descend
    /// from (the key cannot be below a scope the object is not an
    /// instance of).
    pub(crate) fn outside(&self, ns: Ns, name: Symbol) -> Vec<(ClassId, Check)> {
        let Some(decls) = self.decls.get(&(ns, name)) else {
            return Vec::new();
        };
        let mut checks: Vec<(ClassId, Check)> = decls
            .iter()
            .filter(|&&c| self.get(c).is_some_and(|d| d.kind == CKind::Class))
            .map(|&c| {
                let check = match self.visible(c, ns, name) {
                    Some((Vis::Protected, key, decl)) => Check::Protected { key, decl },
                    Some(_) => Check::Ok,
                    None => match self.private_elsewhere(c, ns, name, None) {
                        Some(p) => Check::Deny(Outcome::Private(p)),
                        None => Check::Ok,
                    },
                };
                (c, check)
            })
            .collect();
        if ns == Ns::Prop {
            let extra: Vec<(ClassId, Check)> = checks
                .iter()
                .filter(|(_, o)| matches!(o, Check::Deny(Outcome::Private(_))))
                .flat_map(|&(c, _)| self.children.get(c as usize).into_iter().flatten())
                .filter(|&&k| self.get(k).is_some_and(|d| d.vis_of(ns, name).is_none()))
                .map(|&k| (k, Check::Ok))
                .collect();
            checks.extend(extra);
        }
        checks.sort_by_key(|&(c, _)| (core::cmp::Reverse(self.get(c).map_or(0, |d| d.depth)), c));
        while checks.last().is_some_and(|(_, o)| *o == Check::Ok) {
            let _ = checks.pop();
        }
        checks
    }

    /// Whether every class declaring `name` in `ns` declares it public (or
    /// none does), so that no access to it needs a run-time check: a plan
    /// for it is O(1) instead of a walk over its declarations.
    pub(crate) fn public_only(&self, ns: Ns, name: Symbol) -> bool {
        self.public_only.contains(&(ns, name)) || !self.decls.contains_key(&(ns, name))
    }

    /// Whether `name` in `ns` may be reached from `scope` when the member
    /// is statically known: (declaring class, visibility, the class whose
    /// table holds it).
    pub(crate) fn static_access(
        &self,
        scope: Option<ClassId>,
        holder: ClassId,
        ns: Ns,
        name: Symbol,
        vis: Vis,
    ) -> Outcome {
        match vis {
            Vis::Private if scope != Some(holder) => Outcome::Private(holder),
            Vis::Protected => {
                let root = self.visible(holder, ns, name).map_or(holder, |(_, r, _)| r);
                if self.related(scope, root) {
                    Outcome::Ok
                } else {
                    Outcome::Protected(holder)
                }
            }
            _ => Outcome::Ok,
        }
    }
}

impl ClassDecl {
    /// The visibility of this class's own `name` in `ns`, if it declares one
    /// (methods only with a body: abstract declarations have no slot).
    pub(crate) fn vis_of(&self, ns: Ns, name: Symbol) -> Option<Vis> {
        match ns {
            Ns::Prop => self.prop(name).map(|p| p.vis),
            Ns::Method => self.method(name).filter(|m| m.body).map(|m| m.vis),
            Ns::Static => self.static_prop(name).map(|m| m.vis),
            Ns::Const => self.constant(name).map(|m| m.vis),
        }
    }
}

/// A member table under construction: the first definition of a name wins
/// (indexed, so a class of any size builds in `O(n log n)`).
#[derive(Default)]
struct Members {
    methods: Vec<MethodM>,
    props: Vec<PropM>,
    statics: Vec<ItemM>,
    consts: Vec<ItemM>,
    index: BTreeMap<(Ns, Symbol), usize>,
}

impl Members {
    /// Records `name` in `ns` at position `at`; false if it is taken.
    fn claim(&mut self, ns: Ns, name: Symbol, at: usize) -> bool {
        match self.index.entry((ns, name)) {
            alloc::collections::btree_map::Entry::Occupied(_) => false,
            alloc::collections::btree_map::Entry::Vacant(v) => {
                let _ = v.insert(at);
                true
            }
        }
    }

    fn method(&mut self, m: MethodM) {
        if self.claim(Ns::Method, m.name, self.methods.len()) {
            self.methods.push(m);
        }
    }

    fn prop(&mut self, p: PropM) {
        if self.claim(Ns::Prop, p.name, self.props.len()) {
            self.props.push(p);
        }
    }

    fn statics_add(&mut self, s: ItemM) {
        if self.claim(Ns::Static, s.name, self.statics.len()) {
            self.statics.push(s);
        }
    }

    fn consts_add(&mut self, k: ItemM) {
        if self.claim(Ns::Const, k.name, self.consts.len()) {
            self.consts.push(k);
        }
    }
}

/// A unique LSB name for a class (`Name`, then `Name#2`, ...).
fn unique(used: &mut BTreeMap<String, u32>, text: &str) -> String {
    let base = if text.is_empty() { "<class>" } else { text };
    let n = used.entry(String::from(base)).or_insert(0);
    *n += 1;
    if *n == 1 {
        String::from(base)
    } else {
        alloc::format!("{base}#{n}")
    }
}

/// The LSB name of a member: see the module documentation.
pub(crate) fn lsb_name(ns: Ns, text: &str, private_in: Option<&str>) -> String {
    let mut s = String::with_capacity(text.len() + 16);
    if let Some(c) = private_in {
        s.push_str(c);
        s.push_str("::");
    }
    match ns {
        Ns::Prop => {
            if private_in.is_some() {
                s.push('$');
            }
            s.push_str(text);
        }
        Ns::Method => {
            s.push_str(text);
            s.push_str("()");
        }
        Ns::Static => {
            s.push('$');
            s.push_str(text);
            s.push_str("()");
        }
        Ns::Const => {
            s.push_str("const ");
            s.push_str(text);
            s.push_str("()");
        }
    }
    s
}

#[cfg(test)]
mod tests {
    use super::{Ns, lsb_name, unique};
    use alloc::collections::BTreeMap;

    #[test]
    fn member_names_never_collide_across_namespaces() {
        let names = [
            lsb_name(Ns::Prop, "x", None),
            lsb_name(Ns::Prop, "x", Some("C")),
            lsb_name(Ns::Method, "x", None),
            lsb_name(Ns::Method, "x", Some("C")),
            lsb_name(Ns::Static, "x", None),
            lsb_name(Ns::Static, "x", Some("C")),
            lsb_name(Ns::Const, "x", None),
            lsb_name(Ns::Const, "x", Some("C")),
        ];
        assert_eq!(names[0], "x");
        assert_eq!(names[1], "C::$x");
        assert_eq!(names[2], "x()");
        assert_eq!(names[3], "C::x()");
        assert_eq!(names[4], "$x()");
        assert_eq!(names[6], "const x()");
        for (i, a) in names.iter().enumerate() {
            for b in names.iter().skip(i + 1) {
                assert_ne!(a, b);
            }
        }
    }

    #[test]
    fn class_names_are_made_unique() {
        let mut used = BTreeMap::new();
        assert_eq!(unique(&mut used, "A"), "A");
        assert_eq!(unique(&mut used, "A"), "A#2");
        assert_eq!(unique(&mut used, ""), "<class>");
    }
}
