//! The result of compiling a unit.

use alloc::vec::Vec;

use alloc::string::String;

use bytecode_lang::{FuncId, GlobalId, Module, TypeId};
use hir_lang::{ItemId, NodeRef};

/// A compiled unit: the LSB module, its entry points, and the map from every
/// instruction back to the HIR node it was compiled from.
///
/// # Examples
///
/// ```
/// use hir_lang::{Builder, Name};
/// use intern_lang::Interner;
///
/// let mut names = Interner::new();
/// let mut b = Builder::new();
/// let one = b.int(1);
/// let body = b.block(&[], Some(one));
/// let f = b.func(Name::new(names.intern("one")), &[], body);
/// let root = b.module(None, &[f]);
/// let hir = b.finish(root)?;
///
/// let out = bcgen_lang::compile(&hir, &names)?;
/// let func = out.function(f).unwrap();
/// // Every instruction maps back to a node of the unit.
/// for pc in 0..out.module().function(func).unwrap().code().len() {
///     assert!(out.origin(func, pc as u32).is_some());
/// }
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Compiled {
    pub(crate) module: Module,
    pub(crate) entry: FuncId,
    pub(crate) start: Option<FuncId>,
    pub(crate) result: Option<GlobalId>,
    pub(crate) functions: Vec<(ItemId, FuncId)>,
    pub(crate) origins: Vec<Vec<NodeRef>>,
    pub(crate) classes: Vec<(ItemId, TypeId)>,
    pub(crate) methods: Vec<((ItemId, ItemId), FuncId)>,
    pub(crate) destructor: Option<String>,
}

impl Compiled {
    /// The LSB module.
    ///
    /// # Examples
    ///
    /// ```
    /// let hir = { let mut b = hir_lang::Builder::new(); let r = b.module(None, &[]); b.finish(r)? };
    /// let out = bcgen_lang::compile(&hir, &intern_lang::Interner::new())?;
    /// assert_eq!(out.module().functions().len(), 1); // the entry
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn module(&self) -> &Module {
        &self.module
    }

    /// The LSB module, by value (to hand to a VM or an encoder).
    ///
    /// # Examples
    ///
    /// ```
    /// let hir = { let mut b = hir_lang::Builder::new(); let r = b.module(None, &[]); b.finish(r)? };
    /// let module = bcgen_lang::compile(&hir, &intern_lang::Interner::new())?.into_module();
    /// assert!(!bytecode_lang::encode(&module).is_empty());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn into_module(self) -> Module {
        self.module
    }

    /// The entry function, `() -> dyn`, exported as `<entry>`: it returns the
    /// value of the module body (nil without one). Under
    /// [`BodyMode::Start`](crate::BodyMode::Start) the body runs once, in the
    /// start function, and the entry reads its kept value; under
    /// [`BodyMode::Entry`](crate::BodyMode::Entry) the entry is the body.
    ///
    /// # Examples
    ///
    /// ```
    /// let hir = { let mut b = hir_lang::Builder::new(); let r = b.module(None, &[]); b.finish(r)? };
    /// let out = bcgen_lang::compile(&hir, &intern_lang::Interner::new())?;
    /// assert!(out.module().function(out.entry()).is_some());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn entry(&self) -> FuncId {
        self.entry
    }

    /// The module's start function, if it has one: global and constant
    /// initializers, defaults evaluated once, and (under `BodyMode::Start`)
    /// the body.
    ///
    /// # Examples
    ///
    /// ```
    /// let hir = { let mut b = hir_lang::Builder::new(); let r = b.module(None, &[]); b.finish(r)? };
    /// assert_eq!(bcgen_lang::compile(&hir, &intern_lang::Interner::new())?.start(), None);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn start(&self) -> Option<FuncId> {
        self.start
    }

    /// The global holding the module body's value under `BodyMode::Start`.
    ///
    /// # Examples
    ///
    /// ```
    /// let hir = { let mut b = hir_lang::Builder::new(); let r = b.module(None, &[]); b.finish(r)? };
    /// assert!(bcgen_lang::compile(&hir, &intern_lang::Interner::new())?.result_global().is_none());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn result_global(&self) -> Option<GlobalId> {
        self.result
    }

    /// The function compiled for a HIR function item: its parameters are
    /// `dyn` (a by-reference parameter is a `ref cell dyn` holding an LSB
    /// reference), followed by an `i64` presence mask when any parameter has
    /// a default; it returns `dyn` (a generator's returns its coroutine). It
    /// carries the item's LSB parameter list, so it can be called typed
    /// (`call`, `Vm::run`) or bound dynamically. Root-level functions are
    /// exported under their names.
    ///
    /// # Examples
    ///
    /// See [`Compiled`].
    #[must_use]
    pub fn function(&self, item: ItemId) -> Option<FuncId> {
        self.functions
            .iter()
            .find(|(i, _)| *i == item)
            .map(|&(_, f)| f)
    }

    /// The HIR node instruction `pc` of `func` was compiled from.
    ///
    /// # Examples
    ///
    /// See [`Compiled`].
    #[must_use]
    pub fn origin(&self, func: FuncId, pc: u32) -> Option<NodeRef> {
        self.origins
            .get(func.index())
            .and_then(|o| o.get(pc as usize))
            .copied()
    }

    /// The HIR node of every instruction of `func`, indexed by pc.
    ///
    /// # Examples
    ///
    /// ```
    /// let hir = { let mut b = hir_lang::Builder::new(); let r = b.module(None, &[]); b.finish(r)? };
    /// let out = bcgen_lang::compile(&hir, &intern_lang::Interner::new())?;
    /// assert_eq!(out.origins(out.entry()).len(), out.module().function(out.entry()).unwrap().code().len());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn origins(&self, func: FuncId) -> &[NodeRef] {
        self.origins.get(func.index()).map_or(&[], Vec::as_slice)
    }

    /// The LSB struct type of a class or interface item (mixins have none).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, ClassDef, Generics, Item, ItemKind, List, Name};
    /// use intern_lang::Interner;
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// let class = ClassDef {
    ///     generics: Generics::default(),
    ///     bases: List::EMPTY,
    ///     interfaces: List::EMPTY,
    ///     fields: List::EMPTY,
    ///     items: List::EMPTY,
    ///     is_abstract: false,
    ///     is_final: false,
    ///     mixin: false,
    /// };
    /// let c = b.item(Item::new(Some(Name::new(names.intern("Point"))), ItemKind::Class(class)));
    /// let root = b.module(None, &[c]);
    /// let out = bcgen_lang::compile(&b.finish(root)?, &names)?;
    /// let ty = out.class_type(c).unwrap();
    /// assert!(matches!(out.module().types()[ty.index()], bytecode_lang::TypeDef::Struct(_)));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn class_type(&self, class: hir_lang::ItemId) -> Option<TypeId> {
        self.classes
            .iter()
            .find(|(i, _)| *i == class)
            .map(|&(_, t)| t)
    }

    /// The function a method item was compiled to for a class (a mixin's
    /// method has one per class using it; an abstract method has none).
    ///
    /// # Examples
    ///
    /// See `tests/classes.rs`; a class without methods has none:
    ///
    /// ```
    /// let hir = { let mut b = hir_lang::Builder::new(); let r = b.module(None, &[]); b.finish(r)? };
    /// let out = bcgen_lang::compile(&hir, &intern_lang::Interner::new())?;
    /// assert_eq!(out.method(hir.root(), hir.root()), None);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn method(&self, class: hir_lang::ItemId, method: hir_lang::ItemId) -> Option<FuncId> {
        self.methods
            .iter()
            .find(|(k, _)| *k == (class, method))
            .map(|&(_, f)| f)
    }

    /// The LSB method name of the destructor
    /// ([`Options::destructor`](crate::Options::destructor), `__destruct()`
    /// in the PHP profile), when a class of the unit defines one. LSB format
    /// 2 has no destructor flag: the host passes this name to bvm-lang's
    /// `Vm::set_destructor` on a VM made with the reference-counting memory
    /// profile, so destructors run where PHP runs them.
    ///
    /// # Examples
    ///
    /// ```
    /// let hir = { let mut b = hir_lang::Builder::new(); let r = b.module(None, &[]); b.finish(r)? };
    /// let out = bcgen_lang::compile(&hir, &intern_lang::Interner::new())?;
    /// assert_eq!(out.destructor(), None);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn destructor(&self) -> Option<&str> {
        self.destructor.as_deref()
    }
}
