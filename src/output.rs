//! The result of compiling a unit.

use alloc::vec::Vec;

use bytecode_lang::{FuncId, GlobalId, Module};
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

    /// The direct-call function compiled for a HIR function item: its
    /// parameters are `dyn` (a by-reference parameter is a cell), followed by
    /// an `i64` presence mask when any parameter has a default; it returns
    /// `dyn`. Root-level functions are exported under their names.
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
}
