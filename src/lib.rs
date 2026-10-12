//! # bcgen_lang
//!
//! Compiles HIR (the representation every LexerSketch language lowers into)
//! to LSB, the bytecode `bvm-lang` executes.
//!
//! ## The lazy path
//!
//! Build or lower a resolved unit, [`compile`] it, and hand the module to a
//! VM:
//!
//! ```
//! use hir_lang::{Builder, Name, OpKind};
//! use intern_lang::Interner;
//!
//! // fn add(a, b) { a + b }
//! let mut names = Interner::new();
//! let mut b = Builder::new();
//! let (pa, a) = b.local_param(Name::new(names.intern("a")));
//! let (pb, bb) = b.local_param(Name::new(names.intern("b")));
//! let (ua, ub) = (b.use_binder(a), b.use_binder(bb));
//! let sum = b.op(OpKind::Add, &[ua, ub]);
//! let body = b.block(&[], Some(sum));
//! let add = b.func(Name::new(names.intern("add")), &[pa, pb], body);
//! let root = b.module(None, &[add]);
//! let hir = b.finish(root)?;
//!
//! let out = bcgen_lang::compile(&hir, &names)?;
//! let module = out.module();
//! assert!(module.function(out.function(add).unwrap()).is_some());
//! assert!(!bytecode_lang::encode(module).is_empty());
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! Running it (with `bvm-lang`): `Program::load(out.into_module(), &host)`,
//! then `vm.run(func, &[Value::Int(2), Value::Int(3)])` returns `Int(5)`.
//!
//! ## What it compiles
//!
//! HIR spec v3 (hir-lang 0.4) to LSB format 2 (bytecode-lang 0.3), in the
//! **dynamic profile**: every value is an LSB `dyn`. Functions with defaults
//! (per call or once), named, variadic, and by-reference parameters, each
//! carrying its LSB parameter list so dynamic calls bind in the VM; locals in
//! registers, shared variables in LSB references; closures with explicit,
//! implicit, and recursive captures; generators (keyed `yield`, `yield
//! from`), `await`, and `spawn`; `if`, the loop primitive with its step,
//! labeled `break`/`continue`, `return`; `match` by a sequential decision
//! procedure, raising `NoMatch` when no arm matches; direct, dynamic, host,
//! and method calls; maps and arrays with PHP value semantics, separation
//! that copies only what is shared, and key coercion (or shared references);
//! `let_place` and PHP references into array elements; every OPS v2
//! operation with its policy (`pow`, `promote`, `shift = saturate`);
//! union and intersection type tests and casts; `throw` and
//! `try`/`catch`/`finally` by LSB's canonical lowering, `defer`; globals,
//! constants, statics, and the module body; named intrinsics through an
//! [`Intrinsics`] table ([`Intrinsics::mox`] maps every Mox intrinsic to an
//! inline fast path or a host function). Every instruction maps back to the
//! HIR node it came from ([`Compiled::origin`]) and to a line-table row.
//!
//! Not yet: classes, declared records and sums, and typed fast paths (0.5);
//! each is a precise [`CompileError::Unsupported`].
//!
//! ## Guarantees
//!
//! - **Loads.** Every module it emits passes `bvm-lang`'s load-time checks:
//!   registers, windows, constants, branch targets, and handlers in range.
//! - **Semantics.** Differential tests run random programs through the
//!   compiler and the VM, and through a reference interpreter written in
//!   the tests, comparing results, error kinds, and error locations.
//! - **No recursion over the input.** Generation is an explicit task stack;
//!   any nesting depth compiles in bounded native stack.
//! - **Budgeted and deterministic.** Output is bounded by
//!   [`Options::with_max_instructions`]; the same unit compiles to the same
//!   bytes.
//!
//! ## `no_std`
//!
//! The crate needs only `alloc`. The default `std` feature is additive.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(unused_must_use)]
#![deny(unused_results)]
#![deny(clippy::unwrap_used)]
#![deny(clippy::expect_used)]
#![deny(clippy::todo)]
#![deny(clippy::unimplemented)]
#![deny(clippy::print_stdout)]
#![deny(clippy::print_stderr)]
#![deny(clippy::dbg_macro)]

extern crate alloc;

mod analysis;
mod codegen;
mod error;
mod func;
mod intrinsics;
mod options;
mod output;
mod unit;

pub use error::{CompileError, Unsupported};
pub use intrinsics::{Arity, Fast, IntrinsicDef, Intrinsics, Lowering, LsbOp};
pub use options::{ArraySemantics, BodyMode, KeyCoercion, LineIndex, Locate, Location, Options};
pub use output::Compiled;

/// Compiles and runs the `rust` code blocks in `README.md`, `docs/API.md`,
/// and the current release notes as part of `cargo test`, so the published
/// examples cannot drift from the API.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
#[doc = include_str!("../docs/API.md")]
#[doc = include_str!("../docs/release/v0.3.0.md")]
pub struct MarkdownDocTests;

use hir_lang::Hir;
use intern_lang::Lookup;

/// Compiles a resolved unit with the default [`Options`] (the PHP profile).
///
/// `names` is the interner the unit's names were interned in; function,
/// import, property, and debug names are read from it.
///
/// # Errors
///
/// A [`CompileError`] naming the first form that does not compile, in the
/// unit's canonical order.
///
/// # Examples
///
/// ```
/// use hir_lang::Builder;
/// use intern_lang::Interner;
///
/// let mut b = Builder::new();
/// let root = b.module(None, &[]);
/// let hir = b.finish(root)?;
/// let out = bcgen_lang::compile(&hir, &Interner::new())?;
/// assert_eq!(out.module().functions().len(), 1); // the entry function
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn compile<L: Lookup>(hir: &Hir, names: &L) -> Result<Compiled, CompileError> {
    Compiler::new(Options::new()).compile(hir, names)
}

/// A configured compiler: [`Options`] and, optionally, a [`Locate`] for the
/// line tables.
///
/// # Examples
///
/// ```
/// use bcgen_lang::{Compiler, LineIndex, Options};
/// use hir_lang::Builder;
/// use intern_lang::Interner;
///
/// let lines = LineIndex::new("main.mox", 0, "");
/// let mut b = Builder::new();
/// let root = b.module(None, &[]);
/// let hir = b.finish(root)?;
/// let out = Compiler::new(Options::new())
///     .with_locator(&lines)
///     .compile(&hir, &Interner::new())?;
/// assert!(out.start().is_none());
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone)]
pub struct Compiler<'a> {
    options: Options,
    locator: Option<&'a dyn Locate>,
}

impl core::fmt::Debug for Compiler<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Compiler")
            .field("options", &self.options)
            .field("locator", &self.locator.is_some())
            .finish()
    }
}

impl Compiler<'static> {
    /// A compiler with these options and no locator (line-table rows carry
    /// byte offsets; see [`Locate`]).
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{ArraySemantics, Compiler, Options};
    ///
    /// let c = Compiler::new(Options::new().with_arrays(ArraySemantics::Reference));
    /// assert_eq!(c.options().arrays(), ArraySemantics::Reference);
    /// ```
    #[must_use]
    pub fn new(options: Options) -> Self {
        Compiler {
            options,
            locator: None,
        }
    }
}

impl Compiler<'_> {
    /// The same compiler, writing line-table rows through `locator`.
    ///
    /// # Examples
    ///
    /// See [`Compiler`].
    #[must_use]
    pub fn with_locator(self, locator: &dyn Locate) -> Compiler<'_> {
        Compiler {
            options: self.options,
            locator: Some(locator),
        }
    }

    /// The options.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{Compiler, Options};
    ///
    /// assert_eq!(Compiler::new(Options::new()).options(), &Options::new());
    /// ```
    #[must_use]
    pub fn options(&self) -> &Options {
        &self.options
    }

    /// Compiles a resolved unit.
    ///
    /// # Errors
    ///
    /// A [`CompileError`] naming the first form that does not compile.
    ///
    /// # Examples
    ///
    /// See [`Compiler`].
    pub fn compile<L: Lookup>(&self, hir: &Hir, names: &L) -> Result<Compiled, CompileError> {
        unit::compile(hir, names, &self.options, self.locator)
    }
}
