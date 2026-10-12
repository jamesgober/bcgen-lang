//! Why a unit did not compile.

use core::fmt;

use bytecode_lang::BuildError;
use hir_lang::{NodeRef, Span, Symbol};

use crate::intrinsics::Arity;

/// A HIR form this release does not compile, named precisely.
///
/// Every variant says what is missing and where it is planned, so a front end
/// can report "not supported yet" instead of guessing. Forms that need a
/// missing LSB feature (not a later bcgen-lang release) say so.
///
/// # Examples
///
/// ```
/// use bcgen_lang::Unsupported;
///
/// assert!(Unsupported::Class.to_string().contains("0.5"));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Unsupported {
    /// Classes, impls, interfaces with bodies, mixins, and receiver parameters
    /// (0.5).
    Class,
    /// A record or struct literal or pattern naming a declared type, a sum
    /// variant, or a constructor pattern (typed data arrives with classes in
    /// 0.5; anonymous records compile, as maps).
    Record,
    /// `*e`, `&e`, a `ref` pattern, or binding by reference: the dynamic
    /// profile has no pointer values (PHP references are places, see
    /// [`RefPlace`](Unsupported::RefPlace)).
    Reference,
    /// A reference (`&`) to a place LSB cannot reference: an appended
    /// element (`&$a[]`, whose key is known only after the append), a
    /// variable variable, or a value that is not a place.
    RefPlace,
    /// `$$name`: LSB frames have no names at run time.
    VarVar,
    /// An atomic, volatile, or fence intrinsic (native backends only; named
    /// intrinsics compile through the [`Intrinsics`](crate::Intrinsics)
    /// table).
    Intrinsic,
    /// Inline assembly (native backends only).
    Asm,
    /// A big-integer literal (no big-integer runtime yet).
    BigInt,
    /// A definition of another compilation unit: LSB modules link to host
    /// functions only, so cross-unit calls wait for loader-lang.
    ForeignUnit,
    /// A path resolved only by type (`Vec::new`), or naming a primitive,
    /// type parameter, or const parameter as a value (typed paths, 0.5).
    TypeDirected,
    /// A host function used as a value rather than called: the compiler does
    /// not know the host function's parameter list, which a first-class
    /// value needs (LSB §5.15).
    ExternValue,
    /// Spread or named arguments to a host function: the compiler does not
    /// know its parameter names, so imports take exactly their positional
    /// parameters.
    ExternArgs,
    /// A conversion at a width dynamic values do not have (`zext`/`sext` to
    /// fewer than 64 bits, 32-bit bit casts).
    Conversion,
    /// A cast to a type the dynamic profile cannot test or produce.
    Cast,
    /// A range pattern bound or type test this release cannot evaluate.
    Pattern,
}

impl Unsupported {
    /// A short description of the form and where it is planned.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::Unsupported;
    ///
    /// assert_eq!(Unsupported::Asm.describe(), "inline assembly (native backends only)");
    /// ```
    #[must_use]
    pub const fn describe(self) -> &'static str {
        match self {
            Self::Class => {
                "classes, impls, mixins, and receiver parameters arrive in bcgen-lang 0.5"
            }
            Self::Record => {
                "declared record, struct, and sum types arrive with classes in bcgen-lang 0.5"
            }
            Self::Reference => {
                "dereference, borrow, and by-reference patterns (the dynamic profile has no pointer values)"
            }
            Self::RefPlace => {
                "a reference to an appended element, a variable variable, or a value that is not a place"
            }
            Self::VarVar => "variable variables (LSB frames have no names at run time)",
            Self::Intrinsic => "atomic, volatile, and fence intrinsics (native backends only)",
            Self::Asm => "inline assembly (native backends only)",
            Self::BigInt => "big-integer literals (no big-integer runtime yet)",
            Self::ForeignUnit => {
                "definitions of another unit (LSB modules link to host functions only)"
            }
            Self::TypeDirected => {
                "type-directed paths and type-level values arrive with typed fast paths in bcgen-lang 0.5"
            }
            Self::ExternValue => {
                "a host function used as a value (its parameter list is unknown to the compiler)"
            }
            Self::ExternArgs => "spread or named arguments to a host function",
            Self::Conversion => "a conversion at a width dynamic values do not have",
            Self::Cast => "a cast to a type the dynamic profile cannot test or produce",
            Self::Pattern => "a pattern form the dynamic profile cannot test",
        }
    }
}

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.describe())
    }
}

/// Why [`compile`](crate::compile) refused a unit.
///
/// Errors about the program name the HIR node and its source span, so a
/// front end can point at the offending code. Compilation stops at the first
/// error, in the canonical order of the unit.
///
/// # Examples
///
/// ```
/// use bcgen_lang::CompileError;
/// use hir_lang::{Builder, Effects, Expr, Item, ItemKind, List};
/// use intern_lang::Interner;
///
/// // A module whose body failed to lower: it was reported already, so it
/// // does not compile.
/// let mut b = Builder::new();
/// let body = b.expr(Expr::Err);
/// let module = ItemKind::Module { items: List::EMPTY, body: Some(body), effects: Effects::NONE };
/// let root = b.item(Item::new(None, module));
/// let hir = b.finish(root)?;
///
/// let err = bcgen_lang::compile(&hir, &Interner::new()).unwrap_err();
/// assert!(matches!(err, CompileError::ErrorNode { .. }));
/// # Ok::<(), hir_lang::HirError>(())
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CompileError {
    /// A form this release does not compile.
    Unsupported {
        /// What is missing.
        feature: Unsupported,
        /// The node.
        node: NodeRef,
        /// Its source span.
        span: Span,
    },
    /// A path the resolver left unresolved (or resolved to `Res::Err`): the
    /// compiler runs on resolved HIR.
    Unresolved {
        /// The path's node.
        node: NodeRef,
        /// Its source span.
        span: Span,
    },
    /// An error node (`Expr::Err`, `Stmt::Err`, ...) from lenient lowering:
    /// broken source was reported already and does not compile.
    ErrorNode {
        /// The node.
        node: NodeRef,
        /// Its source span.
        span: Span,
    },
    /// An integer literal outside the dynamic integer range (`i64`).
    LiteralOutOfRange {
        /// The literal's node.
        node: NodeRef,
        /// Its source span.
        span: Span,
    },
    /// An assignment target that is not a writable place (a function, a
    /// constant, an append read).
    NotAssignable {
        /// The target's node.
        node: NodeRef,
        /// Its source span.
        span: Span,
    },
    /// A named intrinsic the [`Intrinsics`](crate::Intrinsics) table does
    /// not have.
    UnknownIntrinsic {
        /// The intrinsic's name.
        name: Symbol,
        /// The intrinsic's node.
        node: NodeRef,
        /// Its source span.
        span: Span,
    },
    /// A named intrinsic called with a number of operands its table entry
    /// does not accept.
    IntrinsicArity {
        /// The intrinsic's node.
        node: NodeRef,
        /// Its source span.
        span: Span,
        /// The operands it takes.
        arity: Arity,
        /// The operands it was given.
        found: u32,
    },
    /// A call with more arguments than an LSB call window carries (255,
    /// counting a method's receiver).
    TooManyArgs {
        /// The call.
        node: NodeRef,
        /// Its source span.
        span: Span,
        /// The limit.
        limit: u32,
    },
    /// A function or closure with more parameters than an LSB parameter list
    /// carries: 64 when a parameter has a default (the width of the presence
    /// mask), else 255 (including a generator closure's captures).
    TooManyParams {
        /// The function or closure.
        node: NodeRef,
        /// Its source span.
        span: Span,
        /// The limit.
        limit: u32,
    },
    /// A `finally` (or `defer`) left by more distinct jump targets than its
    /// `i8` completion kind can number (124).
    TooManyJumps {
        /// The `try` or `defer`.
        node: NodeRef,
        /// Its source span.
        span: Span,
    },
    /// The instruction budget ([`Options::with_max_instructions`]) ran out.
    ///
    /// [`Options::with_max_instructions`]: crate::Options::with_max_instructions
    BudgetExceeded {
        /// The budget, in instructions.
        limit: u64,
    },
    /// The LSB builder refused the module: a format limit (65,536 registers
    /// in one function, 4 GiB in one section, ...).
    Build(BuildError),
}

impl CompileError {
    /// The node the error is about, when it is about one.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::CompileError;
    ///
    /// assert_eq!(CompileError::BudgetExceeded { limit: 1 }.node(), None);
    /// ```
    #[must_use]
    pub const fn node(&self) -> Option<NodeRef> {
        match *self {
            Self::Unsupported { node, .. }
            | Self::Unresolved { node, .. }
            | Self::ErrorNode { node, .. }
            | Self::LiteralOutOfRange { node, .. }
            | Self::NotAssignable { node, .. }
            | Self::UnknownIntrinsic { node, .. }
            | Self::IntrinsicArity { node, .. }
            | Self::TooManyArgs { node, .. }
            | Self::TooManyParams { node, .. }
            | Self::TooManyJumps { node, .. } => Some(node),
            Self::BudgetExceeded { .. } | Self::Build(_) => None,
        }
    }

    /// The source span of the node the error is about, when there is one.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::CompileError;
    ///
    /// assert_eq!(CompileError::BudgetExceeded { limit: 1 }.span(), None);
    /// ```
    #[must_use]
    pub const fn span(&self) -> Option<Span> {
        match *self {
            Self::Unsupported { span, .. }
            | Self::Unresolved { span, .. }
            | Self::ErrorNode { span, .. }
            | Self::LiteralOutOfRange { span, .. }
            | Self::NotAssignable { span, .. }
            | Self::UnknownIntrinsic { span, .. }
            | Self::IntrinsicArity { span, .. }
            | Self::TooManyArgs { span, .. }
            | Self::TooManyParams { span, .. }
            | Self::TooManyJumps { span, .. } => Some(span),
            Self::BudgetExceeded { .. } | Self::Build(_) => None,
        }
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported { feature, span, .. } => {
                write!(f, "unsupported at {span:?}: {feature}")
            }
            Self::Unresolved { span, .. } => write!(f, "unresolved path at {span:?}"),
            Self::ErrorNode { span, .. } => write!(f, "error node at {span:?}"),
            Self::LiteralOutOfRange { span, .. } => {
                write!(f, "integer literal at {span:?} is outside the i64 range")
            }
            Self::NotAssignable { span, .. } => {
                write!(f, "assignment target at {span:?} is not a writable place")
            }
            Self::UnknownIntrinsic { span, .. } => {
                write!(f, "intrinsic at {span:?} is not in the intrinsic table")
            }
            Self::IntrinsicArity {
                span, arity, found, ..
            } => {
                write!(
                    f,
                    "intrinsic at {span:?} takes {arity} operands, not {found}"
                )
            }
            Self::TooManyArgs { span, limit, .. } => {
                write!(f, "call at {span:?} has more than {limit} arguments")
            }
            Self::TooManyParams { span, limit, .. } => {
                write!(f, "function at {span:?} has more than {limit} parameters")
            }
            Self::TooManyJumps { span, .. } => write!(
                f,
                "finally at {span:?} is left by more than 124 distinct jump targets"
            ),
            Self::BudgetExceeded { limit } => {
                write!(f, "the instruction budget of {limit} ran out")
            }
            Self::Build(e) => write!(f, "LSB builder: {e}"),
        }
    }
}

impl core::error::Error for CompileError {}

impl From<BuildError> for CompileError {
    fn from(e: BuildError) -> Self {
        Self::Build(e)
    }
}
