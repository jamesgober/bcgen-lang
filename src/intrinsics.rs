//! The intrinsic table (LexerSketch decision D27): how each named intrinsic
//! (`Intrinsic::Named` in HIR) compiles.
//!
//! A language's lowering turns operators whose semantics are not OPS
//! operations (PHP's loose `==`, `.`, `%`, `**`, casts) into named
//! intrinsics. The embedder registers each name with one of three
//! lowerings: an LSB instruction sequence with LSB's own semantics, a call
//! to a host function the embedder provides to the VM, or a **guarded fast
//! path**: the operands are tested at run time, the LSB sequence runs where
//! its result is exactly the language's, and the host function runs
//! everywhere else. Fast paths never invoke an LSB hook, so their results do
//! not depend on which hooks a module binds.
//!
//! A fourth kind, a **class operation** ([`ClassOp`]: `new`, `instanceof`,
//! `clone`), compiles inline against the unit's own classes and falls back
//! to the host function for anything else (a class name only known at run
//! time that the unit does not declare, a non-object clone).
//!
//! [`Intrinsics::mox`] maps every intrinsic of the Mox sketch; `docs/API.md`
//! states each mapping and the exact semantics its host function must have.

use alloc::collections::BTreeMap;
use alloc::string::String;
use core::fmt;

/// How many operands an intrinsic takes: from [`min`](Arity::min) to
/// [`max`](Arity::max), both inclusive (at most 255, an import's limit).
///
/// # Examples
///
/// ```
/// use bcgen_lang::Arity;
///
/// assert!(Arity::exact(2).accepts(2));
/// assert!(!Arity::exact(2).accepts(3));
/// assert!(Arity::at_least(1).accepts(255));
/// assert_eq!(Arity::at_least(1).to_string(), "1 to 255");
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Arity {
    min: u8,
    max: u8,
}

impl Arity {
    /// Exactly `n` operands.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Arity::exact(1).max(), 1);
    /// ```
    #[must_use]
    pub const fn exact(n: u8) -> Self {
        Arity { min: n, max: n }
    }

    /// From `min` to `max` operands (a `max` below `min` is raised to it).
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::Arity;
    ///
    /// assert_eq!(Arity::range(2, 1), Arity::exact(2));
    /// ```
    #[must_use]
    pub const fn range(min: u8, max: u8) -> Self {
        Arity {
            min,
            max: if max < min { min } else { max },
        }
    }

    /// `n` operands or more, up to 255.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Arity::at_least(0).max(), 255);
    /// ```
    #[must_use]
    pub const fn at_least(n: u8) -> Self {
        Arity::range(n, u8::MAX)
    }

    /// The fewest operands.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Arity::exact(3).min(), 3);
    /// ```
    #[must_use]
    pub const fn min(self) -> u8 {
        self.min
    }

    /// The most operands.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Arity::exact(3).max(), 3);
    /// ```
    #[must_use]
    pub const fn max(self) -> u8 {
        self.max
    }

    /// Whether `n` operands are accepted.
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(!bcgen_lang::Arity::range(1, 2).accepts(0));
    /// ```
    #[must_use]
    pub const fn accepts(self, n: usize) -> bool {
        n >= self.min as usize && n <= self.max as usize
    }
}

impl fmt::Display for Arity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.min == self.max {
            write!(f, "{}", self.min)
        } else {
            write!(f, "{} to {}", self.min, self.max)
        }
    }
}

/// An LSB instruction sequence with LSB's own semantics, hooks included
/// (LSB §5.6–§5.10). These are the 0.2 built-in intrinsics.
///
/// # Examples
///
/// ```
/// use bcgen_lang::{Arity, LsbOp};
///
/// assert_eq!(LsbOp::Concat.arity(), Arity::exact(2));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LsbOp {
    /// `dconcat`: two strings concatenated; other kinds go to the `concat`
    /// hook, else `TypeError`.
    Concat,
    /// `dlen`, as a dynamic `int`: string bytes or collection entries; else
    /// the `len` hook.
    Len,
    /// `dtruthy`, as a dynamic `bool` (the `truthy` hook for non-scalars).
    Truthy,
    /// `dnot`, as a dynamic `bool`: the negated truthiness.
    Not,
    /// `type_of`, as a dynamic `int`: the LSB kind code (LSB §2.2).
    TypeOf,
    /// `diter_new` (after a copy-on-write `dup` under PHP arrays, so the
    /// loop iterates a snapshot): an iterator over a collection or
    /// coroutine.
    Iter,
    /// One `iter_next`: `nil` when the iterator is done, else the pair
    /// `[key, value]` as a new array.
    IterNext,
    /// `resume coro, value`: the value the coroutine (operand 1) yields,
    /// awaits, or returns next, after resuming it with operand 2 (PHP
    /// `Generator::send`, Python `send`).
    Resume,
    /// `resume_throw coro, error`: as [`Resume`](LsbOp::Resume), raising
    /// operand 2 at the suspension point (PHP `Generator::throw`).
    ResumeThrow,
    /// `coro_close coro, signal`: closes the coroutine, running its pending
    /// `finally` blocks (LSB §5.13 rule 11).
    CoroClose,
    /// `coro_key`: the key of the value most recently yielded (PHP
    /// `Generator::key`).
    CoroKey,
    /// `coro_result`: a returned coroutine's return value (PHP
    /// `Generator::getReturn`).
    CoroResult,
    /// `coro_status`, as a dynamic `int` (0 created, 1 running, 2 yielded,
    /// 3 awaiting, 4 returned, 5 failed).
    CoroStatus,
    /// `err_code`, as a dynamic `int`: the code of a caught runtime error
    /// value (`200` for `NoMatch`), else 0.
    ErrCode,
    /// `err_payload`: the payload of a caught runtime error value (the
    /// unmatched value of a `NoMatch`), else nil.
    ErrPayload,
}

impl LsbOp {
    /// The operands the op takes.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::LsbOp::Len.arity().max(), 1);
    /// ```
    #[must_use]
    pub const fn arity(self) -> Arity {
        match self {
            Self::Concat | Self::Resume | Self::ResumeThrow | Self::CoroClose => Arity::exact(2),
            Self::Len
            | Self::Truthy
            | Self::Not
            | Self::TypeOf
            | Self::Iter
            | Self::IterNext
            | Self::CoroKey
            | Self::CoroResult
            | Self::CoroStatus
            | Self::ErrCode
            | Self::ErrPayload => Arity::exact(1),
        }
    }
}

/// A guarded fast path: the operand kinds where an LSB sequence computes
/// exactly the intrinsic's result, tested at run time; outside that domain
/// the intrinsic's host function is called with the same operands.
///
/// Each variant states its **domain** (where the inline code runs) and what
/// it computes there. The domains are chosen so that the inline result is
/// PHP 8's (Mox's) result; a host function bound to the same intrinsic must
/// agree with the fast path on its domain, and is free everywhere else.
/// Kinds are LSB dynamic kinds (§2.2): `nil`, `bool`, `int` (i64), `float`
/// (f64), `str` (bytes), `map`.
///
/// # Examples
///
/// ```
/// use bcgen_lang::{Arity, Fast};
///
/// assert_eq!(Fast::LooseEq.arity(), Arity::exact(2));
/// assert_eq!(Fast::ConcatN.arity(), Arity::at_least(0));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Fast {
    /// Domain: both `str`. Result: the byte concatenation.
    Concat,
    /// Domain: every operand `str` (any count, none included). Result: the
    /// byte concatenation in order (`""` for none), one `str_concat_n`.
    ConcatN,
    /// Domain: both `int`. Result: the truncated remainder (the sign follows
    /// the dividend; `MIN % -1` is 0); a zero divisor raises `DivByZero`
    /// (E0002) at the intrinsic.
    IntRem,
    /// Domain: both numbers (`int` or `float`). Result: `dpow` with
    /// `overflow = promote`: an exact `int` power when it fits, else the
    /// nearest `float`; a negative integer exponent gives the `float`
    /// power; floats by the family's `ls_pow`.
    NumPow,
    /// Domain: both `int`. Result: `shl` with `shift = saturate` (an amount
    /// of 64 or more gives 0; a negative amount raises `ShiftOutOfRange`,
    /// E0003).
    IntShl,
    /// Domain: both `int`. Result: arithmetic `shr` with `shift = saturate`
    /// (64 or more gives 0, or -1 for a negative value; a negative amount
    /// raises `ShiftOutOfRange`).
    IntShr,
    /// Domain: both in `nil`, `bool`, `int`, `float`. Result: the exclusive
    /// or of their truthiness (`nil`, `false`, `0`, `±0.0` are false; NaN is
    /// true), a `bool`.
    ScalarXor,
    /// Domain: the same kind in `nil`, `bool`, `int`, `float` (equality by
    /// value; IEEE for floats, so NaN equals nothing and `-0.0 == 0.0`), or
    /// two `str` with equal bytes (`true`). A `bool`.
    LooseEq,
    /// The negation of [`LooseEq`](Fast::LooseEq), on the same domain.
    LooseNe,
    /// Domain: both in `nil`, `bool`, `int`, `float`, `str`. Result: `true`
    /// exactly when the kinds are equal and the values are (floats by IEEE,
    /// strings by bytes). A `bool`.
    StrictEq,
    /// The negation of [`StrictEq`](Fast::StrictEq), on the same domain.
    StrictNe,
    /// Domain: two `int`s or two `float`s. Result: `a < b` (false with NaN).
    Lt,
    /// Domain: two `int`s or two `float`s. Result: `a <= b`.
    Le,
    /// Domain: two `int`s or two `float`s. Result: `a > b`.
    Gt,
    /// Domain: two `int`s or two `float`s. Result: `a >= b`.
    Ge,
    /// Domain: two `int`s. Result: -1, 0, or 1 as an `int`.
    IntSpaceship,
    /// Domain: an `int` or a `float`. Result: the operand.
    NumIdentity,
    /// Domain: an `int`. Result: its bitwise complement.
    IntBitNot,
    /// Domain: `int` (itself), `bool` (0 or 1), `nil` (0), and `float` by
    /// PHP 7/8's `zend_dval_to_lval` on 64-bit platforms: truncated toward
    /// zero when in `[-2^63, 2^63)`, NaN and infinities 0, and any other
    /// finite value taken modulo 2^64 into the signed range (`1e19` is
    /// `-8446744073709551616`, `-1e19` is `8446744073709551616`). An `int`.
    ToInt,
    /// Domain: `float` (itself), `int` (the nearest `float`, ties to even),
    /// `bool` (0.0 or 1.0), `nil` (0.0). A `float`.
    ToFloat,
    /// Domain: `str`. Result: the operand.
    ToStr,
    /// Domain: `nil`, `bool`, `int`, `float`. Result: the truthiness, a
    /// `bool`.
    ToBool,
    /// Domain: `map`. Result: the operand.
    ToArray,
    /// Domain: a `str` and an `int` offset `i` with `-len <= i < len`.
    /// Result: the one-byte string at `i` (counted from the end when
    /// negative), PHP 7.1+'s `$s[i]`. Out-of-range offsets and every other
    /// operand kind go to the host function (PHP: a warning and `""`, or a
    /// `TypeError` for an offset that is not an integer).
    StrOffset,
}

impl Fast {
    /// The operands the fast path takes.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Fast::ToInt.arity().min(), 1);
    /// ```
    #[must_use]
    pub const fn arity(self) -> Arity {
        match self {
            Self::ConcatN => Arity::at_least(0),
            Self::StrOffset => Arity::exact(2),
            Self::NumIdentity
            | Self::IntBitNot
            | Self::ToInt
            | Self::ToFloat
            | Self::ToStr
            | Self::ToBool
            | Self::ToArray => Arity::exact(1),
            _ => Arity::exact(2),
        }
    }
}

/// A class operation: compiled inline against the classes the unit
/// declares, with a host function for whatever the unit does not declare.
///
/// # Examples
///
/// ```
/// use bcgen_lang::{Arity, ClassOp};
///
/// assert_eq!(ClassOp::InstanceOf.arity(), Arity::range(1, 2));
/// assert_eq!(ClassOp::New.arity(), Arity::at_least(0));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ClassOp {
    /// `new C(args)`: the class is the intrinsic's type argument
    /// (`mox.new<C>(args)`), else operand 1, and the rest are the
    /// constructor's arguments (spread and named ones included, through an
    /// extern call). A class of the unit (a path, `C::class`,
    /// `self::class`, `parent::class`) is instantiated inline: a new struct,
    /// its property defaults, then the constructor, with the arguments
    /// bound by the constructor's parameter list. `static::class` and a
    /// class value only known at run time (a string name, an object) are
    /// looked up among the unit's classes at run time; a name the unit does
    /// not declare goes to the host function with the name and the
    /// arguments (positional only).
    New,
    /// `x instanceof C`: the class or interface is the type argument
    /// (`mox.instanceof<I>(x)`, the only way HIR can name an interface in
    /// an expression), else operand 2. Inline for the unit's classes
    /// (`is_type`) and interfaces (a marker method); a class value only
    /// known at run time is looked up the same way; anything else goes to
    /// the host function.
    InstanceOf,
    /// `clone x`: an instance of a unit class is copied (`dup`, a new
    /// identity; array properties copy on write) and the clone method
    /// ([`Options::clone_method`](crate::Options::clone_method)) is called
    /// on the copy when its class has one; every other value goes to the
    /// host function.
    Clone,
}

impl ClassOp {
    /// The operands the operation takes.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::ClassOp::Clone.arity().max(), 1);
    /// ```
    #[must_use]
    pub const fn arity(self) -> Arity {
        match self {
            Self::New => Arity::at_least(0),
            Self::InstanceOf => Arity::range(1, 2),
            Self::Clone => Arity::exact(1),
        }
    }
}

/// How one named intrinsic compiles.
///
/// # Examples
///
/// ```
/// use bcgen_lang::{Fast, Lowering};
///
/// let l = Lowering::Fast { fast: Fast::Concat, module: "mox".into(), name: "concat".into() };
/// assert_eq!(l.host(), Some(("mox", "concat")));
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Lowering {
    /// An LSB sequence, with LSB's semantics (hooks included).
    Lsb(LsbOp),
    /// A call to the host function `module`.`name` (an LSB import taking the
    /// operands as `dyn` and returning a `dyn`), always.
    Host {
        /// The import module.
        module: String,
        /// The function name.
        name: String,
    },
    /// The fast path inline on its domain, the host function `module`.`name`
    /// everywhere else.
    Fast {
        /// The guarded fast path.
        fast: Fast,
        /// The import module of the slow path.
        module: String,
        /// The function name of the slow path.
        name: String,
    },
    /// A class operation, inline for the unit's classes, the host function
    /// `module`.`name` for everything else. A call of the extern path of
    /// the same name compiles the same way (lowering templates call host
    /// symbols, not intrinsics).
    Class {
        /// The operation.
        op: ClassOp,
        /// The import module of the fallback.
        module: String,
        /// The function name of the fallback.
        name: String,
    },
}

impl Lowering {
    /// The host function this lowering may call, as (module, name).
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{Lowering, LsbOp};
    ///
    /// assert_eq!(Lowering::Lsb(LsbOp::Len).host(), None);
    /// ```
    #[must_use]
    pub fn host(&self) -> Option<(&str, &str)> {
        match self {
            Self::Lsb(_) => None,
            Self::Host { module, name }
            | Self::Fast { module, name, .. }
            | Self::Class { module, name, .. } => Some((module.as_str(), name.as_str())),
        }
    }
}

/// One entry of an [`Intrinsics`] table: the operands it takes and how it
/// compiles.
///
/// # Examples
///
/// ```
/// use bcgen_lang::{Arity, Intrinsics};
///
/// let t = Intrinsics::mox();
/// let def = t.get("mox.concat_n").unwrap();
/// assert_eq!(def.arity(), Arity::at_least(0));
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntrinsicDef {
    arity: Arity,
    lowering: Lowering,
}

impl IntrinsicDef {
    /// The operands it takes; a call with another count is
    /// [`CompileError::IntrinsicArity`](crate::CompileError::IntrinsicArity).
    ///
    /// # Examples
    ///
    /// See [`IntrinsicDef`].
    #[must_use]
    pub fn arity(&self) -> Arity {
        self.arity
    }

    /// How it compiles.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{Intrinsics, Lowering, LsbOp};
    ///
    /// let t = Intrinsics::core();
    /// assert_eq!(t.get("len").unwrap().lowering(), &Lowering::Lsb(LsbOp::Len));
    /// ```
    #[must_use]
    pub fn lowering(&self) -> &Lowering {
        &self.lowering
    }
}

/// The intrinsic table: named intrinsic → arity and lowering. A name that is
/// not in the table is [`CompileError::UnknownIntrinsic`](crate::CompileError::UnknownIntrinsic).
///
/// [`Options::new`](crate::Options::new) starts from [`Intrinsics::core`];
/// Mox uses [`Intrinsics::mox`].
///
/// # Examples
///
/// ```
/// use bcgen_lang::{Arity, Fast, Intrinsics, LsbOp, Options};
///
/// let table = Intrinsics::new()
///     .with_lsb("concat", LsbOp::Concat)
///     .with_host("lang.format", Arity::exact(1), "lang", "format")
///     .with_fast("lang.eq", Fast::StrictEq, "lang", "eq");
/// assert_eq!(table.len(), 3);
/// let opts = Options::new().with_intrinsics(table);
/// assert!(opts.intrinsics().get("lang.eq").is_some());
/// ```
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Intrinsics {
    table: BTreeMap<String, IntrinsicDef>,
}

impl Intrinsics {
    /// An empty table.
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(bcgen_lang::Intrinsics::new().is_empty());
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Intrinsics::default()
    }

    /// The built-in LSB intrinsics (see [`LsbOp`]): `concat`, `len`,
    /// `truthy`, `lnot`, `type_of`, `iter`, `iter_next`, the coroutine
    /// controls `resume`, `resume_throw`, `coro_close`, `coro_key`,
    /// `coro_result`, `coro_status` (what a runtime's generator object
    /// lowers to), and `err_code`, `err_payload` (what a runtime's exception
    /// mapping reads from a caught error value).
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Intrinsics::core().len(), 15);
    /// ```
    #[must_use]
    pub fn core() -> Self {
        Intrinsics::new()
            .with_lsb("concat", LsbOp::Concat)
            .with_lsb("len", LsbOp::Len)
            .with_lsb("truthy", LsbOp::Truthy)
            .with_lsb("lnot", LsbOp::Not)
            .with_lsb("type_of", LsbOp::TypeOf)
            .with_lsb("iter", LsbOp::Iter)
            .with_lsb("iter_next", LsbOp::IterNext)
            .with_lsb("resume", LsbOp::Resume)
            .with_lsb("resume_throw", LsbOp::ResumeThrow)
            .with_lsb("coro_close", LsbOp::CoroClose)
            .with_lsb("coro_key", LsbOp::CoroKey)
            .with_lsb("coro_result", LsbOp::CoroResult)
            .with_lsb("coro_status", LsbOp::CoroStatus)
            .with_lsb("err_code", LsbOp::ErrCode)
            .with_lsb("err_payload", LsbOp::ErrPayload)
    }

    /// [`core`](Intrinsics::core) plus every intrinsic of the Mox sketch
    /// (`_lexersketch/sketches/mox.lsf`), each a [`Fast`] path over the host
    /// function `mox`.`<name>` where one is exact, a [`ClassOp`] over it for
    /// `mox.instanceof` and `mox.clone`, else the host function alone
    /// (`mox.cast_object`); plus `mox.new` (the sketch's `new_object`
    /// template calls the extern `mox.new`) as [`ClassOp::New`], and
    /// `mox.str_offset` ([`Fast::StrOffset`]) for
    /// [`Options::with_string_offsets`](crate::Options::with_string_offsets).
    /// The table in `docs/API.md` gives every mapping and the semantics its
    /// host function must implement.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{Fast, Intrinsics, Lowering};
    ///
    /// let t = Intrinsics::mox();
    /// assert!(matches!(
    ///     t.get("mox.loose_eq").unwrap().lowering(),
    ///     Lowering::Fast { fast: Fast::LooseEq, .. }
    /// ));
    /// assert!(matches!(t.get("mox.clone").unwrap().lowering(), Lowering::Class { .. }));
    /// assert!(matches!(t.get("mox.cast_object").unwrap().lowering(), Lowering::Host { .. }));
    /// ```
    #[must_use]
    pub fn mox() -> Self {
        const FAST: [(&str, Fast); 24] = [
            ("concat", Fast::Concat),
            ("concat_n", Fast::ConcatN),
            ("mod", Fast::IntRem),
            ("pow", Fast::NumPow),
            ("shl", Fast::IntShl),
            ("shr", Fast::IntShr),
            ("xor", Fast::ScalarXor),
            ("loose_eq", Fast::LooseEq),
            ("loose_ne", Fast::LooseNe),
            ("identical", Fast::StrictEq),
            ("not_identical", Fast::StrictNe),
            ("lt", Fast::Lt),
            ("le", Fast::Le),
            ("gt", Fast::Gt),
            ("ge", Fast::Ge),
            ("spaceship", Fast::IntSpaceship),
            ("to_number", Fast::NumIdentity),
            ("bit_not", Fast::IntBitNot),
            ("cast_int", Fast::ToInt),
            ("cast_float", Fast::ToFloat),
            ("cast_string", Fast::ToStr),
            ("cast_bool", Fast::ToBool),
            ("cast_array", Fast::ToArray),
            ("str_offset", Fast::StrOffset),
        ];
        const CLASS: [(&str, ClassOp); 3] = [
            ("new", ClassOp::New),
            ("instanceof", ClassOp::InstanceOf),
            ("clone", ClassOp::Clone),
        ];
        let mut t = Intrinsics::core();
        for (name, fast) in FAST {
            let mut full = String::from("mox.");
            full.push_str(name);
            t = t.with_fast(&full, fast, "mox", name);
        }
        for (name, op) in CLASS {
            let mut full = String::from("mox.");
            full.push_str(name);
            t = t.with_class(&full, op, "mox", name);
        }
        t.with_host("mox.cast_object", Arity::exact(1), "mox", "cast_object")
    }

    /// Registers `name` as the LSB sequence `op` (its arity is the op's),
    /// replacing any earlier entry of that name.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{Intrinsics, LsbOp};
    ///
    /// assert!(Intrinsics::new().with_lsb("strlen", LsbOp::Len).get("strlen").is_some());
    /// ```
    #[must_use]
    pub fn with_lsb(mut self, name: &str, op: LsbOp) -> Self {
        let def = IntrinsicDef {
            arity: op.arity(),
            lowering: Lowering::Lsb(op),
        };
        let _previous = self.table.insert(String::from(name), def);
        self
    }

    /// Registers `name` as a call to the host function `module`.`func`
    /// taking `arity` operands, replacing any earlier entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{Arity, Intrinsics};
    ///
    /// let t = Intrinsics::new().with_host("php.clone", Arity::exact(1), "php", "clone");
    /// assert_eq!(t.get("php.clone").unwrap().lowering().host(), Some(("php", "clone")));
    /// ```
    #[must_use]
    pub fn with_host(mut self, name: &str, arity: Arity, module: &str, func: &str) -> Self {
        let def = IntrinsicDef {
            arity,
            lowering: Lowering::Host {
                module: String::from(module),
                name: String::from(func),
            },
        };
        let _previous = self.table.insert(String::from(name), def);
        self
    }

    /// Registers `name` as the guarded fast path `fast` (its arity is the
    /// fast path's) over the host function `module`.`func`, replacing any
    /// earlier entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{Fast, Intrinsics};
    ///
    /// let t = Intrinsics::new().with_fast("cmp", Fast::IntSpaceship, "rt", "cmp");
    /// assert_eq!(t.len(), 1);
    /// ```
    #[must_use]
    pub fn with_fast(mut self, name: &str, fast: Fast, module: &str, func: &str) -> Self {
        let def = IntrinsicDef {
            arity: fast.arity(),
            lowering: Lowering::Fast {
                fast,
                module: String::from(module),
                name: String::from(func),
            },
        };
        let _previous = self.table.insert(String::from(name), def);
        self
    }

    /// Registers `name` as the class operation `op` (its arity is the
    /// operation's) over the host function `module`.`func`, replacing any
    /// earlier entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{ClassOp, Intrinsics, Lowering};
    ///
    /// let t = Intrinsics::new().with_class("rt.new", ClassOp::New, "rt", "new");
    /// assert!(matches!(t.get("rt.new").unwrap().lowering(), Lowering::Class { op: ClassOp::New, .. }));
    /// ```
    #[must_use]
    pub fn with_class(mut self, name: &str, op: ClassOp, module: &str, func: &str) -> Self {
        let def = IntrinsicDef {
            arity: op.arity(),
            lowering: Lowering::Class {
                op,
                module: String::from(module),
                name: String::from(func),
            },
        };
        let _previous = self.table.insert(String::from(name), def);
        self
    }

    /// The entry for `name`.
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(bcgen_lang::Intrinsics::core().get("mox.concat").is_none());
    /// ```
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&IntrinsicDef> {
        self.table.get(name)
    }

    /// The number of entries.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Intrinsics::mox().len(), 43);
    /// ```
    #[must_use]
    pub fn len(&self) -> usize {
        self.table.len()
    }

    /// Whether the table is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(!bcgen_lang::Intrinsics::core().is_empty());
    /// ```
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }

    /// Every entry, in name order.
    ///
    /// # Examples
    ///
    /// ```
    /// let core = bcgen_lang::Intrinsics::core();
    /// let names: Vec<&str> = core.iter().map(|(n, _)| n).collect();
    /// assert_eq!(names[0], "concat");
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = (&str, &IntrinsicDef)> {
        self.table.iter().map(|(n, d)| (n.as_str(), d))
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use super::{Arity, Fast, Intrinsics, Lowering};

    #[test]
    fn the_mox_preset_covers_every_sketch_intrinsic() {
        let t = Intrinsics::mox();
        for name in [
            "concat",
            "concat_n",
            "mod",
            "pow",
            "shl",
            "shr",
            "xor",
            "loose_eq",
            "loose_ne",
            "identical",
            "not_identical",
            "spaceship",
            "lt",
            "le",
            "gt",
            "ge",
            "to_number",
            "bit_not",
            "instanceof",
            "cast_int",
            "cast_float",
            "cast_string",
            "cast_bool",
            "cast_array",
            "cast_object",
            "clone",
            "new",
            "str_offset",
        ] {
            let full = alloc::format!("mox.{name}");
            let def = t.get(&full).unwrap_or_else(|| panic!("{full} missing"));
            assert_eq!(def.lowering().host(), Some(("mox", name)));
        }
    }

    #[test]
    fn later_entries_replace_earlier_ones() {
        let t = Intrinsics::new()
            .with_host("x", Arity::exact(1), "a", "b")
            .with_fast("x", Fast::Concat, "c", "d");
        assert_eq!(t.len(), 1);
        assert!(matches!(
            t.get("x").map(super::IntrinsicDef::lowering),
            Some(Lowering::Fast { .. })
        ));
        assert_eq!(
            t.get("x").map(super::IntrinsicDef::arity),
            Some(Arity::exact(2))
        );
    }

    #[test]
    fn arity_display_and_bounds() {
        assert_eq!(Arity::exact(2).to_string(), "2");
        assert_eq!(Arity::range(0, 3).to_string(), "0 to 3");
        assert!(Arity::at_least(0).accepts(0));
        assert!(!Arity::at_least(0).accepts(256));
    }
}
