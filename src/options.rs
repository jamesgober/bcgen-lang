//! Compilation options and source locations.

use alloc::string::String;
use alloc::vec::Vec;

use bytecode_lang::Hook;
use hir_lang::Span;

use crate::intrinsics::Intrinsics;

/// How arrays and maps behave when a value is copied.
///
/// # Examples
///
/// ```
/// use bcgen_lang::ArraySemantics;
///
/// assert_eq!(ArraySemantics::default(), ArraySemantics::Php);
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum ArraySemantics {
    /// PHP arrays: values. Assigning, passing, returning, capturing, or
    /// storing an array copies it (an O(1) copy-on-write `dup`), a nested
    /// write (`$a['x']['y'] = 1`) separates each intermediate array from any
    /// copy that shares it, and writing through `null` creates the array
    /// (auto-vivification).
    #[default]
    Php,
    /// Shared references, as in Python, JavaScript, and Ruby: a copy is the
    /// same object, nested writes go through, and writing into `null` is an
    /// error.
    Reference,
}

/// How map keys are normalized before a map is indexed.
///
/// # Examples
///
/// ```
/// use bcgen_lang::KeyCoercion;
///
/// assert_eq!(KeyCoercion::default(), KeyCoercion::Php);
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum KeyCoercion {
    /// PHP's array-key rules: a string holding a canonical decimal `i64`
    /// (`"7"`, `"-3"`, not `"07"`, `"-0"`, or `"+1"`) becomes that integer, a
    /// float is truncated toward zero (saturating at the `i64` range; NaN
    /// gives `0`), `true`/`false` become `1`/`0`, and `null` becomes `""`.
    /// Other keys are left as they are.
    #[default]
    Php,
    /// No normalization: keys compare by LSB's rules (`1` and `1.0` differ).
    None,
}

/// What the module body (`Module.body`) compiles to.
///
/// # Examples
///
/// ```
/// use bcgen_lang::BodyMode;
///
/// assert_eq!(BodyMode::default(), BodyMode::Start);
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum BodyMode {
    /// The body is part of the module's start function, which the VM runs
    /// once before the first call into the module; its value is kept in a
    /// global that the entry function returns. Scripts and modules.
    #[default]
    Start,
    /// The body is the entry function itself and returns its value on every
    /// call; the start function only initializes globals. REPL entries and
    /// tests that run the body more than once.
    Entry,
}

/// Compilation options: the dynamic profile's array and key semantics, the
/// body's role, host linkage, the intrinsic table, and budgets.
///
/// The default is the PHP profile Mox needs: value arrays and PHP keys.
///
/// # Examples
///
/// ```
/// use bcgen_lang::{ArraySemantics, Options};
///
/// let opts = Options::new()
///     .with_arrays(ArraySemantics::Reference)
///     .with_file("app.mox")
///     .with_max_instructions(1_000_000);
/// assert_eq!(opts.arrays(), ArraySemantics::Reference);
/// assert_eq!(opts.file(), "app.mox");
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Options {
    arrays: ArraySemantics,
    keys: KeyCoercion,
    body: BodyMode,
    file: String,
    host_module: String,
    hooks: Vec<(Hook, String, String)>,
    intrinsics: Intrinsics,
    max_instructions: u64,
}

impl Default for Options {
    fn default() -> Self {
        Self::new()
    }
}

impl Options {
    /// The default budget: 64 Mi instructions per module.
    pub const DEFAULT_MAX_INSTRUCTIONS: u64 = 64 << 20;

    /// The PHP profile: [`ArraySemantics::Php`], [`KeyCoercion::Php`],
    /// [`BodyMode::Start`], file name `<hir>`, host module `host`, no hooks,
    /// and the built-in intrinsics ([`Intrinsics::core`]).
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{BodyMode, Options};
    ///
    /// assert_eq!(Options::new().body(), BodyMode::Start);
    /// assert_eq!(Options::new().host_module(), "host");
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self {
            arrays: ArraySemantics::Php,
            keys: KeyCoercion::Php,
            body: BodyMode::Start,
            file: String::from("<hir>"),
            host_module: String::from("host"),
            hooks: Vec::new(),
            intrinsics: Intrinsics::core(),
            max_instructions: Self::DEFAULT_MAX_INSTRUCTIONS,
        }
    }

    /// Sets the array semantics.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{ArraySemantics, Options};
    ///
    /// let o = Options::new().with_arrays(ArraySemantics::Reference);
    /// assert_eq!(o.arrays(), ArraySemantics::Reference);
    /// ```
    #[must_use]
    pub fn with_arrays(mut self, arrays: ArraySemantics) -> Self {
        self.arrays = arrays;
        self
    }

    /// Sets the key coercion.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{KeyCoercion, Options};
    ///
    /// assert_eq!(Options::new().with_keys(KeyCoercion::None).keys(), KeyCoercion::None);
    /// ```
    #[must_use]
    pub fn with_keys(mut self, keys: KeyCoercion) -> Self {
        self.keys = keys;
        self
    }

    /// Sets what the module body compiles to.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{BodyMode, Options};
    ///
    /// assert_eq!(Options::new().with_body(BodyMode::Entry).body(), BodyMode::Entry);
    /// ```
    #[must_use]
    pub fn with_body(mut self, body: BodyMode) -> Self {
        self.body = body;
        self
    }

    /// Sets the file name written into line-table rows when no
    /// [`Locate`] is given.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::Options;
    ///
    /// assert_eq!(Options::new().with_file("main.mox").file(), "main.mox");
    /// ```
    #[must_use]
    pub fn with_file(mut self, file: &str) -> Self {
        self.file = String::from(file);
        self
    }

    /// Sets the import module for host symbols that have no `.` in their
    /// name (`echo` imports as `host`.`echo` by default; `mox.concat` imports
    /// as `mox`.`concat` whatever this is).
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::Options;
    ///
    /// assert_eq!(Options::new().with_host_module("env").host_module(), "env");
    /// ```
    #[must_use]
    pub fn with_host_module(mut self, module: &str) -> Self {
        self.host_module = String::from(module);
        self
    }

    /// Binds an LSB hook (§5.8) to the host function `module`.`name`, with
    /// the hook's signature (every operand `dyn`). A later binding of the same
    /// hook replaces an earlier one.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::Options;
    /// use bytecode_lang::Hook;
    ///
    /// let o = Options::new().with_hook(Hook::Eq, "mox", "loose_eq");
    /// assert_eq!(o.hooks().len(), 1);
    /// ```
    #[must_use]
    pub fn with_hook(mut self, hook: Hook, module: &str, name: &str) -> Self {
        self.hooks.retain(|(h, _, _)| *h != hook);
        self.hooks
            .push((hook, String::from(module), String::from(name)));
        self
    }

    /// Sets the intrinsic table: how each named intrinsic compiles (an LSB
    /// sequence, a host function, or a guarded fast path over one). Names
    /// not in it do not compile
    /// ([`CompileError::UnknownIntrinsic`](crate::CompileError::UnknownIntrinsic)).
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::{Intrinsics, Options};
    ///
    /// let o = Options::new().with_intrinsics(Intrinsics::mox());
    /// assert!(o.intrinsics().get("mox.loose_eq").is_some());
    /// ```
    #[must_use]
    pub fn with_intrinsics(mut self, intrinsics: Intrinsics) -> Self {
        self.intrinsics = intrinsics;
        self
    }

    /// Sets the instruction budget for the whole module; compilation stops
    /// with [`CompileError::BudgetExceeded`](crate::CompileError) beyond it.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::Options;
    ///
    /// assert_eq!(Options::new().with_max_instructions(10).max_instructions(), 10);
    /// ```
    #[must_use]
    pub fn with_max_instructions(mut self, limit: u64) -> Self {
        self.max_instructions = limit;
        self
    }

    /// The array semantics.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Options::new().arrays(), bcgen_lang::ArraySemantics::Php);
    /// ```
    #[must_use]
    pub fn arrays(&self) -> ArraySemantics {
        self.arrays
    }

    /// The key coercion.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Options::new().keys(), bcgen_lang::KeyCoercion::Php);
    /// ```
    #[must_use]
    pub fn keys(&self) -> KeyCoercion {
        self.keys
    }

    /// What the module body compiles to.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Options::new().body(), bcgen_lang::BodyMode::Start);
    /// ```
    #[must_use]
    pub fn body(&self) -> BodyMode {
        self.body
    }

    /// The default file name for line-table rows.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Options::new().file(), "<hir>");
    /// ```
    #[must_use]
    pub fn file(&self) -> &str {
        &self.file
    }

    /// The import module for host symbols without a `.`.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Options::new().host_module(), "host");
    /// ```
    #[must_use]
    pub fn host_module(&self) -> &str {
        &self.host_module
    }

    /// The hook bindings, as (hook, module, name).
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(bcgen_lang::Options::new().hooks().is_empty());
    /// ```
    #[must_use]
    pub fn hooks(&self) -> &[(Hook, String, String)] {
        &self.hooks
    }

    /// The intrinsic table.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::Options::new().intrinsics(), &bcgen_lang::Intrinsics::core());
    /// ```
    #[must_use]
    pub fn intrinsics(&self) -> &Intrinsics {
        &self.intrinsics
    }

    /// The instruction budget.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::Options;
    ///
    /// assert_eq!(Options::new().max_instructions(), Options::DEFAULT_MAX_INSTRUCTIONS);
    /// ```
    #[must_use]
    pub fn max_instructions(&self) -> u64 {
        self.max_instructions
    }
}

/// A source position for a line-table row: file, line, and column, numbered
/// as the [`Locate`] implementation numbers them.
///
/// # Examples
///
/// ```
/// use bcgen_lang::Location;
///
/// let at = Location { file: "a.mox", line: 3, column: 7 };
/// assert_eq!(at.line, 3);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Location<'a> {
    /// The file name.
    pub file: &'a str,
    /// The line.
    pub line: u32,
    /// The column.
    pub column: u32,
}

/// Maps HIR spans to source positions for LSB line tables.
///
/// HIR spans are byte ranges in a session-wide byte space; only the host
/// (typically a source-lang `SourceMap`) knows the files behind them. Without
/// a locator, rows carry the [`Options::file`] name, line `0` ("unknown"),
/// and the span's start byte offset as the column. The exact HIR node of
/// every instruction is always available from [`Compiled::origin`].
///
/// [`Compiled::origin`]: crate::Compiled::origin
///
/// # Examples
///
/// ```
/// use bcgen_lang::{Locate, Location};
/// use hir_lang::Span;
///
/// struct OneLine;
/// impl Locate for OneLine {
///     fn locate(&self, span: Span) -> Location<'_> {
///         Location { file: "x", line: 1, column: span.start().to_u32() + 1 }
///     }
/// }
/// assert_eq!(OneLine.locate(Span::new(4, 5)).column, 5);
/// ```
pub trait Locate {
    /// The position of `span`'s start.
    fn locate(&self, span: Span) -> Location<'_>;
}

/// A [`Locate`] for one source file: 1-based lines and byte columns from the
/// file's text, for spans that start at `base` in the session byte space.
///
/// # Examples
///
/// ```
/// use bcgen_lang::{LineIndex, Locate};
/// use hir_lang::Span;
///
/// let lines = LineIndex::new("app.mox", 0, "a = 1;\nb = 2;\n");
/// let at = lines.locate(Span::new(7, 8));
/// assert_eq!((at.file, at.line, at.column), ("app.mox", 2, 1));
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LineIndex {
    file: String,
    base: u32,
    starts: Vec<u32>,
}

impl LineIndex {
    /// Indexes `text`, whose first byte is at offset `base` of the session
    /// byte space.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcgen_lang::LineIndex;
    ///
    /// assert_eq!(LineIndex::new("f", 100, "x\ny").lines(), 2);
    /// ```
    #[must_use]
    pub fn new(file: &str, base: u32, text: &str) -> Self {
        let mut starts = Vec::with_capacity(text.len() / 32 + 1);
        starts.push(0);
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                starts.push(u32::try_from(i + 1).unwrap_or(u32::MAX));
            }
        }
        Self {
            file: String::from(file),
            base,
            starts,
        }
    }

    /// The number of lines.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(bcgen_lang::LineIndex::new("f", 0, "").lines(), 1);
    /// ```
    #[must_use]
    pub fn lines(&self) -> usize {
        self.starts.len()
    }
}

impl Locate for LineIndex {
    fn locate(&self, span: Span) -> Location<'_> {
        let offset = span.start().to_u32().saturating_sub(self.base);
        // The last line start at or before the offset; offsets past the end
        // land on the last line.
        let line = self.starts.partition_point(|&s| s <= offset).max(1);
        let start = self.starts.get(line - 1).copied().unwrap_or(0);
        Location {
            file: &self.file,
            line: u32::try_from(line).unwrap_or(u32::MAX),
            column: offset - start + 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{LineIndex, Locate, Options};
    use hir_lang::Span;

    #[test]
    fn line_index_counts_from_the_base() {
        let l = LineIndex::new("f", 10, "ab\ncd\n\nx");
        let at = |o: u32| {
            let p = l.locate(Span::new(o, o));
            (p.line, p.column)
        };
        assert_eq!(at(10), (1, 1));
        assert_eq!(at(12), (1, 3));
        assert_eq!(at(13), (2, 1));
        assert_eq!(at(16), (3, 1));
        assert_eq!(at(17), (4, 1));
        // Before the base clamps to the start; past the end stays on the last line.
        assert_eq!(at(0), (1, 1));
        assert_eq!(at(1_000), (4, 984));
    }

    #[test]
    fn a_later_hook_binding_replaces_an_earlier_one() {
        let o = Options::new()
            .with_hook(bytecode_lang::Hook::Eq, "a", "b")
            .with_hook(bytecode_lang::Hook::Eq, "c", "d");
        assert_eq!(o.hooks().len(), 1);
        assert_eq!(o.hooks()[0].1, "c");
    }
}
