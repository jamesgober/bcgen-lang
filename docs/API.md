# bcgen-lang &mdash; API Reference

> Complete reference for every public item in `bcgen-lang`, with examples, and
> the dynamic semantics the compiled code implements.
> **Status: 0.2.0, pre-1.0.** The surface may change across the 0.x series; it
> freezes at 1.0 after the LexerSketch Demo runs Mox through it. See
> [`../dev/ROADMAP.md`](../dev/ROADMAP.md).

<sub>Copyright &copy; 2026 <strong>James Gober</strong>.</sub>

## Table of contents

- [Overview](#overview)
- [Installation](#installation)
- [Quick start](#quick-start)
- [Concepts](#concepts)
  - [What the compiler accepts](#what-the-compiler-accepts)
  - [The module it produces](#the-module-it-produces)
  - [The calling convention](#the-calling-convention)
  - [Argument binding](#argument-binding)
  - [Variables, cells, and closures](#variables-cells-and-closures)
  - [Values and operations](#values-and-operations)
  - [Arrays and maps](#arrays-and-maps)
  - [Places and assignment](#places-and-assignment)
  - [Control flow and `match`](#control-flow-and-match)
  - [Exceptions, `finally`, and `defer`](#exceptions-finally-and-defer)
  - [Named intrinsics](#named-intrinsics)
  - [Error locations and debug information](#error-locations-and-debug-information)
  - [Budgets and hostile input](#budgets-and-hostile-input)
- [`compile`](#compile)
- [`Compiler`](#compiler)
- [`Options`](#options)
- [`ArraySemantics`](#arraysemantics)
- [`KeyCoercion`](#keycoercion)
- [`BodyMode`](#bodymode)
- [`Compiled`](#compiled)
- [`Locate`](#locate)
- [`Location`](#location)
- [`LineIndex`](#lineindex)
- [`CompileError`](#compileerror)
- [`Unsupported`](#unsupported)
- [Feature flags](#feature-flags)
- [Stability](#stability)

## Overview

`bcgen-lang` compiles a resolved HIR unit (`hir_lang::Hir`, HIR spec v2) to an
LSB module (`bytecode_lang::Module`, format version 1) that `bvm-lang` loads
and runs. Version 0.2 compiles the **dynamic profile**: every value is an LSB
`dyn`. It is the bridge LexerSketch decision D19 calls for: HIR to LSB
directly, keeping the structure (closures, maps, dynamic values, exceptions)
that both representations have first-class.

## Installation

```toml
[dependencies]
bcgen-lang = "0.2"
```

## Quick start

```rust
use bvm_lang::{Host, Program, Value, Vm};
use hir_lang::{Builder, Name, OpKind};
use intern_lang::Interner;

// fn double(n) { n * 2 }
let mut names = Interner::new();
let mut b = Builder::new();
let (p, n) = b.local_param(Name::new(names.intern("n")));
let un = b.use_binder(n);
let two = b.int(2);
let product = b.op(OpKind::Mul, &[un, two]);
let body = b.block(&[], Some(product));
let double = b.func(Name::new(names.intern("double")), &[p], body);
let root = b.module(None, &[double]);
let hir = b.finish(root)?;

let out = bcgen_lang::compile(&hir, &names)?;
let program = Program::load(out.into_module(), &Host::new())?;
let mut vm = Vm::new(&program);
assert_eq!(vm.run_export("double", &[Value::Int(21)])?, Value::Int(42));
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Concepts

### What the compiler accepts

A unit hir-lang validated (strict or lenient), with its paths resolved
(resolve-lang). The compiler runs on resolved HIR: an unresolved path, or one
resolved to `Res::Err`, is [`CompileError::Unresolved`](#compileerror); an
error node from lenient lowering is `CompileError::ErrorNode`.

Compiled in 0.2: function items (with or without a body), globals, constants,
nested modules, the module body; every expression form except those below;
`let` (with any supported pattern, and let-else), expression statements,
`static`, `global`, `defer`.

Not compiled in 0.2, each a precise [`Unsupported`](#unsupported) error:
coroutines (`yield`, `await`, `spawn`, `ASYNC`/`YIELD` functions; 0.5),
classes, impls, and mixins (0.5), declared records, sums, and constructor
patterns (0.5), references (`*e`, `&e`, `ref` patterns), variable variables,
atomics and other non-named intrinsics, inline assembly, big-integer
literals, definitions of another unit, type-directed paths, a host function
used as a value, and a few conversions and casts with no dynamic meaning.

### The module it produces

| Function | When | Signature |
|---|---|---|
| One per function item with a body (its name) | always | `(dyn, ..., [i64 mask]) -> dyn`; root-level ones are exported by name |
| `<name>$dyn`, its dynamic entry | when the item is used as a value or called with spreads or mismatched arguments | `(dyn, dyn) -> dyn` |
| `<closure#N>`, one per closure expression | always | `(dyn, dyn) -> dyn`, with captures |
| `<start>`, the module's start function | when there are computed initializers, defaults evaluated once, nested module bodies, or (in `BodyMode::Start`) a body | `() -> ()` |
| `<entry>`, exported as `<entry>` | always | `() -> dyn`: the module body's value |
| `<php_key>` | when PHP key coercion is used | `(dyn) -> dyn` |

Globals: one per global and constant item (literal initializers become LSB
constant initializers; others are computed by `<start>` in canonical order),
one per `static` statement (plus an initialized flag), one per
once-evaluated default, and `<result>` for the body's value in
`BodyMode::Start`. Imports: one per host symbol and argument count, `(dyn ×
n) -> dyn`, module and name split at the symbol's last `.` (`mox.concat` is
`mox`.`concat`; `echo` is [`Options::host_module`](#options)`.echo`); a
bodyless function item imports as its `abi` (or the host module) and name.
Hooks: those [`Options::with_hook`](#options) binds.

### The calling convention

A call of a **known function item** (the callee is a path to it) arranges
the arguments at compile time and uses LSB's direct `call` with a window
(LSB §1.3): each parameter in a register (`dyn`, or a cell for a by-reference
parameter) and, when any parameter has a default, an `i64` **presence mask**
(bit `i` set when argument `i` was supplied). The callee evaluates the
defaults of absent parameters.

Every **function value** (a closure, or an item used as a value) takes one
convention: an **argument packet** `(positional: map, named: map or nil)`.
A dynamic call builds the packet and uses `dcall`, whose arity LSB checks
exactly; the callee's prologue unpacks it (see
[Argument binding](#argument-binding)). So a function value can be called
with any arguments, as dynamic languages require. A `dcall` of something
that is not a function reaches LSB's `call` hook with the arguments array
`[positional, named]`.

A call of a known function with spreads, or whose arguments do not fit its
parameters, goes through the packet to the item's dynamic entry, so the
error is raised by the same prologue. A call of a host function
(`Res::Extern`, or a bodyless item) uses `call_import` with the arguments
positionally; spread or named arguments to it are `Unsupported::ExternArgs`.

Method calls (`receiver.method(args)`) look the method up with `get_prop`
and call it with the receiver as the first positional argument (LSB's struct
method convention); `receiver->$name(args)` looks it up with `dget_index`.

### Argument binding

The same rules at compile time and in the packet prologue:

1. Positional arguments fill the positional-only and normal parameters in
   order; extra ones go to the rest parameter, or are a `TypeError`.
2. A named argument fills the normal or named-only parameter of that name
   (a positional-only parameter cannot be named); a parameter filled twice
   is a `TypeError`; an unknown name goes to the named-rest parameter, or is a
   `TypeError`.
3. A required parameter (no default, not a rest) left empty is a `TypeError`.
4. Rest parameters receive arrays (maps); the named rest receives a map from
   names to values.
5. Defaults: per call (`DefaultEval::PerCall`), evaluated in the callee in
   parameter order, seeing the earlier parameters; once
   (`DefaultEval::Once`), evaluated by `<start>` for function items and at
   creation for closures.
6. A parameter whose pattern does not match its value is a `TypeError` at the
   parameter.

Binding errors are raised at the **callee's definition** (the function item
or closure node), whichever path the call took.

A **place argument** (`Arg::place`) naming a variable that lives in a cell is
passed as that cell: a by-reference parameter aliases it, a by-value one
takes its value (a copy). By-reference parameters receive a new cell when the
argument is not a shared variable. A place argument naming an array element
or property is passed by value to a dynamically called function, and is
`Unsupported::RefPlace` when the callee is a known function with a
by-reference parameter there (LSB has no reference to a map slot).

### Variables, cells, and closures

A variable lives in a register, unless it is shared: captured by reference
(an explicit `ByRef`/`ByMutRef` capture, or an implicit capture under
`ByRef`, `ByMutRef`, or `Infer`), aliased by a reference assignment, passed
as a place argument, or a by-reference parameter. A shared variable lives in
a cell, and every binding of it (each `let`, each match) makes a new cell.
Registers are reused once a variable's scope closes.

A closure captures by value (a copy of the value at creation; each call
starts from that copy) or by reference (the cell). A recursive closure's
self binder is a cell that holds the closure. `global $x` makes a variable
that names the global; `static $x = init` names a global initialized the
first time the statement runs. A global or static shared by reference is
stored in a cell (created by `<start>`, or by the statement's first run).

### Values and operations

Values are LSB `dyn` values: `nil`, `bool`, `int` (64-bit), `float`
(binary64), `char`, `str` (bytes), arrays (maps), functions, and error
values. Unit and `()` are `nil`. A block without a tail, a loop without a
break value, and a `match` no arm matched evaluate to `nil`.

Operations are LSB's dynamic instructions with the op instance's OPS
policy in their modifier (`promote` included): `add sub mul div rem floor_div
floor_mod shl shr neg`, the comparisons, and `and or xor not` (logical on two
bools, bitwise otherwise). The rest dispatch on the operands' kinds: two
`int`s use the typed `i64` instruction; numbers with a `float` use the
`f64` one, converting `int` operands (OPS's mixed rule): `min max abs
ieee_rem total_cmp fma sqrt floor ceil trunc round round_even` (the
float-only ones convert `int` operands). `abs(MIN)` follows the overflow
policy (`promote` gives `2^63` as a float). Conversions: `int_cast<T>`,
`float_to_int<T>`, `narrow<T>`, `int_to_float<T>`, `bool_to_int<T>`,
`f64_to_f32`, `f32_to_f64`, `char_from_u32`, and the 64-bit `zext`, `sext`,
and `bitcast`; a result outside the dynamic integer range raises
`ArithOverflow`. A non-number where a number is needed is a `TypeError`
raised by unboxing (no hook intercepts it).

`expr as T`: to `Any` the identity; to `bool` truthiness; to an integer type
from an `int` (`int_cast`), a `float` (`float_to_int`), or a `bool`; to `f64`/
`f32` from a number or a `bool`; to `str` only from a string (formatting is a
runtime-library call); to `char` from a `char` or an `int`; `T?` passes `nil`.

Conditions use LSB truthiness (`dtruthy`, with its hook). Comparisons in a
condition jump on the comparison directly.

### Arrays and maps

Array and tuple literals, map literals, anonymous record literals, and
`[e; n]` (`n` below 1 gives an empty array) are LSB maps (`map dyn -> dyn`),
so arrays are PHP arrays: ordered, with the next integer key. A record field
is a string key; `{..base}` copies `base` (a non-map base is a `TypeError`).

Under [`ArraySemantics::Php`](#arraysemantics) (the default) arrays are
values: storing a value that may be shared (a variable, an element, a
property, or a construct yielding one) into a variable, an element, a
parameter, a capture, or a return copies it if it is an array, with LSB's
O(1) copy-on-write `dup`. Under `ArraySemantics::Reference` copies are the
same array.

Under [`KeyCoercion::Php`](#keycoercion) (the default) index keys and map
literal keys are normalized as PHP does; property names are not.

### Places and assignment

`target = value` and `target op= value` evaluate, in order: the target's
sub-expressions (its root if it is not a variable, then each key), then (for
a compound) the current value, then `value`, then the operation, then the
write. A variable root is read and written when used, after `value` (a
reference assignment inside `value` may rebind it). The assignment's value is
the value written.

A write through a chain (`a[k1][k2] = v`, properties, `a[] = v`) walks from
the root. Under PHP semantics a `nil` root or intermediate becomes a new
array, stored back (auto-vivification), and each intermediate array is
separated (copied) and stored back before it is written, so a copy that
shared it is unaffected. A non-array container uses the dynamic instructions
and their hooks (`dget_index`/`dset_index`, `get_prop`/`set_prop`). `a[]` on a
non-array is a `TypeError`.

`t = &s` makes the variable `t` name `s`'s cell (both must be variables; a
`global` alias or `static` as the target, or an element, is
`Unsupported::RefPlace`).

### Control flow and `match`

`if`, blocks, labeled blocks with `break 'label value`, and the loop
primitive (`continue` runs the step; every iteration passes a `safepoint`).
`return` leaves the function (or closure, or the module body).

`match` is a sequential decision procedure: each arm's pattern, then its
guard, in order. Patterns: wildcard, binding (by value), `x @ p`,
identifiers (a constant's value, else a binding), literals and constant
paths (`deq`, the language's equality with its hook), ranges (the value and
bounds of one class, numbers or chars, then ordered comparison; NaN is in no
range), tuples and slices (an array, by integer keys `0..n` and `len-m..len`,
with the rest bound to a new array), anonymous records (a map, by string
keys; without `..` the length must match), or-patterns, and type tests by
dynamic kind (`int` types, `f32`/`f64`, `bool`, `char`, `str`, tuples/arrays/
slices as arrays, `Any`, `T?`). `let p = e` with a refutable pattern runs
`else` on no match, or raises a `TypeError` at the statement.

### Exceptions, `finally`, and `defer`

`throw e` raises `e` (a caught runtime error value rethrown keeps its
original location). `try` is LSB §4.3's canonical lowering: a catch region
over the body, its arms tried in order (none matching rethrows from the
`try`), and for a `finally` a second region over the body and the arms, with
a completion kind (`i8`) and value (`dyn`) per `try` and one copy of the
`finally` body ending in a dispatch: normal, return, rethrow (from the
`try`), or the `n`th `break`/`continue` target. A jump out of the `finally`
body overrides the pending completion; an error inside it replaces it.
`defer e` makes the rest of the block a `try` whose `finally` is `e`.

### Named intrinsics

`Intrinsic::Named` with these names (other names are
`Unsupported::Intrinsic`; a wrong operand count is
`CompileError::IntrinsicArity`):

| Name | Operands | Result |
|---|---|---|
| `concat` | 2 | `dconcat` (two strings, else the `concat` hook) |
| `len` | 1 | `dlen` as an `int` |
| `truthy`, `lnot` | 1 | truthiness and its negation as a `bool` |
| `type_of` | 1 | the LSB kind code as an `int` |
| `iter` | 1 | an iterator (`diter_new`), over a copy under PHP semantics |
| `iter_next` | 1 | `nil` when done, else the pair `[key, value]` |

`iter` and `iter_next` are what a `foreach` lowering (HIR spec §9.4) needs.

### Error locations and debug information

Every instruction records the HIR node it was compiled from
([`Compiled::origin`](#compiled)), so a runtime error's `(function, pc)`
maps to a node: an operation's error to the operation, a call's to the call,
a binding error to the callee's definition, an unmatched `let` to the
statement, a rethrow to the `try`. Line-table rows come from a
[`Locate`](#locate), or carry byte offsets without one. Each variable's
register and live range is in the debug locals table.

### Budgets and hostile input

Generation never recurses over the input: an explicit task stack handles any
nesting depth. The module's size is bounded by
[`Options::with_max_instructions`](#options); a function's by LSB's 65,536
registers (a `CompileError::Build` beyond). Functions have at most 64
parameters (the presence mask). A `finally` can be left by at most 124
distinct jump targets (the `i8` completion kind).

## `compile`

```rust,ignore
pub fn compile<L: Lookup>(hir: &Hir, names: &L) -> Result<Compiled, CompileError>
```

Compiles a resolved unit with the default [`Options`](#options). `names` is
the interner the unit's names were interned in (any `intern_lang::Lookup`).

**Errors.** The first [`CompileError`](#compileerror) in the unit.

```rust
use hir_lang::Builder;
use intern_lang::Interner;

let mut b = Builder::new();
let root = b.module(None, &[]);
let hir = b.finish(root)?;
let out = bcgen_lang::compile(&hir, &Interner::new())?;
assert_eq!(out.module().functions().len(), 1); // the entry function
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Compiler`

```rust,ignore
pub struct Compiler<'a> { /* private */ }
impl Compiler<'static> { pub fn new(options: Options) -> Self }
impl<'a> Compiler<'a> {
    pub fn with_locator<'b>(self, locator: &'b dyn Locate) -> Compiler<'b>;
    pub fn options(&self) -> &Options;
    pub fn compile<L: Lookup>(&self, hir: &Hir, names: &L) -> Result<Compiled, CompileError>;
}
```

Options plus an optional [`Locate`](#locate) for the line tables.

```rust
use bcgen_lang::{BodyMode, Compiler, LineIndex, Options};
use hir_lang::Builder;
use intern_lang::Interner;

let lines = LineIndex::new("main.mox", 0, "");
let mut b = Builder::new();
let root = b.module(None, &[]);
let hir = b.finish(root)?;
let c = Compiler::new(Options::new().with_body(BodyMode::Entry)).with_locator(&lines);
assert_eq!(c.options().body(), BodyMode::Entry);
let out = c.compile(&hir, &Interner::new())?;
assert!(out.start().is_none());
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Options`

```rust,ignore
pub struct Options { /* private */ }
impl Options {
    pub const DEFAULT_MAX_INSTRUCTIONS: u64; // 64 Mi
    pub fn new() -> Self;                    // the PHP profile
    pub fn with_arrays(self, ArraySemantics) -> Self;
    pub fn with_keys(self, KeyCoercion) -> Self;
    pub fn with_body(self, BodyMode) -> Self;
    pub fn with_file(self, &str) -> Self;          // line-table file without a locator
    pub fn with_host_module(self, &str) -> Self;   // import module for dot-less symbols
    pub fn with_hook(self, Hook, module: &str, name: &str) -> Self;
    pub fn with_max_instructions(self, u64) -> Self;
    pub fn arrays(&self) -> ArraySemantics;
    pub fn keys(&self) -> KeyCoercion;
    pub fn body(&self) -> BodyMode;
    pub fn file(&self) -> &str;
    pub fn host_module(&self) -> &str;
    pub fn hooks(&self) -> &[(Hook, String, String)];
    pub fn max_instructions(&self) -> u64;
}
```

`with_hook` binds an LSB hook (LSB §5.8) to a host function with the hook's
signature; a language supplies its own semantics this way (PHP's loose `==`,
`get_index` returning `null` for a missing key, ...). With hooks bound, the
compiler copies arrays more conservatively (a hook may return an operand).

```rust
use bcgen_lang::{ArraySemantics, KeyCoercion, Options};
use bytecode_lang::Hook;

let o = Options::new()
    .with_arrays(ArraySemantics::Reference)
    .with_keys(KeyCoercion::None)
    .with_host_module("env")
    .with_hook(Hook::Eq, "mox", "loose_eq")
    .with_max_instructions(1 << 20);
assert_eq!(o.hooks().len(), 1);
assert_eq!(o.max_instructions(), 1 << 20);
```

## `ArraySemantics`

```rust,ignore
pub enum ArraySemantics { Php, Reference }   // default Php
```

`Php`: arrays are values (see [Arrays and maps](#arrays-and-maps)), writes
create missing arrays. `Reference`: arrays are shared, as in Python and
JavaScript, and writing into `nil` is an error.

```rust
assert_eq!(bcgen_lang::ArraySemantics::default(), bcgen_lang::ArraySemantics::Php);
```

## `KeyCoercion`

```rust,ignore
pub enum KeyCoercion { Php, None }   // default Php
```

`Php`: a string holding a canonical decimal `i64` (`"7"`, `"-3"`; not
`"07"`, `"-0"`, `"+1"`, `" 1"`, or out of range) becomes that integer; a
float is truncated toward zero, saturating at the `i64` range, NaN giving 0;
`true`/`false` become 1/0; `null` becomes `""`; other keys are unchanged.
`None`: keys compare by LSB's rules.

```rust
assert_eq!(bcgen_lang::KeyCoercion::default(), bcgen_lang::KeyCoercion::Php);
```

## `BodyMode`

```rust,ignore
pub enum BodyMode { Start, Entry }   // default Start
```

`Start`: the module body runs in the start function, once, before the first
call into the module; `<entry>` returns its value. `Entry`: `<entry>` is the
body and runs it on every call (REPL entries).

```rust
assert_eq!(bcgen_lang::BodyMode::default(), bcgen_lang::BodyMode::Start);
```

## `Compiled`

```rust,ignore
pub struct Compiled { /* private */ }
impl Compiled {
    pub fn module(&self) -> &Module;
    pub fn into_module(self) -> Module;
    pub fn entry(&self) -> FuncId;               // () -> dyn, exported as `<entry>`
    pub fn start(&self) -> Option<FuncId>;
    pub fn result_global(&self) -> Option<GlobalId>;
    pub fn function(&self, item: ItemId) -> Option<FuncId>;
    pub fn origin(&self, func: FuncId, pc: u32) -> Option<NodeRef>;
    pub fn origins(&self, func: FuncId) -> &[NodeRef];
}
```

The module, its entry points, the direct-call function of each function
item, and the HIR node of every instruction.

```rust
use bvm_lang::{Host, Program, Vm};
use hir_lang::{Builder, OpKind};
use intern_lang::Interner;

// A module body that divides by zero.
let mut b = Builder::new();
let one = b.int(1);
let zero = b.int(0);
let div = b.op(OpKind::Div, &[one, zero]);
let module = hir_lang::ItemKind::Module { items: hir_lang::List::EMPTY, body: Some(div), effects: hir_lang::Effects::NONE };
let root = b.item(hir_lang::Item::new(None, module));
let hir = b.finish(root)?;
let out = bcgen_lang::compile(&hir, &Interner::new())?;

let program = Program::load(out.module().clone(), &Host::new())?;
let err = Vm::new(&program).run(out.entry(), &[]).unwrap_err();
let (func, pc) = err.location().unwrap();
assert_eq!(out.origin(func, pc), Some(hir_lang::NodeRef::Expr(div)));
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Locate`

```rust,ignore
pub trait Locate { fn locate(&self, span: Span) -> Location<'_>; }
```

Maps HIR spans (session-wide byte ranges) to line-table positions. Without
one, rows carry [`Options::file`](#options), line 0, and the span's start
offset as the column.

```rust
use bcgen_lang::{Locate, Location};
use hir_lang::Span;

struct Offsets;
impl Locate for Offsets {
    fn locate(&self, span: Span) -> Location<'_> {
        Location { file: "x", line: 1, column: span.start().to_u32() + 1 }
    }
}
assert_eq!(Offsets.locate(Span::new(4, 5)).column, 5);
```

## `Location`

```rust,ignore
pub struct Location<'a> { pub file: &'a str, pub line: u32, pub column: u32 }
```

A line-table position.

```rust
let at = bcgen_lang::Location { file: "a.mox", line: 3, column: 7 };
assert_eq!((at.line, at.column), (3, 7));
```

## `LineIndex`

```rust,ignore
pub struct LineIndex { /* private */ }
impl LineIndex {
    pub fn new(file: &str, base: u32, text: &str) -> Self;
    pub fn lines(&self) -> usize;
}
impl Locate for LineIndex { /* 1-based lines, 1-based byte columns */ }
```

A [`Locate`](#locate) for one source file whose first byte is at `base` in
the session byte space. Offsets past the end land on the last line.

```rust
use bcgen_lang::{LineIndex, Locate};
use hir_lang::Span;

let lines = LineIndex::new("app.mox", 100, "a = 1;\nb = 2;\n");
assert_eq!(lines.lines(), 3);
let at = lines.locate(Span::new(107, 108));
assert_eq!((at.file, at.line, at.column), ("app.mox", 2, 1));
```

## `CompileError`

```rust,ignore
#[non_exhaustive]
pub enum CompileError {
    Unsupported { feature: Unsupported, node: NodeRef, span: Span },
    Unresolved { node: NodeRef, span: Span },
    ErrorNode { node: NodeRef, span: Span },
    LiteralOutOfRange { node: NodeRef, span: Span },
    NotAssignable { node: NodeRef, span: Span },
    IntrinsicArity { node: NodeRef, span: Span, expected: u32 },
    TooManyParams { node: NodeRef, span: Span, limit: u32 },
    TooManyJumps { node: NodeRef, span: Span },
    BudgetExceeded { limit: u64 },
    Build(BuildError),
}
impl CompileError {
    pub fn node(&self) -> Option<NodeRef>;
    pub fn span(&self) -> Option<Span>;
}
```

Why a unit did not compile. `LiteralOutOfRange` is an integer literal outside
`i64` (the dynamic integer range); `NotAssignable` an assignment to a
function, a constant, or a non-place; `Build` an LSB format limit
(`bytecode_lang::BuildError`). `Display` names the problem and its span.

```rust
use bcgen_lang::{CompileError, Options, Compiler};
use hir_lang::{Builder, OpKind};
use intern_lang::Interner;

let mut b = Builder::new();
let mut e = b.int(0);
for _ in 0..100 {
    let one = b.int(1);
    e = b.op(OpKind::Add, &[e, one]);
}
let module = hir_lang::ItemKind::Module { items: hir_lang::List::EMPTY, body: Some(e), effects: hir_lang::Effects::NONE };
let root = b.item(hir_lang::Item::new(None, module));
let hir = b.finish(root)?;
let err = Compiler::new(Options::new().with_max_instructions(10)).compile(&hir, &Interner::new()).unwrap_err();
assert_eq!(err, CompileError::BudgetExceeded { limit: 10 });
assert_eq!(err.node(), None);
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Unsupported`

```rust,ignore
#[non_exhaustive]
pub enum Unsupported {
    Coroutine, Class, Record, Reference, RefPlace, VarVar, Intrinsic, Asm,
    BigInt, ForeignUnit, TypeDirected, ExternValue, ExternArgs, Conversion,
    Cast, Pattern,
}
impl Unsupported { pub const fn describe(self) -> &'static str; }
```

A form 0.2 does not compile, and where it is planned (`describe`, also
`Display`). `Reference`, `RefPlace`, `VarVar`, `ExternValue`, and
`ExternArgs` need LSB features that do not exist (references into map slots,
named frames, variadic imports); the rest arrive with later bcgen-lang
releases or other backends.

```rust
use bcgen_lang::Unsupported;

assert!(Unsupported::Coroutine.describe().contains("0.5"));
assert_eq!(Unsupported::Asm.to_string(), "inline assembly (native backends only)");
```

## Feature flags

| Feature | Default | Effect |
|---|---|---|
| `std` | yes | Forwards `std` to the family crates. Without it the crate is `no_std` + `alloc`. |

## Stability

0.2.0 is a pre-release surface: names and signatures may change across 0.x,
each change recorded in the CHANGELOG. The compiled code's semantics are the
ones this file states, checked by the differential tests; changes to them
are breaking and recorded.
