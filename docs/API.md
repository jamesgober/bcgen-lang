# bcgen-lang &mdash; API Reference

> Complete reference for every public item in `bcgen-lang`, with examples, and
> the dynamic semantics the compiled code implements.
> **Status: 0.3.0, pre-1.0.** The surface may change across the 0.x series; it
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
  - [Variables, references, and closures](#variables-references-and-closures)
  - [Values and operations](#values-and-operations)
  - [Types: casts and type tests](#types-casts-and-type-tests)
  - [Arrays and maps](#arrays-and-maps)
  - [Places, assignment, and `let_place`](#places-assignment-and-let_place)
  - [References (PHP `&`)](#references-php-)
  - [Control flow and `match`](#control-flow-and-match)
  - [Exceptions, `finally`, and `defer`](#exceptions-finally-and-defer)
  - [Generators, `await`, and `spawn`](#generators-await-and-spawn)
  - [Named intrinsics](#named-intrinsics)
  - [The Mox intrinsics](#the-mox-intrinsics)
  - [Error locations and debug information](#error-locations-and-debug-information)
  - [Budgets and hostile input](#budgets-and-hostile-input)
- [`compile`](#compile)
- [`Compiler`](#compiler)
- [`Options`](#options)
- [`ArraySemantics`](#arraysemantics)
- [`KeyCoercion`](#keycoercion)
- [`BodyMode`](#bodymode)
- [`Intrinsics`](#intrinsics)
- [`IntrinsicDef`](#intrinsicdef)
- [`Lowering`](#lowering)
- [`LsbOp`](#lsbop)
- [`Fast`](#fast)
- [`Arity`](#arity)
- [`Compiled`](#compiled)
- [`Locate`](#locate)
- [`Location`](#location)
- [`LineIndex`](#lineindex)
- [`CompileError`](#compileerror)
- [`Unsupported`](#unsupported)
- [Feature flags](#feature-flags)
- [Stability](#stability)

## Overview

`bcgen-lang` compiles a resolved HIR unit (`hir_lang::Hir`, hir-lang 0.4,
HIR spec v3) to an LSB module (`bytecode_lang::Module`, bytecode-lang 0.3,
**LSB format version 2**) that `bvm-lang` 2.0 (`2.0.0-alpha.3`) loads and
runs. It compiles the **dynamic profile**: every value is an LSB `dyn`. It is
the bridge LexerSketch decision D19 calls for: HIR to LSB directly, keeping
the structure (closures, maps, dynamic values, exceptions, coroutines) that
both representations have first-class.

## Installation

```toml
[dependencies]
bcgen-lang = "0.3"
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

A unit hir-lang validated (strict or lenient), with its paths resolved. The
compiler runs on resolved HIR: an unresolved path, or one resolved to
`Res::Err`, is [`CompileError::Unresolved`](#compileerror); an error node from
lenient lowering is `CompileError::ErrorNode`.

Compiled in 0.3: function items (with or without a body; generators and async
functions included), globals, constants, nested modules, the module body;
every expression form except those below, including keyed `yield`, `yield
from`, `await`, `spawn`, `let_place`, reference assignments to and from
elements, and named intrinsics through the [intrinsic table](#intrinsics);
`let` (with any supported pattern, and let-else), expression statements,
`static`, `global`, `defer`.

Not compiled in 0.3, each a precise [`Unsupported`](#unsupported) error:
classes, impls, and mixins, declared records, sums, and constructor patterns
(0.5); pointers (`*e`, `&e` borrows, `ref` patterns); a reference to an
appended element (`$a[] = &$x`) or a variable variable; atomics, volatile
accesses, and fences; inline assembly; big-integer literals; definitions of
another unit; type-directed paths; a host function used as a value or given
spread or named arguments; and a few conversions, casts, and type tests with
no dynamic meaning.

### The module it produces

| Function | When | Signature |
|---|---|---|
| One per function item with a body (its name) | always | `(param, ..., [i64 mask]) -> dyn`, with its LSB parameter list; root-level ones are exported by name. A generator's makes its coroutine. |
| `<name>$gen`, a generator's coroutine body | for each generator function | the same signature |
| `<closure#N>`, one per closure expression | always | `(param, ..., [i64 mask]) -> dyn`, with captures and its parameter list |
| `<closure#N>$gen` | for each generator closure | `(capture, ..., param, ..., [i64 mask]) -> dyn`, no captures |
| `<start>`, the module's start function | when there are computed initializers, defaults evaluated once, nested module bodies, or (in `BodyMode::Start`) a body | `() -> ()` |
| `<entry>`, exported as `<entry>` | always | `() -> dyn`: the module body's value |
| `<php_key>` | when PHP key coercion is used | `(dyn) -> dyn` |

A parameter is `dyn`, or `ref cell dyn` (a reference, LSB §5.17) when it is
by reference. Globals: one per global and constant item (literal
initializers become LSB constant initializers; others are computed by
`<start>` in canonical order), one per `static` statement (plus an
initialized flag), one per once-evaluated default, and `<result>` for the
body's value in `BodyMode::Start`. Imports: one per host symbol and argument
count, `(dyn × n) -> dyn`, module and name split at the symbol's last `.`
(`mox.concat` is `mox`.`concat`; `echo` is
[`Options::host_module`](#options)`.echo`); a bodyless function item imports
as its `abi` (or the host module) and name; one per host function an
[intrinsic](#named-intrinsics) uses, per argument count. Hooks: those
[`Options::with_hook`](#options) binds.

### The calling convention

Every function item and closure compiles to **one** LSB function whose
signature is its parameters and, when any parameter has a default, an `i64`
**presence mask** (bit `i` set when parameter `i` received an argument), and
which carries an **LSB parameter list** (LSB §5.15): each parameter's kind,
name, by-reference flag, and default flag. HIR's parameter kinds map to LSB's
one to one, except `rest`, which is LSB's `rest_map` (PHP 8.1's `...$args`: a
map of the extra positional arguments, and of unknown named ones when there
is no named rest). A `normal` or `named_only` parameter whose pattern binds no
single name (or repeats an earlier name) gets a name no source argument can
spell (it starts with a NUL byte), so it binds by position only.

A call of a **known function item** (the callee is a path to it) arranges the
arguments at compile time, by the same binding rules, and uses LSB's direct
`call` with a window (a generator's: `coro_new` of its body). Every other
call is **dynamic**: of a function value (a closure, an item used as a
value), a method, or a known function given spreads or arguments that do not
bind. It is `dcall` when every argument is positional, else `dcall_shape`
with a call shape (positional, named, spread, named spread, in source order);
the VM binds the arguments through the callee's parameter list and raises
`ArgumentError` (E0114) at the call when they do not bind. A call of
something that is not a function reaches LSB's `call` (or `call_shape`)
hook.

A call of a host function (`Res::Extern`, or a bodyless item) uses
`call_import` with the arguments positionally; spread or named arguments to
it are `Unsupported::ExternArgs`. At most 255 arguments fit a call window
(`CompileError::TooManyArgs`).

Method calls (`receiver.method(args)`) look the method up with `get_prop` and
call it dynamically with the receiver as the first positional argument;
`receiver->$name(args)` looks it up with `dget_index`.

### Argument binding

LSB §5.15's rules, applied at compile time to known callees and by the VM to
everything else, so both paths agree (`tests/binding.rs` checks this on
random parameter and argument lists):

1. A positional argument after a named one is an `ArgumentError`.
2. Positional arguments fill the positional-only and normal parameters in
   order; extra ones go to the rest parameter, or are an `ArgumentError`.
3. A named argument fills the normal or named-only parameter of that name
   (twice is an `ArgumentError`); an unknown name goes to the named rest, else
   to the rest map, else is an `ArgumentError`.
4. A required parameter (no default, not a rest) left empty is an
   `ArgumentError`; an empty rest is an empty map.
5. Defaults: per call (`DefaultEval::PerCall`), evaluated in the callee in
   parameter order, seeing the earlier parameters; once (`DefaultEval::Once`),
   evaluated by `<start>` for function items and at creation for closures.
6. A parameter whose pattern does not match its value is a `TypeError` at the
   parameter.

Binding errors are raised at the **call** (the call expression's node), with
nothing evaluated after the arguments.

A **place argument** (`Arg::place`) gives a by-reference parameter a
reference to the place, and a by-value parameter the place's current value
(a copy under PHP arrays). For a known callee the choice is made at compile
time; for a dynamic call, at run time, with `dparam_ref`/`dparam_ref_named`
on the evaluated callee before the argument is evaluated. Either way the
place's operands are evaluated once. A positional place argument after a
spread goes by value (its position is known only at run time). A
by-reference parameter given a value receives a new reference holding it.

### Variables, references, and closures

A variable lives in a register, unless it is shared: captured by reference
(an explicit `ByRef`/`ByMutRef` capture, or an implicit capture under `ByRef`,
`ByMutRef`, or `Infer`), aliased by a reference assignment, passed as a place
argument, or a by-reference parameter. A shared variable lives in an LSB
**reference** (`new_ref`, LSB §5.17), and every binding of it (each `let`,
each match) makes a new one. Registers are reused once a variable's scope
closes.

A closure captures by value (a copy of the value at creation; each call
starts from that copy) or by reference (the reference). A recursive
closure's self binder is a reference that holds the closure. `global $x`
makes a variable that names the global; `static $x = init` names a global
initialized the first time the statement runs. A global or static shared by
reference is stored in a reference (created by `<start>`, or by the
statement's first run).

### Values and operations

Values are LSB `dyn` values: `nil`, `bool`, `int` (64-bit), `float`
(binary64), `char`, `str` (bytes), arrays (maps), functions, coroutines, and
error values. Unit and `()` are `nil`. A block without a tail and a loop
without a break value evaluate to `nil`.

Operations are LSB's dynamic instructions with the op instance's OPS v2
policy in their modifier (`promote` and `shift = saturate` included): `add
sub mul div rem floor_div floor_mod pow shl shr neg abs bit_not`, the
comparisons, and `and or xor` (logical on two bools, bitwise otherwise).
`not` is **logical** (`dnot`: the negated truthiness, a `bool`); `bit_not` is
the bitwise complement (`dbit_not`). `pow` is `dpow`: an exact integer power
or the overflow policy (`promote` gives the nearest float), a negative integer
exponent is `NegativeExponent` (E0006) unless the policy is `promote` (then
the float power), floats by the family's `ls_pow`. `abs` is `dabs` (`abs(MIN)`
follows the overflow policy). The rest dispatch on the operands' kinds: two
`int`s use the typed `i64` instruction; numbers with a `float` use the `f64`
one, converting `int` operands (OPS's mixed rule): `min max ieee_rem
total_cmp fma sqrt floor ceil trunc round round_even`. Conversions:
`int_cast<T>`, `float_to_int<T>`, `narrow<T>`, `int_to_float<T>`,
`bool_to_int<T>`, `f64_to_f32`, `f32_to_f64`, `char_from_u32`, and the
64-bit `zext`, `sext`, and `bitcast`; a result outside the dynamic integer
range raises `ArithOverflow`. A non-number where a number is needed is a
`TypeError` (the instruction's hook first, where it has one).

Conditions use LSB truthiness (`dtruthy`, with its hook). Comparisons in a
condition jump on the comparison directly.

### Types: casts and type tests

Type annotations are erased: the dynamic profile checks types only where a
`Cast` or a `TypeTest` pattern asks.

A type stands for a set of dynamic kinds: an integer primitive `int`,
`f32`/`f64` `float`, `bool`, `char`, `str`, tuples, arrays, and slices
`map`, `Any` every kind, `never` none; `T?` adds `nil`; a **union** is the
kinds of any member, an **intersection** the kinds of every member (so `int &
(int | str)` is `int`). A type test pattern matches a value of one of the
type's kinds. A path to a declared type is `Unsupported::Pattern` (or
`Unsupported::Cast`).

`expr as T`: to `Any` the identity; to `bool` truthiness; to an integer type
from an `int` (`int_cast`), a `float` (`float_to_int`), or a `bool`; to
`f64`/`f32` from a number or a `bool`; to `str` only from a string
(formatting is a runtime-library call); to `char` from a `char` or an `int`;
to a union or intersection, a **checked identity**: a value of one of its
kinds passes unchanged, any other is a `TypeError`. `T?` passes `nil`.

### Arrays and maps

Array and tuple literals, map literals, anonymous record literals, and
`[e; n]` (`n` below 1 gives an empty array) are LSB maps (`map dyn -> dyn`),
so arrays are PHP arrays: ordered, with the next integer key. A record field
is a string key; `{..base}` copies `base` (a non-map base is a `TypeError`).

Under [`ArraySemantics::Php`](#arraysemantics) (the default) arrays are
values: storing a value that may be shared (a variable, an element, a
property, a host function's or intrinsic's result, or a construct yielding
one) into a variable, an element, a parameter, a capture, a yield, or a
return copies it if it is an array, with LSB's O(1) copy-on-write `dup`.
Under `ArraySemantics::Reference` copies are the same array.

Under [`KeyCoercion::Php`](#keycoercion) (the default) index keys and map
literal keys are normalized as PHP does; property names are not.

### Places, assignment, and `let_place`

A **place** is a variable, a global, or a chain of index, property, dynamic
property, and append steps from a root. Its **operands** are the root (when
it is not a variable) and every index key and dynamic member name, evaluated
left to right, root first.

`target = value` evaluates the target's operands, then `value`, then writes;
`target op= value` evaluates the operands, reads the current value, evaluates
`value`, applies the op, writes. A variable root is read and written when
used (a reference assignment inside `value` may rebind it). **An assignment
evaluates to the value written**, a compound one to the new value (HIR §8.2),
so `a = b = 3` assigns 3 to both.

`let_place p = place in body` (HIR §8.2) evaluates the place's operands once,
into registers, and makes `p` name the place in `body`: each read of `p` reads
through the saved operands, each write writes through them (with
auto-vivification), `&p` references it, and `p[k]`, `p->x` extend it; no
operand is ever recomputed. This is how `$a[f()] .= "x"` (through
`mox.concat`), `$a[f()]++`, and `??=` evaluate their place once. The alias
never crosses a frame (HIR forbids capturing it).

A write through a chain walks from the root. Under PHP semantics a `nil` root
or intermediate becomes a new array, stored back (auto-vivification), and
each intermediate container is separated with `dsep_index`/`dsep_prop` (LSB
§5.16): copied only when another container may share it, so a copy that
shared it is unaffected and repeated nested writes (`$g[$i % 64][] = $i`) run
in place. A non-array container uses the dynamic instructions and their hooks
(`dget_index`/`dset_index`, `get_prop`/`set_prop`). `a[] = v` on a non-array
is a `TypeError`.

### References (PHP `&`)

PHP references are LSB references (LSB §5.17):

| Form | LSB |
|---|---|
| `$t = &$s` (variables) | `$t`'s register takes `$s`'s reference |
| `$t = &$a[k]` (an element; `->p` likewise) | `dref_index` (`dref_prop`): the slot becomes a reference slot, `$t` names its reference; nested chains auto-vivify and separate as writes do |
| `$a[k] = &$s` | `dbind_index` (`dbind_prop`): the slot becomes `$s`'s reference |
| `$a[k] = &$b[j]` | `dref_index`, then `dbind_index` |
| `f($a[k])` to a by-reference parameter | `dref_index`, the reference passed |

The value of a reference assignment is the aliased place's value. A
reference slot is shared by copies of its array (PHP's behaviour while the
reference is held elsewhere); see LSB §5.17 for the one divergence from PHP
(references are not dropped when their count falls to one) and its
`dunref_*` remedy, which this release does not emit.

### Control flow and `match`

`if`, blocks, labeled blocks with `break 'label value`, and the loop
primitive (`continue` runs the step; every iteration passes a `safepoint`).
`return` leaves the function (or closure, or the module body).

`match` is a sequential decision procedure: each arm's pattern, then its
guard, in order. **When no arm matches**, it raises `NoMatch` (E0200) with
the scrutinee as the error's payload (HIR §8.10; Mox maps it to
`UnhandledMatchError`). Patterns: wildcard, binding (by value), `x @ p`,
identifiers (a constant's value, else a binding), literals and constant paths
(`deq`, the language's equality with its hook), ranges (the value and bounds
of one class, numbers or chars, then ordered comparison; NaN is in no range),
tuples and slices (an array, by integer keys `0..n` and `len-m..len`, with
the rest bound to a new array), anonymous records (a map, by string keys;
without `..` the length must match), or-patterns, and
[type tests](#types-casts-and-type-tests). `let p = e` with a refutable
pattern runs `else` on no match, or raises a `TypeError` at the statement.

### Exceptions, `finally`, and `defer`

`throw e` raises `e` (a caught runtime error value rethrown keeps its
original location). `try` is LSB §4.3's canonical lowering: a catch region
over the body, its arms tried in order (none matching rethrows from the
`try`), and for a `finally` a second region over the body and the arms, with
a completion kind (`i8`) and value (`dyn`) per `try` and one copy of the
`finally` body ending in a dispatch: normal, return, rethrow (from the
`try`), or the `n`th `break`/`continue` target. A jump out of the `finally`
body overrides the pending completion; an error inside it replaces it.
`defer e` makes the rest of the block a `try` whose `finally` is `e`. The
completion registers live in the frame, so a `finally` that yields resumes
with its pending completion (LSB §5.13 rule 12).

### Generators, `await`, and `spawn`

LSB coroutines are stackful (LSB §5.13), so only generators need a frame of
their own:

- A function or closure with `YIELD` is a **generator**: calling it makes a
  coroutine of its body (`coro_new`) without running it, and returns the
  coroutine. Its arguments are bound at the call; its parameter defaults and
  patterns are evaluated when the body starts (first resume). A generator
  closure's entry passes its captures to the body as leading arguments.
- `yield v` is `yield` (the automatic key: PHP's rule, LSB rule 10), `yield
  k => v` is `yield_kv`, `yield` without a value yields `nil`; each evaluates
  to the value sent by the next resume (copied under PHP arrays).
- `yield from e` (HIR §8.7): when `e` is a coroutine, a loop that resumes it,
  re-yields each value under its own key (`coro_key`, `yield_kv`), forwards
  each sent value (`resume`) and each error thrown into this generator
  (`resume_throw`, from a handler around the re-yield), passes an `await` of
  the inner coroutine through, and evaluates to its return value; an inner
  coroutine that already returned gives its return value without resuming.
  Any other value is iterated (`diter_new`): each entry yielded under its key,
  the result `nil`.
- `ASYNC` alone changes nothing about a function: its `await`s suspend
  whichever task runs it. `await e` is `await`; `spawn e` is `spawn` of the
  zero-parameter callable `e`, through the module's `spawn` hook (bind it with
  `Options::with_hook(Hook::Spawn, ..)`; without one it raises `NoScheduler`,
  E0112).
- Iterating a generator (`iter`/`iter_next`, or LSB's `iter_new`) resumes it
  with `nil`; the [core intrinsics](#named-intrinsics) `resume`,
  `resume_throw`, `coro_close`, `coro_key`, `coro_result`, and `coro_status`
  are what a runtime's generator object (PHP's `send`, `throw`, `key`,
  `getReturn`, `valid`) lowers to.

Two deviations from PHP, both recorded in the ROADMAP: the automatic key
after a `yield from` continues after the largest integer key the inner
generator yielded (LSB's `yield_kv` moves the counter; PHP keeps the outer
generator's own), and delegating to a generator that was already advanced
resumes it (PHP re-yields its current value first, which LSB cannot read).

### Named intrinsics

`Intrinsic::Named(name)` compiles through the [`Intrinsics`](#intrinsics)
table of the [`Options`](#options): the name must be in the table
(`CompileError::UnknownIntrinsic`), and the operand count within the entry's
[`Arity`](#arity) (`CompileError::IntrinsicArity`). An entry's
[`Lowering`](#lowering) is one of:

- an [`LsbOp`](#lsbop): an LSB sequence with LSB's semantics (hooks
  included);
- a **host function**: `call_import` of `module`.`name` with the operands, an
  import per argument count;
- a **fast path** ([`Fast`](#fast)) over a host function: the operands are
  evaluated straight into the host call's window, their kinds tested, and the
  inline LSB sequence runs where its result is exactly the language's (the
  fast path's documented domain); everywhere else the same window goes to the
  host function. No fast path invokes an LSB hook, so its results do not
  depend on the module's hooks. A host function used by a fast path must
  implement the intrinsic for every input (it is called for exactly the
  operands outside the domain, `tests/intrinsics.rs` checks this) and agree
  with the fast path on its domain.

[`Intrinsics::core`](#intrinsics), the default:

| Name | Operands | Result |
|---|---|---|
| `concat` | 2 | `dconcat` (two strings, else the `concat` hook) |
| `len` | 1 | `dlen` as an `int` |
| `truthy`, `lnot` | 1 | truthiness and its negation as a `bool` |
| `type_of` | 1 | the LSB kind code as an `int` |
| `iter` | 1 | an iterator (`diter_new`), over a copy under PHP semantics; a coroutine is iterated by resuming it |
| `iter_next` | 1 | `nil` when done, else the pair `[key, value]` |
| `resume`, `resume_throw`, `coro_close` | 2 (coroutine, value) | the value yielded, awaited, or returned next |
| `coro_key`, `coro_result` | 1 | the last key; a returned coroutine's return value |
| `coro_status` | 1 | the state code as an `int` (0 created, 1 running, 2 yielded, 3 awaiting, 4 returned, 5 failed) |
| `err_code`, `err_payload` | 1 | a caught runtime error value's code as an `int` (0 for other values), and its payload (nil for other values): how a runtime maps `NoMatch` (200, the unmatched value) to its own exception |

`iter` and `iter_next` are what a `foreach` lowering (HIR spec §9.4) needs.

### The Mox intrinsics

[`Intrinsics::mox`](#intrinsics) is `core` plus every intrinsic of the Mox
sketch (`_lexersketch/sketches/mox.lsf`). Each is a fast path over the host
function `mox`.`<name>` where one is exact, else the host function alone.
"Host" below is what LexerSketch's runtime (ls-exec) must implement: **PHP
8's semantics of the operator for every input** (the column states what PHP
does; the fast path computes exactly that on its domain). Errors are raised
by the host function as `bvm_lang::HostError::Raise(kind)` with the kind
given (the runtime maps kinds to PHP's exception classes), so the fast path
and the host raise alike.

| Intrinsic | PHP | Arity | Fast path: domain → result | Host function: what it computes |
|---|---|---|---|---|
| `mox.concat` | `.` | 2 | two `str` → their bytes concatenated | both operands converted to strings by PHP's rules (null `""`, bools `"1"`/`""`, ints decimal, floats PHP's float-to-string, arrays `"Array"` with a warning, objects `__toString`), concatenated |
| `mox.concat_n` | string interpolation | 0 to 255 | every part `str` → one `str_concat_n` (`""` for none) | each part converted as `concat` does, concatenated in order |
| `mox.mod` | `%` | 2 | two `int` → truncated remainder (sign of the dividend; `MIN % -1` is 0); a zero divisor raises `DivByZero` (E0002) | operands converted to int (PHP's `(int)` on floats, numeric strings; non-numeric strings and arrays raise `TypeError`), then the same; zero divisor `DivByZero` |
| `mox.pow` | `**` | 2 | two numbers → `dpow` with `overflow = promote`: exact int when it fits, else the nearest float; negative int exponent: the float power; floats by `ls_pow` | numeric strings, null, bools converted to numbers, then the same; other operands `TypeError` |
| `mox.shl` | `<<` | 2 | two `int` → `shl`, `shift = saturate` (amount ≥ 64 gives 0; negative raises `ShiftOutOfRange`, E0003) | operands converted to int, then the same |
| `mox.shr` | `>>` | 2 | two `int` → arithmetic `shr`, `shift = saturate` (≥ 64 gives 0 or -1) | as `shl` |
| `mox.xor` | `xor` (logical) | 2 | both in nil/bool/int/float → exclusive or of their truthiness (`0`, `0.0`, `-0.0`, nil, false are false; NaN true) | PHP truthiness (`""` and `"0"` false, empty arrays false), exclusive or |
| `mox.loose_eq` | `==` | 2 | the same kind in nil/bool/int/float → equality by value (IEEE for floats); two `str` with equal bytes → true | PHP 8's loose comparison: numeric strings as numbers (`"1e3" == "1000"`), int vs float as floats, null vs string as strings, null/bool vs others as bools, arrays by pairs |
| `mox.loose_ne` | `!=` | 2 | the negation of `loose_eq`'s, same domain | `!(a == b)` |
| `mox.identical` | `===` | 2 | both in nil/bool/int/float/str → kinds equal and values equal (floats IEEE, strings bytes) | the same for scalars; arrays: same pairs in the same order, identical; objects: same instance |
| `mox.not_identical` | `!==` | 2 | the negation, same domain | `!(a === b)` |
| `mox.lt`, `mox.le`, `mox.gt`, `mox.ge` | `<` `<=` `>` `>=` | 2 | two `int`s or two `float`s → numeric order (false with NaN) | PHP 8's comparison (`a > b` is `b < a`): numeric strings as numbers, else strings bytewise; int vs float as floats; arrays by count then pairs |
| `mox.spaceship` | `<=>` | 2 | two `int`s → -1, 0, or 1 | PHP 8's three-way comparison, `1` when unordered (NaN) |
| `mox.to_number` | unary `+` | 1 | an `int` or `float` → itself | numeric string → its number, null 0, bools 0/1; else `TypeError` |
| `mox.bit_not` | `~` | 1 | an `int` → its complement | a float truncated to int then complemented; a string complemented bytewise; else `TypeError` |
| `mox.cast_int` | `(int)` | 1 | `int` → itself; `bool` → 0/1; nil → 0 | floats truncated (NaN, infinities, and out-of-range values 0), strings by their leading numeric prefix, arrays 0/1 |
| `mox.cast_float` | `(float)` | 1 | `float` → itself; `int` → nearest float; `bool` → 0.0/1.0; nil → 0.0 | strings by their leading numeric prefix, arrays 0.0/1.0 |
| `mox.cast_string` | `(string)` | 1 | `str` → itself | as `concat` converts |
| `mox.cast_bool` | `(bool)` | 1 | nil/bool/int/float → truthiness | PHP truthiness (`"0"` false, empty arrays false, objects true) |
| `mox.cast_array` | `(array)` | 1 | an array → itself | nil `[]`; a scalar `[v]`; an object its properties |
| `mox.instanceof` | `instanceof` | 2 | none (host only) | the runtime's class check |
| `mox.cast_object` | `(object)` | 1 | none (host only) | the runtime's `stdClass` conversion |
| `mox.clone` | `clone` | 1 | none (host only) | the runtime's clone (`__clone`) |

The fast domains are chosen where LSB's result is exactly PHP's: for example,
`1 == 1.0` (an int against a float) goes to the host because PHP compares as
floats and LSB's `deq` exactly (they differ above 2^53), and two different
strings go to the host because PHP compares numeric strings as numbers. The
float `pow` of the fast path is the family's `ls_pow`, correctly rounded
except within 2^-85 of a rounding boundary; PHP's own `pow` is the platform
libm's.

### Error locations and debug information

Every instruction records the HIR node it was compiled from
([`Compiled::origin`](#compiled)), so a runtime error's `(function, pc)`
maps to a node: an operation's error to the operation, a call's (binding
errors included) to the call, an unmatched `let` to the statement, an
unmatched `match` to the `match`, a rethrow to the `try`. Line-table rows
come from a [`Locate`](#locate), or carry byte offsets without one. Each
variable's register and live range is in the debug locals table.

### Budgets and hostile input

Generation never recurses over the input: an explicit task stack handles any
nesting depth (type sets of nested unions and intersections are computed with
an explicit stack too). The module's size is bounded by
[`Options::with_max_instructions`](#options); a function's by LSB's 65,536
registers (a `CompileError::Build` beyond). A parameter list has at most 255
entries, 64 when one has a default (the presence mask), counting a generator
closure's captures (`CompileError::TooManyParams`); a call at most 255
arguments (`CompileError::TooManyArgs`). A `finally` can be left by at most
124 distinct jump targets (the `i8` completion kind).

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
    pub fn new() -> Self;                    // the PHP profile, Intrinsics::core()
    pub fn with_arrays(self, ArraySemantics) -> Self;
    pub fn with_keys(self, KeyCoercion) -> Self;
    pub fn with_body(self, BodyMode) -> Self;
    pub fn with_file(self, &str) -> Self;          // line-table file without a locator
    pub fn with_host_module(self, &str) -> Self;   // import module for dot-less symbols
    pub fn with_hook(self, Hook, module: &str, name: &str) -> Self;
    pub fn with_intrinsics(self, Intrinsics) -> Self;
    pub fn with_max_instructions(self, u64) -> Self;
    pub fn arrays(&self) -> ArraySemantics;
    pub fn keys(&self) -> KeyCoercion;
    pub fn body(&self) -> BodyMode;
    pub fn file(&self) -> &str;
    pub fn host_module(&self) -> &str;
    pub fn hooks(&self) -> &[(Hook, String, String)];
    pub fn intrinsics(&self) -> &Intrinsics;
    pub fn max_instructions(&self) -> u64;
}
```

`with_hook` binds an LSB hook (LSB §5.8) to a host function with the hook's
signature (format 2's `pow`, `abs`, and `call_shape` hooks included); a
language supplies its own semantics this way (PHP's numeric strings in
arithmetic, `get_index` returning `null` for a missing key, `spawn` into a
scheduler, ...). With hooks bound, the compiler copies arrays more
conservatively (a hook may return an operand). `with_intrinsics` sets the
[intrinsic table](#intrinsics).

```rust
use bcgen_lang::{ArraySemantics, Intrinsics, KeyCoercion, Options};
use bytecode_lang::Hook;

let o = Options::new()
    .with_arrays(ArraySemantics::Reference)
    .with_keys(KeyCoercion::None)
    .with_host_module("env")
    .with_hook(Hook::Spawn, "ls.async", "spawn")
    .with_intrinsics(Intrinsics::mox())
    .with_max_instructions(1 << 20);
assert_eq!(o.hooks().len(), 1);
assert!(o.intrinsics().get("mox.loose_eq").is_some());
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

## `Intrinsics`

```rust,ignore
pub struct Intrinsics { /* private */ }
impl Intrinsics {
    pub fn new() -> Self;    // empty
    pub fn core() -> Self;   // the LSB intrinsics (15)
    pub fn mox() -> Self;    // core + the Mox sketch's (41)
    pub fn with_lsb(self, name: &str, op: LsbOp) -> Self;
    pub fn with_host(self, name: &str, arity: Arity, module: &str, func: &str) -> Self;
    pub fn with_fast(self, name: &str, fast: Fast, module: &str, func: &str) -> Self;
    pub fn get(&self, name: &str) -> Option<&IntrinsicDef>;
    pub fn len(&self) -> usize;
    pub fn is_empty(&self) -> bool;
    pub fn iter(&self) -> impl Iterator<Item = (&str, &IntrinsicDef)>;
}
```

The intrinsic table (LexerSketch decision D27): each name's arity and
[lowering](#lowering). A later entry of a name replaces an earlier one. The
semantics of `core` and `mox` are in [Named intrinsics](#named-intrinsics)
and [The Mox intrinsics](#the-mox-intrinsics).

```rust
use bcgen_lang::{Arity, Fast, Intrinsics, LsbOp, Options};

let table = Intrinsics::core()
    .with_fast("lang.eq", Fast::StrictEq, "lang", "eq")
    .with_host("lang.format", Arity::range(1, 8), "lang", "format")
    .with_lsb("lang.size", LsbOp::Len);
assert_eq!(table.len(), 18);
assert_eq!(table.get("lang.format").unwrap().arity(), Arity::range(1, 8));
let opts = Options::new().with_intrinsics(table);
assert!(opts.intrinsics().get("mox.concat").is_none());
```

## `IntrinsicDef`

```rust,ignore
pub struct IntrinsicDef { /* private */ }
impl IntrinsicDef {
    pub fn arity(&self) -> Arity;
    pub fn lowering(&self) -> &Lowering;
}
```

One table entry.

```rust
use bcgen_lang::{Arity, Intrinsics, Lowering};

let t = Intrinsics::mox();
let def = t.get("mox.clone").unwrap();
assert_eq!(def.arity(), Arity::exact(1));
assert!(matches!(def.lowering(), Lowering::Host { .. }));
```

## `Lowering`

```rust,ignore
#[non_exhaustive]
pub enum Lowering {
    Lsb(LsbOp),
    Host { module: String, name: String },
    Fast { fast: Fast, module: String, name: String },
}
impl Lowering { pub fn host(&self) -> Option<(&str, &str)>; }
```

How an intrinsic compiles (see [Named intrinsics](#named-intrinsics)); `host`
is the host function it may call, which the embedder registers with
`bvm_lang::Host::register(module, name, ..)`.

```rust
use bcgen_lang::{Fast, Lowering, LsbOp};

assert_eq!(Lowering::Lsb(LsbOp::Len).host(), None);
let f = Lowering::Fast { fast: Fast::Concat, module: "mox".into(), name: "concat".into() };
assert_eq!(f.host(), Some(("mox", "concat")));
```

## `LsbOp`

```rust,ignore
#[non_exhaustive]
pub enum LsbOp {
    Concat, Len, Truthy, Not, TypeOf, Iter, IterNext,
    Resume, ResumeThrow, CoroClose, CoroKey, CoroResult, CoroStatus,
    ErrCode, ErrPayload,
}
impl LsbOp { pub const fn arity(self) -> Arity; }
```

The LSB sequences of the [core table](#named-intrinsics), with LSB's
semantics.

```rust
use bcgen_lang::{Arity, LsbOp};

assert_eq!(LsbOp::Resume.arity(), Arity::exact(2));
assert_eq!(LsbOp::CoroStatus.arity(), Arity::exact(1));
```

## `Fast`

```rust,ignore
#[non_exhaustive]
pub enum Fast {
    Concat, ConcatN, IntRem, NumPow, IntShl, IntShr, ScalarXor,
    LooseEq, LooseNe, StrictEq, StrictNe, Lt, Le, Gt, Ge, IntSpaceship,
    NumIdentity, IntBitNot, ToInt, ToFloat, ToStr, ToBool, ToArray,
}
impl Fast { pub const fn arity(self) -> Arity; }
```

A guarded fast path: its **domain** (the operand kinds where it runs inline)
and what it computes there, as the [Mox table](#the-mox-intrinsics) states
for each (`Concat` is `mox.concat`'s, `IntRem` `mox.mod`'s, ...). Any
language whose operator agrees with LSB on a domain can reuse it with its own
host function.

```rust
use bcgen_lang::{Arity, Fast};

assert_eq!(Fast::ConcatN.arity(), Arity::at_least(0));
assert_eq!(Fast::ToBool.arity(), Arity::exact(1));
```

## `Arity`

```rust,ignore
pub struct Arity { /* private */ }
impl Arity {
    pub const fn exact(n: u8) -> Self;
    pub const fn range(min: u8, max: u8) -> Self;   // a max below min is raised to it
    pub const fn at_least(n: u8) -> Self;           // up to 255
    pub const fn min(self) -> u8;
    pub const fn max(self) -> u8;
    pub const fn accepts(self, n: usize) -> bool;
}
impl Display for Arity { /* "2", "0 to 255" */ }
```

How many operands an intrinsic takes (at most 255, an import's limit).

```rust
use bcgen_lang::Arity;

assert!(Arity::range(1, 3).accepts(2));
assert!(!Arity::at_least(1).accepts(0));
assert_eq!(Arity::exact(2).to_string(), "2");
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

The module, its entry points, the function compiled for each function item
(its parameters, then the presence mask when a parameter has a default; it
carries the parameter list, so a host can call it typed with `call` or bind
arguments to it dynamically; a generator's returns the coroutine), and the
HIR node of every instruction.

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
    UnknownIntrinsic { name: Symbol, node: NodeRef, span: Span },
    IntrinsicArity { node: NodeRef, span: Span, arity: Arity, found: u32 },
    TooManyArgs { node: NodeRef, span: Span, limit: u32 },
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

Why a unit did not compile, stopping at the first problem in the unit's
canonical order. `LiteralOutOfRange` is an integer literal outside `i64` (the
dynamic integer range); `NotAssignable` an assignment to a function, a
constant, or a non-place; `UnknownIntrinsic` a named intrinsic the table does
not have (its name is the symbol); `IntrinsicArity` a count the entry does not
accept; `TooManyArgs` a call of more than 255 arguments; `TooManyParams` a
parameter list beyond LSB's limits (64 with a default, else 255, counting a
generator closure's captures); `TooManyJumps` a `finally` left by more than
124 jump targets; `BudgetExceeded` the instruction budget; `Build` an LSB
format limit (`bytecode_lang::BuildError`). `Display` names the problem and
its span.

```rust
use bcgen_lang::{CompileError, Intrinsics, Options, Compiler};
use hir_lang::{Builder, Expr, Intrinsic, List, OpKind};
use intern_lang::Interner;

let mut b = Builder::new();
let mut e = b.int(0);
for _ in 0..100 {
    let one = b.int(1);
    e = b.op(OpKind::Add, &[e, one]);
}
let module = hir_lang::ItemKind::Module { items: List::EMPTY, body: Some(e), effects: hir_lang::Effects::NONE };
let root = b.item(hir_lang::Item::new(None, module));
let hir = b.finish(root)?;
let err = Compiler::new(Options::new().with_max_instructions(10)).compile(&hir, &Interner::new()).unwrap_err();
assert_eq!(err, CompileError::BudgetExceeded { limit: 10 });
assert_eq!(err.node(), None);

// A named intrinsic outside the table.
let mut names = Interner::new();
let mut b = Builder::new();
let sym = names.intern("mox.nope");
let x = b.expr(Expr::Intrinsic { kind: Intrinsic::Named(sym), generic_args: List::EMPTY, args: List::EMPTY });
let module = hir_lang::ItemKind::Module { items: List::EMPTY, body: Some(x), effects: hir_lang::Effects::NONE };
let root = b.item(hir_lang::Item::new(None, module));
let hir = b.finish(root)?;
let err = Compiler::new(Options::new().with_intrinsics(Intrinsics::mox())).compile(&hir, &names).unwrap_err();
assert!(matches!(err, CompileError::UnknownIntrinsic { name, .. } if name == sym));
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Unsupported`

```rust,ignore
#[non_exhaustive]
pub enum Unsupported {
    Class, Record, Reference, RefPlace, VarVar, Intrinsic, Asm, BigInt,
    ForeignUnit, TypeDirected, ExternValue, ExternArgs, Conversion, Cast, Pattern,
}
impl Unsupported { pub const fn describe(self) -> &'static str; }
```

A form 0.3 does not compile (`describe`, also `Display`). `Class` and
`Record` arrive in 0.5; `Reference` (pointers), `RefPlace` (a reference to an
appended element or a variable variable), `VarVar` (no named frames), and
`Intrinsic` (atomics, volatile, fences) have no meaning in LSB's dynamic
profile; `ExternValue` and `ExternArgs` need a host function's parameter list,
which the compiler does not know; `Asm` is for native backends.

```rust
use bcgen_lang::Unsupported;

assert!(Unsupported::Class.describe().contains("0.5"));
assert_eq!(Unsupported::Asm.to_string(), "inline assembly (native backends only)");
```

## Feature flags

| Feature | Default | Effect |
|---|---|---|
| `std` | yes | Forwards `std` to the family crates. Without it the crate is `no_std` + `alloc`. |

## Stability

0.3.0 is a pre-release surface: names and signatures may change across 0.x,
each change recorded in the CHANGELOG. The compiled code's semantics are the
ones this file states, checked by the differential, binding, intrinsic, and
end-to-end tests; changes to them are breaking and recorded.
