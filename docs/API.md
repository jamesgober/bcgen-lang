# bcgen-lang &mdash; API Reference

> Complete reference for every public item in `bcgen-lang`, with examples, and
> the dynamic semantics the compiled code implements.
> **Status: 0.4.0, pre-1.0.** The surface may change across the 0.x series; it
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
  - [String offsets](#string-offsets)
  - [Classes, interfaces, and mixins](#classes-interfaces-and-mixins)
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
- [`ClassOp`](#classop)
- [`Arity`](#arity)
- [`Compiled`](#compiled)
- [`Locate`](#locate)
- [`Location`](#location)
- [`LineIndex`](#lineindex)
- [`CompileError`](#compileerror)
- [`ClassProblem`](#classproblem)
- [`Unsupported`](#unsupported)
- [Feature flags](#feature-flags)
- [Stability](#stability)

## Overview

`bcgen-lang` compiles a resolved HIR unit (`hir_lang::Hir`, hir-lang 0.4,
HIR spec v3) to an LSB module (`bytecode_lang::Module`, bytecode-lang 0.3,
**LSB format version 2**) that `bvm-lang` 2.0 (`2.0.0-alpha.4`) loads and
runs. It compiles the **dynamic profile**: every value is an LSB `dyn`. It is
the bridge LexerSketch decision D19 calls for: HIR to LSB directly, keeping
the structure (closures, maps, dynamic values, exceptions, coroutines) that
both representations have first-class.

## Installation

```toml
[dependencies]
bcgen-lang = "0.4"
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

Compiled in 0.4: function items (with or without a body; generators and async
functions included), globals, constants, nested modules, the module body;
**classes, interfaces, and mixins** (PHP traits) with their methods,
properties, static properties, and constants (see
[Classes, interfaces, and mixins](#classes-interfaces-and-mixins)); every
expression form except those below, including keyed `yield`, `yield from`,
`await`, `spawn`, `let_place`, reference assignments to and from elements,
member paths (`C::m`, `self::`, `parent::`, `static::`), and named intrinsics
through the [intrinsic table](#intrinsics); `let` (with any supported
pattern, and let-else), expression statements, `static`, `global`, `defer`.

Not compiled in 0.4, each a precise [`Unsupported`](#unsupported) error:
`impl` blocks, declared records, sums, and constructor patterns (0.5); a
class with several bases (LSB structs have one parent); pointers (`*e`, `&e`
borrows, `ref` patterns); a reference to an appended element (`$a[] = &$x`)
or a variable variable; atomics, volatile accesses, and fences; inline
assembly; big-integer literals; definitions of another unit; type-directed
paths; a host function used as a value or given spread or named arguments; a
class name used as a plain value, a mixin's member reached through the mixin,
a type test against a class the unit does not declare; and a few
conversions, casts, and type tests with no dynamic meaning. A class graph
LSB cannot hold or PHP rejects is a [`ClassProblem`](#classproblem).

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
| `C::m`, one per method of a class (per using class for a mixin's) | always | `(receiver, param, ..., [i64 mask]) -> dyn`, with its parameter list (the receiver positional-only) |
| `C::new`, `C::test`, `C::class` | per class and interface | `(receiver) -> dyn`; `C::test` also takes the value tested |
| an accessor per static property and constant | per class holding one | `(receiver) -> dyn`: the static's reference, the constant's value |
| `<marker>`, `<class_of>`, `<noop>`, `<dyn get>`, `<dyn set>`, `<dyn method>` | when used | interface markers; run-time class values; `new` without a constructor; [members by run-time name](#members-by-run-time-name) |

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
[`Options::with_hook`](#options) binds. Types: one LSB `struct` per class and
interface. Globals per class: its token (`C::class`), one per static
property (a reference) and constant, and `<classes>`, the name registry.

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

Method calls (`receiver.method(args)`) look the method up and call it
dynamically with the receiver as the first positional argument; static
member calls of a known method are direct calls. The details, visibility
included, are in [Classes, interfaces, and mixins](#classes-interfaces-and-mixins).
Without classes in the unit a method call is 0.3's: `get_prop` of the plain
name, and `receiver->$name(args)` looks it up with `dget_index`.

### Argument binding

LSB §5.15's rules, applied at compile time to known callees and by the VM to
everything else, so both paths agree (`tests/binding.rs` checks this on
random parameter and argument lists):

1. A positional argument after a named one is an `ArgumentError`.
2. Positional arguments fill the positional-only and normal parameters in
   order; extra ones go to the rest parameter, or are an `ArgumentError`;
   under [`Options::with_ignore_extra`](#options) (PHP) they are evaluated and
   dropped (every parameter list carries LSB's `ignore_extra`).
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
`dunref_*` remedy, which this release does not emit. bvm-lang's
reference-counting profile unbinds such a reference at run time when an
array is copied (ISSUES P34).

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
| `mox.cast_int` | `(int)` | 1 | `int` → itself; `bool` → 0/1; nil → 0; `float` → PHP 7/8's `zend_dval_to_lval` (64-bit): truncated in `[-2^63, 2^63)`, NaN and infinities 0, anything else modulo 2^64 into the signed range | strings by their leading numeric prefix (a float part saturating, `zend_dval_to_lval_cap`), arrays 0/1 |
| `mox.cast_float` | `(float)` | 1 | `float` → itself; `int` → nearest float; `bool` → 0.0/1.0; nil → 0.0 | strings by their leading numeric prefix, arrays 0.0/1.0 |
| `mox.cast_string` | `(string)` | 1 | `str` → itself | as `concat` converts |
| `mox.cast_bool` | `(bool)` | 1 | nil/bool/int/float → truthiness | PHP truthiness (`"0"` false, empty arrays false, objects true) |
| `mox.cast_array` | `(array)` | 1 | an array → itself | nil `[]`; a scalar `[v]`; an object its properties |
| `mox.instanceof` | `instanceof` | 1 to 2 | [class operation](#classop): the unit's classes and interfaces inline | a class the unit does not declare (the value and the class value): the runtime's class check |
| `mox.new` | `new` (the extern of the sketch's `new_object` template) | 0 to 255 | [class operation](#classop): the unit's classes inline | a class name the unit does not declare, then the positional arguments: the runtime's `new` |
| `mox.cast_object` | `(object)` | 1 | none (host only) | the runtime's `stdClass` conversion |
| `mox.clone` | `clone` | 1 | [class operation](#classop): instances of the unit's classes (`dup`, then `__clone`) | every other value: the runtime's clone (PHP raises `Error` for a non-object) |
| `mox.str_offset` | `$s[i]` on a string ([string offsets](#string-offsets)) | 2 | a `str` and an `int` in `-len..len` → the one-byte string at that offset | PHP 8: an out-of-range offset warns and gives `""`; a numeric string offset converts; a leading-numeric one warns; any other offset raises `TypeError` ("Cannot access offset of type ... on string") |

`(int)` of a float follows PHP 7/8 on 64-bit platforms exactly (ISSUES P41),
inline: `(int)1e19` is `-8446744073709551616`, `(int)-1e19` is
`8446744073709551616`, `(int)1e20` is `7766279631452241920`, `(int)2**63`
is `PHP_INT_MIN`, `(int)(2**64 + 4096)` is `4096`, `(int)1e300` is `0`, and
NaN and the infinities are `0` (`tests/intrinsics.rs` has these vectors and
4,000 random bit patterns against a transcription of `zend_dval_to_lval`).
A runtime that computes `(int)` itself must do the same.

The fast domains are chosen where LSB's result is exactly PHP's: for example,
`1 == 1.0` (an int against a float) goes to the host because PHP compares as
floats and LSB's `deq` exactly (they differ above 2^53), and two different
strings go to the host because PHP compares numeric strings as numbers. The
float `pow` of the fast path is the family's `ls_pow`, correctly rounded
except within 2^-85 of a rounding boundary; PHP's own `pow` is the platform
libm's.

### String offsets

LSB's `dget_index` reads an in-range string offset as the **byte** (`"abc"[1]`
is `98`) and never consults the `get_index` hook (LSB §5.7, ISSUES P38).
[`Options::with_string_offsets`](#options) routes every indexed read whose
base is a string (`$s[i]`, also through a `let_place` alias or inside a
place chain) through an entry of the intrinsic table, called with the string
and the coerced key; other bases keep `dget_index`. Writes to a string offset
are unchanged (LSB strings are immutable: the `set_index` hook decides).

**How LexerSketch uses it:** compile Mox with

```rust
use bcgen_lang::{Intrinsics, Options};

let opts = Options::new()
    .with_intrinsics(Intrinsics::mox())
    .with_string_offsets("mox.str_offset");
assert_eq!(opts.string_offsets(), Some("mox.str_offset"));
```

and register the host function `mox`.`str_offset(s, k)` in ls-exec with
PHP 8's semantics for everything outside the fast path's domain (see the
table above): `"abc"[1]` and `"abc"[-1]` never reach it (they are `"b"` and
`"c"` inline). The option is off by default, so languages that want bytes
(and existing modules) are unchanged.

### Classes, interfaces, and mixins

HIR's class items (spec v3 §10) compile to LSB structs (LSB §3.1). Mixins
(PHP traits, `ClassDef::mixin`) have no struct: their members are copied into
each class that uses them.

**Types.** Each class and interface is an LSB `struct` named after it (a
repeated name gets `#2`, `#3`, ...). A class's parent is its base class's
struct: one base, LSB's single inheritance (several bases are
`Unsupported::MultipleInheritance`; a chain deeper than 256, bvm-lang's
load-time limit, is [`ClassProblem::TooDeep`](#classproblem)). Its fields are
the instance properties, the parent's first, every one `dyn`: a public or
protected property keeps its slot when a subclass redeclares it (the
redeclaration's default wins), and a private property is a slot of its own
per declaring class, so a parent's private `$x` and a child's public `$x` are
two properties, as in PHP. An interface's struct has no fields: it carries
the interface's token, constants, and `::test`.

**Names.** Properties keep their plain names, so records, hooks, and hosts
see `x`. Everything callable gets a name no property can have:

| Member | Public, protected | Private, declared in `C` |
|---|---|---|
| property | `x` | `C::$x` |
| method | `m()` | `C::m()` |
| static property accessor (`static::$x`) | `$x()` | `C::$x()` |
| constant accessor (`static::X`) | `const X()` | `C::const X()` |

plus the synthetic methods every struct has: `::new` (allocate and set the
property defaults, or raise for an abstract class or interface), `::test`
(the class's `instanceof`), `::class` (its name), and `::is I` for each
interface `I` it implements (an empty marker; subclasses inherit it). A
destructor is therefore `__destruct()` in the module: see
[`Compiled::destructor`](#compiled).

**Methods and receivers.** A method is an **instance method** when its first
HIR parameter is a `Receiver` (its pattern binds `$this`); any other method is
static and gets a hidden first parameter. Either way the receiver is
register 0: the instance, or for a static method the class's **token** (an
uninitialized instance the start function makes per class and interface) or
the instance it was called through. `static::` looks members up on the
receiver, so late static binding needs no hidden class argument. One LSB
function is compiled per method of a class, and one per class using a mixin's
method; subclasses reach inherited methods through LSB's method lookup.

| Call | LSB |
|---|---|
| `$o->m(args)` | the scope's private `C::m()` when the object has it (`has_prop`); else `has_prop o, "m()"`, the [visibility tests](#visibility), `get_prop`, and `dcall`/`dcall_shape` with `o` first. An object without the method reads `m()` once more, so the `get_prop` hook (PHP's `__call`) or `UndefinedProperty` applies; a receiver that is not an object (a map of closures, a host value) reads the plain name `m`, as 0.3 did |
| `C::m(args)`, a static method | a direct `call` of the method's function, `C`'s token as the receiver, the arguments arranged at compile time |
| `C::m()`, an instance method, from a method of a subclass of `C` | a direct call with `$this` (PHP's `A::m()` parent call); elsewhere it raises "Non-static method C::m() cannot be called statically" |
| `self::m()`, `parent::m()` | a direct call, forwarding the current receiver (PHP's forwarding call) |
| `static::m()` | `get_prop` on the receiver, then a dynamic call |
| `$o->$m(args)` | the [by-name dispatch](#members-by-run-time-name) |

**Properties.** `$o->x` is `get_prop`; `$o->x = v` is `set_prop`; nested
writes, references, and reference bindings use `dsep_prop`, `dref_prop`, and
`dbind_prop`; each picks its name by the scope's plan (below). Writing a
property no class declares raises `UndefinedProperty` unless a `set_prop`
hook is bound: LSB structs have fixed fields, so PHP's dynamic properties are
the host's.

**Static properties and constants.** A static property is a global per
(class, property) holding a reference, made by the start function in the
class's scope; an inherited one is its declaring class's global (PHP shares
it), a mixin's is the using class's own. `C::$x`, `self::$x`, and `parent::$x`
read and write that global; `static::$x` calls the receiver's `$x()`
accessor, which returns the reference. A constant is a global per (class,
constant): a literal is an LSB constant initializer, anything else is
computed by the start function in the class's scope, classes in canonical
order. Interface constants are reachable through every implementing class.
A member a class does not have raises PHP's error where the access runs
("Call to undefined method C::m()", "Undefined constant C::X", "Access to
undeclared static property C::$x").

**`new`, `instanceof`, `clone`.** These are [class operations](#classop) of
the intrinsic table (`Intrinsics::mox()` maps `mox.new`, `mox.instanceof`, and
`mox.clone`; a call of the extern `mox.new`, which the Mox sketch's
`new_object` template writes, compiles the same way). The class is the
intrinsic's type argument (`mox.instanceof<I>(x)`; HIR can name an interface
in an expression no other way) or the operand, a path to a class of the unit,
`C::class`, `self::class`, `parent::class`, or `static::class` (HIR has no
bare `self` or `static` path: a lowering writes `new static` as
`new (static::class)`).

- `new C(args)`: `C`'s `::new` (`new_struct`, then each property default,
  evaluated in the scope of the class that declared it), then the constructor
  ([`Options::constructor`](#options), `__construct`), found up the chain,
  called directly with the instance and the arguments; its visibility is
  checked first. Without a constructor the arguments are evaluated and
  dropped. An abstract class, an interface, or a mixin raises "Cannot
  instantiate ..." before the arguments are evaluated. The result is the
  instance.
- `new $v(args)` with a class value only known at run time: `<class_of>`
  finds the token (an object of a unit class is its own; a string is looked up
  in the module's name registry, exact and case-sensitive, the first class of
  a name winning), then its `::new` and its constructor by the scope's plan,
  called dynamically. A name the unit does not declare goes to the host
  function (`mox.new`) with the value and the positional arguments (named or
  spread ones raise `ArgumentError` there).
- `x instanceof C`: `is_type` for a class (descendants included, nil false);
  for an interface, `x` is an object with the `::is I` marker; a mixin is
  never instantiated (false). A run-time class value calls its token's
  `::test`, or the host function when the unit does not declare it.
- `clone x`: an instance of a unit class is `dup`ed (a new identity; array
  properties are shared copy-on-write, so writes through either separate) and
  the clone method ([`Options::clone_method`](#options), `__clone`) runs on the
  copy when its class has one, by the scope's plan. Anything else goes to the
  host function.
- `C::class` is the class's name (a string); `static::class` calls the
  receiver's `::class`.

**Type tests and exceptions.** A type test pattern (a `catch` arm) whose type
names a class or interface of the unit tests the instance as `instanceof`
does; unions (`catch (A | B $e)`), intersections, and nullables combine class
tests with kind tests. `throw` raises any value, objects included; an object
is caught by its class or interface, and LSB runtime errors (error values,
not objects) only by a test that admits every kind (Mox's `Throwable`, which
the sketch maps to `any`). A type naming a class the unit does not declare is
`Unsupported::ClassTest`.

**Destructors.** LSB format 2 has no destructor flag (ISSUES P44). The
destructor method ([`Options::destructor`](#options), `__destruct`) must be an
instance method without parameters ([`ClassProblem::BadDestructor`](#classproblem));
[`Compiled::destructor`](#compiled) gives its LSB name, `__destruct()`, which
the host passes to bvm-lang's `Vm::set_destructor`. Under bvm-lang's
reference-counting profile (`Memory::Rc`, the language's `[runtime] memory =
"rc"`), compile with [`Options::with_reference_counting`](#options) so objects
die where PHP frees them: dead temporaries holding a reference are cleared
and variables live until the function returns (`tests/classes.rs` checks
PHP's order: reassignment, then the end of the script).

#### Visibility

Visibility is decided where PHP decides it, and a violation raises
`TypeError` (E0100, PHP's `Error`) with PHP's message as the payload.

- **Through a static path** (`C::m()`, `C::X`, `C::$x`, `self::`, `parent::`,
  `new C`): at compile time, against the scope of the code (a method's class;
  a closure's is the class it was created in; module code has none). The
  `raise` sits where the access is.
- **Through an object** (and `static::`): at run time, by a plan per scope
  and name. When the scope declares a private member of that name, `has_prop`
  tests the object for the scope's private slot first (PHP's
  `zend_get_parent_private_*`). Then the object's class is tested against
  the classes declaring the name whose visible member the scope may not
  reach, deepest first (`is_type`), raising for a protected member the scope
  is unrelated to (PHP's prototype root for a method, the declaring class for
  a property) or for a method that is only private elsewhere; and the public
  name is used. A private property of an ancestor read from outside is an
  undefined property (PHP's dynamic-property path), not an error. A name
  every class declares public needs no tests at all.
- **Many declarations of one name.** When more than four classes declare a
  name (say, every model class redeclares `protected $table`), a method's
  plan lists only its own class's lineage (its ancestors and descendants
  declaring the name), behind one `is_type` test that the object is an
  instance of the method's class, which `$this` always is. Any other object
  calls a function shared by the whole module for that name, `<vis name>(obj,
  scope token, scope name)`, which tests every declaring class once and asks
  `is_type` of the scope's token for a protected member. Code and compile
  time stay linear in the number of classes (`benches/bench.rs` compiles
  1,000 classes that all redeclare six protected properties in 72 ms).

The messages are PHP's ("Cannot access private property C::$x", "Call to
protected method C::m() from scope D", "... from global scope"), except that a
protected property's names its declaring class where PHP names the object's
class. `tests/class_model.rs` compares every method call and property read,
from every scope, on random hierarchies, with a model transcribed from PHP
8's `zend_std_get_method` and `zend_get_property_offset`.

#### Mixins (PHP traits)

A class's members are its own, then those of the mixins it uses, flattened as
PHP 8's `zend_traits_copy_functions` and `zend_add_trait_method` do. For each
used mixin in order, each of its methods: every `as` rule with a new name
copies the mixin's own method under that name (the rule's visibility, else
the method's); the method itself is copied unless an `insteadof` rule excludes
it from this mixin, with the visibility of the last name-less `as` rule for it
from this mixin. A rule without a mixin applies to the one used mixin that
has the method. The class's own members win; when two mixins give a name
(PHP rejects that without `insteadof`) the first wins. Properties, static
properties, and constants are copied too. A mixin that uses mixins is
flattened first; a cycle is [`ClassProblem::Cycle`](#classproblem). A mixin's
methods are compiled once per using class, so `self::` in them is the using
class and their static properties are its own. `tests/mixins.rs` compares
every member, on random graphs of mixins and rules PHP accepts, with a model
of those two PHP functions. (resolve-lang 0.4's member tables differ from
PHP on some visibility rules; that test counts and prints the differences.)

#### Members by run-time name

`$o->$name`, `$o->$name = v`, and `$o->$m()` call a function generated per
scope: on an object, a binary search over the unit's property (or method)
names, each leaf the scope's ordinary access to that name; a name no class
declares raises `UndefinedProperty` with the name as the payload. Any other
value keeps LSB's `dget_index`/`dset_index`. Nested writes and references
through a run-time name on an object (`$o->$n[] = 1`, `&$o->$n`) still use
`dsep_index`/`dref_index`, which raise `TypeError` on an object. Without
classes in the unit, the 0.3 instructions are emitted unchanged.

#### PHP class semantics: covered and refused

| PHP | 0.4 | How, or what is missing |
|---|---|---|
| Classes, single inheritance, abstract classes | compiled | LSB structs; `new` of an abstract class raises |
| `final` | recorded, not enforced | PHP rejects a violation at compile time; HIR records it, bcgen does not check it |
| Interfaces, interface inheritance, `instanceof`, interface constants | compiled | marker methods; named by a type argument |
| Traits: `use`, `insteadof`, `as` (aliases, visibility), trait properties, statics, constants | compiled | flattened per using class (PHP's algorithm) |
| `new`, constructors, private and protected constructors | compiled | |
| Constructor property promotion | not in HIR | `Param` has no property marker: the lowering must write the property and the assignment (Mox: the `mox_lower` hook) |
| Instance properties and defaults | compiled | defaults evaluated per instance |
| Typed properties (uninitialized state, coercion), `readonly` | not in HIR | read as `null`; HIR's `FieldDef` has no readonly flag and types are erased |
| Dynamic (undeclared) properties | refused at run time | `UndefinedProperty`, or the `set_prop`/`get_prop` hooks |
| `$this`, methods, static methods, `self::`, `parent::`, `static::` | compiled | late static binding through the receiver |
| Static properties, class constants, `static::$x`, `static::X` | compiled | |
| `public`, `protected`, `private` on properties, methods, constants, static properties, constructors | compiled, checked at run time | see [Visibility](#visibility) |
| Exceptions as objects, `catch` by class or interface, multi-catch | compiled | non-objects still throw |
| `Exception`, `Error`, `Throwable` and their methods | not here | a runtime library (Mox's `mox.core`) |
| `__destruct` | compiled | the host calls `Vm::set_destructor(Compiled::destructor())` |
| `__clone` | compiled | |
| `__get`, `__set`, `__isset`, `__unset`, `__call`, `__callStatic`, `__toString`, `__invoke` | through LSB hooks only | the host's hook functions |
| `$o->$name`, `$o->$m()` | compiled (reads, writes, calls) | nested writes and references through a run-time name on an object raise `TypeError` |
| `new $name`, `$x instanceof $name` | compiled | names are exact and case-sensitive (Mox OQ-1) |
| `C::class`, `static::class`, `new static`, `new self`, `new parent` | compiled | as `new (static::class)` |
| `$cls::m()`, anonymous classes, enums, first-class callables, `Closure::bind` | not compiled | lowering (`mox_lower`); enums are sums (`Unsupported::Record`) |
| Calling an abstract method statically | raises | "Cannot call abstract method" |
| A constant expression reading a constant declared later | deviation | constants are computed in canonical order (PHP evaluates lazily) |
| A class declared inside a function or `if` | deviation | declared when the module loads |
| Case-insensitive class and method names | not compiled | Mox is case-sensitive (OQ-1) |

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
    pub fn with_ignore_extra(self, bool) -> Self;          // PHP: extra arguments dropped
    pub fn with_string_offsets(self, intrinsic: &str) -> Self;
    pub fn with_constructor(self, Option<&str>) -> Self;   // default "__construct"
    pub fn with_destructor(self, Option<&str>) -> Self;    // default "__destruct"
    pub fn with_clone_method(self, Option<&str>) -> Self;  // default "__clone"
    pub fn with_reference_counting(self, bool) -> Self;    // code for bvm-lang's Memory::Rc
    pub fn arrays(&self) -> ArraySemantics;
    pub fn keys(&self) -> KeyCoercion;
    pub fn body(&self) -> BodyMode;
    pub fn file(&self) -> &str;
    pub fn host_module(&self) -> &str;
    pub fn hooks(&self) -> &[(Hook, String, String)];
    pub fn intrinsics(&self) -> &Intrinsics;
    pub fn max_instructions(&self) -> u64;
    pub fn ignore_extra(&self) -> bool;
    pub fn string_offsets(&self) -> Option<&str>;
    pub fn constructor(&self) -> Option<&str>;
    pub fn destructor(&self) -> Option<&str>;
    pub fn clone_method(&self) -> Option<&str>;
    pub fn reference_counting(&self) -> bool;
}
```

`with_hook` binds an LSB hook (LSB §5.8) to a host function with the hook's
signature (format 2's `pow`, `abs`, and `call_shape` hooks included); a
language supplies its own semantics this way (PHP's numeric strings in
arithmetic, `get_index` returning `null` for a missing key, `spawn` into a
scheduler, ...). With hooks bound, the compiler copies arrays more
conservatively (a hook may return an operand). `with_intrinsics` sets the
[intrinsic table](#intrinsics).

- `with_ignore_extra(true)`: extra positional arguments to user functions,
  closures, and methods are evaluated and dropped (PHP, ISSUES P34); the
  default raises `ArgumentError` (Python). Every LSB parameter list carries
  `ignore_extra`, so dynamic calls agree.
- `with_string_offsets(name)`: see [String offsets](#string-offsets). The
  entry must exist and take two operands and must not be a class operation,
  or compiling fails with `CompileError::InvalidOption { option:
  "string_offsets" }`.
- `with_constructor`, `with_destructor`, `with_clone_method`: the magic
  method names of [classes](#classes-interfaces-and-mixins) (`None` turns the
  behaviour off: no constructor call, no destructor reported, no clone
  method).
- `with_reference_counting(true)`: code for bvm-lang's reference-counting
  profile: dead temporaries and call windows holding a reference are cleared
  (one `load_nil` each) and variables keep their registers until the function
  returns, so destructors run where PHP runs them. Off, a dead temporary keeps
  its object until the register is reused (harmless under the tracing
  collector). The differential test runs every random program with it too.

```rust
use bcgen_lang::{ArraySemantics, Intrinsics, KeyCoercion, Options};
use bytecode_lang::Hook;

let o = Options::new()
    .with_arrays(ArraySemantics::Reference)
    .with_keys(KeyCoercion::None)
    .with_host_module("env")
    .with_hook(Hook::Spawn, "ls.async", "spawn")
    .with_intrinsics(Intrinsics::mox())
    .with_ignore_extra(true)
    .with_reference_counting(true)
    .with_max_instructions(1 << 20);
assert_eq!(o.hooks().len(), 1);
assert!(o.ignore_extra() && o.reference_counting());
assert_eq!(o.destructor(), Some("__destruct"));
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
    pub fn mox() -> Self;    // core + the Mox sketch's, mox.new and mox.str_offset (43)
    pub fn with_lsb(self, name: &str, op: LsbOp) -> Self;
    pub fn with_host(self, name: &str, arity: Arity, module: &str, func: &str) -> Self;
    pub fn with_fast(self, name: &str, fast: Fast, module: &str, func: &str) -> Self;
    pub fn with_class(self, name: &str, op: ClassOp, module: &str, func: &str) -> Self;
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
assert!(matches!(def.lowering(), Lowering::Class { .. }));
assert!(matches!(t.get("mox.cast_object").unwrap().lowering(), Lowering::Host { .. }));
```

## `Lowering`

```rust,ignore
#[non_exhaustive]
pub enum Lowering {
    Lsb(LsbOp),
    Host { module: String, name: String },
    Fast { fast: Fast, module: String, name: String },
    Class { op: ClassOp, module: String, name: String },
}
impl Lowering { pub fn host(&self) -> Option<(&str, &str)>; }
```

How an intrinsic compiles (see [Named intrinsics](#named-intrinsics)); `host`
is the host function it may call, which the embedder registers with
`bvm_lang::Host::register(module, name, ..)`. A `Class` entry also compiles a
call of the extern path of the same name (lowering templates call host
symbols, not intrinsics: lower-lang 0.4, ISSUES P40), and takes its class
from the intrinsic's type argument when there is one.

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
    NumIdentity, IntBitNot, ToInt, ToFloat, ToStr, ToBool, ToArray, StrOffset,
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
assert_eq!(Fast::StrOffset.arity(), Arity::exact(2));
```

`ToInt`'s domain includes floats since 0.4 (PHP's modular conversion,
[above](#the-mox-intrinsics)); `StrOffset` is PHP's `$s[i]` for an in-range
integer offset ([String offsets](#string-offsets)).

## `ClassOp`

```rust,ignore
#[non_exhaustive]
pub enum ClassOp { New, InstanceOf, Clone }
impl ClassOp { pub const fn arity(self) -> Arity; }   // New 0 to 255, InstanceOf 1 to 2, Clone 1
```

A class operation ([`Lowering::Class`](#lowering)): inline for the unit's
classes, the host function for the rest. `New`: the class is the type
argument or operand 1, then the constructor's arguments (spread and named
included); `InstanceOf`: the value, then the class unless it is the type
argument; `Clone`: the value. See
[Classes, interfaces, and mixins](#classes-interfaces-and-mixins).

```rust
use bcgen_lang::{Arity, ClassOp, Intrinsics, Lowering};

assert_eq!(ClassOp::InstanceOf.arity(), Arity::range(1, 2));
let t = Intrinsics::new().with_class("rt.new", ClassOp::New, "rt", "new");
assert!(matches!(t.get("rt.new").unwrap().lowering(), Lowering::Class { op: ClassOp::New, .. }));
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
    pub fn class_type(&self, class: ItemId) -> Option<TypeId>;          // a class's or interface's struct
    pub fn method(&self, class: ItemId, method: ItemId) -> Option<FuncId>;
    pub fn destructor(&self) -> Option<&str>;                          // for Vm::set_destructor
}
```

The module, its entry points, the function compiled for each function item
(its parameters, then the presence mask when a parameter has a default; it
carries the parameter list, so a host can call it typed with `call` or bind
arguments to it dynamically; a generator's returns the coroutine), the HIR
node of every instruction, and for classes: each class's struct type, the
function compiled for each method of a class (receiver first; a mixin's
method has one per using class, an abstract method none), and the LSB name of
the destructor when a class defines one (`__destruct()`), which the host
passes to bvm-lang's `Vm::set_destructor`.

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
    Class { problem: ClassProblem, node: NodeRef, span: Span },
    InvalidOption { option: &'static str },
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
124 jump targets; `Class` a class graph or member the module cannot hold or
PHP rejects ([`ClassProblem`](#classproblem)); `InvalidOption` an option
naming something unusable (`string_offsets`); `BudgetExceeded` the
instruction budget (class layouts, interface closures, and mixin copies are
charged to it too); `Build` an LSB format limit (`bytecode_lang::BuildError`). `Display` names the problem and
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

## `ClassProblem`

```rust,ignore
#[non_exhaustive]
pub enum ClassProblem {
    Cycle, TooDeep { limit: u32 }, TooManyFields { limit: u32 },
    NotAClass, NotAnInterface, NotAMixin, BadDestructor,
}
```

Why a class graph does not compile ([`CompileError::Class`](#compileerror)):
an inheritance or mixin `Cycle`; a chain deeper than 256 classes
(`TooDeep`, bvm-lang's `MAX_INHERITANCE_DEPTH`); more than 65,536 property
slots in one class, its ancestors' included (`TooManyFields`: LSB field slots
are 16 bits); a base that is not a class (`NotAClass`), an implemented
interface that is not an interface (`NotAnInterface`), a used mixin that is
not a mixin (`NotAMixin`); a destructor that takes parameters or is static
(`BadDestructor`).

```rust
use bcgen_lang::ClassProblem;

assert_eq!(ClassProblem::TooDeep { limit: 256 }.to_string(), "an inheritance chain deeper than 256 classes");
```

## `Unsupported`

```rust,ignore
#[non_exhaustive]
pub enum Unsupported {
    Class, Record, Reference, RefPlace, VarVar, Intrinsic, Asm, BigInt,
    ForeignUnit, TypeDirected, ExternValue, ExternArgs, Conversion, Cast, Pattern,
    Impl, MultipleInheritance, ClassValue, MixinMember, ClassTest, AmbiguousClass, StaticRef,
}
impl Unsupported { pub const fn describe(self) -> &'static str; }
```

A form 0.4 does not compile (`describe`, also `Display`). `Impl` and
`Record` arrive with typed fast paths in 0.5; `MultipleInheritance` needs
several struct parents, which LSB does not have; `ClassValue` is a class name
used as a plain value (outside `new`, `instanceof`, type tests, and member
access); `MixinMember` a mixin's member reached through the mixin itself
(`T::m()`, deprecated in PHP 8.1); `ClassTest` a type test against a class
the unit does not declare; `AmbiguousClass` a member path naming one of two
same-named classes that both reach the member; `StaticRef` binding
`static::$x` to a reference; `Class` a receiver parameter outside a member
(which valid HIR does not have). `Reference` (pointers), `RefPlace` (a
reference to an appended element or a variable variable), `VarVar` (no named
frames), and `Intrinsic` (atomics, volatile, fences) have no meaning in LSB's
dynamic profile; `ExternValue` and `ExternArgs` need a host function's
parameter list, which the compiler does not know; `Asm` is for native
backends.

```rust
use bcgen_lang::Unsupported;

assert!(Unsupported::Impl.describe().contains("0.5"));
assert_eq!(Unsupported::Asm.to_string(), "inline assembly (native backends only)");
```

## Feature flags

| Feature | Default | Effect |
|---|---|---|
| `std` | yes | Forwards `std` to the family crates. Without it the crate is `no_std` + `alloc`. |

## Stability

0.4.0 is a pre-release surface: names and signatures may change across 0.x,
each change recorded in the CHANGELOG. The compiled code's semantics are the
ones this file states, checked by the differential, binding, intrinsic, and
end-to-end tests; changes to them are breaking and recorded.
