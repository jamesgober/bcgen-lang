<h1 align="center">
    <img width="90px" height="auto" src="https://raw.githubusercontent.com/jamesgober/jamesgober/main/media/icons/hexagon-3.svg" alt="Triple Hexagon">
    <br><b>CHANGELOG</b>
</h1>
<p>
  All notable changes to <code>bcgen-lang</code> will be documented in this file. The format is based on <a href="https://keepachangelog.com/en/1.1.0/">Keep a Changelog</a>,
  and this project adheres to <a href="https://semver.org/spec/v2.0.0.html/">Semantic Versioning</a>.
</p>

---

## [Unreleased]

---

## [0.4.1] - 2026-10-13

**Patch: initializers of a nested module.** A computed class constant or
static property, an enum case, and a computed module constant or global
declared inside a nested module (a lowered `namespace`) were still `null`
when the module's own body read them. Found through the LexerSketch Demo
(Mox `namespace A; class S { const C = [1]; } echo count(S::C);` printed
nothing useful; the same code without the `namespace` worked). No API change.

### Fixed

- **The start function ran a nested module's body before the initializers of
  the declarations inside it.** It walked the unit's items in pre-order and
  ran each module's body at the module's own position, ahead of the classes,
  constants, and globals declared in it (and of those of the modules after
  it). A body that read a computed value saw it uninitialized; literal
  initializers were unaffected because LSB constant initializers need no
  code. Every initializer now runs first, in canonical order, and then the
  nested module bodies, in canonical order (`src/analysis.rs`). A unit
  without a nested module compiles to the same bytes as before.

### Added

- `tests/nested_modules.rs`: five programs, each in both body modes
  (`BodyMode::Start` and `BodyMode::Entry`): the root control, a class
  constant and static property in a namespace, a namespace constant and
  global, a doubly nested namespace, and a body reading a later sibling
  namespace's constant. Four of them failed on 0.4.0.
- `tests/common/hb.rs`: `H::module`, a nested module item.

---

## [0.4.0] - 2026-10-12

**Classes.** HIR's classes, interfaces, and mixins (PHP traits) compile to
LSB structs (LSB §3.1) with PHP 8's semantics, pulled forward from the 0.5
plan because Mox needs them for the LexerSketch Demo. Also: PHP's ignored
extra arguments, Mox's `(int)` of an out-of-range float, string offsets
through a named intrinsic, and resolve-lang back in the end-to-end tests.
Executes on bvm-lang `=2.0.0-alpha.4`.

### Breaking

- **Classes compile.** A unit with class, interface, or mixin items, receiver
  parameters, member paths, `new`, `instanceof`, or `clone` no longer fails
  with `Unsupported::Class`; `Unsupported::Class` now means only a receiver
  parameter outside a class or mixin member.
- **`Intrinsics::mox()`**: `mox.instanceof` and `mox.clone` are class
  operations (`Lowering::Class`, inline for the unit's classes, the host
  function only for other values; 0.3: host functions); `mox.new` (class
  operation) and `mox.str_offset` (fast path) are added; 43 entries.
- **Mox `(int)` of a finite float outside the `i64` range wraps modulo 2^64**
  like PHP 8's `zend_dval_to_lval` (NaN and infinities give 0); 0.3
  saturated (`Fast::ToInt`, ISSUES P41).
- **Dev-dependencies**: bvm-lang `=2.0.0-alpha.4`; resolve-lang `0.4`.

### Added

- **Classes** (`docs/API.md`, "Classes, interfaces, and mixins"): one LSB
  struct per class and interface; single inheritance up to bvm-lang's 256
  levels; instance properties with defaults (a private property is a slot
  per declaring class); instance and static methods (the receiver, or the
  class's token, in register 0); `self::`, `parent::`, and late-bound
  `static::` through the receiver; static properties (a reference per
  declaring class, shared by subclasses) and class constants (literal or
  computed in the class's scope at load); interfaces as marker methods, with
  their constants; mixins flattened per using class by PHP's
  `zend_traits_copy_functions` (aliases, `insteadof`, visibility changes,
  mixin properties, statics, and constants).
- **`new`, `instanceof`, `clone`** as class operations of the intrinsic table
  (`ClassOp`, `Intrinsics::with_class`, `Lowering::Class`): constructors found
  up the chain and called directly, class values known only at run time
  through a name registry, `__clone`, `C::class`/`static::class`, and the host
  function for anything the unit does not declare.
- **Visibility** checked where PHP checks it (compile time for static paths,
  per-scope run-time plans through objects), each violation a `TypeError`
  (E0100) with PHP's message; members a class does not have raise PHP's
  "undefined" errors where the access runs.
- **Exceptions as objects**: `catch` by class, interface, union, or
  intersection; non-objects still throw and catch as before.
- **Destructors**: `Compiled::destructor()` names the destructor method
  (`__destruct()`) for bvm-lang's `Vm::set_destructor`;
  `Options::with_reference_counting` clears dead temporaries so objects die
  where PHP frees them under `Memory::Rc`.
- **Members by run-time name**: `$o->$name` reads and writes and `$o->$m()`
  calls, through a per-scope dispatch function.
- `Options::with_constructor`, `with_destructor`, `with_clone_method`,
  `with_reference_counting`, `with_ignore_extra`, `with_string_offsets`, and
  their getters; `Compiled::class_type`, `Compiled::method`,
  `Compiled::destructor`; `ClassOp`; `ClassProblem`;
  `CompileError::Class` and `CompileError::InvalidOption`;
  `Unsupported::Impl`, `MultipleInheritance`, `ClassValue`, `MixinMember`,
  `ClassTest`, `AmbiguousClass`, `StaticRef`; `Fast::StrOffset`.
- **`ignore_extra`** (ISSUES P34): `Options::with_ignore_extra(true)` gives
  every parameter list LSB's `ignore_extra`, so extra arguments to user
  functions are dropped as PHP drops them; direct calls arranged at compile
  time follow the same rule.
- **String offsets through an intrinsic** (ISSUES P38):
  `Options::with_string_offsets("mox.str_offset")` routes indexed reads of a
  string through the table entry (a fast path returns the one-byte string for
  an in-range offset, negative offsets from the end) instead of LSB's byte
  read.
- `tests/classes.rs` (15 programs end to end, resolved by resolve-lang 0.4),
  `tests/class_model.rs` (dispatch and visibility against a model of PHP 8's
  lookups), `tests/mixins.rs` (flattening against a model of PHP's trait
  copying), `tests/hostile_classes.rs` (random class graphs never panic),
  `tests/features_0_4.rs`, `examples/classes.rs`, class benchmarks.

### Changed

- `tests/e2e.rs` resolves its Mox program with resolve-lang 0.4 again
  (ISSUES P35), not a resolver written in the test.

---

## [0.3.0] - 2026-10-12

HIR spec v3 (hir-lang 0.4) to **LSB format 2** (bytecode-lang 0.3), which
bvm-lang 2.0.0-alpha.3 executes, with the named intrinsics Mox needs. This
release unblocks the LexerSketch Demo chain (lang-forge → lower-lang →
resolve-lang → typeck-lang → bcgen-lang → bvm-lang): it is on the hir-lang
version typeck-lang 0.3 uses, emits the bytecode format the VM reads, and
compiles every intrinsic of the Mox sketch.

### Breaking

- **hir-lang 0.4 and bytecode-lang 0.3.** `compile` takes a hir-lang 0.4
  `Hir`; `Compiled::module` is an LSB format 2 module (bytecode-lang 0.3);
  `Options::with_hook` takes bytecode-lang 0.3's `Hook`. Format 1 modules are
  no longer produced.
- **The calling convention is LSB §5.15's.** Every function item and closure
  is one LSB function carrying its **parameter list**; function values and
  dynamic calls (`dcall`, `dcall_shape`) bind through it in the VM. The 0.2
  argument packets, the `<name>$dyn` entries, and the closures' `(dyn, dyn)`
  signature are gone: a closure's function takes its parameters and presence
  mask like a function item's.
- **Binding errors are `ArgumentError` (E0114) at the call**, as LSB raises
  them (0.2: `TypeError` at the callee's definition): a positional argument
  after a named one, too many or too few arguments, an unknown or repeated
  name.
- **HIR `rest` parameters are LSB `rest_map`** (PHP 8.1's `...$args`): with
  no named-rest parameter, unknown named arguments are collected into the
  rest map under their names instead of raising.
- **A `match` with no matching arm raises `NoMatch` (E0200)** with the
  scrutinee as payload (HIR v3 §8.10); 0.2 evaluated it to `nil`. Lowerings
  that want `nil` add a final wildcard arm.
- **`OpKind::Not` is logical only** (`dnot`, HIR v3); the bitwise complement
  is `OpKind::BitNot` (`dbit_not`). `abs` is LSB's `dabs`: a non-number goes
  to the `abs` hook when one is bound.
- **Shared variables live in LSB references** (`new_ref`, kind `reference`),
  not cells, so they can be bound into array slots.
- **Named intrinsics are table-driven.** `Options::new()` uses
  `Intrinsics::core()` (the 0.2 built-ins plus coroutine controls); a name
  outside the table is the new `CompileError::UnknownIntrinsic` (0.2:
  `Unsupported::Intrinsic`), and `CompileError::IntrinsicArity` carries
  `arity: Arity` and `found: u32` (was `expected: u32`).
- **`CompileError`** gains `UnknownIntrinsic` and `TooManyArgs`;
  `TooManyParams` allows 255 parameters without defaults (64 with one, as
  before). **`Unsupported::Coroutine` is removed** (coroutines compile), and
  `Unsupported::RefPlace` now covers only references to appended elements,
  variable variables, and non-places.
- **Dev-dependencies**: bvm-lang `=2.0.0-alpha.3`; resolve-lang is dropped
  (resolve-lang 0.3 is built on hir-lang 0.3, so it cannot resolve a 0.4
  unit).

### Added

- **Generators**: functions and closures with `YIELD` make coroutines
  (`coro_new` of a generated body; a generator closure's captures pass as
  leading arguments); keyed `yield` (`yield_kv`) and automatic keys
  (`yield`); `yield from` by the delegation loop of HIR v3 §8.7 (keys
  preserved, sent values forwarded with `resume`, thrown errors with
  `resume_throw`, an inner `await` passed through, the return value as the
  result; arrays and other iterables yielded entry by entry).
- **`await`** and **`spawn`** (through the module's `spawn` hook); `ASYNC`
  functions compile as ordinary functions on LSB's stackful model.
- **`let_place`** (HIR v3 §8.2): a place's operands evaluated once into
  registers; reads, writes, references, and further steps through the alias,
  so `.=` through a host operator, `++`, and `??=` evaluate their place once.
  **Assignments evaluate to the value written.**
- **PHP references into elements and properties**: `$x = &$a[k]`
  (`dref_index`/`dref_prop`), `$a[k] = &$x` (`dbind_index`/`dbind_prop`),
  element place arguments to by-reference parameters, and run-time
  by-reference decisions for dynamic calls (`dparam_ref`,
  `dparam_ref_named`), each place's operands evaluated once.
- **Copy-on-write separation that copies only what is shared**: nested
  writes separate with `dsep_index`/`dsep_prop` (LSB §5.16).
- **OPS v2**: `pow` (`dpow`, every overflow policy, `NegativeExponent`),
  `bit_not`, `shift = saturate`, `abs` through `dabs`.
- **Union and intersection types** in type-test patterns and casts (a
  checked identity), nested to any depth.
- **The intrinsic table** (decision D27): `Intrinsics` (`new`, `core`, `mox`,
  `with_lsb`, `with_host`, `with_fast`, `get`, `len`, `is_empty`, `iter`),
  `IntrinsicDef`, `Lowering` (an LSB sequence, a host function, or a guarded
  fast path over one), `LsbOp`, `Fast`, `Arity`; `Options::with_intrinsics`
  and `Options::intrinsics`. `Intrinsics::mox()` maps every intrinsic of
  `mox.lsf` (`concat`, `concat_n`, `mod`, `pow`, `shl`, `shr`, `xor`,
  `loose_eq`, `loose_ne`, `identical`, `not_identical`, `lt`, `le`, `gt`,
  `ge`, `spaceship`, `to_number`, `bit_not`, `cast_int`, `cast_float`,
  `cast_string`, `cast_bool`, `cast_array`, `cast_object`, `instanceof`,
  `clone`), each documented with its PHP semantics in `docs/API.md`.
- Core intrinsics `resume`, `resume_throw`, `coro_close`, `coro_key`,
  `coro_result`, `coro_status` (a runtime's generator object lowers to them),
  and `err_code`, `err_payload` (a runtime's exception mapping reads a caught
  error's code and payload with them).
- Hooks `pow`, `abs`, and `call_shape` can be bound (`Options::with_hook`).
- Tests: `tests/features_0_3.rs` (every new form on bvm-lang),
  `tests/intrinsics.rs` (every Mox mapping against a PHP-semantics test host;
  each fast path exact on its documented domain and calling the host exactly
  outside it), `tests/binding.rs` (compile-time arrangement against the VM's
  binder on random parameter and argument lists), `tests/hostile.rs` (random
  HIR of every form, repaired by `finish_lenient`, never panics; deep nests
  on a small stack); the reference interpreter and the program generator gain
  `let_place`, `pow`, `bit_not`, saturating shifts, union type tests, LSB
  binding, and `NoMatch`.
- Benchmarks: a generator, `let_place` updates, dynamic calls with named
  arguments, by-reference element arguments, and `mox.loose_eq`'s fast path.
- `examples/mox_intrinsics.rs`.

### Changed

- The end-to-end test resolves its hand-lowered Mox program with a small
  lexical resolver in the test instead of resolve-lang.
- The result of a host call or an intrinsic is copied when stored under PHP
  arrays (a host function may return its argument).

### Fixed

- Nested writes (`$g[$i % 64][] = $i`) no longer copy the inner array on
  every write: 18 times faster on the 100k benchmark.
- A by-value place argument to a dynamic call is read when it is evaluated,
  not when the callee binds it.

### Migration from 0.2

| 0.2 | 0.3 |
|---|---|
| `hir-lang = "0.3"`, `bytecode-lang = "0.2"`, bvm-lang `2.0.0-alpha.1` | `hir-lang = "0.4"`, `bytecode-lang = "0.3"`, bvm-lang `2.0.0-alpha.3` |
| A function value called with `(positional map, named map)` | Called with its arguments (`dcall`/`dcall_shape`; from the host, `Vm::run` with the parameters and the presence mask) |
| Binding error: `TypeError` (E0100) at the function | `ArgumentError` (E0114) at the call |
| `match` without a matching arm is `nil` | It raises `NoMatch` (E0200); add `_ => null` to keep `nil` |
| `OpKind::Not` on an integer (bitwise) | `OpKind::BitNot` |
| `CompileError::IntrinsicArity { expected, .. }` | `CompileError::IntrinsicArity { arity, found, .. }` |
| Unknown named intrinsic: `Unsupported::Intrinsic` | `CompileError::UnknownIntrinsic { name, .. }` |
| `Unsupported::Coroutine` | Removed: coroutines compile |
| Mox operators as host calls | `Options::new().with_intrinsics(Intrinsics::mox())` and the host functions `docs/API.md` lists |

---

## [0.2.0] - 2026-10-09

The foundation: dynamic-profile compilation of resolved HIR (spec v2) to LSB
modules (format version 1) that bvm-lang 2.0.0-alpha.1 loads and runs.

### Added

- `compile` (the Tier-1 entry point), `Compiler` (`new`, `with_locator`,
  `options`, `compile`), `Options` (array semantics, key coercion, body mode,
  line-table file, host import module, hook bindings, instruction budget),
  `ArraySemantics`, `KeyCoercion`, `BodyMode`, `Compiled` (`module`,
  `into_module`, `entry`, `start`, `result_global`, `function`, `origin`,
  `origins`), `Locate`, `Location`, `LineIndex`, `CompileError`, and
  `Unsupported`.
- Functions with positional-only, normal, rest, named-only, and named-rest
  parameters, defaults evaluated per call or once, by-reference parameters;
  direct calls arranged at compile time with a presence mask, and an argument
  packet convention for every function value (closures, items as values).
- Closures with explicit, implicit, and recursive (self-binder) captures, by
  value or through cells; `global` and `static` variables, shared by
  reference through cells when they need to be.
- `if`, blocks with labels, the loop primitive with its step, labeled
  `break`/`continue`, `return`; `match` by a sequential decision procedure
  over literal, binding, identifier, range, tuple, slice, record, or, and
  type-test patterns with guards; let-else.
- Every OPS operation on dynamic values under its policy, `promote` included;
  conversions and casts by dynamic kind.
- Arrays and maps as PHP arrays: value semantics (copy-on-write `dup` on
  transfer, separation on nested writes, auto-vivification) or shared
  references, and PHP key coercion through an emitted `<php_key>` helper.
- `throw`, `try`/`catch`/`finally` by LSB section 4.3's canonical lowering
  (jumps out of `finally` override the pending completion), and `defer`.
- Globals, constants, nested module bodies, and the module body, compiled as
  the start function (or as the entry function, `BodyMode::Entry`).
- Host calls through LSB imports; hooks bound to host functions; named
  intrinsics `concat`, `len`, `truthy`, `lnot`, `type_of`, `iter`,
  `iter_next`.
- An origin table mapping every instruction to its HIR node, LSB line tables
  through a `Locate`, and debug locals for every variable.
- Tests: a reference HIR interpreter and a random program generator for
  differential testing against bvm-lang (both array profiles), property
  tests for loading, round-tripping, origins, and determinism, an end-to-end
  Mox program resolved by resolve-lang, deep-nesting and budget tests, and
  criterion benchmarks for compile throughput and run time.
- `examples/run_script.rs`: the Tier-1 path.

### Changed

- Wires `hir-lang` 0.3, `bytecode-lang` 0.2, and `intern-lang` 1; bvm-lang
  2.0.0-alpha.1 and resolve-lang 0.2 as dev-dependencies.

---

## [0.1.0] - 2026-10-08

Initial scaffold and repository bootstrap. No domain logic yet &mdash; this release establishes the structure, tooling, and quality gates the implementation will be built on.

### Added

- `Cargo.toml` with crate metadata, Rust 2024 edition, MSRV 1.85.
- Dual `Apache-2.0 OR MIT` license files.
- `README.md`, `CHANGELOG.md`, and a documentation skeleton.
- `REPS.md` compliance baseline.
- `.github/workflows/ci.yml` CI matrix; `deny.toml`, `clippy.toml`, `rustfmt.toml`.
- `dev/DIRECTIVES.md` and `dev/ROADMAP.md` (committed engineering standards + plan).

[Unreleased]: https://github.com/jamesgober/bcgen-lang/compare/v0.4.1...HEAD
[0.4.1]: https://github.com/jamesgober/bcgen-lang/compare/v0.4.0...v0.4.1
[0.4.0]: https://github.com/jamesgober/bcgen-lang/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/jamesgober/bcgen-lang/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/jamesgober/bcgen-lang/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/jamesgober/bcgen-lang/releases/tag/v0.1.0
