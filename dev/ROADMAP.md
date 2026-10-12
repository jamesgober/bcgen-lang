# bcgen-lang - Roadmap

> Path from scaffold to a stable 1.0. Hard parts are front-loaded; each phase has hard exit criteria.
> Master plan: ../_lexersketch/ROADMAP.md and ../_lexersketch/NEW-LIBS.md
>
> **Anti-deferral rule:** no listed hard task moves to a later phase unless this file records the move and the reason.

## v0.1.0 - Scaffold (DONE)
Compiles, CI green, structure correct, no domain logic.
- [x] Manifest, README, CHANGELOG, REPS, dual license, CI, deny, clippy, rustfmt, DIRECTIVES, ROADMAP.

## v0.2.0 - Foundation (DONE)
- [x] Dynamic-profile compilation of the HIR core (functions, closures, locals, control flow, calls incl. named/default/variadic, maps/arrays/strings, dynamic ops with OPS policies, exceptions with finally), debug line tables, differential tests against a reference HIR interpreter in tests.
- [x] Wires hir-lang and bytecode-lang; bvm-lang as a dev-dependency for execution tests.

Delivered:
- `compile`, `Compiler`, `Options`, `ArraySemantics`, `KeyCoercion`,
  `BodyMode`, `Compiled`, `Locate`, `Location`, `LineIndex`, `CompileError`,
  `Unsupported`.
- Code generation as an explicit task stack (no recursion over the input),
  registers and call windows pooled per type and shape, binders freed at
  scope end, an instruction budget.
- Calling convention: direct calls arranged at compile time (a presence mask
  for defaults), an argument packet for every function value, unpacked by a
  prologue with the same binding rules; host calls through imports; method
  calls through `get_prop` with the receiver first.
- Closures (explicit, implicit, self-binder captures; by value or by cell),
  shared locals in cells, `global`/`static` (cells when shared by
  reference), by-reference parameters and reference assignment between
  variables.
- Control flow, sequential `match` over every pattern the dynamic profile can
  test, let-else; `throw`, `try`/`catch`/`finally` by the canonical lowering
  (LSB section 4.3), `defer`.
- Every OPS op on `dyn` values with its policy (`promote` included),
  conversions, casts; PHP arrays (value semantics, auto-vivification,
  separation on nested writes, key coercion) or shared references.
- Origins for every instruction, line tables through `Locate`, debug locals.
- Proof: a reference HIR interpreter and a random program generator
  (`tests/common`), the differential test under both array profiles (over a
  million programs before release, mutation-checked), properties (loads in
  bvm, encoding round-trip, origins, determinism), an end-to-end Mox program
  through resolve-lang, deep nesting on a 512 KiB stack, budgets, every
  `Unsupported`.

Dependency wiring (decided here, recorded per the anti-deferral rule):
- **hir-lang 0.3: wired** (the input). **bytecode-lang 0.2: wired** (the
  output, through `ModuleBuilder`/`FunctionBuilder` and labels).
- **intern-lang 1: wired** (symbol text through `Lookup`; hir-lang re-exports
  `Symbol` but not the interner). Same major version hir-lang uses.
- **bvm-lang =2.0.0-alpha.1: dev-dependency** (execution, differential and
  load tests, benches). **resolve-lang 0.2: dev-dependency** (end to end).
- **lower-lang: not wired.** It is not on crates.io; the end-to-end test
  lowers by hand into the HIR a lowering produces and resolves it with
  resolve-lang. A lowering-driven test moves to 0.5 (below).
- **match-lang: not wired** (decision trees are 0.5 scope).

Moved, or not possible on LSB 1 (with the reason):
- `FunctionBuilder::parallel_move` is not used: arguments are evaluated
  straight into call windows, so no move set ever forms a cycle.
- References into array elements and properties (a known by-reference
  parameter given `$a[0]`, `$x = &$a[0]`), `$$name`, a host function used as a
  value, and spread or named arguments to host functions: LSB has no
  reference to a map slot, no named frames, and fixed-arity imports. Each is
  a precise `Unsupported`; reported to the LSB spec owners.
- A place argument naming an element, passed to a function called
  dynamically, goes by value (the callee is unknown when it is sent), and a
  place argument to a dynamic call is read when the callee binds it (after
  every argument). Documented deviations from PHP pending an LSB mechanism.
- Nested writes into a copied array separate the inner array on every write
  (a `dup` plus a copy-on-write store copy each time), because LSB cannot ask
  whether an array is shared: correct, but O(inner size) per nested write. An
  LSB "separate if shared" instruction is requested.
- LSB verifier checks: the verifier lands in bytecode-lang 0.5; until then
  every module is checked by bvm-lang's load-time checks.

## v0.3.0 - HIR 0.4, LSB v2, intrinsics (DONE, 2026-10-12)
Unblocks the LexerSketch Demo chain (lang-forge → lower-lang → resolve-lang →
typeck-lang → bcgen-lang → bvm-lang): the hir-lang version typeck-lang 0.3
uses, the LSB format bvm-lang 2.0.0-alpha.3 reads, and the Mox intrinsics.
- [x] hir-lang 0.4 (HIR spec v3): keyed `yield`, `yield from`, `let_place`,
  assignments as values, `pow`, `bit_not` versus logical `not`,
  `shift = saturate`, `NoMatch`, union and intersection types.
- [x] bytecode-lang 0.3 (LSB format 2): parameter lists and call shapes,
  `dsep_*`, references (`new_ref`, `dref_*`, `dbind_*`, `dparam_ref*`),
  `raise`, `dpow`/`dabs`, and coroutines.
- [x] The intrinsic table (decision D27) with the Mox preset.

Delivered:
- `Intrinsics` (`new`, `core`, `mox`, `with_lsb`, `with_host`, `with_fast`,
  `get`, `len`, `is_empty`, `iter`), `IntrinsicDef`, `Lowering`, `LsbOp`,
  `Fast`, `Arity`; `Options::with_intrinsics`/`intrinsics`;
  `CompileError::UnknownIntrinsic` and `TooManyArgs`.
- The LSB §5.15 calling convention: one LSB function per function item and
  closure, carrying its parameter list (HIR `rest` → `rest_map`); direct
  calls arranged at compile time by the same rules; every other call
  `dcall`/`dcall_shape`, bound by the VM (`ArgumentError` at the call).
- Generators (`coro_new` of a generated body; closures pass their captures
  as leading arguments), keyed and automatic `yield`, `yield from` by HIR
  §8.7's delegation loop (sends with `resume`, throws with `resume_throw`
  from a handler around the re-yield, `await` passed through, iterables
  entry by entry), `await`, `spawn`.
- Evaluated places: `let_place` aliases, assignments, reference assignments,
  and place arguments share one mechanism that evaluates a place's operands
  once and reads, writes (`dsep_*` separation, auto-vivification),
  references (`dref_*`), or binds (`dbind_*`) through them; run-time
  by-reference decisions with `dparam_ref`/`dparam_ref_named`; shared
  variables in LSB references.
- OPS v2 (`dpow`, `dbit_not`, logical `dnot`, `shift = saturate`, `dabs`),
  `NoMatch` raised with the scrutinee, union/intersection kind sets for type
  tests and checked casts (iterative).
- Proof: `tests/features_0_3.rs` (26 end-to-end programs on bvm-lang),
  `tests/intrinsics.rs` (every Mox mapping; fast paths exact on their
  documented domains, host called exactly outside them, over a 37-value pool),
  `tests/binding.rs` (compile-time arrangement against VM binding),
  `tests/hostile.rs` (random HIR of every form through `finish_lenient`;
  200,000 programs before release; 20,000-deep nests on 512 KiB), the
  differential test extended to the new forms (1,320,000 programs before
  release), benchmarks for the new forms.

Decision D27 (the intrinsic table), as built: each named intrinsic is an LSB
sequence (only where LSB's semantics are the language's), a host function the
embedder provides, or a **guarded fast path**: the operand kinds are tested
at run time, the LSB sequence runs on the domain where it is exactly the
language's result, and the host function everywhere else (the sketch's
performance note asks for inline int/float/string fast paths). Fast paths
never invoke a hook, so they do not depend on the hooks a module binds.
`Intrinsics::mox()` maps all 26 intrinsics of `mox.lsf`; `docs/API.md` states
each domain and the PHP semantics ls-exec's host functions must implement.

Dependency wiring (decided here, recorded per the anti-deferral rule):
- **hir-lang 0.4: wired** (typeck-lang 0.3's version). **bytecode-lang 0.3:
  wired** (LSB format 2). **intern-lang 1: wired.**
- **bvm-lang =2.0.0-alpha.3: dev-dependency** (every execution test and
  benchmark).
- **resolve-lang: dropped as a dev-dependency.** The published resolve-lang
  0.3 is built on hir-lang 0.3, so it cannot resolve a 0.4 unit; the
  end-to-end test resolves its hand-lowered program with a small lexical
  resolver in the test. Moved to 0.5: resolve the end-to-end program with
  resolve-lang again once a release on hir-lang 0.4 is published.
- **lower-lang: not wired** (0.3 is on hir-lang 0.3; the lowering-driven test
  stays in 0.5). **typeck-lang, match-lang: not wired** (typed fast paths and
  decision trees are 0.5).

Known deviations and gaps (each a precise behaviour, none a crash):
- **`yield from`'s automatic key.** After a delegation, the outer
  generator's next automatic key continues after the largest integer key the
  inner one yielded, because the re-yield is `yield_kv` and LSB rule 10 moves
  the counter on explicit keys; PHP keeps the outer generator's own counter.
  Needs an LSB way to yield under a key without moving the counter
  (reported to the LSB spec owners).
- **Delegating to an advanced generator.** `yield from` on a generator that
  already yielded resumes it; PHP first re-yields its current value, which
  LSB cannot read back from a coroutine.
- **Generator defaults run lazily.** A generator's parameter defaults and
  patterns are evaluated when its body starts (first resume); PHP binds them
  at the call. Unobservable for PHP's constant-expression defaults except
  `new` in a default.
- **Extra arguments to PHP user functions.** Parameter lists are emitted
  without `ignore_extra`, so too many arguments raise `ArgumentError`
  (Python's rule); PHP ignores them. Needs a language
  switch (HIR or `Options`), planned for 0.5.
- **`dunref_*` is not emitted.** A reference slot made by `$x = &$a[k]` stays
  one after `$x` dies (LSB §5.17's documented divergence); proving the last
  holder gone (the `foreach` by reference case) is 0.5 work with
  match-lang's flow information.
- **Not compiled, precise errors:** a reference to an appended element
  (`$a[] = &$x`: the key is known only after the append), a host function as
  a value or with spread/named arguments (its parameter list is unknown to
  the compiler), a place argument after a spread (passed by value), more than
  255 arguments in one call.
- **LSB verifier**: still bytecode-lang 0.5; every emitted module is checked
  by bvm-lang's load-time checks.

## v0.4.0 - Classes (DONE, 2026-10-12)
Mox needs classes for the LexerSketch Demo, so they moved here from v0.5
(recorded under "Moved" below, per the anti-deferral rule).
- [x] Classes, objects, and interfaces from HIR: inheritance, interfaces as
  type tests, mixins (PHP traits); `new` with constructors; instance
  properties with defaults; methods with `$this`; `parent::`, `self::`,
  `static::`; static properties and methods, class constants, `instanceof`;
  visibility violations raised (`TypeError` with PHP's message); exceptions
  as objects caught by class or interface (non-objects still throw); the
  destructor's name for bvm-lang alpha.4's `Vm::set_destructor`.
- [x] resolve-lang 0.4 back in the end-to-end tests (ISSUES P35).
- [x] `ignore_extra` (ISSUES P34).
- [x] Mox `(int)` of an out-of-range finite float wraps modulo 2^64 like
  `zend_dval_to_lval`; NaN and infinities give 0 (ISSUES P41).
- [x] String-offset reads through a named intrinsic (ISSUES P38), with how
  LexerSketch uses it (`docs/API.md`, "String offsets").

Delivered:
- `ClassOp` (`New`, `InstanceOf`, `Clone`; `arity`), `Intrinsics::with_class`,
  `Lowering::Class`; `Intrinsics::mox()` with `mox.new`, `mox.instanceof`,
  `mox.clone` as class operations, `mox.str_offset` (`Fast::StrOffset`), and
  `mox.cast_object` on the host (43 entries).
- `Options::with_constructor`/`constructor`, `with_destructor`/`destructor`,
  `with_clone_method`/`clone_method`, `with_reference_counting`/
  `reference_counting`, `with_ignore_extra`/`ignore_extra`,
  `with_string_offsets`/`string_offsets`.
- `Compiled::class_type`, `Compiled::method`, `Compiled::destructor`.
- `ClassProblem` (`Cycle`, `TooDeep`, `TooManyFields`, `NotAClass`,
  `NotAnInterface`, `NotAMixin`, `BadDestructor`); `CompileError::Class`,
  `CompileError::InvalidOption`; `Unsupported::Impl`, `MultipleInheritance`,
  `ClassValue`, `MixinMember`, `ClassTest`, `AmbiguousClass`, `StaticRef`
  (`Unsupported::Class` narrowed to a receiver outside a class member).
- The class table (`src/class.rs`): linking, depths and cycles (iterative),
  mixin flattening by PHP's `zend_traits_copy_functions` and
  `zend_add_trait_method`, field layouts, preorder intervals for
  "descends from", and visibility plans (a scope's lineage plus one shared
  `<vis name>` check per name, so plans stay linear in the number of
  classes). Members and synthetic functions (`src/members.rs`), and class
  code generation (`src/codegen/class.rs`): method dispatch, properties,
  statics, constants, `new`/`instanceof`/`clone`, by-name access, class
  type tests, exceptions, and the start function's class prologue.
- Proof: `tests/classes.rs` (15 programs end to end through resolve-lang
  0.4, each against PHP's output: inheritance, overriding, interfaces,
  statics, constants, late static binding, mixins, exceptions by class and
  interface, visibility, destructor order under reference counting, members
  by run-time name), `tests/class_model.rs` (every method call and property
  read from every scope on random hierarchies of up to 12 classes against a
  model of PHP 8's `zend_std_get_method`/`zend_get_property_offset`; 5,000
  hierarchies before release, 300 per `cargo test`), `tests/mixins.rs`
  (flattening against a model of PHP's trait copying; 5,000 before release,
  400 per run), `tests/hostile_classes.rs` (random class graphs, cyclic,
  deep, huge, and malformed, compiled and run under budgets in both memory
  profiles, never a panic; 50,000 before release, 2,000 per run),
  `tests/limits.rs` (chains of 256 load and 257 are `TooDeep`, huge member
  counts and deep chains hit the budget), `tests/intrinsics.rs` (P41
  vectors and 4,000 random float bit patterns against `zend_dval_to_lval`),
  `tests/features_0_4.rs`, `examples/classes.rs`, class benchmarks.

Dependency wiring (decided here, recorded per the anti-deferral rule):
- **hir-lang 0.4, bytecode-lang 0.3, intern-lang 1: wired** (unchanged).
- **bvm-lang =2.0.0-alpha.4: dev-dependency** (alpha.4 adds
  `Vm::set_destructor` and the reference-counting profile the destructor
  tests use).
- **resolve-lang 0.4: dev-dependency again** (its PHP policy resolves the
  end-to-end and class tests). Two of its gaps are worked around in the
  tests and reported (below).
- **lower-lang: not wired** (see "Moved"). **typeck-lang, match-lang: not
  wired** (typed fast paths and decision trees stay in 0.5).

Moved:
- **Classes, interfaces, and mixins: from v0.5 to v0.4** (Mox needs them for
  the Demo). Declared records and sums, and `impl` blocks, stay in v0.5
  (`Unsupported::Record`, `Unsupported::Impl`).
- **A lowering-driven end-to-end test stays in v0.5.** lower-lang 0.4 emits
  no `Receiver` parameter for Mox methods (its `implicit_receiver` is still
  pending), so a Mox method lowered by it has no `$this` and an instance
  method cannot work end to end through lower-lang yet. Needed: lower-lang
  emitting `ParamKind::Receiver` first in every instance method.

Missing pieces, compiled as far as possible and refused precisely (never
faked); each is in `docs/API.md`'s "covered and refused" table:
- **HIR**: `Param` has no promoted-property marker (constructor promotion is
  the lowering's: a property plus an assignment); `FieldDef` has no
  `readonly` flag and property types are erased (no uninitialized state); no
  zero-segment `self`/`static` path (a lowering writes `new static` as
  `new (static::class)`); an interface cannot be named in value position
  (`instanceof` takes it as the intrinsic's type argument); `final` is
  recorded but not enforced.
- **LSB**: no destructor flag in format 2 (ISSUES P44: the host passes
  `Compiled::destructor()` to `Vm::set_destructor`); structs have fixed
  fields (PHP's dynamic properties go to the `get_prop`/`set_prop` hooks or
  raise `UndefinedProperty`); `get_prop` takes a constant name (by-name
  access is a generated binary search per scope); one parent per struct
  (`Unsupported::MultipleInheritance`); `dsep_index`/`dref_index` raise on
  objects (nested writes and references through a run-time property name on
  an object raise `TypeError`).
- **resolve-lang 0.4**: rejects a class name in value position ("expected a
  value, found class"), so the Mox sketch's `new_object` template,
  `mox.new(Class, ...)`, does not resolve; the tests resolve the class
  operand themselves. It does not resolve an interface constant through an
  implementing class (bcgen resolves member paths by name). Its trait member
  tables differ from PHP on some visibility rules (`tests/mixins.rs` counts
  and prints them; bcgen follows PHP).

Known deviations (documented in `docs/API.md`): a protected property's
message names the declaring class (PHP names the object's); constants are
computed at load in canonical order (PHP evaluates them lazily); a class
declared inside a function or `if` is declared at load; a closure's
`static::` is its class's token unless it captured `$this`; by-name dispatch
functions are generated per scope over every member name of the unit
(bounded by the instruction budget).

## v0.5.0 - Implementation
- [ ] Typed fast paths from typeck-lang; match-lang decision trees; declared records and sums, `impl` blocks; register allocation quality and benchmarks. (Coroutines moved up to 0.3, done; classes and mixins moved up to 0.4, done.)
- [ ] (Moved from 0.2) A lowering-driven end-to-end test through lower-lang once it is published on hir-lang 0.4; verifier-checked output once bytecode-lang 0.5 ships the LSB verifier. (References into map slots: done in 0.3, LSB format 2.)
- [ ] (Moved from 0.3) `dunref_*` where the last holder of a reference is provably gone; `yield from`'s automatic key and advanced delegates if LSB gains the means. (resolve-lang in the end-to-end test and `ignore_extra`: done in 0.4.)
- [ ] (From 0.4) Mox instance methods end to end through lower-lang once it emits receivers (`implicit_receiver`); the Mox `new_object` template through resolve-lang once it accepts a class in value position; `final` enforcement, `readonly`, and constructor promotion if HIR gains the markers; a destructor flag if LSB gains one (P44).

## v0.9.0 - Hardening
- [ ] Differential fuzzing; scale benchmarks; audit with the LexerSketch Demo as the consumer.

## v1.0.0 - Stable
- [ ] Frozen after Mox runs through it in the LexerSketch Demo (D18).
