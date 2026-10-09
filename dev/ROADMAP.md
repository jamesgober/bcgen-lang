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

## v0.5.0 - Implementation
- [ ] Typed fast paths from typeck-lang; match-lang decision trees; coroutines (yield/await/spawn); classes, mixins, declared records and sums; register allocation quality and benchmarks.
- [ ] (Moved from 0.2) A lowering-driven end-to-end test through lower-lang once it is published; verifier-checked output once bytecode-lang 0.5 ships the LSB verifier; references into map slots if LSB adds them.

## v0.9.0 - Hardening
- [ ] Differential fuzzing; scale benchmarks; audit with the LexerSketch Demo as the consumer.

## v1.0.0 - Stable
- [ ] Frozen after Mox runs through it in the LexerSketch Demo (D18).
