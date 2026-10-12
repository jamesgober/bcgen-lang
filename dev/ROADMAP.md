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

## v0.5.0 - Implementation
- [ ] Typed fast paths from typeck-lang; match-lang decision trees; classes, mixins, declared records and sums; register allocation quality and benchmarks. (Coroutines moved up to 0.3, done.)
- [ ] (Moved from 0.2) A lowering-driven end-to-end test through lower-lang once it is published on hir-lang 0.4; verifier-checked output once bytecode-lang 0.5 ships the LSB verifier. (References into map slots: done in 0.3, LSB format 2.)
- [ ] (Moved from 0.3) resolve-lang back in the end-to-end test once it is published on hir-lang 0.4; a language switch for PHP's ignored extra arguments (`ignore_extra`); `dunref_*` where the last holder of a reference is provably gone; `yield from`'s automatic key and advanced delegates if LSB gains the means.

## v0.9.0 - Hardening
- [ ] Differential fuzzing; scale benchmarks; audit with the LexerSketch Demo as the consumer.

## v1.0.0 - Stable
- [ ] Frozen after Mox runs through it in the LexerSketch Demo (D18).
