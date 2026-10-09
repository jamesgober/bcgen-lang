# bcgen-lang - Roadmap

> Path from scaffold to a stable 1.0. Hard parts are front-loaded; each phase has hard exit criteria.
> Master plan: ../_lexersketch/ROADMAP.md and ../_lexersketch/NEW-LIBS.md
>
> **Anti-deferral rule:** no listed hard task moves to a later phase unless this file records the move and the reason.

## v0.1.0 - Scaffold (DONE)
Compiles, CI green, structure correct, no domain logic.
- [x] Manifest, README, CHANGELOG, REPS, dual license, CI, deny, clippy, rustfmt, DIRECTIVES, ROADMAP.

## v0.2.0 - Foundation
- [ ] Dynamic-profile compilation of the HIR core (functions, closures, locals, control flow, calls incl. named/default/variadic, maps/arrays/strings, dynamic ops with OPS policies, exceptions with finally), debug line tables, differential tests against a reference HIR interpreter in tests.
- [ ] Wires hir-lang and bytecode-lang; bvm-lang as a dev-dependency for execution tests.

## v0.5.0 - Implementation
- [ ] Typed fast paths from typeck-lang; match-lang decision trees; coroutines (yield/await/spawn); classes, mixins, by-ref params; register allocation quality and benchmarks.

## v0.9.0 - Hardening
- [ ] Differential fuzzing; scale benchmarks; audit with the LexerSketch Demo as the consumer.

## v1.0.0 - Stable
- [ ] Frozen after Mox runs through it in the LexerSketch Demo (D18).
