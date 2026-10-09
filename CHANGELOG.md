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

[Unreleased]: https://github.com/jamesgober/bcgen-lang/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/jamesgober/bcgen-lang/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/jamesgober/bcgen-lang/releases/tag/v0.1.0
