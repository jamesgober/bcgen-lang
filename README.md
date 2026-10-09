<h1 align="center">
    <img width="99" alt="Rust logo" src="https://raw.githubusercontent.com/jamesgober/rust-collection/72baabd71f00e14aa9184efcb16fa3deddda3a0a/assets/rust-logo.svg">
    <br>
    <b>bcgen-lang</b>
    <br>
    <sub><sup>HIR TO BYTECODE COMPILER</sup></sub>
</h1>

<div align="center">
    <a href="https://crates.io/crates/bcgen-lang"><img alt="Crates.io" src="https://img.shields.io/crates/v/bcgen-lang"></a>
    <a href="https://crates.io/crates/bcgen-lang"><img alt="Downloads" src="https://img.shields.io/crates/d/bcgen-lang?color=%230099ff"></a>
    <a href="https://docs.rs/bcgen-lang"><img alt="docs.rs" src="https://img.shields.io/docsrs/bcgen-lang"></a>
    <a href="https://github.com/jamesgober/bcgen-lang/actions"><img alt="CI" src="https://github.com/jamesgober/bcgen-lang/actions/workflows/ci.yml/badge.svg"></a>
    <a href="https://github.com/rust-lang/rfcs/blob/master/text/2495-min-rust-version.md"><img alt="MSRV" src="https://img.shields.io/badge/MSRV-1.85%2B-blue"></a>
</div>

<br>

<div align="left">
    <p>
        <strong>bcgen-lang</strong> compiles HIR, the representation every LexerSketch language lowers into, to LSB, the bytecode <a href="https://crates.io/crates/bvm-lang"><code>bvm-lang</code></a> executes. Hand it a resolved unit and it returns an LSB module, ready to load: functions with defaults, named, variadic, and by-reference parameters; closures; loops, <code>match</code>, and exceptions with <code>finally</code>; PHP arrays; and every OPS operation under the policy the language chose. It is what lets a forged language run the moment it is forged.
    </p>
    <p>
        Version 0.2 compiles the <strong>dynamic profile</strong>: every value is an LSB <code>dyn</code>, the profile Mox and other dynamic languages run under. Every instruction it emits maps back to the HIR node it came from, so runtime errors point at source. Typed fast paths (from typeck-lang), classes, and coroutines arrive in 0.5; until then those forms are precise <code>Unsupported</code> errors, never silent miscompilations.
    </p>
    <br>
    <hr>
    <p>
        <strong>MSRV is 1.85+</strong> (Rust 2024 edition). <code>no_std</code>-compatible (needs only <code>alloc</code>), <code>#![forbid(unsafe_code)]</code>, three dependencies from the family: <a href="https://crates.io/crates/hir-lang"><code>hir-lang</code></a>, <a href="https://crates.io/crates/bytecode-lang"><code>bytecode-lang</code></a>, and <a href="https://crates.io/crates/intern-lang"><code>intern-lang</code></a>.
    </p>
    <blockquote>
        <strong>Status: pre-1.0, in active development.</strong> The public API is being designed across the 0.x series and frozen at <code>1.0.0</code>, after the LexerSketch Demo runs Mox through it. See <a href="./CHANGELOG.md"><code>CHANGELOG.md</code></a> and <a href="./dev/ROADMAP.md"><code>dev/ROADMAP.md</code></a>.
    </blockquote>
</div>

<hr>
<br>

## The model

- **[`compile`](./docs/API.md#compile)** takes a resolved `hir_lang::Hir` and the interner its names came from, and returns a **[`Compiled`](./docs/API.md#compiled)**: the LSB module, its entry function, and an origin table mapping every instruction to its HIR node.
- **[`Compiler`](./docs/API.md#compiler)** adds **[`Options`](./docs/API.md#options)** (array semantics, key coercion, what the module body compiles to, hooks, budgets) and a **[`Locate`](./docs/API.md#locate)** for real line numbers in the line tables ([`LineIndex`](./docs/API.md#lineindex) for one source file).
- **[`CompileError`](./docs/API.md#compileerror)** says why a unit does not compile, naming the HIR node and its span; **[`Unsupported`](./docs/API.md#unsupported)** names the forms planned for later releases.

<br>

What it guarantees, and how each guarantee is checked:

| Guarantee | How it is held |
|---|---|
| Compiled programs mean what the HIR means. | `tests/differential.rs`: random well-formed programs (functions, closures, loops, `match`, `try`/`finally`, `defer`, maps, every op under random policies, `promote` included) run on bvm-lang and on a reference HIR interpreter written in the tests; results, printed output, error kinds, and error locations (the raising HIR node) must agree, under both array profiles. 1,000,000 programs were run before this release; every `cargo test` runs 3,000 more. Mutation-checked: removing the array copy, swapping two `finally` dispatch targets, or compiling `floor_mod` as `rem` makes it fail. |
| Every module it emits loads in bvm-lang. | `tests/properties.rs`: every generated program's module passes bvm-lang's load-time checks (registers, call windows, constants, branch targets, handlers in range) and round-trips through the LSB encoding unchanged. |
| Every instruction maps back to its HIR origin. | The origin table holds one node per instruction of every function, each a node of the unit; line-table rows are strictly increasing; a runtime error's location maps to the raising node and, through a `LineIndex`, to its source line (`tests/properties.rs`). |
| Compilation is deterministic. | The same unit compiles to the same bytes, from a clone and on another thread (`tests/properties.rs`). |
| No recursion over the input. | Code generation is an explicit task stack: 100,000 nested operations and 20,000 nested `if`s inside 20,000 blocks compile on a 512 KiB stack in a debug build (`tests/limits.rs`). Output is bounded by an instruction budget. |
| PHP array semantics. | Arrays are values (copied on assignment, passing, returning, capture, and store, with an O(1) copy-on-write `dup`), nested writes separate shared arrays and create missing ones, and keys follow PHP's coercion, checked against a reference interpreter that makes real deep copies, and by `tests/keys.rs` against PHP's canonical-integer rule. |
| A Mox program runs end to end. | `tests/e2e.rs`: a hand-lowered Mox program is resolved by resolve-lang, compiled, and run on bvm-lang, printing through a host function. |

<hr>
<br>

## Installation

```toml
[dependencies]
bcgen-lang = "0.2"
```

Without the standard library:

```toml
[dependencies]
bcgen-lang = { version = "0.2", default-features = false }
```

<hr>
<br>

## Quick start

Compile a unit and run it on bvm-lang:

```rust
use bvm_lang::{Host, Program, Value, Vm};
use hir_lang::{Builder, Name, OpKind};
use intern_lang::Interner;

// fn add(a, b) { a + b }
let mut names = Interner::new();
let mut b = Builder::new();
let (pa, a) = b.local_param(Name::new(names.intern("a")));
let (pb, bb) = b.local_param(Name::new(names.intern("b")));
let (ua, ub) = (b.use_binder(a), b.use_binder(bb));
let sum = b.op(OpKind::Add, &[ua, ub]);
let body = b.block(&[], Some(sum));
let add = b.func(Name::new(names.intern("add")), &[pa, pb], body);
let root = b.module(None, &[add]);
let hir = b.finish(root)?;

let out = bcgen_lang::compile(&hir, &names)?;
let func = out.function(add).unwrap();
let program = Program::load(out.into_module(), &Host::new())?;
let mut vm = Vm::new(&program);
assert_eq!(vm.run(func, &[Value::Int(2), Value::Int(3)])?, Value::Int(5));
# Ok::<(), Box<dyn std::error::Error>>(())
```

### Scripts, host functions, and source lines

A module body runs in the module's start function and the entry function
returns its value. Host symbols (`Res::Extern`) become LSB imports:

```rust
use bcgen_lang::{Compiler, LineIndex, Options};
use bvm_lang::{Host, Program, Value, Vm};
use hir_lang::{Builder, Effects, Expr, Item, ItemKind, List, Name, Ns, Path, Res, Segment};
use intern_lang::Interner;

// echo("hello"); 42
let mut names = Interner::new();
let mut b = Builder::new();
let echo = names.intern("echo");
let seg = Segment::new(Name::new(echo), b.origin());
let segs = b.list(&[seg]);
let path = b.path(Path { res: Res::Extern(echo), ..Path::new(segs, Ns::Value) });
let callee = b.expr(Expr::Path(path));
let hello = b.str_lit("hello");
let call = b.call(callee, &[hello]);
let stmt = b.expr_stmt(call);
let answer = b.int(42);
let body = b.block(&[stmt], Some(answer));
let module = ItemKind::Module { items: List::EMPTY, body: Some(body), effects: Effects::NONE };
let root = b.item(Item::new(None, module));
let hir = b.finish(root)?;

let lines = LineIndex::new("hello.mox", 0, "echo(\"hello\"); 42\n");
let out = Compiler::new(Options::new()).with_locator(&lines).compile(&hir, &names)?;

let mut host = Host::new();
host.register("host", "echo", |ctx, args| {
    assert_eq!(ctx.str_bytes(args[0]), Some(&b"hello"[..]));
    Ok(Value::Nil)
});
let program = Program::load(out.module().clone(), &host)?;
assert_eq!(Vm::new(&program).run(out.entry(), &[])?, Value::Int(42));
# Ok::<(), Box<dyn std::error::Error>>(())
```

The full reference, including the calling convention, the dynamic semantics
of every form, and what each option changes, is in
[`docs/API.md`](./docs/API.md).

<hr>
<br>

## Performance

Release build on the development machine (Windows 11), criterion medians from
`benches/bench.rs`. Compile figures are library-only (HIR in memory to an LSB
module, no encoding); run figures are bvm-lang 2.0.0-alpha.1 executing the
compiled module (VM instance creation included).

| Benchmark | Result |
|---|---|
| Compile, synthetic unit, 152k HIR nodes | 23 ms (6.6 M nodes/s) |
| Compile, synthetic unit, 532k HIR nodes | 103 ms (5.2 M nodes/s) |
| Compile, synthetic unit, 1.52M HIR nodes | 354 ms (4.3 M nodes/s) |
| `fib(25)`, direct calls | 8.6 ms |
| Counting loop, 1M iterations | 10.7 ms |
| PHP array: 100k appends, then 100k indexed reads | 13.0 ms |
| The same plus 100k nested writes `g[i % 64][] = i` | 371 ms |

"Nodes" counts items, expressions, statements, patterns, paths, and
parameters. Compile time is linear: `tests/scaling.rs` measures 150 to 170 ns
per node from 146k to 2.3M nodes (the criterion spread above is allocator
noise around that). The last row is the cost of PHP nested-write separation:
LSB cannot ask whether an inner array is shared, so every nested write copies
the inner array's store while the old copy is uncollected (about 28 times the
plain-append case here). An LSB instruction that separates only when shared
is requested from the spec owners.

<hr>
<br>

## Contributing

See <a href="./dev/DIRECTIVES.md"><code>dev/DIRECTIVES.md</code></a> for engineering standards and the definition of done. Before a PR: `cargo fmt --all`, `cargo clippy --all-targets --all-features -- -D warnings`, and `cargo test --all-features` must be clean.

<br>

<div id="license">
    <h2>License</h2>
    <p>Licensed under either of</p>
    <ul>
        <li><b>Apache License, Version 2.0</b> &mdash; <a href="./LICENSE-APACHE">LICENSE-APACHE</a></li>
        <li><b>MIT License</b> &mdash; <a href="./LICENSE-MIT">LICENSE-MIT</a></li>
    </ul>
    <p>at your option.</p>
</div>

<div align="center">
  <h2></h2>
  <sup>COPYRIGHT <small>&copy;</small> 2026 <strong>James Gober.</strong></sup>
</div>
