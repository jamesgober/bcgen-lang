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
        <strong>bcgen-lang</strong> compiles HIR, the representation every LexerSketch language lowers into, to LSB, the bytecode <a href="https://crates.io/crates/bvm-lang"><code>bvm-lang</code></a> executes. Hand it a resolved unit and it returns an LSB module, ready to load: functions with defaults, named, variadic, and by-reference parameters, each carrying its LSB parameter list; closures; generators, <code>await</code>, and <code>spawn</code>; loops, <code>match</code>, and exceptions with <code>finally</code>; PHP arrays and references; and every OPS operation under the policy the language chose. It is what lets a forged language run the moment it is forged.
    </p>
    <p>
        Version 0.3 compiles HIR spec v3 (hir-lang 0.4) to LSB format 2 (bytecode-lang 0.3, which bvm-lang 2.0.0-alpha.3 runs) in the <strong>dynamic profile</strong>: every value is an LSB <code>dyn</code>, the profile Mox and other dynamic languages run under. Operators a language defines itself (PHP's loose <code>==</code>, <code>.</code>, <code>**</code>) compile through an <strong>intrinsic table</strong>: an inline LSB fast path where LSB's result is exactly the language's, a host function the embedder provides everywhere else; <code>Intrinsics::mox()</code> covers every Mox intrinsic. Every instruction maps back to the HIR node it came from, so runtime errors point at source. Typed fast paths (from typeck-lang), classes, and declared records arrive in 0.5; until then those forms are precise <code>Unsupported</code> errors, never silent miscompilations.
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
- **[`Compiler`](./docs/API.md#compiler)** adds **[`Options`](./docs/API.md#options)** (array semantics, key coercion, what the module body compiles to, hooks, the intrinsic table, budgets) and a **[`Locate`](./docs/API.md#locate)** for real line numbers in the line tables ([`LineIndex`](./docs/API.md#lineindex) for one source file).
- **[`Intrinsics`](./docs/API.md#intrinsics)** says how each named intrinsic compiles: an LSB sequence, a host function, or a guarded fast path over one ([`Lowering`](./docs/API.md#lowering), [`Fast`](./docs/API.md#fast)). [`Intrinsics::mox`](./docs/API.md#the-mox-intrinsics) maps all of Mox's, with the semantics each host function must implement.
- **[`CompileError`](./docs/API.md#compileerror)** says why a unit does not compile, naming the HIR node and its span; **[`Unsupported`](./docs/API.md#unsupported)** names the forms planned for later releases.

<br>

What it guarantees, and how each guarantee is checked:

| Guarantee | How it is held |
|---|---|
| Compiled programs mean what the HIR means. | `tests/differential.rs`: random well-formed programs (functions, closures, loops, `match`, `try`/`finally`, `defer`, maps, `let_place`, union type tests, every op under random policies, `promote`, `pow`, and saturating shifts included) run on bvm-lang and on a reference HIR interpreter written in the tests; results, printed output, error kinds, and error locations (the raising HIR node) must agree, under both array profiles. 1,320,000 programs were run before this release; every `cargo test` runs 3,000 more. |
| The forms the generator does not reach run as PHP runs them. | `tests/features_0_3.rs`: generators (keys, sends, `yield from` with throws, closing with `finally`, by-reference parameters), `await` and `spawn` on bvm-lang's scheduler, `let_place`, references into elements, OPS v2, `NoMatch`, unions, dynamic calls with named arguments and spreads, each checked against PHP's result. |
| Calls bind the same whichever path they take. | `tests/binding.rs`: random parameter lists and argument lists (positional, named, unknown names, spreads, named spreads); the compile-time arrangement of a direct call and the VM's binding of the same call through the function's value give the same parameters or the same `ArgumentError`. |
| Every Mox intrinsic computes PHP's result. | `tests/intrinsics.rs`: every mapping of `Intrinsics::mox()` runs against a test host implementing PHP 8's semantics, over every pair of a 37-value scalar pool; each fast path gives exactly the host's result on its documented domain and calls the host exactly for the operands outside it. |
| Every module it emits loads in bvm-lang. | `tests/properties.rs`: every generated program's module passes bvm-lang's load-time checks (registers, call windows, constants, branch targets, handlers in range) and round-trips through the LSB encoding unchanged. |
| Every instruction maps back to its HIR origin. | The origin table holds one node per instruction of every function, each a node of the unit; line-table rows are strictly increasing; a runtime error's location maps to the raising node and, through a `LineIndex`, to its source line (`tests/properties.rs`). |
| Compilation is deterministic. | The same unit compiles to the same bytes, from a clone and on another thread (`tests/properties.rs`). |
| No recursion over the input. | Code generation is an explicit task stack: 100,000 nested operations, 20,000 nested `if`s inside 20,000 blocks, and 20,000 nested `let_place`s and union-of-intersection types compile on a 512 KiB stack in a debug build (`tests/limits.rs`, `tests/hostile.rs`). Output is bounded by an instruction budget. |
| Hostile HIR never panics the compiler. | `tests/hostile.rs`: random HIR mixing every form anywhere (generators, `let_place`, references, intrinsics of any name and arity), repaired by `finish_lenient`; compiling either succeeds, and the module loads and runs under budgets, or returns a precise error. 200,000 programs before this release; 2,000 per `cargo test`. |
| PHP array semantics. | Arrays are values (copied on assignment, passing, returning, capture, and store, with an O(1) copy-on-write `dup`), nested writes separate shared arrays and create missing ones, and keys follow PHP's coercion, checked against a reference interpreter that makes real deep copies, and by `tests/keys.rs` against PHP's canonical-integer rule. |
| A Mox program runs end to end. | `tests/e2e.rs`: a hand-lowered Mox program (names unresolved, as a lowering emits them) is resolved by a lexical resolver in the test, compiled, and run on bvm-lang, printing through a host function. (resolve-lang 0.3 is on hir-lang 0.3; it returns to this test when it moves to 0.4.) |

<hr>
<br>

## Installation

```toml
[dependencies]
bcgen-lang = "0.3"
```

Without the standard library:

```toml
[dependencies]
bcgen-lang = { version = "0.3", default-features = false }
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

### Mox operators through the intrinsic table

```rust
use bcgen_lang::{BodyMode, Compiler, Intrinsics, Options};
use bvm_lang::{Host, Program, Value, Vm};
use hir_lang::{Builder, Effects, Expr, Intrinsic, Item, ItemKind, List};
use intern_lang::Interner;

// "a" . "b": both strings, so the fast path concatenates inline.
let mut names = Interner::new();
let mut b = Builder::new();
let (x, y) = (b.str_lit("a"), b.str_lit("b"));
let args = b.list(&[x, y]);
let sym = names.intern("mox.concat");
let cat = b.expr(Expr::Intrinsic { kind: Intrinsic::Named(sym), generic_args: List::EMPTY, args });
let module = ItemKind::Module { items: List::EMPTY, body: Some(cat), effects: Effects::NONE };
let root = b.item(Item::new(None, module));
let hir = b.finish(root)?;

let opts = Options::new().with_body(BodyMode::Entry).with_intrinsics(Intrinsics::mox());
let out = Compiler::new(opts).compile(&hir, &names)?;
// The runtime's `mox.concat` handles every other operand (here unused).
let mut host = Host::new();
host.register("mox", "concat", |_, _| Ok(Value::Nil));
let program = Program::load(out.module().clone(), &host)?;
let mut vm = Vm::new(&program);
let v = vm.run(out.entry(), &[])?;
assert_eq!(vm.str_bytes(v), Some(&b"ab"[..]));
# Ok::<(), Box<dyn std::error::Error>>(())
```

The full reference, including the calling convention, the dynamic semantics
of every form, every Mox intrinsic's semantics, and what each option changes,
is in [`docs/API.md`](./docs/API.md).

<hr>
<br>

## Performance

Release build on the development machine (Windows 11), criterion medians from
`benches/bench.rs`. Compile figures are library-only (HIR in memory to an LSB
module, no encoding); run figures are bvm-lang 2.0.0-alpha.3 executing the
compiled module (VM instance creation included). The 0.2 column is bcgen-lang
0.2.0 on bvm-lang 2.0.0-alpha.1, measured on the same machine the same day.
Medians move by up to about 10% between runs on this machine; differences
below that are noise.

| Benchmark | 0.3.0 | 0.2.0 |
|---|---|---|
| Compile, synthetic unit, 152k HIR nodes | 28 ms | 27 to 32 ms |
| Compile, synthetic unit, 532k HIR nodes | 110 to 117 ms | 108 to 117 ms |
| Compile, synthetic unit, 1.52M HIR nodes | 335 to 352 ms | 331 to 333 ms |
| `fib(25)`, direct calls | 6.6 to 7.3 ms | 6.7 to 7.0 ms |
| Counting loop, 1M iterations | 9.5 ms | 9.4 ms |
| PHP array: 100k appends, then 100k indexed reads | 10.6 ms | 10.3 ms |
| The same plus 100k nested writes `g[i % 64][] = i` | 23 to 29 ms | 415 ms |
| A generator yielding 100k values, summed through `iter`/`iter_next` | 29 ms | (not compiled) |
| 100k `let_place p = a[i % 64] in p = p + i` | 7.3 to 9.7 ms | (not compiled) |
| 100k dynamic calls with two named arguments and a default | 15 to 22 ms | (packets) |
| 100k `inc(&a[i % 64])` (a reference to an element) | 8.8 ms | (not compiled) |
| 1M `mox.loose_eq(i, i)` (the inline fast path) | 54 to 57 ms | (host only) |

"Nodes" counts items, expressions, statements, patterns, paths, and
parameters. Compile time is linear: `tests/scaling.rs` measures 134 to 178 ns
per node from 146k to 2.3M nodes. Nested writes are 15 to 18 times faster
than 0.2's: `dsep_index` (LSB format 2) copies an inner array only when
another array may share it, where 0.2 had to copy it on every write.

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
