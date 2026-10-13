//! Initializers inside nested modules (a lowered `namespace`), end to end
//! (HIR → LSB → bvm-lang 2.0.0-alpha.4): the HIR is built the way
//! lower-lang emits a namespace (a `Module` item holding the declarations,
//! its statements as the module's body), resolved by resolve-lang under the
//! PHP policy, compiled with the Mox table, and run.
//!
//! The start function used to run a nested module's body at the module's
//! own position, before the initializers of the declarations inside it, so
//! `namespace A; class S { const C = [1]; } echo count(S::C);` read the
//! constant before it was computed (bcgen-lang 0.4.1).

mod common;

use std::sync::{Arc, Mutex};

use bcgen_lang::{BodyMode, Compiler, Intrinsics, Options};
use bvm_lang::{Program, Vm, VmError};
use common::hb::H;
use common::to_rv;
use hir_lang::{ExprId, Hir, ItemId, PathRoot, Vis};
use intern_lang::Interner;
use resolve_lang::{DefKind, Export, MapEnv, Namespace, Policy, Resolver};

/// Resolves a unit built with unresolved names (`echo` is a host function).
fn resolve(hir: Hir, names: &Interner) -> Hir {
    let mut env = MapEnv::new();
    if let Some(s) = names.get("echo") {
        env = env.with_prelude(
            hir_lang::Name::new(s),
            Namespace::Value,
            Export::new(hir_lang::Res::Extern(s), DefKind::Extern),
        );
    }
    let unit = hir.unit();
    let res = Resolver::new(Policy::php())
        .with_env(&env)
        .resolve(hir, names)
        .unwrap_or_else(|e| panic!("resolve: {e}"));
    assert!(res.is_clean(), "resolution diagnostics");
    res.hir(unit).cloned().unwrap_or_else(|| panic!("unit"))
}

/// Compiles in `mode` and runs; returns what the program printed.
fn run(h: H, items: &[ItemId], body: Option<ExprId>, mode: BodyMode) -> Vec<String> {
    let (hir, names) = h.finish(items, body);
    let hir = resolve(hir, &names);
    let opts = Options::new()
        .with_body(mode)
        .with_intrinsics(Intrinsics::mox());
    let out = Compiler::new(opts)
        .compile(&hir, &names)
        .unwrap_or_else(|e| panic!("compile error: {e}"));
    let printed = Arc::new(Mutex::new(Vec::new()));
    let host = common::host(printed.clone());
    let program = Program::load(out.module().clone(), &host).unwrap_or_else(|e| {
        panic!(
            "load error: {e}\n{}",
            bytecode_lang::disassemble(out.module())
        )
    });
    let mut vm = Vm::new(&program);
    match vm.run(out.entry(), &[]) {
        Ok(v) => {
            let _ = to_rv(&vm, v, 0);
        }
        Err(VmError::Raised { kind, .. }) => panic!("raised {}", kind.code()),
        Err(e) => panic!("unexpected VM error: {e:?}"),
    }
    match printed.lock() {
        Ok(v) => v.clone(),
        Err(_) => Vec::new(),
    }
}

/// `echo(args..)` as an expression.
fn echo(h: &mut H, args: &[ExprId]) -> ExprId {
    let e = h.uname("echo");
    h.call(e, args)
}

/// `class S { const C = [10, 20]; public static $p = [30, 40]; }`.
fn class_s(h: &mut H) -> ItemId {
    let a = h.int(10);
    let b = h.int(20);
    let arr = h.array(&[a, b]);
    let c = h.class_const("C", Vis::Public, Some(arr));
    let a = h.int(30);
    let b = h.int(40);
    let arr = h.array(&[a, b]);
    let p = h.static_prop("p", Vis::Public, Some(arr));
    h.class("S", None, &[], &[c, p])
}

/// `echo(S::C[1], " ", S::$p[0])`, the names relative.
fn echo_s(h: &mut H) -> ExprId {
    let c = h.spath(PathRoot::Relative, &["S", "C"]);
    let one = h.int(1);
    let c1 = h.index(c, one);
    let sp = h.str(" ");
    let p = h.spath(PathRoot::Relative, &["S", "p"]);
    let zero = h.int(0);
    let p0 = h.index(p, zero);
    echo(h, &[c1, sp, p0])
}

const BOTH: [BodyMode; 2] = [BodyMode::Entry, BodyMode::Start];

#[test]
fn computed_constants_and_statics_work_at_the_root() {
    // The control: no namespace.
    for mode in BOTH {
        let mut h = H::new();
        let s = class_s(&mut h);
        let e = echo_s(&mut h);
        assert_eq!(run(h, &[s], Some(e), mode), ["20 30"], "{mode:?}");
    }
}

#[test]
fn computed_constants_and_statics_work_in_a_namespace() {
    // namespace A; class S { const C = [10, 20]; static $p = [30, 40]; }
    // echo(S::C[1], " ", S::$p[0]);
    for mode in BOTH {
        let mut h = H::new();
        let s = class_s(&mut h);
        let e = echo_s(&mut h);
        let a = h.module("A", &[s], Some(e));
        assert_eq!(run(h, &[a], None, mode), ["20 30"], "{mode:?}");
    }
}

#[test]
fn a_namespace_global_and_constant_are_set_before_the_namespace_body() {
    // namespace A; const K = 1 + 2; $g = ...; echo(K);
    for mode in BOTH {
        let mut h = H::new();
        let one = h.int(1);
        let two = h.int(2);
        let sum = h.op(hir_lang::OpKind::Add, &[one, two]);
        let k = h.constant("K", sum);
        let a = h.int(5);
        let b = h.int(6);
        let sum = h.op(hir_lang::OpKind::Add, &[a, b]);
        let g = h.global("g", Some(sum));
        let kr = h.item_ref("K", k);
        let sp = h.str(" ");
        let gr = h.item_ref("g", g);
        let e = echo(&mut h, &[kr, sp, gr]);
        let a = h.module("A", &[k, g], Some(e));
        assert_eq!(run(h, &[a], None, mode), ["3 11"], "{mode:?}");
    }
}

#[test]
fn a_doubly_nested_namespace_runs_after_all_the_initializers() {
    // namespace A { echo("outer"); namespace B { class S {..} echo(S..); } }
    // The outer body runs first (source order); both run after every
    // initializer, including those of the module nested in the first.
    for mode in BOTH {
        let mut h = H::new();
        let s = class_s(&mut h);
        let inner = echo_s(&mut h);
        let b = h.module("B", &[s], Some(inner));
        let o = h.str("outer");
        let outer = echo(&mut h, &[o]);
        let a = h.module("A", &[b], Some(outer));
        assert_eq!(run(h, &[a], None, mode), ["outer", "20 30"], "{mode:?}");
    }
}

#[test]
fn a_namespace_body_sees_a_later_sibling_namespaces_initializers() {
    // namespace A { echo(B's const) }  namespace B { const K = 1 + 2; }
    for mode in BOTH {
        let mut h = H::new();
        let one = h.int(1);
        let two = h.int(2);
        let sum = h.op(hir_lang::OpKind::Add, &[one, two]);
        let k = h.constant("K", sum);
        let b = h.module("B", &[k], None);
        let kr = h.item_ref("K", k);
        let e = echo(&mut h, &[kr]);
        let a = h.module("A", &[], Some(e));
        // A first, B second: A's body runs after every declaration.
        assert_eq!(run(h, &[a, b], None, mode), ["3"], "{mode:?}");
    }
}
