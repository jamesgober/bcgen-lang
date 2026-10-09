//! Hostile input: nesting at any depth compiles on a small native stack
//! (generation is an explicit task stack), the instruction budget holds, and
//! every form this release does not compile is a precise error.

mod common;

use bcgen_lang::{BodyMode, CompileError, Compiler, Options, Unsupported};
use bvm_lang::{Host, Program, Value, Vm};
use common::hb::H;
use hir_lang::{
    ClassDef, DefaultEval, Effects, Expr, FnDef, IntLit, Item, ItemKind, Lit, NodeRef, OpKind,
    ParamKind, Prim, Ty,
};

fn entry() -> Options {
    Options::new().with_body(BodyMode::Entry)
}

/// Runs `f` on a thread with a 512 KiB stack: deep input must not need more.
fn small_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(512 << 10)
            .spawn_scoped(s, f)
            .expect("spawn")
            .join()
            .expect("no stack overflow")
    })
}

fn run(out: &bcgen_lang::Compiled) -> Value {
    let p = Program::load(out.module().clone(), &Host::new()).expect("loads");
    Vm::new(&p).run(out.entry(), &[]).expect("runs")
}

#[test]
fn a_hundred_thousand_nested_operations_compile_iteratively() {
    let (hir, names) = {
        let mut h = H::new();
        let mut e = h.int(0);
        for _ in 0..100_000 {
            let one = h.int(1);
            e = h.op(OpKind::Add, &[e, one]);
        }
        h.finish(&[], Some(e))
    };
    let out = small_stack(|| {
        Compiler::new(entry())
            .compile(&hir, &names)
            .expect("compiles")
    });
    assert_eq!(run(&out), Value::Int(100_000));
}

#[test]
fn deeply_nested_blocks_ifs_and_calls_compile_iteratively() {
    let (hir, names) = {
        let mut h = H::new();
        // if c { if c { ... 7 } else 0 } else 0, 20k deep, inside 20k blocks,
        // as the argument of 5k nested intrinsic calls.
        let mut e = h.int(7);
        for _ in 0..20_000 {
            let c = h.boolean(true);
            let z = h.int(0);
            e = h.if_(c, e, Some(z));
        }
        for _ in 0..20_000 {
            e = h.block(&[], Some(e));
        }
        for _ in 0..5_000 {
            e = h.intrinsic("truthy", &[e]);
        }
        h.finish(&[], Some(e))
    };
    let out = small_stack(|| {
        Compiler::new(entry())
            .compile(&hir, &names)
            .expect("compiles")
    });
    assert_eq!(run(&out), Value::Bool(true));
}

#[test]
fn the_instruction_budget_is_enforced() {
    let mut h = H::new();
    let mut e = h.int(0);
    for _ in 0..1_000 {
        let one = h.int(1);
        e = h.op(OpKind::Add, &[e, one]);
    }
    let (hir, names) = h.finish(&[], Some(e));
    let err = Compiler::new(entry().with_max_instructions(100))
        .compile(&hir, &names)
        .unwrap_err();
    assert_eq!(err, CompileError::BudgetExceeded { limit: 100 });
    assert!(Compiler::new(entry()).compile(&hir, &names).is_ok());
}

#[test]
fn too_many_parameters_is_an_error() {
    let mut h = H::new();
    let params: Vec<_> = (0..65)
        .map(|i| h.param(&format!("p{i}"), ParamKind::Normal, None, false).0)
        .collect();
    let body = h.block(&[], None);
    let f = h.func("wide", &params, body, DefaultEval::PerCall);
    let (hir, names) = h.finish(&[f], None);
    let err = bcgen_lang::compile(&hir, &names).unwrap_err();
    assert!(
        matches!(err, CompileError::TooManyParams { limit: 64, .. }),
        "{err:?}"
    );
}

fn unsupported(
    build: impl FnOnce(&mut H) -> (Vec<hir_lang::ItemId>, Option<hir_lang::ExprId>),
) -> CompileError {
    let mut h = H::new();
    let (items, body) = build(&mut h);
    let (hir, names) = h.finish(&items, body);
    Compiler::new(entry()).compile(&hir, &names).unwrap_err()
}

fn feature(e: CompileError) -> Unsupported {
    match e {
        CompileError::Unsupported { feature, .. } => feature,
        e => panic!("not an unsupported form: {e:?}"),
    }
}

#[test]
fn coroutines_are_reported_for_0_5() {
    let e = unsupported(|h| {
        let y = h.expr(Expr::Yield(None));
        let body = h.block(&[], Some(y));
        h.tick();
        let n = h.name("gen");
        let f = h.b.item(Item::new(
            Some(n),
            ItemKind::Fn(FnDef {
                body: Some(body),
                effects: Effects::YIELD,
                ..FnDef::default()
            }),
        ));
        (vec![f], None)
    });
    assert_eq!(feature(e), Unsupported::Coroutine);
    assert!(Unsupported::Coroutine.to_string().contains("0.5"));
}

#[test]
fn classes_are_reported_for_0_5() {
    let e = unsupported(|h| {
        h.tick();
        let n = h.name("C");
        let c =
            h.b.item(Item::new(Some(n), ItemKind::Class(ClassDef::default())));
        (vec![c], None)
    });
    assert_eq!(feature(e), Unsupported::Class);
}

#[test]
fn reference_forms_are_reported() {
    let e = unsupported(|h| {
        let one = h.int(1);
        let d = h.expr(Expr::Deref(one));
        (vec![], Some(d))
    });
    assert_eq!(feature(e), Unsupported::Reference);
    let e = unsupported(|h| {
        let s = h.str("x");
        let v = h.expr(Expr::VarVar(s));
        (vec![], Some(v))
    });
    assert_eq!(feature(e), Unsupported::VarVar);
}

#[test]
fn host_functions_as_values_and_with_named_arguments_are_reported() {
    let e = unsupported(|h| {
        let x = h.extern_ref("echo");
        (vec![], Some(x))
    });
    assert_eq!(feature(e), Unsupported::ExternValue);
    let e = unsupported(|h| {
        let x = h.extern_ref("echo");
        let one = h.int(1);
        let a = h.named("v", one);
        let c = h.call_args(x, &[a]);
        (vec![], Some(c))
    });
    assert_eq!(feature(e), Unsupported::ExternArgs);
}

#[test]
fn conversions_without_a_dynamic_width_are_reported() {
    let e = unsupported(|h| {
        let one = h.int(1);
        let z = h.op(OpKind::Zext(Prim::I8), &[one]);
        (vec![], Some(z))
    });
    assert_eq!(feature(e), Unsupported::Conversion);
    let e = unsupported(|h| {
        let one = h.int(1);
        let t = h.ty(Ty::Never);
        let c = h.expr(Expr::Cast {
            expr: one,
            ty: t,
            policy: hir_lang::Policy::CAST,
        });
        (vec![], Some(c))
    });
    assert_eq!(feature(e), Unsupported::Cast);
}

#[test]
fn big_integers_and_out_of_range_literals_are_reported() {
    let e = unsupported(|h| {
        let t = h.b.text("123456789012345678901234567890");
        let l = h.lit(Lit::BigInt(t));
        (vec![], Some(l))
    });
    assert_eq!(feature(e), Unsupported::BigInt);
    let e = unsupported(|h| {
        let l = h.lit(Lit::Int(IntLit::new(u64::MAX).with_suffix(Prim::U64)));
        (vec![], Some(l))
    });
    assert!(matches!(e, CompileError::LiteralOutOfRange { .. }), "{e:?}");
}

#[test]
fn reference_assignment_to_an_element_is_reported() {
    let e = unsupported(|h| {
        let a = h.local("a");
        let arr = h.array(&[]);
        let la = h.let_(a, Some(arr));
        let va = h.var(a);
        let z = h.int(0);
        let ix = h.index(va, z);
        let vb = h.var(a);
        let r = h.expr(Expr::RefAssign {
            target: ix,
            source: vb,
        });
        let body = h.block(&[la], Some(r));
        (vec![], Some(body))
    });
    assert_eq!(feature(e), Unsupported::RefPlace);
}

#[test]
fn error_nodes_and_unresolved_paths_do_not_compile() {
    let e = unsupported(|h| {
        let x = h.expr(Expr::Err);
        (vec![], Some(x))
    });
    assert!(
        matches!(
            e,
            CompileError::ErrorNode {
                node: NodeRef::Expr(_),
                ..
            }
        ),
        "{e:?}"
    );
    let e = unsupported(|h| {
        h.tick();
        let n = h.name("nowhere");
        let x = h.b.name_expr(n);
        (vec![], Some(x))
    });
    assert!(matches!(e, CompileError::Unresolved { .. }), "{e:?}");
    // Errors name the node and its span.
    assert!(e.node().is_some() && e.span().is_some());
}

#[test]
fn assigning_to_a_function_is_not_assignable() {
    let e = unsupported(|h| {
        let body = h.block(&[], None);
        let f = h.func("f", &[], body, DefaultEval::PerCall);
        let t = h.item_ref("f", f);
        let one = h.int(1);
        let a = h.assign(t, one);
        (vec![f], Some(a))
    });
    assert!(matches!(e, CompileError::NotAssignable { .. }), "{e:?}");
}

#[test]
fn unknown_intrinsics_and_wrong_arity_are_reported() {
    let e = unsupported(|h| {
        let x = h.intrinsic("nope", &[]);
        (vec![], Some(x))
    });
    assert_eq!(feature(e), Unsupported::Intrinsic);
    let e = unsupported(|h| {
        let one = h.int(1);
        let two = h.int(2);
        let x = h.intrinsic("len", &[one, two]);
        (vec![], Some(x))
    });
    assert!(
        matches!(e, CompileError::IntrinsicArity { expected: 1, .. }),
        "{e:?}"
    );
}
