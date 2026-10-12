//! Hostile input: nesting at any depth compiles on a small native stack
//! (generation is an explicit task stack), the instruction budget holds, and
//! every form this release does not compile is a precise error.

mod common;

use bcgen_lang::{BodyMode, CompileError, Compiler, Options, Unsupported};
use bvm_lang::{Host, Program, Value, Vm};
use common::hb::H;
use hir_lang::{
    ClassDef, DefaultEval, Expr, IntLit, Item, ItemKind, Lit, NodeRef, OpKind, ParamKind, Prim, Ty,
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
    // With a default: the presence mask carries 64.
    let mut h = H::new();
    let mut params: Vec<_> = (0..64)
        .map(|i| h.param(&format!("p{i}"), ParamKind::Normal, None, false).0)
        .collect();
    let d = h.int(1);
    params.push(h.param("last", ParamKind::Normal, Some(d), false).0);
    let body = h.block(&[], None);
    let f = h.func("wide", &params, body, DefaultEval::PerCall);
    let (hir, names) = h.finish(&[f], None);
    let err = bcgen_lang::compile(&hir, &names).unwrap_err();
    assert!(
        matches!(err, CompileError::TooManyParams { limit: 64, .. }),
        "{err:?}"
    );
    // Without: an LSB parameter list carries 255.
    let mut h = H::new();
    let params: Vec<_> = (0..256)
        .map(|i| h.param(&format!("p{i}"), ParamKind::Normal, None, false).0)
        .collect();
    let body = h.block(&[], None);
    let f = h.func("wider", &params, body, DefaultEval::PerCall);
    let (hir, names) = h.finish(&[f], None);
    let err = bcgen_lang::compile(&hir, &names).unwrap_err();
    assert!(
        matches!(err, CompileError::TooManyParams { limit: 255, .. }),
        "{err:?}"
    );
    // 255 compile and run.
    let mut h = H::new();
    let params: Vec<_> = (0..255)
        .map(|i| h.param(&format!("p{i}"), ParamKind::Normal, None, false).0)
        .collect();
    let body = h.block(&[], None);
    let f = h.func("widest", &params, body, DefaultEval::PerCall);
    let (hir, names) = h.finish(&[f], None);
    assert!(bcgen_lang::compile(&hir, &names).is_ok());
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
fn impls_and_multiple_bases_are_reported() {
    // An `impl` block (typed fast paths, 0.5).
    let e = unsupported(|h| {
        let t = h.ty(Ty::Infer);
        h.tick();
        let i = h.b.item(Item::new(
            None,
            ItemKind::Impl(hir_lang::ImplDef {
                generics: hir_lang::Generics::default(),
                interface: None,
                self_ty: t,
                items: hir_lang::List::EMPTY,
            }),
        ));
        (vec![i], None)
    });
    assert_eq!(feature(e), Unsupported::Impl);
    // Python's several bases: an LSB struct has one parent.
    let mut h = H::new();
    let a = h.class("A", None, &[], &[]);
    let b = h.class("B", None, &[], &[]);
    let ta = class_ty(&mut h, "A", a);
    let tb = class_ty(&mut h, "B", b);
    h.tick();
    let n = h.name("C");
    let bases = h.b.list(&[ta, tb]);
    let c = h.b.item(Item::new(
        Some(n),
        ItemKind::Class(ClassDef {
            bases,
            ..ClassDef::default()
        }),
    ));
    let (hir, names) = h.finish(&[a, b, c], None);
    let e = Compiler::new(entry()).compile(&hir, &names).unwrap_err();
    assert_eq!(feature(e), Unsupported::MultipleInheritance);
}

/// A type naming class `item`, resolved.
fn class_ty(h: &mut H, name: &str, item: hir_lang::ItemId) -> hir_lang::TyId {
    let d = h.b.def(hir_lang::Def::Item(item));
    let p = h.path_ns(name, hir_lang::Ns::Type, hir_lang::Res::Def(d));
    h.ty(Ty::Path(p))
}

/// A chain of `n` classes, each extending the previous one, resolved.
fn chain(h: &mut H, n: usize) -> Vec<hir_lang::ItemId> {
    let mut items: Vec<hir_lang::ItemId> = Vec::with_capacity(n);
    for i in 0..n {
        let bases = match items.last() {
            Some(&prev) => {
                let t = class_ty(h, &format!("C{}", i - 1), prev);
                h.b.list(&[t])
            }
            None => hir_lang::List::EMPTY,
        };
        h.tick();
        let name = h.name(&format!("C{i}"));
        items.push(h.b.item(Item::new(
            Some(name),
            ItemKind::Class(ClassDef {
                bases,
                ..ClassDef::default()
            }),
        )));
    }
    items
}

#[test]
fn inheritance_chains_load_up_to_bvm_s_depth_and_deeper_ones_are_refused() {
    // 256 classes deep: bvm-lang's `MAX_INHERITANCE_DEPTH`; it loads, and an
    // instance of the deepest is an instance of the first.
    let mut h = H::new();
    let items = chain(&mut h, 256);
    let last = *items.last().unwrap_or_else(|| panic!("items"));
    let first = items[0];
    let lr = h.item_ref("C255", last);
    let f = h.extern_ref("mox.new");
    let o = h.call(f, &[lr]);
    let fr = h.item_ref("C0", first);
    let t = h.intrinsic("mox.instanceof", &[o, fr]);
    let (hir, names) = small_stack(|| h.finish(&items, Some(t)));
    let out = small_stack(|| {
        Compiler::new(entry().with_intrinsics(bcgen_lang::Intrinsics::mox())).compile(&hir, &names)
    })
    .unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(run(&out), Value::Bool(true));
    // 257: refused before the VM would refuse it.
    let mut h = H::new();
    let items = chain(&mut h, 257);
    let (hir, names) = h.finish(&items, None);
    let e = bcgen_lang::compile(&hir, &names).unwrap_err();
    assert!(
        matches!(
            e,
            CompileError::Class {
                problem: bcgen_lang::ClassProblem::TooDeep { limit: 256 },
                ..
            }
        ),
        "{e:?}"
    );
}

#[test]
fn class_graph_errors_are_precise() {
    use bcgen_lang::ClassProblem;
    let problem = |e: CompileError| match e {
        CompileError::Class { problem, .. } => problem,
        e => panic!("not a class problem: {e:?}"),
    };
    // A cycle: A extends B, B extends A (built by hand: forward references).
    let mut h = H::new();
    let mut ids = Vec::new();
    for name in ["A", "B"] {
        h.tick();
        let n = h.name(name);
        ids.push(h.b.item(Item::new(Some(n), ItemKind::Class(ClassDef::default()))));
    }
    let (hir, names) = h.finish(&ids, None);
    // Rebuild with the bases now that both ids are known.
    let _ = (hir, names);
    let mut h = H::new();
    h.tick();
    let an = h.name("A");
    let bn = h.name("B");
    // Item ids are dense: A is the item made after its base type's nodes.
    let a_guess = hir_lang::ItemId::from_index(0).unwrap_or_else(|| panic!("id"));
    let b_guess = hir_lang::ItemId::from_index(1).unwrap_or_else(|| panic!("id"));
    let tb = class_ty(&mut h, "B", b_guess);
    let ta = class_ty(&mut h, "A", a_guess);
    let ba = h.b.list(&[tb]);
    let bb = h.b.list(&[ta]);
    let a = h.b.item(Item::new(
        Some(an),
        ItemKind::Class(ClassDef {
            bases: ba,
            ..ClassDef::default()
        }),
    ));
    let b = h.b.item(Item::new(
        Some(bn),
        ItemKind::Class(ClassDef {
            bases: bb,
            ..ClassDef::default()
        }),
    ));
    assert_eq!((a, b), (a_guess, b_guess));
    let (hir, names) = h.finish(&[a, b], None);
    assert_eq!(
        problem(bcgen_lang::compile(&hir, &names).unwrap_err()),
        ClassProblem::Cycle
    );

    // Extending an interface; implementing a class; using a class as a mixin.
    let mut h = H::new();
    let i = h.interface("I", &[], &[]);
    let ti = class_ty(&mut h, "I", i);
    let bases = h.b.list(&[ti]);
    h.tick();
    let n = h.name("C");
    let c = h.b.item(Item::new(
        Some(n),
        ItemKind::Class(ClassDef {
            bases,
            ..ClassDef::default()
        }),
    ));
    let (hir, names) = h.finish(&[i, c], None);
    assert_eq!(
        problem(bcgen_lang::compile(&hir, &names).unwrap_err()),
        ClassProblem::NotAClass
    );
    let mut h = H::new();
    let k = h.class("K", None, &[], &[]);
    let tk = class_ty(&mut h, "K", k);
    let ifs = h.b.list(&[tk]);
    h.tick();
    let n = h.name("C");
    let c = h.b.item(Item::new(
        Some(n),
        ItemKind::Class(ClassDef {
            interfaces: ifs,
            ..ClassDef::default()
        }),
    ));
    let (hir, names) = h.finish(&[k, c], None);
    assert_eq!(
        problem(bcgen_lang::compile(&hir, &names).unwrap_err()),
        ClassProblem::NotAnInterface
    );
    let mut h = H::new();
    let k = h.class("K", None, &[], &[]);
    let tk = class_ty(&mut h, "K", k);
    let mixins = h.b.list(&[tk]);
    h.tick();
    let u = h.b.item(Item::new(
        None,
        ItemKind::MixinUse(hir_lang::MixinUseDef {
            mixins,
            rules: hir_lang::List::EMPTY,
        }),
    ));
    let c = h.class("C", None, &[], &[u]);
    let (hir, names) = h.finish(&[k, c], None);
    assert_eq!(
        problem(bcgen_lang::compile(&hir, &names).unwrap_err()),
        ClassProblem::NotAMixin
    );
    // A destructor that takes a parameter.
    let mut h = H::new();
    let (tp, _) = h.this_param();
    let (px, _) = h.param("x", ParamKind::Normal, None, false);
    let body = h.block(&[], None);
    let d = h.method_item("__destruct", hir_lang::Vis::Public, &[tp, px], body);
    let c = h.class("C", None, &[], &[d]);
    let (hir, names) = h.finish(&[c], None);
    assert_eq!(
        problem(bcgen_lang::compile(&hir, &names).unwrap_err()),
        ClassProblem::BadDestructor
    );
}

#[test]
fn a_mixin_that_uses_itself_is_a_cycle() {
    let mut h = H::new();
    h.tick();
    let tn = h.name("T");
    let guess = hir_lang::ItemId::from_index(1).unwrap_or_else(|| panic!("id"));
    let tt = class_ty(&mut h, "T", guess);
    let mixins = h.b.list(&[tt]);
    h.tick();
    let u = h.b.item(Item::new(
        None,
        ItemKind::MixinUse(hir_lang::MixinUseDef {
            mixins,
            rules: hir_lang::List::EMPTY,
        }),
    ));
    let items = h.b.list(&[u]);
    let t = h.b.item(Item::new(
        Some(tn),
        ItemKind::Class(ClassDef {
            items,
            mixin: true,
            ..ClassDef::default()
        }),
    ));
    assert_eq!(t, guess);
    let (hir, names) = h.finish(&[t], None);
    assert!(matches!(
        bcgen_lang::compile(&hir, &names).unwrap_err(),
        CompileError::Class {
            problem: bcgen_lang::ClassProblem::Cycle,
            ..
        }
    ));
}

#[test]
fn huge_member_counts_compile_within_the_budget_or_hit_it() {
    // 20,000 properties and 20,000 methods on one class: compiles, loads,
    // and runs.
    let mut h = H::new();
    let mut fields = Vec::new();
    for i in 0..20_000 {
        let v = h.int(i);
        fields.push(h.prop(&format!("p{i}"), hir_lang::Vis::Public, Some(v)));
    }
    let mut methods = Vec::new();
    for i in 0..20_000 {
        let (tp, _) = h.this_param();
        let v = h.int(i);
        let body = h.block(&[], Some(v));
        methods.push(h.method_item(&format!("m{i}"), hir_lang::Vis::Public, &[tp], body));
    }
    let c = h.class("Big", None, &fields, &methods);
    let cr = h.item_ref("Big", c);
    let f = h.extern_ref("mox.new");
    let o = h.call(f, &[cr]);
    let call = h.method(o, "m19999", &[]);
    let (hir, names) = h.finish(&[c], Some(call));
    let opts = entry().with_intrinsics(bcgen_lang::Intrinsics::mox());
    let out = Compiler::new(opts.clone())
        .compile(&hir, &names)
        .unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(run(&out), Value::Int(19_999));
    // The same class under a small budget: a budget error, not a panic.
    let e = Compiler::new(opts.with_max_instructions(10_000))
        .compile(&hir, &names)
        .unwrap_err();
    assert!(matches!(e, CompileError::BudgetExceeded { .. }), "{e:?}");
}

#[test]
fn a_deep_chain_with_many_members_hits_the_budget_not_quadratic_time() {
    // 256 classes, each adding 250 properties (64,000 slots in the
    // deepest, under the 65,536 limit): the layouts are 256 * 257 / 2 * 250
    // slots (8.2 million), charged to the budget.
    let mut h = H::new();
    let mut items: Vec<hir_lang::ItemId> = Vec::new();
    for i in 0..256 {
        let fields: Vec<_> = (0..250)
            .map(|j| h.prop(&format!("p{i}_{j}"), hir_lang::Vis::Public, None))
            .collect();
        let bases = match items.last() {
            Some(&prev) => {
                let t = class_ty(&mut h, &format!("C{}", i - 1), prev);
                h.b.list(&[t])
            }
            None => hir_lang::List::EMPTY,
        };
        let fl = h.b.list(&fields);
        h.tick();
        let name = h.name(&format!("C{i}"));
        items.push(h.b.item(Item::new(
            Some(name),
            ItemKind::Class(ClassDef {
                bases,
                fields: fl,
                ..ClassDef::default()
            }),
        )));
    }
    let (hir, names) = h.finish(&items, None);
    let t = std::time::Instant::now();
    let e = Compiler::new(entry().with_max_instructions(1 << 22))
        .compile(&hir, &names)
        .unwrap_err();
    assert!(matches!(e, CompileError::BudgetExceeded { .. }), "{e:?}");
    assert!(t.elapsed() < std::time::Duration::from_secs(20));
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
fn a_reference_to_an_appended_element_is_reported() {
    // $a[] = &$r: the new element's key is known only after the append.
    let e = unsupported(|h| {
        let a = h.local("a");
        let arr = h.array(&[]);
        let la = h.let_(a, Some(arr));
        let r = h.local("r");
        let nil = h.nil();
        let lr = h.let_(r, Some(nil));
        let va = h.var(a);
        let app = h.append(va);
        let vr = h.var(r);
        let x = h.expr(Expr::RefAssign {
            target: app,
            source: vr,
        });
        let body = h.block(&[la, lr], Some(x));
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
    assert!(matches!(e, CompileError::UnknownIntrinsic { .. }), "{e:?}");
    let e = unsupported(|h| {
        let one = h.int(1);
        let two = h.int(2);
        let x = h.intrinsic("len", &[one, two]);
        (vec![], Some(x))
    });
    assert!(
        matches!(
            e,
            CompileError::IntrinsicArity { arity, found: 2, .. } if arity == bcgen_lang::Arity::exact(1)
        ),
        "{e:?}"
    );
}
