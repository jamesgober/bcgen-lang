//! The DIRECTIVES §4 invariants, as properties over random programs:
//! every module loads in bvm-lang (whose load-time checks reject any
//! out-of-range register, window, constant, or branch target), survives the
//! LSB encoding, maps every instruction back to a node of the unit, and
//! compiles deterministically.

mod common;

use bcgen_lang::{Compiler, LineIndex, Options};
use bvm_lang::{Host, Program};
use common::{Profile, progs};
use hir_lang::{Hir, NodeRef};
use proptest::prelude::*;

fn node_exists(hir: &Hir, n: NodeRef) -> bool {
    match n {
        NodeRef::Item(i) => hir.get_item(i).is_some(),
        NodeRef::Expr(e) => hir.get_expr(e).is_some(),
        NodeRef::Stmt(s) => hir.get_stmt(s).is_some(),
        NodeRef::Pat(p) => hir.get_pat(p).is_some(),
        NodeRef::Param(p) => hir.get_param(p).is_some(),
        NodeRef::Path(p) => hir.get_path(p).is_some(),
        NodeRef::Ty(t) => hir.get_ty(t).is_some(),
        NodeRef::Field(f) => hir.get_field(f).is_some(),
        NodeRef::Variant(v) => hir.variant(v).is_some(),
    }
}

/// A host that binds every import the programs use.
fn host() -> Host {
    common::host(std::sync::Arc::new(std::sync::Mutex::new(Vec::new())))
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 400, ..ProptestConfig::default() })]

    #[test]
    fn every_module_loads_and_round_trips(seed in any::<u64>()) {
        let (hir, names) = progs::program(seed);
        for profile in [Profile::PHP, Profile::REFERENCE] {
            let out = common::compile(&hir, &names, profile);
            let module = out.module().clone();
            let bytes = bytecode_lang::encode(&module);
            let back = bytecode_lang::decode(&bytes).expect("decodes");
            prop_assert_eq!(&back, &module);
            prop_assert!(Program::load(module, &host()).is_ok());
            prop_assert!(Program::decode(&bytes, &host()).is_ok());
        }
    }

    #[test]
    fn every_instruction_maps_to_a_node_of_the_unit(seed in any::<u64>()) {
        let (hir, names) = progs::program(seed);
        let out = common::compile(&hir, &names, Profile::PHP);
        for (i, f) in out.module().functions().iter().enumerate() {
            let id = bytecode_lang::FuncId(i as u32);
            prop_assert_eq!(out.origins(id).len(), f.code().len());
            for pc in 0..f.code().len() {
                let n = out.origin(id, pc as u32);
                prop_assert!(n.is_some_and(|n| node_exists(&hir, n)));
            }
            // Line rows: strictly increasing pcs inside the code.
            let rows = f.lines();
            prop_assert!(rows.windows(2).all(|w| w[0].pc < w[1].pc));
            prop_assert!(rows.iter().all(|r| (r.pc as usize) < f.code().len()));
        }
    }

    #[test]
    fn compilation_is_deterministic(seed in any::<u64>()) {
        let (hir, names) = progs::program(seed);
        let a = common::compile(&hir, &names, Profile::PHP);
        let b = common::compile(&hir.clone(), &names, Profile::PHP);
        prop_assert_eq!(bytecode_lang::encode(a.module()), bytecode_lang::encode(b.module()));
        prop_assert_eq!(a, b);
        // And on another thread.
        let c = std::thread::scope(|s| s.spawn(|| common::compile(&hir, &names, Profile::PHP)).join().expect("thread"));
        prop_assert_eq!(bytecode_lang::encode(c.module()), bytecode_lang::encode(common::compile(&hir, &names, Profile::PHP).module()));
    }
}

#[test]
fn line_rows_follow_the_locator() {
    // The e2e-sized unit: every row's line is a real line of the text.
    let (hir, names) = progs::program(7);
    let text = "x\n".repeat(10_000);
    let lines = LineIndex::new("gen.mox", 0, &text);
    let out = Compiler::new(Options::new())
        .with_locator(&lines)
        .compile(&hir, &names)
        .expect("compiles");
    let file = out
        .module()
        .strings()
        .position(|s| s == "gen.mox")
        .expect("file name interned");
    for f in out.module().functions() {
        for r in f.lines() {
            assert_eq!(r.file.index(), file);
            assert!(r.line >= 1);
        }
    }
}

#[test]
fn errors_map_back_to_their_source_line() {
    // Line 1: let a = 1;   Line 2: let b = a / 0;   (spans set by hand)
    use common::hb::H;
    use hir_lang::{OpKind, Span};
    let src = "let a = 1;\nlet b = a / 0;\n";
    let mut h = H::new();
    let a = h.local("a");
    h.b.set_span(Span::new(8, 9));
    let one = h.b.int(1);
    h.b.set_span(Span::new(0, 10));
    let pa = h.b.bind(a);
    let la = h.b.let_stmt(pa, Some(one));
    h.b.set_span(Span::new(19, 20));
    let ua = h.b.use_binder(a);
    h.b.set_span(Span::new(23, 24));
    let zero = h.b.int(0);
    h.b.set_span(Span::new(19, 24));
    let div = h.b.op(OpKind::Div, &[ua, zero]);
    let body = h.b.block(&[la], Some(div));
    let (hir, names) = h.finish(&[], Some(body));
    let lines = LineIndex::new("app.mox", 0, src);
    let opts = Options::new().with_body(bcgen_lang::BodyMode::Entry);
    let out = Compiler::new(opts)
        .with_locator(&lines)
        .compile(&hir, &names)
        .expect("compiles");
    let program = Program::load(out.module().clone(), &Host::new()).expect("loads");
    let err = bvm_lang::Vm::new(&program)
        .run(out.entry(), &[])
        .unwrap_err();
    let (func, pc) = err.location().expect("located");
    assert_eq!(out.origin(func, pc), Some(NodeRef::Expr(div)));
    assert_eq!(
        program.location(func, pc).expect("row").to_string(),
        "app.mox:2:9"
    );
}
