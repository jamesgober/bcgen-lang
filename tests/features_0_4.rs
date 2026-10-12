//! The 0.4 options that are not about classes: PHP's ignored extra
//! arguments (`Options::with_ignore_extra`, ISSUES P34) and string-offset
//! reads through an intrinsic (`Options::with_string_offsets`, ISSUES P38),
//! end to end on bvm-lang 2.0.0-alpha.4.

mod common;

use std::sync::{Arc, Mutex};

use bcgen_lang::{Arity, BodyMode, CompileError, Compiler, Fast, Intrinsics, LsbOp, Options};
use bvm_lang::{Program, Vm, VmError};
use bytecode_lang::ErrorKind;
use common::hb::H;
use common::{RV, to_rv};
use hir_lang::{Arg, ArgKind, DefaultEval, Hir, ParamKind};
use intern_lang::Interner;

fn run(hir: &Hir, names: &Interner, opts: Options) -> (Result<RV, u32>, Vec<String>) {
    let out = Compiler::new(opts.with_body(BodyMode::Entry))
        .compile(hir, names)
        .unwrap_or_else(|e| panic!("compile error: {e}"));
    let printed = Arc::new(Mutex::new(Vec::new()));
    let mut host = common::host(printed.clone());
    let _ = host.register("mox", "str_offset", |_, _| {
        Err(bvm_lang::HostError::Raise(ErrorKind::IndexOutOfBounds))
    });
    let program =
        Program::load(out.module().clone(), &host).unwrap_or_else(|e| panic!("load error: {e}"));
    let mut vm = Vm::new(&program);
    let r = match vm.run(out.entry(), &[]) {
        Ok(v) => Ok(to_rv(&vm, v, 0)),
        Err(VmError::Raised { kind, .. }) => Err(kind.code()),
        Err(e) => panic!("unexpected: {e:?}"),
    };
    let p = printed.lock().map(|v| v.clone()).unwrap_or_default();
    (r, p)
}

/// `function f($a, $b = 2) { return $a + $b; }` called `f(1, 10, g())`
/// directly, through a function value, and with a spread of three.
fn extra_args() -> (Hir, Interner) {
    let mut h = H::new();
    let (pa, a) = h.param("a", ParamKind::Normal, None, false);
    let two = h.int(2);
    let (pb, b) = h.param("b", ParamKind::Normal, Some(two), false);
    let va = h.var(a);
    let vb = h.var(b);
    let sum = h.op(hir_lang::OpKind::Add, &[va, vb]);
    let body = h.block(&[], Some(sum));
    let f = h.func("f", &[pa, pb], body, DefaultEval::PerCall);
    // A side effect in the extra argument: PHP evaluates it.
    let e = h.extern_ref("echo");
    let x = h.str("evaluated");
    let side = h.call(e, &[x]);
    let fr = h.item_ref("f", f);
    let one = h.int(1);
    let ten = h.int(10);
    let direct = h.call(fr, &[one, ten, side]);
    let fr = h.item_ref("f", f);
    let fv = h.local("fv");
    let lf = h.let_(fv, Some(fr));
    let vf = h.var(fv);
    let one = h.int(1);
    let ten = h.int(10);
    let three = h.int(3);
    let dynamic = h.call(vf, &[one, ten, three]);
    let fr = h.item_ref("f", f);
    let one = h.int(1);
    let ten = h.int(10);
    let three = h.int(3);
    let arr = h.array(&[one, ten, three]);
    let spread = Arg {
        kind: ArgKind::Spread,
        value: arr,
        place: false,
    };
    let spreads = h.call_args(fr, &[spread]);
    let sum = h.op(hir_lang::OpKind::Add, &[direct, dynamic]);
    let sum = h.op(hir_lang::OpKind::Add, &[sum, spreads]);
    let body = h.block(&[lf], Some(sum));
    h.finish(&[f], Some(body))
}

#[test]
fn extra_arguments_are_ignored_when_the_language_says_so() {
    let (hir, names) = extra_args();
    let (r, printed) = run(&hir, &names, Options::new().with_ignore_extra(true));
    assert_eq!(r, Ok(RV::Int(33)));
    assert_eq!(printed, vec!["evaluated".to_string()]);
    // Python's rule (the default): too many arguments raise at the call.
    let (r, printed) = run(&hir, &names, Options::new());
    assert_eq!(r, Err(ErrorKind::ArgumentError.code()));
    // The direct call's arguments were evaluated before it raised.
    assert_eq!(printed, vec!["evaluated".to_string()]);
    // Every parameter list says so.
    let out = Compiler::new(Options::new().with_ignore_extra(true))
        .compile(&hir, &names)
        .unwrap_or_else(|e| panic!("{e}"));
    let f = out
        .module()
        .functions()
        .iter()
        .find(|f| f.params().is_some());
    assert!(f.is_some_and(|f| f.params().is_some_and(|p| p.ignore_extra)));
}

/// `$s = "abc"; [$s[0], $s[1], $s[-1], $s[5]]` (the last out of range).
fn offsets(last: bool) -> (Hir, Interner) {
    let mut h = H::new();
    let s = h.local("s");
    let abc = h.str("abc");
    let ls = h.let_(s, Some(abc));
    let mut elems = Vec::new();
    let idx: &[i64] = if last { &[0, 1, -1, 5] } else { &[0, 1, -1] };
    for &i in idx {
        let v = h.var(s);
        let k = h.int(i);
        elems.push(h.index(v, k));
    }
    let arr = h.array(&elems);
    let body = h.block(&[ls], Some(arr));
    h.finish(&[], Some(body))
}

#[test]
fn string_offsets_read_through_the_configured_intrinsic() {
    let (hir, names) = offsets(false);
    let mox = Options::new()
        .with_intrinsics(Intrinsics::mox())
        .with_string_offsets("mox.str_offset");
    let (r, _) = run(&hir, &names, mox.clone());
    let s = |x: &str| RV::Str(x.as_bytes().to_vec());
    assert_eq!(
        r,
        Ok(RV::Map(vec![
            (RV::Int(0), s("a")),
            (RV::Int(1), s("b")),
            (RV::Int(2), s("c")),
        ]))
    );
    // Out of range: the host function decides (the stand-in raises).
    let (hir2, names2) = offsets(true);
    let (r, _) = run(&hir2, &names2, mox);
    assert_eq!(r, Err(ErrorKind::IndexOutOfBounds.code()));
    // Without the option, LSB's answer: the byte. (`$s[-1]` is out of range
    // for `dget_index`.)
    let (r, _) = run(&hir, &names, Options::new());
    assert_eq!(r, Err(ErrorKind::IndexOutOfBounds.code()));
}

#[test]
fn string_offsets_through_a_place_and_an_lsb_or_host_lowering() {
    // A table where the offset read is a plain host function.
    let (hir, names) = offsets(false);
    let t = Intrinsics::core().with_host("lang.offset", Arity::exact(2), "mox", "str_offset");
    let (r, _) = run(
        &hir,
        &names,
        Options::new()
            .with_intrinsics(t)
            .with_string_offsets("lang.offset"),
    );
    assert_eq!(r, Err(ErrorKind::IndexOutOfBounds.code()));
    // An entry that is missing, takes another arity, or is a class operation
    // is refused when the options are checked.
    for (table, name) in [
        (Intrinsics::core(), "missing"),
        (Intrinsics::core(), "len"),
        (Intrinsics::mox(), "mox.new"),
    ] {
        let e = Compiler::new(
            Options::new()
                .with_intrinsics(table)
                .with_string_offsets(name),
        )
        .compile(&hir, &names);
        assert_eq!(
            e.err(),
            Some(CompileError::InvalidOption {
                option: "string_offsets"
            })
        );
    }
    // An LSB lowering of two operands is allowed (here: concatenation).
    let t = Intrinsics::core().with_lsb("cat", LsbOp::Concat);
    assert!(
        Compiler::new(Options::new().with_intrinsics(t).with_string_offsets("cat"))
            .compile(&hir, &names)
            .is_ok()
    );
    // The fast path's domain.
    assert_eq!(Fast::StrOffset.arity(), Arity::exact(2));
}

#[test]
fn string_offsets_inside_places_use_the_intrinsic() {
    // $s = "xyz"; let_place p = $s[2] in p  ->  "z"
    let mut h = H::new();
    let s = h.local("s");
    let xyz = h.str("xyz");
    let ls = h.let_(s, Some(xyz));
    let v = h.var(s);
    let two = h.int(2);
    let idx = h.index(v, two);
    let pb = h.place_binder("p");
    let pv = h.var(pb);
    let lp = h.let_place(pb, idx, pv);
    let body = h.block(&[ls], Some(lp));
    let (hir, names) = h.finish(&[], Some(body));
    let (r, _) = run(
        &hir,
        &names,
        Options::new()
            .with_intrinsics(Intrinsics::mox())
            .with_string_offsets("mox.str_offset"),
    );
    assert_eq!(r, Ok(RV::Str(b"z".to_vec())));
}
