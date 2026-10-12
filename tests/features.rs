//! One program per feature, run on bvm-lang and on the reference
//! interpreter: both must agree, and on the expected value.

mod common;

use common::hb::H;
use common::{Outcome, Profile, RV, check};
use hir_lang::{
    Arg, CaptureMode, DefaultEval, Expr, Lit, Op, OpKind, Overflow, ParamKind, Pat, Prim, Ty,
};

fn both(h: H, items: &[hir_lang::ItemId], body: hir_lang::ExprId) -> (Outcome, Outcome) {
    let (hir, names) = h.finish(items, Some(body));
    let php = check(&hir, &names, Profile::PHP);
    let rf = check(&hir, &names, Profile::REFERENCE);
    (php, rf)
}

fn value(h: H, items: &[hir_lang::ItemId], body: hir_lang::ExprId) -> RV {
    let (php, _) = both(h, items, body);
    match php {
        Outcome::Value(v) => v,
        o => panic!("expected a value, got {o:?}"),
    }
}

fn s(x: &str) -> RV {
    RV::Str(x.as_bytes().to_vec())
}

fn list(xs: &[i64]) -> RV {
    RV::Map(
        xs.iter()
            .enumerate()
            .map(|(i, &x)| (RV::Int(i as i64), RV::Int(x)))
            .collect(),
    )
}

#[test]
fn arithmetic_under_policies() {
    let mut h = H::new();
    let max = h.int(i64::MAX);
    let one = h.int(1);
    let wrap = h.op_with(
        Op::new(OpKind::Add).with_overflow(Overflow::Wrap),
        &[max, one],
    );
    let max2 = h.int(i64::MAX);
    let one2 = h.int(1);
    let promote = h.op_with(
        Op::new(OpKind::Add).with_overflow(Overflow::Promote),
        &[max2, one2],
    );
    let seven = h.int(7);
    let two = h.int(2);
    let div = h.op_with(
        Op::new(OpKind::Div).with_overflow(Overflow::Promote),
        &[seven, two],
    );
    let m7 = h.float(-7.0);
    let f2 = h.float(2.0);
    let fdiv = h.op(OpKind::FloorDiv, &[m7, f2]);
    let a = h.int(3);
    let b = h.float(3.0);
    let eq = h.op(OpKind::Eq, &[a, b]);
    let body = h.array(&[wrap, promote, div, fdiv, eq]);
    let v = value(h, &[], body);
    assert_eq!(
        v,
        RV::Map(vec![
            (RV::Int(0), RV::Int(i64::MIN)),
            (RV::Int(1), RV::float(9_223_372_036_854_775_808.0)),
            (RV::Int(2), RV::float(3.5)),
            (RV::Int(3), RV::float(-4.0)),
            (RV::Int(4), RV::Bool(true)),
        ])
    );
}

#[test]
fn overflow_error_is_raised_at_the_op() {
    let mut h = H::new();
    let max = h.int(i64::MAX);
    let one = h.int(1);
    let add = h.op(OpKind::Add, &[max, one]);
    let (hir, names) = h.finish(&[], Some(add));
    let o = check(&hir, &names, Profile::PHP);
    assert_eq!(
        o,
        Outcome::Raised {
            code: 1,
            node: hir_lang::NodeRef::Expr(add)
        }
    );
}

#[test]
fn loops_break_continue_labels() {
    // let i = 0; let sum = 0;
    // 'outer: loop [step: i = i + 1] { if i >= 10 { break 'outer sum }; if i % 2 == 0 { continue }; sum = sum + i }
    let mut h = H::new();
    let i = h.local("i");
    let sum = h.local("sum");
    let outer = h.label("outer");
    let z1 = h.int(0);
    let li = h.let_(i, Some(z1));
    let z2 = h.int(0);
    let ls = h.let_(sum, Some(z2));
    let vi = h.var(i);
    let ten = h.int(10);
    let ge = h.op(OpKind::Ge, &[vi, ten]);
    let vs = h.var(sum);
    let brk = h.brk(Some(outer), Some(vs));
    let bb = h.block(&[], Some(brk));
    let if1 = h.if_(ge, bb, None);
    let s1 = h.stmt(if1);
    let vi2 = h.var(i);
    let two = h.int(2);
    let rem = h.op(OpKind::Rem, &[vi2, two]);
    let zero = h.int(0);
    let iseven = h.op(OpKind::Eq, &[rem, zero]);
    let c = h.cont(None);
    let cb = h.block(&[], Some(c));
    let if2 = h.if_(iseven, cb, None);
    let s2 = h.stmt(if2);
    let vs2 = h.var(sum);
    let vi3 = h.var(i);
    let add = h.op(OpKind::Add, &[vs2, vi3]);
    let ts = h.var(sum);
    let asg = h.assign(ts, add);
    let s3 = h.stmt(asg);
    let body = h.block(&[s1, s2, s3], None);
    let ti = h.var(i);
    let vi4 = h.var(i);
    let one = h.int(1);
    let inc = h.op(OpKind::Add, &[vi4, one]);
    let step = h.assign(ti, inc);
    let lp = h.loop_(Some(outer), body, Some(step));
    let top = h.block(&[li, ls], Some(lp));
    assert_eq!(value(h, &[], top), RV::Int(1 + 3 + 5 + 7 + 9));
}

#[test]
fn functions_defaults_named_rest() {
    // fn f(a, b = a * 10, ...rest, *, tag = "t") { [a, b, rest, tag] }
    let mut h = H::new();
    let (pa, a) = h.param("a", ParamKind::Normal, None, false);
    let va = h.var(a);
    let ten = h.int(10);
    let dflt = h.op(OpKind::Mul, &[va, ten]);
    let (pb, b) = h.param("b", ParamKind::Normal, Some(dflt), false);
    let (pr, r) = h.param("rest", ParamKind::Rest, None, false);
    let tdef = h.str("t");
    let (pt, t) = h.param("tag", ParamKind::NamedOnly, Some(tdef), false);
    let (xa, xb, xr, xt) = (h.var(a), h.var(b), h.var(r), h.var(t));
    let arr = h.array(&[xa, xb, xr, xt]);
    let fb = h.block(&[], Some(arr));
    let f = h.func("f", &[pa, pb, pr, pt], fb, DefaultEval::PerCall);
    // [f(1), f(1, 2, 3, 4), f(5, tag: "x"), (f)(6)]
    let c1 = h.item_ref("f", f);
    let one = h.int(1);
    let call1 = h.call(c1, &[one]);
    let c2 = h.item_ref("f", f);
    let args: Vec<_> = (1..=4).map(|x| h.int(x)).collect();
    let call2 = h.call(c2, &args);
    let c3 = h.item_ref("f", f);
    let five = h.int(5);
    let x = h.str("x");
    let tagarg = h.named("tag", x);
    let call3 = h.call_args(c3, &[Arg::positional(five), tagarg]);
    // A dynamic call: the function as a value.
    let fv = h.local("fv");
    let c4 = h.item_ref("f", f);
    let lf = h.let_(fv, Some(c4));
    let vf = h.var(fv);
    let six = h.int(6);
    let call4 = h.call(vf, &[six]);
    let arr = h.array(&[call1, call2, call3, call4]);
    let body = h.block(&[lf], Some(arr));
    let v = value(h, &[f], body);
    let e = |a: i64, b: i64, rest: &[i64], tag: &str| {
        RV::Map(vec![
            (RV::Int(0), RV::Int(a)),
            (RV::Int(1), RV::Int(b)),
            (RV::Int(2), list(rest)),
            (RV::Int(3), s(tag)),
        ])
    };
    assert_eq!(
        v,
        RV::Map(vec![
            (RV::Int(0), e(1, 10, &[], "t")),
            (RV::Int(1), e(1, 2, &[3, 4], "t")),
            (RV::Int(2), e(5, 50, &[], "x")),
            (RV::Int(3), e(6, 60, &[], "t")),
        ])
    );
}

#[test]
fn argument_errors_raise_at_the_call() {
    // fn g(a) { a }   g(1, 2)  -> ArgumentError (E0114) at the call
    let mut h = H::new();
    let (pa, a) = h.param("a", ParamKind::Normal, None, false);
    let va = h.var(a);
    let gb = h.block(&[], Some(va));
    let g = h.func("g", &[pa], gb, DefaultEval::PerCall);
    let c = h.item_ref("g", g);
    let one = h.int(1);
    let two = h.int(2);
    let call = h.call(c, &[one, two]);
    let (hir, names) = h.finish(&[g], Some(call));
    let o = check(&hir, &names, Profile::PHP);
    assert_eq!(
        o,
        Outcome::Raised {
            code: 114,
            node: hir_lang::NodeRef::Expr(call)
        }
    );
}

#[test]
fn closures_capture_by_value_and_by_reference() {
    // let n = 1; let byval = closure[by-value n] () => n; let byref = closure implicit=by-ref () => n;
    // n = 5; [byval(), byref()]
    let mut h = H::new();
    let n = h.local("n");
    let one = h.int(1);
    let ln = h.let_(n, Some(one));
    let (cap, inner) = h.capture(n, "n", CaptureMode::ByValue);
    let vin = h.var(inner);
    let cb1 = h.closure(&[], vin, None, &[cap], None, DefaultEval::PerCall);
    let byval = h.local("byval");
    let l1 = h.let_(byval, Some(cb1));
    let vn = h.var(n);
    let cb2 = h.closure(
        &[],
        vn,
        Some(CaptureMode::ByRef),
        &[],
        None,
        DefaultEval::PerCall,
    );
    let byref = h.local("byref");
    let l2 = h.let_(byref, Some(cb2));
    let tn = h.var(n);
    let five = h.int(5);
    let asg = h.assign(tn, five);
    let s3 = h.stmt(asg);
    let f1 = h.var(byval);
    let c1 = h.call(f1, &[]);
    let f2 = h.var(byref);
    let c2 = h.call(f2, &[]);
    let arr = h.array(&[c1, c2]);
    let body = h.block(&[ln, l1, l2, s3], Some(arr));
    assert_eq!(value(h, &[], body), list(&[1, 5]));
}

#[test]
fn recursive_closure_through_its_self_binder() {
    // let fact = closure self=me (n) => if n <= 1 { 1 } else { n * me(n - 1) }; fact(10)
    let mut h = H::new();
    let me = h.self_binder("me");
    let (pn, n) = h.param("n", ParamKind::Normal, None, false);
    let vn = h.var(n);
    let one = h.int(1);
    let le = h.op(OpKind::Le, &[vn, one]);
    let one2 = h.int(1);
    let vn2 = h.var(n);
    let vme = h.var(me);
    let vn3 = h.var(n);
    let one3 = h.int(1);
    let dec = h.op(OpKind::Sub, &[vn3, one3]);
    let rec = h.call(vme, &[dec]);
    let mul = h.op(OpKind::Mul, &[vn2, rec]);
    let ife = h.if_(le, one2, Some(mul));
    let clo = h.closure(
        &[pn],
        ife,
        Some(CaptureMode::ByRef),
        &[],
        Some(me),
        DefaultEval::PerCall,
    );
    let fact = h.local("fact");
    let lf = h.let_(fact, Some(clo));
    let vf = h.var(fact);
    let ten = h.int(10);
    let call = h.call(vf, &[ten]);
    let body = h.block(&[lf], Some(call));
    assert_eq!(value(h, &[], body), RV::Int(3_628_800));
}

#[test]
fn php_arrays_are_values() {
    // let a = [1, [2]]; let b = a; b[0] = 9; b[1][] = 3; let c = []; c['x']['y'] = 1; [a, b, c]
    let mut h = H::new();
    let a = h.local("a");
    let b = h.local("b");
    let c = h.local("c");
    let one = h.int(1);
    let two = h.int(2);
    let inner = h.array(&[two]);
    let arr = h.array(&[one, inner]);
    let la = h.let_(a, Some(arr));
    let va = h.var(a);
    let lb = h.let_(b, Some(va));
    let vb = h.var(b);
    let z = h.int(0);
    let ix = h.index(vb, z);
    let nine = h.int(9);
    let s1 = h.assign(ix, nine);
    let s1 = h.stmt(s1);
    let vb2 = h.var(b);
    let o = h.int(1);
    let ix2 = h.index(vb2, o);
    let ap = h.append(ix2);
    let three = h.int(3);
    let s2 = h.assign(ap, three);
    let s2 = h.stmt(s2);
    let empty = h.array(&[]);
    let lc = h.let_(c, Some(empty));
    let vc = h.var(c);
    let kx = h.str("x");
    let ky = h.str("y");
    let i1 = h.index(vc, kx);
    let i2 = h.index(i1, ky);
    let one2 = h.int(1);
    let s3 = h.assign(i2, one2);
    let s3 = h.stmt(s3);
    let (ra, rb, rc) = (h.var(a), h.var(b), h.var(c));
    let out = h.array(&[ra, rb, rc]);
    let body = h.block(&[la, lb, s1, s2, lc, s3], Some(out));
    let (php, rf) = both(h, &[], body);
    let Outcome::Value(v) = php else {
        panic!("{php:?}")
    };
    assert_eq!(
        v,
        RV::Map(vec![
            (
                RV::Int(0),
                RV::Map(vec![(RV::Int(0), RV::Int(1)), (RV::Int(1), list(&[2]))])
            ),
            (
                RV::Int(1),
                RV::Map(vec![(RV::Int(0), RV::Int(9)), (RV::Int(1), list(&[2, 3]))])
            ),
            (
                RV::Int(2),
                RV::Map(vec![(s("x"), RV::Map(vec![(s("y"), RV::Int(1))]))])
            ),
        ])
    );
    // Shared references: the copy is the same array; writing into a
    // missing key is an error.
    assert!(matches!(rf, Outcome::Raised { code: 103, .. }), "{rf:?}");
}

#[test]
fn php_keys_are_normalized() {
    // let m = []; m["1"] = "a"; m[1.9] = "b"; m[true] = "c"; m[null] = "d"; m["01"] = "e"; m
    let mut h = H::new();
    let m = h.local("m");
    let e = h.array(&[]);
    let lm = h.let_(m, Some(e));
    let mut stmts = vec![lm];
    let ks: Vec<hir_lang::ExprId> = vec![
        h.str("1"),
        h.float(1.9),
        h.boolean(true),
        h.nil(),
        h.str("01"),
    ];
    for (k, v) in ks.into_iter().zip(["a", "b", "c", "d", "e"]) {
        let vm = h.var(m);
        let ix = h.index(vm, k);
        let val = h.str(v);
        let a = h.assign(ix, val);
        stmts.push(h.stmt(a));
    }
    let vm = h.var(m);
    let body = h.block(&stmts, Some(vm));
    let v = value(h, &[], body);
    assert_eq!(
        v,
        RV::Map(vec![
            (RV::Int(1), s("c")),
            (s(""), s("d")),
            (s("01"), s("e"))
        ])
    );
}

#[test]
fn try_catch_finally() {
    // try { 1 / 0 } catch e => { "caught" } finally { echo("fin") }
    let mut h = H::new();
    let one = h.int(1);
    let zero = h.int(0);
    let div = h.op(OpKind::Div, &[one, zero]);
    let e = h.local("e");
    let pe = h.pbind(e);
    let caught = h.str("caught");
    let arm = h.arm(pe, None, caught);
    let echo = h.extern_ref("echo");
    let fin = h.str("fin");
    let call = h.call(echo, &[fin]);
    let t = h.try_(div, &[arm], Some(call));
    let (hir, names) = h.finish(&[], Some(t));
    assert_eq!(
        check(&hir, &names, Profile::PHP),
        Outcome::Value(s("caught"))
    );
}

#[test]
fn return_and_break_out_of_finally_override() {
    // fn f() { try { return 1 } finally { return 2 } }
    // fn g() { loop { try { throw 5 } finally { break } }; 3 }
    let mut h = H::new();
    let one = h.int(1);
    let r1 = h.ret(Some(one));
    let two = h.int(2);
    let r2 = h.ret(Some(two));
    let t = h.try_(r1, &[], Some(r2));
    let fb = h.block(&[], Some(t));
    let f = h.func("f", &[], fb, DefaultEval::PerCall);
    let five = h.int(5);
    let th = h.throw(five);
    let br = h.brk(None, None);
    let t2 = h.try_(th, &[], Some(br));
    let lp = h.loop_(None, t2, None);
    let s1 = h.stmt(lp);
    let three = h.int(3);
    let gb = h.block(&[s1], Some(three));
    let g = h.func("g", &[], gb, DefaultEval::PerCall);
    let cf = h.item_ref("f", f);
    let c1 = h.call(cf, &[]);
    let cg = h.item_ref("g", g);
    let c2 = h.call(cg, &[]);
    let arr = h.array(&[c1, c2]);
    assert_eq!(value(h, &[f, g], arr), list(&[2, 3]));
}

#[test]
fn uncaught_throw_reports_the_rethrowing_try() {
    // try { throw 7 } catch 1 => 0   (no arm matches 7: rethrown by the try)
    let mut h = H::new();
    let seven = h.int(7);
    let th = h.throw(seven);
    let p = h.pat(Pat::Lit(Lit::Int(hir_lang::IntLit::new(1))));
    let z = h.int(0);
    let arm = h.arm(p, None, z);
    let t = h.try_(th, &[arm], None);
    let (hir, names) = h.finish(&[], Some(t));
    assert_eq!(
        check(&hir, &names, Profile::PHP),
        Outcome::Thrown {
            value: RV::Int(7),
            node: hir_lang::NodeRef::Expr(t)
        }
    );
}

#[test]
fn match_sequential_patterns() {
    // [ m(0), m(5), m(15), m([1, 2]), m("s"), m(0.5) ] where
    // m(x) = match x { 0 => "zero", 1..=9 => "small", (a, b) => a + b, s: str => "str",
    //                  y if y > 10 => "big", _ => null }
    let mut h = H::new();
    let (px, x) = h.param("x", ParamKind::Normal, None, false);
    let vx = h.var(x);
    let p0 = h.pat(Pat::Lit(Lit::Int(hir_lang::IntLit::new(0))));
    let zero = h.str("zero");
    let a0 = h.arm(p0, None, zero);
    let lo = h.pat(Pat::Lit(Lit::Int(hir_lang::IntLit::new(1))));
    let hi = h.pat(Pat::Lit(Lit::Int(hir_lang::IntLit::new(9))));
    let pr = h.pat(Pat::Range {
        lo: Some(lo),
        hi: Some(hi),
        inclusive: true,
    });
    let small = h.str("small");
    let a1 = h.arm(pr, None, small);
    let a = h.local("a");
    let b = h.local("b");
    let pa = h.pbind(a);
    let pb = h.pbind(b);
    let elems = h.b.list(&[pa, pb]);
    let pt = h.pat(Pat::Tuple { elems, rest: None });
    let (va, vb) = (h.var(a), h.var(b));
    let sum = h.op(OpKind::Add, &[va, vb]);
    let a2 = h.arm(pt, None, sum);
    let sty = h.ty(Ty::Prim(Prim::Str));
    let ps = h.pat(Pat::TypeTest { ty: sty, pat: None });
    let st = h.str("str");
    let a3 = h.arm(ps, None, st);
    let y = h.local("y");
    let py = h.pbind(y);
    let vy = h.var(y);
    let ten = h.int(10);
    let g = h.op(OpKind::Gt, &[vy, ten]);
    let big = h.str("big");
    let a4 = h.arm(py, Some(g), big);
    let w = h.pat(Pat::Wild);
    let null = h.nil();
    let a5 = h.arm(w, None, null);
    let m = h.match_(vx, &[a0, a1, a2, a3, a4, a5]);
    let mb = h.block(&[], Some(m));
    let mf = h.func("m", &[px], mb, DefaultEval::PerCall);
    let mut calls = Vec::new();
    let args: Vec<hir_lang::ExprId> = {
        let a0 = h.int(0);
        let a1 = h.int(5);
        let a2 = h.int(15);
        let one = h.int(1);
        let two = h.int(2);
        let a3 = h.array(&[one, two]);
        let a4 = h.str("s");
        let a5 = h.float(0.5);
        vec![a0, a1, a2, a3, a4, a5]
    };
    for a in args {
        let c = h.item_ref("m", mf);
        calls.push(h.call(c, &[a]));
    }
    let arr = h.array(&calls);
    let v = value(h, &[mf], arr);
    assert_eq!(
        v,
        RV::Map(vec![
            (RV::Int(0), s("zero")),
            (RV::Int(1), s("small")),
            (RV::Int(2), s("big")),
            (RV::Int(3), RV::Int(3)),
            (RV::Int(4), s("str")),
            (RV::Int(5), RV::Nil),
        ])
    );
}

#[test]
fn statics_and_globals() {
    // global G = 10;  fn tick() { static n = 0; n = n + 1; global G as g; g = g + n; n }
    // [tick(), tick(), tick(), G]
    let mut h = H::new();
    let ten = h.int(10);
    let gi = h.global("G", Some(ten));
    let n = h.local("n");
    let z = h.int(0);
    let st = h.raw_stmt(hir_lang::Stmt::Static {
        binder: n,
        ty: None,
        init: Some(z),
    });
    let tn = h.var(n);
    let vn = h.var(n);
    let one = h.int(1);
    let inc = h.op(OpKind::Add, &[vn, one]);
    let a1 = h.assign(tn, inc);
    let s1 = h.stmt(a1);
    let gl = h.local("g");
    let d = h.b.def(hir_lang::Def::Item(gi));
    let gp = h.path("G", hir_lang::Res::Def(d));
    let sg = h.raw_stmt(hir_lang::Stmt::Global {
        binder: gl,
        path: gp,
    });
    let tg = h.var(gl);
    let vg = h.var(gl);
    let vn2 = h.var(n);
    let add = h.op(OpKind::Add, &[vg, vn2]);
    let a2 = h.assign(tg, add);
    let s2 = h.stmt(a2);
    let vn3 = h.var(n);
    let fb = h.block(&[st, s1, sg, s2], Some(vn3));
    let tick = h.func("tick", &[], fb, DefaultEval::PerCall);
    let mut calls = Vec::new();
    for _ in 0..3 {
        let c = h.item_ref("tick", tick);
        calls.push(h.call(c, &[]));
    }
    let gv = h.item_ref("G", gi);
    calls.push(gv);
    let arr = h.array(&calls);
    assert_eq!(value(h, &[gi, tick], arr), list(&[1, 2, 3, 16]));
}

#[test]
fn strings_concat_len_index_and_echo() {
    let mut h = H::new();
    let a = h.str("ab");
    let b = h.str("cd");
    let cat = h.intrinsic("concat", &[a, b]);
    let x = h.local("x");
    let lx = h.let_(x, Some(cat));
    let echo = h.extern_ref("echo");
    let vx = h.var(x);
    let pr = h.call(echo, &[vx]);
    let s1 = h.stmt(pr);
    let vx2 = h.var(x);
    let len = h.intrinsic("len", &[vx2]);
    let vx3 = h.var(x);
    let two = h.int(2);
    let byte = h.index(vx3, two);
    let arr = h.array(&[len, byte]);
    let body = h.block(&[lx, s1], Some(arr));
    let (hir, names) = h.finish(&[], Some(body));
    let (o, printed) = common::run_bvm(&hir, &names, Profile::PHP, 1_000_000);
    assert_eq!(o, Outcome::Value(list(&[4, i64::from(b'c')])));
    assert_eq!(printed, vec!["abcd".to_string()]);
    let _ = check(&hir, &names, Profile::PHP);
}

#[test]
fn by_reference_parameters_and_reference_assignment() {
    // fn inc(&x) { x = x + 1 }   let a = 1; inc(&a); let b = &a (ref-assign); b = 10; [a, b]
    let mut h = H::new();
    let (px, x) = h.param("x", ParamKind::Normal, None, true);
    let tx = h.var(x);
    let vx = h.var(x);
    let one = h.int(1);
    let add = h.op(OpKind::Add, &[vx, one]);
    let asg = h.assign(tx, add);
    let fb = h.block(&[], Some(asg));
    let inc = h.func("inc", &[px], fb, DefaultEval::PerCall);
    let a = h.local("a");
    let b = h.local("b");
    let one2 = h.int(1);
    let la = h.let_(a, Some(one2));
    let c = h.item_ref("inc", inc);
    let va = h.var(a);
    let call = h.call_args(
        c,
        &[Arg {
            kind: hir_lang::ArgKind::Positional,
            value: va,
            place: true,
        }],
    );
    let s1 = h.stmt(call);
    let lb = h.let_(b, None);
    let tb = h.var(b);
    let sa = h.var(a);
    let ra = h.expr(Expr::RefAssign {
        target: tb,
        source: sa,
    });
    let s2 = h.stmt(ra);
    let tb2 = h.var(b);
    let ten = h.int(10);
    let a2 = h.assign(tb2, ten);
    let s3 = h.stmt(a2);
    let (ra, rb) = (h.var(a), h.var(b));
    let arr = h.array(&[ra, rb]);
    let body = h.block(&[la, s1, lb, s2, s3], Some(arr));
    assert_eq!(value(h, &[inc], body), list(&[10, 10]));
}

#[test]
fn method_calls_pass_the_receiver_first() {
    // let o = {"k": 5, "get": closure (self) => self["k"]}; o.get()
    let mut h = H::new();
    let (ps, sf) = h.param("self", ParamKind::Normal, None, false);
    let vs = h.var(sf);
    let k = h.str("k");
    let ix = h.index(vs, k);
    let clo = h.closure(&[ps], ix, None, &[], None, DefaultEval::PerCall);
    let k2 = h.str("k");
    let five = h.int(5);
    let g = h.str("get");
    let m = h.map(&[(Some(k2), five), (Some(g), clo)]);
    let o = h.local("o");
    let lo = h.let_(o, Some(m));
    let vo = h.var(o);
    let call = h.method(vo, "get", &[]);
    let body = h.block(&[lo], Some(call));
    assert_eq!(value(h, &[], body), RV::Int(5));
}

#[test]
fn defer_runs_last_registered_first() {
    // { defer echo("1"); defer echo("2"); echo("body"); 7 }
    let mut h = H::new();
    let mut stmts = Vec::new();
    for t in ["1", "2"] {
        let e = h.extern_ref("echo");
        let a = h.str(t);
        let c = h.call(e, &[a]);
        stmts.push(h.raw_stmt(hir_lang::Stmt::Defer(c)));
    }
    let e = h.extern_ref("echo");
    let a = h.str("body");
    let c = h.call(e, &[a]);
    stmts.push(h.stmt(c));
    let seven = h.int(7);
    let body = h.block(&stmts, Some(seven));
    let (hir, names) = h.finish(&[], Some(body));
    let (o, printed) = common::run_bvm(&hir, &names, Profile::PHP, 1_000_000);
    assert_eq!(o, Outcome::Value(RV::Int(7)));
    assert_eq!(printed, vec!["body", "2", "1"]);
    let _ = check(&hir, &names, Profile::PHP);
}
