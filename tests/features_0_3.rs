//! The 0.3 forms end to end (HIR v3 → LSB format 2 → bvm-lang 2.0.0-alpha.3):
//! generators (keyed yields, `yield from`, sends, throws), `await` and
//! `spawn`, `let_place`, PHP references into array elements, OPS v2 `pow`,
//! `bit_not`, saturating shifts, `NoMatch`, union and intersection types,
//! and dynamic calls through LSB parameter lists. Programs the reference
//! interpreter models are run on both (`check`); the rest assert the VM's
//! result against the value PHP gives.

mod common;

use std::sync::{Arc, Mutex};

use bcgen_lang::{BodyMode, Compiler, Options};
use bvm_lang::{Program, Vm, VmError};
use bytecode_lang::Hook;
use common::hb::H;
use common::{Outcome, Profile, RV, check, to_rv};
use hir_lang::{
    Arg, ArgKind, CaptureMode, DefaultEval, Effects, ExprId, Hir, Lit, NodeRef, Op, OpKind,
    Overflow, ParamKind, Pat, Prim, Shift, StmtId, Ty,
};
use intern_lang::Interner;

/// How a VM run ended, with what it printed.
#[derive(Debug, PartialEq)]
enum Ex {
    Val(RV),
    Raised {
        code: u32,
        node: NodeRef,
        payload: RV,
    },
    Thrown(RV),
}

fn opts() -> Options {
    Options::new().with_body(BodyMode::Entry)
}

/// Compiles under `opts` and runs the entry on bvm-lang (as the first task of
/// the built-in scheduler when `asynchronous`).
fn exec(hir: &Hir, names: &Interner, opts: Options, asynchronous: bool) -> (Ex, Vec<String>) {
    let out = Compiler::new(opts)
        .compile(hir, names)
        .unwrap_or_else(|e| panic!("compile error: {e}"));
    let printed = Arc::new(Mutex::new(Vec::new()));
    let mut host = common::host(printed.clone());
    let _ = host.register_scheduler("ls.async", "spawn");
    let program = Program::load(out.module().clone(), &host).unwrap_or_else(|e| {
        panic!(
            "load error: {e}\n{}",
            bytecode_lang::disassemble(out.module())
        )
    });
    let mut vm = Vm::new(&program);
    let r = if asynchronous {
        vm.run_async(out.entry(), &[])
    } else {
        vm.run(out.entry(), &[])
    };
    let ex = match r {
        Ok(v) => Ex::Val(to_rv(&vm, v, 0)),
        Err(VmError::Raised {
            kind,
            payload,
            func,
            pc,
        }) => Ex::Raised {
            code: kind.code(),
            node: out.origin(func, pc).unwrap_or_else(|| panic!("no origin")),
            payload: to_rv(&vm, payload, 0),
        },
        Err(VmError::Thrown { value, .. }) => Ex::Thrown(to_rv(&vm, value, 0)),
        Err(e) => panic!("unexpected VM error: {e:?}"),
    };
    let printed = printed.lock().map(|v| v.clone()).unwrap_or_default();
    (ex, printed)
}

fn run(h: H, items: &[hir_lang::ItemId], body: ExprId) -> Ex {
    let (hir, names) = h.finish(items, Some(body));
    exec(&hir, &names, opts(), false).0
}

fn s(x: &str) -> RV {
    RV::Str(x.as_bytes().to_vec())
}

fn arr(xs: Vec<RV>) -> RV {
    RV::Map(
        xs.into_iter()
            .enumerate()
            .map(|(i, x)| (RV::Int(i as i64), x))
            .collect(),
    )
}

fn pair(k: RV, v: RV) -> RV {
    arr(vec![k, v])
}

/// `foreach (coll as k => v) body` through the `iter`/`iter_next`
/// intrinsics, lowered as HIR §9.4 does.
fn foreach(
    h: &mut H,
    coll: ExprId,
    body: impl FnOnce(&mut H, hir_lang::BinderId, hir_lang::BinderId) -> Vec<StmtId>,
) -> StmtId {
    let it = h.local("it");
    let iter = h.intrinsic("iter", &[coll]);
    let lit = h.let_(it, Some(iter));
    let vit = h.var(it);
    let next = h.intrinsic("iter_next", &[vit]);
    let null = h.pat(Pat::Lit(Lit::Null));
    let brk = h.brk(None, None);
    let a1 = h.arm(null, None, brk);
    let kb = h.local("k");
    let vb = h.local("v");
    let pk = h.pbind(kb);
    let pv = h.pbind(vb);
    let elems = h.b.list(&[pk, pv]);
    let tup = h.pat(Pat::Tuple { elems, rest: None });
    let stmts = body(h, kb, vb);
    let blk = h.block(&stmts, None);
    let a2 = h.arm(tup, None, blk);
    let m = h.match_(next, &[a1, a2]);
    let lp = h.loop_(None, m, None);
    let outer = h.block(&[lit], Some(lp));
    h.stmt(outer)
}

/// `out[] = [k, v]` for every entry of `coll`; evaluates to `out`.
fn collect_pairs(h: &mut H, coll: ExprId) -> (Vec<StmtId>, ExprId) {
    let out = h.local("out");
    let empty = h.array(&[]);
    let lo = h.let_(out, Some(empty));
    let each = foreach(h, coll, |h, k, v| {
        let vo = h.var(out);
        let target = h.append(vo);
        let (vk, vv) = (h.var(k), h.var(v));
        let p = h.array(&[vk, vv]);
        let a = h.assign(target, p);
        vec![h.stmt(a)]
    });
    let vo = h.var(out);
    (vec![lo, each], vo)
}

// ---------------------------------------------------------------- generators

#[test]
fn a_generator_yields_with_automatic_and_explicit_keys_and_returns() {
    // fn gen() { yield 'a' => 1; yield 2; yield 10 => 3; yield 4; return 99; }
    let mut h = H::new();
    let mut st = Vec::new();
    for (k, v) in [(Some("a"), 1), (None, 2), (Some("10"), 3), (None, 4)] {
        let key = k.map(|k| match k.parse::<i64>() {
            Ok(i) => h.int(i),
            Err(_) => h.str(k),
        });
        let val = h.int(v);
        let y = h.yield_(key, Some(val));
        st.push(h.stmt(y));
    }
    let ninety = h.int(99);
    let ret = h.ret(Some(ninety));
    let body = h.block(&st, Some(ret));
    let generator = h.gen_func("gen", &[], body);
    // let g = gen(); collect; [pairs, coro_result(g), coro_status(g)]
    let g = h.local("g");
    let cg = h.item_ref("gen", generator);
    let call = h.call(cg, &[]);
    let lg = h.let_(g, Some(call));
    let vg = h.var(g);
    let (mut stmts, pairs) = collect_pairs(&mut h, vg);
    stmts.insert(0, lg);
    let vg = h.var(g);
    let res = h.intrinsic("coro_result", &[vg]);
    let vg = h.var(g);
    let status = h.intrinsic("coro_status", &[vg]);
    let all = h.array(&[pairs, res, status]);
    let body = h.block(&stmts, Some(all));
    assert_eq!(
        run(h, &[generator], body),
        Ex::Val(arr(vec![
            arr(vec![
                pair(s("a"), RV::Int(1)),
                pair(RV::Int(0), RV::Int(2)),
                pair(RV::Int(10), RV::Int(3)),
                pair(RV::Int(11), RV::Int(4)),
            ]),
            RV::Int(99),
            RV::Int(4),
        ]))
    );
}

#[test]
fn sent_values_arrive_at_the_yield() {
    // fn gen() { let x = yield 1; let y = yield x + 10; return y; }
    let mut h = H::new();
    let x = h.local("x");
    let one = h.int(1);
    let y1 = h.yield_(None, Some(one));
    let lx = h.let_(x, Some(y1));
    let y = h.local("y");
    let vx = h.var(x);
    let ten = h.int(10);
    let sum = h.op(OpKind::Add, &[vx, ten]);
    let y2 = h.yield_(None, Some(sum));
    let ly = h.let_(y, Some(y2));
    let vy = h.var(y);
    let ret = h.ret(Some(vy));
    let body = h.block(&[lx, ly], Some(ret));
    let generator = h.gen_func("gen", &[], body);
    let g = h.local("g");
    let cg = h.item_ref("gen", generator);
    let call = h.call(cg, &[]);
    let lg = h.let_(g, Some(call));
    let mut outs = Vec::new();
    for sent in [None, Some(5), Some(7)] {
        let vg = h.var(g);
        let v = match sent {
            Some(i) => h.int(i),
            None => h.nil(),
        };
        outs.push(h.intrinsic("resume", &[vg, v]));
    }
    let vg = h.var(g);
    outs.push(h.intrinsic("coro_status", &[vg]));
    let vg = h.var(g);
    outs.push(h.intrinsic("coro_result", &[vg]));
    let all = h.array(&outs);
    let body = h.block(&[lg], Some(all));
    assert_eq!(
        run(h, &[generator], body),
        Ex::Val(arr(vec![
            RV::Int(1),
            RV::Int(15),
            RV::Int(7),
            RV::Int(4),
            RV::Int(7)
        ]))
    );
}

#[test]
fn yield_from_delegates_keys_values_and_the_return_value() {
    // fn inner() { yield 1; yield 2; return "r"; }
    // fn outer() { let r = yield from inner(); yield r; yield from ["x" => 5, 6]; }
    let mut h = H::new();
    let one = h.int(1);
    let y1 = h.yield_(None, Some(one));
    let two = h.int(2);
    let y2 = h.yield_(None, Some(two));
    let (s1, s2) = (h.stmt(y1), h.stmt(y2));
    let r = h.str("r");
    let ret = h.ret(Some(r));
    let ib = h.block(&[s1, s2], Some(ret));
    let inner = h.gen_func("inner", &[], ib);
    let rb = h.local("r");
    let ci = h.item_ref("inner", inner);
    let call = h.call(ci, &[]);
    let yf = h.yield_from(call);
    let lr = h.let_(rb, Some(yf));
    let vr = h.var(rb);
    let y3 = h.yield_(None, Some(vr));
    let s3 = h.stmt(y3);
    let xk = h.str("x");
    let five = h.int(5);
    let six = h.int(6);
    let m = h.map(&[(Some(xk), five), (None, six)]);
    let yf2 = h.yield_from(m);
    let s4 = h.stmt(yf2);
    let ob = h.block(&[lr, s3, s4], None);
    let outer = h.gen_func("outer", &[], ob);
    let co = h.item_ref("outer", outer);
    let call = h.call(co, &[]);
    let (stmts, pairs) = collect_pairs(&mut h, call);
    let body = h.block(&stmts, Some(pairs));
    // The key of `yield r` continues after the largest delegated integer key
    // (LSB's `yield_kv` moves the automatic key; PHP 8 would give 0 here).
    assert_eq!(
        run(h, &[inner, outer], body),
        Ex::Val(arr(vec![
            pair(RV::Int(0), RV::Int(1)),
            pair(RV::Int(1), RV::Int(2)),
            pair(RV::Int(2), s("r")),
            pair(s("x"), RV::Int(5)),
            pair(RV::Int(0), RV::Int(6)),
        ]))
    );
}

#[test]
fn errors_thrown_into_a_delegating_generator_reach_the_inner_one() {
    // fn inner() { try { yield 1; } catch (e) { yield concat("caught ", e); }; yield 3; }
    // fn outer() { yield from inner(); }
    let mut h = H::new();
    let one = h.int(1);
    let y1 = h.yield_(None, Some(one));
    let e = h.local("e");
    let pe = h.pbind(e);
    let caught = h.str("caught ");
    let ve = h.var(e);
    let msg = h.intrinsic("concat", &[caught, ve]);
    let y2 = h.yield_(None, Some(msg));
    let arm = h.arm(pe, None, y2);
    let tr = h.try_(y1, &[arm], None);
    let s1 = h.stmt(tr);
    let three = h.int(3);
    let y3 = h.yield_(None, Some(three));
    let s3 = h.stmt(y3);
    let ib = h.block(&[s1, s3], None);
    let inner = h.gen_func("inner", &[], ib);
    let ci = h.item_ref("inner", inner);
    let call = h.call(ci, &[]);
    let yf = h.yield_from(call);
    let ob = h.block(&[], Some(yf));
    let outer = h.gen_func("outer", &[], ob);
    // let g = outer(); [resume(g, null), resume_throw(g, "boom"), resume(g, null)]
    let g = h.local("g");
    let co = h.item_ref("outer", outer);
    let call = h.call(co, &[]);
    let lg = h.let_(g, Some(call));
    let vg = h.var(g);
    let nil = h.nil();
    let a = h.intrinsic("resume", &[vg, nil]);
    let vg = h.var(g);
    let boom = h.str("boom");
    let b = h.intrinsic("resume_throw", &[vg, boom]);
    let vg = h.var(g);
    let nil = h.nil();
    let c = h.intrinsic("resume", &[vg, nil]);
    let all = h.array(&[a, b, c]);
    let body = h.block(&[lg], Some(all));
    assert_eq!(
        run(h, &[inner, outer], body),
        Ex::Val(arr(vec![RV::Int(1), s("caught boom"), RV::Int(3)]))
    );
}

#[test]
fn generator_closures_capture_and_bind_parameters() {
    // let n = 10; let m = 1;
    // let g = function (x, y = 100) use (n, &m) { yield n; yield m; yield x + y; };
    // m = 2; [values of g(5), values of g(5, y: 1)]
    let mut h = H::new();
    let n = h.local("n");
    let ten = h.int(10);
    let ln = h.let_(n, Some(ten));
    let m = h.local("m");
    let one = h.int(1);
    let lm = h.let_(m, Some(one));
    let (cn, bn) = h.capture(n, "n", CaptureMode::ByValue);
    let (cm, bm) = h.capture(m, "m", CaptureMode::ByRef);
    let (px, x) = h.param("x", ParamKind::Normal, None, false);
    let hundred = h.int(100);
    let (py, y) = h.param("y", ParamKind::Normal, Some(hundred), false);
    let vn = h.var(bn);
    let y1 = h.yield_(None, Some(vn));
    let vm = h.var(bm);
    let y2 = h.yield_(None, Some(vm));
    let (vx, vy) = (h.var(x), h.var(y));
    let sum = h.op(OpKind::Add, &[vx, vy]);
    let y3 = h.yield_(None, Some(sum));
    let (s1, s2, s3) = (h.stmt(y1), h.stmt(y2), h.stmt(y3));
    let gb = h.block(&[s1, s2, s3], None);
    let clo = h.closure_with(
        &[px, py],
        gb,
        None,
        &[cn, cm],
        Effects::THROWS.union(Effects::YIELD),
    );
    let g = h.local("g");
    let lg = h.let_(g, Some(clo));
    let vm = h.var(m);
    let two = h.int(2);
    let am = h.assign(vm, two);
    let sm = h.stmt(am);
    let stmts = vec![ln, lm, lg, sm];
    let mut results = Vec::new();
    for named in [false, true] {
        let vg = h.var(g);
        let five = h.int(5);
        let call = if named {
            let one = h.int(1);
            let ny = h.named("y", one);
            h.call_args(vg, &[Arg::positional(five), ny])
        } else {
            h.call(vg, &[five])
        };
        let (st, pairs) = collect_pairs(&mut h, call);
        let bl = h.block(&st, Some(pairs));
        results.push(bl);
    }
    let all = h.array(&results);
    let body = h.block(&stmts, Some(all));
    let vals = |a: i64, b: i64, c: i64| {
        arr(vec![
            pair(RV::Int(0), RV::Int(a)),
            pair(RV::Int(1), RV::Int(b)),
            pair(RV::Int(2), RV::Int(c)),
        ])
    };
    assert_eq!(
        run(h, &[], body),
        Ex::Val(arr(vec![vals(10, 2, 105), vals(10, 2, 6)]))
    );
}

#[test]
fn a_generator_function_called_dynamically_binds_named_arguments() {
    // fn gen(a, b) { yield a - b; }   let f = gen; values of f(b: 2, a: 10)
    let mut h = H::new();
    let (pa, a) = h.param("a", ParamKind::Normal, None, false);
    let (pb, b) = h.param("b", ParamKind::Normal, None, false);
    let (va, vb) = (h.var(a), h.var(b));
    let d = h.op(OpKind::Sub, &[va, vb]);
    let y = h.yield_(None, Some(d));
    let gb = h.block(&[], Some(y));
    let generator = h.gen_func("gen", &[pa, pb], gb);
    let f = h.local("f");
    let gv = h.item_ref("gen", generator);
    let lf = h.let_(f, Some(gv));
    let vf = h.var(f);
    let two = h.int(2);
    let ten = h.int(10);
    let nb = h.named("b", two);
    let na = h.named("a", ten);
    let call = h.call_args(vf, &[nb, na]);
    let (mut st, pairs) = collect_pairs(&mut h, call);
    st.insert(0, lf);
    let body = h.block(&st, Some(pairs));
    assert_eq!(
        run(h, &[generator], body),
        Ex::Val(arr(vec![pair(RV::Int(0), RV::Int(8))]))
    );
}

#[test]
fn spawn_and_await_run_on_the_scheduler() {
    // fn work(x) { x * 2 }
    // async fn main() { let t = spawn(fn() => work(21)); [await t, await 5] }
    // body: main()
    let mut h = H::new();
    let (px, x) = h.param("x", ParamKind::Normal, None, false);
    let vx = h.var(x);
    let two = h.int(2);
    let mul = h.op(OpKind::Mul, &[vx, two]);
    let wb = h.block(&[], Some(mul));
    let work = h.func("work", &[px], wb, DefaultEval::PerCall);
    let cw = h.item_ref("work", work);
    let tw = h.int(21);
    let call = h.call(cw, &[tw]);
    let clo = h.closure(&[], call, None, &[], None, DefaultEval::PerCall);
    let sp = h.expr(hir_lang::Expr::Spawn(clo));
    let t = h.local("t");
    let lt = h.let_(t, Some(sp));
    let vt = h.var(t);
    let a1 = h.expr(hir_lang::Expr::Await(vt));
    let five = h.int(5);
    let a2 = h.expr(hir_lang::Expr::Await(five));
    let both = h.array(&[a1, a2]);
    let mb = h.block(&[lt], Some(both));
    let main = h.func_with("main", &[], mb, Effects::THROWS.union(Effects::ASYNC));
    let cm = h.item_ref("main", main);
    let body = h.call(cm, &[]);
    let (hir, names) = h.finish(&[work, main], Some(body));
    let o = opts().with_hook(Hook::Spawn, "ls.async", "spawn");
    assert_eq!(
        exec(&hir, &names, o, true).0,
        Ex::Val(arr(vec![RV::Int(42), RV::Int(5)]))
    );
    // Without a scheduler bound, `spawn` raises NoScheduler (E0112).
    let (ex, _) = exec(&hir, &names, opts(), true);
    assert!(matches!(ex, Ex::Raised { code: 112, .. }), "{ex:?}");
}

// ---------------------------------------------------------------- let_place

#[test]
fn let_place_evaluates_the_place_once() {
    // let n = 0; let f = function () use (&n) { n += 1; "k" };
    // let a = ["k" => "x"];
    // let_place p = a[f()] in p = concat(p, "!");   [a, n]
    let mut h = H::new();
    let n = h.local("n");
    let z = h.int(0);
    let ln = h.let_(n, Some(z));
    let (cn, bn) = h.capture(n, "n", CaptureMode::ByRef);
    let vn = h.var(bn);
    let one = h.int(1);
    let inc = h.compound(vn, Op::new(OpKind::Add), one);
    let si = h.stmt(inc);
    let k = h.str("k");
    let fb = h.block(&[si], Some(k));
    let clo = h.closure(&[], fb, None, &[cn], None, DefaultEval::PerCall);
    let f = h.local("f");
    let lf = h.let_(f, Some(clo));
    let a = h.local("a");
    let k = h.str("k");
    let x = h.str("x");
    let m = h.map(&[(Some(k), x)]);
    let la = h.let_(a, Some(m));
    let p = h.place_binder("p");
    let va = h.var(a);
    let vf = h.var(f);
    let key = h.call(vf, &[]);
    let place = h.index(va, key);
    let vp1 = h.var(p);
    let bang = h.str("!");
    let cat = h.intrinsic("concat", &[vp1, bang]);
    let vp2 = h.var(p);
    let asg = h.assign(vp2, cat);
    let lp = h.let_place(p, place, asg);
    let s = h.stmt(lp);
    let (va, vn) = (h.var(a), h.var(n));
    let out = h.array(&[va, vn]);
    let body = h.block(&[ln, lf, la, s], Some(out));
    let (hir, names) = h.finish(&[], Some(body));
    let o = check(&hir, &names, Profile::PHP);
    assert_eq!(
        o,
        Outcome::Value(arr(vec![
            RV::Map(vec![(RV::Str(b"k".to_vec()), RV::Str(b"x!".to_vec()))]),
            RV::Int(1),
        ]))
    );
}

#[test]
fn let_place_post_increment_and_alias_bases() {
    // let a = [5]; let i = 0;
    // let old = let_place p = a[i] in { let o = p; p = p + 1; o };
    // let b = [];  let_place q = b["x"] in q["y"] = 1;
    // [old, a, b]
    let mut h = H::new();
    let a = h.local("a");
    let five = h.int(5);
    let arr5 = h.array(&[five]);
    let la = h.let_(a, Some(arr5));
    let i = h.local("i");
    let z = h.int(0);
    let li = h.let_(i, Some(z));
    let p = h.place_binder("p");
    let va = h.var(a);
    let vi = h.var(i);
    let place = h.index(va, vi);
    let o = h.local("o");
    let vp = h.var(p);
    let lo = h.let_(o, Some(vp));
    let vp = h.var(p);
    let one = h.int(1);
    let inc = h.op(OpKind::Add, &[vp, one]);
    let vp = h.var(p);
    let asg = h.assign(vp, inc);
    let sa = h.stmt(asg);
    let vo = h.var(o);
    let pb = h.block(&[lo, sa], Some(vo));
    let lp = h.let_place(p, place, pb);
    let old = h.local("old");
    let lold = h.let_(old, Some(lp));
    let b = h.local("b");
    let empty = h.array(&[]);
    let lb = h.let_(b, Some(empty));
    let q = h.place_binder("q");
    let vb = h.var(b);
    let xk = h.str("x");
    let qplace = h.index(vb, xk);
    let vq = h.var(q);
    let yk = h.str("y");
    let deep = h.index(vq, yk);
    let one = h.int(1);
    let set = h.assign(deep, one);
    let lq = h.let_place(q, qplace, set);
    let sq = h.stmt(lq);
    let (vold, va, vb) = (h.var(old), h.var(a), h.var(b));
    let out = h.array(&[vold, va, vb]);
    let body = h.block(&[la, li, lold, lb, sq], Some(out));
    let (hir, names) = h.finish(&[], Some(body));
    // PHP arrays: writing through the alias creates b["x"].
    assert_eq!(
        check(&hir, &names, Profile::PHP),
        Outcome::Value(arr(vec![
            RV::Int(5),
            arr(vec![RV::Int(6)]),
            RV::Map(vec![(s("x"), RV::Map(vec![(s("y"), RV::Int(1))]))]),
        ]))
    );
    // Shared references: no auto-vivification, so b["x"] is missing.
    assert!(matches!(
        check(&hir, &names, Profile::REFERENCE),
        Outcome::Raised { code: 103, .. }
    ));
}

#[test]
fn assignments_evaluate_to_the_assigned_value() {
    // let a = 0; let b = 0; let c = 0;  a = b = 3; c = (a += 2); [a, b, c]
    let mut h = H::new();
    let (a, b, c) = (h.local("a"), h.local("b"), h.local("c"));
    let mut st = Vec::new();
    for v in [a, b, c] {
        let z = h.int(0);
        st.push(h.let_(v, Some(z)));
    }
    let (va, vb) = (h.var(a), h.var(b));
    let three = h.int(3);
    let inner = h.assign(vb, three);
    let outer = h.assign(va, inner);
    st.push(h.stmt(outer));
    let (vc, va) = (h.var(c), h.var(a));
    let two = h.int(2);
    let comp = h.compound(va, Op::new(OpKind::Add), two);
    let set = h.assign(vc, comp);
    st.push(h.stmt(set));
    let (va, vb, vc) = (h.var(a), h.var(b), h.var(c));
    let out = h.array(&[va, vb, vc]);
    let body = h.block(&st, Some(out));
    let (hir, names) = h.finish(&[], Some(body));
    assert_eq!(
        check(&hir, &names, Profile::PHP),
        Outcome::Value(arr(vec![RV::Int(5), RV::Int(3), RV::Int(5)]))
    );
}

// ---------------------------------------------------------------- references

/// `fn inc(&x) { x = x + 1 }` and `fn set1(&x) { x = 1 }`.
fn ref_fns(h: &mut H) -> (hir_lang::ItemId, hir_lang::ItemId) {
    let (px, x) = h.param("x", ParamKind::Normal, None, true);
    let (vx, vx2) = (h.var(x), h.var(x));
    let one = h.int(1);
    let sum = h.op(OpKind::Add, &[vx2, one]);
    let asg = h.assign(vx, sum);
    let b = h.block(&[], Some(asg));
    let inc = h.func("inc", &[px], b, DefaultEval::PerCall);
    let (py, y) = h.param("x", ParamKind::Normal, None, true);
    let vy = h.var(y);
    let one = h.int(1);
    let asg = h.assign(vy, one);
    let b = h.block(&[], Some(asg));
    let set1 = h.func("set1", &[py], b, DefaultEval::PerCall);
    (inc, set1)
}

#[test]
fn by_reference_parameters_take_references_to_elements() {
    // let a = ["k" => 5]; inc(&a["k"]); inc(&a["k"]);
    // let b = []; set1(&b["new"]["deep"]);  [a, b]
    let mut h = H::new();
    let (inc, set1) = ref_fns(&mut h);
    let a = h.local("a");
    let k = h.str("k");
    let five = h.int(5);
    let m = h.map(&[(Some(k), five)]);
    let la = h.let_(a, Some(m));
    let mut st = vec![la];
    for _ in 0..2 {
        let va = h.var(a);
        let k = h.str("k");
        let el = h.index(va, k);
        let ci = h.item_ref("inc", inc);
        let arg = h.place_arg(el);
        let c = h.call_args(ci, &[arg]);
        st.push(h.stmt(c));
    }
    let b = h.local("b");
    let empty = h.array(&[]);
    st.push(h.let_(b, Some(empty)));
    let vb = h.var(b);
    let nk = h.str("new");
    let e1 = h.index(vb, nk);
    let dk = h.str("deep");
    let e2 = h.index(e1, dk);
    let cs = h.item_ref("set1", set1);
    let arg = h.place_arg(e2);
    let c = h.call_args(cs, &[arg]);
    st.push(h.stmt(c));
    let (va, vb) = (h.var(a), h.var(b));
    let out = h.array(&[va, vb]);
    let body = h.block(&st, Some(out));
    assert_eq!(
        run(h, &[inc, set1], body),
        Ex::Val(arr(vec![
            RV::Map(vec![(s("k"), RV::Int(7))]),
            RV::Map(vec![(s("new"), RV::Map(vec![(s("deep"), RV::Int(1))]))]),
        ]))
    );
}

#[test]
fn dynamic_calls_decide_by_reference_at_run_time() {
    // let a = ["k" => 5]; let f = inc; let g = function (x) { x = 100 };
    // f(&a["k"]); g(&a["k"]); f(x: &a["k"]);  a
    let mut h = H::new();
    let (inc, set1) = ref_fns(&mut h);
    let a = h.local("a");
    let k = h.str("k");
    let five = h.int(5);
    let m = h.map(&[(Some(k), five)]);
    let la = h.let_(a, Some(m));
    let f = h.local("f");
    let iv = h.item_ref("inc", inc);
    let lf = h.let_(f, Some(iv));
    let (px, x) = h.param("x", ParamKind::Normal, None, false);
    let vx = h.var(x);
    let hundred = h.int(100);
    let asg = h.assign(vx, hundred);
    let clo = h.closure(&[px], asg, None, &[], None, DefaultEval::PerCall);
    let g = h.local("g");
    let lg = h.let_(g, Some(clo));
    let mut st = vec![la, lf, lg];
    for (callee, named) in [(f, false), (g, false), (f, true)] {
        let va = h.var(a);
        let k = h.str("k");
        let el = h.index(va, k);
        let vc = h.var(callee);
        let arg = if named {
            Arg {
                kind: ArgKind::Named(h.ident("x")),
                value: el,
                place: true,
            }
        } else {
            h.place_arg(el)
        };
        let c = h.call_args(vc, &[arg]);
        st.push(h.stmt(c));
    }
    let va = h.var(a);
    let body = h.block(&st, Some(va));
    assert_eq!(
        run(h, &[inc, set1], body),
        Ex::Val(RV::Map(vec![(s("k"), RV::Int(7))]))
    );
}

#[test]
fn reference_assignment_to_and_from_elements() {
    // let a = ["k" => 1]; let x = 0;
    // x = &a["k"]; x = 9;            -- a["k"] is 9
    // let b = a; b["k"] = 2;         -- the slot is shared: a["k"] is 2 (PHP)
    // let y = 3; let c = []; c["r"] = &y; y = 4;
    // let v = (c["s"] = &y);         -- the value of the aliased place
    // [a["k"], c, v]
    let mut h = H::new();
    let a = h.local("a");
    let k = h.str("k");
    let one = h.int(1);
    let m = h.map(&[(Some(k), one)]);
    let la = h.let_(a, Some(m));
    let x = h.local("x");
    let z = h.int(0);
    let lx = h.let_(x, Some(z));
    let vx = h.var(x);
    let va = h.var(a);
    let k = h.str("k");
    let el = h.index(va, k);
    let ra = h.ref_assign(vx, el);
    let s1 = h.stmt(ra);
    let vx = h.var(x);
    let nine = h.int(9);
    let s2 = {
        let a9 = h.assign(vx, nine);
        h.stmt(a9)
    };
    let b = h.local("b");
    let va = h.var(a);
    let lb = h.let_(b, Some(va));
    let vb = h.var(b);
    let k = h.str("k");
    let bel = h.index(vb, k);
    let two = h.int(2);
    let s3 = {
        let a2 = h.assign(bel, two);
        h.stmt(a2)
    };
    let y = h.local("y");
    let three = h.int(3);
    let ly = h.let_(y, Some(three));
    let c = h.local("c");
    let empty = h.array(&[]);
    let lc = h.let_(c, Some(empty));
    let vc = h.var(c);
    let rk = h.str("r");
    let cel = h.index(vc, rk);
    let vy = h.var(y);
    let rb = h.ref_assign(cel, vy);
    let s4 = h.stmt(rb);
    let vy = h.var(y);
    let four = h.int(4);
    let s5 = {
        let a4 = h.assign(vy, four);
        h.stmt(a4)
    };
    let v = h.local("v");
    let vc = h.var(c);
    let sk = h.str("s");
    let cel = h.index(vc, sk);
    let vy = h.var(y);
    let rv = h.ref_assign(cel, vy);
    let lv = h.let_(v, Some(rv));
    let va = h.var(a);
    let k = h.str("k");
    let ak = h.index(va, k);
    let (vc, vv) = (h.var(c), h.var(v));
    let out = h.array(&[ak, vc, vv]);
    let body = h.block(&[la, lx, s1, s2, lb, s3, ly, lc, s4, s5, lv], Some(out));
    assert_eq!(
        run(h, &[], body),
        Ex::Val(arr(vec![
            RV::Int(2),
            RV::Map(vec![(s("r"), RV::Int(4)), (s("s"), RV::Int(4))]),
            RV::Int(4),
        ]))
    );
}

// ---------------------------------------------------------------- operations

fn op2(h: &mut H, op: Op, a: ExprId, b: ExprId) -> ExprId {
    h.op_with(op, &[a, b])
}

#[test]
fn pow_follows_ops_v2() {
    let mut h = H::new();
    let mut es = Vec::new();
    for (b, e, over) in [
        (2, 10, Overflow::Error),
        (-2, 3, Overflow::Error),
        (2, 63, Overflow::Wrap),
        (3, 0, Overflow::Error),
    ] {
        let (x, y) = (h.int(b), h.int(e));
        es.push(op2(&mut h, Op::new(OpKind::Pow).with_overflow(over), x, y));
    }
    let out = h.array(&es);
    let (hir, names) = h.finish(&[], Some(out));
    assert_eq!(
        check(&hir, &names, Profile::PHP),
        Outcome::Value(arr(vec![
            RV::Int(1024),
            RV::Int(-8),
            RV::Int(i64::MIN),
            RV::Int(1)
        ]))
    );
    // `promote`: the nearest float of the exact power; a negative exponent
    // takes the float rule (PHP `2 ** -1` is 0.5).
    let mut h = H::new();
    let mut es = Vec::new();
    for (b, e) in [(2, 64), (2, -1), (10, -2)] {
        let (x, y) = (h.int(b), h.int(e));
        es.push(op2(
            &mut h,
            Op::new(OpKind::Pow).with_overflow(Overflow::Promote),
            x,
            y,
        ));
    }
    let (x, y) = (h.float(2.0), h.float(0.5));
    es.push(op2(
        &mut h,
        Op::new(OpKind::Pow).with_overflow(Overflow::Error),
        x,
        y,
    ));
    let out = h.array(&es);
    assert_eq!(
        run(h, &[], out),
        Ex::Val(arr(vec![
            RV::float(18446744073709551616.0),
            RV::float(0.5),
            RV::float(0.01),
            RV::float(std::f64::consts::SQRT_2),
        ]))
    );
    // Any other policy: NegativeExponent (E0006).
    let mut h = H::new();
    let (x, y) = (h.int(2), h.int(-1));
    let p = op2(
        &mut h,
        Op::new(OpKind::Pow).with_overflow(Overflow::Error),
        x,
        y,
    );
    let (hir, names) = h.finish(&[], Some(p));
    assert_eq!(
        check(&hir, &names, Profile::PHP),
        Outcome::Raised {
            code: 6,
            node: NodeRef::Expr(p)
        }
    );
}

#[test]
fn logical_not_bitwise_not_and_saturating_shifts() {
    let mut h = H::new();
    let mut es = Vec::new();
    // Logical `not` on any value: its truthiness negated.
    for v in [0i64, 7] {
        let x = h.int(v);
        es.push(h.op(OpKind::Not, &[x]));
    }
    let e = h.str("");
    es.push(h.op(OpKind::Not, &[e]));
    let empty = h.array(&[]);
    es.push(h.op(OpKind::Not, &[empty]));
    // Bitwise.
    let five = h.int(5);
    es.push(h.op(OpKind::BitNot, &[five]));
    // Saturating shifts (PHP).
    let sat = |k| Op::new(k).with_shift(Shift::Saturate);
    for (k, a, n) in [
        (OpKind::Shl, 1, 64),
        (OpKind::Shr, -8, 70),
        (OpKind::Shr, 8, 64),
        (OpKind::Shl, 3, 2),
    ] {
        let (x, y) = (h.int(a), h.int(n));
        es.push(op2(&mut h, sat(k), x, y));
    }
    let out = h.array(&es);
    let (hir, names) = h.finish(&[], Some(out));
    assert_eq!(
        check(&hir, &names, Profile::PHP),
        Outcome::Value(arr(vec![
            RV::Bool(true),
            RV::Bool(false),
            RV::Bool(true),
            RV::Bool(true),
            RV::Int(-6),
            RV::Int(0),
            RV::Int(-1),
            RV::Int(0),
            RV::Int(12),
        ]))
    );
    // A negative amount is ShiftOutOfRange even when saturating; `bit_not`
    // of a string is a TypeError without a `bit_not` hook.
    for neg in [true, false] {
        let mut h = H::new();
        let e = if neg {
            let (x, y) = (h.int(1), h.int(-1));
            op2(
                &mut h,
                Op::new(OpKind::Shl).with_shift(Shift::Saturate),
                x,
                y,
            )
        } else {
            let a = h.str("a");
            h.op(OpKind::BitNot, &[a])
        };
        let (hir, names) = h.finish(&[], Some(e));
        assert_eq!(
            check(&hir, &names, Profile::PHP),
            Outcome::Raised {
                code: if neg { 3 } else { 100 },
                node: NodeRef::Expr(e)
            }
        );
    }
}

#[test]
fn abs_of_the_minimum_promotes() {
    let mut h = H::new();
    let min = h.int(i64::MIN);
    let a = h.op_with(
        Op::new(OpKind::Abs).with_overflow(Overflow::Promote),
        &[min],
    );
    let f = h.float(-2.5);
    let b = h.op_with(Op::new(OpKind::Abs).with_overflow(Overflow::Error), &[f]);
    let out = h.array(&[a, b]);
    let (hir, names) = h.finish(&[], Some(out));
    assert_eq!(
        check(&hir, &names, Profile::PHP),
        Outcome::Value(arr(vec![
            RV::float(9_223_372_036_854_775_808.0),
            RV::float(2.5)
        ]))
    );
}

#[test]
fn a_match_without_a_matching_arm_raises_no_match_with_the_scrutinee() {
    // match 42 { 1 => "one" }
    let mut h = H::new();
    let v = h.int(42);
    let p1 = h.pat(Pat::Lit(Lit::Int(hir_lang::IntLit::new(1))));
    let one = h.str("one");
    let arm = h.arm(p1, None, one);
    let m = h.match_(v, &[arm]);
    let (hir, names) = h.finish(&[], Some(m));
    assert_eq!(
        check(&hir, &names, Profile::PHP),
        Outcome::Raised {
            code: 200,
            node: NodeRef::Expr(m)
        }
    );
    assert_eq!(
        exec(&hir, &names, opts(), false).0,
        Ex::Raised {
            code: 200,
            node: NodeRef::Expr(m),
            payload: RV::Int(42)
        }
    );
}

// ---------------------------------------------------------------- types

#[test]
fn unions_and_intersections_test_and_check_kinds() {
    // m(x) = match x { y: int|string => "is", y: ?(int|string) => "null", _ => "not" }
    // k(x) = match x { y: int & (int|string) => "int", _ => "other" }
    let mut h = H::new();
    let (px, x) = h.param("x", ParamKind::Normal, None, false);
    let int = h.ty(Ty::Prim(Prim::I64));
    let st = h.ty(Ty::Prim(Prim::Str));
    let members = h.b.list(&[int, st]);
    let un = h.ty(Ty::Union(members));
    let p1 = h.pat(Pat::TypeTest { ty: un, pat: None });
    let is = h.str("is");
    let a1 = h.arm(p1, None, is);
    let int2 = h.ty(Ty::Prim(Prim::I64));
    let st2 = h.ty(Ty::Prim(Prim::Str));
    let members = h.b.list(&[int2, st2]);
    let un2 = h.ty(Ty::Union(members));
    let nun = h.ty(Ty::Nullable(un2));
    let p2 = h.pat(Pat::TypeTest { ty: nun, pat: None });
    let null = h.str("null");
    let a2 = h.arm(p2, None, null);
    let w = h.pat(Pat::Wild);
    let not = h.str("not");
    let a3 = h.arm(w, None, not);
    let vx = h.var(x);
    let m = h.match_(vx, &[a1, a2, a3]);
    let mb = h.block(&[], Some(m));
    let mf = h.func("m", &[px], mb, DefaultEval::PerCall);
    let (py, y) = h.param("x", ParamKind::Normal, None, false);
    let int3 = h.ty(Ty::Prim(Prim::I64));
    let int4 = h.ty(Ty::Prim(Prim::I64));
    let st3 = h.ty(Ty::Prim(Prim::Str));
    let members = h.b.list(&[int4, st3]);
    let un3 = h.ty(Ty::Union(members));
    let members = h.b.list(&[int3, un3]);
    let inter = h.ty(Ty::Intersection(members));
    let p3 = h.pat(Pat::TypeTest {
        ty: inter,
        pat: None,
    });
    let isint = h.str("int");
    let b1 = h.arm(p3, None, isint);
    let w = h.pat(Pat::Wild);
    let other = h.str("other");
    let b2 = h.arm(w, None, other);
    let vy = h.var(y);
    let k = h.match_(vy, &[b1, b2]);
    let kb = h.block(&[], Some(k));
    let kf = h.func("k", &[py], kb, DefaultEval::PerCall);
    let mut calls = Vec::new();
    for f in [(mf, "m"), (kf, "k")] {
        for i in 0..4 {
            let arg = match i {
                0 => h.int(1),
                1 => h.str("s"),
                2 => h.float(1.5),
                _ => h.nil(),
            };
            let c = h.item_ref(f.1, f.0);
            calls.push(h.call(c, &[arg]));
        }
    }
    let out = h.array(&calls);
    assert_eq!(
        run(h, &[mf, kf], out),
        Ex::Val(arr(vec![
            s("is"),
            s("is"),
            s("not"),
            s("null"),
            s("int"),
            s("other"),
            s("other"),
            s("other"),
        ]))
    );
}

#[test]
fn a_cast_to_a_union_checks_the_kind() {
    for (v, ok) in [(0, true), (1, false)] {
        let mut h = H::new();
        let x = if v == 0 { h.int(7) } else { h.float(1.5) };
        let int = h.ty(Ty::Prim(Prim::I64));
        let st = h.ty(Ty::Prim(Prim::Str));
        let members = h.b.list(&[int, st]);
        let un = h.ty(Ty::Union(members));
        let c = h.expr(hir_lang::Expr::Cast {
            expr: x,
            ty: un,
            policy: hir_lang::Policy::CAST,
        });
        let r = run(h, &[], c);
        if ok {
            assert_eq!(r, Ex::Val(RV::Int(7)));
        } else {
            assert!(matches!(r, Ex::Raised { code: 100, .. }), "{r:?}");
        }
    }
}

// ---------------------------------------------------------------- dynamic calls

/// `fn f(a, b = 10, c = 100) { [a, b, c] }`.
fn abc(h: &mut H) -> hir_lang::ItemId {
    let (pa, a) = h.param("a", ParamKind::Normal, None, false);
    let ten = h.int(10);
    let (pb, b) = h.param("b", ParamKind::Normal, Some(ten), false);
    let hundred = h.int(100);
    let (pc, c) = h.param("c", ParamKind::Normal, Some(hundred), false);
    let (va, vb, vc) = (h.var(a), h.var(b), h.var(c));
    let out = h.array(&[va, vb, vc]);
    let body = h.block(&[], Some(out));
    h.func("f", &[pa, pb, pc], body, DefaultEval::PerCall)
}

#[test]
fn function_values_bind_named_arguments_spreads_and_defaults() {
    // let g = f; [g(1), g(1, c: 3), g(c: 3, a: 2), g(...[4, 5]), g(...["a" => 6, "c" => 7]), f(...[8])]
    let mut h = H::new();
    let f = abc(&mut h);
    let g = h.local("g");
    let fv = h.item_ref("f", f);
    let lg = h.let_(g, Some(fv));
    let mut calls = Vec::new();
    let one = h.int(1);
    let vg = h.var(g);
    calls.push(h.call(vg, &[one]));
    let (one, three) = (h.int(1), h.int(3));
    let nc = h.named("c", three);
    let vg = h.var(g);
    calls.push(h.call_args(vg, &[Arg::positional(one), nc]));
    let (three, two) = (h.int(3), h.int(2));
    let (nc, na) = (h.named("c", three), h.named("a", two));
    let vg = h.var(g);
    calls.push(h.call_args(vg, &[nc, na]));
    let (four, five) = (h.int(4), h.int(5));
    let list = h.array(&[four, five]);
    let vg = h.var(g);
    calls.push(h.call_args(
        vg,
        &[Arg {
            kind: ArgKind::Spread,
            value: list,
            place: false,
        }],
    ));
    let (ka, six, kc, seven) = (h.str("a"), h.int(6), h.str("c"), h.int(7));
    let named = h.map(&[(Some(ka), six), (Some(kc), seven)]);
    let vg = h.var(g);
    calls.push(h.call_args(
        vg,
        &[Arg {
            kind: ArgKind::SpreadNamed,
            value: named,
            place: false,
        }],
    ));
    let eight = h.int(8);
    let list = h.array(&[eight]);
    let fd = h.item_ref("f", f);
    calls.push(h.call_args(
        fd,
        &[Arg {
            kind: ArgKind::Spread,
            value: list,
            place: false,
        }],
    ));
    let out = h.array(&calls);
    let body = h.block(&[lg], Some(out));
    let (hir, names) = h.finish(&[f], Some(body));
    let row = |a, b, c| arr(vec![RV::Int(a), RV::Int(b), RV::Int(c)]);
    assert_eq!(
        check(&hir, &names, Profile::PHP),
        Outcome::Value(arr(vec![
            row(1, 10, 100),
            row(1, 10, 3),
            row(2, 10, 3),
            row(4, 5, 100),
            row(6, 10, 7),
            row(8, 10, 100),
        ]))
    );
}

#[test]
fn arguments_that_do_not_bind_raise_argument_error_at_the_call() {
    // g() (missing a); g(1, d: 2) (unknown name); g(a: 1, 2) (positional
    // after named); f(1, 2, 3, 4) (too many, a direct call)
    for case in 0..4 {
        let mut h = H::new();
        let f = abc(&mut h);
        let g = h.local("g");
        let fv = h.item_ref("f", f);
        let lg = h.let_(g, Some(fv));
        let call = match case {
            0 => {
                let vg = h.var(g);
                h.call(vg, &[])
            }
            1 => {
                let vg = h.var(g);
                let (one, two) = (h.int(1), h.int(2));
                let nd = h.named("d", two);
                h.call_args(vg, &[Arg::positional(one), nd])
            }
            2 => {
                let vg = h.var(g);
                let (one, two) = (h.int(1), h.int(2));
                let na = h.named("a", one);
                h.call_args(vg, &[na, Arg::positional(two)])
            }
            _ => {
                let fd = h.item_ref("f", f);
                let args: Vec<ExprId> = (1..=4).map(|i| h.int(i)).collect();
                h.call(fd, &args)
            }
        };
        let body = h.block(&[lg], Some(call));
        let (hir, names) = h.finish(&[f], Some(body));
        let expect = Outcome::Raised {
            code: 114,
            node: NodeRef::Expr(call),
        };
        // The reference rejects case 2 the same way.
        assert_eq!(check(&hir, &names, Profile::PHP), expect, "case {case}");
    }
}

#[test]
fn a_rest_parameter_collects_extra_positional_and_unknown_named_arguments() {
    // fn r(x, ...rest) { rest }   [r(1, 2, z: 3), (r as a value)(1, 2, z: 3)]
    let mut h = H::new();
    let (px, _) = h.param("x", ParamKind::Normal, None, false);
    let (pr, rest) = h.param("rest", ParamKind::Rest, None, false);
    let vr = h.var(rest);
    let body = h.block(&[], Some(vr));
    let r = h.func("r", &[px, pr], body, DefaultEval::PerCall);
    let mut calls = Vec::new();
    for dynamic in [false, true] {
        let (one, two, three) = (h.int(1), h.int(2), h.int(3));
        let nz = h.named("z", three);
        let callee = if dynamic {
            let t = h.local("t");
            let rv = h.item_ref("r", r);
            let lt = h.let_(t, Some(rv));
            let vt = h.var(t);
            let c = h.call_args(vt, &[Arg::positional(one), Arg::positional(two), nz]);
            h.block(&[lt], Some(c))
        } else {
            let rd = h.item_ref("r", r);
            h.call_args(rd, &[Arg::positional(one), Arg::positional(two), nz])
        };
        calls.push(callee);
    }
    let out = h.array(&calls);
    let (hir, names) = h.finish(&[r], Some(out));
    let rest = RV::Map(vec![(RV::Int(0), RV::Int(2)), (s("z"), RV::Int(3))]);
    assert_eq!(
        check(&hir, &names, Profile::PHP),
        Outcome::Value(arr(vec![rest.clone(), rest]))
    );
}

#[test]
fn a_caught_no_match_carries_its_code_and_payload() {
    // try { match "zz" { "a" => 1 } } catch (e) { [err_code(e), err_payload(e)] }
    let mut h = H::new();
    let v = h.str("zz");
    let ta = h.b.text("a");
    let pa = h.pat(Pat::Lit(Lit::Str(ta)));
    let one = h.int(1);
    let arm = h.arm(pa, None, one);
    let m = h.match_(v, &[arm]);
    let e = h.local("e");
    let pe = h.pbind(e);
    let ve = h.var(e);
    let code = h.intrinsic("err_code", &[ve]);
    let ve = h.var(e);
    let payload = h.intrinsic("err_payload", &[ve]);
    let pair = h.array(&[code, payload]);
    let catch = h.arm(pe, None, pair);
    let t = h.try_(m, &[catch], None);
    assert_eq!(run(h, &[], t), Ex::Val(arr(vec![RV::Int(200), s("zz")])));
}

#[test]
fn a_generator_takes_by_reference_parameters() {
    // fn gen(&x) { yield 1; x = 5; yield 2; }
    // let a = 0; foreach (gen(&a) as ...) {}; a   (directly and as a value)
    for dynamic in [false, true] {
        let mut h = H::new();
        let (px, x) = h.param("x", ParamKind::Normal, None, true);
        let one = h.int(1);
        let y1 = h.yield_(None, Some(one));
        let vx = h.var(x);
        let five = h.int(5);
        let set = h.assign(vx, five);
        let two = h.int(2);
        let y2 = h.yield_(None, Some(two));
        let (s1, s2, s3) = (h.stmt(y1), h.stmt(set), h.stmt(y2));
        let gb = h.block(&[s1, s2, s3], None);
        let generator = h.gen_func("gen", &[px], gb);
        let a = h.local("a");
        let z = h.int(0);
        let la = h.let_(a, Some(z));
        let va = h.var(a);
        let arg = h.place_arg(va);
        let call = if dynamic {
            let f = h.local("f");
            let gv = h.item_ref("gen", generator);
            let lf = h.let_(f, Some(gv));
            let vf = h.var(f);
            let c = h.call_args(vf, &[arg]);
            h.block(&[lf], Some(c))
        } else {
            let gd = h.item_ref("gen", generator);
            h.call_args(gd, &[arg])
        };
        let (st, pairs) = collect_pairs(&mut h, call);
        let collected = h.block(&st, Some(pairs));
        let sc = h.stmt(collected);
        let va = h.var(a);
        let body = h.block(&[la, sc], Some(va));
        assert_eq!(
            run(h, &[generator], body),
            Ex::Val(RV::Int(5)),
            "dynamic {dynamic}"
        );
    }
}

#[test]
fn closing_a_suspended_generator_runs_its_finally() {
    // fn gen() { try { yield 1; yield 2; } finally { echo("cleanup") } }
    // let g = gen(); resume(g, null); coro_close(g, null); coro_status(g)
    let mut h = H::new();
    let one = h.int(1);
    let y1 = h.yield_(None, Some(one));
    let two = h.int(2);
    let y2 = h.yield_(None, Some(two));
    let (s1, s2) = (h.stmt(y1), h.stmt(y2));
    let tb = h.block(&[s1, s2], None);
    let echo = h.extern_ref("echo");
    let msg = h.str("cleanup");
    let fin = h.call(echo, &[msg]);
    let tr = h.try_(tb, &[], Some(fin));
    let gb = h.block(&[], Some(tr));
    let generator = h.gen_func("gen", &[], gb);
    let g = h.local("g");
    let cg = h.item_ref("gen", generator);
    let call = h.call(cg, &[]);
    let lg = h.let_(g, Some(call));
    let vg = h.var(g);
    let nil = h.nil();
    let r = h.intrinsic("resume", &[vg, nil]);
    let sr = h.stmt(r);
    let vg = h.var(g);
    let nil = h.nil();
    let c = h.intrinsic("coro_close", &[vg, nil]);
    let sc = h.stmt(c);
    let vg = h.var(g);
    let st = h.intrinsic("coro_status", &[vg]);
    let body = h.block(&[lg, sr, sc], Some(st));
    let (hir, names) = h.finish(&[generator], Some(body));
    let (ex, printed) = exec(&hir, &names, opts(), false);
    assert_eq!(ex, Ex::Val(RV::Int(4)));
    assert_eq!(printed, vec!["cleanup".to_string()]);
}

#[test]
fn a_place_alias_can_be_referenced_and_passed_by_reference() {
    // let a = ["k" => 1]; let x = 0;
    // let_place p = a["k"] in { inc(&p); x = &p; x = x + 10 }; a
    let mut h = H::new();
    let (inc, set1) = ref_fns(&mut h);
    let a = h.local("a");
    let k = h.str("k");
    let one = h.int(1);
    let m = h.map(&[(Some(k), one)]);
    let la = h.let_(a, Some(m));
    let x = h.local("x");
    let z = h.int(0);
    let lx = h.let_(x, Some(z));
    let p = h.place_binder("p");
    let va = h.var(a);
    let k = h.str("k");
    let place = h.index(va, k);
    let ci = h.item_ref("inc", inc);
    let vp = h.var(p);
    let arg = h.place_arg(vp);
    let call = h.call_args(ci, &[arg]);
    let s1 = h.stmt(call);
    let vx = h.var(x);
    let vp = h.var(p);
    let ra = h.ref_assign(vx, vp);
    let s2 = h.stmt(ra);
    let (vx, vx2) = (h.var(x), h.var(x));
    let ten = h.int(10);
    let sum = h.op(OpKind::Add, &[vx2, ten]);
    let asg = h.assign(vx, sum);
    let s3 = h.stmt(asg);
    let pb = h.block(&[s1, s2, s3], None);
    let lp = h.let_place(p, place, pb);
    let sl = h.stmt(lp);
    let va = h.var(a);
    let body = h.block(&[la, lx, sl], Some(va));
    assert_eq!(
        run(h, &[inc, set1], body),
        Ex::Val(RV::Map(vec![(s("k"), RV::Int(12))]))
    );
}
