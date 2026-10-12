//! End to end: a small Mox program, lowered by hand into HIR the way a
//! lowering emits it (names unresolved), resolved by a small lexical
//! resolver in the test (resolve-lang 0.3 is built on hir-lang 0.3, so it
//! cannot resolve this unit), compiled by bcgen-lang, and run on bvm-lang,
//! printing through a host function.
//!
//! The Mox source it stands for:
//!
//! ```text
//! function greet($name, $greeting = "Hello") {
//!     return $greeting . ", " . $name . "!";
//! }
//! function fib($n) { return $n < 2 ? $n : fib($n - 1) + fib($n - 2); }
//!
//! $people = ["Ada", "Linus", "Grace"];
//! foreach ($people as $i => $p) { echo($i, ": ", greet($p)); }
//! echo(greet("Mox", greeting: "Welcome"));
//!
//! $total = 0;
//! for ($i = 1; $i <= 10; $i++) { if ($i % 2 == 0) continue; $total += $i; }
//! echo("odd sum ", $total);
//!
//! $add = function ($x) use (&$total) { $total += $x; };
//! $add(100);
//! echo("total ", $total);
//!
//! try { echo(intdiv(1, 0)); } catch ($e) { echo("caught"); } finally { echo("finally"); }
//!
//! $counts = [];
//! foreach ([3, 1, 3, 2, 3] as $v) { $counts[$v] = ($counts[$v] ?? 0) + 1; }
//! echo("threes ", $counts[3]);
//! echo("fib ", fib(20));
//! ```

mod common;

use std::sync::{Arc, Mutex};

use bcgen_lang::{Compiler, LineIndex, Options};
use bvm_lang::{Program, Value, Vm};
use common::hb::H;
use hir_lang::{
    Arm, Binder, BinderKind, Capture, CaptureMode, Closure, DefaultEval, Effects, Expr, ExprId,
    Lit, Ns, OpKind, ParamKind, Pat, Res, Span,
};

/// A reference by name, left for the resolver.
fn name(h: &mut H, s: &str) -> ExprId {
    h.tick();
    let n = h.name(s);
    h.b.name_expr(n)
}

/// `let s = init;` binding a fresh local named `s`.
fn let_named(h: &mut H, s: &str, init: ExprId) -> hir_lang::StmtId {
    let b = h.local(s);
    h.let_(b, Some(init))
}

fn concat(h: &mut H, parts: &[ExprId]) -> ExprId {
    let mut acc = parts[0];
    for &p in &parts[1..] {
        acc = h.intrinsic("concat", &[acc, p]);
    }
    acc
}

fn echo(h: &mut H, args: &[ExprId]) -> hir_lang::StmtId {
    let e = name(h, "echo");
    let c = h.call(e, args);
    h.stmt(c)
}

/// `foreach (it_expr as k => v) body` lowered as HIR §9.4 does, with the
/// iteration intrinsics.
fn foreach(
    h: &mut H,
    coll: ExprId,
    k: &str,
    v: &str,
    body: Vec<hir_lang::StmtId>,
) -> hir_lang::StmtId {
    let it = h.local("it");
    let iter = h.intrinsic("iter", &[coll]);
    let lit = h.let_(it, Some(iter));
    let vit = h.var(it);
    let next = h.intrinsic("iter_next", &[vit]);
    let null = h.pat(Pat::Lit(Lit::Null));
    let brk = h.brk(None, None);
    let a1 = h.arm(null, None, brk);
    let kb = h.local(k);
    let vb = h.local(v);
    let pk = h.pbind(kb);
    let pv = h.pbind(vb);
    let elems = h.b.list(&[pk, pv]);
    let tup = h.pat(Pat::Tuple { elems, rest: None });
    let blk = h.block(&body, None);
    let a2 = h.arm(tup, None, blk);
    let m = h.match_(next, &[a1, a2]);
    let lp = h.loop_(None, m, None);
    let outer = h.block(&[lit], Some(lp));
    h.stmt(outer)
}

/// Resolves every unresolved one-segment path: to the innermost local of
/// that name in scope, else to a root-level function of that name, else to
/// the host function of that name (what resolve-lang's `php` preset does for
/// this program).
fn resolve_by_hand(hir: &mut hir_lang::Hir, names: &intern_lang::Interner) {
    let root = hir.root();
    let items: Vec<(String, hir_lang::ItemId)> = match hir.item(root).kind {
        hir_lang::ItemKind::Module { items, .. } => hir
            .list(items)
            .iter()
            .filter_map(|&i| {
                let n = hir.item(i).name?;
                Some((names.resolve(n.sym).unwrap_or("").to_string(), i))
            })
            .collect(),
        _ => Vec::new(),
    };
    for i in 0..hir.count(hir_lang::IdKind::Path) {
        let Some(p) = hir_lang::PathId::from_index(i) else {
            continue;
        };
        let path = *hir.path(p);
        if path.res != Res::Unresolved {
            continue;
        }
        let Some(seg) = hir.list(path.segments).first().copied() else {
            continue;
        };
        let text = names.resolve(seg.name.sym).unwrap_or("").to_string();
        let res = match hir.lookup_local(p, seg.name) {
            Some(b) => Res::Local(b),
            None => match items.iter().find(|(n, _)| *n == text) {
                Some(&(_, item)) => Res::Def(hir.def(hir_lang::Def::Item(item))),
                None => Res::Extern(seg.name.sym),
            },
        };
        hir.resolve(p, res).expect("resolves");
    }
}

fn program() -> (hir_lang::Hir, intern_lang::Interner) {
    let mut h = H::new();
    // function greet($name, $greeting = "Hello")
    let (p1, _) = h.param("name", ParamKind::Normal, None, false);
    let hello = h.str("Hello");
    let (p2, _) = h.param("greeting", ParamKind::Normal, Some(hello), false);
    let g = name(&mut h, "greeting");
    let sep = h.str(", ");
    let n = name(&mut h, "name");
    let bang = h.str("!");
    let msg = concat(&mut h, &[g, sep, n, bang]);
    let ret = h.ret(Some(msg));
    let body = h.block(&[], Some(ret));
    let greet = h.func("greet", &[p1, p2], body, DefaultEval::PerCall);

    // function fib($n)
    let (pn, _) = h.param("n", ParamKind::Normal, None, false);
    let n1 = name(&mut h, "n");
    let two = h.int(2);
    let lt = h.op(OpKind::Lt, &[n1, two]);
    let n2 = name(&mut h, "n");
    let mut rec = Vec::new();
    for k in [1, 2] {
        let f = name(&mut h, "fib");
        let nn = name(&mut h, "n");
        let kk = h.int(k);
        let sub = h.op(OpKind::Sub, &[nn, kk]);
        rec.push(h.call(f, &[sub]));
    }
    let sum = h.op(OpKind::Add, &[rec[0], rec[1]]);
    let ife = h.if_(lt, n2, Some(sum));
    let ret = h.ret(Some(ife));
    let fbody = h.block(&[], Some(ret));
    let fib = h.func("fib", &[pn], fbody, DefaultEval::PerCall);

    let mut stmts = Vec::new();
    // $people = [...]; foreach
    let names: Vec<ExprId> = ["Ada", "Linus", "Grace"].iter().map(|s| h.str(s)).collect();
    let arr = h.array(&names);
    stmts.push(let_named(&mut h, "people", arr));
    let people = name(&mut h, "people");
    let i = name(&mut h, "i");
    let colon = h.str(": ");
    let gr = name(&mut h, "greet");
    let p = name(&mut h, "p");
    let call = h.call(gr, &[p]);
    let e1 = echo(&mut h, &[i, colon, call]);
    stmts.push(foreach(&mut h, people, "i", "p", vec![e1]));
    // greet("Mox", greeting: "Welcome")
    let gr = name(&mut h, "greet");
    let mox = h.str("Mox");
    let welcome = h.str("Welcome");
    let named = h.named("greeting", welcome);
    let c = h.call_args(gr, &[hir_lang::Arg::positional(mox), named]);
    stmts.push(echo(&mut h, &[c]));
    // $total = 0; for (...)
    let zero = h.int(0);
    stmts.push(let_named(&mut h, "total", zero));
    let one = h.int(1);
    let ib = h.local("i");
    let li = h.let_(ib, Some(one));
    let vi = name(&mut h, "i");
    let ten = h.int(10);
    let le = h.op(OpKind::Le, &[vi, ten]);
    let empty = h.block(&[], None);
    let brk = h.brk(None, None);
    let brkb = h.block(&[], Some(brk));
    let guard = h.if_(le, empty, Some(brkb));
    let gs = h.stmt(guard);
    let vi2 = name(&mut h, "i");
    let two = h.int(2);
    let rem = h.op(OpKind::Rem, &[vi2, two]);
    let z = h.int(0);
    let even = h.op(OpKind::Eq, &[rem, z]);
    let cont = h.cont(None);
    let cb = h.block(&[], Some(cont));
    let ifc = h.if_(even, cb, None);
    let cs = h.stmt(ifc);
    let t = name(&mut h, "total");
    let vi3 = name(&mut h, "i");
    let add = h.compound(t, hir_lang::Op::new(OpKind::Add), vi3);
    let adds = h.stmt(add);
    let body = h.block(&[gs, cs, adds], None);
    let ti = name(&mut h, "i");
    let vi4 = name(&mut h, "i");
    let one2 = h.int(1);
    let inc = h.op(OpKind::Add, &[vi4, one2]);
    let step = h.assign(ti, inc);
    let lp = h.loop_(None, body, Some(step));
    let forb = h.block(&[li], Some(lp));
    stmts.push(h.stmt(forb));
    let odd = h.str("odd sum ");
    let tt = name(&mut h, "total");
    stmts.push(echo(&mut h, &[odd, tt]));
    // $add = function ($x) use (&$total) { $total += $x; }
    h.tick();
    let total_outer = {
        let n = h.name("total");
        h.b.name_path(n, Ns::Value)
    };
    let tn = h.name("total");
    let cap_b =
        h.b.binder(Binder::new(tn, BinderKind::Capture).with_mutable(true));
    let cap = Capture {
        outer: total_outer,
        binder: cap_b,
        mode: CaptureMode::ByRef,
    };
    let (px, _) = h.param("x", ParamKind::Normal, None, false);
    let t2 = name(&mut h, "total");
    let x = name(&mut h, "x");
    let addx = h.compound(t2, hir_lang::Op::new(OpKind::Add), x);
    let ab = h.block(&[], Some(addx));
    let params = h.b.list(&[px]);
    let caps = h.b.list(&[cap]);
    let clo = h.expr(Expr::Closure(Closure {
        params,
        ret: None,
        body: ab,
        effects: Effects::THROWS,
        implicit: None,
        captures: caps,
        self_binder: None,
        defaults: DefaultEval::PerCall,
    }));
    stmts.push(let_named(&mut h, "add", clo));
    let a = name(&mut h, "add");
    let hundred = h.int(100);
    let call = h.call(a, &[hundred]);
    stmts.push(h.stmt(call));
    let tl = h.str("total ");
    let tt = name(&mut h, "total");
    stmts.push(echo(&mut h, &[tl, tt]));
    // try { echo(intdiv(1, 0)) } catch ($e) { echo("caught") } finally { echo("finally") }
    let one = h.int(1);
    let zero = h.int(0);
    let div = h.op(OpKind::Div, &[one, zero]);
    let e = name(&mut h, "echo");
    let tb = h.call(e, &[div]);
    let eb = h.local("e");
    let pe = h.pbind(eb);
    let caught = h.str("caught");
    let ec = name(&mut h, "echo");
    let cbody = h.call(ec, &[caught]);
    let arm = Arm {
        pat: pe,
        guard: None,
        body: cbody,
    };
    let fin = h.str("finally");
    let ef = name(&mut h, "echo");
    let fbody = h.call(ef, &[fin]);
    let tr = h.try_(tb, &[arm], Some(fbody));
    stmts.push(h.stmt(tr));
    // $counts: a PHP array used as a map, with `??` lowered to a try.
    let empty = h.array(&[]);
    stmts.push(let_named(&mut h, "counts", empty));
    let items: Vec<ExprId> = [3, 1, 3, 2, 3].iter().map(|&v| h.int(v)).collect();
    let coll = h.array(&items);
    let c1 = name(&mut h, "counts");
    let v1 = name(&mut h, "v");
    let target = h.index(c1, v1);
    let c2 = name(&mut h, "counts");
    let v2 = name(&mut h, "v");
    let read = h.index(c2, v2);
    let w = h.pat(Pat::Wild);
    let z = h.int(0);
    let dflt = Arm {
        pat: w,
        guard: None,
        body: z,
    };
    let coalesce = h.try_(read, &[dflt], None);
    let one = h.int(1);
    let plus = h.op(OpKind::Add, &[coalesce, one]);
    let asg = h.assign(target, plus);
    let s = h.stmt(asg);
    stmts.push(foreach(&mut h, coll, "k", "v", vec![s]));
    let th = h.str("threes ");
    let c3 = name(&mut h, "counts");
    let three = h.int(3);
    let get = h.index(c3, three);
    stmts.push(echo(&mut h, &[th, get]));
    let fl = h.str("fib ");
    let f = name(&mut h, "fib");
    let twenty = h.int(20);
    let fc = h.call(f, &[twenty]);
    stmts.push(echo(&mut h, &[fl, fc]));
    let tot = name(&mut h, "total");
    let body = h.block(&stmts, Some(tot));
    let _ = Span::empty(0);
    h.finish(&[greet, fib], Some(body))
}

#[test]
fn a_mox_program_runs_end_to_end() {
    let (mut hir, names) = program();
    resolve_by_hand(&mut hir, &names);
    let lines = LineIndex::new("main.mox", 0, "");
    let out = Compiler::new(Options::new())
        .with_locator(&lines)
        .compile(&hir, &names)
        .expect("compiles");

    let printed = Arc::new(Mutex::new(Vec::new()));
    let program =
        Program::load(out.module().clone(), &common::host(printed.clone())).expect("loads");
    let mut vm = Vm::new(&program);
    let result = vm.run(out.entry(), &[]).expect("runs");
    assert_eq!(result, Value::Int(125));
    let printed = printed.lock().expect("lock").clone();
    assert_eq!(
        printed,
        vec![
            "0: Hello, Ada!",
            "1: Hello, Linus!",
            "2: Hello, Grace!",
            "Welcome, Mox!",
            "odd sum 25",
            "total 125",
            "caught",
            "finally",
            "threes 3",
            "fib 6765",
        ]
    );

    // The reference interpreter agrees on everything.
    let (r, rp) = common::run_reference(&hir, &names, common::Profile::PHP, 10_000_000);
    assert_eq!(r, common::Outcome::Value(common::RV::Int(125)));
    assert_eq!(rp, printed);
}
