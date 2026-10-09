//! Benchmarks: compile throughput on synthetic units of 100k to 1M HIR
//! nodes, and the run time on bvm-lang of classic programs compiled by
//! bcgen-lang (fib, a counting loop, map-heavy PHP-array code).

use std::hint::black_box;

use bcgen_lang::{BodyMode, Compiler, Options};
use bvm_lang::{Host, Program, Vm};
use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use hir_lang::{
    Binder, BinderId, BinderKind, Builder, Def, DefaultEval, Effects, Expr, ExprId, FnDef, Hir,
    IdKind, Item, ItemId, ItemKind, Name, Ns, OpKind, Param, ParamId, Path, Res, Segment, StmtId,
};
use intern_lang::Interner;

struct B {
    b: Builder,
    names: Interner,
}

impl B {
    fn new() -> Self {
        B {
            b: Builder::new(),
            names: Interner::new(),
        }
    }

    fn local(&mut self, s: &str) -> BinderId {
        let n = Name::new(self.names.intern(s));
        self.b
            .binder(Binder::new(n, BinderKind::Local).with_mutable(true))
    }

    fn param(&mut self, s: &str) -> (ParamId, BinderId) {
        let n = Name::new(self.names.intern(s));
        let b = self.b.binder(Binder::new(n, BinderKind::Param));
        let p = self.b.bind(b);
        (self.b.param(Param::new(p)), b)
    }

    fn func(&mut self, name: &str, params: &[ParamId], body: ExprId) -> ItemId {
        let n = Name::new(self.names.intern(name));
        let params = self.b.list(params);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Fn(FnDef {
                params,
                body: Some(body),
                effects: Effects::THROWS,
                defaults: DefaultEval::PerCall,
                ..FnDef::default()
            }),
        ))
    }

    fn fn_ref(&mut self, name: Name, item: ItemId) -> ExprId {
        let d = self.b.def(Def::Item(item));
        let seg = Segment::new(name, self.b.origin());
        let segs = self.b.list(&[seg]);
        let p = self.b.path(Path {
            res: Res::Def(d),
            ..Path::new(segs, Ns::Value)
        });
        self.b.expr(Expr::Path(p))
    }

    fn assign(&mut self, t: BinderId, v: ExprId) -> StmtId {
        let target = self.b.use_binder(t);
        let a = self.b.expr(Expr::Assign {
            target,
            op: None,
            value: v,
        });
        self.b.expr_stmt(a)
    }

    fn module(mut self, items: &[ItemId], body: Option<ExprId>) -> (Hir, Interner) {
        let items = self.b.list(items);
        let root = self.b.item(Item::new(
            None,
            ItemKind::Module {
                items,
                body,
                effects: Effects::THROWS,
            },
        ));
        match self.b.finish(root) {
            Ok(h) => (h, self.names),
            Err(e) => panic!("invalid HIR: {e}"),
        }
    }

    /// `{ let i = 0; loop [step: i = i + 1] { if i >= n { break }; body } }`
    fn counted(
        &mut self,
        n: ExprId,
        body: impl FnOnce(&mut Self, BinderId) -> Vec<StmtId>,
    ) -> ExprId {
        let i = self.local("i");
        let zero = self.b.int(0);
        let pi = self.b.bind(i);
        let li = self.b.let_stmt(pi, Some(zero));
        let vi = self.b.use_binder(i);
        let ge = self.b.op(OpKind::Ge, &[vi, n]);
        let brk = self.b.expr(Expr::Break {
            label: None,
            value: None,
        });
        let bb = self.b.block(&[], Some(brk));
        let guard = self.b.expr(Expr::If {
            cond: ge,
            then: bb,
            else_: None,
        });
        let mut stmts = vec![self.b.expr_stmt(guard)];
        stmts.extend(body(self, i));
        let lb = self.b.block(&stmts, None);
        let vi2 = self.b.use_binder(i);
        let one = self.b.int(1);
        let inc = self.b.op(OpKind::Add, &[vi2, one]);
        let ti = self.b.use_binder(i);
        let step = self.b.expr(Expr::Assign {
            target: ti,
            op: None,
            value: inc,
        });
        let lp = self.b.expr(Expr::Loop {
            label: None,
            body: lb,
            step: Some(step),
        });
        self.b.block(&[li], Some(lp))
    }
}

/// A unit of `fns` functions, each a mix of locals, arithmetic, `if`, a
/// loop, array building and indexing, and a call to the previous function.
fn synthetic(fns: usize) -> (Hir, Interner) {
    let mut s = B::new();
    let mut items: Vec<(Name, ItemId)> = Vec::new();
    for f in 0..fns {
        let (pa, a) = s.param("a");
        let (pb, b) = s.param("b");
        let acc = s.local("acc");
        let arr = s.local("arr");
        let va = s.b.use_binder(a);
        let vb = s.b.use_binder(b);
        let prod = s.b.op(OpKind::Mul, &[va, vb]);
        let p1 = s.b.bind(acc);
        let l1 = s.b.let_stmt(p1, Some(prod));
        let empty = s.b.expr(Expr::Array(hir_lang::List::EMPTY));
        let p2 = s.b.bind(arr);
        let l2 = s.b.let_stmt(p2, Some(empty));
        let n = s.b.int(4);
        let lp = s.counted(n, |s, i| {
            let vacc = s.b.use_binder(acc);
            let vi = s.b.use_binder(i);
            let add = s.b.op(OpKind::Add, &[vacc, vi]);
            let st = s.assign(acc, add);
            let ta = s.b.use_binder(arr);
            let app = s.b.expr(Expr::Append(ta));
            let vi2 = s.b.use_binder(i);
            let w = s.b.expr(Expr::Assign {
                target: app,
                op: None,
                value: vi2,
            });
            vec![st, s.b.expr_stmt(w)]
        });
        let s3 = s.b.expr_stmt(lp);
        let vacc = s.b.use_binder(acc);
        let hundred = s.b.int(100);
        let gt = s.b.op(OpKind::Gt, &[vacc, hundred]);
        let va2 = s.b.use_binder(a);
        let vb2 = s.b.use_binder(b);
        let then = s.b.op(OpKind::Sub, &[va2, vb2]);
        let els = match items.last().copied() {
            Some((pname, prev)) => {
                let c = s.fn_ref(pname, prev);
                let vb = s.b.use_binder(b);
                let va = s.b.use_binder(a);
                s.b.call(c, &[vb, va])
            }
            None => s.b.int(0),
        };
        let ife = s.b.expr(Expr::If {
            cond: gt,
            then,
            else_: Some(els),
        });
        let varr = s.b.use_binder(arr);
        let z = s.b.int(0);
        let ix = s.b.expr(Expr::Index {
            base: varr,
            index: z,
        });
        let tail = s.b.op(OpKind::Add, &[ife, ix]);
        let body = s.b.block(&[l1, l2, s3], Some(tail));
        let name = format!("f{f}");
        let item = s.func(&name, &[pa, pb], body);
        items.push((Name::new(s.names.intern(&name)), item));
    }
    let ids: Vec<ItemId> = items.iter().map(|&(_, i)| i).collect();
    s.module(&ids, None)
}

fn nodes(hir: &Hir) -> u64 {
    [
        IdKind::Item,
        IdKind::Expr,
        IdKind::Stmt,
        IdKind::Pat,
        IdKind::Path,
        IdKind::Param,
    ]
    .iter()
    .map(|&k| hir.count(k) as u64)
    .sum()
}

fn compile_throughput(c: &mut Criterion) {
    let mut g = c.benchmark_group("compile");
    g.sample_size(10);
    for fns in [2_000usize, 7_000, 20_000] {
        let (hir, names) = synthetic(fns);
        let n = nodes(&hir);
        g.throughput(Throughput::Elements(n));
        g.bench_with_input(BenchmarkId::new("synthetic_nodes", n), &hir, |b, hir| {
            b.iter(|| bcgen_lang::compile(black_box(hir), &names));
        });
    }
    g.finish();
}

fn load(hir: &Hir, names: &Interner) -> (Program, bytecode_lang::FuncId) {
    let opts = Options::new().with_body(BodyMode::Entry);
    match Compiler::new(opts).compile(hir, names) {
        Ok(out) => {
            let entry = out.entry();
            match Program::load(out.into_module(), &Host::new()) {
                Ok(p) => (p, entry),
                Err(e) => panic!("load: {e}"),
            }
        }
        Err(e) => panic!("compile: {e}"),
    }
}

/// `fn fib(n) { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }  fib(n)`
fn fib(n: i64) -> (Hir, Interner) {
    let mut s = B::new();
    let (pn, nb) = s.param("n");
    let fname = Name::new(s.names.intern("fib"));
    // The function is the first item the builder creates.
    let Some(me) = ItemId::from_index(0) else {
        panic!("item id")
    };
    let call = |s: &mut B, k: i64| {
        let callee = s.fn_ref(fname, me);
        let vn = s.b.use_binder(nb);
        let kk = s.b.int(k);
        let sub = s.b.op(OpKind::Sub, &[vn, kk]);
        s.b.call(callee, &[sub])
    };
    let vn = s.b.use_binder(nb);
    let two = s.b.int(2);
    let lt = s.b.op(OpKind::Lt, &[vn, two]);
    let vn2 = s.b.use_binder(nb);
    let c1 = call(&mut s, 1);
    let c2 = call(&mut s, 2);
    let sum = s.b.op(OpKind::Add, &[c1, c2]);
    let ife = s.b.expr(Expr::If {
        cond: lt,
        then: vn2,
        else_: Some(sum),
    });
    let body = s.b.block(&[], Some(ife));
    let f = s.func("fib", &[pn], body);
    assert_eq!(f, me);
    let callee = s.fn_ref(fname, f);
    let arg = s.b.int(n);
    let main = s.b.call(callee, &[arg]);
    s.module(&[f], Some(main))
}

/// `{ let s = 0; for i in 0..n { s = s + i }; s }`
fn counting(n: i64) -> (Hir, Interner) {
    let mut s = B::new();
    let acc = s.local("s");
    let zero = s.b.int(0);
    let pa = s.b.bind(acc);
    let la = s.b.let_stmt(pa, Some(zero));
    let nn = s.b.int(n);
    let lp = s.counted(nn, |s, i| {
        let va = s.b.use_binder(acc);
        let vi = s.b.use_binder(i);
        let add = s.b.op(OpKind::Add, &[va, vi]);
        vec![s.assign(acc, add)]
    });
    let ls = s.b.expr_stmt(lp);
    let va = s.b.use_binder(acc);
    let body = s.b.block(&[la, ls], Some(va));
    s.module(&[], Some(body))
}

/// `{ let a = []; for i in 0..n { a[] = i; (g[i % 64][] = i) }; sum a[i] }`:
/// appends to a PHP array, then reads it back by index; with `nested`, also
/// nested writes, which separate the inner array on every write (the cost
/// the README's PHP-semantics notes describe).
fn map_heavy(n: i64, nested: bool) -> (Hir, Interner) {
    let mut s = B::new();
    let a = s.local("a");
    let g = s.local("g");
    let e1 = s.b.expr(Expr::Array(hir_lang::List::EMPTY));
    let p1 = s.b.bind(a);
    let l1 = s.b.let_stmt(p1, Some(e1));
    let e2 = s.b.expr(Expr::Array(hir_lang::List::EMPTY));
    let p2 = s.b.bind(g);
    let l2 = s.b.let_stmt(p2, Some(e2));
    let nn = s.b.int(n);
    let fill = s.counted(nn, |s, i| {
        let ta = s.b.use_binder(a);
        let app = s.b.expr(Expr::Append(ta));
        let vi = s.b.use_binder(i);
        let w = s.b.expr(Expr::Assign {
            target: app,
            op: None,
            value: vi,
        });
        let mut out = vec![s.b.expr_stmt(w)];
        if nested {
            let tg = s.b.use_binder(g);
            let vi2 = s.b.use_binder(i);
            let k = s.b.int(64);
            let m = s.b.op(OpKind::Rem, &[vi2, k]);
            let ix = s.b.expr(Expr::Index { base: tg, index: m });
            let app2 = s.b.expr(Expr::Append(ix));
            let vi3 = s.b.use_binder(i);
            let w2 = s.b.expr(Expr::Assign {
                target: app2,
                op: None,
                value: vi3,
            });
            out.push(s.b.expr_stmt(w2));
        }
        out
    });
    let s1 = s.b.expr_stmt(fill);
    let total = s.local("t");
    let z = s.b.int(0);
    let pt = s.b.bind(total);
    let lt = s.b.let_stmt(pt, Some(z));
    let nn2 = s.b.int(n);
    let sum = s.counted(nn2, |s, i| {
        let vt = s.b.use_binder(total);
        let va = s.b.use_binder(a);
        let vi = s.b.use_binder(i);
        let ix = s.b.expr(Expr::Index {
            base: va,
            index: vi,
        });
        let add = s.b.op(OpKind::Add, &[vt, ix]);
        vec![s.assign(total, add)]
    });
    let s2 = s.b.expr_stmt(sum);
    let vt = s.b.use_binder(total);
    let body = s.b.block(&[l1, l2, s1, lt, s2], Some(vt));
    s.module(&[], Some(body))
}

fn run_time(c: &mut Criterion) {
    let mut g = c.benchmark_group("run");
    g.sample_size(10);
    let cases: Vec<(&str, (Hir, Interner))> = vec![
        ("fib_25", fib(25)),
        ("count_1m", counting(1_000_000)),
        ("php_array_append_index_100k", map_heavy(100_000, false)),
        ("php_array_nested_writes_100k", map_heavy(100_000, true)),
    ];
    for (name, (hir, names)) in &cases {
        let (program, entry) = load(hir, names);
        g.bench_function(*name, |b| {
            b.iter(|| {
                let mut vm = Vm::new(&program);
                black_box(vm.run(entry, &[]))
            });
        });
    }
    g.finish();
}

criterion_group!(benches, compile_throughput, run_time);
criterion_main!(benches);
