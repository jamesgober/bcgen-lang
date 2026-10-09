//! Compile time is linear in the unit's size: per-node cost from 146k to
//! 2.3M HIR nodes stays within a factor of two. A timing test, so it runs in
//! release builds on demand:
//! `cargo test --release --test scaling -- --ignored --nocapture`.

#![allow(dead_code, unused_imports)]
use bcgen_lang::{BodyMode, Compiler, Options};
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

#[test]
#[ignore = "a timing test: run in release"]
fn compile_time_is_linear_in_the_unit() {
    let mut per_node = Vec::new();
    for fns in [2_000usize, 8_000, 32_000] {
        let (hir, names) = synthetic(fns);
        let n: usize = [IdKind::Expr, IdKind::Stmt, IdKind::Pat, IdKind::Path]
            .iter()
            .map(|&k| hir.count(k))
            .sum();
        let compiler = Compiler::new(Options::new().with_body(BodyMode::Start));
        let t = std::time::Instant::now();
        for _ in 0..3 {
            assert!(compiler.compile(&hir, &names).is_ok());
        }
        let ns = t.elapsed().as_nanos() as f64 / 3.0 / n as f64;
        println!("{fns} functions, {n} nodes: {ns:.1} ns/node");
        per_node.push(ns);
    }
    let (first, last) = (per_node[0], per_node[per_node.len() - 1]);
    assert!(
        last < first * 2.0,
        "per-node cost grew from {first:.1} to {last:.1} ns"
    );
}
