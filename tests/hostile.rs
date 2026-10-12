//! Hostile input: random HIR mixing every expression form, the 0.3 ones
//! included (generators, `yield from`, `await`, `spawn`, `let_place`,
//! reference assignments, place arguments, named intrinsics of any name and
//! arity, unions and intersections), placed anywhere, repaired by
//! `finish_lenient` into valid HIR. Compiling never panics; a module that
//! compiles loads in bvm-lang, and running it under budgets never panics.
//! Deep nesting of the new forms compiles on a small native stack.

mod common;

use bcgen_lang::{BodyMode, CompileError, Compiler, Intrinsics, Options};
use bvm_lang::{Host, Limits, Program, Vm};
use common::progs::Rng;
use hir_lang::{
    Arg, ArgKind, Arm, BindMode, Binder, BinderId, BinderKind, Builder, Capture, CaptureMode,
    Closure, DefaultEval, Effects, Expr, ExprId, FnDef, Ident, Intrinsic, Item, ItemId, ItemKind,
    Lit, Name, Ns, Op, OpKind, Overflow, Param, ParamKind, Pat, Path, Prim, Res, Segment, Shift,
    Span, Ty, TyId,
};
use intern_lang::Interner;
use proptest::prelude::*;

struct G {
    r: Rng,
    b: Builder,
    names: Interner,
    /// The value binders in scope, innermost last.
    binders: Vec<BinderId>,
    made: usize,
    items: Vec<ItemId>,
    fuel: u32,
}

const INTRINSICS: &[&str] = &[
    "concat",
    "len",
    "iter",
    "iter_next",
    "resume",
    "coro_key",
    "coro_status",
    "mox.concat",
    "mox.concat_n",
    "mox.loose_eq",
    "mox.identical",
    "mox.spaceship",
    "mox.pow",
    "mox.cast_int",
    "mox.clone",
    "nope",
    "mox.nope",
];

impl G {
    fn name(&mut self, s: &str) -> Name {
        Name::new(self.names.intern(s))
    }

    fn binder(&mut self, kind: BinderKind) -> BinderId {
        self.made += 1;
        let n = self.name(&format!("v{}", self.made));
        self.b.binder(Binder::new(n, kind).with_mutable(true))
    }

    fn path(&mut self, s: &str, res: Res) -> ExprId {
        let n = self.name(s);
        let seg = Segment::new(n, self.b.origin());
        let segs = self.b.list(&[seg]);
        let p = self.b.path(Path {
            res,
            ..Path::new(segs, Ns::Value)
        });
        self.b.expr(Expr::Path(p))
    }

    fn ty(&mut self, d: u32) -> TyId {
        match self.r.below(if d == 0 { 3 } else { 6 }) {
            0 => self.b.ty(Ty::Prim(Prim::I64)),
            1 => self.b.ty(Ty::Prim(Prim::Str)),
            2 => self.b.ty(Ty::Any),
            3 | 4 => {
                let (a, b) = (self.ty(d - 1), self.ty(d - 1));
                let l = self.b.list(&[a, b]);
                if self.r.chance(50) {
                    self.b.ty(Ty::Union(l))
                } else {
                    self.b.ty(Ty::Intersection(l))
                }
            }
            _ => {
                let t = self.ty(d - 1);
                self.b.ty(Ty::Nullable(t))
            }
        }
    }

    fn effects(&mut self) -> Effects {
        let mut e = Effects::THROWS;
        if self.r.chance(40) {
            e = e.union(Effects::YIELD);
        }
        if self.r.chance(20) {
            e = e.union(Effects::ASYNC);
        }
        e
    }

    /// Parameters, and their binders (visible in the body).
    fn params(&mut self, d: u32) -> (Vec<hir_lang::ParamId>, Vec<BinderId>) {
        let n = self.r.below(4);
        let mut bs = Vec::new();
        let mut kinds: Vec<ParamKind> = (0..n)
            .map(|_| {
                self.r.pick(&[
                    ParamKind::Normal,
                    ParamKind::Normal,
                    ParamKind::NamedOnly,
                    ParamKind::Rest,
                    ParamKind::PositionalOnly,
                ])
            })
            .collect();
        let rank = |k: &ParamKind| match k {
            ParamKind::PositionalOnly => 0,
            ParamKind::Normal => 1,
            ParamKind::Rest => 2,
            _ => 3,
        };
        kinds.sort_by_key(rank);
        let mut seen_rest = false;
        kinds.retain(|k| {
            let keep = !(*k == ParamKind::Rest && seen_rest);
            seen_rest |= *k == ParamKind::Rest;
            keep
        });
        let ps = kinds
            .into_iter()
            .map(|kind| {
                let b = self.binder(BinderKind::Param);
                bs.push(b);
                let pat = self.b.pat(Pat::Bind {
                    binder: b,
                    mode: BindMode::Value,
                    sub: None,
                });
                let default = if kind != ParamKind::Rest && self.r.chance(30) {
                    Some(self.expr(d.saturating_sub(1)))
                } else {
                    None
                };
                self.b.param(Param {
                    pat,
                    ty: None,
                    default,
                    kind,
                    by_ref: self.r.chance(30),
                })
            })
            .collect();
        (ps, bs)
    }

    /// Evaluates `f` with `bs` in scope.
    fn scoped<T>(&mut self, bs: &[BinderId], f: impl FnOnce(&mut Self) -> T) -> T {
        let mark = self.binders.len();
        self.binders.extend_from_slice(bs);
        let r = f(self);
        self.binders.truncate(mark);
        r
    }

    /// An intrinsic's arity (usually the right one).
    fn arity(&mut self, name: &str) -> usize {
        let t = Intrinsics::mox();
        match t.get(name) {
            Some(d) if self.r.chance(85) => {
                let a = d.arity();
                usize::from(a.min())
                    + self.r.below(u64::from(a.max().min(3) - a.min().min(3)) + 1) as usize
            }
            _ => self.r.below(4) as usize,
        }
    }

    fn args(&mut self, d: u32) -> Vec<Arg> {
        let n = self.r.below(4);
        (0..n)
            .map(|i| {
                let kind = match self.r.below(5) {
                    0 => {
                        let s = self.names.intern(&format!("v{i}"));
                        ArgKind::Named(Ident::new(s, Span::empty(0)))
                    }
                    1 => ArgKind::Spread,
                    _ => ArgKind::Positional,
                };
                // A place argument is a positional or named place.
                let place = kind != ArgKind::Spread && self.r.chance(30);
                let value = if place {
                    self.place(d, false)
                } else {
                    self.expr(d)
                };
                Arg { kind, value, place }
            })
            .collect()
    }

    fn var(&mut self) -> ExprId {
        if self.r.below(1000) < 2 {
            return self.path("x", Res::Unresolved);
        }
        if self.binders.is_empty() {
            return self.b.int(7);
        }
        let b = self.binders[self.r.below(self.binders.len() as u64) as usize];
        self.b.use_binder(b)
    }

    fn expr(&mut self, d: u32) -> ExprId {
        self.b.set_span(Span::new(self.fuel, self.fuel + 1));
        if d == 0 || self.fuel == 0 {
            return match self.r.below(5) {
                0 => self.b.int(self.r.below(5) as i64 - 1),
                1 => self.b.str_lit("s"),
                2 => self.b.lit(Lit::Null),
                _ => self.var(),
            };
        }
        self.fuel -= 1;
        let d1 = d - 1;
        match self.r.below(28) {
            0 => {
                let key = self.r.chance(40).then(|| self.expr(d1));
                let value = (key.is_some() || self.r.chance(80)).then(|| self.expr(d1));
                self.b.expr(Expr::Yield { key, value })
            }
            1 => {
                let e = self.expr(d1);
                self.b.expr(Expr::YieldFrom(e))
            }
            2 => {
                let e = self.expr(d1);
                self.b.expr(Expr::Await(e))
            }
            3 => {
                let e = self.expr(d1);
                self.b.expr(Expr::Spawn(e))
            }
            4 => {
                let binder = self.binder(BinderKind::Place);
                let base = self.var();
                let k = self.expr(d1);
                let place = if self.r.chance(70) {
                    self.b.expr(Expr::Index { base, index: k })
                } else {
                    base
                };
                let body = self.scoped(&[binder], |g| g.expr(d1));
                self.b.expr(Expr::LetPlace {
                    binder,
                    place,
                    body,
                })
            }
            5 => {
                let target = self.place(d1, true);
                let source = self.place(d1, false);
                self.b.expr(Expr::RefAssign { target, source })
            }
            6 | 7 => {
                let target = self.place(d1, true);
                let value = self.expr(d1);
                let op = self.r.chance(30).then(|| Op::new(OpKind::Add));
                self.b.expr(Expr::Assign { target, op, value })
            }
            8 | 9 => {
                let name = self.r.pick(INTRINSICS);
                let sym = self.names.intern(name);
                let n = self.arity(name);
                let args: Vec<ExprId> = (0..n).map(|_| self.expr(d1)).collect();
                let args = self.b.list(&args);
                self.b.expr(Expr::Intrinsic {
                    kind: Intrinsic::Named(sym),
                    generic_args: hir_lang::List::EMPTY,
                    args,
                })
            }
            10 | 11 => {
                let kind = self.r.pick(&[
                    OpKind::Add,
                    OpKind::Pow,
                    OpKind::Not,
                    OpKind::BitNot,
                    OpKind::Shl,
                    OpKind::Abs,
                    OpKind::Eq,
                ]);
                let mut op = Op::new(kind);
                if op.policy.overflow.is_some() {
                    op = op.with_overflow(self.r.pick(&[Overflow::Error, Overflow::Promote]));
                }
                if op.policy.shift.is_some() {
                    op = op.with_shift(Shift::Saturate);
                }
                let args: Vec<ExprId> = (0..kind.arity()).map(|_| self.expr(d1)).collect();
                self.b.op_with(op, &args)
            }
            12 => {
                let ty = self.ty(3);
                let e = self.expr(d1);
                self.b.expr(Expr::Cast {
                    expr: e,
                    ty,
                    policy: hir_lang::Policy::CAST,
                })
            }
            13 | 14 => {
                let callee = if self.r.chance(30) && !self.items.is_empty() {
                    let i = self.items[self.r.below(self.items.len() as u64) as usize];
                    let d = self.b.def(hir_lang::Def::Item(i));
                    self.path("f", Res::Def(d))
                } else if self.r.chance(30) {
                    let s = self.names.intern("echo");
                    self.path("echo", Res::Extern(s))
                } else {
                    self.expr(d1)
                };
                let args = self.args(d1);
                let args = self.b.list(&args);
                self.b.expr(Expr::Call { callee, args })
            }
            15 => {
                let (params, pbs) = self.params(d1);
                let effects = self.effects();
                let mut inner = pbs;
                let captures = if !self.binders.is_empty() && self.r.chance(40) {
                    let ob = self.binders[self.r.below(self.binders.len() as u64) as usize];
                    let n = self.name("c");
                    let seg = Segment::new(n, self.b.origin());
                    let segs = self.b.list(&[seg]);
                    let outer = self.b.path(Path {
                        res: Res::Local(ob),
                        ..Path::new(segs, Ns::Value)
                    });
                    let binder = self.binder(BinderKind::Capture);
                    inner.push(binder);
                    vec![Capture {
                        outer,
                        binder,
                        mode: self.r.pick(&[CaptureMode::ByRef, CaptureMode::ByValue]),
                    }]
                } else {
                    Vec::new()
                };
                let body = self.scoped(&inner, |g| g.expr(d1));
                let params = self.b.list(&params);
                let captures = self.b.list(&captures);
                let implicit = self
                    .r
                    .chance(80)
                    .then(|| self.r.pick(&[CaptureMode::ByRef, CaptureMode::ByValue]));
                self.b.expr(Expr::Closure(Closure {
                    params,
                    ret: None,
                    body,
                    effects,
                    implicit,
                    captures,
                    self_binder: None,
                    defaults: DefaultEval::PerCall,
                }))
            }
            16 => {
                let s = self.expr(d1);
                let n = self.r.below(3) + 1;
                let arms: Vec<Arm> = (0..n)
                    .map(|_| {
                        let mut bound = Vec::new();
                        let pat = match self.r.below(4) {
                            0 => {
                                let ty = self.ty(3);
                                self.b.pat(Pat::TypeTest { ty, pat: None })
                            }
                            1 => {
                                let b = self.binder(BinderKind::Local);
                                bound.push(b);
                                self.b.pat(Pat::Bind {
                                    binder: b,
                                    mode: BindMode::Value,
                                    sub: None,
                                })
                            }
                            2 => self.b.pat(Pat::Lit(Lit::Null)),
                            _ => self.b.pat(Pat::Wild),
                        };
                        let body = self.scoped(&bound, |g| g.expr(d1));
                        Arm {
                            pat,
                            guard: None,
                            body,
                        }
                    })
                    .collect();
                let arms = self.b.list(&arms);
                self.b.expr(Expr::Match { scrutinee: s, arms })
            }
            17 => {
                let b = self.binder(BinderKind::Local);
                let pat = self.b.pat(Pat::Bind {
                    binder: b,
                    mode: BindMode::Value,
                    sub: None,
                });
                let init = self.expr(d1);
                let st = self.b.let_stmt(pat, Some(init));
                let tail = self.scoped(&[b], |g| g.expr(d1));
                self.b.block(&[st], Some(tail))
            }
            18 => {
                let body = self.expr(d1);
                let brk = self.b.expr(Expr::Break {
                    label: None,
                    value: None,
                });
                let st = self.b.expr_stmt(body);
                let blk = self.b.block(&[st], Some(brk));
                self.b.expr(Expr::Loop {
                    label: None,
                    body: blk,
                    step: None,
                })
            }
            19 => {
                let body = self.expr(d1);
                let b = self.binder(BinderKind::Local);
                let pat = self.b.pat(Pat::Bind {
                    binder: b,
                    mode: BindMode::Value,
                    sub: None,
                });
                let ab = self.scoped(&[b], |g| g.expr(d1));
                let arms = self.b.list(&[Arm {
                    pat,
                    guard: None,
                    body: ab,
                }]);
                let finally = self.r.chance(50).then(|| self.expr(d1));
                self.b.expr(Expr::Try {
                    body,
                    catches: arms,
                    finally,
                })
            }
            20 => {
                let es: Vec<ExprId> = (0..self.r.below(3)).map(|_| self.expr(d1)).collect();
                let l = self.b.list(&es);
                self.b.expr(Expr::Array(l))
            }
            21 => {
                let base = self.expr(d1);
                let index = self.expr(d1);
                self.b.expr(Expr::Index { base, index })
            }
            22 => {
                let c = self.expr(d1);
                let t = self.expr(d1);
                let e = self.expr(d1);
                self.b.expr(Expr::If {
                    cond: c,
                    then: t,
                    else_: Some(e),
                })
            }
            23 => {
                let v = self.r.chance(50).then(|| self.expr(d1));
                self.b.expr(Expr::Return(v))
            }
            24 if self.r.chance(5) => self.b.expr(Expr::Err),
            25 => {
                let e = self.expr(d1);
                self.b.expr(Expr::Throw(e))
            }
            _ => self.var(),
        }
    }

    /// A place expression (rarely a non-place); `append`: a write target,
    /// which may append.
    fn place(&mut self, d: u32, append: bool) -> ExprId {
        let base = self.var();
        match self.r.below(20) {
            0..=6 => base,
            7..=15 => {
                let k = self.expr(d);
                self.b.expr(Expr::Index { base, index: k })
            }
            16..=18 if append => self.b.expr(Expr::Append(base)),
            16..=18 => base,
            _ => self.expr(d),
        }
    }

    /// `{ let a = 1; let b = []; e }` with `a` and `b` in scope in `e`.
    fn body(&mut self, d: u32) -> ExprId {
        let a = self.binder(BinderKind::Local);
        let pa = self.b.bind(a);
        let one = self.b.int(1);
        let la = self.b.let_stmt(pa, Some(one));
        let bb = self.binder(BinderKind::Local);
        let pb = self.b.bind(bb);
        let arr = self.b.expr(Expr::Array(hir_lang::List::EMPTY));
        let lb = self.b.let_stmt(pb, Some(arr));
        let tail = self.scoped(&[a, bb], |g| g.expr(d));
        self.b.block(&[la, lb], Some(tail))
    }

    fn program(mut self) -> (hir_lang::Hir, Interner) {
        for i in 0..self.r.below(3) {
            let outer = std::mem::take(&mut self.binders);
            let (params, pbs) = self.params(2);
            let body = self.scoped(&pbs, |g| g.body(4));
            self.binders = outer;
            let effects = self.effects();
            let n = self.name(&format!("f{i}"));
            let params = self.b.list(&params);
            let item = self.b.item(Item::new(
                Some(n),
                ItemKind::Fn(FnDef {
                    params,
                    body: Some(body),
                    effects,
                    ..FnDef::default()
                }),
            ));
            self.items.push(item);
        }
        let body = self.body(6);
        let items = self.b.list(&self.items);
        let root = self.b.item(Item::new(
            None,
            ItemKind::Module {
                items,
                body: Some(body),
                effects: Effects::THROWS.union(Effects::YIELD).union(Effects::ASYNC),
            },
        ));
        match self.b.finish_lenient(root) {
            Ok((hir, problems)) => {
                if std::env::var("BCGEN_PROBLEMS").is_ok() {
                    for p in problems {
                        let k = format!("{p:?}");
                        println!("problem {k}");
                    }
                }
                (hir, self.names)
            }
            Err(e) => panic!("lenient finish refused: {e}"),
        }
    }
}

fn garbage(seed: u64) -> (hir_lang::Hir, Interner) {
    G {
        r: Rng::new(seed),
        b: Builder::new(),
        names: Interner::new(),
        binders: Vec::new(),
        made: 0,
        items: Vec::new(),
        fuel: 120,
    }
    .program()
}

/// A host binding every import a garbage program can name.
fn host() -> Host {
    let mut h = common::host(std::sync::Arc::new(std::sync::Mutex::new(Vec::new())));
    for (_, def) in Intrinsics::mox().iter() {
        if let Some((m, f)) = def.lowering().host() {
            let _ = h.register(m, f, |_, _| Ok(bvm_lang::Value::Nil));
        }
    }
    let _ = h.register_scheduler("ls.async", "spawn");
    h
}

/// Cases per run (`BCGEN_CASES` overrides, for long runs).
fn cases() -> u32 {
    std::env::var("BCGEN_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(2000)
}

proptest! {
    #![proptest_config(ProptestConfig { cases: cases(), ..ProptestConfig::default() })]

    #[test]
    fn garbage_compiles_or_errors_and_runs_without_panicking(seed in any::<u64>()) {
        let (hir, names) = garbage(seed);
        let opts = Options::new()
            .with_body(BodyMode::Entry)
            .with_intrinsics(Intrinsics::mox())
            .with_hook(bytecode_lang::Hook::Spawn, "ls.async", "spawn")
            .with_max_instructions(1 << 20);
        if let Ok(out) = Compiler::new(opts).compile(&hir, &names) {
            let program = Program::load(out.module().clone(), &host());
            prop_assert!(program.is_ok(), "{:?}", program.err());
            if let Ok(p) = program {
                let limits = Limits::new().with_fuel(20_000).with_depth(64).with_memory(16 << 20);
                let mut vm = Vm::with_limits(&p, limits);
                let _ = vm.run(out.entry(), &[]);
                let mut vm = Vm::with_limits(&p, limits);
                let _ = vm.run_async(out.entry(), &[]);
            }
        }
    }
}

/// Compiles `hir` on a thread with a 512 KiB stack.
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

#[test]
fn deep_let_place_yield_and_union_nests_compile_on_a_small_stack() {
    const DEPTH: usize = 20_000;
    let mut b = Builder::new();
    let mut names = Interner::new();
    let a =
        b.binder(Binder::new(Name::new(names.intern("a")), BinderKind::Local).with_mutable(true));
    let arr = b.expr(Expr::Array(hir_lang::List::EMPTY));
    let pa = b.bind(a);
    let la = b.let_stmt(pa, Some(arr));
    // let_place p_k = a[k] in (let_place ... in yield p_k) ...
    let mut inner = b.lit(Lit::Null);
    for k in 0..DEPTH {
        let p = b.binder(
            Binder::new(Name::new(names.intern(&format!("p{k}"))), BinderKind::Place)
                .with_mutable(true),
        );
        let va = b.use_binder(a);
        let key = b.int(k as i64);
        let place = b.expr(Expr::Index {
            base: va,
            index: key,
        });
        let vp = b.use_binder(p);
        let y = b.expr(Expr::Yield {
            key: Some(vp),
            value: Some(inner),
        });
        inner = b.expr(Expr::LetPlace {
            binder: p,
            place,
            body: y,
        });
    }
    // A cast to a union of intersections of unions ..., DEPTH deep.
    let mut ty = b.ty(Ty::Prim(Prim::I64));
    for k in 0..DEPTH {
        let other = b.ty(Ty::Prim(if k % 2 == 0 { Prim::Str } else { Prim::Bool }));
        let l = b.list(&[ty, other]);
        ty = b.ty(if k % 2 == 0 {
            Ty::Union(l)
        } else {
            Ty::Intersection(l)
        });
    }
    let cast = b.expr(Expr::Cast {
        expr: inner,
        ty,
        policy: hir_lang::Policy::CAST,
    });
    let body = b.block(&[la], Some(cast));
    let f = b.item(Item::new(
        Some(Name::new(names.intern("g"))),
        ItemKind::Fn(FnDef {
            body: Some(body),
            effects: Effects::THROWS.union(Effects::YIELD),
            ..FnDef::default()
        }),
    ));
    let root = b.module(None, &[f]);
    let hir = b.finish(root).expect("valid");
    let r = small_stack(|| bcgen_lang::compile(&hir, &names));
    assert!(r.is_ok(), "{:?}", r.err());
}

#[test]
fn a_generator_closure_with_too_many_captures_is_an_error() {
    // 254 locals captured by value plus two parameters: 256 signature
    // entries for the coroutine body.
    let mut b = Builder::new();
    let mut names = Interner::new();
    let mut stmts = Vec::new();
    let mut caps = Vec::new();
    for k in 0..254 {
        let n = Name::new(names.intern(&format!("c{k}")));
        let v = b.binder(Binder::new(n, BinderKind::Local).with_mutable(true));
        let pv = b.bind(v);
        let one = b.int(1);
        stmts.push(b.let_stmt(pv, Some(one)));
        let seg = Segment::new(n, b.origin());
        let segs = b.list(&[seg]);
        let outer = b.path(Path {
            res: Res::Local(v),
            ..Path::new(segs, Ns::Value)
        });
        let binder = b.binder(Binder::new(n, BinderKind::Capture));
        caps.push(Capture {
            outer,
            binder,
            mode: CaptureMode::ByValue,
        });
    }
    let mut params = Vec::new();
    for k in 0..2 {
        let pb = b.binder(Binder::new(
            Name::new(names.intern(&format!("q{k}"))),
            BinderKind::Param,
        ));
        let pat = b.bind(pb);
        params.push(b.param(Param::new(pat)));
    }
    let y = b.expr(Expr::Yield {
        key: None,
        value: None,
    });
    let params = b.list(&params);
    let captures = b.list(&caps);
    let clo = b.expr(Expr::Closure(Closure {
        params,
        ret: None,
        body: y,
        effects: Effects::THROWS.union(Effects::YIELD),
        implicit: None,
        captures,
        self_binder: None,
        defaults: DefaultEval::PerCall,
    }));
    let body = b.block(&stmts, Some(clo));
    let root = b.item(Item::new(
        None,
        ItemKind::Module {
            items: hir_lang::List::EMPTY,
            body: Some(body),
            effects: Effects::THROWS,
        },
    ));
    let hir = b.finish(root).expect("valid");
    let e = bcgen_lang::compile(&hir, &names).unwrap_err();
    assert!(matches!(e, CompileError::TooManyParams { .. }), "{e:?}");
}

#[test]
#[ignore = "a measurement"]
fn garbage_outcomes() {
    let mut counts: std::collections::BTreeMap<String, u32> = std::collections::BTreeMap::new();
    for seed in 0..2000u64 {
        let (hir, names) = garbage(seed);
        let opts = Options::new()
            .with_body(BodyMode::Entry)
            .with_intrinsics(Intrinsics::mox());
        let k = match Compiler::new(opts).compile(&hir, &names) {
            Ok(_) => "ok".to_string(),
            Err(e) => {
                format!("{e:?}")
                    .split([' ', '{', '('])
                    .next()
                    .unwrap_or("")
                    .to_string()
                    + match e {
                        CompileError::Unsupported { feature, .. } => format!(" {feature:?}"),
                        _ => String::new(),
                    }
                    .as_str()
            }
        };
        *counts.entry(k).or_insert(0) += 1;
    }
    println!("{counts:#?}");
}
