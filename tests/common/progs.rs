//! Random well-formed dynamic programs, built with hir-lang's `Builder`.
//!
//! Every program terminates by construction: functions call only functions
//! declared before them, loops count with a variable nothing else can write,
//! and both sides run under budgets anyway. Programs exercise every form the
//! compiler supports: arithmetic under random OPS policies (`promote`
//! included), comparisons, conversions, locals and assignment (plain,
//! compound, through index chains), `if`, loops with steps and labeled
//! `break`/`continue`, `match` with literal, binding, tuple, range, or, and
//! type-test patterns and guards, functions with defaults, named, and rest
//! parameters (called directly, as values, with spreads, and wrongly),
//! closures capturing by value and by reference, arrays and maps (literals,
//! reads, writes, appends, nested writes), strings, `throw`,
//! `try`/`catch`/`finally` (with jumps out of `finally`), `defer`, globals,
//! and host calls.

#![allow(dead_code)]

use hir_lang::{
    Arg, ArgKind, Arm, BinderId, CaptureMode, DefaultEval, DivZero, ExprId, Hir, ItemId, Lit, Op,
    OpKind, Overflow, ParamKind, Pat, PatId, Prim, Shift, StmtId, Ty,
};
use intern_lang::Interner;

use super::hb::H;

pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng((seed ^ 0x9E37_79B9_7F4A_7C15) | 1)
    }

    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }

    pub fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }

    pub fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len() as u64) as usize]
    }
}

#[derive(Clone)]
struct FnSig {
    item: ItemId,
    name: String,
    /// (kind, has default, name)
    params: Vec<(ParamKind, bool, String)>,
}

#[derive(Clone, Default)]
struct Cx {
    /// Readable variables, and whether code may write them.
    vars: Vec<(BinderId, bool)>,
    /// Enclosing loops of this frame: their labels.
    loops: Vec<Option<BinderId>>,
    in_fn: bool,
    /// `throw` is allowed (functions, closures, and the body declare
    /// `THROWS`; defaults and initializers do not).
    can_throw: bool,
}

pub struct Gen {
    r: Rng,
    pub h: H,
    fuel: u32,
    fns: Vec<FnSig>,
    globals: Vec<(ItemId, String)>,
    consts: Vec<(ItemId, String)>,
    /// Statics and `global` aliases: never the target of `t = &s`.
    aliases: Vec<BinderId>,
    names: u32,
}

const INTS: &[i64] = &[
    0,
    1,
    2,
    -1,
    3,
    7,
    10,
    -7,
    100,
    255,
    256,
    i64::MAX,
    i64::MIN,
    i64::MAX - 1,
    1 << 53,
];
const FLOATS: &[f64] = &[
    0.0,
    -0.0,
    1.5,
    -2.5,
    3.0,
    0.1,
    1e300,
    -1e300,
    f64::INFINITY,
    f64::NAN,
    2.0,
    -7.0,
];
const STRS: &[&str] = &[
    "",
    "a",
    "ab",
    "1",
    "01",
    "-5",
    "x1",
    "7",
    "-0",
    "-01",
    "9223372036854775807",
    "9223372036854775808",
    "-9223372036854775808",
    "-9223372036854775809",
    " 1",
    "+1",
];

impl Gen {
    pub fn new(seed: u64) -> Self {
        Gen {
            r: Rng::new(seed),
            h: H::new(),
            fuel: 220,
            fns: Vec::new(),
            globals: Vec::new(),
            consts: Vec::new(),
            aliases: Vec::new(),
            names: 0,
        }
    }

    fn fresh(&mut self, base: &str) -> String {
        self.names += 1;
        format!("{base}{}", self.names)
    }

    fn local(&mut self) -> BinderId {
        let n = self.fresh("v");
        self.h.local(&n)
    }

    /// A whole program: globals, functions, and a module body.
    pub fn program(mut self) -> (Hir, Interner) {
        let mut items = Vec::new();
        for _ in 0..self.r.below(3) {
            let name = self.fresh("G");
            let init = if self.r.chance(50) {
                Some(self.literal())
            } else {
                let cx = Cx::default();
                Some(self.expr(&cx, 1))
            };
            let g = self.h.global(&name, init);
            self.globals.push((g, name));
            items.push(g);
        }
        for _ in 0..self.r.below(3) {
            let name = self.fresh("K");
            let v = self.literal();
            let c = self.h.constant(&name, v);
            self.consts.push((c, name));
            items.push(c);
        }
        for _ in 0..self.r.below(4) {
            let f = self.function();
            items.push(f);
        }
        let mut cx = Cx {
            in_fn: true,
            can_throw: true,
            ..Cx::default()
        };
        let body = self.block(&mut cx, 3, true);
        self.h.finish(&items, Some(body))
    }

    fn function(&mut self) -> ItemId {
        let name = self.fresh("f");
        let mut cx = Cx {
            in_fn: true,
            can_throw: true,
            ..Cx::default()
        };
        let mut params = Vec::new();
        let mut sig = Vec::new();
        let n = self.r.below(4);
        let mut named_only = false;
        let once = self.r.chance(15);
        for i in 0..n {
            let pname = self.fresh("p");
            let kind = if i + 1 == n && !named_only && self.r.chance(25) {
                ParamKind::Rest
            } else if named_only || (i > 0 && self.r.chance(15)) {
                named_only = true;
                ParamKind::NamedOnly
            } else {
                ParamKind::Normal
            };
            let default = if kind != ParamKind::Rest && (named_only || self.r.chance(35)) {
                if once {
                    // Evaluated once, at definition: no parameter is visible.
                    Some(self.literal())
                } else {
                    // Evaluated per call: may read the earlier parameters
                    // (a default is its own frame: no `return` there).
                    let dcx = Cx {
                        vars: cx.vars.clone(),
                        loops: Vec::new(),
                        in_fn: false,
                        can_throw: false,
                    };
                    Some(self.expr(&dcx, 1))
                }
            } else {
                None
            };
            let (p, b) = self.h.param(&pname, kind, default, false);
            params.push(p);
            cx.vars.push((b, true));
            sig.push((kind, default.is_some(), pname));
        }
        let body = self.block(&mut cx, 2, true);
        let defaults = if once {
            DefaultEval::Once
        } else {
            DefaultEval::PerCall
        };
        let item = self.h.func(&name, &params, body, defaults);
        self.fns.push(FnSig {
            item,
            name,
            params: sig,
        });
        item
    }

    // ------------------------------------------------------------ leaves

    fn literal(&mut self) -> ExprId {
        match self.r.below(14) {
            0..=4 => {
                let v = self.r.below(9) as i64 - 3;
                self.h.int(v)
            }
            5..=7 => {
                let v = self.r.pick(INTS);
                self.h.int(v)
            }
            8 | 9 => {
                let v = self.r.pick(FLOATS);
                self.h.float(v)
            }
            10 | 11 => {
                let s = self.r.pick(STRS);
                self.h.str(s)
            }
            12 => {
                let b = self.r.chance(50);
                self.h.boolean(b)
            }
            _ => self.h.nil(),
        }
    }

    fn small_int(&mut self) -> ExprId {
        let v = self.r.below(6) as i64 - 1;
        self.h.int(v)
    }

    fn leaf(&mut self, cx: &Cx) -> ExprId {
        if !cx.vars.is_empty() && self.r.chance(55) {
            let (b, _) = cx.vars[self.r.below(cx.vars.len() as u64) as usize];
            return self.h.var(b);
        }
        if !self.globals.is_empty() && self.r.chance(8) {
            let (g, n) = self.globals[self.r.below(self.globals.len() as u64) as usize].clone();
            return self.h.item_ref(&n, g);
        }
        if !self.consts.is_empty() && self.r.chance(5) {
            let (c, n) = self.consts[self.r.below(self.consts.len() as u64) as usize].clone();
            return self.h.item_ref(&n, c);
        }
        self.literal()
    }

    fn assignable(&mut self, cx: &Cx) -> Option<BinderId> {
        let w: Vec<BinderId> = cx.vars.iter().filter(|v| v.1).map(|v| v.0).collect();
        if w.is_empty() {
            None
        } else {
            Some(self.r.pick(&w))
        }
    }

    // ------------------------------------------------------------ expressions

    fn op(&mut self) -> Op {
        let kinds = [
            OpKind::Add,
            OpKind::Sub,
            OpKind::Mul,
            OpKind::Div,
            OpKind::Rem,
            OpKind::FloorDiv,
            OpKind::FloorMod,
            OpKind::And,
            OpKind::Or,
            OpKind::Xor,
            OpKind::Shl,
            OpKind::Shr,
            OpKind::Pow,
            OpKind::Eq,
            OpKind::Ne,
            OpKind::Lt,
            OpKind::Le,
            OpKind::Gt,
            OpKind::Ge,
            OpKind::Min,
            OpKind::Max,
        ];
        let k = self.r.pick(&kinds);
        self.policy(Op::new(k))
    }

    fn policy(&mut self, op: Op) -> Op {
        let mut op = op;
        if op.policy.overflow.is_some() {
            let o = self.r.pick(&[
                Overflow::Error,
                Overflow::Wrap,
                Overflow::Promote,
                Overflow::Promote,
                Overflow::Error,
                Overflow::Trap,
            ]);
            op = op.with_overflow(o);
        }
        if op.policy.div_zero.is_some() {
            let d = if self.r.chance(10) {
                DivZero::Trap
            } else {
                DivZero::Error
            };
            op = op.with_div_zero(d);
        }
        if op.policy.shift.is_some() {
            let s = self.r.pick(&[Shift::Mask, Shift::Error, Shift::Saturate]);
            op = op.with_shift(s);
        }
        op
    }

    fn expr(&mut self, cx: &Cx, d: u32) -> ExprId {
        if d == 0 || self.fuel == 0 {
            return self.leaf(cx);
        }
        self.fuel -= 1;
        let d1 = d - 1;
        match self.r.below(40) {
            30 => self.method_call(cx, d1),
            31 => self.record(cx, d1),
            32 => self.labeled_block(cx, d1),
            33 => {
                let v = self.expr(cx, d1);
                let n = self.h.int(self.r.below(4) as i64 - 1);
                self.h.expr(hir_lang::Expr::Repeat { elem: v, count: n })
            }
            34 => self.foreach(cx, d1),
            35 => self.recursive_closure(cx, d1),
            36 => self.ref_forms(cx, d1),
            37 => self.more_ops(cx, d1),
            38 => {
                // A dynamic property read or method call.
                let b = self.leaf(cx);
                let k = self.literal();
                if self.r.chance(50) {
                    self.h.expr(hir_lang::Expr::DynField { base: b, name: k })
                } else {
                    let args = self.h.b.list(&[]);
                    self.h.expr(hir_lang::Expr::DynMethodCall {
                        receiver: b,
                        name: k,
                        args,
                    })
                }
            }
            0..=4 => {
                let op = self.op();
                let a = self.expr(cx, d1);
                let b = self.expr(cx, d1);
                self.h.op_with(op, &[a, b])
            }
            5 => {
                let k = self.r.pick(&[
                    OpKind::Neg,
                    OpKind::Not,
                    OpKind::BitNot,
                    OpKind::Abs,
                    OpKind::Sqrt,
                    OpKind::Floor,
                    OpKind::Round,
                ]);
                let op = self.policy(Op::new(k));
                let a = self.expr(cx, d1);
                self.h.op_with(op, &[a])
            }
            6 => {
                let k = self.r.pick(&[
                    OpKind::IntCast(Prim::I8),
                    OpKind::IntCast(Prim::U8),
                    OpKind::IntCast(Prim::I32),
                    OpKind::IntToFloat(Prim::F64),
                    OpKind::F64ToF32,
                    OpKind::BoolToInt(Prim::I64),
                ]);
                let op = self.policy(Op::new(k));
                // `promote` is invalid where the result type is static.
                let op = if op.promotes() {
                    op.with_overflow(Overflow::Wrap)
                } else {
                    op
                };
                let a = self.expr(cx, d1);
                self.h.op_with(op, &[a])
            }
            7 | 8 => {
                let n = self.r.below(4);
                let es: Vec<ExprId> = (0..n).map(|_| self.expr(cx, d1)).collect();
                self.h.array(&es)
            }
            9 => {
                let n = self.r.below(4);
                let mut es = Vec::new();
                for _ in 0..n {
                    let k = if self.r.chance(80) {
                        Some(self.literal())
                    } else {
                        None
                    };
                    let v = self.expr(cx, d1);
                    es.push((k, v));
                }
                self.h.map(&es)
            }
            10 | 11 => {
                let b = if self.r.chance(45) {
                    let n = self.r.below(4) + 1;
                    let es: Vec<ExprId> = (0..n)
                        .map(|_| self.expr(cx, d1.saturating_sub(1)))
                        .collect();
                    self.h.array(&es)
                } else {
                    self.leaf(cx)
                };
                let k = if self.r.chance(80) {
                    self.small_int()
                } else {
                    self.literal()
                };
                self.h.index(b, k)
            }
            12 | 13 => self.call(cx, d1),
            14 => self.closure_call(cx, d1),
            15 => {
                let c = self.expr(cx, d1);
                let t = self.block_expr(cx, d1);
                let e = if self.r.chance(60) {
                    Some(self.block_expr(cx, d1))
                } else {
                    None
                };
                self.h.if_(c, t, e)
            }
            16 => self.match_expr(cx, d1),
            17 => {
                let name = self.r.pick(&["concat", "len", "truthy", "lnot", "type_of"]);
                if name == "concat" {
                    let a = self.expr(cx, d1);
                    let b = self.expr(cx, d1);
                    self.h.intrinsic(name, &[a, b])
                } else {
                    let a = self.expr(cx, d1);
                    self.h.intrinsic(name, &[a])
                }
            }
            18 => self.try_expr(cx, d1),
            19 => self.block_expr(cx, d1),
            20 => self.loop_expr(cx, d1),
            21 | 22 => self.assign(cx, d1),
            23 => self.jump(cx, d1),
            24 if cx.can_throw => {
                let v = self.expr(cx, d1);
                self.h.throw(v)
            }
            25 => {
                let ty = match self.r.below(7) {
                    0 => Ty::Prim(Prim::I64),
                    1 => Ty::Prim(Prim::U8),
                    2 => Ty::Prim(Prim::F64),
                    3 => Ty::Prim(Prim::Bool),
                    4 => Ty::Prim(Prim::Char),
                    5 => Ty::Prim(Prim::Str),
                    _ => Ty::Any,
                };
                let ty = self.h.ty(ty);
                let ty = if self.r.chance(20) {
                    self.h.ty(Ty::Nullable(ty))
                } else {
                    ty
                };
                let v = self.expr(cx, d1);
                let over = if self.r.chance(50) {
                    Overflow::Wrap
                } else {
                    Overflow::Error
                };
                let pol = hir_lang::Policy::CAST.with_overflow(over);
                self.h.expr(hir_lang::Expr::Cast {
                    expr: v,
                    ty,
                    policy: pol,
                })
            }
            26 => {
                // A host call.
                let e = self.h.extern_ref("echo");
                let a = self.expr(cx, d1);
                self.h.call(e, &[a])
            }
            _ => self.leaf(cx),
        }
    }

    fn block_expr(&mut self, cx: &Cx, d: u32) -> ExprId {
        let mut inner = cx.clone();
        self.block(&mut inner, d, true)
    }

    fn block(&mut self, cx: &mut Cx, d: u32, tail: bool) -> ExprId {
        let n = self.r.below(4);
        let mut stmts = Vec::new();
        for _ in 0..n {
            if let Some(s) = self.stmt(cx, d) {
                stmts.push(s);
            }
        }
        let t = if tail && self.r.chance(80) {
            Some(self.expr(cx, d))
        } else {
            None
        };
        // Observe the variables at the end, sometimes.
        let t = if t.is_some() && !cx.vars.is_empty() && self.r.chance(30) {
            let bs: Vec<BinderId> = cx.vars.iter().take(4).map(|v| v.0).collect();
            let mut all: Vec<ExprId> = bs.into_iter().map(|b| self.h.var(b)).collect();
            all.extend(t);
            Some(self.h.array(&all))
        } else {
            t
        };
        self.h.block(&stmts, t)
    }

    fn stmt(&mut self, cx: &mut Cx, d: u32) -> Option<StmtId> {
        match self.r.below(10) {
            0..=3 => {
                let init = self.expr(cx, d);
                let init = self.guard(cx, init, 35);
                let b = self.local();
                let s = self.h.let_(b, Some(init));
                cx.vars.push((b, true));
                Some(s)
            }
            4 => {
                // let (a, b) = [x, y]: destructuring (sometimes of a non-pair).
                let x = self.expr(cx, d.saturating_sub(1));
                let init = if self.r.chance(85) {
                    let y = self.expr(cx, d.saturating_sub(1));
                    self.h.array(&[x, y])
                } else {
                    x
                };
                let (a, b) = (self.local(), self.local());
                let pa = self.h.pbind(a);
                let pb = self.h.pbind(b);
                let elems = self.h.b.list(&[pa, pb]);
                let pat = self.h.pat(Pat::Tuple { elems, rest: None });
                let s = self.h.let_pat(pat, init, None);
                cx.vars.push((a, true));
                cx.vars.push((b, true));
                Some(s)
            }
            6 if cx.in_fn && self.r.chance(25) => {
                // static s = lit; (a per-statement variable kept across calls)
                let b = self.local();
                let init = self.literal();
                let s = self.h.raw_stmt(hir_lang::Stmt::Static {
                    binder: b,
                    ty: None,
                    init: Some(init),
                });
                cx.vars.push((b, true));
                self.aliases.push(b);
                Some(s)
            }
            7 if !self.globals.is_empty() && self.r.chance(25) => {
                // global G as g;
                let (gi, gname) =
                    self.globals[self.r.below(self.globals.len() as u64) as usize].clone();
                let b = self.local();
                let d = self.h.b.def(hir_lang::Def::Item(gi));
                let p = self.h.path(&gname, hir_lang::Res::Def(d));
                let s = self
                    .h
                    .raw_stmt(hir_lang::Stmt::Global { binder: b, path: p });
                cx.vars.push((b, true));
                self.aliases.push(b);
                Some(s)
            }
            5 if self.r.chance(30) => {
                // defer echo(..): no jumps inside.
                let e = self.h.extern_ref("echo");
                let a = self.literal();
                let c = self.h.call(e, &[a]);
                Some(self.h.raw_stmt(hir_lang::Stmt::Defer(c)))
            }
            _ => {
                let e = self.expr(cx, d);
                let e = self.guard(cx, e, 45);
                Some(self.h.stmt(e))
            }
        }
    }

    /// Often wraps `e` in a catch-all, so a runtime error does not end the
    /// program.
    fn guard(&mut self, cx: &Cx, e: ExprId, percent: u64) -> ExprId {
        if !cx.can_throw || !self.r.chance(percent) {
            return e;
        }
        let v = self.local();
        let p = self.h.pbind(v);
        let r = self.literal();
        let arm = Arm {
            pat: p,
            guard: None,
            body: r,
        };
        self.h.try_(e, &[arm], None)
    }

    fn assign(&mut self, cx: &Cx, d: u32) -> ExprId {
        let Some(b) = self.assignable(cx) else {
            return self.leaf(cx);
        };
        let base = self.h.var(b);
        let shape = self.r.below(6);
        let target = match shape {
            0 | 1 => base,
            2 => {
                let k = self.small_int();
                self.h.index(base, k)
            }
            3 => {
                let k1 = if self.r.chance(50) {
                    self.small_int()
                } else {
                    self.literal()
                };
                let i1 = self.h.index(base, k1);
                let k2 = self.small_int();
                self.h.index(i1, k2)
            }
            4 => self.h.append(base),
            _ => {
                let k = self.small_int();
                let i1 = self.h.index(base, k);
                self.h.append(i1)
            }
        };
        let v = self.expr(cx, d);
        if (2..4).contains(&shape) && self.r.chance(40) {
            // let_place p = target in p = op(p, v) (or concat): the place's
            // operands evaluated once.
            let n = self.fresh("p");
            let p = self.h.place_binder(&n);
            let vp = self.h.var(p);
            let combined = if self.r.chance(30) {
                self.h.intrinsic("concat", &[vp, v])
            } else {
                let k = self
                    .r
                    .pick(&[OpKind::Add, OpKind::Sub, OpKind::Pow, OpKind::Or]);
                let op = self.policy(Op::new(k));
                self.h.op_with(op, &[vp, v])
            };
            let tp = self.h.var(p);
            let body = self.h.assign(tp, combined);
            return self.h.let_place(p, target, body);
        }
        if shape < 4 && self.r.chance(30) {
            let k = self.r.pick(&[
                OpKind::Add,
                OpKind::Sub,
                OpKind::Mul,
                OpKind::Rem,
                OpKind::Or,
            ]);
            let op = self.policy(Op::new(k));
            self.h.compound(target, op, v)
        } else {
            self.h.assign(target, v)
        }
    }

    fn jump(&mut self, cx: &Cx, d: u32) -> ExprId {
        if !cx.loops.is_empty() && self.r.chance(70) {
            let target = cx.loops[self.r.below(cx.loops.len() as u64) as usize];
            // Unlabeled jumps go to the innermost loop.
            let label = if self.r.chance(50) { target } else { None };
            if self.r.chance(50) {
                let v = if self.r.chance(50) {
                    Some(self.expr(cx, d))
                } else {
                    None
                };
                return self.h.brk(label, v);
            }
            return self.h.cont(label);
        }
        if cx.in_fn {
            let v = if self.r.chance(80) {
                Some(self.expr(cx, d))
            } else {
                None
            };
            return self.h.ret(v);
        }
        self.leaf(cx)
    }

    fn loop_expr(&mut self, cx: &Cx, d: u32) -> ExprId {
        // { let i = 0; 'l: loop [step: i = i + 1] { if i >= N { break }; body } }
        let i = self.local();
        let zero = self.h.int(0);
        let li = self.h.let_(i, Some(zero));
        let label = if self.r.chance(50) {
            let n = self.fresh("l");
            Some(self.h.label(&n))
        } else {
            None
        };
        let mut inner = cx.clone();
        inner.vars.push((i, false));
        inner.loops.push(label);
        let vi = self.h.var(i);
        let n = self.r.below(5) as i64;
        let lim = self.h.int(n);
        let ge = self.h.op(OpKind::Ge, &[vi, lim]);
        let bv = if self.r.chance(50) {
            Some(self.expr(&inner, d.saturating_sub(1)))
        } else {
            None
        };
        let brk = self.h.brk(None, bv);
        let bb = self.h.block(&[], Some(brk));
        let guard = self.h.if_(ge, bb, None);
        let gs = self.h.stmt(guard);
        let body = {
            let mut b = inner.clone();
            let stmts_n = self.r.below(3) + 1;
            let mut stmts = vec![gs];
            for _ in 0..stmts_n {
                if let Some(s) = self.stmt(&mut b, d) {
                    stmts.push(s);
                }
            }
            self.h.block(&stmts, None)
        };
        let ti = self.h.var(i);
        let vi2 = self.h.var(i);
        let one = self.h.int(1);
        let inc = self.h.op(OpKind::Add, &[vi2, one]);
        let step = self.h.assign(ti, inc);
        let lp = self.h.loop_(label, body, Some(step));
        self.h.block(&[li], Some(lp))
    }

    fn match_expr(&mut self, cx: &Cx, d: u32) -> ExprId {
        let s = self.expr(cx, d);
        let mut arms = Vec::new();
        for _ in 0..(self.r.below(3) + 1) {
            let mut inner = cx.clone();
            let p = self.pattern(&mut inner, 2);
            let g = if self.r.chance(25) {
                Some(self.expr(&inner, d.saturating_sub(1)))
            } else {
                None
            };
            let body = self.expr(&inner, d);
            arms.push(Arm {
                pat: p,
                guard: g,
                body,
            });
        }
        self.h.match_(s, &arms)
    }

    fn pattern(&mut self, cx: &mut Cx, d: u32) -> PatId {
        match self.r.below(if d == 0 { 4 } else { 11 }) {
            0 => self.h.pat(Pat::Wild),
            1 => {
                let b = self.local();
                cx.vars.push((b, true));
                self.h.pbind(b)
            }
            2 => {
                let lit = match self.r.below(4) {
                    0 => Lit::Int(hir_lang::IntLit::signed(self.r.pick(INTS))),
                    1 => Lit::Bool(self.r.chance(50)),
                    2 => Lit::Null,
                    _ => {
                        let t = self.r.pick(STRS);
                        let t = self.h.b.text(t);
                        Lit::Str(t)
                    }
                };
                self.h.pat(Pat::Lit(lit))
            }
            3 => {
                let lo = self.r.below(5) as i64 - 2;
                let hi = lo + self.r.below(5) as i64;
                let l = self.h.pat(Pat::Lit(Lit::Int(hir_lang::IntLit::signed(lo))));
                let hh = self.h.pat(Pat::Lit(Lit::Int(hir_lang::IntLit::signed(hi))));
                let inclusive = self.r.chance(50);
                self.h.pat(Pat::Range {
                    lo: Some(l),
                    hi: Some(hh),
                    inclusive,
                })
            }
            4 | 5 => {
                let n = self.r.below(3);
                let es: Vec<PatId> = (0..n).map(|_| self.pattern(cx, d - 1)).collect();
                let elems = self.h.b.list(&es);
                let rest = if self.r.chance(25) {
                    Some(self.r.below(n + 1) as u32)
                } else {
                    None
                };
                self.h.pat(Pat::Tuple { elems, rest })
            }
            6 => {
                // Alternatives that bind nothing (they must bind one set).
                let a = self.pattern_nobind();
                let b = self.pattern_nobind();
                let l = self.h.b.list(&[a, b]);
                self.h.pat(Pat::Or(l))
            }
            7 => {
                let prims = [Prim::I64, Prim::F64, Prim::Str, Prim::Bool, Prim::Char];
                let p = self.r.pick(&prims);
                let ty = self.h.ty(Ty::Prim(p));
                let ty = if self.r.chance(30) {
                    // A union of two primitives (canonicalized by `finish`).
                    let q = self.r.pick(&prims);
                    let other = self.h.ty(Ty::Prim(q));
                    let members = self.h.b.list(&[ty, other]);
                    self.h.ty(Ty::Union(members))
                } else {
                    ty
                };
                let ty = if self.r.chance(25) {
                    self.h.ty(Ty::Nullable(ty))
                } else {
                    ty
                };
                let sub = if self.r.chance(30) {
                    Some(self.pattern(cx, d - 1))
                } else {
                    None
                };
                self.h.pat(Pat::TypeTest { ty, pat: sub })
            }
            8 => {
                // [a, ..rest, z]
                let n = self.r.below(2) + 1;
                let prefix: Vec<PatId> = (0..n).map(|_| self.pattern(cx, d - 1)).collect();
                let prefix = self.h.b.list(&prefix);
                let bind = if self.r.chance(60) {
                    let b = self.local();
                    cx.vars.push((b, true));
                    Some(self.h.pbind(b))
                } else {
                    None
                };
                let m = self.r.below(2);
                let suffix: Vec<PatId> = (0..m).map(|_| self.pattern(cx, d - 1)).collect();
                let suffix = self.h.b.list(&suffix);
                self.h.pat(Pat::Slice {
                    prefix,
                    rest: Some(hir_lang::SliceRest { bind, suffix }),
                })
            }
            9 => {
                // { k: p, .. } over string keys
                let n = self.r.below(3);
                let mut fields = Vec::new();
                let keys = ["k", "a", "b"];
                for k in keys.iter().take(n as usize) {
                    let name = self.h.ident(k);
                    let pat = self.pattern(cx, d - 1);
                    fields.push(hir_lang::FieldPat { name, pat });
                }
                let fields = self.h.b.list(&fields);
                let rest = self.r.chance(50);
                self.h.pat(Pat::Record {
                    path: None,
                    fields,
                    rest,
                })
            }
            _ => {
                // A bare identifier: a constant's value, or a new binding.
                let b = self.local();
                if !self.consts.is_empty() && self.r.chance(50) {
                    let (ci, cname) =
                        self.consts[self.r.below(self.consts.len() as u64) as usize].clone();
                    let def = self.h.b.def(hir_lang::Def::Item(ci));
                    let path =
                        self.h
                            .path_ns(&cname, hir_lang::Ns::Pattern, hir_lang::Res::Def(def));
                    self.h.pat(Pat::Ident { binder: b, path })
                } else {
                    let n = self.fresh("id");
                    let path = self
                        .h
                        .path_ns(&n, hir_lang::Ns::Pattern, hir_lang::Res::Unresolved);
                    cx.vars.push((b, true));
                    self.h.pat(Pat::Ident { binder: b, path })
                }
            }
        }
    }

    fn pattern_nobind(&mut self) -> PatId {
        match self.r.below(3) {
            0 => self.h.pat(Pat::Wild),
            1 => self.lit_pat(),
            _ => self.range_pat(),
        }
    }

    fn lit_pat(&mut self) -> PatId {
        let lit = match self.r.below(4) {
            0 => Lit::Int(hir_lang::IntLit::signed(self.r.pick(INTS))),
            1 => Lit::Bool(self.r.chance(50)),
            2 => Lit::Null,
            _ => {
                let t = self.r.pick(STRS);
                let t = self.h.b.text(t);
                Lit::Str(t)
            }
        };
        self.h.pat(Pat::Lit(lit))
    }

    fn range_pat(&mut self) -> PatId {
        let lo = self.r.below(5) as i64 - 2;
        let hi = lo + self.r.below(5) as i64;
        let l = self.h.pat(Pat::Lit(Lit::Int(hir_lang::IntLit::signed(lo))));
        let hh = self.h.pat(Pat::Lit(Lit::Int(hir_lang::IntLit::signed(hi))));
        let inclusive = self.r.chance(50);
        self.h.pat(Pat::Range {
            lo: Some(l),
            hi: Some(hh),
            inclusive,
        })
    }

    fn try_expr(&mut self, cx: &Cx, d: u32) -> ExprId {
        let body = self.block_expr(cx, d);
        let mut arms = Vec::new();
        for _ in 0..self.r.below(3) {
            let mut inner = cx.clone();
            let p = if self.r.chance(60) {
                let b = self.local();
                inner.vars.push((b, true));
                self.h.pbind(b)
            } else {
                self.pattern(&mut inner, 1)
            };
            let body = self.expr(&inner, d);
            arms.push(Arm {
                pat: p,
                guard: None,
                body,
            });
        }
        let fin = if arms.is_empty() || self.r.chance(40) {
            Some(self.block_expr(cx, d.saturating_sub(1)))
        } else {
            None
        };
        self.h.try_(body, &arms, fin)
    }

    // ------------------------------------------------------------ more forms

    /// `{ let o = {"k": v, "m": closure(self, x) => body}; o.m(arg) }`
    fn method_call(&mut self, cx: &Cx, d: u32) -> ExprId {
        let k = self.h.str("k");
        let kv = self.expr(cx, d);
        let mut inner = Cx {
            vars: cx.vars.clone(),
            loops: Vec::new(),
            in_fn: true,
            can_throw: true,
        };
        let (ps, sb) = self.h.param("self", ParamKind::Normal, None, false);
        let (px, xb) = self.h.param("x", ParamKind::Normal, None, false);
        inner.vars.push((sb, true));
        inner.vars.push((xb, true));
        let body = if self.r.chance(50) {
            let vs = self.h.var(sb);
            let k2 = self.h.str("k");
            let field = self.h.index(vs, k2);
            let vx = self.h.var(xb);
            let op = self.policy(Op::new(OpKind::Add));
            self.h.op_with(op, &[field, vx])
        } else {
            self.block(&mut inner, d, true)
        };
        let clo = self.h.closure(
            &[ps, px],
            body,
            Some(CaptureMode::ByRef),
            &[],
            None,
            DefaultEval::PerCall,
        );
        let mk = self.h.str("m");
        let map = self.h.map(&[(Some(k), kv), (Some(mk), clo)]);
        let o = self.local();
        let lo = self.h.let_(o, Some(map));
        let vo = self.h.var(o);
        let arg = self.expr(cx, d);
        let name = if self.r.chance(85) { "m" } else { "missing" };
        let call = self.h.method(vo, name, &[arg]);
        self.h.block(&[lo], Some(call))
    }

    /// `{ k: e, a: e, ..base }` (an anonymous record: a map).
    fn record(&mut self, cx: &Cx, d: u32) -> ExprId {
        let n = self.r.below(3);
        let mut fields = Vec::new();
        for k in ["k", "a", "b"].iter().take(n as usize) {
            let name = self.h.ident(k);
            let value = self.expr(cx, d);
            fields.push(hir_lang::FieldInit { name, value });
        }
        let fields = self.h.b.list(&fields);
        let base = if self.r.chance(35) {
            Some(self.expr(cx, d))
        } else {
            None
        };
        self.h.expr(hir_lang::Expr::Record {
            path: None,
            fields,
            base,
        })
    }

    /// `'b: { if c { break 'b v }; stmt; tail }`
    fn labeled_block(&mut self, cx: &Cx, d: u32) -> ExprId {
        let n = self.fresh("b");
        let label = self.h.label(&n);
        let mut inner = cx.clone();
        let c = self.expr(&inner, d);
        let v = if self.r.chance(70) {
            Some(self.expr(&inner, d))
        } else {
            None
        };
        let brk = self.h.brk(Some(label), v);
        let bb = self.h.block(&[], Some(brk));
        let iff = self.h.if_(c, bb, None);
        let s1 = self.h.stmt(iff);
        let mut stmts = vec![s1];
        if let Some(st) = self.stmt(&mut inner, d) {
            stmts.push(st);
        }
        let tail = if self.r.chance(70) {
            Some(self.expr(&inner, d))
        } else {
            None
        };
        self.h.labeled_block(label, &stmts, tail)
    }

    /// `foreach (coll as k => v) { body }`, lowered with the iteration
    /// intrinsics as HIR spec section 9.4 does.
    fn foreach(&mut self, cx: &Cx, d: u32) -> ExprId {
        let coll = if self.r.chance(60) {
            let n = self.r.below(4);
            let es: Vec<ExprId> = (0..n).map(|_| self.expr(cx, d.saturating_sub(1))).collect();
            self.h.array(&es)
        } else {
            self.leaf(cx)
        };
        let it = self.local();
        let iter = self.h.intrinsic("iter", &[coll]);
        let lit = self.h.let_(it, Some(iter));
        let vit = self.h.var(it);
        let next = self.h.intrinsic("iter_next", &[vit]);
        let null = self.h.pat(Pat::Lit(Lit::Null));
        let brk = self.h.brk(None, None);
        let a1 = Arm {
            pat: null,
            guard: None,
            body: brk,
        };
        let (kb, vb) = (self.local(), self.local());
        let mut inner = cx.clone();
        inner.loops.push(None);
        inner.vars.push((kb, true));
        inner.vars.push((vb, true));
        let pk = self.h.pbind(kb);
        let pv = self.h.pbind(vb);
        let elems = self.h.b.list(&[pk, pv]);
        let tup = self.h.pat(Pat::Tuple { elems, rest: None });
        let body = self.block(&mut inner, d, false);
        let a2 = Arm {
            pat: tup,
            guard: None,
            body,
        };
        let m = self.h.match_(next, &[a1, a2]);
        let lp = self.h.loop_(None, m, None);
        self.h.block(&[lit], Some(lp))
    }

    /// `{ let f = closure self=me (n) => if n <= 0 { e } else { me(n - 1) op k }; f(N) }`
    fn recursive_closure(&mut self, cx: &Cx, d: u32) -> ExprId {
        let me = self.h.self_binder("me");
        let (pn, n) = self.h.param("n", ParamKind::Normal, None, false);
        let mut inner = Cx {
            vars: cx.vars.clone(),
            loops: Vec::new(),
            in_fn: true,
            can_throw: true,
        };
        inner.vars.push((n, false));
        let vn = self.h.var(n);
        let z = self.h.int(0);
        let le = self.h.op(OpKind::Le, &[vn, z]);
        let base = self.expr(&inner, d);
        let vme = self.h.var(me);
        let vn2 = self.h.var(n);
        let one = self.h.int(1);
        let dec = self.h.op(OpKind::Sub, &[vn2, one]);
        let rec = self.h.call(vme, &[dec]);
        let k = self.expr(&inner, d.saturating_sub(1));
        let kind = self.r.pick(&[OpKind::Add, OpKind::Mul, OpKind::Sub]);
        let op = self.policy(Op::new(kind));
        let comb = self.h.op_with(op, &[rec, k]);
        let ife = self.h.if_(le, base, Some(comb));
        let clo = self.h.closure(
            &[pn],
            ife,
            Some(CaptureMode::ByRef),
            &[],
            Some(me),
            DefaultEval::PerCall,
        );
        let f = self.local();
        let lf = self.h.let_(f, Some(clo));
        let vf = self.h.var(f);
        let arg = self.h.int(self.r.below(6) as i64);
        let call = self.h.call(vf, &[arg]);
        self.h.block(&[lf], Some(call))
    }

    /// Reference forms: `t = &s`, and a by-reference call
    /// `{ let r = closure(&p) => p = p + v; r(&x); x }`.
    fn ref_forms(&mut self, cx: &Cx, d: u32) -> ExprId {
        let w: Vec<BinderId> = cx.vars.iter().filter(|v| v.1).map(|v| v.0).collect();
        let targets: Vec<BinderId> = w
            .iter()
            .copied()
            .filter(|b| !self.aliases.contains(b))
            .collect();
        if !targets.is_empty() && w.len() >= 2 && self.r.chance(40) {
            let t = targets[0];
            let s = if w[0] == t { w[1] } else { w[0] };
            let vt = self.h.var(t);
            let vs = self.h.var(s);
            return self.h.expr(hir_lang::Expr::RefAssign {
                target: vt,
                source: vs,
            });
        }
        let Some(x) = self.assignable(cx) else {
            return self.leaf(cx);
        };
        let (pp, pb) = self.h.param("p", ParamKind::Normal, None, true);
        let mut inner = Cx {
            vars: cx.vars.clone(),
            loops: Vec::new(),
            in_fn: true,
            can_throw: true,
        };
        inner.vars.push((pb, true));
        let tp = self.h.var(pb);
        let vp = self.h.var(pb);
        let v = self.expr(&inner, d);
        let op = self.policy(Op::new(OpKind::Add));
        let sum = self.h.op_with(op, &[vp, v]);
        let body = self.h.assign(tp, sum);
        let clo = self.h.closure(
            &[pp],
            body,
            Some(CaptureMode::ByRef),
            &[],
            None,
            DefaultEval::PerCall,
        );
        let r = self.local();
        let lr = self.h.let_(r, Some(clo));
        let vr = self.h.var(r);
        let vx = self.h.var(x);
        let call = self.h.call_args(
            vr,
            &[Arg {
                kind: ArgKind::Positional,
                value: vx,
                place: true,
            }],
        );
        let s = self.h.stmt(call);
        let vx2 = self.h.var(x);
        self.h.block(&[lr, s], Some(vx2))
    }

    fn more_ops(&mut self, cx: &Cx, d: u32) -> ExprId {
        let k = self.r.pick(&[
            OpKind::Ceil,
            OpKind::Trunc,
            OpKind::RoundEven,
            OpKind::TotalCmp,
            OpKind::Fma,
            OpKind::FloatToInt(Prim::I32),
            OpKind::FloatToInt(Prim::U8),
            OpKind::Narrow(Prim::I8),
            OpKind::Narrow(Prim::U16),
            OpKind::Bitcast(Prim::I64),
            OpKind::Bitcast(Prim::F64),
            OpKind::CharFromU32,
            OpKind::Zext(Prim::U64),
            OpKind::Sext(Prim::I64),
            OpKind::F32ToF64,
        ]);
        let mut op = self.policy(Op::new(k));
        if op.policy.float_to_int.is_some() && self.r.chance(50) {
            op = op.with_float_to_int(hir_lang::FloatToInt::Saturate);
        }
        let args: Vec<ExprId> = (0..k.arity()).map(|_| self.expr(cx, d)).collect();
        self.h.op_with(op, &args)
    }

    // ------------------------------------------------------------ calls

    fn call(&mut self, cx: &Cx, d: u32) -> ExprId {
        if self.fns.is_empty() {
            return self.leaf(cx);
        }
        let f = self.fns[self.r.below(self.fns.len() as u64) as usize].clone();
        let mut args = Vec::new();
        let wrong = self.r.chance(8);
        let spread = self.r.chance(15);
        if spread {
            let es: Vec<ExprId> = (0..self.r.below(3)).map(|_| self.expr(cx, d)).collect();
            let arr = self.h.array(&es);
            args.push(Arg {
                kind: ArgKind::Spread,
                value: arr,
                place: false,
            });
        }
        for (k, has_default, name) in &f.params {
            let skip = *has_default && self.r.chance(40);
            if skip && !wrong {
                continue;
            }
            match k {
                ParamKind::Normal | ParamKind::Rest if spread => {}
                ParamKind::Normal if !self.r.chance(20) => {
                    let v = self.expr(cx, d);
                    args.push(Arg::positional(v));
                }
                ParamKind::Normal | ParamKind::NamedOnly => {
                    let v = self.expr(cx, d);
                    let a = self.h.named(name, v);
                    args.push(a);
                }
                ParamKind::Rest => {
                    for _ in 0..self.r.below(3) {
                        let v = self.expr(cx, d);
                        args.push(Arg::positional(v));
                    }
                }
                _ => {}
            }
        }
        if wrong {
            let v = self.expr(cx, d);
            args.push(Arg::positional(v));
        }
        if self.r.chance(30) {
            // Through a function value: a dynamic call.
            let fv = self.h.item_ref(&f.name, f.item);
            let tmp = self.local();
            let l = self.h.let_(tmp, Some(fv));
            let callee = self.h.var(tmp);
            let call = self.h.call_args(callee, &args);
            return self.h.block(&[l], Some(call));
        }
        let c = self.h.item_ref(&f.name, f.item);
        self.h.call_args(c, &args)
    }

    fn closure_call(&mut self, cx: &Cx, d: u32) -> ExprId {
        let mut inner = Cx {
            vars: Vec::new(),
            loops: Vec::new(),
            in_fn: true,
            can_throw: true,
        };
        let mode = self.r.pick(&[CaptureMode::ByRef, CaptureMode::ByValue]);
        // Implicit captures: outer variables stay readable inside.
        for &(b, w) in &cx.vars {
            inner.vars.push((b, w));
        }
        let mut captures = Vec::new();
        if let Some(&(ob, _)) = cx.vars.first() {
            if self.r.chance(40) {
                let n = self.fresh("c");
                let cm = self.r.pick(&[CaptureMode::ByRef, CaptureMode::ByValue]);
                let (c, b) = self.h.capture(ob, &n, cm);
                captures.push(c);
                inner.vars.push((b, true));
            }
        }
        let mut params = Vec::new();
        let np = self.r.below(3);
        for _ in 0..np {
            let pname = self.fresh("q");
            let default = if self.r.chance(30) {
                Some(self.literal())
            } else {
                None
            };
            let (p, b) = self.h.param(&pname, ParamKind::Normal, default, false);
            params.push(p);
            inner.vars.push((b, true));
        }
        let body = self.block(&mut inner, d, true);
        let clo = self.h.closure(
            &params,
            body,
            Some(mode),
            &captures,
            None,
            DefaultEval::PerCall,
        );
        let tmp = self.local();
        let l = self.h.let_(tmp, Some(clo));
        let n = if self.r.chance(80) {
            np
        } else {
            self.r.below(np + 2)
        };
        let args: Vec<ExprId> = (0..n).map(|_| self.expr(cx, d)).collect();
        let callee = self.h.var(tmp);
        let call = self.h.call(callee, &args);
        self.h.block(&[l], Some(call))
    }
}

/// The program for `seed`.
pub fn program(seed: u64) -> (Hir, Interner) {
    Gen::new(seed).program()
}
