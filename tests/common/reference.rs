//! The reference HIR interpreter: the differential oracle.
//!
//! A direct tree-walking evaluator of the dynamic semantics bcgen-lang
//! documents, written independently of the compiler: PHP arrays are real
//! values (deep-copied on every store, not copy-on-write), OPS arithmetic is
//! computed in `i128` and `f64`, and control flow is Rust `Result` signals.
//! It is deliberately simple and recursive (it only runs generated test
//! programs of bounded size).

#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use hir_lang::{
    Arg, ArgKind, BindMode, BinderId, Block, CaptureMode, DefaultEval, Expr, ExprId, Hir,
    Intrinsic, ItemId, ItemKind, Lit, Member, NodeRef, Op, OpKind, Overflow, ParamId, ParamKind,
    Pat, PatId, Prim, Res, Stmt, StmtId, Ty, TyId,
};
use intern_lang::Interner;

use super::{Outcome, RV};

pub type Cell = Rc<RefCell<V>>;

#[derive(Clone, Debug)]
pub enum V {
    Nil,
    Bool(bool),
    Int(i64),
    Float(f64),
    Char(char),
    Str(Rc<Vec<u8>>),
    Map(Rc<RefCell<MapData>>),
    Func(Rc<Func>),
    Error(u32, NodeRef),
    Iter(Rc<RefCell<IterState>>),
}

#[derive(Debug)]
pub enum Func {
    Item(ItemId),
    Closure {
        e: ExprId,
        /// Shared variables (by reference) and captured values.
        caps: Vec<(BinderId, Captured)>,
        once: Vec<Option<V>>,
    },
}

#[derive(Debug, Clone)]
pub enum Captured {
    Value(V),
    Shared(Cell),
    Global(Cell),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Key {
    Nil,
    Bool(bool),
    Int(i64),
    Float(u64),
    Char(char),
    Str(Vec<u8>),
}

#[derive(Clone, Debug, Default)]
pub struct MapData {
    pub entries: Vec<(Key, V)>,
    /// The largest integer key ever inserted (`None`: none yet).
    pub next: Option<i64>,
}

#[derive(Debug)]
pub struct IterState {
    /// Snapshot (PHP) or the live map.
    pub map: Rc<RefCell<MapData>>,
    pub pos: usize,
}

/// An exception in flight.
#[derive(Clone, Debug)]
pub enum Exc {
    Error { code: u32, node: NodeRef },
    Value { v: V, node: NodeRef },
}

pub enum Sig {
    Break(Option<BinderId>, V),
    Continue(Option<BinderId>),
    Return(V),
    Throw(Exc),
    Trap(u32, NodeRef),
    /// The program did something whose result the semantics leave open
    /// (identity of copied arrays); the case is discarded.
    Unspecified,
    Budget,
}

type R<T> = Result<T, Sig>;

pub const TYPE_ERROR: u32 = 100;
pub const KEY_NOT_FOUND: u32 = 103;
pub const INDEX_OOB: u32 = 102;
pub const UNDEFINED_PROPERTY: u32 = 104;
pub const ARITH_OVERFLOW: u32 = 1;
pub const DIV_BY_ZERO: u32 = 2;
pub const SHIFT: u32 = 3;
pub const INVALID_CONV: u32 = 4;
pub const INVALID_CHAR: u32 = 5;
pub const NULL_REF: u32 = 101;
pub const NEG_EXPONENT: u32 = 6;
pub const ARG_ERROR: u32 = 114;
pub const NO_MATCH: u32 = 200;

#[derive(Clone, Copy)]
pub struct Config {
    pub php_arrays: bool,
    pub php_keys: bool,
    pub max_steps: u64,
}

pub struct Interp<'h> {
    hir: &'h Hir,
    names: &'h Interner,
    cfg: Config,
    globals: HashMap<ItemId, Cell>,
    statics: HashMap<StmtId, (Cell, bool)>,
    once: HashMap<(ItemId, usize), V>,
    pub out: Vec<String>,
    steps: u64,
    depth: usize,
    /// `let_place` aliases in scope (saved and restored around each body).
    aliases: HashMap<BinderId, PlaceRef>,
}

type Env = HashMap<BinderId, Cell>;

/// Evaluated arguments, in order: (name for a named one, value).
type Args = Vec<(Option<Vec<u8>>, Av)>;

/// A place whose operands are evaluated (LSB/HIR `let_place`).
#[derive(Clone, Debug)]
pub struct PlaceRef {
    /// A variable root, looked up when the place is accessed.
    root_local: Option<BinderId>,
    /// A global root.
    root: Option<Cell>,
    /// A value root.
    root_val: Option<V>,
    steps: Vec<Step>,
    keys: Vec<V>,
}

fn cell(v: V) -> Cell {
    Rc::new(RefCell::new(v))
}

fn err<T>(code: u32, node: NodeRef) -> R<T> {
    Err(Sig::Throw(Exc::Error { code, node }))
}

impl<'h> Interp<'h> {
    pub fn new(hir: &'h Hir, names: &'h Interner, cfg: Config) -> Self {
        Interp {
            hir,
            names,
            cfg,
            globals: HashMap::new(),
            statics: HashMap::new(),
            once: HashMap::new(),
            out: Vec::new(),
            steps: 0,
            depth: 0,
            aliases: HashMap::new(),
        }
    }

    fn tick(&mut self) -> R<()> {
        self.steps += 1;
        if self.steps > self.cfg.max_steps {
            return Err(Sig::Budget);
        }
        Ok(())
    }

    fn text(&self, s: hir_lang::Symbol) -> String {
        self.names.resolve(s).unwrap_or("").to_string()
    }

    // ------------------------------------------------------------ values

    /// A copy for storing (PHP value semantics: a deep copy of arrays).
    fn copy(&self, v: &V) -> V {
        if !self.cfg.php_arrays {
            return v.clone();
        }
        deep_copy(v)
    }

    pub fn kind(v: &V) -> u32 {
        match v {
            V::Nil => 0,
            V::Bool(_) => 1,
            V::Int(_) => 2,
            V::Float(_) => 3,
            V::Char(_) => 4,
            V::Str(_) => 5,
            V::Map(_) => 7,
            V::Func(_) => 9,
            V::Iter(_) => 11,
            V::Error(..) => 12,
        }
    }

    fn truthy(v: &V) -> bool {
        match v {
            V::Nil => false,
            V::Bool(b) => *b,
            V::Int(i) => *i != 0,
            V::Float(f) => *f != 0.0,
            V::Str(s) => !s.is_empty(),
            V::Map(m) => !m.borrow().entries.is_empty(),
            _ => true,
        }
    }

    // ------------------------------------------------------------ running

    /// Runs the module: initializers, then the body; the body's value.
    pub fn run_module(&mut self) -> Outcome {
        let r = self.run_module_inner();
        match r {
            Ok(v) => Outcome::Value(to_rv(&v, 0)),
            Err(Sig::Throw(Exc::Error { code, node })) => Outcome::Raised { code, node },
            Err(Sig::Throw(Exc::Value { v, node })) => Outcome::Thrown {
                value: to_rv(&v, 0),
                node,
            },
            Err(Sig::Trap(code, node)) => Outcome::Trap { code, node },
            Err(Sig::Unspecified) => Outcome::Unspecified,
            Err(Sig::Budget) => Outcome::Budget,
            Err(Sig::Break(..) | Sig::Continue(_) | Sig::Return(_)) => Outcome::Unspecified,
        }
    }

    fn run_module_inner(&mut self) -> R<V> {
        let hir = self.hir;
        let root = hir.root();
        // Globals: literal initializers first (they are constants), then
        // computed ones and once-evaluated defaults in canonical order.
        let mut items: Vec<ItemId> = Vec::new();
        hir.walk_from(NodeRef::Item(root), |ev| {
            if let hir_lang::Event::Enter(NodeRef::Item(i)) = ev {
                items.push(i);
            }
            hir_lang::Control::Continue
        });
        for &i in &items {
            match hir.item(i).kind {
                ItemKind::Global { init, .. } | ItemKind::Const { value: init, .. } => {
                    let v = match init.map(|e| *hir.expr(e)) {
                        Some(Expr::Lit(l)) => self.lit(l),
                        _ => V::Nil,
                    };
                    let _ = self.globals.insert(i, cell(v));
                }
                _ => {}
            }
        }
        let mut env = Env::new();
        for &i in &items {
            match hir.item(i).kind {
                ItemKind::Global { init: Some(e), .. } | ItemKind::Const { value: Some(e), .. } => {
                    if matches!(hir.expr(e), Expr::Lit(_)) {
                        continue;
                    }
                    let v = self.eval(e, &mut env)?;
                    let v = self.copy(&v);
                    if let Some(c) = self.globals.get(&i) {
                        *c.borrow_mut() = v;
                    }
                }
                ItemKind::Fn(def) if def.defaults == DefaultEval::Once && def.body.is_some() => {
                    for (k, &p) in hir.list(def.params).iter().enumerate() {
                        if let Some(d) = hir.param(p).default {
                            let v = self.eval(d, &mut env)?;
                            let _ = self.once.insert((i, k), v);
                        }
                    }
                }
                ItemKind::Module { body: Some(b), .. } if i != root => {
                    let _ = self.eval(b, &mut env)?;
                }
                _ => {}
            }
        }
        let body = match hir.item(root).kind {
            ItemKind::Module { body, .. } => body,
            _ => None,
        };
        let mut env = Env::new();
        match body {
            Some(b) => match self.eval(b, &mut env) {
                Ok(v) => Ok(v),
                Err(Sig::Return(v)) => Ok(v),
                Err(e) => Err(e),
            },
            None => Ok(V::Nil),
        }
    }

    fn lit(&mut self, l: Lit) -> V {
        match l {
            Lit::Null => V::Nil,
            Lit::Bool(b) => V::Bool(b),
            Lit::Int(i) => V::Int(if i.negative {
                (i.value as i64).wrapping_neg()
            } else {
                i.value as i64
            }),
            Lit::Float(f) => V::Float(f.value()),
            Lit::Char(c) => V::Char(c),
            Lit::Str(t) => V::Str(Rc::new(self.hir.str(t).as_bytes().to_vec())),
            Lit::Bytes(t) => V::Str(Rc::new(self.hir.text(t).to_vec())),
            Lit::BigInt(_) => V::Nil,
        }
    }

    // ------------------------------------------------------------ expressions

    pub fn eval(&mut self, e: ExprId, env: &mut Env) -> R<V> {
        self.tick()?;
        let node = NodeRef::Expr(e);
        let hir = self.hir;
        match *hir.expr(e) {
            Expr::Lit(l) => Ok(self.lit(l)),
            Expr::Path(p) => self.read_path(p, node, env),
            Expr::Tuple(l) | Expr::Array(l) => {
                let list = hir.list(l);
                if list.is_empty() && matches!(hir.expr(e), Expr::Tuple(_)) {
                    return Ok(V::Nil);
                }
                let m = Rc::new(RefCell::new(MapData::default()));
                for &x in list {
                    let v = self.eval(x, env)?;
                    let v = self.copy(&v);
                    map_push(&m, v, node)?;
                }
                Ok(V::Map(m))
            }
            Expr::Map(entries) => {
                let m = Rc::new(RefCell::new(MapData::default()));
                for en in hir.list(entries) {
                    match en.key {
                        Some(k) => {
                            let k = self.eval(k, env)?;
                            let k = self.coerce_key(k);
                            let v = self.eval(en.value, env)?;
                            let v = self.copy(&v);
                            let key = key_of(&k)?;
                            map_set(&m, key, v);
                        }
                        None => {
                            let v = self.eval(en.value, env)?;
                            let v = self.copy(&v);
                            map_push(&m, v, node)?;
                        }
                    }
                }
                Ok(V::Map(m))
            }
            Expr::Repeat { elem, count } => {
                let v = self.eval(elem, env)?;
                let c = self.eval(count, env)?;
                let V::Int(n) = c else {
                    return err(TYPE_ERROR, node);
                };
                let m = Rc::new(RefCell::new(MapData::default()));
                for _ in 0..n.max(0) {
                    self.tick()?;
                    let x = self.copy(&v);
                    map_push(&m, x, node)?;
                }
                Ok(V::Map(m))
            }
            Expr::Record { fields, base, .. } => {
                let m = Rc::new(RefCell::new(MapData::default()));
                for f in hir.list(fields) {
                    let v = self.eval(f.value, env)?;
                    let v = self.copy(&v);
                    let name = self.text(f.name.sym).into_bytes();
                    map_set(&m, Key::Str(name), v);
                }
                match base {
                    None => Ok(V::Map(m)),
                    Some(b) => {
                        let bv = self.eval(b, env)?;
                        let V::Map(bm) = bv else {
                            return err(TYPE_ERROR, node);
                        };
                        let out = Rc::new(RefCell::new(bm.borrow().clone()));
                        if self.cfg.php_arrays {
                            let c = deep_copy(&V::Map(out.clone()));
                            if let V::Map(c) = c {
                                let fields = m.borrow().entries.clone();
                                for (k, v) in fields {
                                    map_set(&c, k, v);
                                }
                                return Ok(V::Map(c));
                            }
                        }
                        let fields = m.borrow().entries.clone();
                        for (k, v) in fields {
                            map_set(&out, k, v);
                        }
                        Ok(V::Map(out))
                    }
                }
            }
            Expr::Call { callee, args } => self.call(e, callee, args, env),
            Expr::MethodCall {
                receiver,
                method,
                args,
                ..
            } => {
                let r = self.eval(receiver, env)?;
                let name = self.text(method.sym).into_bytes();
                let f = self.get_prop(&r, &name, node)?;
                let recv = self.copy(&r);
                self.dyn_call(f, Some(recv), args, env, node)
            }
            Expr::DynMethodCall {
                receiver,
                name,
                args,
            } => {
                let r = self.eval(receiver, env)?;
                let n = self.eval(name, env)?;
                let f = self.get_index(&r, &n, node)?;
                let recv = self.copy(&r);
                self.dyn_call(f, Some(recv), args, env, node)
            }
            Expr::Field { base, member, .. } => {
                let b = self.eval(base, env)?;
                match member {
                    Member::Named(s) => {
                        let name = self.text(s).into_bytes();
                        self.get_prop(&b, &name, node)
                    }
                    Member::Index(i) => self.get_index(&b, &V::Int(i64::from(i)), node),
                }
            }
            Expr::DynField { base, name } => {
                let b = self.eval(base, env)?;
                let n = self.eval(name, env)?;
                self.get_index(&b, &n, node)
            }
            Expr::Index { base, index } => {
                let b = self.eval(base, env)?;
                let k = self.eval(index, env)?;
                let k = self.coerce_key(k);
                self.get_index(&b, &k, node)
            }
            Expr::Op { op, args } => {
                let mut vs = Vec::new();
                for &a in hir.list(args) {
                    vs.push(self.eval(a, env)?);
                }
                self.op(op, &vs, node)
            }
            Expr::Cast { expr, ty, policy } => {
                let v = self.eval(expr, env)?;
                self.cast(v, ty, policy, node)
            }
            Expr::Assign { target, op, value } => self.assign(e, target, op, value, env),
            Expr::LetPlace {
                binder,
                place,
                body,
            } => {
                let pr = self.eval_place(place, env)?;
                let saved = self.aliases.insert(binder, pr);
                let r = self.eval(body, env);
                match saved {
                    Some(old) => {
                        let _ = self.aliases.insert(binder, old);
                    }
                    None => {
                        let _ = self.aliases.remove(&binder);
                    }
                }
                r
            }
            Expr::RefAssign { target, source } => {
                let (Some(t), Some(s)) = (self.local_of(target), self.local_of(source)) else {
                    return Err(Sig::Unspecified);
                };
                let sc = env.get(&s).cloned().unwrap_or_else(|| cell(V::Nil));
                let _ = env.insert(t, sc.clone());
                let v = sc.borrow().clone();
                Ok(v)
            }
            Expr::Block(b) => self.block(b, env),
            Expr::If { cond, then, else_ } => {
                let c = self.eval(cond, env)?;
                if Self::truthy(&c) {
                    self.eval(then, env)
                } else if let Some(x) = else_ {
                    self.eval(x, env)
                } else {
                    Ok(V::Nil)
                }
            }
            Expr::Match { scrutinee, arms } => {
                let s = self.eval(scrutinee, env)?;
                for arm in hir.list(arms) {
                    if self.matches(arm.pat, &s, env)? {
                        if let Some(g) = arm.guard {
                            let gv = self.eval(g, env)?;
                            if !Self::truthy(&gv) {
                                continue;
                            }
                        }
                        return self.eval(arm.body, env);
                    }
                }
                err(NO_MATCH, node)
            }
            Expr::Loop { label, body, step } => loop {
                self.tick()?;
                match self.eval(body, env) {
                    Ok(_) => {}
                    Err(Sig::Break(l, v)) if l.is_none() || l == label => return Ok(v),
                    Err(Sig::Continue(l)) if l.is_none() || l == label => {}
                    Err(x) => return Err(x),
                }
                if let Some(s) = step {
                    match self.eval(s, env) {
                        Ok(_) => {}
                        Err(Sig::Break(l, v)) if l.is_none() || l == label => return Ok(v),
                        Err(x) => return Err(x),
                    }
                }
            },
            Expr::Break { label, value } => {
                let v = match value {
                    Some(v) => {
                        let x = self.eval(v, env)?;
                        self.copy(&x)
                    }
                    None => V::Nil,
                };
                Err(Sig::Break(label, v))
            }
            Expr::Continue { label } => Err(Sig::Continue(label)),
            Expr::Return(v) => {
                let x = match v {
                    Some(v) => self.eval(v, env)?,
                    None => V::Nil,
                };
                Err(Sig::Return(self.copy(&x)))
            }
            Expr::Closure(c) => self.make_closure(e, c, env),
            Expr::Throw(x) => {
                let v = self.eval(x, env)?;
                Err(Sig::Throw(match v {
                    V::Error(code, n) => Exc::Error { code, node: n },
                    v => Exc::Value { v, node },
                }))
            }
            Expr::Try {
                body,
                catches,
                finally,
            } => self.try_(e, body, catches, finally, env),
            Expr::Intrinsic {
                kind: Intrinsic::Named(n),
                args,
                ..
            } => {
                let mut vs = Vec::new();
                for &a in hir.list(args) {
                    vs.push(self.eval(a, env)?);
                }
                self.intrinsic(&self.text(n), &vs, node)
            }
            _ => Err(Sig::Unspecified),
        }
    }

    fn local_of(&self, e: ExprId) -> Option<BinderId> {
        match *self.hir.expr(e) {
            Expr::Path(p) => match self.hir.path(p).res {
                Res::Local(b) => Some(b),
                _ => None,
            },
            _ => None,
        }
    }

    fn global_cell(&self, res: Res) -> Option<Cell> {
        match res {
            Res::Def(d) => match d.def() {
                hir_lang::Def::Item(i) => self.globals.get(&i).cloned(),
                _ => None,
            },
            _ => None,
        }
    }

    fn read_path(&mut self, p: hir_lang::PathId, node: NodeRef, env: &mut Env) -> R<V> {
        let path = *self.hir.path(p);
        match path.res {
            Res::Local(b) if self.aliases.contains_key(&b) => {
                let pr = self.aliases.get(&b).cloned().ok_or(Sig::Unspecified)?;
                self.place_read(&pr, node, env)
            }
            Res::Local(b) => match env.get(&b) {
                Some(c) => Ok(c.borrow().clone()),
                None => Err(Sig::Unspecified),
            },
            Res::Def(d) => match d.def() {
                hir_lang::Def::Item(i) => match self.hir.item(i).kind {
                    ItemKind::Fn(_) => Ok(V::Func(Rc::new(Func::Item(i)))),
                    _ => match self.globals.get(&i) {
                        Some(c) => Ok(c.borrow().clone()),
                        None => Err(Sig::Unspecified),
                    },
                },
                _ => Err(Sig::Unspecified),
            },
            _ => {
                let _ = node;
                Err(Sig::Unspecified)
            }
        }
    }

    fn block(&mut self, b: Block, env: &mut Env) -> R<V> {
        let hir = self.hir;
        let stmts = hir.list(b.stmts);
        let r = self.stmts(stmts, b.tail, env);
        match (r, b.label) {
            (Err(Sig::Break(Some(l), v)), Some(lab)) if l == lab => Ok(v),
            (r, _) => r,
        }
    }

    fn stmts(&mut self, stmts: &[StmtId], tail: Option<ExprId>, env: &mut Env) -> R<V> {
        let hir = self.hir;
        for (i, &s) in stmts.iter().enumerate() {
            if let Stmt::Defer(d) = *hir.stmt(s) {
                // The rest runs under a `finally` of `d`.
                let rest = &stmts[i + 1..];
                let r = self.stmts(rest, tail, env);
                return self.finally(r, d, NodeRef::Stmt(s), env);
            }
            self.stmt(s, env)?;
        }
        match tail {
            Some(t) => self.eval(t, env),
            None => Ok(V::Nil),
        }
    }

    fn stmt(&mut self, s: StmtId, env: &mut Env) -> R<()> {
        let node = NodeRef::Stmt(s);
        let hir = self.hir;
        match *hir.stmt(s) {
            Stmt::Expr(e) => {
                let _ = self.eval(e, env)?;
            }
            Stmt::Let {
                pat, init, else_, ..
            } => {
                let v = match init {
                    Some(i) => self.eval(i, env)?,
                    None => V::Nil,
                };
                if !self.matches(pat, &v, env)? {
                    match else_ {
                        Some(e) => {
                            let _ = self.eval(e, env)?;
                        }
                        None => return err(TYPE_ERROR, node),
                    }
                }
            }
            Stmt::Static { binder, init, .. } => {
                let (c, done) = match self.statics.get(&s) {
                    Some((c, d)) => (c.clone(), *d),
                    None => (cell(V::Nil), false),
                };
                let _ = self.statics.insert(s, (c.clone(), done));
                let _ = env.insert(binder, c.clone());
                if !done {
                    if let Some(i) = init {
                        let v = self.eval(i, env)?;
                        *c.borrow_mut() = self.copy(&v);
                        let _ = self.statics.insert(s, (c, true));
                    }
                }
            }
            Stmt::Global { binder, path } => {
                let res = hir.path(path).res;
                if let Some(c) = self.global_cell(res) {
                    let _ = env.insert(binder, c);
                }
            }
            Stmt::Item(_) => {}
            Stmt::Defer(d) => {
                let _ = self.eval(d, env)?;
            }
            Stmt::Err => return Err(Sig::Unspecified),
        }
        Ok(())
    }

    // ------------------------------------------------------------ try

    fn finally(&mut self, r: R<V>, fin: ExprId, node: NodeRef, env: &mut Env) -> R<V> {
        match r {
            // Traps and budget exhaustion skip handlers entirely.
            Err(Sig::Trap(..) | Sig::Budget | Sig::Unspecified) => r,
            r => {
                let _ = self.eval(fin, env)?;
                match r {
                    // A rethrown value is thrown again by the `finally`.
                    Err(Sig::Throw(Exc::Value { v, .. })) => {
                        Err(Sig::Throw(Exc::Value { v, node }))
                    }
                    r => r,
                }
            }
        }
    }

    fn try_(
        &mut self,
        e: ExprId,
        body: ExprId,
        catches: hir_lang::List<hir_lang::Arm>,
        finally: Option<ExprId>,
        env: &mut Env,
    ) -> R<V> {
        let node = NodeRef::Expr(e);
        let hir = self.hir;
        let mut r = self.eval(body, env);
        if let Err(Sig::Throw(exc)) = &r {
            let arms = hir.list(catches);
            if !arms.is_empty() {
                let exc = exc.clone();
                let v = match &exc {
                    Exc::Error { code, node } => V::Error(*code, *node),
                    Exc::Value { v, .. } => v.clone(),
                };
                r = Err(Sig::Throw(match exc {
                    Exc::Value { v, .. } => Exc::Value { v, node },
                    e => e,
                }));
                for arm in arms {
                    match self.matches(arm.pat, &v, env) {
                        Ok(true) => {}
                        Ok(false) => continue,
                        Err(x) => {
                            r = Err(x);
                            break;
                        }
                    }
                    if let Some(g) = arm.guard {
                        match self.eval(g, env) {
                            Ok(gv) if !Self::truthy(&gv) => continue,
                            Ok(_) => {}
                            Err(x) => {
                                r = Err(x);
                                break;
                            }
                        }
                    }
                    r = self.eval(arm.body, env);
                    break;
                }
            }
        }
        match finally {
            Some(f) => self.finally(r, f, node, env),
            None => r,
        }
    }

    // ------------------------------------------------------------ calls

    fn call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        args: hir_lang::List<Arg>,
        env: &mut Env,
    ) -> R<V> {
        let node = NodeRef::Expr(e);
        let hir = self.hir;
        if let Expr::Path(p) = *hir.expr(callee) {
            match hir.path(p).res {
                Res::Extern(sym) => {
                    let mut vs = Vec::new();
                    for a in hir.list(args) {
                        let v = self.eval(a.value, env)?;
                        vs.push(self.copy(&v));
                    }
                    return self.host(&self.text(sym), &vs, node);
                }
                Res::Def(d) => {
                    if let hir_lang::Def::Item(i) = d.def() {
                        if let ItemKind::Fn(_) = hir.item(i).kind {
                            let f = Func::Item(i);
                            let items = self.args(&f, 0, args, env, node)?;
                            return self.invoke(&f, items, node);
                        }
                    }
                }
                _ => {}
            }
        }
        let f = self.eval(callee, env)?;
        self.dyn_call(f, None, args, env, node)
    }

    fn dyn_call(
        &mut self,
        f: V,
        recv: Option<V>,
        args: hir_lang::List<Arg>,
        env: &mut Env,
        node: NodeRef,
    ) -> R<V> {
        let shift = usize::from(recv.is_some());
        let func = match &f {
            V::Func(func) => Some(func.clone()),
            _ => None,
        };
        let mut items = match &func {
            Some(func) => self.args(func, shift, args, env, node)?,
            None => self.args(&Func::Item(self.hir.root()), shift, args, env, node)?,
        };
        if let Some(r) = recv {
            items.insert(0, (None, Av::Val(r)));
        }
        match func {
            Some(func) => self.invoke(&func, items, node),
            None => err(TYPE_ERROR, node),
        }
    }

    /// Whether `f` takes the argument at `at` by reference (LSB §5.15's
    /// `dparam_ref` rule).
    fn takes_ref(&self, f: &Func, at: Result<usize, &[u8]>) -> bool {
        let hir = self.hir;
        let params: Vec<ParamId> = match f {
            Func::Item(i) => match hir.item(*i).kind {
                ItemKind::Fn(def) => hir.list(def.params).to_vec(),
                _ => return false,
            },
            Func::Closure { e, .. } => match *hir.expr(*e) {
                Expr::Closure(c) => hir.list(c.params).to_vec(),
                _ => return false,
            },
        };
        let infos: Vec<hir_lang::Param> = params.iter().map(|&p| *hir.param(p)).collect();
        let rest = infos.iter().find(|p| p.kind == ParamKind::Rest);
        match at {
            Ok(pos) => {
                let positional: Vec<&hir_lang::Param> = infos
                    .iter()
                    .filter(|p| matches!(p.kind, ParamKind::PositionalOnly | ParamKind::Normal))
                    .collect();
                match positional.get(pos) {
                    Some(p) => p.by_ref,
                    None => rest.is_some_and(|p| p.by_ref),
                }
            }
            Err(name) => {
                let named = infos.iter().enumerate().find(|(i, p)| {
                    matches!(p.kind, ParamKind::Normal | ParamKind::NamedOnly)
                        && self.param_name(params[*i]).as_deref() == Some(name)
                });
                match named {
                    Some((_, p)) => p.by_ref,
                    None => match infos.iter().find(|p| p.kind == ParamKind::RestNamed) {
                        Some(p) => p.by_ref,
                        None => rest.is_some_and(|p| p.by_ref),
                    },
                }
            }
        }
    }

    /// Evaluates arguments in order (spreads flattened, LSB §5.15 step 2).
    /// A place argument naming a shared variable passes the variable when
    /// `f` takes that argument by reference, else its value now; after a
    /// spread, positions are unknown and place arguments go by value.
    fn args(
        &mut self,
        f: &Func,
        shift: usize,
        args: hir_lang::List<Arg>,
        env: &mut Env,
        node: NodeRef,
    ) -> R<Args> {
        let hir = self.hir;
        let mut items: Args = Vec::new();
        let mut pos = shift;
        let mut spread = false;
        for a in hir.list(args) {
            let at = match a.kind {
                ArgKind::Positional => {
                    pos += 1;
                    (!spread).then_some(Ok(pos - 1))
                }
                ArgKind::Named(id) => Some(Err(self.text(id.sym).into_bytes())),
                _ => None,
            };
            let by_ref = match &at {
                Some(Ok(p)) => self.takes_ref(f, Ok(*p)),
                Some(Err(n)) => self.takes_ref(f, Err(n.as_slice())),
                None => false,
            };
            let place = if a.place && by_ref {
                match *hir.expr(a.value) {
                    Expr::Path(p) => match hir.path(p).res {
                        Res::Local(b) => env.get(&b).cloned(),
                        res => match hir.item_kind_of(res) {
                            Some(false) => self.global_cell(res),
                            _ => None,
                        },
                    },
                    _ => None,
                }
            } else {
                None
            };
            match a.kind {
                ArgKind::Positional | ArgKind::Named(_) => {
                    let name = match a.kind {
                        ArgKind::Named(id) => Some(self.text(id.sym).into_bytes()),
                        _ => None,
                    };
                    match place {
                        Some(c) => items.push((name, Av::Cell(c))),
                        None => {
                            let v = self.eval(a.value, env)?;
                            items.push((name, Av::Val(self.copy(&v))));
                        }
                    }
                }
                ArgKind::Spread => {
                    spread = true;
                    let v = self.eval(a.value, env)?;
                    let V::Map(m) = v else {
                        return err(TYPE_ERROR, node);
                    };
                    let entries = m.borrow().entries.clone();
                    for (k, x) in entries {
                        let name = match k {
                            Key::Int(_) => None,
                            Key::Str(s) => Some(s),
                            _ => return err(ARG_ERROR, node),
                        };
                        items.push((name, Av::Val(self.copy(&x))));
                    }
                }
                ArgKind::SpreadNamed => {
                    spread = true;
                    let v = self.eval(a.value, env)?;
                    let V::Map(m) = v else {
                        return err(TYPE_ERROR, node);
                    };
                    let entries = m.borrow().entries.clone();
                    for (k, x) in entries {
                        let Key::Str(s) = k else {
                            return err(ARG_ERROR, node);
                        };
                        items.push((Some(s), Av::Val(self.copy(&x))));
                    }
                }
            }
        }
        Ok(items)
    }

    fn invoke(&mut self, f: &Func, items: Args, call: NodeRef) -> R<V> {
        self.depth += 1;
        if self.depth > 200 {
            self.depth -= 1;
            return Err(Sig::Budget);
        }
        let r = self.invoke_inner(f, items, call);
        self.depth -= 1;
        r
    }

    fn invoke_inner(&mut self, f: &Func, items: Args, call: NodeRef) -> R<V> {
        let hir = self.hir;
        let (params, body, node, defaults, item): (
            Vec<ParamId>,
            Option<ExprId>,
            NodeRef,
            DefaultEval,
            Option<ItemId>,
        ) = match f {
            Func::Item(i) => match hir.item(*i).kind {
                ItemKind::Fn(def) => (
                    hir.list(def.params).to_vec(),
                    def.body,
                    NodeRef::Item(*i),
                    def.defaults,
                    Some(*i),
                ),
                _ => return Err(Sig::Unspecified),
            },
            Func::Closure { e, .. } => match *hir.expr(*e) {
                Expr::Closure(c) => (
                    hir.list(c.params).to_vec(),
                    Some(c.body),
                    NodeRef::Expr(*e),
                    c.defaults,
                    None,
                ),
                _ => return Err(Sig::Unspecified),
            },
        };
        let Some(body) = body else {
            // A bodyless function is a host function.
            let name = match f {
                Func::Item(i) => hir
                    .item(*i)
                    .name
                    .map(|n| self.text(n.sym))
                    .unwrap_or_default(),
                _ => String::new(),
            };
            let vs: Vec<V> = items.iter().map(|(_, a)| a.value()).collect();
            return self.host(&name, &vs, node);
        };
        let mut env = Env::new();
        let mut once_vals: Vec<Option<V>> = vec![None; params.len()];
        if let Func::Closure { caps, once, .. } = f {
            for (b, c) in caps {
                let slot = match c {
                    Captured::Value(v) => cell(self.copy(v)),
                    Captured::Shared(c) | Captured::Global(c) => c.clone(),
                };
                let _ = env.insert(*b, slot);
            }
            once_vals = once.clone();
        }
        if let Some(i) = item {
            for (k, slot) in once_vals.iter_mut().enumerate() {
                if let Some(v) = self.once.get(&(i, k)) {
                    *slot = Some(v.clone());
                }
            }
        }
        // Bind arguments (LSB §5.15 step 3: errors at the call).
        let infos: Vec<hir_lang::Param> = params.iter().map(|&p| *hir.param(p)).collect();
        let mut vals: Vec<Option<Av>> = vec![None; params.len()];
        let positional: Vec<usize> = (0..infos.len())
            .filter(|&i| matches!(infos[i].kind, ParamKind::PositionalOnly | ParamKind::Normal))
            .collect();
        let rest = infos.iter().position(|p| p.kind == ParamKind::Rest);
        let rest_named = infos.iter().position(|p| p.kind == ParamKind::RestNamed);
        let rest_map = Rc::new(RefCell::new(MapData::default()));
        let named_map = Rc::new(RefCell::new(MapData::default()));
        let mut next = 0usize;
        let mut named_seen = false;
        for (name, a) in items {
            match name {
                None => {
                    if named_seen {
                        return err(ARG_ERROR, call);
                    }
                    match positional.get(next) {
                        Some(&j) => {
                            next += 1;
                            vals[j] = Some(a);
                        }
                        None if rest.is_some() => {
                            let v = a.value();
                            map_push(&rest_map, self.copy(&v), call)?;
                        }
                        None => return err(ARG_ERROR, call),
                    }
                }
                Some(n) => {
                    named_seen = true;
                    let j = infos.iter().enumerate().position(|(i, p)| {
                        matches!(p.kind, ParamKind::Normal | ParamKind::NamedOnly)
                            && self.param_name(params[i]).as_deref() == Some(n.as_slice())
                    });
                    match j {
                        Some(j) => {
                            if vals[j].is_some() {
                                return err(ARG_ERROR, call);
                            }
                            vals[j] = Some(a);
                        }
                        None => {
                            let into = match (rest_named, rest) {
                                (Some(_), _) => &named_map,
                                (None, Some(_)) => &rest_map,
                                (None, None) => return err(ARG_ERROR, call),
                            };
                            let key = Key::Str(n);
                            if map_find(into, &key).is_some() {
                                return err(ARG_ERROR, call);
                            }
                            let v = a.value();
                            map_set(into, key, self.copy(&v));
                        }
                    }
                }
            }
        }
        for (i, p) in infos.iter().enumerate() {
            if vals[i].is_none()
                && p.default.is_none()
                && !matches!(p.kind, ParamKind::Rest | ParamKind::RestNamed)
            {
                return err(ARG_ERROR, call);
            }
        }
        if let Some(r) = rest {
            vals[r] = Some(Av::Val(V::Map(rest_map)));
        }
        if let Some(r) = rest_named {
            vals[r] = Some(Av::Val(V::Map(named_map)));
        }
        // Defaults and patterns, in order.
        for (i, &pid) in params.iter().enumerate() {
            let p = infos[i];
            let pnode = NodeRef::Param(pid);
            let slot: Cell = match vals[i].take() {
                Some(Av::Cell(c)) if p.by_ref => c,
                Some(Av::Cell(c)) => {
                    let v = c.borrow().clone();
                    cell(self.copy(&v))
                }
                Some(Av::Val(v)) => cell(v),
                None => {
                    let v = match (&once_vals[i], defaults) {
                        (Some(v), _) => self.copy(v),
                        (None, _) => match p.default {
                            Some(d) => {
                                let v = self.eval(d, &mut env)?;
                                self.copy(&v)
                            }
                            None => V::Nil,
                        },
                    };
                    cell(v)
                }
            };
            match *hir.pat(p.pat) {
                Pat::Bind {
                    binder,
                    mode: BindMode::Value,
                    sub: None,
                } => {
                    let _ = env.insert(binder, slot);
                }
                _ => {
                    let v = slot.borrow().clone();
                    if !self.matches(p.pat, &v, &mut env)? {
                        return err(TYPE_ERROR, pnode);
                    }
                }
            }
        }
        match self.eval(body, &mut env) {
            Ok(v) => Ok(self.copy(&v)),
            Err(Sig::Return(v)) => Ok(v),
            Err(e) => Err(e),
        }
    }

    fn param_name(&self, p: ParamId) -> Option<Vec<u8>> {
        match *self.hir.pat(self.hir.param(p).pat) {
            Pat::Bind { binder, .. } | Pat::Ident { binder, .. } => self
                .hir
                .binder(binder)
                .map(|b| self.text(b.name.sym).into_bytes()),
            _ => None,
        }
    }

    fn make_closure(&mut self, e: ExprId, c: hir_lang::Closure, env: &mut Env) -> R<V> {
        let hir = self.hir;
        let mut caps = Vec::new();
        let self_cell = c.self_binder.map(|b| (b, cell(V::Nil)));
        if let Some((b, sc)) = &self_cell {
            caps.push((*b, Captured::Shared(sc.clone())));
        }
        for cap in hir.list(c.captures) {
            let outer = hir.path(cap.outer).res;
            let src = match outer {
                Res::Local(b) => env.get(&b).cloned(),
                r => self.global_cell(r),
            };
            let Some(src) = src else {
                return Err(Sig::Unspecified);
            };
            let is_global = !matches!(outer, Res::Local(_)) || self.is_global_alias(&src);
            match cap.mode {
                CaptureMode::ByValue | CaptureMode::Infer => {
                    let v = src.borrow().clone();
                    caps.push((cap.binder, Captured::Value(self.copy(&v))));
                }
                _ if is_global => caps.push((cap.binder, Captured::Global(src))),
                _ => caps.push((cap.binder, Captured::Shared(src))),
            }
        }
        let implicit = hir
            .all_implicit_captures()
            .into_iter()
            .find(|(x, _)| *x == e)
            .map(|(_, v)| v)
            .unwrap_or_default();
        for b in implicit {
            let Some(src) = env.get(&b).cloned() else {
                continue;
            };
            match c.implicit {
                Some(CaptureMode::ByValue) => {
                    let v = src.borrow().clone();
                    caps.push((b, Captured::Value(self.copy(&v))));
                }
                _ => caps.push((b, Captured::Shared(src))),
            }
        }
        let mut once = vec![None; hir.list(c.params).len()];
        if c.defaults == DefaultEval::Once {
            for (i, &p) in hir.list(c.params).iter().enumerate() {
                if let Some(d) = hir.param(p).default {
                    once[i] = Some(self.eval(d, env)?);
                }
            }
        }
        let f = V::Func(Rc::new(Func::Closure { e, caps, once }));
        if let Some((_, sc)) = self_cell {
            *sc.borrow_mut() = f.clone();
        }
        Ok(f)
    }

    fn is_global_alias(&self, c: &Cell) -> bool {
        self.globals.values().any(|g| Rc::ptr_eq(g, c))
            || self.statics.values().any(|(g, _)| Rc::ptr_eq(g, c))
    }

    /// Host functions the tests register.
    fn host(&mut self, name: &str, args: &[V], node: NodeRef) -> R<V> {
        match name {
            "echo" | "host.echo" => {
                let s: Vec<String> = args.iter().map(show).collect();
                self.out.push(s.join(""));
                Ok(V::Nil)
            }
            "fail" | "host.fail" => err(TYPE_ERROR, node),
            _ => err(TYPE_ERROR, node),
        }
    }

    // ------------------------------------------------------------ places

    fn assign(
        &mut self,
        e: ExprId,
        target: ExprId,
        op: Option<Op>,
        value: ExprId,
        env: &mut Env,
    ) -> R<V> {
        let node = NodeRef::Expr(e);
        let pr = self.eval_place(target, env)?;
        let v = match op {
            Some(op) => {
                let old = self.place_read(&pr, node, env)?;
                let v = self.eval(value, env)?;
                self.op(op, &[old, v], node)?
            }
            None => {
                let v = self.eval(value, env)?;
                self.copy(&v)
            }
        };
        self.place_write(&pr, v.clone(), node, env)?;
        Ok(v)
    }

    /// Evaluates a place's operands (root value, then keys, in order); a
    /// `let_place` alias in the chain contributes its own.
    fn eval_place(&mut self, target: ExprId, env: &mut Env) -> R<PlaceRef> {
        let hir = self.hir;
        let mut steps: Vec<Step> = Vec::new();
        let mut key_exprs: Vec<(ExprId, bool)> = Vec::new();
        let mut cur = target;
        let mut base = PlaceRef {
            root_local: None,
            root: None,
            root_val: None,
            steps: Vec::new(),
            keys: Vec::new(),
        };
        let mut value_root = false;
        loop {
            match *hir.expr(cur) {
                Expr::Index { base: b, index } => {
                    steps.push(Step::Index);
                    key_exprs.push((index, true));
                    cur = b;
                }
                Expr::DynField { base: b, name } => {
                    steps.push(Step::Dyn);
                    key_exprs.push((name, false));
                    cur = b;
                }
                Expr::Field {
                    base: b, member, ..
                } => {
                    steps.push(match member {
                        Member::Named(s) => Step::Prop(self.text(s).into_bytes()),
                        Member::Index(i) => Step::Elem(i),
                    });
                    cur = b;
                }
                Expr::Append(b) => {
                    steps.push(Step::Append);
                    cur = b;
                }
                Expr::Path(p) => {
                    let res = hir.path(p).res;
                    match res {
                        Res::Local(b) if self.aliases.contains_key(&b) => {
                            base = self.aliases.get(&b).cloned().ok_or(Sig::Unspecified)?;
                        }
                        Res::Local(b) => base.root_local = Some(b),
                        _ => match self.global_cell(res) {
                            Some(c) if !matches!(hir.item_kind_of(res), Some(true)) => {
                                base.root = Some(c);
                            }
                            _ => value_root = true,
                        },
                    }
                    break;
                }
                _ => {
                    value_root = true;
                    break;
                }
            }
        }
        steps.reverse();
        key_exprs.reverse();
        if value_root {
            base.root_val = Some(self.eval(cur, env)?);
        }
        for (k, index) in key_exprs {
            let v = self.eval(k, env)?;
            base.keys.push(if index { self.coerce_key(v) } else { v });
        }
        base.steps.extend(steps);
        Ok(base)
    }

    /// The current root value of a place.
    fn place_root(&self, pr: &PlaceRef, env: &Env) -> (Option<Cell>, V) {
        let cell = match pr.root_local {
            Some(b) => env.get(&b).cloned(),
            None => pr.root.clone(),
        };
        let v = match (&cell, &pr.root_val) {
            (Some(c), _) => c.borrow().clone(),
            (None, Some(v)) => v.clone(),
            _ => V::Nil,
        };
        (cell, v)
    }

    fn place_read(&mut self, pr: &PlaceRef, node: NodeRef, env: &mut Env) -> R<V> {
        let (_, mut cur) = self.place_root(pr, env);
        let mut ki = 0;
        for s in &pr.steps {
            cur = match s {
                Step::Index | Step::Dyn => {
                    let k = pr.keys[ki].clone();
                    ki += 1;
                    self.get_index(&cur, &k, node)?
                }
                Step::Elem(i) => self.get_index(&cur, &V::Int(i64::from(*i)), node)?,
                Step::Prop(n) => self.get_prop(&cur, n, node)?,
                Step::Append => return Err(Sig::Unspecified),
            };
        }
        Ok(cur)
    }

    fn place_write(&mut self, pr: &PlaceRef, v: V, node: NodeRef, env: &mut Env) -> R<()> {
        let php = self.cfg.php_arrays;
        let (root, mut cur) = self.place_root(pr, env);
        if pr.steps.is_empty() {
            let Some(rc) = root else {
                return Err(Sig::Unspecified);
            };
            *rc.borrow_mut() = v;
            return Ok(());
        }
        if php && matches!(cur, V::Nil) {
            cur = V::Map(Rc::new(RefCell::new(MapData::default())));
            if let Some(c) = &root {
                *c.borrow_mut() = cur.clone();
            }
        }
        let last = pr.steps.len() - 1;
        let mut ki = 0;
        for (i, s) in pr.steps.iter().enumerate() {
            let key: Option<V> = match s {
                Step::Index | Step::Dyn => {
                    let k = pr.keys[ki].clone();
                    ki += 1;
                    Some(k)
                }
                Step::Elem(n) => Some(V::Int(i64::from(*n))),
                Step::Prop(n) => Some(V::Str(Rc::new(n.clone()))),
                Step::Append => None,
            };
            if i == last {
                match (s, key) {
                    (Step::Append, _) => match &cur {
                        V::Map(m) => map_push(m, v.clone(), node)?,
                        _ => return err(TYPE_ERROR, node),
                    },
                    (Step::Prop(n), _) => match &cur {
                        V::Map(m) => map_set(m, Key::Str(n.clone()), v.clone()),
                        _ => return err(UNDEFINED_PROPERTY, node),
                    },
                    (_, Some(k)) => match &cur {
                        V::Map(m) => map_set(m, key_of(&k)?, v.clone()),
                        _ => return err(TYPE_ERROR, node),
                    },
                    _ => {}
                }
            } else {
                cur = match (&cur, s, key) {
                    (V::Map(m), Step::Append, _) if php => {
                        let n = V::Map(Rc::new(RefCell::new(MapData::default())));
                        map_push(m, n.clone(), node)?;
                        n
                    }
                    (V::Map(m), _, Some(k)) if php => {
                        let key = key_of(&k)?;
                        let found = map_find(m, &key);
                        match found {
                            Some(c @ V::Map(_)) => c,
                            Some(V::Nil) | None => {
                                let n = V::Map(Rc::new(RefCell::new(MapData::default())));
                                map_set(m, key, n.clone());
                                n
                            }
                            Some(other) => other,
                        }
                    }
                    (V::Map(m), Step::Append, _) => {
                        let n = V::Map(Rc::new(RefCell::new(MapData::default())));
                        map_push(m, n.clone(), node)?;
                        n
                    }
                    (_, Step::Append, _) => return err(TYPE_ERROR, node),
                    (c, Step::Prop(n), _) => self.get_prop(c, n, node)?,
                    (c, _, Some(k)) => self.get_index(c, &k, node)?,
                    _ => V::Nil,
                };
            }
        }
        Ok(())
    }

    // ------------------------------------------------------------ access

    fn get_index(&mut self, b: &V, k: &V, node: NodeRef) -> R<V> {
        match b {
            V::Map(m) => {
                let key = key_of(k)?;
                match map_find(m, &key) {
                    Some(v) => Ok(v),
                    None => err(KEY_NOT_FOUND, node),
                }
            }
            V::Str(s) => match k {
                V::Int(i) if *i >= 0 && (*i as usize) < s.len() => {
                    Ok(V::Int(i64::from(s[*i as usize])))
                }
                V::Int(_) => err(INDEX_OOB, node),
                _ => err(TYPE_ERROR, node),
            },
            _ => err(TYPE_ERROR, node),
        }
    }

    fn get_prop(&mut self, b: &V, name: &[u8], node: NodeRef) -> R<V> {
        match b {
            V::Map(m) => match map_find(m, &Key::Str(name.to_vec())) {
                Some(v) => Ok(v),
                None => err(UNDEFINED_PROPERTY, node),
            },
            _ => err(UNDEFINED_PROPERTY, node),
        }
    }

    pub fn coerce_key(&self, k: V) -> V {
        if !self.cfg.php_keys {
            return k;
        }
        match k {
            V::Str(s) => match canonical_int(&s) {
                Some(i) => V::Int(i),
                None => V::Str(s),
            },
            V::Float(f) => V::Int(if f.is_nan() {
                0
            } else if f >= 9_223_372_036_854_775_808.0 {
                i64::MAX
            } else if f <= -9_223_372_036_854_775_808.0 {
                i64::MIN
            } else {
                f.trunc() as i64
            }),
            V::Bool(b) => V::Int(i64::from(b)),
            V::Nil => V::Str(Rc::new(Vec::new())),
            k => k,
        }
    }

    // ------------------------------------------------------------ patterns

    fn bind(&mut self, b: BinderId, v: &V, env: &mut Env) {
        let v = self.copy(v);
        let _ = env.insert(b, cell(v));
    }

    fn matches(&mut self, p: PatId, v: &V, env: &mut Env) -> R<bool> {
        let hir = self.hir;
        let node = NodeRef::Pat(p);
        Ok(match *hir.pat(p) {
            Pat::Wild => true,
            Pat::Bind { binder, sub, .. } => {
                if let Some(s) = sub {
                    if !self.matches(s, v, env)? {
                        return Ok(false);
                    }
                }
                self.bind(binder, v, env);
                true
            }
            Pat::Ident { binder, path } => match self.global_cell(hir.path(path).res) {
                Some(c) => {
                    let x = c.borrow().clone();
                    deq(v, &x)?
                }
                None => {
                    self.bind(binder, v, env);
                    true
                }
            },
            Pat::Lit(l) => {
                let x = self.lit(l);
                deq(v, &x)?
            }
            Pat::Path(path) => match self.global_cell(hir.path(path).res) {
                Some(c) => {
                    let x = c.borrow().clone();
                    deq(v, &x)?
                }
                None => return Err(Sig::Unspecified),
            },
            Pat::Range { lo, hi, inclusive } => {
                let mut ok = true;
                for (i, b) in [lo, hi].into_iter().enumerate() {
                    let Some(b) = b else { continue };
                    let bv = match *hir.pat(b) {
                        Pat::Lit(l) => self.lit(l),
                        Pat::Path(path) => match self.global_cell(hir.path(path).res) {
                            Some(c) => c.borrow().clone(),
                            None => return Err(Sig::Unspecified),
                        },
                        _ => return Err(Sig::Unspecified),
                    };
                    let same = match (&bv, v) {
                        (V::Char(_), V::Char(_)) => true,
                        (V::Char(_), _) => false,
                        (V::Int(_) | V::Float(_), V::Int(_) | V::Float(_)) => true,
                        _ => false,
                    };
                    if !same {
                        return Ok(false);
                    }
                    let c = if i == 0 {
                        dcmp(&bv, v, node)?.is_some_and(|o| o.is_le())
                    } else if inclusive {
                        dcmp(v, &bv, node)?.is_some_and(|o| o.is_le())
                    } else {
                        dcmp(v, &bv, node)?.is_some_and(|o| o.is_lt())
                    };
                    ok &= c;
                    if !ok {
                        return Ok(false);
                    }
                }
                ok
            }
            Pat::Tuple { elems, rest } => {
                let elems = hir.list(elems).to_vec();
                self.seq(v, &elems, rest.map(|r| r as usize), None, env)?
            }
            Pat::Slice { prefix, rest } => {
                let prefix = hir.list(prefix).to_vec();
                match rest {
                    None => self.seq(v, &prefix, None, None, env)?,
                    Some(r) => {
                        let mut all = prefix.clone();
                        all.extend_from_slice(hir.list(r.suffix));
                        self.seq(v, &all, Some(prefix.len()), Some(r.bind), env)?
                    }
                }
            }
            Pat::Record { fields, rest, .. } => {
                let V::Map(m) = v else { return Ok(false) };
                let fields = hir.list(fields).to_vec();
                if !rest && m.borrow().entries.len() != fields.len() {
                    return Ok(false);
                }
                let mut subs = Vec::new();
                for f in &fields {
                    let k = Key::Str(self.text(f.name.sym).into_bytes());
                    match map_find(m, &k) {
                        Some(x) => subs.push((f.pat, x)),
                        None => return Ok(false),
                    }
                }
                for (p, x) in subs {
                    if !self.matches(p, &x, env)? {
                        return Ok(false);
                    }
                }
                true
            }
            Pat::Or(alts) => {
                for &a in hir.list(alts) {
                    if self.matches(a, v, env)? {
                        return Ok(true);
                    }
                }
                false
            }
            Pat::TypeTest { ty, pat } => {
                if !self.type_ok(ty, v)? {
                    return Ok(false);
                }
                match pat {
                    Some(s) => self.matches(s, v, env)?,
                    None => true,
                }
            }
            _ => return Err(Sig::Unspecified),
        })
    }

    fn seq(
        &mut self,
        v: &V,
        pats: &[PatId],
        rest: Option<usize>,
        bind: Option<Option<PatId>>,
        env: &mut Env,
    ) -> R<bool> {
        let V::Map(m) = v else { return Ok(false) };
        let n = pats.len();
        let len = m.borrow().entries.len();
        match rest {
            None if len != n => return Ok(false),
            Some(_) if len < n => return Ok(false),
            _ => {}
        }
        let split = rest.unwrap_or(n);
        let mut subs = Vec::new();
        for (i, &p) in pats.iter().enumerate() {
            let k = if i < split {
                i as i64
            } else {
                len as i64 - (n - i) as i64
            };
            match map_find(m, &Key::Int(k)) {
                Some(x) => subs.push((p, x)),
                None => return Ok(false),
            }
        }
        if let Some(Some(rp)) = bind {
            let out = Rc::new(RefCell::new(MapData::default()));
            let end = len as i64 - (n - split) as i64;
            let mut k = split as i64;
            while k < end {
                match map_find(m, &Key::Int(k)) {
                    Some(x) => map_push(&out, x, NodeRef::Pat(rp))?,
                    None => return Ok(false),
                }
                k += 1;
            }
            subs.push((rp, V::Map(out)));
        }
        for (p, x) in subs {
            if !self.matches(p, &x, env)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn type_ok(&self, ty: TyId, v: &V) -> R<bool> {
        let hir = self.hir;
        let (ty, nullable) = match *hir.ty(ty) {
            Ty::Nullable(t) => (t, true),
            _ => (ty, false),
        };
        if nullable && matches!(v, V::Nil) {
            return Ok(true);
        }
        let prim = match *hir.ty(ty) {
            Ty::Any | Ty::Infer => return Ok(true),
            Ty::Union(ms) => {
                for &m in hir.list(ms) {
                    if self.type_ok(m, v)? {
                        return Ok(true);
                    }
                }
                return Ok(false);
            }
            Ty::Intersection(ms) => {
                for &m in hir.list(ms) {
                    if !self.type_ok(m, v)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            Ty::Tuple(_) | Ty::Array { .. } | Ty::Slice(_) => return Ok(matches!(v, V::Map(_))),
            Ty::Prim(p) => p,
            Ty::Path(p) => match hir.path(p).res {
                Res::Prim(p) => p,
                _ => return Err(Sig::Unspecified),
            },
            _ => return Err(Sig::Unspecified),
        };
        Ok(match prim {
            Prim::Bool => matches!(v, V::Bool(_)),
            Prim::F32 | Prim::F64 => matches!(v, V::Float(_)),
            Prim::Char => matches!(v, V::Char(_)),
            Prim::Str => matches!(v, V::Str(_)),
            _ => matches!(v, V::Int(_)),
        })
    }

    // ------------------------------------------------------------ operations

    pub fn op(&mut self, op: Op, a: &[V], node: NodeRef) -> R<V> {
        let x = a.first().cloned().unwrap_or(V::Nil);
        let y = a.get(1).cloned().unwrap_or(V::Nil);
        let p = op.policy;
        let over = p.overflow.unwrap_or(Overflow::Error);
        let dz = p.div_zero.unwrap_or(hir_lang::DivZero::Error);
        let sh = p.shift.unwrap_or(hir_lang::Shift::Error);
        use OpKind as K;
        match op.kind {
            K::Add | K::Sub | K::Mul | K::Div | K::Rem | K::FloorDiv | K::FloorMod => {
                arith(op.kind, &x, &y, over, dz, node)
            }
            K::Neg => match x {
                V::Int(i) => match i.checked_neg() {
                    Some(r) => Ok(V::Int(r)),
                    None => overflowed(over, i128::from(i).wrapping_neg(), i64::MIN, node),
                },
                V::Float(f) => Ok(V::Float(-f)),
                _ => err(TYPE_ERROR, node),
            },
            K::And | K::Or | K::Xor => match (&x, &y) {
                (V::Bool(a), V::Bool(b)) => Ok(V::Bool(match op.kind {
                    K::And => *a & *b,
                    K::Or => *a | *b,
                    _ => *a ^ *b,
                })),
                (V::Int(a), V::Int(b)) => Ok(V::Int(match op.kind {
                    K::And => a & b,
                    K::Or => a | b,
                    _ => a ^ b,
                })),
                _ => err(TYPE_ERROR, node),
            },
            K::Not => Ok(V::Bool(!Self::truthy(&x))),
            K::BitNot => match x {
                V::Int(i) => Ok(V::Int(!i)),
                _ => err(TYPE_ERROR, node),
            },
            K::Pow => pow(&x, &y, over, node),
            K::Shl | K::Shr => match (&x, &y) {
                (V::Int(a), V::Int(n)) => {
                    let n = if *n < 0 || *n >= 64 {
                        match sh {
                            hir_lang::Shift::Error => return err(SHIFT, node),
                            hir_lang::Shift::Mask => n & 63,
                            hir_lang::Shift::Saturate if *n < 0 => return err(SHIFT, node),
                            hir_lang::Shift::Saturate => {
                                return Ok(V::Int(if op.kind == K::Shl || *a >= 0 {
                                    0
                                } else {
                                    -1
                                }));
                            }
                        }
                    } else {
                        *n
                    };
                    Ok(V::Int(if op.kind == K::Shl {
                        a.wrapping_shl(n as u32)
                    } else {
                        a >> n
                    }))
                }
                _ => err(TYPE_ERROR, node),
            },
            K::Eq | K::Ne => {
                let e = deq(&x, &y)?;
                Ok(V::Bool(if op.kind == K::Eq { e } else { !e }))
            }
            K::Lt | K::Le | K::Gt | K::Ge => {
                let (l, r) = if matches!(op.kind, K::Gt | K::Ge) {
                    (&y, &x)
                } else {
                    (&x, &y)
                };
                let o = dcmp(l, r, node)?;
                Ok(V::Bool(match op.kind {
                    K::Lt | K::Gt => o.is_some_and(|o| o.is_lt()),
                    _ => o.is_some_and(|o| o.is_le()),
                }))
            }
            K::Min | K::Max => match (&x, &y) {
                (V::Int(a), V::Int(b)) => Ok(V::Int(if op.kind == K::Min {
                    *a.min(b)
                } else {
                    *a.max(b)
                })),
                _ => {
                    let a = num_f(&x, node)?;
                    let b = num_f(&y, node)?;
                    Ok(V::Float(if a.is_nan() || b.is_nan() {
                        f64::NAN
                    } else if op.kind == K::Min {
                        if a == b {
                            if a.is_sign_negative() { a } else { b }
                        } else {
                            a.min(b)
                        }
                    } else if a == b {
                        if a.is_sign_positive() { a } else { b }
                    } else {
                        a.max(b)
                    }))
                }
            },
            K::Abs => match x {
                V::Int(i) => match i.checked_abs() {
                    Some(r) => Ok(V::Int(r)),
                    None => overflowed(over, 1i128 << 63, i64::MIN, node),
                },
                V::Float(f) => Ok(V::Float(f.abs())),
                _ => err(TYPE_ERROR, node),
            },
            K::Sqrt => Ok(V::Float(num_f(&x, node)?.sqrt())),
            K::Floor => Ok(V::Float(num_f(&x, node)?.floor())),
            K::Ceil => Ok(V::Float(num_f(&x, node)?.ceil())),
            K::Trunc => Ok(V::Float(num_f(&x, node)?.trunc())),
            K::Round => Ok(V::Float(num_f(&x, node)?.round())),
            K::RoundEven => Ok(V::Float(num_f(&x, node)?.round_ties_even())),
            K::IntCast(t) => {
                let V::Int(i) = x else {
                    return err(TYPE_ERROR, node);
                };
                let r = int_cast(i128::from(i), t, over, node)?;
                box_int(r, t, node)
            }
            K::IntToFloat(t) => {
                let V::Int(i) = x else {
                    return err(TYPE_ERROR, node);
                };
                Ok(V::Float(if t == Prim::F32 {
                    f64::from(i as f32)
                } else {
                    i as f64
                }))
            }
            K::F64ToF32 => {
                let V::Float(f) = x else {
                    return err(TYPE_ERROR, node);
                };
                Ok(V::Float(f64::from(f as f32)))
            }
            K::F32ToF64 => {
                let V::Float(f) = x else {
                    return err(TYPE_ERROR, node);
                };
                Ok(V::Float(f))
            }
            K::BoolToInt(t) => {
                let V::Bool(b) = x else {
                    return err(TYPE_ERROR, node);
                };
                box_int(i128::from(b), t, node)
            }
            K::Fma => {
                let z = a.get(2).cloned().unwrap_or(V::Nil);
                let p = num_f(&x, node)?;
                let q = num_f(&y, node)?;
                let r = num_f(&z, node)?;
                Ok(V::Float(p.mul_add(q, r)))
            }
            K::TotalCmp => {
                // Dynamic floats hold one canonical NaN (the sign is not
                // kept): what totalOrder sees.
                let a = canon(num_f(&x, node)?);
                let b = canon(num_f(&y, node)?);
                Ok(V::Int(a.total_cmp(&b) as i64))
            }
            K::FloatToInt(t) => {
                let V::Float(f) = x else {
                    return err(TYPE_ERROR, node);
                };
                let r = float_to_int(
                    f,
                    t,
                    p.float_to_int.unwrap_or(hir_lang::FloatToInt::Error),
                    node,
                )?;
                box_int(r, t, node)
            }
            K::Narrow(t) => {
                let V::Int(i) = x else {
                    return err(TYPE_ERROR, node);
                };
                let r = int_cast(i128::from(i), t, Overflow::Wrap, node)?;
                box_int(r, t, node)
            }
            K::Zext(t) | K::Sext(t) => {
                let V::Int(i) = x else {
                    return err(TYPE_ERROR, node);
                };
                // i64 to a 64-bit type: zext reinterprets as unsigned.
                let r = if matches!(op.kind, K::Zext(_)) && matches!(t, Prim::U64 | Prim::Usize) {
                    i128::from(i as u64)
                } else {
                    i128::from(i)
                };
                box_int(r, t, node)
            }
            K::Bitcast(t) => match (t, x) {
                (Prim::F64, V::Int(i)) => Ok(V::Float(f64::from_bits(i as u64))),
                (Prim::I64 | Prim::Isize, V::Float(f)) => Ok(V::Int(canon(f).to_bits() as i64)),
                (Prim::U64 | Prim::Usize, V::Float(f)) => {
                    box_int(i128::from(canon(f).to_bits()), t, node)
                }
                _ => err(TYPE_ERROR, node),
            },
            K::CharFromU32 => {
                let V::Int(i) = x else {
                    return err(TYPE_ERROR, node);
                };
                let Ok(u) = u32::try_from(i) else {
                    return err(ARITH_OVERFLOW, node);
                };
                match char::from_u32(u) {
                    Some(c) => Ok(V::Char(c)),
                    None => err(INVALID_CHAR, node),
                }
            }
            _ => Err(Sig::Unspecified),
        }
    }

    fn cast(&mut self, v: V, ty: TyId, pol: hir_lang::Policy, node: NodeRef) -> R<V> {
        let hir = self.hir;
        let (ty, nullable) = match *hir.ty(ty) {
            Ty::Nullable(t) => (t, true),
            _ => (ty, false),
        };
        if nullable && matches!(v, V::Nil) {
            return Ok(V::Nil);
        }
        let p = match *hir.ty(ty) {
            Ty::Any | Ty::Infer => return Ok(v),
            Ty::Union(_) | Ty::Intersection(_) => {
                return if self.type_ok(ty, &v)? {
                    Ok(v)
                } else {
                    err(TYPE_ERROR, node)
                };
            }
            Ty::Prim(p) => p,
            _ => return Err(Sig::Unspecified),
        };
        match p {
            Prim::Bool => Ok(V::Bool(Self::truthy(&v))),
            Prim::Str => match v {
                V::Str(_) => Ok(v),
                _ => err(TYPE_ERROR, node),
            },
            Prim::F64 | Prim::F32 => match v {
                V::Bool(b) => Ok(V::Float(if b { 1.0 } else { 0.0 })),
                V::Int(i) => {
                    let f = i as f64;
                    Ok(V::Float(if p == Prim::F32 {
                        f64::from(f as f32)
                    } else {
                        f
                    }))
                }
                V::Float(f) => Ok(V::Float(if p == Prim::F32 {
                    f64::from(f as f32)
                } else {
                    f
                })),
                _ => err(TYPE_ERROR, node),
            },
            Prim::Char => match v {
                V::Char(_) => Ok(v),
                V::Int(i) => {
                    let Ok(u) = u32::try_from(i) else {
                        return err(ARITH_OVERFLOW, node);
                    };
                    match char::from_u32(u) {
                        Some(c) => Ok(V::Char(c)),
                        None => err(INVALID_CHAR, node),
                    }
                }
                _ => err(TYPE_ERROR, node),
            },
            t => {
                let r = match v {
                    V::Int(i) => int_cast(
                        i128::from(i),
                        t,
                        pol.overflow.unwrap_or(Overflow::Error),
                        node,
                    )?,
                    V::Float(f) => float_to_int(
                        f,
                        t,
                        pol.float_to_int.unwrap_or(hir_lang::FloatToInt::Error),
                        node,
                    )?,
                    V::Bool(b) => i128::from(b),
                    _ => return err(TYPE_ERROR, node),
                };
                box_int(r, t, node)
            }
        }
    }

    fn intrinsic(&mut self, name: &str, a: &[V], node: NodeRef) -> R<V> {
        let x = a.first().cloned().unwrap_or(V::Nil);
        match name {
            "concat" => match (&x, a.get(1)) {
                (V::Str(p), Some(V::Str(q))) => {
                    let mut s = p.as_ref().clone();
                    s.extend_from_slice(q);
                    Ok(V::Str(Rc::new(s)))
                }
                _ => err(TYPE_ERROR, node),
            },
            "len" => match &x {
                V::Str(s) => Ok(V::Int(s.len() as i64)),
                V::Map(m) => Ok(V::Int(m.borrow().entries.len() as i64)),
                _ => err(TYPE_ERROR, node),
            },
            "truthy" => Ok(V::Bool(Self::truthy(&x))),
            "lnot" => Ok(V::Bool(!Self::truthy(&x))),
            "type_of" => Ok(V::Int(i64::from(Self::kind(&x)))),
            "iter" => match &x {
                V::Map(m) => {
                    let map = if self.cfg.php_arrays {
                        match deep_copy(&x) {
                            V::Map(c) => c,
                            _ => m.clone(),
                        }
                    } else {
                        m.clone()
                    };
                    Ok(V::Iter(Rc::new(RefCell::new(IterState { map, pos: 0 }))))
                }
                _ => err(TYPE_ERROR, node),
            },
            "iter_next" => match &x {
                V::Iter(it) => {
                    let mut it = it.borrow_mut();
                    let e = it.map.borrow().entries.get(it.pos).cloned();
                    match e {
                        None => Ok(V::Nil),
                        Some((k, v)) => {
                            it.pos += 1;
                            let m = Rc::new(RefCell::new(MapData::default()));
                            map_push(&m, key_value(&k), node)?;
                            map_push(&m, self.copy(&v), node)?;
                            Ok(V::Map(m))
                        }
                    }
                }
                _ => err(TYPE_ERROR, node),
            },
            _ => Err(Sig::Unspecified),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Av {
    Val(V),
    Cell(Cell),
}

impl Av {
    fn value(&self) -> V {
        match self {
            Av::Val(v) => v.clone(),
            Av::Cell(c) => c.borrow().clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Step {
    Index,
    Dyn,
    Prop(Vec<u8>),
    Elem(u32),
    Append,
}

trait ItemKindOf {
    /// `Some(true)` when the resolution names a function (not assignable).
    fn item_kind_of(&self, res: Res) -> Option<bool>;
}

impl ItemKindOf for Hir {
    fn item_kind_of(&self, res: Res) -> Option<bool> {
        match res {
            Res::Def(d) => match d.def() {
                hir_lang::Def::Item(i) => Some(matches!(self.item(i).kind, ItemKind::Fn(_))),
                _ => None,
            },
            _ => None,
        }
    }
}

// ---------------------------------------------------------------- maps

pub fn deep_copy(v: &V) -> V {
    match v {
        V::Map(m) => {
            let d = m.borrow();
            let entries = d
                .entries
                .iter()
                .map(|(k, x)| (k.clone(), deep_copy(x)))
                .collect();
            V::Map(Rc::new(RefCell::new(MapData {
                entries,
                next: d.next,
            })))
        }
        v => v.clone(),
    }
}

fn key_of(v: &V) -> R<Key> {
    Ok(match v {
        V::Nil => Key::Nil,
        V::Bool(b) => Key::Bool(*b),
        V::Int(i) => Key::Int(*i),
        V::Float(f) => Key::Float(if f.is_nan() {
            f64::NAN.to_bits()
        } else if *f == 0.0 {
            0
        } else {
            f.to_bits()
        }),
        V::Char(c) => Key::Char(*c),
        V::Str(s) => Key::Str(s.as_ref().clone()),
        _ => return Err(Sig::Unspecified),
    })
}

fn key_value(k: &Key) -> V {
    match k {
        Key::Nil => V::Nil,
        Key::Bool(b) => V::Bool(*b),
        Key::Int(i) => V::Int(*i),
        Key::Float(b) => V::Float(f64::from_bits(*b)),
        Key::Char(c) => V::Char(*c),
        Key::Str(s) => V::Str(Rc::new(s.clone())),
    }
}

fn map_find(m: &Rc<RefCell<MapData>>, k: &Key) -> Option<V> {
    m.borrow()
        .entries
        .iter()
        .find(|(x, _)| x == k)
        .map(|(_, v)| v.clone())
}

fn map_set(m: &Rc<RefCell<MapData>>, k: Key, v: V) {
    let mut d = m.borrow_mut();
    if let Key::Int(i) = k {
        // `next` records the largest integer key ever inserted.
        d.next = Some(match d.next {
            Some(x) if x >= i => x,
            _ => i,
        });
    }
    match d.entries.iter_mut().find(|(x, _)| *x == k) {
        Some(e) => e.1 = v,
        None => d.entries.push((k, v)),
    }
}

/// `map_push`: under one more than the largest integer key ever inserted
/// (0 if none); past `i64::MAX` it is `ArithOverflow`.
fn map_push(m: &Rc<RefCell<MapData>>, v: V, node: NodeRef) -> R<()> {
    let next = match m.borrow().next {
        None => 0,
        Some(x) => match x.checked_add(1) {
            Some(n) => n,
            None => return err(ARITH_OVERFLOW, node),
        },
    };
    map_set(m, Key::Int(next), v);
    Ok(())
}

// ---------------------------------------------------------------- semantics

/// A PHP canonical integer string.
pub fn canonical_int(s: &[u8]) -> Option<i64> {
    let t = std::str::from_utf8(s).ok()?;
    if t.is_empty() || t.len() > 20 {
        return None;
    }
    let digits = t.strip_prefix('-').unwrap_or(t);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if digits.starts_with('0') && (digits.len() > 1 || t.starts_with('-')) {
        return None;
    }
    t.parse::<i64>().ok()
}

pub fn deq(a: &V, b: &V) -> R<bool> {
    Ok(match (a, b) {
        (V::Int(x), V::Int(y)) => x == y,
        (V::Float(x), V::Float(y)) => x == y,
        (V::Int(i), V::Float(f)) | (V::Float(f), V::Int(i)) => {
            cmp_int_float(*i, *f) == Some(std::cmp::Ordering::Equal)
        }
        (V::Nil, V::Nil) => true,
        (V::Bool(x), V::Bool(y)) => x == y,
        (V::Char(x), V::Char(y)) => x == y,
        (V::Str(x), V::Str(y)) => x == y,
        // Identity of heap objects: what copies share is not specified.
        (V::Map(_), V::Map(_))
        | (V::Func(_), V::Func(_))
        | (V::Iter(_), V::Iter(_))
        | (V::Error(..), V::Error(..)) => {
            return Err(Sig::Unspecified);
        }
        _ => false,
    })
}

/// Exact comparison of an integer and a float (`None` for NaN).
fn cmp_int_float(i: i64, f: f64) -> Option<std::cmp::Ordering> {
    if f.is_nan() {
        return None;
    }
    if f >= 9_223_372_036_854_775_808.0 {
        return Some(std::cmp::Ordering::Less);
    }
    if f < -9_223_372_036_854_775_808.0 {
        return Some(std::cmp::Ordering::Greater);
    }
    let t = f.trunc();
    let ti = t as i64;
    match i.cmp(&ti) {
        std::cmp::Ordering::Equal => {
            let frac = f - t;
            Some(if frac > 0.0 {
                std::cmp::Ordering::Less
            } else if frac < 0.0 {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            })
        }
        o => Some(o),
    }
}

fn dcmp(a: &V, b: &V, node: NodeRef) -> R<Option<std::cmp::Ordering>> {
    Ok(match (a, b) {
        (V::Int(x), V::Int(y)) => Some(x.cmp(y)),
        (V::Float(x), V::Float(y)) => x.partial_cmp(y),
        (V::Int(i), V::Float(f)) => cmp_int_float(*i, *f),
        (V::Float(f), V::Int(i)) => cmp_int_float(*i, *f).map(std::cmp::Ordering::reverse),
        (V::Str(x), V::Str(y)) => Some(x.as_slice().cmp(y.as_slice())),
        (V::Char(x), V::Char(y)) => Some(x.cmp(y)),
        _ => return err(TYPE_ERROR, node),
    })
}

/// The canonical NaN of a dynamic float.
fn canon(f: f64) -> f64 {
    if f.is_nan() { f64::NAN } else { f }
}

fn num_f(v: &V, node: NodeRef) -> R<f64> {
    match v {
        V::Int(i) => Ok(*i as f64),
        V::Float(f) => Ok(*f),
        _ => err(TYPE_ERROR, node),
    }
}

/// The result of an overflowing integer op under `over`; `exact` is the
/// mathematical result, `wrapped` the two's-complement one.
fn overflowed(over: Overflow, exact: i128, wrapped: i64, node: NodeRef) -> R<V> {
    match over {
        Overflow::Error => err(ARITH_OVERFLOW, node),
        Overflow::Trap => Err(Sig::Trap(ARITH_OVERFLOW, node)),
        Overflow::Wrap => Ok(V::Int(wrapped)),
        Overflow::Promote => Ok(V::Float(exact as f64)),
    }
}

fn div_zero(dz: hir_lang::DivZero, node: NodeRef) -> R<V> {
    match dz {
        hir_lang::DivZero::Error => err(DIV_BY_ZERO, node),
        hir_lang::DivZero::Trap => Err(Sig::Trap(DIV_BY_ZERO, node)),
    }
}

/// The `f64` nearest the rational `n / d` (`d != 0`), correctly rounded.
fn div_round(n: i128, d: i128) -> f64 {
    let neg = (n < 0) != (d < 0);
    let (mut n, d) = (n.unsigned_abs(), d.unsigned_abs());
    // Scale so the quotient has at least 66 significant bits, then fold the
    // remainder into a sticky bit: the conversion rounds correctly.
    let mut shift = 0i32;
    while n / d < (1u128 << 66) && n.leading_zeros() > 1 {
        n <<= 1;
        shift += 1;
    }
    let q = n / d;
    let r = n % d;
    let q = q | u128::from(r != 0);
    let f = q as f64 * 2f64.powi(-shift);
    if neg { -f } else { f }
}

fn arith(k: OpKind, x: &V, y: &V, over: Overflow, dz: hir_lang::DivZero, node: NodeRef) -> R<V> {
    use OpKind as K;
    match (x, y) {
        (V::Int(a), V::Int(b)) => {
            let (a, b) = (*a, *b);
            let (wa, wb) = (i128::from(a), i128::from(b));
            match k {
                K::Add | K::Sub | K::Mul => {
                    let exact = match k {
                        K::Add => wa + wb,
                        K::Sub => wa - wb,
                        _ => wa * wb,
                    };
                    match i64::try_from(exact) {
                        Ok(r) => Ok(V::Int(r)),
                        Err(_) => overflowed(over, exact, exact as i64, node),
                    }
                }
                K::Div => {
                    if b == 0 {
                        return div_zero(dz, node);
                    }
                    if a == i64::MIN && b == -1 {
                        return match over {
                            Overflow::Promote => Ok(V::Float(9_223_372_036_854_775_808.0)),
                            o => overflowed(o, 1i128 << 63, i64::MIN, node),
                        };
                    }
                    if over == Overflow::Promote && a % b != 0 {
                        return Ok(V::Float(div_round(wa, wb)));
                    }
                    Ok(V::Int(a / b))
                }
                K::Rem => {
                    if b == 0 {
                        return div_zero(dz, node);
                    }
                    Ok(V::Int(a.wrapping_rem(b)))
                }
                K::FloorDiv => {
                    if b == 0 {
                        return div_zero(dz, node);
                    }
                    if a == i64::MIN && b == -1 {
                        return overflowed(over, 1i128 << 63, i64::MIN, node);
                    }
                    Ok(V::Int(
                        a.div_euclid(b) - i64::from(b < 0 && a.rem_euclid(b) != 0),
                    ))
                }
                K::FloorMod => {
                    if b == 0 {
                        return div_zero(dz, node);
                    }
                    let m = a.wrapping_rem(b);
                    Ok(V::Int(if m != 0 && ((m < 0) != (b < 0)) {
                        m + b
                    } else {
                        m
                    }))
                }
                _ => err(TYPE_ERROR, node),
            }
        }
        (V::Int(_) | V::Float(_), V::Int(_) | V::Float(_)) => {
            let a = num_f(x, node)?;
            let b = num_f(y, node)?;
            Ok(V::Float(match k {
                K::Add => a + b,
                K::Sub => a - b,
                K::Mul => a * b,
                K::Div => a / b,
                K::Rem => a % b,
                K::FloorDiv => py_divmod(a, b).0,
                _ => py_divmod(a, b).1,
            }))
        }
        _ => err(TYPE_ERROR, node),
    }
}

/// CPython's float `//` and `%` (LSB §5.6).
fn py_divmod(a: f64, b: f64) -> (f64, f64) {
    let mut m = a % b;
    let mut q = (a - m) / b;
    if m != 0.0 || m.is_nan() {
        if (b < 0.0) != (m < 0.0) {
            m += b;
            q -= 1.0;
        }
    } else {
        m = 0.0f64.copysign(b);
    }
    let fq = if q != 0.0 || q.is_nan() {
        let mut fq = q.floor();
        if q - fq > 0.5 {
            fq += 1.0;
        }
        fq
    } else {
        0.0f64.copysign(a / b)
    };
    (fq, m)
}

fn int_range(t: Prim) -> (i128, i128) {
    match t {
        Prim::I8 => (i128::from(i8::MIN), i128::from(i8::MAX)),
        Prim::I16 => (i128::from(i16::MIN), i128::from(i16::MAX)),
        Prim::I32 => (i128::from(i32::MIN), i128::from(i32::MAX)),
        Prim::U8 => (0, i128::from(u8::MAX)),
        Prim::U16 => (0, i128::from(u16::MAX)),
        Prim::U32 => (0, i128::from(u32::MAX)),
        Prim::U64 | Prim::Usize => (0, i128::from(u64::MAX)),
        _ => (i128::from(i64::MIN), i128::from(i64::MAX)),
    }
}

fn int_cast(v: i128, t: Prim, over: Overflow, node: NodeRef) -> R<i128> {
    let (lo, hi) = int_range(t);
    if v >= lo && v <= hi {
        return Ok(v);
    }
    match over {
        Overflow::Error | Overflow::Promote => err(ARITH_OVERFLOW, node),
        Overflow::Trap => Err(Sig::Trap(ARITH_OVERFLOW, node)),
        Overflow::Wrap => {
            let bits = match t {
                Prim::I8 | Prim::U8 => 8,
                Prim::I16 | Prim::U16 => 16,
                Prim::I32 | Prim::U32 => 32,
                _ => 64,
            };
            let m = v & ((1i128 << bits) - 1);
            Ok(if lo < 0 && m >= (1i128 << (bits - 1)) {
                m - (1i128 << bits)
            } else {
                m
            })
        }
    }
}

fn float_to_int(f: f64, t: Prim, pol: hir_lang::FloatToInt, node: NodeRef) -> R<i128> {
    let (lo, hi) = int_range(t);
    let tr = f.trunc();
    if f.is_nan() || tr < lo as f64 || tr > hi as f64 || (tr >= hi as f64 && hi as f64 != tr) {
        return match pol {
            hir_lang::FloatToInt::Error => err(INVALID_CONV, node),
            hir_lang::FloatToInt::Saturate => Ok(if f.is_nan() {
                0
            } else if f < 0.0 {
                lo
            } else {
                hi
            }),
        };
    }
    let r = tr as i128;
    if r < lo || r > hi {
        return match pol {
            hir_lang::FloatToInt::Error => err(INVALID_CONV, node),
            hir_lang::FloatToInt::Saturate => Ok(if r < lo { lo } else { hi }),
        };
    }
    Ok(r)
}

/// An integer of type `t` as a dynamic value (`i64`; a `u64` above
/// `i64::MAX` does not fit: `ArithOverflow`).
fn box_int(v: i128, _t: Prim, node: NodeRef) -> R<V> {
    match i64::try_from(v) {
        Ok(i) => Ok(V::Int(i)),
        Err(_) => err(ARITH_OVERFLOW, node),
    }
}

/// How `echo` prints a value (the test host does the same).
pub fn show(v: &V) -> String {
    match v {
        V::Nil => String::new(),
        V::Bool(true) => "1".into(),
        V::Bool(false) => String::new(),
        V::Int(i) => i.to_string(),
        V::Float(f) => format!("{f:?}"),
        V::Char(c) => c.to_string(),
        V::Str(s) => String::from_utf8_lossy(s).into_owned(),
        V::Map(_) => "Array".into(),
        V::Func(_) => "Closure".into(),
        V::Error(c, _) => format!("E{c:04}"),
        V::Iter(_) => "Iterator".into(),
    }
}

pub fn to_rv(v: &V, depth: usize) -> RV {
    match v {
        V::Nil => RV::Nil,
        V::Bool(b) => RV::Bool(*b),
        V::Int(i) => RV::Int(*i),
        V::Float(f) => RV::float(*f),
        V::Char(c) => RV::Char(*c),
        V::Str(s) => RV::Str(s.as_ref().clone()),
        V::Map(m) if depth < 16 => RV::Map(
            m.borrow()
                .entries
                .iter()
                .map(|(k, x)| (to_rv(&key_value(k), depth + 1), to_rv(x, depth + 1)))
                .collect(),
        ),
        V::Map(_) => RV::Other(7),
        V::Func(_) => RV::Func,
        V::Error(c, _) => RV::Error(*c),
        V::Iter(_) => RV::Other(11),
    }
}

/// OPS v2 `pow` on dynamic values (LSB `dpow`). Results the oracle cannot
/// compute exactly (a float power, or a promoted power beyond `i128`) are
/// unspecified: the float routine is the family's `ls_pow`, which the VM
/// tests itself.
fn pow(x: &V, y: &V, over: Overflow, node: NodeRef) -> R<V> {
    match (x, y) {
        (V::Int(b), V::Int(e)) if *e >= 0 && matches!(*b, -1..=1) => Ok(V::Int(match *b {
            0 if *e == 0 => 1,
            -1 if *e % 2 == 1 => -1,
            -1 => 1,
            b => b,
        })),
        (V::Int(_), V::Int(e)) if *e < 0 => match over {
            Overflow::Promote => Err(Sig::Unspecified),
            _ => err(NEG_EXPONENT, node),
        },
        (V::Int(b), V::Int(e)) => {
            let exact = u32::try_from(*e)
                .ok()
                .and_then(|e| i128::from(*b).checked_pow(e));
            match exact {
                Some(r) => match i64::try_from(r) {
                    Ok(v) => Ok(V::Int(v)),
                    Err(_) => match over {
                        Overflow::Wrap => Ok(V::Int(b.wrapping_pow(*e as u32))),
                        Overflow::Promote => Ok(V::Float(r as f64)),
                        Overflow::Trap => Err(Sig::Trap(ARITH_OVERFLOW, node)),
                        Overflow::Error => err(ARITH_OVERFLOW, node),
                    },
                },
                // |b| >= 2 with a huge exponent: does not fit.
                None => match over {
                    Overflow::Wrap => {
                        let mut acc: i64 = 1;
                        let mut base = *b;
                        let mut n = *e as u64;
                        while n > 0 {
                            if n & 1 == 1 {
                                acc = acc.wrapping_mul(base);
                            }
                            base = base.wrapping_mul(base);
                            n >>= 1;
                        }
                        Ok(V::Int(acc))
                    }
                    Overflow::Promote => Err(Sig::Unspecified),
                    Overflow::Trap => Err(Sig::Trap(ARITH_OVERFLOW, node)),
                    Overflow::Error => err(ARITH_OVERFLOW, node),
                },
            }
        }
        (V::Int(_) | V::Float(_), V::Int(_) | V::Float(_)) => Err(Sig::Unspecified),
        _ => err(TYPE_ERROR, node),
    }
}
