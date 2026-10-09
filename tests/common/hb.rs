//! A terse HIR builder for tests: every node gets its own span, names are
//! interned on the way, and paths are created resolved.

#![allow(dead_code)]

use hir_lang::{
    Arg, ArgKind, Arm, Binder, BinderId, BinderKind, Block, Builder, Capture, CaptureMode, Closure,
    Def, DefaultEval, Effects, Expr, ExprId, FloatLit, FnDef, Hir, Ident, IntLit, Item, ItemId,
    ItemKind, Lit, MapEntry, Member, Name, Ns, Op, OpKind, Param, ParamId, ParamKind, Pat, PatId,
    Path, Res, Segment, Span, Stmt, StmtId, TyId,
};
use intern_lang::Interner;

pub struct H {
    pub b: Builder,
    pub names: Interner,
    pos: u32,
}

impl Default for H {
    fn default() -> Self {
        Self::new()
    }
}

impl H {
    pub fn new() -> Self {
        H {
            b: Builder::new(),
            names: Interner::new(),
            pos: 0,
        }
    }

    /// Advances the builder's span, so every node has its own.
    pub fn tick(&mut self) {
        self.pos += 2;
        self.b.set_span(Span::new(self.pos, self.pos + 1));
    }

    pub fn name(&mut self, s: &str) -> Name {
        Name::new(self.names.intern(s))
    }

    pub fn ident(&mut self, s: &str) -> Ident {
        Ident::new(self.names.intern(s), Span::empty(0))
    }

    pub fn local(&mut self, s: &str) -> BinderId {
        let n = self.name(s);
        self.b
            .binder(Binder::new(n, BinderKind::Local).with_mutable(true))
    }

    pub fn label(&mut self, s: &str) -> BinderId {
        let n = self.name(s);
        self.b.binder(Binder::new(n, BinderKind::Label))
    }

    // -------------------------------------------------------------- literals

    pub fn int(&mut self, v: i64) -> ExprId {
        self.tick();
        self.b.lit(Lit::Int(IntLit::signed(v)))
    }

    pub fn float(&mut self, v: f64) -> ExprId {
        self.tick();
        self.b.lit(Lit::Float(FloatLit::new(v)))
    }

    pub fn str(&mut self, s: &str) -> ExprId {
        self.tick();
        self.b.str_lit(s)
    }

    pub fn boolean(&mut self, v: bool) -> ExprId {
        self.tick();
        self.b.lit(Lit::Bool(v))
    }

    pub fn nil(&mut self) -> ExprId {
        self.tick();
        self.b.lit(Lit::Null)
    }

    pub fn ch(&mut self, c: char) -> ExprId {
        self.tick();
        self.b.lit(Lit::Char(c))
    }

    pub fn lit(&mut self, l: Lit) -> ExprId {
        self.tick();
        self.b.lit(l)
    }

    // -------------------------------------------------------------- paths

    pub fn var(&mut self, b: BinderId) -> ExprId {
        self.tick();
        self.b.use_binder(b)
    }

    pub fn path(&mut self, name: &str, res: Res) -> hir_lang::PathId {
        self.tick();
        let n = self.name(name);
        let seg = Segment::new(n, self.b.origin());
        let segs = self.b.list(&[seg]);
        self.b.path(Path {
            res,
            ..Path::new(segs, Ns::Value)
        })
    }

    pub fn path_ns(&mut self, name: &str, ns: Ns, res: Res) -> hir_lang::PathId {
        self.tick();
        let n = self.name(name);
        let seg = Segment::new(n, self.b.origin());
        let segs = self.b.list(&[seg]);
        self.b.path(Path {
            res,
            ..Path::new(segs, ns)
        })
    }

    pub fn constant(&mut self, name: &str, value: ExprId) -> ItemId {
        self.tick();
        let n = self.name(name);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Const {
                ty: None,
                value: Some(value),
            },
        ))
    }

    pub fn item_ref(&mut self, name: &str, item: ItemId) -> ExprId {
        let d = self.b.def(Def::Item(item));
        let p = self.path(name, Res::Def(d));
        self.b.expr(Expr::Path(p))
    }

    pub fn extern_ref(&mut self, name: &str) -> ExprId {
        let sym = self.names.intern(name);
        let p = self.path(name, Res::Extern(sym));
        self.b.expr(Expr::Path(p))
    }

    // -------------------------------------------------------------- operations

    pub fn op(&mut self, k: OpKind, args: &[ExprId]) -> ExprId {
        self.tick();
        self.b.op(k, args)
    }

    pub fn op_with(&mut self, op: Op, args: &[ExprId]) -> ExprId {
        self.tick();
        self.b.op_with(op, args)
    }

    pub fn expr(&mut self, e: Expr) -> ExprId {
        self.tick();
        self.b.expr(e)
    }

    pub fn intrinsic(&mut self, name: &str, args: &[ExprId]) -> ExprId {
        let sym = self.names.intern(name);
        let args = self.b.list(args);
        self.expr(Expr::Intrinsic {
            kind: hir_lang::Intrinsic::Named(sym),
            generic_args: hir_lang::List::EMPTY,
            args,
        })
    }

    pub fn index(&mut self, base: ExprId, index: ExprId) -> ExprId {
        self.expr(Expr::Index { base, index })
    }

    pub fn field(&mut self, base: ExprId, name: &str) -> ExprId {
        let sym = self.names.intern(name);
        self.expr(Expr::Field {
            base,
            member: Member::Named(sym),
            span: Span::empty(0),
        })
    }

    pub fn append(&mut self, base: ExprId) -> ExprId {
        self.expr(Expr::Append(base))
    }

    pub fn assign(&mut self, target: ExprId, value: ExprId) -> ExprId {
        self.expr(Expr::Assign {
            target,
            op: None,
            value,
        })
    }

    pub fn compound(&mut self, target: ExprId, op: Op, value: ExprId) -> ExprId {
        self.expr(Expr::Assign {
            target,
            op: Some(op),
            value,
        })
    }

    pub fn array(&mut self, elems: &[ExprId]) -> ExprId {
        let l = self.b.list(elems);
        self.expr(Expr::Array(l))
    }

    pub fn map(&mut self, entries: &[(Option<ExprId>, ExprId)]) -> ExprId {
        let es: Vec<MapEntry> = entries
            .iter()
            .map(|&(key, value)| MapEntry { key, value })
            .collect();
        let l = self.b.list(&es);
        self.expr(Expr::Map(l))
    }

    // -------------------------------------------------------------- calls

    pub fn call(&mut self, callee: ExprId, args: &[ExprId]) -> ExprId {
        self.tick();
        self.b.call(callee, args)
    }

    pub fn call_args(&mut self, callee: ExprId, args: &[Arg]) -> ExprId {
        let args = self.b.list(args);
        self.expr(Expr::Call { callee, args })
    }

    pub fn named(&mut self, name: &str, value: ExprId) -> Arg {
        let id = self.ident(name);
        Arg {
            kind: ArgKind::Named(id),
            value,
            place: false,
        }
    }

    pub fn method(&mut self, receiver: ExprId, name: &str, args: &[ExprId]) -> ExprId {
        let method = self.ident(name);
        let args: Vec<Arg> = args.iter().map(|&a| Arg::positional(a)).collect();
        let args = self.b.list(&args);
        self.expr(Expr::MethodCall {
            receiver,
            method,
            generic_args: hir_lang::List::EMPTY,
            args,
        })
    }

    // -------------------------------------------------------------- statements

    pub fn let_(&mut self, b: BinderId, init: Option<ExprId>) -> StmtId {
        self.tick();
        let p = self.b.bind(b);
        self.b.let_stmt(p, init)
    }

    pub fn let_pat(&mut self, pat: PatId, init: ExprId, else_: Option<ExprId>) -> StmtId {
        self.tick();
        self.b.stmt(Stmt::Let {
            pat,
            ty: None,
            init: Some(init),
            else_,
        })
    }

    pub fn stmt(&mut self, e: ExprId) -> StmtId {
        self.tick();
        self.b.expr_stmt(e)
    }

    pub fn raw_stmt(&mut self, s: Stmt) -> StmtId {
        self.tick();
        self.b.stmt(s)
    }

    pub fn block(&mut self, stmts: &[StmtId], tail: Option<ExprId>) -> ExprId {
        self.tick();
        self.b.block(stmts, tail)
    }

    pub fn labeled_block(
        &mut self,
        label: BinderId,
        stmts: &[StmtId],
        tail: Option<ExprId>,
    ) -> ExprId {
        let stmts = self.b.list(stmts);
        self.expr(Expr::Block(Block {
            stmts,
            tail,
            label: Some(label),
            is_unsafe: false,
        }))
    }

    pub fn if_(&mut self, cond: ExprId, then: ExprId, else_: Option<ExprId>) -> ExprId {
        self.expr(Expr::If { cond, then, else_ })
    }

    pub fn loop_(&mut self, label: Option<BinderId>, body: ExprId, step: Option<ExprId>) -> ExprId {
        self.expr(Expr::Loop { label, body, step })
    }

    pub fn brk(&mut self, label: Option<BinderId>, value: Option<ExprId>) -> ExprId {
        self.expr(Expr::Break { label, value })
    }

    pub fn cont(&mut self, label: Option<BinderId>) -> ExprId {
        self.expr(Expr::Continue { label })
    }

    pub fn ret(&mut self, v: Option<ExprId>) -> ExprId {
        self.expr(Expr::Return(v))
    }

    pub fn throw(&mut self, v: ExprId) -> ExprId {
        self.expr(Expr::Throw(v))
    }

    pub fn try_(&mut self, body: ExprId, catches: &[Arm], finally: Option<ExprId>) -> ExprId {
        let catches = self.b.list(catches);
        self.expr(Expr::Try {
            body,
            catches,
            finally,
        })
    }

    pub fn match_(&mut self, scrutinee: ExprId, arms: &[Arm]) -> ExprId {
        let arms = self.b.list(arms);
        self.expr(Expr::Match { scrutinee, arms })
    }

    // -------------------------------------------------------------- patterns

    pub fn pbind(&mut self, b: BinderId) -> PatId {
        self.tick();
        self.b.bind(b)
    }

    pub fn pat(&mut self, p: Pat) -> PatId {
        self.tick();
        self.b.pat(p)
    }

    pub fn arm(&mut self, pat: PatId, guard: Option<ExprId>, body: ExprId) -> Arm {
        Arm { pat, guard, body }
    }

    // -------------------------------------------------------------- functions

    pub fn param(
        &mut self,
        name: &str,
        kind: ParamKind,
        default: Option<ExprId>,
        by_ref: bool,
    ) -> (ParamId, BinderId) {
        self.tick();
        let n = self.name(name);
        let binder = self
            .b
            .binder(Binder::new(n, BinderKind::Param).with_mutable(true));
        let pat = self.b.bind(binder);
        let p = self.b.param(Param {
            pat,
            ty: None,
            default,
            kind,
            by_ref,
        });
        (p, binder)
    }

    pub fn func(
        &mut self,
        name: &str,
        params: &[ParamId],
        body: ExprId,
        defaults: DefaultEval,
    ) -> ItemId {
        self.tick();
        let n = self.name(name);
        let params = self.b.list(params);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Fn(FnDef {
                params,
                body: Some(body),
                effects: Effects::THROWS,
                defaults,
                ..FnDef::default()
            }),
        ))
    }

    pub fn global(&mut self, name: &str, init: Option<ExprId>) -> ItemId {
        self.tick();
        let n = self.name(name);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Global {
                ty: None,
                mutable: true,
                init,
            },
        ))
    }

    pub fn closure(
        &mut self,
        params: &[ParamId],
        body: ExprId,
        implicit: Option<CaptureMode>,
        captures: &[Capture],
        self_binder: Option<BinderId>,
        defaults: DefaultEval,
    ) -> ExprId {
        let params = self.b.list(params);
        let captures = self.b.list(captures);
        self.expr(Expr::Closure(Closure {
            params,
            ret: None,
            body,
            effects: Effects::THROWS,
            implicit,
            captures,
            self_binder,
            defaults,
        }))
    }

    pub fn capture(
        &mut self,
        outer: BinderId,
        name: &str,
        mode: CaptureMode,
    ) -> (Capture, BinderId) {
        let n = self.name(name);
        let p = self.path(name, Res::Local(outer));
        let binder = self
            .b
            .binder(Binder::new(n, BinderKind::Capture).with_mutable(true));
        (
            Capture {
                outer: p,
                binder,
                mode,
            },
            binder,
        )
    }

    pub fn self_binder(&mut self, name: &str) -> BinderId {
        let n = self.name(name);
        self.b.binder(Binder::new(n, BinderKind::Capture))
    }

    /// The root module, with items and a body; finishes the unit.
    pub fn finish(mut self, items: &[ItemId], body: Option<ExprId>) -> (Hir, Interner) {
        self.tick();
        let items = self.b.list(items);
        let root = self.b.item(Item::new(
            None,
            ItemKind::Module {
                items,
                body,
                effects: Effects::THROWS,
            },
        ));
        let hir = match self.b.finish(root) {
            Ok(h) => h,
            Err(e) => panic!("invalid HIR: {e}"),
        };
        (hir, self.names)
    }

    pub fn ty(&mut self, t: hir_lang::Ty) -> TyId {
        self.tick();
        self.b.ty(t)
    }
}
