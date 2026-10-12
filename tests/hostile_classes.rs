//! Hostile class graphs: random graphs of classes, interfaces, and mixins
//! (bases, interfaces, and mixins naming any item, earlier or later, so
//! cycles, wrong kinds, and dangling names appear; rules naming anything;
//! members of every kind and visibility; method bodies using every class
//! form), repaired by `finish_lenient` into valid HIR. Compiling never
//! panics; a module that compiles loads in bvm-lang, and running it under
//! budgets, on both memory profiles, never panics.

mod common;

use bcgen_lang::{BodyMode, Compiler, Intrinsics, Options};
use bvm_lang::{Host, Limits, Memory, Program, Vm};
use common::progs::Rng;
use hir_lang::{
    Arg, Binder, BinderId, BinderKind, Builder, ClassDef, Def, Effects, Expr, ExprId, FieldDef,
    FieldId, FnDef, Ident, InterfaceDef, Item, ItemId, ItemKind, Lit, Member, MixinAction,
    MixinRule, MixinUseDef, Name, Ns, Param, ParamKind, Pat, Path, PathRoot, Res, Segment, Span,
    Stmt, Ty, TyId, Vis,
};
use intern_lang::Interner;
use proptest::prelude::*;

const MEMBERS: &[&str] = &["a", "b", "c", "__construct", "__destruct", "__clone"];

/// A class made so far: its kind (0 class, 1 abstract, 2 mixin, 3
/// interface), name, and members (item, name).
type ClassInfo = (u64, String, Vec<(ItemId, String)>);

struct G {
    r: Rng,
    b: Builder,
    names: Interner,
    /// Class-like items made so far.
    classes: Vec<ItemId>,
    /// Per class made so far: its kind (0 class, 1 abstract, 2 mixin, 3
    /// interface), name, and members (item, name).
    info: Vec<ClassInfo>,
    /// Members of the class being made.
    current: Vec<(ItemId, String)>,
    /// Members made so far (any class's).
    members: Vec<ItemId>,
    /// Items the next class-like items will get, so bases can point ahead.
    made: usize,
    fuel: u32,
    /// Generating a class member (type-relative paths are valid only
    /// there).
    in_class: bool,
    /// The class being generated has a base (`parent::` is valid).
    has_parent: bool,
}

impl G {
    fn name(&mut self, s: &str) -> Name {
        Name::new(self.names.intern(s))
    }

    fn ident(&mut self, s: &str) -> Ident {
        Ident::new(self.names.intern(s), Span::empty(0))
    }

    fn member_name(&mut self) -> String {
        MEMBERS[self.r.below(MEMBERS.len() as u64) as usize].to_string()
    }

    /// A resolution to a random item: mostly an earlier class or member;
    /// now and then a guessed later one, or nothing.
    fn some_item(&mut self, pool: bool) -> Res {
        let list = if pool { &self.classes } else { &self.members };
        match self.r.below(40) {
            0 => Res::Unresolved,
            1 => {
                let guess = self.r.below(self.made as u64 + 8) as usize;
                match ItemId::from_index(guess) {
                    Some(i) => Res::Def(self.b.def(Def::Item(i))),
                    None => Res::Err,
                }
            }
            _ if !list.is_empty() => {
                let i = list[self.r.below(list.len() as u64) as usize];
                Res::Def(self.b.def(Def::Item(i)))
            }
            _ => Res::Unresolved,
        }
    }

    fn path(&mut self, root: PathRoot, segs: &[String], ns: Ns, res: Res) -> hir_lang::PathId {
        let segs: Vec<Segment> = segs
            .iter()
            .map(|s| {
                let n = self.name(s);
                Segment::new(n, self.b.origin())
            })
            .collect();
        let n = u32::try_from(segs.len()).unwrap_or(0);
        let list = self.b.list(&segs);
        let unresolved = if matches!(res, Res::Unresolved) && root != PathRoot::Relative {
            n
        } else {
            0
        };
        self.b.path(Path {
            root,
            res,
            unresolved,
            ..Path::new(list, ns)
        })
    }

    /// A type naming an earlier class-like item, usually of one of the
    /// `kinds`; rarely anything.
    fn class_ty_of(&mut self, kinds: &[u64]) -> Option<TyId> {
        let fit: Vec<usize> = (0..self.info.len())
            .filter(|&i| kinds.contains(&self.info[i].0))
            .collect();
        let (res, name) = if !fit.is_empty() && !self.r.chance(8) {
            let i = fit[self.r.below(fit.len() as u64) as usize];
            let d = self.b.def(Def::Item(self.classes[i]));
            (Res::Def(d), self.info[i].1.clone())
        } else if self.r.chance(2) {
            (self.some_item(true), format!("K{}", self.r.below(9)))
        } else {
            return None;
        };
        let p = self.path(PathRoot::Relative, &[name], Ns::Type, res);
        Some(self.b.ty(Ty::Path(p)))
    }

    fn class_ty(&mut self) -> TyId {
        match self.class_ty_of(&[0, 1, 3]) {
            Some(t) => t,
            None => self.b.ty(Ty::Any),
        }
    }

    /// A member path: `self::m`/`parent::m`/`static::m` left to the
    /// compiler, or `K::m` naming an earlier class and (resolved) one of its
    /// members, or by name only.
    fn member_path(&mut self, root: PathRoot) -> hir_lang::PathId {
        if root != PathRoot::Relative || self.info.is_empty() {
            let root = if root == PathRoot::Relative {
                PathRoot::SelfType
            } else {
                root
            };
            let m = self.member_name();
            return self.path(root, &[m], Ns::Value, Res::Unresolved);
        }
        let fit: Vec<usize> = (0..self.info.len())
            .filter(|&i| self.info[i].0 < 2)
            .collect();
        if fit.is_empty() {
            let m = self.member_name();
            let root = if self.in_class {
                PathRoot::SelfType
            } else {
                PathRoot::Relative
            };
            return self.path(root, &[m], Ns::Value, Res::Unresolved);
        }
        let i = fit[self.r.below(fit.len() as u64) as usize];
        let class = self.info[i].1.clone();
        let ms = self.info[i].2.clone();
        if !ms.is_empty() && self.r.chance(70) {
            let (item, m) = ms[self.r.below(ms.len() as u64) as usize].clone();
            let d = self.b.def(Def::Item(item));
            self.path(PathRoot::Relative, &[class, m], Ns::Value, Res::Def(d))
        } else {
            // `K::m` with only `K` resolved (left to the type).
            let d = self.b.def(Def::Item(self.classes[i]));
            let m = self.member_name();
            let segs: Vec<Segment> = [class, m]
                .iter()
                .map(|s| {
                    let n = self.name(s);
                    Segment::new(n, self.b.origin())
                })
                .collect();
            let list = self.b.list(&segs);
            self.b.path(Path {
                res: Res::Def(d),
                unresolved: 1,
                ..Path::new(list, Ns::Value)
            })
        }
    }

    fn lit(&mut self) -> ExprId {
        match self.r.below(3) {
            0 => self.b.int(self.r.below(10) as i64),
            1 => self.b.str_lit("s"),
            _ => self.b.lit(Lit::Null),
        }
    }

    fn this(&mut self, this: Option<BinderId>) -> ExprId {
        match this {
            Some(t) => self.b.use_binder(t),
            None => self.lit(),
        }
    }

    fn args(&mut self, d: u32, this: Option<BinderId>) -> Vec<Arg> {
        (0..self.r.below(3))
            .map(|_| Arg::positional(self.expr(d.saturating_sub(1), this)))
            .collect()
    }

    fn call(&mut self, callee: ExprId, d: u32, this: Option<BinderId>) -> ExprId {
        let args = self.args(d, this);
        let args = self.b.list(&args);
        self.b.expr(Expr::Call { callee, args })
    }

    fn intrinsic(&mut self, name: &str, args: &[ExprId], ty: Option<TyId>) -> ExprId {
        let sym = self.names.intern(name);
        let args = self.b.list(args);
        let generic_args = match ty {
            Some(t) => self.b.list(&[hir_lang::GenericArg::Ty(t)]),
            None => hir_lang::List::EMPTY,
        };
        self.b.expr(Expr::Intrinsic {
            kind: hir_lang::Intrinsic::Named(sym),
            generic_args,
            args,
        })
    }

    fn expr(&mut self, d: u32, this: Option<BinderId>) -> ExprId {
        if d == 0 || self.fuel == 0 {
            return self.lit();
        }
        self.fuel -= 1;
        let pick = self.r.below(16);
        // Outside a class, with no class to name yet, a class form has
        // nothing valid to refer to.
        if !self.in_class && self.info.is_empty() && matches!(pick, 4..=9 | 11 | 13) {
            return self.lit();
        }
        if !self.in_class && !self.info.iter().any(|x| x.0 < 2) && matches!(pick, 4 | 5 | 13) {
            return self.lit();
        }
        match pick {
            0 => self.this(this),
            // `$x->m(..)`.
            1 => {
                let receiver = self.expr(d - 1, this);
                let m = self.member_name();
                let method = self.ident(&m);
                let args = self.args(d, this);
                let args = self.b.list(&args);
                self.b.expr(Expr::MethodCall {
                    receiver,
                    method,
                    generic_args: hir_lang::List::EMPTY,
                    args,
                })
            }
            // `$x->p` (read).
            2 => {
                let base = self.expr(d - 1, this);
                let m = self.member_name();
                let sym = self.names.intern(&m);
                self.b.expr(Expr::Field {
                    base,
                    member: Member::Named(sym),
                    span: Span::empty(0),
                })
            }
            // `$x->p = v`, `$x->p[] = v`.
            3 => {
                let base = self.this(this);
                let m = self.member_name();
                let sym = self.names.intern(&m);
                let mut target = self.b.expr(Expr::Field {
                    base,
                    member: Member::Named(sym),
                    span: Span::empty(0),
                });
                if self.r.chance(30) {
                    target = self.b.expr(Expr::Append(target));
                }
                let value = self.expr(d - 1, this);
                self.b.expr(Expr::Assign {
                    target,
                    op: None,
                    value,
                })
            }
            // `self::m()`, `parent::m()`, `static::m()`, `K::m()`.
            4 | 5 => {
                let root = if self.in_class {
                    let parent = if self.has_parent {
                        PathRoot::ParentType
                    } else {
                        PathRoot::SelfType
                    };
                    self.r.pick(&[
                        PathRoot::SelfType,
                        PathRoot::SelfType,
                        parent,
                        PathRoot::StaticType,
                        PathRoot::Relative,
                    ])
                } else {
                    PathRoot::Relative
                };
                let p = self.member_path(root);
                let callee = self.b.expr(Expr::Path(p));
                self.call(callee, d, this)
            }
            // `static::$x = v`, `self::$x[] = v`.
            6 if self.in_class => {
                let root = self.r.pick(&[PathRoot::SelfType, PathRoot::StaticType]);
                let m = self.member_name();
                let res = if root == PathRoot::StaticType {
                    Res::Unresolved
                } else {
                    self.some_item(false)
                };
                let p = self.path(root, &[m], Ns::Value, res);
                let mut target = self.b.expr(Expr::Path(p));
                if self.r.chance(30) {
                    target = self.b.expr(Expr::Append(target));
                }
                let value = self.expr(d - 1, this);
                self.b.expr(Expr::Assign {
                    target,
                    op: None,
                    value,
                })
            }
            // `new K(..)`, `new (static::class)(..)`, `new $x(..)`.
            7 | 8 => {
                let f = {
                    let sym = self.names.intern("mox.new");
                    let p = self.path(
                        PathRoot::Relative,
                        &["mox.new".to_string()],
                        Ns::Value,
                        Res::Extern(sym),
                    );
                    self.b.expr(Expr::Path(p))
                };
                let cls = match self.r.below(3) {
                    0 => {
                        let fit: Vec<usize> = (0..self.info.len())
                            .filter(|&i| self.info[i].0 != 3)
                            .collect();
                        let (res, name) = if !fit.is_empty() && !self.r.chance(2) {
                            let i = fit[self.r.below(fit.len() as u64) as usize];
                            let d = self.b.def(Def::Item(self.classes[i]));
                            (Res::Def(d), self.info[i].1.clone())
                        } else {
                            (self.some_item(true), "K".into())
                        };
                        let p = self.path(PathRoot::Relative, &[name], Ns::Value, res);
                        self.b.expr(Expr::Path(p))
                    }
                    1 if self.in_class => {
                        let root = self.r.pick(&[
                            PathRoot::SelfType,
                            PathRoot::StaticType,
                            PathRoot::SelfType,
                        ]);
                        let p = self.path(root, &["class".into()], Ns::Value, Res::Unresolved);
                        self.b.expr(Expr::Path(p))
                    }
                    _ => self.expr(d - 1, this),
                };
                let mut args = vec![Arg::positional(cls)];
                args.extend(self.args(d, this));
                let args = self.b.list(&args);
                self.b.expr(Expr::Call { callee: f, args })
            }
            // `x instanceof K`, by type or by value.
            9 => {
                let x = self.expr(d - 1, this);
                if let Some(t) = self.class_ty_of(&[0, 1, 2, 3]) {
                    self.intrinsic("mox.instanceof", &[x], Some(t))
                } else {
                    let c = self.expr(d - 1, this);
                    self.intrinsic("mox.instanceof", &[x, c], None)
                }
            }
            10 => {
                let x = self.expr(d - 1, this);
                self.intrinsic("mox.clone", &[x], None)
            }
            // `try { throw x } catch (K $e) { .. }`.
            11 => {
                let x = self.expr(d - 1, this);
                let th = self.b.expr(Expr::Throw(x));
                let body = self.b.block(&[], Some(th));
                let ty = self.class_ty();
                let n = self.name("e");
                let eb = self
                    .b
                    .binder(Binder::new(n, BinderKind::Local).with_mutable(true));
                let bind = self.b.bind(eb);
                let pat = self.b.pat(Pat::TypeTest {
                    ty,
                    pat: Some(bind),
                });
                let cb = self.expr(d - 1, this);
                let arms = self.b.list(&[hir_lang::Arm {
                    pat,
                    guard: None,
                    body: cb,
                }]);
                self.b.expr(Expr::Try {
                    body,
                    catches: arms,
                    finally: None,
                })
            }
            // A closure using `$this` implicitly.
            12 => {
                let body = self.expr(d - 1, this);
                let params = hir_lang::List::EMPTY;
                let c = self.b.expr(Expr::Closure(hir_lang::Closure {
                    params,
                    ret: None,
                    body,
                    effects: Effects::THROWS,
                    implicit: Some(hir_lang::CaptureMode::ByValue),
                    captures: hir_lang::List::EMPTY,
                    self_binder: None,
                    defaults: hir_lang::DefaultEval::PerCall,
                }));
                self.call(c, d, this)
            }
            // `K::class`, `static::X`, `self::X`.
            13 => {
                let root = if self.in_class {
                    self.r
                        .pick(&[PathRoot::SelfType, PathRoot::StaticType, PathRoot::Relative])
                } else {
                    PathRoot::Relative
                };
                let p = if self.r.chance(30) && root != PathRoot::Relative {
                    self.path(root, &["class".to_string()], Ns::Value, Res::Unresolved)
                } else {
                    self.member_path(root)
                };
                self.b.expr(Expr::Path(p))
            }
            _ => {
                let a = self.expr(d - 1, this);
                let bb = self.expr(d - 1, this);
                self.intrinsic("mox.concat", &[a, bb], None)
            }
        }
    }

    fn vis(&mut self) -> Vis {
        self.r
            .pick(&[Vis::Public, Vis::Protected, Vis::Private, Vis::Public])
    }

    fn method(&mut self) -> ItemId {
        let name = self.member_name();
        let dtor = name == "__destruct" && !self.r.chance(5);
        let instance = dtor || self.r.chance(70);
        let mut params = Vec::new();
        let mut this = None;
        if instance {
            let n = self.name("this");
            let tb = self
                .b
                .binder(Binder::new(n, BinderKind::Param).with_mutable(true));
            let pat = self.b.bind(tb);
            params.push(self.b.param(Param {
                pat,
                ty: None,
                default: None,
                kind: ParamKind::Receiver,
                by_ref: false,
            }));
            this = Some(tb);
        }
        for i in 0..if dtor { 0 } else { self.r.below(3) } {
            let n = self.name(&format!("p{i}"));
            let pb = self
                .b
                .binder(Binder::new(n, BinderKind::Param).with_mutable(true));
            let pat = self.b.bind(pb);
            let default = self.r.chance(30).then(|| self.lit());
            params.push(self.b.param(Param {
                pat,
                ty: None,
                default,
                kind: ParamKind::Normal,
                by_ref: false,
            }));
        }
        let body = if self.r.chance(15) {
            None
        } else {
            let e = self.expr(3, this);
            Some(self.b.block(&[], Some(e)))
        };
        let mut effects = Effects::THROWS;
        if self.r.chance(15) {
            effects = effects.union(Effects::YIELD);
        }
        let n = self.name(&name);
        let params = self.b.list(&params);
        let vis = self.vis();
        let item = self.b.item(
            Item::new(
                Some(n),
                ItemKind::Fn(FnDef {
                    params,
                    body,
                    effects,
                    ..FnDef::default()
                }),
            )
            .with_vis(vis),
        );
        self.members.push(item);
        self.current.push((item, name));
        item
    }

    fn members(&mut self, interface: bool) -> (Vec<ItemId>, Vec<FieldId>) {
        let mut items = Vec::new();
        let mut fields = Vec::new();
        for _ in 0..self.r.below(6) {
            match self.r.below(if interface { 2 } else { 5 }) {
                0 => items.push(self.method()),
                1 => {
                    let name = self.member_name();
                    let n = self.name(&name);
                    let value = Some(self.expr(1, None));
                    let vis = self.vis();
                    let item = self.b.item(
                        Item::new(Some(n), ItemKind::Const { ty: None, value }).with_vis(vis),
                    );
                    self.members.push(item);
                    self.current.push((item, name));
                    items.push(item);
                }
                2 => {
                    let name = self.member_name();
                    let n = self.name(&name);
                    let init = self.r.chance(70).then(|| self.expr(1, None));
                    let vis = self.vis();
                    let item = self.b.item(
                        Item::new(
                            Some(n),
                            ItemKind::Global {
                                ty: None,
                                mutable: true,
                                init,
                            },
                        )
                        .with_vis(vis),
                    );
                    self.members.push(item);
                    self.current.push((item, name));
                    items.push(item);
                }
                3 => {
                    let name = self.member_name();
                    let id = self.ident(&name);
                    let default = self.r.chance(60).then(|| self.expr(1, None));
                    let vis = self.vis();
                    fields.push(self.b.field(FieldDef {
                        name: Some(id),
                        vis,
                        ty: None,
                        default,
                    }));
                }
                _ => {
                    let mixins: Vec<TyId> = (0..1 + self.r.below(2))
                        .filter_map(|_| self.class_ty_of(&[2]))
                        .collect();
                    let mut rules = Vec::new();
                    for _ in 0..self.r.below(3) {
                        let method = {
                            let m = self.member_name();
                            self.ident(&m)
                        };
                        let from = if self.r.chance(60) {
                            self.class_ty_of(&[2])
                        } else {
                            None
                        };
                        let action = if self.r.chance(40) {
                            let o: Vec<TyId> = self.class_ty_of(&[2]).into_iter().collect();
                            MixinAction::Insteadof(self.b.list(&o))
                        } else {
                            let name = self.r.chance(60).then(|| {
                                let m = self.member_name();
                                self.ident(&format!("{m}2"))
                            });
                            let vis = self.r.chance(50).then(|| self.vis());
                            MixinAction::Alias { name, vis }
                        };
                        rules.push(MixinRule {
                            method,
                            from,
                            action,
                        });
                    }
                    let mixins = self.b.list(&mixins);
                    let rules = self.b.list(&rules);
                    items.push(self.b.item(Item::new(
                        None,
                        ItemKind::MixinUse(MixinUseDef { mixins, rules }),
                    )));
                }
            }
        }
        (items, fields)
    }

    fn program(mut self) -> (hir_lang::Hir, Interner) {
        let n = 1 + self.r.below(6);
        for i in 0..n {
            self.made += 1;
            let kind = self.r.below(4);
            // The class graph first, so members know whether `parent::`
            // has a meaning.
            let (bases, ifaces) = match kind {
                0 | 1 => {
                    let most = if self.r.chance(3) { 3 } else { 2 };
                    let bases: Vec<TyId> = (0..self.r.below(most))
                        .filter_map(|_| self.class_ty_of(&[0, 1]))
                        .collect();
                    let ifaces: Vec<TyId> = (0..self.r.below(3))
                        .filter_map(|_| self.class_ty_of(&[3]))
                        .collect();
                    (bases, ifaces)
                }
                3 => {
                    let supers: Vec<TyId> = (0..self.r.below(3))
                        .filter_map(|_| self.class_ty_of(&[3]))
                        .collect();
                    (Vec::new(), supers)
                }
                _ => (Vec::new(), Vec::new()),
            };
            self.has_parent = !bases.is_empty();
            self.current.clear();
            self.in_class = true;
            let (items, fields) = self.members(kind == 3);
            self.in_class = false;
            let name = self.name(&format!("K{i}"));
            let item = if kind == 3 {
                let supers = self.b.list(&ifaces);
                let items = self.b.list(&items);
                self.b.item(
                    Item::new(
                        Some(name),
                        ItemKind::Interface(InterfaceDef {
                            supers,
                            items,
                            ..InterfaceDef::default()
                        }),
                    )
                    .with_vis(Vis::Public),
                )
            } else {
                let def = ClassDef {
                    bases: self.b.list(&bases),
                    interfaces: self.b.list(&ifaces),
                    fields: self.b.list(&fields),
                    items: self.b.list(&items),
                    is_abstract: kind == 1,
                    mixin: kind == 2,
                    ..ClassDef::default()
                };
                self.b
                    .item(Item::new(Some(name), ItemKind::Class(def)).with_vis(Vis::Public))
            };
            self.classes.push(item);
            let members = std::mem::take(&mut self.current);
            self.info.push((kind, format!("K{i}"), members));
        }
        // A body exercising the classes.
        let mut stmts = Vec::new();
        for _ in 0..1 + self.r.below(5) {
            let e = self.expr(4, None);
            stmts.push(self.b.stmt(Stmt::Expr(e)));
        }
        let tail = self.expr(3, None);
        let body = self.b.block(&stmts, Some(tail));
        let items = self.b.list(&self.classes);
        let root = self.b.item(Item::new(
            None,
            ItemKind::Module {
                items,
                body: Some(body),
                effects: Effects::THROWS,
            },
        ));
        match self.b.finish_lenient(root) {
            Ok((hir, problems)) => {
                if std::env::var("BCGEN_PROBLEMS").is_ok() {
                    for p in problems {
                        println!("problem {p:?}");
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
        classes: Vec::new(),
        info: Vec::new(),
        current: Vec::new(),
        members: Vec::new(),
        made: 0,
        fuel: 150,
        in_class: false,
        has_parent: false,
    }
    .program()
}

fn host() -> Host {
    let mut h = common::host(std::sync::Arc::new(std::sync::Mutex::new(Vec::new())));
    for (_, def) in Intrinsics::mox().iter() {
        if let Some((m, f)) = def.lowering().host() {
            let _ = h.register(m, f, |_, _| Ok(bvm_lang::Value::Nil));
        }
    }
    h
}

fn cases() -> u32 {
    std::env::var("BCGEN_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(2000)
}

fn exercise(seed: u64) -> Result<(), TestCaseError> {
    let (hir, names) = garbage(seed);
    for rc in [false, true] {
        let opts = Options::new()
            .with_body(BodyMode::Entry)
            .with_intrinsics(Intrinsics::mox())
            .with_reference_counting(rc)
            .with_max_instructions(1 << 20);
        let Ok(out) = Compiler::new(opts).compile(&hir, &names) else {
            continue;
        };
        let program = Program::load(out.module().clone(), &host());
        prop_assert!(program.is_ok(), "{:?}", program.err());
        let Ok(p) = program else { continue };
        let limits = Limits::new()
            .with_fuel(20_000)
            .with_depth(64)
            .with_memory(16 << 20);
        let memory = if rc { Memory::Rc } else { Memory::Tracing };
        let mut vm = Vm::with_limits(&p, limits);
        let _ = vm.run(out.entry(), &[]);
        let mut vm = Vm::with_memory(&p, memory);
        vm.set_limits(limits);
        if let Some(d) = out.destructor() {
            let _ = vm.set_destructor(d);
        }
        let _ = vm.run(out.entry(), &[]);
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig { cases: cases(), ..ProptestConfig::default() })]

    #[test]
    fn class_garbage_compiles_or_errors_and_runs_without_panicking(seed in any::<u64>()) {
        exercise(seed)?;
    }
}

/// How the garbage fares (`--ignored --nocapture`): how many programs
/// compile, and why the rest do not.
#[test]
#[ignore = "a measurement"]
fn class_garbage_outcomes() {
    let mut counts: std::collections::BTreeMap<String, u32> = std::collections::BTreeMap::new();
    for seed in 0..2000u64 {
        let (hir, names) = garbage(seed);
        let opts = Options::new()
            .with_body(BodyMode::Entry)
            .with_intrinsics(Intrinsics::mox());
        let k = match Compiler::new(opts).compile(&hir, &names) {
            Ok(_) => "ok".to_string(),
            Err(e) => {
                let what = match e.node() {
                    Some(hir_lang::NodeRef::Path(p)) => {
                        let path = hir.path(p);
                        format!(" path {:?} {:?}", path.root, path.res)
                    }
                    Some(hir_lang::NodeRef::Expr(x)) => match hir.expr(x) {
                        Expr::Path(p) => {
                            let path = hir.path(*p);
                            format!(" expr path {:?} {:?}", path.root, path.res)
                        }
                        other => format!(
                            " {}",
                            format!("{other:?}").split(['{', '(']).next().unwrap_or("")
                        ),
                    },
                    Some(n) => format!(" {n:?}")
                        .split(['('])
                        .next()
                        .unwrap_or("")
                        .to_string(),
                    None => String::new(),
                };
                let head = match e {
                    bcgen_lang::CompileError::Class { problem, .. } => format!("Class {problem:?}"),
                    bcgen_lang::CompileError::Unsupported { feature, .. } => {
                        format!("Unsupported {feature:?}")
                    }
                    _ => format!("{e:?}")
                        .split([' ', '{', '('])
                        .next()
                        .unwrap_or("")
                        .to_string(),
                };
                head + &what
            }
        };
        *counts.entry(k).or_insert(0) += 1;
    }
    println!("{counts:#?}");
}
