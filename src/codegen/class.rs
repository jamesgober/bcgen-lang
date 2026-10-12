//! Classes in code: member access with run-time visibility, static and
//! late-bound member paths, `new`, `instanceof`, `clone`, class type tests,
//! and the synthetic functions every struct carries.
//!
//! **Receivers.** Every method takes its receiver in register 0: the
//! instance for an instance method; for a static method the class's token,
//! or the instance it was called through. `static::` looks members up on the
//! receiver, so late static binding needs no hidden class argument. A
//! `self::`/`parent::` call forwards the receiver (PHP's forwarding call);
//! `C::m()` passes `C`'s token.
//!
//! **Selection.** An access through an object picks its LSB name at run
//! time from a [`Plan`]: the scope's own private member when the object has
//! it, else the public name after the class tests that decide visibility.
//! Without classes in the unit every access is the plain 0.3 instruction.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use bytecode_lang::{ErrorKind, Inst, IntTy, Kind, NameRef, Reg, ValType};
use hir_lang::{Arg, Expr, ExprId, ItemId, ItemKind, NodeRef, PathId, PathRoot, Res, Symbol};
use intern_lang::Lookup;

use super::{Dst, Gen, Rel, Step, Task, Val};
use crate::class::{CKind, Check, ClassId, Ns, Outcome, Plan, lsb_name};
use crate::error::{CompileError, Unsupported};
use crate::func::FnCx;
use crate::unit::{ClassJob, Slot};

/// A class an operand names at compile time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ClassRef {
    /// A class or interface of the unit.
    Known(ClassId),
    /// `static`: the receiver's class.
    Late,
}

/// A member a static path names.
#[derive(Clone, Copy, Debug)]
pub(crate) enum MemberRef {
    /// A constant (`global` holds the value) or static property (`global`
    /// holds a reference).
    Value {
        global: bytecode_lang::GlobalId,
        is_static: bool,
        denied: Option<Denied>,
    },
    /// A method: compiled for `holder`; `named` is the class the path named
    /// (its token is the receiver of a static call through it); `forward`
    /// for `self::`/`parent::`.
    Method {
        holder: ClassId,
        item: ItemId,
        named: ClassId,
        is_static: bool,
        forward: bool,
        denied: Option<Denied>,
        name: Symbol,
    },
    /// `static::name`: looked up on the receiver at run time.
    Late { name: Symbol },
    /// `C::class`: the class's name (`None`: `static::class`, the
    /// receiver's class's).
    ClassName(Option<ClassId>),
    /// A member class `class` does not have: PHP raises where the access
    /// runs ("Call to undefined method", "Undefined constant", "Access to
    /// undeclared static property").
    Missing {
        class: ClassId,
        ns: Ns,
        name: Symbol,
    },
}

/// A statically known visibility violation, raised where the access runs.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Denied {
    pub(crate) ns: Ns,
    pub(crate) outcome: Outcome,
    pub(crate) name: Symbol,
}

/// What a path's member is wanted for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Want {
    Value,
    Call,
}

/// The continuation steps of class operations.
#[derive(Clone, Debug)]
pub(crate) enum ClassStep {
    /// `new` of a class value: the value is on the stack.
    NewDyn {
        args: Vec<Arg>,
        host: (String, String),
        dst: Dst,
        node: NodeRef,
    },
    /// The arguments of a dynamic `new` are in the window: construct, or
    /// call the host function when the class was not found.
    NewFinish {
        win: (u32, Reg),
        kinds: Vec<bytecode_lang::ArgKind>,
        tok: Reg,
        cls: Reg,
        obj: Reg,
        host: (String, String),
        dst: Dst,
        node: NodeRef,
    },
    /// `x instanceof C`: `x` (and a run-time class value) on the stack.
    InstanceOf {
        class: Option<ClassRef>,
        host: (String, String),
        dst: Dst,
        node: NodeRef,
    },
    /// `clone x`: `x` on the stack.
    Clone {
        host: (String, String),
        dst: Dst,
        node: NodeRef,
    },
    /// Pushes the reference of the late-bound static property `name` (the
    /// root of a place `static::$x...`).
    LateRef { name: Symbol, node: NodeRef },
}

impl<L: Lookup> Gen<'_, '_, L> {
    // ------------------------------------------------------------ scope

    /// The class of the code being generated.
    pub(crate) fn scope_class(&self) -> Option<ClassId> {
        self.scope.map(|s| s.class)
    }

    /// The class's LSB name.
    fn lsb_of(&self, c: ClassId) -> String {
        self.cx.ct.get(c).map(|d| d.lsb.clone()).unwrap_or_default()
    }

    fn class_text(&self, c: ClassId) -> String {
        self.cx
            .ct
            .get(c)
            .map(|d| d.text.clone())
            .unwrap_or_default()
    }

    /// A per-function name reference for an LSB name.
    pub(crate) fn lsb_ref(&mut self, name: &str) -> NameRef {
        let s = self.cx.mb.string(name);
        self.fx.f.name_ref(s)
    }

    /// The visibility plan for `name` in `ns` from the current scope
    /// (cached; its computation is charged to the budget).
    fn plan(&mut self, ns: Ns, name: Symbol) -> Plan {
        let key = (self.scope_class(), ns, name);
        if let Some(p) = self.cx.plans.get(&key) {
            return p.clone();
        }
        let p = self.cx.ct.plan(key.0, ns, name);
        let cost = p.work.saturating_add(p.checks.len() as u64);
        self.cx.emitted = self.cx.emitted.saturating_add(cost);
        let _ = self.cx.plans.insert(key, p.clone());
        p
    }

    /// Raises `TypeError` (E0100, PHP's `Error`) with a message payload.
    pub(crate) fn raise_msg(&mut self, msg: &str) {
        let s = self.cx.mb.string(msg);
        let k = self.cx.mb.constant(bytecode_lang::Const::Str(s));
        let r = self.fx.temp(ValType::Dyn);
        self.emit(Inst::DLoadConst { dst: r, k });
        self.emit(Inst::Raise {
            src: r,
            kind: ErrorKind::TypeError,
        });
        self.fx.release(r);
    }

    /// Raises a statically known visibility violation.
    pub(crate) fn raise_denied(&mut self, d: Denied) {
        let msg = self.denial(d.ns, d.outcome, d.name);
        self.raise_msg(&msg);
    }

    /// PHP's message for a member a class does not have.
    pub(crate) fn missing_msg(&self, class: ClassId, ns: Ns, name: Symbol) -> String {
        let c = self.class_text(class);
        let n = self.cx.text(name);
        match ns {
            Ns::Method => alloc::format!("Call to undefined method {c}::{n}()"),
            Ns::Static => alloc::format!("Access to undeclared static property {c}::${n}"),
            Ns::Const => alloc::format!("Undefined constant {c}::{n}"),
            Ns::Prop => alloc::format!("Undefined property {c}::${n}"),
        }
    }

    /// PHP's message for a denied access.
    fn denial(&self, ns: Ns, outcome: Outcome, name: Symbol) -> String {
        let (vis, c) = match outcome {
            Outcome::Ok => return String::new(),
            Outcome::Protected(c) => ("protected", c),
            Outcome::Private(c) => ("private", c),
        };
        let class = self.class_text(c);
        let n = self.cx.text(name);
        let scope = match self.scope_class() {
            Some(s) => alloc::format!("scope {}", self.class_text(s)),
            None => String::from("global scope"),
        };
        match ns {
            Ns::Prop | Ns::Static => alloc::format!("Cannot access {vis} property {class}::${n}"),
            Ns::Method => alloc::format!("Call to {vis} method {class}::{n}() from {scope}"),
            Ns::Const => alloc::format!("Cannot access {vis} constant {class}::{n}"),
        }
    }

    /// The type reference of class `c`'s struct.
    fn class_ref(&mut self, c: ClassId) -> Option<bytecode_lang::TypeRef> {
        let ty = self.cx.crt.get(c as usize)?.ty?;
        Some(self.fx.f.type_ref(ty))
    }

    /// Emits a plan's class tests on `obj`: a denied outcome raises; every
    /// other path falls through. A plan for the scope's instances only
    /// (`Plan::inside`) sends any other object to the name's shared check.
    fn checks(&mut self, obj: Reg, ns: Ns, name: Symbol, plan: &Plan) {
        let Some(s) = plan.inside else {
            self.checks_inline(obj, ns, name, &plan.checks);
            return;
        };
        let token = self.cx.crt.get(s as usize).and_then(|r| r.token);
        let (Some(tr), Some(token)) = (self.class_ref(s), token) else {
            let full = self.cx.ct.plan_full(Some(s), ns, name);
            self.cx.emitted = self.cx.emitted.saturating_add(full.work);
            self.checks_inline(obj, ns, name, &full.checks);
            return;
        };
        let (inside, done) = (self.label(), self.label());
        let b = self.fx.temp(ValType::Bool);
        self.emit(Inst::IsType {
            dst: b,
            src: obj,
            ty: tr,
        });
        self.jump_on(b, inside, true);
        self.fx.release(b);
        let f = self.cx.vis_fn(ns, name);
        let win = self.fx.window(&[ValType::Dyn; 4]);
        self.emit(Inst::Mov {
            dst: FnCx::slot(win.1, 1),
            src: obj,
        });
        self.emit(Inst::GetGlobal {
            dst: FnCx::slot(win.1, 2),
            global: token,
        });
        let text = alloc::format!("scope {}", self.class_text(s));
        let sid = self.cx.mb.string(&text);
        let k = self.cx.mb.constant(bytecode_lang::Const::Str(sid));
        self.emit(Inst::DLoadConst {
            dst: FnCx::slot(win.1, 3),
            k,
        });
        self.emit(Inst::Call {
            dst: win.1,
            func: f,
            argc: 3,
        });
        self.fx.release_window(win.0, win.1);
        self.jmp(done);
        self.bind(inside);
        self.checks_inline(obj, ns, name, &plan.checks);
        self.bind(done);
    }

    /// The body of `<vis name>(obj, scope_token, scope_text)`: every class
    /// declaring the name, deepest first; a protected member's scope test
    /// asks whether the scope's token is an instance of the member's key.
    fn vis_body(&mut self, ns: Ns, name: Symbol) {
        let (obj, tok, scope) = (Reg(0), Reg(1), Reg(2));
        let list = self.cx.ct.outside(ns, name);
        self.cx.emitted = self.cx.emitted.saturating_add(list.len() as u64);
        let ok = self.label();
        let b = self.fx.temp(ValType::Bool);
        let mut targets: BTreeMap<Check, bytecode_lang::Label> = BTreeMap::new();
        for &(c, check) in &list {
            let Some(tr) = self.class_ref(c) else {
                continue;
            };
            self.emit(Inst::IsType {
                dst: b,
                src: obj,
                ty: tr,
            });
            let l = match check {
                Check::Ok => ok,
                _ => match targets.get(&check) {
                    Some(&l) => l,
                    None => {
                        let l = self.label();
                        let _ = targets.insert(check, l);
                        l
                    }
                },
            };
            self.jump_on(b, l, true);
        }
        self.jmp(ok);
        for (check, l) in targets {
            self.bind(l);
            let outcome = match check {
                Check::Ok => Outcome::Ok,
                Check::Deny(o) => o,
                Check::Protected { key, decl } => {
                    if let Some(kr) = self.class_ref(key) {
                        self.emit(Inst::IsType {
                            dst: b,
                            src: tok,
                            ty: kr,
                        });
                        self.jump_on(b, ok, true);
                    }
                    Outcome::Protected(decl)
                }
            };
            if ns == Ns::Method {
                // The message names the accessing scope, an argument here.
                let (vis, c) = match outcome {
                    Outcome::Private(c) => ("private", c),
                    Outcome::Protected(c) => ("protected", c),
                    Outcome::Ok => {
                        self.jmp(ok);
                        continue;
                    }
                };
                let head = alloc::format!(
                    "Call to {vis} method {}::{}() from ",
                    self.class_text(c),
                    self.cx.text(name)
                );
                let sid = self.cx.mb.string(&head);
                let k = self.cx.mb.constant(bytecode_lang::Const::Str(sid));
                let parts = self.fx.window(&[ValType::Str, ValType::Str]);
                self.emit(Inst::LoadConst {
                    dst: FnCx::slot(parts.1, 0),
                    k,
                });
                self.emit(Inst::FromDyn {
                    dst: FnCx::slot(parts.1, 1),
                    src: scope,
                    to: bytecode_lang::Prim::Str,
                });
                let s = self.fx.temp(ValType::Str);
                self.emit(Inst::StrConcatN {
                    dst: s,
                    first: parts.1,
                    count: 2,
                });
                let r = self.fx.temp(ValType::Dyn);
                self.emit(Inst::ToDyn {
                    dst: r,
                    src: s,
                    from: bytecode_lang::Prim::Str,
                });
                self.emit(Inst::Raise {
                    src: r,
                    kind: ErrorKind::TypeError,
                });
                self.fx.release(r);
                self.fx.release(s);
                self.fx.release_window(parts.0, parts.1);
            } else {
                let msg = self.denial(ns, outcome, name);
                self.raise_msg(&msg);
            }
        }
        self.fx.release(b);
        self.bind(ok);
        let r = self.fx.temp(ValType::Dyn);
        self.emit(Inst::LoadNil { dst: r });
        self.emit(Inst::Ret { src: r });
    }

    /// Emits class tests on `obj` inline: a denied outcome raises; every
    /// other path falls through.
    fn checks_inline(&mut self, obj: Reg, ns: Ns, name: Symbol, checks: &[(ClassId, Outcome)]) {
        if checks.is_empty() {
            return;
        }
        let ok = self.label();
        let b = self.fx.temp(ValType::Bool);
        let mut targets: Vec<(bytecode_lang::Label, Outcome)> = Vec::with_capacity(checks.len());
        for &(c, outcome) in checks {
            let Some(tr) = self.class_ref(c) else {
                continue;
            };
            self.emit(Inst::IsType {
                dst: b,
                src: obj,
                ty: tr,
            });
            let l = if outcome == Outcome::Ok {
                ok
            } else {
                let l = self.label();
                targets.push((l, outcome));
                l
            };
            self.jump_on(b, l, true);
        }
        self.fx.release(b);
        self.jmp(ok);
        for (l, outcome) in targets {
            self.bind(l);
            let msg = self.denial(ns, outcome, name);
            self.raise_msg(&msg);
        }
        self.bind(ok);
    }

    /// Emits an access to `name` in `ns` through `obj` by the current
    /// scope's plan: `emit` is called with the LSB name to use (once for the
    /// scope's private member, once for the public one).
    pub(crate) fn select<F>(&mut self, obj: Reg, ns: Ns, name: Symbol, mut emit: F)
    where
        F: FnMut(&mut Self, NameRef),
    {
        let text = self.cx.text(name);
        if self.cx.ct.is_empty() {
            let n = self.lsb_ref(&text);
            emit(self, n);
            return;
        }
        let plan = self.plan(ns, name);
        let public = lsb_name(ns, &text, None);
        let public = self.lsb_ref(&public);
        let Some(s) = plan.private else {
            self.checks(obj, ns, name, &plan);
            emit(self, public);
            return;
        };
        let lsb = self.lsb_of(s);
        let private = lsb_name(ns, &text, Some(&lsb));
        let private = self.lsb_ref(&private);
        let (own, done) = (self.label(), self.label());
        let b = self.fx.temp(ValType::Bool);
        self.emit(Inst::HasProp {
            dst: b,
            obj,
            name: private,
        });
        self.jump_on(b, own, true);
        self.fx.release(b);
        self.checks(obj, ns, name, &plan);
        emit(self, public);
        self.jmp(done);
        self.bind(own);
        emit(self, private);
        self.bind(done);
    }

    /// `dst = obj.name` (a property read).
    pub(crate) fn prop_get(&mut self, dst: Reg, obj: Reg, name: Symbol) {
        self.select(obj, Ns::Prop, name, |g, n| {
            g.emit(Inst::GetProp { dst, obj, name: n });
        });
    }

    /// `obj.name = src`.
    pub(crate) fn prop_set(&mut self, obj: Reg, name: Symbol, src: Reg) {
        self.select(obj, Ns::Prop, name, |g, n| {
            g.emit(Inst::SetProp { obj, name: n, src });
        });
    }

    /// `dst = &obj.name`.
    pub(crate) fn prop_ref(&mut self, dst: Reg, obj: Reg, name: Symbol) {
        self.select(obj, Ns::Prop, name, |g, n| {
            g.emit(Inst::DRefProp { dst, obj, name: n });
        });
    }

    /// `obj.name =& src`.
    pub(crate) fn prop_bind(&mut self, obj: Reg, name: Symbol, src: Reg) {
        self.select(obj, Ns::Prop, name, |g, n| {
            g.emit(Inst::DBindProp { obj, name: n, src });
        });
    }

    /// The method `name` of `recv` as a function value in `dst`: the
    /// scope's private method, else the public one after the visibility
    /// tests. A receiver that is not an object (a map of closures, a host
    /// value) reads the plain name, as 0.3 did.
    pub(crate) fn method_lookup(&mut self, dst: Reg, recv: Reg, name: Symbol) {
        let text = self.cx.text(name);
        if self.cx.ct.is_empty() {
            let n = self.lsb_ref(&text);
            self.emit(Inst::GetProp {
                dst,
                obj: recv,
                name: n,
            });
            return;
        }
        let plan = self.plan(Ns::Method, name);
        let public = lsb_name(Ns::Method, &text, None);
        let public = self.lsb_ref(&public);
        let plain = self.lsb_ref(&text);
        let (miss, objmiss, done) = (self.label(), self.label(), self.label());
        let own = self.label();
        let b = self.fx.temp(ValType::Bool);
        let mut private = None;
        if let Some(s) = plan.private {
            let lsb = self.lsb_of(s);
            let p = lsb_name(Ns::Method, &text, Some(&lsb));
            let p = self.lsb_ref(&p);
            self.emit(Inst::HasProp {
                dst: b,
                obj: recv,
                name: p,
            });
            self.jump_on(b, own, true);
            private = Some(p);
        }
        self.emit(Inst::HasProp {
            dst: b,
            obj: recv,
            name: public,
        });
        self.jump_on(b, miss, false);
        self.checks(recv, Ns::Method, name, &plan);
        self.emit(Inst::GetProp {
            dst,
            obj: recv,
            name: public,
        });
        self.jmp(done);
        self.bind(miss);
        self.emit(Inst::IsKind {
            dst: b,
            src: recv,
            kind: Kind::Object,
        });
        self.jump_on(b, objmiss, true);
        self.emit(Inst::GetProp {
            dst,
            obj: recv,
            name: plain,
        });
        self.jmp(done);
        self.bind(objmiss);
        self.checks(recv, Ns::Method, name, &plan);
        // The `get_prop` hook (PHP's `__call`) or `UndefinedProperty`.
        self.emit(Inst::GetProp {
            dst,
            obj: recv,
            name: public,
        });
        self.fx.release(b);
        if let Some(p) = private {
            self.jmp(done);
            self.bind(own);
            self.emit(Inst::GetProp {
                dst,
                obj: recv,
                name: p,
            });
        }
        self.bind(done);
    }

    // ------------------------------------------------------------ static paths

    /// The class an operand of `new`/`instanceof` names at compile time:
    /// a path to a class or interface of the unit, `C::class`, or
    /// `self::class`/`parent::class`/`static::class` (a bare `self` is no
    /// valid HIR path; a lowering writes `new static` as
    /// `new (static::class)`).
    pub(crate) fn class_operand(&self, e: ExprId) -> Result<Option<ClassRef>, CompileError> {
        let hir = self.cx.hir;
        let Expr::Path(p) = *hir.expr(e) else {
            return Ok(None);
        };
        if let Some(c) = self.class_name_path(p)? {
            return Ok(Some(c));
        }
        let path = *hir.path(p);
        let node = NodeRef::Path(p);
        match (path.root, path.unresolved, path.res) {
            (PathRoot::Relative | PathRoot::Global, 0, Res::Def(_)) => {
                Ok(self.cx.ct.of_res(hir, path.res, node)?.map(ClassRef::Known))
            }
            _ => Ok(None),
        }
    }

    /// The class a path of the form `C::class` names (`self`, `parent`,
    /// `static`, or a class of the unit before `::class`).
    pub(crate) fn class_name_path(&self, p: PathId) -> Result<Option<ClassRef>, CompileError> {
        if self.cx.ct.is_empty() {
            return Ok(None);
        }
        let hir = self.cx.hir;
        let path = *hir.path(p);
        let node = NodeRef::Path(p);
        let segs = hir.list(path.segments);
        let is_class = segs.last().is_some_and(|s| {
            self.cx.names.resolve_with(s.name.sym, |t| t == "class") == Some(true)
        });
        let unresolved = || CompileError::Unresolved {
            node,
            span: self.cx.span(node),
        };
        match path.root {
            PathRoot::SelfType | PathRoot::ParentType | PathRoot::StaticType
                if segs.is_empty() || (segs.len() == 1 && is_class) =>
            {
                let Some(s) = self.scope_class() else {
                    return Err(unresolved());
                };
                Ok(Some(match path.root {
                    PathRoot::StaticType => ClassRef::Late,
                    PathRoot::ParentType => match self.cx.ct.get(s).and_then(|d| d.parent) {
                        Some(p) => ClassRef::Known(p),
                        None => return Err(unresolved()),
                    },
                    _ => ClassRef::Known(s),
                }))
            }
            PathRoot::Relative | PathRoot::Global
                if is_class && path.unresolved == 1 && segs.len() >= 2 =>
            {
                match path.res {
                    Res::Def(_) => Ok(self.cx.ct.of_res(hir, path.res, node)?.map(ClassRef::Known)),
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    /// The class a type operand names (a class operation's generic
    /// argument: `mox.instanceof<I>(x)`, `mox.new<C>(args)`).
    pub(crate) fn class_type_operand(
        &self,
        ty: hir_lang::TyId,
    ) -> Result<Option<ClassRef>, CompileError> {
        let hir = self.cx.hir;
        match *hir.ty(ty) {
            hir_lang::Ty::SelfTy => Ok(self.scope_class().map(ClassRef::Known)),
            hir_lang::Ty::Path(p) => {
                let path = *hir.path(p);
                let node = NodeRef::Path(p);
                if path.unresolved != 0 {
                    return Ok(None);
                }
                match path.res {
                    Res::Def(_) => Ok(self.cx.ct.of_res(hir, path.res, node)?.map(ClassRef::Known)),
                    Res::Extern(_) => Err(self.cx.unsupported(Unsupported::ClassTest, node)),
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    /// The member a static path names, if it names one: `self::`,
    /// `parent::`, `static::` paths, and paths resolved to a member of a
    /// class, interface, or mixin of the unit.
    pub(crate) fn member_path(
        &self,
        p: PathId,
        want: Want,
    ) -> Result<Option<MemberRef>, CompileError> {
        if self.cx.ct.is_empty() {
            return Ok(None);
        }
        if want == Want::Value {
            match self.class_name_path(p)? {
                Some(ClassRef::Known(c)) => return Ok(Some(MemberRef::ClassName(Some(c)))),
                Some(ClassRef::Late) => return Ok(Some(MemberRef::ClassName(None))),
                None => {}
            }
        }
        let hir = self.cx.hir;
        let path = *hir.path(p);
        let node = NodeRef::Path(p);
        let segs = hir.list(path.segments);
        let unresolved = || CompileError::Unresolved {
            node,
            span: self.cx.span(node),
        };
        let Some(last) = segs.last() else {
            return Ok(None);
        };
        let name = last.name.sym;
        // The namespace: the resolved item's kind, else what the use wants.
        let item_ns = |item: ItemId| match hir.item(item).kind {
            ItemKind::Fn(_) => Some(Ns::Method),
            ItemKind::Global { .. } => Some(Ns::Static),
            ItemKind::Const { .. } => Some(Ns::Const),
            _ => None,
        };
        let resolved_item = match (path.res, path.unresolved) {
            (Res::Def(d), 0) if d.unit() == hir.unit() => match d.def() {
                hir_lang::Def::Item(i) if self.cx.ct.owner.contains_key(&i) => Some(i),
                _ => None,
            },
            _ => None,
        };
        let ns = match resolved_item.and_then(item_ns) {
            Some(ns) => ns,
            None if want == Want::Call => Ns::Method,
            None => {
                let ct = &self.cx.ct;
                if ct.decls.contains_key(&(Ns::Static, name))
                    && !ct.decls.contains_key(&(Ns::Const, name))
                {
                    Ns::Static
                } else {
                    Ns::Const
                }
            }
        };
        let (start, named, forward) = match path.root {
            PathRoot::SelfType | PathRoot::ParentType | PathRoot::StaticType => {
                let Some(s) = self.scope_class() else {
                    return Err(unresolved());
                };
                match path.root {
                    PathRoot::StaticType => return Ok(Some(MemberRef::Late { name })),
                    PathRoot::ParentType => {
                        let Some(p) = self.cx.ct.get(s).and_then(|d| d.parent) else {
                            return Err(unresolved());
                        };
                        (p, p, true)
                    }
                    _ => (s, s, true),
                }
            }
            _ => {
                let Some(item) = resolved_item else {
                    // `C::member` the resolver left to the type (a constant
                    // of an interface `C` implements, a member only the run
                    // time could find): looked up by name in `C`.
                    let class = match (path.res, path.unresolved) {
                        (Res::Def(_), 1) if segs.len() >= 2 => {
                            self.cx.ct.of_res(hir, path.res, node)?
                        }
                        _ => None,
                    };
                    let Some(c) = class
                        .filter(|&c| self.cx.ct.get(c).is_some_and(|d| d.kind != CKind::Mixin))
                    else {
                        return Ok(None);
                    };
                    return self.member_in(c, c, false, ns, name, node).map(Some);
                };
                let owner = self.cx.ct.owner.get(&item).copied();
                let named = self.named_class(segs, ns, name, item)?;
                let named = match (named, owner) {
                    (Some(c), _) => c,
                    (None, Some(o))
                        if self.cx.ct.get(o).is_some_and(|d| d.kind != CKind::Mixin) =>
                    {
                        o
                    }
                    _ => {
                        return Err(self.cx.unsupported(Unsupported::MixinMember, node));
                    }
                };
                (named, named, false)
            }
        };
        self.member_in(start, named, forward, ns, name, node)
            .map(Some)
    }

    /// The member `name` in `ns` as class `start` sees it.
    fn member_in(
        &self,
        start: ClassId,
        named: ClassId,
        forward: bool,
        ns: Ns,
        name: Symbol,
        node: NodeRef,
    ) -> Result<MemberRef, CompileError> {
        let unresolved = || CompileError::Unresolved {
            node,
            span: self.cx.span(node),
        };
        let ct = &self.cx.ct;
        let scope = self.scope_class();
        let missing = MemberRef::Missing {
            class: start,
            ns,
            name,
        };
        match ns {
            Ns::Method => {
                let Some((holder, m)) = ct.find_method(start, name) else {
                    return Ok(missing);
                };
                let outcome = ct.static_access(scope, holder, Ns::Method, name, m.vis);
                Ok(MemberRef::Method {
                    holder,
                    item: m.item,
                    named,
                    is_static: m.is_static,
                    forward,
                    denied: (outcome != Outcome::Ok).then_some(Denied { ns, outcome, name }),
                    name,
                })
            }
            Ns::Static | Ns::Const => {
                let found = if ns == Ns::Static {
                    ct.find_static(start, name)
                } else {
                    ct.find_const(start, name)
                };
                let Some((holder, m)) = found else {
                    return Ok(missing);
                };
                let Some(&global) = self.cx.member_globals.get(&(holder, m.item)) else {
                    return Err(unresolved());
                };
                let outcome = ct.static_access(scope, holder, ns, name, m.vis);
                Ok(MemberRef::Value {
                    global,
                    is_static: ns == Ns::Static,
                    denied: (outcome != Outcome::Ok).then_some(Denied { ns, outcome, name }),
                })
            }
            Ns::Prop => Err(unresolved()),
        }
    }

    /// The class a qualified member path names by its next-to-last segment:
    /// the unit's class of that name whose member table reaches `item`.
    fn named_class(
        &self,
        segs: &[hir_lang::Segment],
        ns: Ns,
        name: Symbol,
        item: ItemId,
    ) -> Result<Option<ClassId>, CompileError> {
        let Some(cseg) = segs.len().checked_sub(2).and_then(|i| segs.get(i)) else {
            return Ok(None);
        };
        let ct = &self.cx.ct;
        let mut found: Option<ClassId> = None;
        for &c in ct.by_name(cseg.name.sym) {
            let reaches = match ns {
                Ns::Method => ct.find_method(c, name).map(|(_, m)| m.item),
                Ns::Static => ct.find_static(c, name).map(|(_, m)| m.item),
                Ns::Const => ct.find_const(c, name).map(|(_, m)| m.item),
                Ns::Prop => None,
            };
            if reaches == Some(item) {
                if found.is_some_and(|f| f != c) {
                    let node = NodeRef::Item(item);
                    return Err(self.cx.unsupported(Unsupported::AmbiguousClass, node));
                }
                found = Some(c);
            }
        }
        Ok(found)
    }

    /// The receiver of the code being generated: the method's register 0,
    /// else a captured `$this`, else the scope class's token (in a closure
    /// that did not capture `$this`).
    pub(crate) fn current_receiver(&mut self) -> Option<Val> {
        if let Some(r) = self.recv {
            return Some(Val {
                reg: r,
                rel: Rel::Keep,
            });
        }
        let scope = self.scope?;
        if let Some(b) = scope.this {
            if let Some(slot) = self.cx.slot(b) {
                let r = self.fx.temp(ValType::Dyn);
                self.read_var(slot, r);
                return Some(Val {
                    reg: r,
                    rel: Rel::Temp,
                });
            }
        }
        self.token(scope.class)
    }

    /// The `$this` of the code being generated, if it has one.
    fn current_this(&mut self) -> Option<Val> {
        if self.recv.is_some() {
            return if self.instance {
                self.recv.map(|reg| Val {
                    reg,
                    rel: Rel::Keep,
                })
            } else {
                None
            };
        }
        let b = self.scope?.this?;
        let slot = self.cx.slot(b)?;
        let r = self.fx.temp(ValType::Dyn);
        self.read_var(slot, r);
        Some(Val {
            reg: r,
            rel: Rel::Temp,
        })
    }

    /// Class `c`'s token in a new temporary.
    pub(crate) fn token(&mut self, c: ClassId) -> Option<Val> {
        let g = self.cx.crt.get(c as usize)?.token?;
        let r = self.fx.temp(ValType::Dyn);
        self.emit(Inst::GetGlobal { dst: r, global: g });
        Some(Val {
            reg: r,
            rel: Rel::Temp,
        })
    }

    /// Reads a member path as a value (a constant, a static property, a
    /// late-bound one).
    pub(crate) fn member_value(
        &mut self,
        m: MemberRef,
        node: NodeRef,
        dst: Dst,
    ) -> Result<(), CompileError> {
        match m {
            MemberRef::Value {
                global,
                is_static,
                denied,
            } => {
                if let Some(d) = denied {
                    let msg = self.denial(d.ns, d.outcome, d.name);
                    self.raise_msg(&msg);
                }
                if dst == Dst::Discard {
                    return Ok(());
                }
                let r = self.result_reg(dst);
                let slot = if is_static {
                    Slot::GlobalCell(global)
                } else {
                    Slot::Global(global)
                };
                self.read_var(slot, r);
                self.produced(r, dst);
            }
            MemberRef::Late { name } => {
                let ns = self.late_ns(name);
                let r = self.result_reg(dst);
                let Some(recv) = self.current_receiver() else {
                    return Err(CompileError::Unresolved {
                        node,
                        span: self.cx.span(node),
                    });
                };
                self.late_member(r, recv.reg, ns, name);
                if ns == Ns::Static {
                    self.emit(Inst::CellGet { dst: r, cell: r });
                }
                self.release(recv);
                self.produced(r, dst);
            }
            MemberRef::ClassName(class) => {
                if dst == Dst::Discard {
                    return Ok(());
                }
                let r = self.result_reg(dst);
                match class {
                    Some(c) => {
                        let text = self.class_text(c);
                        let s = self.cx.mb.string(&text);
                        let k = self.cx.mb.constant(bytecode_lang::Const::Str(s));
                        self.emit(Inst::DLoadConst { dst: r, k });
                    }
                    None => {
                        let Some(recv) = self.current_receiver() else {
                            return Err(CompileError::Unresolved {
                                node,
                                span: self.cx.span(node),
                            });
                        };
                        let f = self.fx.temp(ValType::Dyn);
                        let n = self.lsb_ref("::class");
                        self.emit(Inst::GetProp {
                            dst: f,
                            obj: recv.reg,
                            name: n,
                        });
                        let win = self.fx.window(&[ValType::Dyn, ValType::Dyn]);
                        self.emit(Inst::Mov {
                            dst: FnCx::slot(win.1, 1),
                            src: recv.reg,
                        });
                        self.emit(Inst::DCall {
                            dst: win.1,
                            callee: f,
                            argc: 1,
                        });
                        self.emit(Inst::Mov { dst: r, src: win.1 });
                        self.fx.release_window(win.0, win.1);
                        self.fx.release(f);
                        self.release(recv);
                    }
                }
                self.produced(r, dst);
            }
            MemberRef::Missing { class, ns, name } => {
                let msg = self.missing_msg(class, ns, name);
                self.raise_msg(&msg);
                self.dummy(dst);
            }
            MemberRef::Method { .. } => {
                return Err(self.cx.unsupported(Unsupported::ClassValue, node));
            }
        }
        Ok(())
    }

    /// Whether `static::name` as a value is a static property or a
    /// constant (HIR spells both the same once the `$` is gone): a static
    /// property when some class declares one of that name.
    pub(crate) fn late_ns(&self, name: Symbol) -> Ns {
        if self.cx.ct.decls.contains_key(&(Ns::Static, name)) {
            Ns::Static
        } else {
            Ns::Const
        }
    }

    /// `dst` = the accessor result of `name` in `ns` on `recv` (a constant's
    /// value, a static property's reference).
    pub(crate) fn late_member(&mut self, dst: Reg, recv: Reg, ns: Ns, name: Symbol) {
        let win = self.fx.window(&[ValType::Dyn, ValType::Dyn]);
        let f = self.fx.temp(ValType::Dyn);
        self.select(recv, ns, name, |g, n| {
            g.emit(Inst::GetProp {
                dst: f,
                obj: recv,
                name: n,
            });
        });
        self.emit(Inst::Mov {
            dst: FnCx::slot(win.1, 1),
            src: recv,
        });
        self.emit(Inst::DCall {
            dst: win.1,
            callee: f,
            argc: 1,
        });
        self.emit(Inst::Mov { dst, src: win.1 });
        self.fx.release(f);
        self.fx.release_window(win.0, win.1);
    }

    /// A call whose callee is a member path: `C::m()`, `self::m()`,
    /// `parent::m()`, `static::m()`. Returns false when the path is no
    /// member.
    pub(crate) fn member_call(
        &mut self,
        p: PathId,
        args: &[Arg],
        dst: Dst,
        node: NodeRef,
    ) -> Result<bool, CompileError> {
        let Some(m) = self.member_path(p, Want::Call)? else {
            return Ok(false);
        };
        match m {
            MemberRef::Method {
                holder,
                item,
                named,
                is_static,
                forward,
                denied,
                name,
            } => {
                if let Some(d) = denied {
                    let msg = self.denial(d.ns, d.outcome, d.name);
                    self.raise_msg(&msg);
                    self.dummy(dst);
                    return Ok(true);
                }
                let recv = if is_static {
                    if forward {
                        self.current_receiver()
                    } else {
                        self.token(named)
                    }
                } else {
                    // An instance method through a class name: `$this`, when
                    // the code has one that is an instance of that class.
                    let usable = self
                        .scope_class()
                        .is_some_and(|s| self.cx.ct.descends(s, holder));
                    if usable { self.current_this() } else { None }
                };
                let Some(recv) = recv else {
                    let class = self.class_text(holder);
                    let n = self.cx.text(name);
                    let msg = alloc::format!(
                        "Non-static method {class}::{n}() cannot be called statically"
                    );
                    self.raise_msg(&msg);
                    self.dummy(dst);
                    return Ok(true);
                };
                self.method_direct(holder, item, recv, args, dst, node)?;
            }
            MemberRef::Late { name } => {
                let Some(recv) = self.current_receiver() else {
                    return Err(CompileError::Unresolved {
                        node,
                        span: self.cx.span(node),
                    });
                };
                let f = self.fx.temp(ValType::Dyn);
                self.method_lookup(f, recv.reg, name);
                self.vals.push(recv);
                self.vals.push(Val {
                    reg: f,
                    rel: Rel::Temp,
                });
                self.call_step(super::call::CallStep::ValueBegin {
                    args: args.to_vec(),
                    recv: true,
                    dst,
                    node,
                })?;
            }
            MemberRef::Missing { class, ns, name } => {
                let msg = self.missing_msg(class, ns, name);
                self.raise_msg(&msg);
                self.dummy(dst);
            }
            MemberRef::Value { .. } | MemberRef::ClassName(_) => {
                // A callable stored in a constant or static property.
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Calls method `item` compiled for `holder` with the receiver `recv`
    /// (released after the call) and `args`.
    pub(crate) fn method_direct(
        &mut self,
        holder: ClassId,
        item: ItemId,
        recv: Val,
        args: &[Arg],
        dst: Dst,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let Some(info) = self.cx.methods.get(&(holder, item)).cloned() else {
            // An abstract method.
            self.release(recv);
            self.raise_msg("Cannot call abstract method");
            self.dummy(dst);
            return Ok(());
        };
        self.direct_with(&info, Some(recv), args, dst, node)
    }

    // ------------------------------------------------------------ new

    /// A class operation of the intrinsic table (`new`, `instanceof`,
    /// `clone`) over `args`, its class given by `ty` (a generic argument)
    /// or by its class operand (`new`'s first, `instanceof`'s second).
    pub(crate) fn class_op(
        &mut self,
        op: crate::ClassOp,
        host: (String, String),
        ty: Option<hir_lang::TyId>,
        args: &[Arg],
        dst: Dst,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let need = match (op, ty) {
            (crate::ClassOp::New, None) => 1,
            (crate::ClassOp::InstanceOf, None) => 2,
            (crate::ClassOp::InstanceOf, Some(_)) | (crate::ClassOp::Clone, _) => 1,
            _ => 0,
        };
        let exact = !matches!(op, crate::ClassOp::New);
        if args.len() < need || (exact && args.len() != need) {
            return Err(CompileError::IntrinsicArity {
                node,
                span: self.cx.span(node),
                arity: if exact {
                    crate::Arity::exact(need as u8)
                } else {
                    crate::Arity::at_least(need as u8)
                },
                found: u32::try_from(args.len()).unwrap_or(u32::MAX),
            });
        }
        let typed = match ty {
            Some(t) => Some(self.class_type_operand(t)?),
            None => None,
        };
        match op {
            crate::ClassOp::New => {
                let (class, rest, cls) = match typed {
                    Some(c) => (c, args.to_vec(), None),
                    None => {
                        let cls = args.first().map(|a| a.value);
                        let class = match cls {
                            Some(c) => self.class_operand(c)?,
                            None => None,
                        };
                        (class, args.get(1..).unwrap_or(&[]).to_vec(), cls)
                    }
                };
                match class {
                    Some(ClassRef::Known(c)) => self.new_static(c, &rest, dst, node),
                    Some(ClassRef::Late) => {
                        let Some(recv) = self.current_receiver() else {
                            return Err(CompileError::Unresolved {
                                node,
                                span: self.cx.span(node),
                            });
                        };
                        self.vals.push(recv);
                        self.class_step(ClassStep::NewDyn {
                            args: rest,
                            host,
                            dst,
                            node,
                        })
                    }
                    None => {
                        let Some(cls) = cls else {
                            // A type operand that names no class of the unit.
                            return Err(self.cx.unsupported(Unsupported::ClassTest, node));
                        };
                        self.sched([
                            Task::Expr(cls, Dst::Temp),
                            Task::Step(Step::Class(ClassStep::NewDyn {
                                args: rest,
                                host,
                                dst,
                                node,
                            })),
                        ]);
                        Ok(())
                    }
                }
            }
            crate::ClassOp::InstanceOf => {
                let Some(x) = args.first().map(|a| a.value) else {
                    return Ok(());
                };
                let (class, cls) = match typed {
                    Some(c) => (c, None),
                    None => {
                        let cls = args.get(1).map(|a| a.value);
                        let class = match cls {
                            Some(c) => self.class_operand(c)?,
                            None => None,
                        };
                        (class, cls)
                    }
                };
                let step = Task::Step(Step::Class(ClassStep::InstanceOf {
                    class,
                    host,
                    dst,
                    node,
                }));
                match (class, cls) {
                    (Some(_), _) => self.sched([Task::Expr(x, Dst::Temp), step]),
                    (None, Some(cls)) => {
                        self.sched([Task::Expr(x, Dst::Temp), Task::Expr(cls, Dst::Temp), step])
                    }
                    (None, None) => {
                        return Err(self.cx.unsupported(Unsupported::ClassTest, node));
                    }
                }
                Ok(())
            }
            crate::ClassOp::Clone => {
                let Some(x) = args.first().map(|a| a.value) else {
                    return Ok(());
                };
                self.sched([
                    Task::Expr(x, Dst::Temp),
                    Task::Step(Step::Class(ClassStep::Clone { host, dst, node })),
                ]);
                Ok(())
            }
        }
    }

    /// `new C(args)` for a class of the unit: allocate (the struct and its
    /// property defaults), then the constructor with the arguments.
    fn new_static(
        &mut self,
        c: ClassId,
        args: &[Arg],
        dst: Dst,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let Some(d) = self.cx.ct.get(c) else {
            return Ok(());
        };
        if !d.instantiable() {
            let what = match d.kind {
                CKind::Interface => "interface",
                CKind::Mixin => "trait",
                CKind::Class => "abstract class",
            };
            let msg = alloc::format!("Cannot instantiate {what} {}", d.text);
            self.raise_msg(&msg);
            self.dummy(dst);
            return Ok(());
        }
        let Some(alloc) = self.cx.crt.get(c as usize).and_then(|r| r.alloc) else {
            return Ok(());
        };
        let ctor = self
            .cx
            .opts
            .constructor()
            .and_then(|n| self.ctor_symbol(n))
            .and_then(|sym| self.cx.ct.find_method(c, sym).map(|(h, m)| (h, m, sym)))
            .filter(|(_, m, _)| m.body);
        if let Some((holder, m, sym)) = ctor {
            let outcome =
                self.cx
                    .ct
                    .static_access(self.scope_class(), holder, Ns::Method, sym, m.vis);
            if outcome != Outcome::Ok {
                let msg = self.denial(Ns::Method, outcome, sym);
                self.raise_msg(&msg);
                self.dummy(dst);
                return Ok(());
            }
        }
        // The instance, in its own temporary until it is the result.
        let obj = self.fx.temp(ValType::Dyn);
        let win = self.fx.window(&[ValType::Dyn, ValType::Dyn]);
        self.emit(Inst::LoadNil {
            dst: FnCx::slot(win.1, 1),
        });
        self.emit(Inst::Call {
            dst: win.1,
            func: alloc,
            argc: 1,
        });
        self.emit(Inst::Mov {
            dst: obj,
            src: win.1,
        });
        self.fx.release_window(win.0, win.1);
        let result = Val {
            reg: obj,
            rel: Rel::Temp,
        };
        match ctor {
            Some((holder, m, _)) => {
                self.sched([Task::Push(result), Task::Deliver { dst, dup: false }]);
                let recv = Val {
                    reg: obj,
                    rel: Rel::Keep,
                };
                self.method_direct(holder, m.item, recv, args, Dst::Discard, node)?;
            }
            None => {
                // No constructor: the arguments are evaluated and dropped.
                let mut ts: Vec<Task> = args
                    .iter()
                    .map(|a| Task::Expr(a.value, Dst::Discard))
                    .collect();
                ts.push(Task::At(node));
                ts.push(Task::Push(result));
                ts.push(Task::Deliver { dst, dup: false });
                self.sched_all(ts);
            }
        }
        Ok(())
    }

    /// The symbol of a configured magic method name, if the unit uses it as
    /// a method name anywhere.
    fn ctor_symbol(&self, name: &str) -> Option<Symbol> {
        self.cx.names.get(name)
    }

    /// The token of the class a run-time class value names, into `tok`
    /// (nil when the unit does not declare it): an object's own class, or a
    /// registered name.
    fn class_of(&mut self, tok: Reg, v: Reg) {
        let f = self.cx.class_of_fn();
        let win = self.fx.window(&[ValType::Dyn, ValType::Dyn]);
        self.emit(Inst::Mov {
            dst: FnCx::slot(win.1, 1),
            src: v,
        });
        self.emit(Inst::Call {
            dst: win.1,
            func: f,
            argc: 1,
        });
        self.emit(Inst::Mov {
            dst: tok,
            src: win.1,
        });
        self.fx.release_window(win.0, win.1);
    }

    pub(crate) fn class_step(&mut self, s: ClassStep) -> Result<(), CompileError> {
        match s {
            ClassStep::NewDyn {
                args,
                host,
                dst,
                node,
            } => {
                self.at(node);
                let cls = self.pop();
                let tok = self.fx.temp(ValType::Dyn);
                let obj = self.fx.temp(ValType::Dyn);
                let callee = self.fx.temp(ValType::Dyn);
                self.class_of(tok, cls.reg);
                let (missing, ready) = (self.label(), self.label());
                let b = self.fx.temp(ValType::Bool);
                self.emit(Inst::IsKind {
                    dst: b,
                    src: tok,
                    kind: Kind::Nil,
                });
                self.jump_on(b, missing, true);
                // `::new` of the class (an abstract class's raises).
                let n = self.lsb_ref("::new");
                let win = self.fx.window(&[ValType::Dyn, ValType::Dyn]);
                self.emit(Inst::GetProp {
                    dst: callee,
                    obj: tok,
                    name: n,
                });
                self.emit(Inst::Mov {
                    dst: FnCx::slot(win.1, 1),
                    src: tok,
                });
                self.emit(Inst::DCall {
                    dst: win.1,
                    callee,
                    argc: 1,
                });
                self.emit(Inst::Mov {
                    dst: obj,
                    src: win.1,
                });
                self.fx.release_window(win.0, win.1);
                // The constructor, else a function taking anything.
                let noop = self.cx.noop_fn();
                self.emit(Inst::MakeClosure {
                    dst: callee,
                    func: noop,
                });
                if let Some(sym) = self
                    .cx
                    .opts
                    .constructor()
                    .and_then(|name| self.ctor_symbol(name))
                {
                    self.magic_lookup(callee, obj, sym, b);
                }
                self.jmp(ready);
                self.bind(missing);
                self.emit(Inst::LoadNil { dst: obj });
                self.emit(Inst::MakeClosure {
                    dst: callee,
                    func: noop,
                });
                self.bind(ready);
                self.fx.release(b);
                // The receiver (the instance) and the callee, then the
                // arguments; `NewFinish` calls.
                self.vals.push(Val {
                    reg: obj,
                    rel: Rel::Keep,
                });
                self.vals.push(Val {
                    reg: callee,
                    rel: Rel::Temp,
                });
                self.new_args(args, tok, cls, obj, host, dst, node)?;
            }
            ClassStep::NewFinish {
                win,
                kinds,
                tok,
                cls,
                obj,
                host,
                dst,
                node,
            } => {
                self.at(node);
                let callee = self.pop();
                let recv = self.pop();
                self.release(recv);
                let r = self.result_reg(dst);
                let (missing, done) = (self.label(), self.label());
                let b = self.fx.temp(ValType::Bool);
                self.emit(Inst::IsKind {
                    dst: b,
                    src: tok,
                    kind: Kind::Nil,
                });
                self.jump_on(b, missing, true);
                self.fx.release(b);
                self.dynamic_call(win, &kinds, callee.reg);
                self.emit(Inst::Mov { dst: r, src: obj });
                self.jmp(done);
                self.bind(missing);
                // Not a class of the unit: the host function, with the
                // class value and the positional arguments.
                let user = kinds.len().saturating_sub(1);
                if kinds
                    .iter()
                    .skip(1)
                    .all(|k| *k == bytecode_lang::ArgKind::Positional)
                    && user < crate::unit::MAX_ARITY
                {
                    let argc = u8::try_from(user + 1).unwrap_or(u8::MAX);
                    let import = self.cx.import(&host.0, &host.1, argc);
                    let shape = alloc::vec![ValType::Dyn; user + 2];
                    let hw = self.fx.window(&shape);
                    self.emit(Inst::Mov {
                        dst: FnCx::slot(hw.1, 1),
                        src: cls,
                    });
                    for i in 0..user {
                        self.emit(Inst::Mov {
                            dst: FnCx::slot(hw.1, i + 2),
                            src: FnCx::slot(win.1, i + 2),
                        });
                    }
                    self.emit(Inst::CallImport {
                        dst: hw.1,
                        import,
                        argc,
                    });
                    self.emit(Inst::Mov { dst: r, src: hw.1 });
                    self.fx.release_window(hw.0, hw.1);
                } else {
                    self.raise_kind(ErrorKind::ArgumentError);
                }
                self.bind(done);
                self.fx.release_window(win.0, win.1);
                self.release(callee);
                self.fx.release(tok);
                self.fx.release(obj);
                self.fx.release(cls);
                self.produced(r, dst);
            }
            ClassStep::InstanceOf {
                class,
                host,
                dst,
                node,
            } => {
                self.at(node);
                let cls = match class {
                    None => Some(self.pop()),
                    Some(_) => None,
                };
                let x = self.pop();
                let r = self.result_reg(dst);
                match class {
                    Some(ClassRef::Known(c)) => {
                        let b = self.fx.temp(ValType::Bool);
                        self.instance_test(b, x.reg, c);
                        self.emit(Inst::ToDyn {
                            dst: r,
                            src: b,
                            from: bytecode_lang::Prim::Bool,
                        });
                        self.fx.release(b);
                    }
                    _ => {
                        let cls = match cls {
                            Some(v) => v,
                            None => match self.current_receiver() {
                                Some(v) => v,
                                None => {
                                    return Err(CompileError::Unresolved {
                                        node,
                                        span: self.cx.span(node),
                                    });
                                }
                            },
                        };
                        self.dynamic_instanceof(r, x.reg, cls.reg, &host);
                        self.release(cls);
                    }
                }
                self.release(x);
                self.produced(r, dst);
            }
            ClassStep::LateRef { name, node } => {
                self.at(node);
                let Some(recv) = self.current_receiver() else {
                    return Err(CompileError::Unresolved {
                        node,
                        span: self.cx.span(node),
                    });
                };
                let r = self.fx.temp(ValType::Dyn);
                self.late_member(r, recv.reg, Ns::Static, name);
                self.release(recv);
                self.vals.push(Val {
                    reg: r,
                    rel: Rel::Temp,
                });
            }
            ClassStep::Clone { host, dst, node } => {
                self.at(node);
                let x = self.pop();
                let r = self.result_reg(dst);
                self.clone_value(r, x.reg, &host);
                self.release(x);
                self.produced(r, dst);
            }
        }
        Ok(())
    }

    /// Schedules the arguments of a dynamic `new` into a call window whose
    /// receiver slot holds the instance.
    #[allow(clippy::too_many_arguments)]
    fn new_args(
        &mut self,
        args: Vec<Arg>,
        tok: Reg,
        cls: Val,
        obj: Reg,
        host: (String, String),
        dst: Dst,
        node: NodeRef,
    ) -> Result<(), CompileError> {
        let (win, kinds, ts) = self.dynamic_args(&args, true, node)?;
        let cls_reg = match cls.rel {
            Rel::Keep => {
                let t = self.fx.temp(ValType::Dyn);
                self.emit(Inst::Mov {
                    dst: t,
                    src: cls.reg,
                });
                t
            }
            _ => cls.reg,
        };
        let mut ts = ts;
        ts.push(Task::Step(Step::Class(ClassStep::NewFinish {
            win,
            kinds,
            tok,
            cls: cls_reg,
            obj,
            host,
            dst,
            node,
        })));
        self.sched_all(ts);
        Ok(())
    }

    /// `b = x instanceof c` for a class or interface of the unit.
    pub(crate) fn instance_test(&mut self, b: Reg, x: Reg, c: ClassId) {
        let kind = self.cx.ct.get(c).map(|d| d.kind);
        match kind {
            Some(CKind::Class) => match self.class_ref(c) {
                Some(tr) => self.emit(Inst::IsType {
                    dst: b,
                    src: x,
                    ty: tr,
                }),
                None => self.emit(Inst::LoadBool { dst: b, val: false }),
            },
            Some(CKind::Interface) => {
                let done = self.label();
                self.emit(Inst::IsKind {
                    dst: b,
                    src: x,
                    kind: Kind::Object,
                });
                self.jump_on(b, done, false);
                let mut marker = String::from("::is ");
                marker.push_str(&self.lsb_of(c));
                let n = self.lsb_ref(&marker);
                self.emit(Inst::HasProp {
                    dst: b,
                    obj: x,
                    name: n,
                });
                self.bind(done);
            }
            // A mixin is never instantiated (PHP: `instanceof` a trait is
            // false).
            _ => self.emit(Inst::LoadBool { dst: b, val: false }),
        }
    }

    /// `r = x instanceof cls` for a class value only known at run time.
    fn dynamic_instanceof(&mut self, r: Reg, x: Reg, cls: Reg, host: &(String, String)) {
        let tok = self.fx.temp(ValType::Dyn);
        self.class_of(tok, cls);
        let (missing, done) = (self.label(), self.label());
        let b = self.fx.temp(ValType::Bool);
        self.emit(Inst::IsKind {
            dst: b,
            src: tok,
            kind: Kind::Nil,
        });
        self.jump_on(b, missing, true);
        self.fx.release(b);
        let f = self.fx.temp(ValType::Dyn);
        let n = self.lsb_ref("::test");
        self.emit(Inst::GetProp {
            dst: f,
            obj: tok,
            name: n,
        });
        let win = self.fx.window(&[ValType::Dyn, ValType::Dyn, ValType::Dyn]);
        self.emit(Inst::Mov {
            dst: FnCx::slot(win.1, 1),
            src: tok,
        });
        self.emit(Inst::Mov {
            dst: FnCx::slot(win.1, 2),
            src: x,
        });
        self.emit(Inst::DCall {
            dst: win.1,
            callee: f,
            argc: 2,
        });
        self.emit(Inst::Mov { dst: r, src: win.1 });
        self.fx.release_window(win.0, win.1);
        self.fx.release(f);
        self.jmp(done);
        self.bind(missing);
        self.host_call(r, host, &[x, cls]);
        self.bind(done);
        self.fx.release(tok);
    }

    /// `r = clone x`: an instance of a unit class is `dup`ed and its clone
    /// method runs on the copy; anything else goes to the host function.
    fn clone_value(&mut self, r: Reg, x: Reg, host: &(String, String)) {
        let (other, done) = (self.label(), self.label());
        let b = self.fx.temp(ValType::Bool);
        // Objects of the unit's classes (a host object is the host's).
        self.emit(Inst::IsKind {
            dst: b,
            src: x,
            kind: Kind::Object,
        });
        self.jump_on(b, other, false);
        let n = self.lsb_ref("::test");
        self.emit(Inst::HasProp {
            dst: b,
            obj: x,
            name: n,
        });
        self.jump_on(b, other, false);
        self.emit(Inst::Dup { dst: r, src: x });
        if let Some(sym) = self
            .cx
            .opts
            .clone_method()
            .and_then(|name| self.ctor_symbol(name))
        {
            let skip = self.label();
            let f = self.fx.temp(ValType::Dyn);
            self.emit(Inst::LoadNil { dst: f });
            self.magic_lookup(f, r, sym, b);
            self.emit(Inst::IsKind {
                dst: b,
                src: f,
                kind: Kind::Nil,
            });
            self.jump_on(b, skip, true);
            let win = self.fx.window(&[ValType::Dyn, ValType::Dyn]);
            self.emit(Inst::Mov {
                dst: FnCx::slot(win.1, 1),
                src: r,
            });
            self.emit(Inst::DCall {
                dst: win.1,
                callee: f,
                argc: 1,
            });
            self.fx.release_window(win.0, win.1);
            self.fx.release(f);
            self.bind(skip);
        }
        self.jmp(done);
        self.bind(other);
        self.host_call(r, host, &[x]);
        self.bind(done);
        self.fx.release(b);
    }

    /// `f` = the magic method `sym` (a constructor, a clone method) of the
    /// instance `obj` when its class has one, by the scope's plan (a
    /// visibility violation raises); `f` is left as it is when there is
    /// none.
    fn magic_lookup(&mut self, f: Reg, obj: Reg, sym: Symbol, b: Reg) {
        let text = self.cx.text(sym);
        let public = lsb_name(Ns::Method, &text, None);
        let public = self.lsb_ref(&public);
        let (found, none) = (self.label(), self.label());
        let private = self
            .scope_class()
            .filter(|&s| self.cx.ct.scope_private(Some(s), Ns::Method, sym));
        if let Some(s) = private {
            let lsb = self.lsb_of(s);
            let p = lsb_name(Ns::Method, &text, Some(&lsb));
            let p = self.lsb_ref(&p);
            let next = self.label();
            self.emit(Inst::HasProp {
                dst: b,
                obj,
                name: p,
            });
            self.jump_on(b, next, false);
            self.emit(Inst::GetProp {
                dst: f,
                obj,
                name: p,
            });
            self.jmp(found);
            self.bind(next);
        }
        self.emit(Inst::HasProp {
            dst: b,
            obj,
            name: public,
        });
        self.jump_on(b, none, false);
        let plan = self.plan(Ns::Method, sym);
        self.checks(obj, Ns::Method, sym, &plan);
        self.emit(Inst::GetProp {
            dst: f,
            obj,
            name: public,
        });
        self.jmp(found);
        self.bind(none);
        self.bind(found);
    }

    /// `r = module.name(args..)`.
    fn host_call(&mut self, r: Reg, host: &(String, String), args: &[Reg]) {
        let argc = u8::try_from(args.len()).unwrap_or(u8::MAX);
        let import = self.cx.import(&host.0, &host.1, argc);
        let shape = alloc::vec![ValType::Dyn; args.len() + 1];
        let win = self.fx.window(&shape);
        for (i, &a) in args.iter().enumerate() {
            self.emit(Inst::Mov {
                dst: FnCx::slot(win.1, i + 1),
                src: a,
            });
        }
        self.emit(Inst::CallImport {
            dst: win.1,
            import,
            argc,
        });
        self.emit(Inst::Mov { dst: r, src: win.1 });
        self.fx.release_window(win.0, win.1);
    }

    // ------------------------------------------------------------ type tests

    /// Jumps to `ok` when `v` is an instance of a class or interface a type
    /// term names (a path to one of the unit's); `Ok(false)` when the type
    /// names none.
    pub(crate) fn class_type_test(
        &mut self,
        v: Reg,
        ty: hir_lang::TyId,
        ok: bytecode_lang::Label,
    ) -> Result<bool, CompileError> {
        let hir = self.cx.hir;
        let hir_lang::Ty::Path(p) = *hir.ty(ty) else {
            return Ok(false);
        };
        let path = *hir.path(p);
        let node = NodeRef::Path(p);
        let class = match path.res {
            Res::Def(_) if path.unresolved == 0 => self.cx.ct.of_res(hir, path.res, node)?,
            Res::Def(_) | Res::Extern(_) => {
                return Err(self.cx.unsupported(Unsupported::ClassTest, node));
            }
            _ => None,
        };
        let class = match (class, path.root) {
            (Some(c), _) => Some(c),
            (None, PathRoot::SelfType | PathRoot::ParentType)
                if hir.list(path.segments).is_empty() =>
            {
                let s = self.scope_class();
                if path.root == PathRoot::ParentType {
                    s.and_then(|s| self.cx.ct.get(s)).and_then(|d| d.parent)
                } else {
                    s
                }
            }
            _ => None,
        };
        let Some(c) = class else {
            return Ok(false);
        };
        let b = self.fx.temp(ValType::Bool);
        self.instance_test(b, v, c);
        self.jump_on(b, ok, true);
        self.fx.release(b);
        Ok(true)
    }

    // ------------------------------------------------------------ synthetic

    /// Generates a synthetic class function.
    pub(crate) fn class_job(&mut self, what: ClassJob) -> Result<(), CompileError> {
        match what {
            ClassJob::Alloc(c) => self.alloc_body(c),
            ClassJob::Test(c) => {
                let b = self.fx.temp(ValType::Bool);
                let r = self.fx.temp(ValType::Dyn);
                self.instance_test(b, Reg(1), c);
                self.emit(Inst::ToDyn {
                    dst: r,
                    src: b,
                    from: bytecode_lang::Prim::Bool,
                });
                self.emit(Inst::Ret { src: r });
                Ok(())
            }
            ClassJob::Name(c) => {
                let text = self.class_text(c);
                let s = self.cx.mb.string(&text);
                let k = self.cx.mb.constant(bytecode_lang::Const::Str(s));
                let r = self.fx.temp(ValType::Dyn);
                self.emit(Inst::DLoadConst { dst: r, k });
                self.emit(Inst::Ret { src: r });
                Ok(())
            }
            ClassJob::Accessor(g) => {
                let r = self.fx.temp(ValType::Dyn);
                self.emit(Inst::GetGlobal { dst: r, global: g });
                self.emit(Inst::Ret { src: r });
                Ok(())
            }
            ClassJob::Marker | ClassJob::Noop => {
                let r = self.fx.temp(ValType::Dyn);
                self.emit(Inst::LoadNil { dst: r });
                self.emit(Inst::Ret { src: r });
                Ok(())
            }
            ClassJob::ClassOf => {
                self.class_of_body();
                Ok(())
            }
            ClassJob::Dyn(_, op) => {
                self.dyn_body(op);
                Ok(())
            }
            ClassJob::Vis(ns, name) => {
                self.vis_body(ns, name);
                Ok(())
            }
        }
    }

    /// `::new`: a new instance with its property defaults (each evaluated in
    /// the scope of the class that declared it); an abstract class, an
    /// interface raises.
    fn alloc_body(&mut self, c: ClassId) -> Result<(), CompileError> {
        let Some(d) = self.cx.ct.get(c).cloned() else {
            return Ok(());
        };
        if !d.instantiable() {
            let what = if d.kind == CKind::Interface {
                "interface"
            } else {
                "abstract class"
            };
            let msg = alloc::format!("Cannot instantiate {what} {}", d.text);
            self.raise_msg(&msg);
            let r = self.fx.temp(ValType::Dyn);
            self.emit(Inst::LoadNil { dst: r });
            self.emit(Inst::Ret { src: r });
            return Ok(());
        }
        let Some(ty) = self.cx.crt.get(c as usize).and_then(|r| r.ty) else {
            return Ok(());
        };
        let tr = self.fx.f.type_ref(ty);
        let obj = self.fx.temp(ValType::Ref(ty));
        self.emit(Inst::NewStruct { dst: obj, ty: tr });
        let layout = self
            .cx
            .ct
            .layout
            .get(c as usize)
            .cloned()
            .unwrap_or_default();
        let mut ts: Vec<Task> = Vec::new();
        let saved = self.scope;
        for (i, slot) in layout.iter().enumerate() {
            let Some((e, ctx)) = slot.default else {
                continue;
            };
            let field = bytecode_lang::FieldIdx(u16::try_from(i).unwrap_or(u16::MAX));
            ts.push(Task::SetScope(Some(crate::unit::ClassScope {
                class: ctx,
                this: None,
            })));
            let dup = self.needs_dup(e);
            ts.push(Task::Expr(e, Dst::Any));
            if dup {
                ts.push(Task::Deliver {
                    dst: Dst::Any,
                    dup: true,
                });
            }
            ts.push(Task::Step(Step::SetField { obj, field }));
        }
        ts.push(Task::SetScope(saved));
        let r = self.fx.temp(ValType::Dyn);
        ts.push(Task::Emit(Inst::Mov { dst: r, src: obj }));
        ts.push(Task::Emit(Inst::Ret { src: r }));
        self.sched_all(ts);
        self.run()
    }

    /// `obj->{name}` by a run-time name: on an object, a binary search over
    /// the unit's property (or method) names, each leaf the current scope's
    /// access to that name ([`select`](Self::select),
    /// [`method_lookup`](Self::method_lookup)); a name no class declares
    /// raises `UndefinedProperty` with the name. Anything else keeps LSB's
    /// `dget_index`/`dset_index` (maps, host values).
    fn dyn_body(&mut self, op: crate::unit::DynOp) {
        use crate::unit::DynOp;
        let (obj, key, val) = (Reg(0), Reg(1), Reg(2));
        let r = self.fx.temp(ValType::Dyn);
        let b = self.fx.temp(ValType::Bool);
        let (object, miss) = (self.label(), self.label());
        self.emit(Inst::IsKind {
            dst: b,
            src: obj,
            kind: Kind::Object,
        });
        self.jump_on(b, object, true);
        match op {
            DynOp::Set => {
                self.emit(Inst::DSetIndex { obj, key, src: val });
                self.emit(Inst::Ret { src: val });
            }
            _ => {
                self.emit(Inst::DGetIndex { dst: r, obj, key });
                self.emit(Inst::Ret { src: r });
            }
        }
        self.bind(object);
        self.emit(Inst::IsKind {
            dst: b,
            src: key,
            kind: Kind::Str,
        });
        self.jump_on(b, miss, false);
        let ns = if op == DynOp::Method {
            Ns::Method
        } else {
            Ns::Prop
        };
        // The names, sorted by their bytes (`str_cmp`'s order).
        let mut names: Vec<(String, Symbol)> = self
            .cx
            .ct
            .decls
            .keys()
            .filter(|(n, _)| *n == ns)
            .map(|&(_, sym)| (self.cx.text(sym), sym))
            .collect();
        names.sort();
        names.dedup_by(|a, b| a.0 == b.0);
        let s = self.fx.temp(ValType::Str);
        self.emit(Inst::FromDyn {
            dst: s,
            src: key,
            to: bytecode_lang::Prim::Str,
        });
        let k = self.fx.temp(ValType::Str);
        let c = self.fx.temp(ValType::I8);
        let z = self.fx.temp(ValType::I8);
        self.emit(Inst::LoadInt {
            dst: z,
            val: 0,
            ty: IntTy::I8,
        });
        // Iterative binary search: (lo, hi, entry label).
        let mut leaves: Vec<bytecode_lang::Label> = names.iter().map(|_| self.label()).collect();
        let first = self.label();
        self.jmp(first);
        let mut stack: Vec<(usize, usize, bytecode_lang::Label)> =
            alloc::vec![(0, names.len(), first)];
        while let Some((lo, hi, at)) = stack.pop() {
            self.bind(at);
            if hi <= lo {
                self.jmp(miss);
                continue;
            }
            let mid = lo + (hi - lo) / 2;
            let (left, right) = (self.label(), self.label());
            let text = names.get(mid).map(|(t, _)| t.clone()).unwrap_or_default();
            let sid = self.cx.mb.string(&text);
            let kc = self.cx.mb.constant(bytecode_lang::Const::Str(sid));
            self.emit(Inst::LoadConst { dst: k, k: kc });
            self.emit(Inst::StrCmp {
                dst: c,
                lhs: s,
                rhs: k,
            });
            self.emit(Inst::IEq {
                dst: b,
                lhs: c,
                rhs: z,
                ty: IntTy::I8,
            });
            if let Some(&leaf) = leaves.get(mid) {
                self.jump_on(b, leaf, true);
            }
            self.emit(Inst::ILt {
                dst: b,
                lhs: c,
                rhs: z,
                ty: IntTy::I8,
            });
            self.jump_on(b, left, true);
            self.jmp(right);
            stack.push((mid + 1, hi, right));
            stack.push((lo, mid, left));
        }
        for (i, (_, sym)) in names.iter().enumerate() {
            let Some(leaf) = leaves.get_mut(i).map(|l| *l) else {
                continue;
            };
            self.bind(leaf);
            match op {
                DynOp::Get => self.prop_get(r, obj, *sym),
                DynOp::Set => {
                    self.prop_set(obj, *sym, val);
                    self.emit(Inst::Mov { dst: r, src: val });
                }
                DynOp::Method => self.method_lookup(r, obj, *sym),
            }
            self.emit(Inst::Ret { src: r });
        }
        leaves.clear();
        self.bind(miss);
        self.emit(Inst::Raise {
            src: key,
            kind: ErrorKind::UndefinedProperty,
        });
        // `raise` always raises, but the loader wants a block end.
        self.emit(Inst::Ret { src: r });
        for x in [z, c, k, s, b, r] {
            self.fx.release(x);
        }
    }

    /// `dst = obj->{key}` (`dset` with `src`) through the by-name access
    /// function of the current scope (classes in the unit), else LSB's
    /// indexing (0.3).
    pub(crate) fn dyn_access(
        &mut self,
        op: crate::unit::DynOp,
        dst: Reg,
        obj: Reg,
        key: Reg,
        src: Option<Reg>,
    ) {
        use crate::unit::DynOp;
        if self.cx.ct.is_empty() {
            match (op, src) {
                (DynOp::Set, Some(v)) => self.emit(Inst::DSetIndex { obj, key, src: v }),
                _ => self.emit(Inst::DGetIndex { dst, obj, key }),
            }
            return;
        }
        let f = self.cx.dyn_fn(self.scope_class(), op);
        let shape: &[ValType] = if op == DynOp::Set {
            &[ValType::Dyn, ValType::Dyn, ValType::Dyn, ValType::Dyn]
        } else {
            &[ValType::Dyn, ValType::Dyn, ValType::Dyn]
        };
        let win = self.fx.window(shape);
        self.emit(Inst::Mov {
            dst: FnCx::slot(win.1, 1),
            src: obj,
        });
        self.emit(Inst::Mov {
            dst: FnCx::slot(win.1, 2),
            src: key,
        });
        if let (DynOp::Set, Some(v)) = (op, src) {
            self.emit(Inst::Mov {
                dst: FnCx::slot(win.1, 3),
                src: v,
            });
        }
        let argc = if op == DynOp::Set { 3 } else { 2 };
        self.emit(Inst::Call {
            dst: win.1,
            func: f,
            argc,
        });
        if op != DynOp::Set {
            self.emit(Inst::Mov { dst, src: win.1 });
        }
        self.fx.release_window(win.0, win.1);
    }

    /// `<class_of>(v)`: an object is its own class's token (its `::new`
    /// and `::test` are found through it); a string is looked up in the
    /// registry; anything else is nil.
    fn class_of_body(&mut self) {
        let v = Reg(0);
        let r = self.fx.temp(ValType::Dyn);
        let b = self.fx.temp(ValType::Bool);
        let (string, none) = (self.label(), self.label());
        self.emit(Inst::IsKind {
            dst: b,
            src: v,
            kind: Kind::Object,
        });
        self.jump_on(b, string, false);
        // An object of a unit class (a host object is not one).
        let n = self.lsb_ref("::test");
        self.emit(Inst::HasProp {
            dst: b,
            obj: v,
            name: n,
        });
        self.jump_on(b, none, false);
        self.emit(Inst::Ret { src: v });
        self.bind(string);
        self.emit(Inst::IsKind {
            dst: b,
            src: v,
            kind: Kind::Str,
        });
        self.jump_on(b, none, false);
        if let Some(g) = self.cx.registry {
            let mt = self.map_ty();
            let tr = self.map_ref();
            let m = self.fx.temp(mt);
            self.emit(Inst::GetGlobal { dst: r, global: g });
            self.emit(Inst::Cast {
                dst: m,
                src: r,
                ty: tr,
            });
            self.emit(Inst::MapFind {
                dst: r,
                map: m,
                key: v,
            });
            self.emit(Inst::Ret { src: r });
            self.fx.release(m);
        }
        self.bind(none);
        self.emit(Inst::LoadNil { dst: r });
        self.emit(Inst::Ret { src: r });
    }

    /// The start function's class prologue: every token, then the registry
    /// of class names.
    pub(crate) fn class_prologue(&mut self) {
        let n = self.cx.ct.len();
        let t = self.fx.temp(ValType::Dyn);
        for c in 0..n {
            let Some(rt) = self.cx.crt.get(c).copied() else {
                continue;
            };
            let (Some(ty), Some(g)) = (rt.ty, rt.token) else {
                continue;
            };
            let tr = self.fx.f.type_ref(ty);
            self.emit(Inst::NewStruct { dst: t, ty: tr });
            self.emit(Inst::SetGlobal { global: g, src: t });
        }
        if let Some(reg) = self.cx.registry {
            let m = self.new_map();
            for c in 0..n {
                let Some(g) = self.cx.crt.get(c).and_then(|rt| rt.token) else {
                    continue;
                };
                let Some(d) = self.cx.ct.classes.get(c) else {
                    continue;
                };
                if d.text.is_empty() {
                    continue;
                }
                let s = self.cx.mb.string(&d.text.clone());
                let k = self.cx.mb.constant(bytecode_lang::Const::Str(s));
                let key = self.fx.temp(ValType::Dyn);
                self.emit(Inst::DLoadConst { dst: key, k });
                self.emit(Inst::GetGlobal { dst: t, global: g });
                // The first class of a name wins.
                let b = self.fx.temp(ValType::Bool);
                let skip = self.label();
                self.emit(Inst::MapHas {
                    dst: b,
                    map: m,
                    key,
                });
                self.jump_on(b, skip, true);
                self.emit(Inst::MapSet {
                    map: m,
                    key,
                    src: t,
                });
                self.bind(skip);
                self.fx.release(b);
                self.fx.release(key);
            }
            self.emit(Inst::Mov { dst: t, src: m });
            self.emit(Inst::SetGlobal {
                global: reg,
                src: t,
            });
            self.fx.release(m);
        }
        self.fx.release(t);
    }

    /// The start-function tasks of class item `item`: its static
    /// properties (a reference holding the initial value) and constants
    /// with code, in its scope.
    pub(crate) fn class_inits(&mut self, item: ItemId, ts: &mut Vec<Task>) {
        let Some(&c) = self.cx.ct.by_item.get(&item) else {
            return;
        };
        let Some(d) = self.cx.ct.get(c).cloned() else {
            return;
        };
        if d.kind == CKind::Mixin {
            return;
        }
        let hir = self.cx.hir;
        ts.push(Task::SetScope(Some(crate::unit::ClassScope {
            class: c,
            this: None,
        })));
        for s in &d.statics {
            let Some(&g) = self.cx.member_globals.get(&(c, s.item)) else {
                continue;
            };
            ts.push(Task::At(NodeRef::Item(s.item)));
            let init = match hir.item(s.item).kind {
                ItemKind::Global { init, .. } => init,
                _ => None,
            };
            match init {
                Some(e) => {
                    let dup = self.needs_dup(e);
                    ts.push(Task::Expr(e, Dst::Any));
                    if dup {
                        ts.push(Task::Deliver {
                            dst: Dst::Any,
                            dup: true,
                        });
                    }
                }
                None => {
                    let r = self.fx.temp(ValType::Dyn);
                    ts.push(Task::Emit(Inst::LoadNil { dst: r }));
                    ts.push(Task::Push(Val {
                        reg: r,
                        rel: Rel::Temp,
                    }));
                }
            }
            ts.push(Task::Step(Step::SetGlobalCell(g)));
        }
        for k in &d.consts {
            let Some(&g) = self.cx.member_globals.get(&(c, k.item)) else {
                continue;
            };
            let value = match hir.item(k.item).kind {
                ItemKind::Const { value, .. } => value,
                _ => None,
            };
            let Some(e) = value else { continue };
            if matches!(hir.expr(e), Expr::Lit(_)) {
                continue;
            }
            let dup = self.needs_dup(e);
            ts.push(Task::At(NodeRef::Item(k.item)));
            ts.push(Task::Expr(e, Dst::Any));
            if dup {
                ts.push(Task::Deliver {
                    dst: Dst::Any,
                    dup: true,
                });
            }
            ts.push(Task::Step(Step::SetGlobal(g)));
        }
        ts.push(Task::SetScope(None));
    }
}
