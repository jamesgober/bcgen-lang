//! Classes end to end (HIR v3 → LSB format 2 → bvm-lang 2.0.0-alpha.4):
//! programs are built the way a lowering emits them (names unresolved),
//! resolved by resolve-lang 0.4 under its PHP policy, compiled with the Mox
//! intrinsic table, and run; each asserts what PHP prints or raises.

mod common;

use std::sync::{Arc, Mutex};

use bcgen_lang::{BodyMode, Compiled, Compiler, Intrinsics, Options};
use bvm_lang::{HostError, Memory, Program, Vm, VmError};
use bytecode_lang::ErrorKind;
use common::hb::H;
use common::{RV, to_rv};
use hir_lang::{
    BinderId, Effects, ExprId, Hir, MixinAction, MixinRule, ParamKind, PathRoot, StmtId, Vis,
};
use intern_lang::Interner;
use resolve_lang::{DefKind, Export, MapEnv, Namespace, Policy, Resolver};

// ------------------------------------------------------------------ harness

/// How a run ended.
#[derive(Debug, PartialEq)]
enum Ex {
    Val(RV),
    /// A runtime error: its code and payload (a message for class errors).
    Raised(u32, RV),
    /// A thrown value.
    Thrown(RV),
}

fn opts() -> Options {
    Options::new()
        .with_body(BodyMode::Entry)
        .with_intrinsics(Intrinsics::mox())
}

/// Resolves a unit built with unresolved names under resolve-lang's PHP
/// policy (`echo` is a host function); panics on a resolution diagnostic.
fn resolve(hir: Hir, names: &Interner) -> Hir {
    let echo = names.get("echo").map(|s| {
        (
            hir_lang::Name::new(s),
            Export::new(hir_lang::Res::Extern(s), DefKind::Extern),
        )
    });
    let mut env = MapEnv::new();
    if let Some((n, e)) = echo {
        env = env.with_prelude(n, Namespace::Value, e);
    }
    let unit = hir.unit();
    let res = Resolver::new(Policy::php())
        .with_env(&env)
        .resolve(hir, names)
        .unwrap_or_else(|e| panic!("resolve: {e}"));
    if !res.is_clean() {
        let msgs: Vec<String> = res.diagnostics().iter().map(|d| d.message(names)).collect();
        panic!("resolution diagnostics: {msgs:?}");
    }
    res.hir(unit).cloned().unwrap_or_else(|| panic!("unit"))
}

fn compile(hir: &Hir, names: &Interner, o: Options) -> Compiled {
    Compiler::new(o)
        .compile(hir, names)
        .unwrap_or_else(|e| panic!("compile error: {e}"))
}

/// The host: `echo`, and stand-ins for the Mox host functions the class
/// operations fall back to (they record that they were called).
fn host(printed: Arc<Mutex<Vec<String>>>) -> bvm_lang::Host {
    let mut h = common::host(printed.clone());
    for name in ["new", "instanceof", "clone", "str_offset", "cast_object"] {
        let p = printed.clone();
        let _ = h.register("mox", name, move |_, _| {
            if let Ok(mut v) = p.lock() {
                v.push(format!("<host mox.{name}>"));
            }
            Err(HostError::Raise(ErrorKind::TypeError))
        });
    }
    h
}

fn exec_with(out: &Compiled, memory: Memory) -> (Ex, Vec<String>) {
    let printed = Arc::new(Mutex::new(Vec::new()));
    let program = Program::load(out.module().clone(), &host(printed.clone())).unwrap_or_else(|e| {
        panic!(
            "load error: {e}\n{}",
            bytecode_lang::disassemble(out.module())
        )
    });
    let mut vm = Vm::with_memory(&program, memory);
    if let Some(d) = out.destructor() {
        vm.set_destructor(d)
            .unwrap_or_else(|e| panic!("destructor: {e:?}"));
    }
    let r = vm.run(out.entry(), &[]);
    let ex = match r {
        Ok(v) => Ex::Val(to_rv(&vm, v, 0)),
        Err(VmError::Raised { kind, payload, .. }) => {
            Ex::Raised(kind.code(), to_rv(&vm, payload, 0))
        }
        Err(VmError::Thrown { value, .. }) => Ex::Thrown(to_rv(&vm, value, 0)),
        Err(e) => panic!("unexpected VM error: {e:?}"),
    };
    let printed = printed.lock().map(|v| v.clone()).unwrap_or_default();
    (ex, printed)
}

/// Resolves, compiles (Mox table, entry body), and runs under tracing.
fn run(h: H, items: &[hir_lang::ItemId], body: Option<ExprId>) -> (Ex, Vec<String>) {
    run_opts(h, items, body, opts(), Memory::Tracing)
}

fn run_opts(
    h: H,
    items: &[hir_lang::ItemId],
    body: Option<ExprId>,
    o: Options,
    memory: Memory,
) -> (Ex, Vec<String>) {
    let (hir, names) = h.finish(items, body);
    let hir = resolve(hir, &names);
    let out = compile(&hir, &names, o);
    exec_with(&out, memory)
}

fn s(v: &str) -> RV {
    RV::Str(v.as_bytes().to_vec())
}

fn lines(v: &[&str]) -> Vec<String> {
    v.iter().map(|x| (*x).to_string()).collect()
}

// --------------------------------------------------------- program helpers

/// `echo(args..)` as a statement.
fn echo(h: &mut H, args: &[ExprId]) -> StmtId {
    let e = h.uname("echo");
    let c = h.call(e, args);
    h.stmt(c)
}

/// `let name = init;`.
fn let_(h: &mut H, name: &str, init: ExprId) -> (StmtId, BinderId) {
    let b = h.local(name);
    (h.let_(b, Some(init)), b)
}

/// `$this`, by name.
fn this(h: &mut H) -> ExprId {
    h.uname("this")
}

/// `$this->name`.
fn this_prop(h: &mut H, name: &str) -> ExprId {
    let t = this(h);
    h.field(t, name)
}

/// `$this->name = v` as a statement.
fn set_this(h: &mut H, name: &str, v: ExprId) -> StmtId {
    let p = this_prop(h, name);
    let a = h.assign(p, v);
    h.stmt(a)
}

fn add(h: &mut H, a: ExprId, b: ExprId) -> ExprId {
    h.op(hir_lang::OpKind::Add, &[a, b])
}

fn concat(h: &mut H, a: ExprId, b: ExprId) -> ExprId {
    h.intrinsic("concat", &[a, b])
}

/// An instance method `name($params..) { body }` (`$this` first).
fn method(h: &mut H, name: &str, vis: Vis, params: &[&str], body: ExprId) -> hir_lang::ItemId {
    let mut ps = vec![h.this_param().0];
    for p in params {
        ps.push(h.param(p, ParamKind::Normal, None, false).0);
    }
    h.method_item(name, vis, &ps, body)
}

/// A static method.
fn static_method(
    h: &mut H,
    name: &str,
    vis: Vis,
    params: &[&str],
    body: ExprId,
) -> hir_lang::ItemId {
    let ps: Vec<_> = params
        .iter()
        .map(|p| h.param(p, ParamKind::Normal, None, false).0)
        .collect();
    h.method_item(name, vis, &ps, body)
}

/// `return e`, as a block body.
fn returns(h: &mut H, e: ExprId) -> ExprId {
    let r = h.ret(Some(e));
    h.block(&[], Some(r))
}

/// `$o->m(args)`.
fn call_m(h: &mut H, o: ExprId, m: &str, args: &[ExprId]) -> ExprId {
    h.method(o, m, args)
}

// ------------------------------------------------------------------ tests

#[test]
fn properties_methods_statics_and_constants() {
    // class Counter {
    //   private $count = 0;
    //   public static $instances = 0;
    //   const STEP = 2;
    //   public function __construct($start) { $this->count = $start; self::$instances = self::$instances + 1; }
    //   public function inc() { $this->count = $this->count + self::STEP; return $this; }
    //   public function get() { return $this->count; }
    // }
    // $c = new Counter(10); $c->inc()->inc(); new Counter(0);
    // echo($c->get(), " ", Counter::$instances);
    let mut h = H::new();
    let zero = h.int(0);
    let count = h.prop("count", Vis::Private, Some(zero));
    let zero = h.int(0);
    let instances = h.static_prop("instances", Vis::Public, Some(zero));
    let two = h.int(2);
    let step = h.class_const("STEP", Vis::Public, Some(two));
    let start = h.uname("start");
    let s1 = set_this(&mut h, "count", start);
    let si = h.spath(PathRoot::SelfType, &["instances"]);
    let si2 = h.spath(PathRoot::SelfType, &["instances"]);
    let one = h.int(1);
    let inc1 = add(&mut h, si2, one);
    let a = h.assign(si, inc1);
    let s2 = h.stmt(a);
    let body = h.block(&[s1, s2], None);
    let ctor = method(&mut h, "__construct", Vis::Public, &["start"], body);
    let cur = this_prop(&mut h, "count");
    let st = h.spath(PathRoot::SelfType, &["STEP"]);
    let sum = add(&mut h, cur, st);
    let s1 = set_this(&mut h, "count", sum);
    let t = this(&mut h);
    let r = h.ret(Some(t));
    let body = h.block(&[s1], Some(r));
    let inc = method(&mut h, "inc", Vis::Public, &[], body);
    let cur = this_prop(&mut h, "count");
    let body = returns(&mut h, cur);
    let get = method(&mut h, "get", Vis::Public, &[], body);
    let class = h.class(
        "Counter",
        None,
        &[count],
        &[instances, step, ctor, inc, get],
    );

    let cls = h.item_ref("Counter", class);
    let ten = h.int(10);
    let n = h.new_obj(cls, &[ten]);
    let (l1, _) = let_(&mut h, "c", n);
    let c = h.uname("c");
    let i1 = call_m(&mut h, c, "inc", &[]);
    let i2 = call_m(&mut h, i1, "inc", &[]);
    let st2 = h.stmt(i2);
    let cls = h.item_ref("Counter", class);
    let z = h.int(0);
    let n2 = h.new_obj(cls, &[z]);
    let st3 = h.stmt(n2);
    let c = h.uname("c");
    let g = call_m(&mut h, c, "get", &[]);
    let sp = h.str(" ");
    let inst = h.spath(PathRoot::Relative, &["Counter", "instances"]);
    let e = echo(&mut h, &[g, sp, inst]);
    let body = h.block(&[l1, st2, st3, e], None);
    let (ex, out) = run(h, &[class], Some(body));
    assert_eq!(ex, Ex::Val(RV::Nil), "{out:?}");
    assert_eq!(out, lines(&["14 2"]));
}

/// `if (a == b) then`: a statement.
fn if_eq(h: &mut H, a: ExprId, b: ExprId, then: ExprId) -> StmtId {
    let c = h.op(hir_lang::OpKind::Eq, &[a, b]);
    let i = h.if_(c, then, None);
    h.stmt(i)
}

/// `catch (T $name) body` for a class or interface `T` by name.
fn catch_class(h: &mut H, class: &str, name: &str, body: ExprId) -> (hir_lang::Arm, BinderId) {
    let ty = h.ty_name(class);
    let b = h.local(name);
    let bind = h.pbind(b);
    let pat = h.pat(hir_lang::Pat::TypeTest {
        ty,
        pat: Some(bind),
    });
    (h.arm(pat, None, body), b)
}

/// `catch (Throwable $name) body`, Mox's `Throwable` being `any`.
fn catch_any(h: &mut H, name: &str, body: ExprId) -> hir_lang::Arm {
    let ty = h.ty(hir_lang::Ty::Any);
    let b = h.local(name);
    let bind = h.pbind(b);
    let pat = h.pat(hir_lang::Pat::TypeTest {
        ty,
        pat: Some(bind),
    });
    h.arm(pat, None, body)
}

/// `echo(args)` as a block (a catch arm's body).
fn echo_block(h: &mut H, args: &[ExprId]) -> ExprId {
    let e = echo(h, args);
    h.block(&[e], None)
}

#[test]
fn inheritance_overriding_and_parent_calls() {
    // class Animal { protected $name;
    //   function __construct($name) { $this->name = $name; }
    //   function speak() { return $this->name . " makes a sound"; }
    //   function intro() { return "I am " . $this->name . ": " . $this->speak(); } }
    // class Dog extends Animal { function speak() { return $this->name . " barks"; } }
    // class Puppy extends Dog {
    //   function __construct($name) { parent::__construct($name . " jr"); }
    //   function speak() { return parent::speak() . " softly"; } }
    let mut h = H::new();
    let name = h.prop("name", Vis::Protected, None);
    let n = h.uname("name");
    let st = set_this(&mut h, "name", n);
    let body = h.block(&[st], None);
    let ctor = method(&mut h, "__construct", Vis::Public, &["name"], body);
    let nm = this_prop(&mut h, "name");
    let tail = h.str(" makes a sound");
    let r = concat(&mut h, nm, tail);
    let body = returns(&mut h, r);
    let speak = method(&mut h, "speak", Vis::Public, &[], body);
    let pre = h.str("I am ");
    let nm = this_prop(&mut h, "name");
    let r = concat(&mut h, pre, nm);
    let colon = h.str(": ");
    let r = concat(&mut h, r, colon);
    let t = this(&mut h);
    let sp = call_m(&mut h, t, "speak", &[]);
    let r = concat(&mut h, r, sp);
    let body = returns(&mut h, r);
    let intro = method(&mut h, "intro", Vis::Public, &[], body);
    let animal = h.class("Animal", None, &[name], &[ctor, speak, intro]);

    let nm = this_prop(&mut h, "name");
    let tail = h.str(" barks");
    let r = concat(&mut h, nm, tail);
    let body = returns(&mut h, r);
    let speak = method(&mut h, "speak", Vis::Public, &[], body);
    let dog = h.class("Dog", Some("Animal"), &[], &[speak]);

    let pc = h.spath(PathRoot::ParentType, &["__construct"]);
    let n = h.uname("name");
    let jr = h.str(" jr");
    let arg = concat(&mut h, n, jr);
    let call = h.call(pc, &[arg]);
    let st = h.stmt(call);
    let body = h.block(&[st], None);
    let ctor = method(&mut h, "__construct", Vis::Public, &["name"], body);
    let ps = h.spath(PathRoot::ParentType, &["speak"]);
    let call = h.call(ps, &[]);
    let soft = h.str(" softly");
    let r = concat(&mut h, call, soft);
    let body = returns(&mut h, r);
    let speak = method(&mut h, "speak", Vis::Public, &[], body);
    let puppy = h.class("Puppy", Some("Dog"), &[], &[ctor, speak]);

    let mut stmts = Vec::new();
    for (class, arg) in [(animal, "cat"), (dog, "rex"), (puppy, "rex")] {
        let cname = ["Animal", "Dog", "Puppy"][stmts.len()];
        let c = h.item_ref(cname, class);
        let a = h.str(arg);
        let o = h.new_obj(c, &[a]);
        let i = call_m(&mut h, o, "intro", &[]);
        stmts.push(echo(&mut h, &[i]));
    }
    let body = h.block(&stmts, None);
    let (ex, out) = run(h, &[animal, dog, puppy], Some(body));
    assert_eq!(ex, Ex::Val(RV::Nil), "{out:?}");
    assert_eq!(
        out,
        lines(&[
            "I am cat: cat makes a sound",
            "I am rex: rex barks",
            "I am rex jr: rex jr barks softly",
        ])
    );
}

#[test]
fn late_static_binding_through_static_and_new_static() {
    // class Model { const KIND = "model";
    //   static function create() { return new static(); }
    //   static function kind() { return static::KIND; }
    //   function describe() { return static::kind() . "/" . self::KIND; } }
    // class User extends Model { const KIND = "user"; }
    // echo(User::kind(), " ", Model::kind(), " ", User::create()->describe(),
    //      " ", User::create() instanceof User, Model::create() instanceof User);
    let mut h = H::new();
    let v = h.str("model");
    let kind = h.class_const("KIND", Vis::Public, Some(v));
    // `new static()`, written `new (static::class)()`.
    let st = h.spath(PathRoot::StaticType, &["class"]);
    let n = h.new_obj(st, &[]);
    let body = returns(&mut h, n);
    let create = static_method(&mut h, "create", Vis::Public, &[], body);
    let sk = h.spath(PathRoot::StaticType, &["KIND"]);
    let body = returns(&mut h, sk);
    let kindf = static_method(&mut h, "kind", Vis::Public, &[], body);
    let sk = h.spath(PathRoot::StaticType, &["kind"]);
    let call = h.call(sk, &[]);
    let slash = h.str("/");
    let r = concat(&mut h, call, slash);
    let selfk = h.spath(PathRoot::SelfType, &["KIND"]);
    let r = concat(&mut h, r, selfk);
    let body = returns(&mut h, r);
    let describe = method(&mut h, "describe", Vis::Public, &[], body);
    let model = h.class("Model", None, &[], &[kind, create, kindf, describe]);
    let v = h.str("user");
    let kind = h.class_const("KIND", Vis::Public, Some(v));
    let user = h.class("User", Some("Model"), &[], &[kind]);

    let uk = h.spath(PathRoot::Relative, &["User", "kind"]);
    let a = h.call(uk, &[]);
    let sp = h.str(" ");
    let mk = h.spath(PathRoot::Relative, &["Model", "kind"]);
    let b = h.call(mk, &[]);
    let sp2 = h.str(" ");
    let uc = h.spath(PathRoot::Relative, &["User", "create"]);
    let o = h.call(uc, &[]);
    let d = call_m(&mut h, o, "describe", &[]);
    let sp3 = h.str(" ");
    let uc = h.spath(PathRoot::Relative, &["User", "create"]);
    let o = h.call(uc, &[]);
    let ur = h.item_ref("User", user);
    let t1 = h.instanceof(o, ur);
    let mc = h.spath(PathRoot::Relative, &["Model", "create"]);
    let o = h.call(mc, &[]);
    let ur = h.item_ref("User", user);
    let t2 = h.instanceof(o, ur);
    let e = echo(&mut h, &[a, sp, b, sp2, d, sp3, t1, t2]);
    let body = h.block(&[e], None);
    let (ex, out) = run(h, &[model, user], Some(body));
    assert_eq!(ex, Ex::Val(RV::Nil), "{out:?}");
    assert_eq!(out, lines(&["user model user/model 1"]));
}

#[test]
fn interfaces_are_type_tests_and_carry_constants() {
    // interface Named { function name(); }
    // interface Shape extends Named { const UNITS = "cm"; function area(); }
    // class Sq implements Shape { private $s;
    //   function __construct($s) { $this->s = $s; }
    //   function area() { return $this->s * $this->s; }
    //   function name() { return "square " . static::UNITS; } }
    // class Big extends Sq {}
    // $b = new Big(3);
    // echo($b->area(), " ", $b instanceof Shape, $b instanceof Named, $b instanceof Sq,
    //      " ", Sq::UNITS, " ", new Sq(1) instanceof Big, " ", $b->name(), " ", 5 instanceof Named);
    let mut h = H::new();
    let n = h.method_def("name", Vis::Public, &[], None, Effects::THROWS);
    let named = h.interface("Named", &[], &[n]);
    let cm = h.str("cm");
    let units = h.class_const("UNITS", Vis::Public, Some(cm));
    let a = h.method_def("area", Vis::Public, &[], None, Effects::THROWS);
    let shape = h.interface("Shape", &["Named"], &[units, a]);
    let sf = h.prop("s", Vis::Private, None);
    let sv = h.uname("s");
    let st = set_this(&mut h, "s", sv);
    let body = h.block(&[st], None);
    let ctor = method(&mut h, "__construct", Vis::Public, &["s"], body);
    let x = this_prop(&mut h, "s");
    let y = this_prop(&mut h, "s");
    let m = h.op(hir_lang::OpKind::Mul, &[x, y]);
    let body = returns(&mut h, m);
    let area = method(&mut h, "area", Vis::Public, &[], body);
    let sq_s = h.str("square ");
    let su = h.spath(PathRoot::StaticType, &["UNITS"]);
    let r = concat(&mut h, sq_s, su);
    let body = returns(&mut h, r);
    let namef = method(&mut h, "name", Vis::Public, &[], body);
    let sq = h.class_full(
        "Sq",
        None,
        &["Shape"],
        &[sf],
        &[ctor, area, namef],
        false,
        false,
    );
    let big = h.class("Big", Some("Sq"), &[], &[]);

    let bc = h.item_ref("Big", big);
    let three = h.int(3);
    let o = h.new_obj(bc, &[three]);
    let (l, _) = let_(&mut h, "b", o);
    let b = h.uname("b");
    let ar = call_m(&mut h, b, "area", &[]);
    let sp = h.str(" ");
    // An interface is named in an expression by a type argument.
    let b = h.uname("b");
    let sr = h.ty_name("Shape");
    let t1 = h.intrinsic_ty("mox.instanceof", sr, &[b]);
    let b = h.uname("b");
    let nr = h.ty_name("Named");
    let t2 = h.intrinsic_ty("mox.instanceof", nr, &[b]);
    let b = h.uname("b");
    let qr = h.item_ref("Sq", sq);
    let t3 = h.instanceof(b, qr);
    let sp2 = h.str(" ");
    let u = h.spath(PathRoot::Relative, &["Sq", "UNITS"]);
    let sp3 = h.str(" ");
    let qc = h.item_ref("Sq", sq);
    let one = h.int(1);
    let o1 = h.new_obj(qc, &[one]);
    let br = h.item_ref("Big", big);
    let t4 = h.instanceof(o1, br);
    let sp4 = h.str(" ");
    let b = h.uname("b");
    let nm = call_m(&mut h, b, "name", &[]);
    let sp5 = h.str(" ");
    let five = h.int(5);
    let nr = h.ty_name("Named");
    let t5 = h.intrinsic_ty("mox.instanceof", nr, &[five]);
    let e = echo(
        &mut h,
        &[ar, sp, t1, t2, t3, sp2, u, sp3, t4, sp4, nm, sp5, t5],
    );
    let body = h.block(&[l, e], None);
    let (ex, out) = run(h, &[named, shape, sq, big], Some(body));
    assert_eq!(ex, Ex::Val(RV::Nil), "{out:?}");
    assert_eq!(out, lines(&["9 111 cm  square cm "]));
}

#[test]
fn mixins_flatten_with_insteadof_and_aliases() {
    // trait Greets { public $greeting = "Hello"; public static $uses = 0;
    //   function greet() { self::$uses = self::$uses + 1; return $this->greeting . " from " . self::who(); } }
    // trait Waves { function greet() { return "wave"; } function wave() { return "~"; } }
    // class A { use Greets, Waves { Greets::greet insteadof Waves; Waves::greet as waveGreet; wave as protected; }
    //   static function who() { return "A"; } }
    // class B { use Greets; static function who() { return "B"; } }
    // $a = new A; $b = new B;
    // echo($a->greet(), "|", $a->waveGreet(), "|", $b->greet(), "|", $b->greet(), "|", A::$uses, B::$uses);
    // $a->wave();   // Error: protected
    let mut h = H::new();
    let hello = h.str("Hello");
    let greeting = h.prop("greeting", Vis::Public, Some(hello));
    let zero = h.int(0);
    let uses = h.static_prop("uses", Vis::Public, Some(zero));
    let su = h.spath(PathRoot::SelfType, &["uses"]);
    let su2 = h.spath(PathRoot::SelfType, &["uses"]);
    let one = h.int(1);
    let inc = add(&mut h, su2, one);
    let a = h.assign(su, inc);
    let s1 = h.stmt(a);
    let g = this_prop(&mut h, "greeting");
    let from = h.str(" from ");
    let r = concat(&mut h, g, from);
    let who = h.spath(PathRoot::SelfType, &["who"]);
    let w = h.call(who, &[]);
    let r = concat(&mut h, r, w);
    let ret = h.ret(Some(r));
    let body = h.block(&[s1], Some(ret));
    let greet = method(&mut h, "greet", Vis::Public, &[], body);
    let greets = h.class_full(
        "Greets",
        None,
        &[],
        &[greeting],
        &[uses, greet],
        false,
        true,
    );
    let wv = h.str("wave");
    let body = returns(&mut h, wv);
    let greet2 = method(&mut h, "greet", Vis::Public, &[], body);
    let tilde = h.str("~");
    let body = returns(&mut h, tilde);
    let wave = method(&mut h, "wave", Vis::Public, &[], body);
    let waves = h.class_full("Waves", None, &[], &[], &[greet2, wave], false, true);

    let g_ty = h.ty_name("Greets");
    let w_ty = h.ty_name("Waves");
    let w_ty2 = h.ty_name("Waves");
    let others = h.b.list(&[w_ty]);
    let r1 = MixinRule {
        method: h.ident("greet"),
        from: Some(g_ty),
        action: MixinAction::Insteadof(others),
    };
    let r2 = MixinRule {
        method: h.ident("greet"),
        from: Some(w_ty2),
        action: MixinAction::Alias {
            name: Some(h.ident("waveGreet")),
            vis: None,
        },
    };
    let r3 = MixinRule {
        method: h.ident("wave"),
        from: None,
        action: MixinAction::Alias {
            name: None,
            vis: Some(Vis::Protected),
        },
    };
    let use_a = h.mixin_use(&["Greets", "Waves"], &[r1, r2, r3]);
    let av = h.str("A");
    let body = returns(&mut h, av);
    let who_a = static_method(&mut h, "who", Vis::Public, &[], body);
    let a_class = h.class("A", None, &[], &[use_a, who_a]);
    let use_b = h.mixin_use(&["Greets"], &[]);
    let bv = h.str("B");
    let body = returns(&mut h, bv);
    let who_b = static_method(&mut h, "who", Vis::Public, &[], body);
    let b_class = h.class("B", None, &[], &[use_b, who_b]);

    let ar = h.item_ref("A", a_class);
    let na = h.new_obj(ar, &[]);
    let (l1, _) = let_(&mut h, "a", na);
    let br = h.item_ref("B", b_class);
    let nb = h.new_obj(br, &[]);
    let (l2, _) = let_(&mut h, "b", nb);
    let mut parts = Vec::new();
    for (var, m) in [
        ("a", "greet"),
        ("a", "waveGreet"),
        ("b", "greet"),
        ("b", "greet"),
    ] {
        let v = h.uname(var);
        parts.push(call_m(&mut h, v, m, &[]));
        parts.push(h.str("|"));
    }
    parts.push(h.spath(PathRoot::Relative, &["A", "uses"]));
    parts.push(h.spath(PathRoot::Relative, &["B", "uses"]));
    let e = echo(&mut h, &parts);
    let a = h.uname("a");
    let w = call_m(&mut h, a, "wave", &[]);
    let s3 = h.stmt(w);
    let body = h.block(&[l1, l2, e, s3], None);
    let (ex, out) = run(h, &[greets, waves, a_class, b_class], Some(body));
    assert_eq!(
        out,
        lines(&["Hello from A|wave|Hello from B|Hello from B|12"]),
        "{ex:?}"
    );
    assert_eq!(
        ex,
        Ex::Raised(
            100,
            s("Call to protected method A::wave() from global scope")
        )
    );
}

#[test]
fn visibility_private_slots_are_per_class_and_violations_raise() {
    // class P { private $secret = "p"; protected $prot = "pp";
    //   function peek($o) { return $o->secret; }
    //   private function hidden() { return "P-hidden"; }
    //   function callHidden() { return $this->hidden(); } }
    // class C extends P { public $secret = "c";
    //   public function hidden() { return "C-hidden"; }
    //   function prot() { return $this->prot; } }
    // $c = new C;
    // echo($c->secret, "|", $c->peek($c), "|", $c->callHidden(), "|", $c->prot(), "|", $c->hidden());
    // then each of: (new P)->secret, $c->prot, (new P)->hidden()
    let build = |h: &mut H| {
        let pv = h.str("p");
        let secret = h.prop("secret", Vis::Private, Some(pv));
        let ppv = h.str("pp");
        let prot = h.prop("prot", Vis::Protected, Some(ppv));
        let o = h.uname("o");
        let f = h.field(o, "secret");
        let body = returns(h, f);
        let peek = method(h, "peek", Vis::Public, &["o"], body);
        let hv = h.str("P-hidden");
        let body = returns(h, hv);
        let hidden = method(h, "hidden", Vis::Private, &[], body);
        let t = this(h);
        let c = call_m(h, t, "hidden", &[]);
        let body = returns(h, c);
        let call_hidden = method(h, "callHidden", Vis::Public, &[], body);
        let p = h.class("P", None, &[secret, prot], &[peek, hidden, call_hidden]);
        let cv = h.str("c");
        let secret = h.prop("secret", Vis::Public, Some(cv));
        let hv = h.str("C-hidden");
        let body = returns(h, hv);
        let hidden = method(h, "hidden", Vis::Public, &[], body);
        let pr = this_prop(h, "prot");
        let body = returns(h, pr);
        let protf = method(h, "prot", Vis::Public, &[], body);
        let c = h.class("C", Some("P"), &[secret], &[hidden, protf]);
        (p, c)
    };
    let mut h = H::new();
    let (p, c) = build(&mut h);
    let cr = h.item_ref("C", c);
    let o = h.new_obj(cr, &[]);
    let (l, _) = let_(&mut h, "c", o);
    let mut parts = Vec::new();
    let v = h.uname("c");
    parts.push(h.field(v, "secret"));
    for (m, arg) in [
        ("peek", true),
        ("callHidden", false),
        ("prot", false),
        ("hidden", false),
    ] {
        parts.push(h.str("|"));
        let v = h.uname("c");
        let args = if arg { vec![h.uname("c")] } else { vec![] };
        parts.push(call_m(&mut h, v, m, &args));
    }
    let e = echo(&mut h, &parts);
    let body = h.block(&[l, e], None);
    let (ex, out) = run(h, &[p, c], Some(body));
    assert_eq!(ex, Ex::Val(RV::Nil), "{out:?}");
    assert_eq!(out, lines(&["c|p|P-hidden|pp|C-hidden"]));

    for (case, msg) in [
        (0, "Cannot access private property P::$secret"),
        (1, "Cannot access protected property P::$prot"),
        (2, "Call to private method P::hidden() from global scope"),
    ] {
        let mut h = H::new();
        let (p, c) = build(&mut h);
        let e = match case {
            0 => {
                let pr = h.item_ref("P", p);
                let o = h.new_obj(pr, &[]);
                h.field(o, "secret")
            }
            1 => {
                let cr = h.item_ref("C", c);
                let o = h.new_obj(cr, &[]);
                h.field(o, "prot")
            }
            _ => {
                let pr = h.item_ref("P", p);
                let o = h.new_obj(pr, &[]);
                call_m(&mut h, o, "hidden", &[])
            }
        };
        let st = h.stmt(e);
        let body = h.block(&[st], None);
        let (ex, _) = run(h, &[p, c], Some(body));
        assert_eq!(ex, Ex::Raised(100, s(msg)), "case {case}");
    }
}

#[test]
fn exceptions_are_objects_caught_by_class_and_interface() {
    // class MyEx { public $msg; function __construct($m) { $this->msg = $m; } }
    // class SubEx extends MyEx {}
    // interface Tagged {}
    // class TagEx extends MyEx implements Tagged {}
    // function risky($k) { if ($k == 1) throw new SubEx("sub"); if ($k == 2) throw new TagEx("tag");
    //   if ($k == 3) throw new MyEx("my"); if ($k == 4) throw "plain"; return "ok"; }
    // for k in 0..=4: try { echo(risky(k)); } catch (SubEx $e) { echo("SubEx ", $e->msg); }
    //   catch (Tagged $e) { echo("Tagged ", $e->msg); } catch (MyEx $e) { echo("MyEx ", $e->msg); }
    //   catch (Throwable $e) { echo("any ", $e); }
    // throw new SubEx("out");   // uncaught
    let mut h = H::new();
    let msg = h.prop("msg", Vis::Public, None);
    let m = h.uname("m");
    let st = set_this(&mut h, "msg", m);
    let body = h.block(&[st], None);
    let ctor = method(&mut h, "__construct", Vis::Public, &["m"], body);
    let my = h.class("MyEx", None, &[msg], &[ctor]);
    let sub = h.class("SubEx", Some("MyEx"), &[], &[]);
    let tagged = h.interface("Tagged", &[], &[]);
    let tag = h.class_full("TagEx", Some("MyEx"), &["Tagged"], &[], &[], false, false);
    let (pk, _) = h.param("k", ParamKind::Normal, None, false);
    let mut stmts = Vec::new();
    for (k, class, item, text) in [
        (1, "SubEx", sub, "sub"),
        (2, "TagEx", tag, "tag"),
        (3, "MyEx", my, "my"),
    ] {
        let kv = h.uname("k");
        let n = h.int(k);
        let cr = h.item_ref(class, item);
        let t = h.str(text);
        let o = h.new_obj(cr, &[t]);
        let th = h.throw(o);
        stmts.push(if_eq(&mut h, kv, n, th));
    }
    let kv = h.uname("k");
    let four = h.int(4);
    let plain = h.str("plain");
    let th = h.throw(plain);
    stmts.push(if_eq(&mut h, kv, four, th));
    let ok = h.str("ok");
    let r = h.ret(Some(ok));
    let body = h.block(&stmts, Some(r));
    let risky = h.func("risky", &[pk], body, hir_lang::DefaultEval::PerCall);

    let mut stmts = Vec::new();
    for k in 0..=4 {
        let f = h.uname("risky");
        let kk = h.int(k);
        let c = h.call(f, &[kk]);
        let tb = echo_block(&mut h, &[c]);
        let mut arms = Vec::new();
        for class in ["SubEx", "Tagged", "MyEx"] {
            let label = h.str(&format!("{class} "));
            let ev = h.uname("e");
            let m = h.field(ev, "msg");
            let body = echo_block(&mut h, &[label, m]);
            arms.push(catch_class(&mut h, class, "e", body).0);
        }
        let label = h.str("any ");
        let ev = h.uname("e");
        let body = echo_block(&mut h, &[label, ev]);
        arms.push(catch_any(&mut h, "e", body));
        let t = h.try_(tb, &arms, None);
        stmts.push(h.stmt(t));
    }
    let sr = h.item_ref("SubEx", sub);
    let out = h.str("out");
    let o = h.new_obj(sr, &[out]);
    let th = h.throw(o);
    stmts.push(h.stmt(th));
    let body = h.block(&stmts, None);
    let (ex, out) = run(h, &[my, sub, tagged, tag, risky], Some(body));
    assert_eq!(
        out,
        lines(&["ok", "SubEx sub", "Tagged tag", "MyEx my", "any plain"])
    );
    // An object of kind 8 (`object`) escapes uncaught.
    assert_eq!(ex, Ex::Thrown(RV::Other(8)));
}

#[test]
fn abstract_classes_interfaces_and_traits_cannot_be_instantiated() {
    for (case, msg) in [
        (0, "Cannot instantiate abstract class Shape"),
        (1, "Cannot instantiate interface Named"),
        (2, "Cannot instantiate trait T"),
    ] {
        let mut h = H::new();
        let area = h.method_def("area", Vis::Public, &[], None, Effects::THROWS);
        let shape = h.class_full("Shape", None, &[], &[], &[area], true, false);
        let named = h.interface("Named", &[], &[]);
        let t = h.class_full("T", None, &[], &[], &[], false, true);
        let name = ["Shape", "Named", "T"][case];
        // The arguments are not evaluated: `fail()` would raise first.
        let f = h.uname("fail");
        let fc = h.call(f, &[]);
        let ty = h.ty_name(name);
        let n = h.intrinsic_ty("mox.new", ty, &[fc]);
        let st = h.stmt(n);
        let body = h.block(&[st], None);
        let (hir, names) = h.finish(&[shape, named, t], Some(body));
        let fail = names.get("fail").unwrap_or_else(|| panic!("fail"));
        let env = MapEnv::new().with_prelude(
            hir_lang::Name::new(fail),
            Namespace::Value,
            Export::new(hir_lang::Res::Extern(fail), DefKind::Extern),
        );
        let unit = hir.unit();
        let res = Resolver::new(Policy::php())
            .with_env(&env)
            .resolve(hir, &names)
            .unwrap_or_else(|e| panic!("{e}"));
        let hir = res.hir(unit).cloned().unwrap_or_else(|| panic!("unit"));
        let out = compile(&hir, &names, opts());
        let (ex, _) = exec_with(&out, Memory::Tracing);
        assert_eq!(ex, Ex::Raised(100, s(msg)), "case {case}");
    }
}

#[test]
fn clone_copies_and_calls_the_clone_method() {
    // class Box { public $items = [1]; public $copies = 0;
    //   function __clone() { $this->copies = $this->copies + 1; } }
    // $a = new Box; $b = clone $a; $b->items[] = 2;
    // echo(len($a->items), len($b->items), $a->copies, $b->copies);
    let mut h = H::new();
    let one = h.int(1);
    let arr = h.array(&[one]);
    let items = h.prop("items", Vis::Public, Some(arr));
    let zero = h.int(0);
    let copies = h.prop("copies", Vis::Public, Some(zero));
    let c = this_prop(&mut h, "copies");
    let one = h.int(1);
    let inc = add(&mut h, c, one);
    let st = set_this(&mut h, "copies", inc);
    let body = h.block(&[st], None);
    let cl = method(&mut h, "__clone", Vis::Public, &[], body);
    let bx = h.class("Box", None, &[items, copies], &[cl]);
    let br = h.item_ref("Box", bx);
    let n = h.new_obj(br, &[]);
    let (l1, _) = let_(&mut h, "a", n);
    let a = h.uname("a");
    let c = h.clone_of(a);
    let (l2, _) = let_(&mut h, "b", c);
    let b = h.uname("b");
    let it = h.field(b, "items");
    let ap = h.append(it);
    let two = h.int(2);
    let asg = h.assign(ap, two);
    let s3 = h.stmt(asg);
    let mut parts = Vec::new();
    for (v, f) in [("a", "items"), ("b", "items")] {
        let x = h.uname(v);
        let fx = h.field(x, f);
        parts.push(h.intrinsic("len", &[fx]));
    }
    for v in ["a", "b"] {
        let x = h.uname(v);
        parts.push(h.field(x, "copies"));
    }
    let e = echo(&mut h, &parts);
    let body = h.block(&[l1, l2, s3, e], None);
    let (ex, out) = run(h, &[bx], Some(body));
    assert_eq!(ex, Ex::Val(RV::Nil), "{out:?}");
    assert_eq!(out, lines(&["1201"]));
}

/// `class Res { public $n; function __construct($n) { $this->n = $n; }
/// function __destruct() { echo("drop ", $this->n); } }`.
fn res_class(h: &mut H) -> hir_lang::ItemId {
    let n = h.prop("n", Vis::Public, None);
    let v = h.uname("n");
    let st = set_this(h, "n", v);
    let body = h.block(&[st], None);
    let ctor = method(h, "__construct", Vis::Public, &["n"], body);
    let drop = h.str("drop ");
    let nv = this_prop(h, "n");
    let body = echo_block(h, &[drop, nv]);
    let dtor = method(h, "__destruct", Vis::Public, &[], body);
    h.class("Res", None, &[n], &[ctor, dtor])
}

#[test]
fn destructors_run_where_php_runs_them_under_reference_counting() {
    // $a = new Res(1); $a = null; echo("after"); $b = new Res(2); $b = new Res(3); echo("end");
    // PHP: drop 1, after, drop 2, end, drop 3 (at the end of the script).
    let mut h = H::new();
    let res = res_class(&mut h);
    let r = h.item_ref("Res", res);
    let one = h.int(1);
    let o = h.new_obj(r, &[one]);
    let (l1, _) = let_(&mut h, "a", o);
    let a = h.uname("a");
    let nil = h.nil();
    let asg = h.assign(a, nil);
    let s2 = h.stmt(asg);
    let after = h.str("after");
    let s3 = echo(&mut h, &[after]);
    let r = h.item_ref("Res", res);
    let two = h.int(2);
    let o = h.new_obj(r, &[two]);
    let (l4, _) = let_(&mut h, "b", o);
    let r = h.item_ref("Res", res);
    let three = h.int(3);
    let o = h.new_obj(r, &[three]);
    let b = h.uname("b");
    let asg = h.assign(b, o);
    let s5 = h.stmt(asg);
    let end = h.str("end");
    let s6 = echo(&mut h, &[end]);
    let body = h.block(&[l1, s2, s3, l4, s5, s6], None);
    let (hir, names) = h.finish(&[res], Some(body));
    let hir = resolve(hir, &names);
    let out = compile(&hir, &names, opts().with_reference_counting(true));
    assert_eq!(out.destructor(), Some("__destruct()"));
    let (ex, printed) = exec_with(&out, Memory::Rc);
    assert_eq!(ex, Ex::Val(RV::Nil));
    assert_eq!(
        printed,
        lines(&["drop 1", "after", "drop 2", "end", "drop 3"])
    );
}

#[test]
fn class_values_known_only_at_run_time() {
    // class Dog { public $n; function __construct($n) { $this->n = $n; }
    //   function speak() { return $this->n . " barks"; } }
    // $cls = "Dog"; $d = new $cls("rex");
    // echo($d->speak(), " ", $d instanceof $cls, " ", "x" instanceof $cls, " ", $d instanceof $d);
    // new $missing(1)  -> the host function `mox.new`
    let mut h = H::new();
    let nf = h.prop("n", Vis::Public, None);
    let v = h.uname("n");
    let st = set_this(&mut h, "n", v);
    let body = h.block(&[st], None);
    let ctor = method(&mut h, "__construct", Vis::Public, &["n"], body);
    let nv = this_prop(&mut h, "n");
    let b = h.str(" barks");
    let r = concat(&mut h, nv, b);
    let body = returns(&mut h, r);
    let speak = method(&mut h, "speak", Vis::Public, &[], body);
    let dog = h.class("Dog", None, &[nf], &[ctor, speak]);
    let name = h.str("Dog");
    let (l1, _) = let_(&mut h, "cls", name);
    let c = h.uname("cls");
    let rex = h.str("rex");
    let o = h.new_obj(c, &[rex]);
    let (l2, _) = let_(&mut h, "d", o);
    let d = h.uname("d");
    let sp = call_m(&mut h, d, "speak", &[]);
    let s1 = h.str(" ");
    let d = h.uname("d");
    let c = h.uname("cls");
    let t1 = h.instanceof(d, c);
    let s2 = h.str(" ");
    let x = h.str("x");
    let c = h.uname("cls");
    let t2 = h.instanceof(x, c);
    let s3 = h.str(" ");
    let d = h.uname("d");
    let d2 = h.uname("d");
    let t3 = h.instanceof(d, d2);
    let e = echo(&mut h, &[sp, s1, t1, s2, t2, s3, t3]);
    let nope = h.str("Nope");
    let (l3, _) = let_(&mut h, "missing", nope);
    let m = h.uname("missing");
    let one = h.int(1);
    let o = h.new_obj(m, &[one]);
    let s4 = h.stmt(o);
    let body = h.block(&[l1, l2, e, l3, s4], None);
    let (ex, out) = run(h, &[dog], Some(body));
    assert_eq!(out, lines(&["rex barks 1  1", "<host mox.new>"]));
    // The stand-in host function raises.
    assert_eq!(ex, Ex::Raised(100, RV::Nil));
}

#[test]
fn static_methods_through_instances_and_closures_over_this() {
    // class K { public $v = 5; public static $hits = 0; public static $log = [];
    //   static function bump() { static::$hits += 1; return static::$hits; }
    //   function adder() { return function ($x) use ($this) { return $this->v + $x; }; }
    //   function viaSelf() { return self::bump() + static::bump(); }
    //   function useStatic() { self::$log[] = "a"; return len(self::$log); } }
    // $k = new K;
    // echo($k->bump(), K::bump(), " ", ($k->adder())(10), " ", $k->viaSelf(), " ",
    //      $k->useStatic(), $k->useStatic());
    let mut h = H::new();
    let five = h.int(5);
    let vf = h.prop("v", Vis::Public, Some(five));
    let zero = h.int(0);
    let hits = h.static_prop("hits", Vis::Public, Some(zero));
    let empty = h.array(&[]);
    let log = h.static_prop("log", Vis::Public, Some(empty));
    let sh = h.spath(PathRoot::StaticType, &["hits"]);
    let one = h.int(1);
    let inc = h.compound(sh, hir_lang::Op::new(hir_lang::OpKind::Add), one);
    let s1 = h.stmt(inc);
    let sh = h.spath(PathRoot::StaticType, &["hits"]);
    let r = h.ret(Some(sh));
    let body = h.block(&[s1], Some(r));
    let bump = static_method(&mut h, "bump", Vis::Public, &[], body);
    let (tp, this_b) = h.this_param();
    let (cap, inner_this) = h.capture(this_b, "this", hir_lang::CaptureMode::ByValue);
    let (px, xb) = h.param("x", ParamKind::Normal, None, false);
    let it = h.var(inner_this);
    let v = h.field(it, "v");
    let xv = h.var(xb);
    let sum = add(&mut h, v, xv);
    let cbody = returns(&mut h, sum);
    let clo = h.closure(
        &[px],
        cbody,
        None,
        &[cap],
        None,
        hir_lang::DefaultEval::PerCall,
    );
    let body = returns(&mut h, clo);
    let adder = h.method_item("adder", Vis::Public, &[tp], body);
    let sb = h.spath(PathRoot::SelfType, &["bump"]);
    let c1 = h.call(sb, &[]);
    let stb = h.spath(PathRoot::StaticType, &["bump"]);
    let c2 = h.call(stb, &[]);
    let sum = add(&mut h, c1, c2);
    let body = returns(&mut h, sum);
    let via = method(&mut h, "viaSelf", Vis::Public, &[], body);
    let sl = h.spath(PathRoot::SelfType, &["log"]);
    let ap = h.append(sl);
    let a = h.str("a");
    let asg = h.assign(ap, a);
    let s1 = h.stmt(asg);
    let sl = h.spath(PathRoot::SelfType, &["log"]);
    let n = h.intrinsic("len", &[sl]);
    let r = h.ret(Some(n));
    let body = h.block(&[s1], Some(r));
    let use_static = method(&mut h, "useStatic", Vis::Public, &[], body);
    let k = h.class("K", None, &[vf], &[hits, log, bump, adder, via, use_static]);

    let kr = h.item_ref("K", k);
    let o = h.new_obj(kr, &[]);
    let (l1, _) = let_(&mut h, "k", o);
    let kv = h.uname("k");
    let b1 = call_m(&mut h, kv, "bump", &[]);
    let kb = h.spath(PathRoot::Relative, &["K", "bump"]);
    let b2 = h.call(kb, &[]);
    let sp = h.str(" ");
    let kv = h.uname("k");
    let f = call_m(&mut h, kv, "adder", &[]);
    let ten = h.int(10);
    let r = h.call(f, &[ten]);
    let sp2 = h.str(" ");
    let kv = h.uname("k");
    let vs = call_m(&mut h, kv, "viaSelf", &[]);
    let sp3 = h.str(" ");
    let kv = h.uname("k");
    let u1 = call_m(&mut h, kv, "useStatic", &[]);
    let kv = h.uname("k");
    let u2 = call_m(&mut h, kv, "useStatic", &[]);
    let e = echo(&mut h, &[b1, b2, sp, r, sp2, vs, sp3, u1, u2]);
    let body = h.block(&[l1, e], None);
    let (ex, out) = run(h, &[k], Some(body));
    assert_eq!(ex, Ex::Val(RV::Nil), "{out:?}");
    // bump: 1, 2; adder: 15; viaSelf: 3 + 4; useStatic: 1, 2.
    assert_eq!(out, lines(&["12 15 7 12"]));
}

#[test]
fn private_constructors_and_instance_methods_called_statically() {
    // class Single { private static $it = null; private function __construct() {}
    //   static function get() { if (self::$it == null) self::$it = new self(); return self::$it; }
    //   function hello() { return "hi"; } }
    // echo(Single::get()->hello());
    // then: new Single -> Error; Single::hello() -> Error
    let build = |h: &mut H| {
        let nil = h.nil();
        let it = h.static_prop("it", Vis::Private, Some(nil));
        let body = h.block(&[], None);
        let ctor = method(h, "__construct", Vis::Private, &[], body);
        let si = h.spath(PathRoot::SelfType, &["it"]);
        let nil = h.nil();
        let si2 = h.spath(PathRoot::SelfType, &["it"]);
        let sc = h.spath(PathRoot::SelfType, &["class"]);
        let n = h.new_obj(sc, &[]);
        let asg = h.assign(si2, n);
        let s1 = if_eq(h, si, nil, asg);
        let si = h.spath(PathRoot::SelfType, &["it"]);
        let r = h.ret(Some(si));
        let body = h.block(&[s1], Some(r));
        let get = static_method(h, "get", Vis::Public, &[], body);
        let hi = h.str("hi");
        let body = returns(h, hi);
        let hello = method(h, "hello", Vis::Public, &[], body);
        h.class("Single", None, &[], &[it, ctor, get, hello])
    };
    let mut h = H::new();
    let single = build(&mut h);
    let g = h.spath(PathRoot::Relative, &["Single", "get"]);
    let o = h.call(g, &[]);
    let hello = call_m(&mut h, o, "hello", &[]);
    let e = echo(&mut h, &[hello]);
    let body = h.block(&[e], None);
    let (ex, out) = run(h, &[single], Some(body));
    assert_eq!(ex, Ex::Val(RV::Nil), "{out:?}");
    assert_eq!(out, lines(&["hi"]));
    for (case, msg) in [
        (
            0,
            "Call to private method Single::__construct() from global scope",
        ),
        (
            1,
            "Non-static method Single::hello() cannot be called statically",
        ),
    ] {
        let mut h = H::new();
        let single = build(&mut h);
        let e = if case == 0 {
            let r = h.item_ref("Single", single);
            h.new_obj(r, &[])
        } else {
            let p = h.spath(PathRoot::Relative, &["Single", "hello"]);
            h.call(p, &[])
        };
        let st = h.stmt(e);
        let body = h.block(&[st], None);
        let (ex, _) = run(h, &[single], Some(body));
        assert_eq!(ex, Ex::Raised(100, s(msg)), "case {case}");
    }
}

#[test]
fn generator_methods_and_methods_with_defaults_and_named_arguments() {
    // class G { public $n = 3;
    //   function count() { $i = 0; while ($i < $this->n) { yield $i; $i = $i + 1; } }
    //   function greet($who, $greeting = "Hello") { return $greeting . " " . $who; } }
    // $g = new G; $s = 0; foreach ($g->count() as $v) $s += $v;
    // echo($s, " ", $g->greet("Ann"), " ", $g->greet(greeting: "Hey", who: "Bo"));
    let mut h = H::new();
    let three = h.int(3);
    let nf = h.prop("n", Vis::Public, Some(three));
    let (tp, _) = h.this_param();
    let ib = h.local("i");
    let zero = h.int(0);
    let li = h.let_(ib, Some(zero));
    let iv = h.var(ib);
    let n = this_prop(&mut h, "n");
    let lt = h.op(hir_lang::OpKind::Lt, &[iv, n]);
    let br = h.brk(None, None);
    let empty = h.block(&[], None);
    let cond = h.if_(lt, empty, Some(br));
    let c1 = h.stmt(cond);
    let iv = h.var(ib);
    let y = h.yield_(None, Some(iv));
    let c2 = h.stmt(y);
    let iv = h.var(ib);
    let one = h.int(1);
    let inc = add(&mut h, iv, one);
    let iv = h.var(ib);
    let asg = h.assign(iv, inc);
    let c3 = h.stmt(asg);
    let lb = h.block(&[c1, c2, c3], None);
    let lp = h.loop_(None, lb, None);
    let ls = h.stmt(lp);
    let body = h.block(&[li, ls], None);
    let count = h.method_def(
        "count",
        Vis::Public,
        &[tp],
        Some(body),
        Effects::THROWS.union(Effects::YIELD),
    );
    let (tp, _) = h.this_param();
    let (pw, _) = h.param("who", ParamKind::Normal, None, false);
    let hello = h.str("Hello");
    let (pg, _) = h.param("greeting", ParamKind::Normal, Some(hello), false);
    let g = h.uname("greeting");
    let sp = h.str(" ");
    let r = concat(&mut h, g, sp);
    let w = h.uname("who");
    let r = concat(&mut h, r, w);
    let body = returns(&mut h, r);
    let greet = h.method_item("greet", Vis::Public, &[tp, pw, pg], body);
    let gc = h.class("G", None, &[nf], &[count, greet]);

    let r = h.item_ref("G", gc);
    let o = h.new_obj(r, &[]);
    let (l1, _) = let_(&mut h, "g", o);
    let z = h.int(0);
    let (l2, sb) = let_(&mut h, "s", z);
    let gv = h.uname("g");
    let generator = call_m(&mut h, gv, "count", &[]);
    let itb = h.local("it");
    let iter = h.intrinsic("iter", &[generator]);
    let lit = h.let_(itb, Some(iter));
    let itv = h.var(itb);
    let next = h.intrinsic("iter_next", &[itv]);
    let null = h.pat(hir_lang::Pat::Lit(hir_lang::Lit::Null));
    let brk = h.brk(None, None);
    let a1 = h.arm(null, None, brk);
    let kb = h.local("k");
    let vb = h.local("v");
    let pk = h.pbind(kb);
    let pv = h.pbind(vb);
    let elems = h.b.list(&[pk, pv]);
    let tup = h.pat(hir_lang::Pat::Tuple { elems, rest: None });
    let svar = h.var(sb);
    let vv = h.var(vb);
    let sum = add(&mut h, svar, vv);
    let svar = h.var(sb);
    let asg = h.assign(svar, sum);
    let a2 = h.arm(tup, None, asg);
    let m = h.match_(next, &[a1, a2]);
    let lp = h.loop_(None, m, None);
    let fe = h.block(&[lit], Some(lp));
    let l3 = h.stmt(fe);
    let sv = h.var(sb);
    let sp = h.str(" ");
    let gv = h.uname("g");
    let ann = h.str("Ann");
    let g1 = call_m(&mut h, gv, "greet", &[ann]);
    let sp2 = h.str(" ");
    let gv = h.uname("g");
    let hey = h.str("Hey");
    let bo = h.str("Bo");
    let a = h.named("greeting", hey);
    let b = h.named("who", bo);
    let method = h.ident("greet");
    let args = h.b.list(&[a, b]);
    let gm = h.expr(hir_lang::Expr::MethodCall {
        receiver: gv,
        method,
        generic_args: hir_lang::List::EMPTY,
        args,
    });
    let e = echo(&mut h, &[sv, sp, g1, sp2, gm]);
    let body = h.block(&[l1, l2, l3, e], None);
    let (ex, out) = run(h, &[gc], Some(body));
    assert_eq!(ex, Ex::Val(RV::Nil), "{out:?}");
    assert_eq!(out, lines(&["3 Hello Ann Hey Bo"]));
}

#[test]
fn members_by_run_time_name() {
    // class D { public $a = 1; private $b = 2;
    //   function get($n) { return $this->$n; }
    //   function put($n, $v) { $this->$n = $v; }
    //   function call($m) { return $this->$m(); }
    //   function hi() { return "hi"; } private function sec() { return "sec"; } }
    // $d = new D; $n = "a"; $m = "hi";
    // echo($d->$n, $d->get("b"), " ", $d->call("sec"), " ", $d->call("hi"), " ", $d->$m());
    // $d->put("a", 5); $d->$n = $d->$n + 1; echo($d->a);
    // then: $d->{"b"} (private, from outside) and $d->{"zz"} (undefined)
    let build = |h: &mut H| {
        let one = h.int(1);
        let a = h.prop("a", Vis::Public, Some(one));
        let two = h.int(2);
        let b = h.prop("b", Vis::Private, Some(two));
        let t = this(h);
        let n = h.uname("n");
        let r = h.expr(hir_lang::Expr::DynField { base: t, name: n });
        let body = returns(h, r);
        let get = method(h, "get", Vis::Public, &["n"], body);
        let t = this(h);
        let n = h.uname("n");
        let target = h.expr(hir_lang::Expr::DynField { base: t, name: n });
        let v = h.uname("v");
        let asg = h.assign(target, v);
        let st = h.stmt(asg);
        let body = h.block(&[st], None);
        let put = method(h, "put", Vis::Public, &["n", "v"], body);
        let t = this(h);
        let m = h.uname("m");
        let args = h.b.list(&[]);
        let c = h.expr(hir_lang::Expr::DynMethodCall {
            receiver: t,
            name: m,
            args,
        });
        let body = returns(h, c);
        let call = method(h, "call", Vis::Public, &["m"], body);
        let hi = h.str("hi");
        let body = returns(h, hi);
        let hif = method(h, "hi", Vis::Public, &[], body);
        let sv = h.str("sec");
        let body = returns(h, sv);
        let sec = method(h, "sec", Vis::Private, &[], body);
        h.class("D", None, &[a, b], &[get, put, call, hif, sec])
    };
    let mut h = H::new();
    let d = build(&mut h);
    let dr = h.item_ref("D", d);
    let o = h.new_obj(dr, &[]);
    let (l1, _) = let_(&mut h, "d", o);
    let a = h.str("a");
    let (l2, _) = let_(&mut h, "n", a);
    let hi = h.str("hi");
    let (l3, _) = let_(&mut h, "m", hi);
    let dv = h.uname("d");
    let nv = h.uname("n");
    let p1 = h.expr(hir_lang::Expr::DynField { base: dv, name: nv });
    let dv = h.uname("d");
    let b = h.str("b");
    let p2 = call_m(&mut h, dv, "get", &[b]);
    let sp = h.str(" ");
    let dv = h.uname("d");
    let sec = h.str("sec");
    let p3 = call_m(&mut h, dv, "call", &[sec]);
    let sp2 = h.str(" ");
    let dv = h.uname("d");
    let hi = h.str("hi");
    let p4 = call_m(&mut h, dv, "call", &[hi]);
    let sp3 = h.str(" ");
    let dv = h.uname("d");
    let mv = h.uname("m");
    let args = h.b.list(&[]);
    let p5 = h.expr(hir_lang::Expr::DynMethodCall {
        receiver: dv,
        name: mv,
        args,
    });
    let e1 = echo(&mut h, &[p1, p2, sp, p3, sp2, p4, sp3, p5]);
    let dv = h.uname("d");
    let a = h.str("a");
    let five = h.int(5);
    let put = call_m(&mut h, dv, "put", &[a, five]);
    let s2 = h.stmt(put);
    let dv = h.uname("d");
    let nv = h.uname("n");
    let target = h.expr(hir_lang::Expr::DynField { base: dv, name: nv });
    let dv = h.uname("d");
    let nv = h.uname("n");
    let cur = h.expr(hir_lang::Expr::DynField { base: dv, name: nv });
    let one = h.int(1);
    let inc = add(&mut h, cur, one);
    let asg = h.assign(target, inc);
    let s3 = h.stmt(asg);
    let dv = h.uname("d");
    let fa = h.field(dv, "a");
    let e2 = echo(&mut h, &[fa]);
    let body = h.block(&[l1, l2, l3, e1, s2, s3, e2], None);
    let (ex, out) = run(h, &[d], Some(body));
    assert_eq!(ex, Ex::Val(RV::Nil), "{out:?}");
    assert_eq!(out, lines(&["12 sec hi hi", "6"]));
    for (name, want) in [
        (
            "b",
            Ex::Raised(100, s("Cannot access private property D::$b")),
        ),
        ("zz", Ex::Raised(104, s("zz"))),
    ] {
        let mut h = H::new();
        let d = build(&mut h);
        let dr = h.item_ref("D", d);
        let o = h.new_obj(dr, &[]);
        let k = h.str(name);
        let e = h.expr(hir_lang::Expr::DynField { base: o, name: k });
        let st = h.stmt(e);
        let body = h.block(&[st], None);
        let (ex, _) = run(h, &[d], Some(body));
        assert_eq!(ex, want, "{name}");
    }
}
