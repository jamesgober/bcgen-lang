//! Dispatch and visibility against a model: random class hierarchies
//! (single inheritance, methods and properties of random visibility that
//! PHP accepts: a redeclaration never narrows an inherited member's
//! visibility), every method called and every property read through every
//! object from every scope, compared with a model transcribed from PHP 8's
//! `zend_std_get_method` and `zend_get_property_offset` (written over the
//! declarations directly, independently of the compiler's plans).
//!
//! Messages follow bcgen-lang's documented convention: a protected
//! property's message names the declaring class (PHP names the object's).

mod common;

use std::sync::{Arc, Mutex};

use bcgen_lang::{BodyMode, Compiler, Intrinsics, Options};
use bvm_lang::{Program, Vm};
use common::hb::H;
use hir_lang::{DefaultEval, ExprId, ParamKind, StmtId, Ty, Vis};
use proptest::prelude::*;
use resolve_lang::{DefKind, Export, MapEnv, Namespace, Policy, Resolver};

const NAMES: usize = 2;

/// A generated hierarchy: per class, its parent, and per member name its
/// own declaration's visibility (if it declares one).
#[derive(Clone, Debug)]
struct World {
    parent: Vec<Option<usize>>,
    methods: Vec<[Option<Vis>; NAMES]>,
    props: Vec<[Option<Vis>; NAMES]>,
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}

fn chain(w: &World, c: usize) -> Vec<usize> {
    let mut out = vec![c];
    let mut cur = w.parent[c];
    while let Some(p) = cur {
        out.push(p);
        cur = w.parent[p];
    }
    out
}

/// The visibility a redeclaration may have: never narrower than the
/// nearest inherited declaration, unless that one is private.
fn legal(rng: &mut Rng, inherited: Option<Vis>) -> Vis {
    let all = [Vis::Public, Vis::Protected, Vis::Private];
    match inherited {
        Some(Vis::Public) => Vis::Public,
        Some(Vis::Protected) => all[rng.below(2) as usize],
        _ => all[rng.below(3) as usize],
    }
}

fn world(seed: u64) -> World {
    let mut rng = Rng(seed | 1);
    // Up to 12 classes: a name declared by more than 4 of them takes the
    // compiler's lineage plans and shared `<vis>` checks, fewer the
    // inline ones; both are compared with the model.
    let n = 1 + rng.below(12) as usize;
    let mut w = World {
        parent: Vec::new(),
        methods: Vec::new(),
        props: Vec::new(),
    };
    for c in 0..n {
        let parent = if c > 0 && rng.below(4) != 0 {
            Some(rng.below(c as u64) as usize)
        } else {
            None
        };
        w.parent.push(parent);
        let mut ms = [None; NAMES];
        let mut ps = [None; NAMES];
        for k in 0..NAMES {
            let up = |table: &Vec<[Option<Vis>; NAMES]>| {
                let mut cur = parent;
                while let Some(p) = cur {
                    if let Some(v) = table[p][k] {
                        return Some(v);
                    }
                    cur = w.parent[p];
                }
                None
            };
            if rng.below(2) == 0 {
                ms[k] = Some(legal(&mut rng, up(&w.methods)));
            }
            if rng.below(2) == 0 {
                ps[k] = Some(legal(&mut rng, up(&w.props)));
            }
        }
        w.methods.push(ms);
        w.props.push(ps);
    }
    w
}

// ------------------------------------------------------------------ model

fn related(w: &World, a: Option<usize>, b: usize) -> bool {
    a.is_some_and(|a| chain(w, a).contains(&b) || chain(w, b).contains(&a))
}

fn scope_text(s: Option<usize>) -> String {
    match s {
        Some(s) => format!("scope C{s}"),
        None => "global scope".into(),
    }
}

/// The nearest declaration of member `k` in `table` on `c`'s chain, and
/// whether it carries PHP's `ZEND_ACC_CHANGED`: set on a redeclaration of a
/// member that is private or itself `CHANGED` in the parent
/// (`do_inheritance_check_on_method`, `do_inherit_property`), so on any
/// declaration with a private one somewhere above it.
fn lookup(
    w: &World,
    table: &[[Option<Vis>; NAMES]],
    c: usize,
    k: usize,
) -> Option<(usize, Vis, bool)> {
    let ch = chain(w, c);
    let i = ch.iter().position(|&x| table[x][k].is_some())?;
    let d = ch[i];
    let vis = table[d][k]?;
    let changed = ch[i + 1..]
        .iter()
        .any(|&x| table[x][k] == Some(Vis::Private));
    Some((d, vis, changed))
}

/// `zend_get_parent_private_method`/`_property`: the scope's own private
/// member, when the object is an instance of a strict subclass of it.
fn parent_private(
    w: &World,
    table: &[[Option<Vis>; NAMES]],
    s: Option<usize>,
    c: usize,
    k: usize,
) -> Option<usize> {
    let s = s?;
    (s != c && chain(w, c).contains(&s) && table[s][k] == Some(Vis::Private)).then_some(s)
}

/// `$o->m{k}()` from scope `s` on an instance of `c`.
fn call(w: &World, s: Option<usize>, c: usize, k: usize) -> String {
    let Some((d, vis, changed)) = lookup(w, &w.methods, c, k) else {
        return "E:104:".into();
    };
    let ok = |d: usize| format!("C{d}.m{k}");
    if Some(d) == s || (vis == Vis::Public && !changed) {
        return ok(d);
    }
    if changed {
        if let Some(p) = parent_private(w, &w.methods, s, c, k) {
            return ok(p);
        }
        if vis == Vis::Public {
            return ok(d);
        }
    }
    match vis {
        Vis::Private => format!(
            "E:100:Call to private method C{d}::m{k}() from {}",
            scope_text(s)
        ),
        _ => {
            // The prototype root: up the chain while the overridden
            // declaration is not private.
            let ch = chain(w, d);
            let mut root = d;
            for &x in &ch[1..] {
                match w.methods[x][k] {
                    Some(Vis::Private) => break,
                    Some(_) => root = x,
                    None => {}
                }
            }
            if related(w, s, root) {
                ok(d)
            } else {
                format!(
                    "E:100:Call to protected method C{d}::m{k}() from {}",
                    scope_text(s)
                )
            }
        }
    }
}

/// `$o->p{k}` from scope `s` on an instance of `c`.
fn read(w: &World, s: Option<usize>, c: usize, k: usize) -> String {
    let Some((d, vis, changed)) = lookup(w, &w.props, c, k) else {
        return "E:104:".into();
    };
    let ok = |d: usize| format!("C{d}.p{k}");
    if Some(d) == s || (vis == Vis::Public && !changed) {
        return ok(d);
    }
    if changed {
        if let Some(p) = parent_private(w, &w.props, s, c, k) {
            return ok(p);
        }
        if vis == Vis::Public {
            return ok(d);
        }
    }
    match vis {
        // An ancestor's private property is an undefined (dynamic) one.
        Vis::Private if d != c => "E:104:".into(),
        Vis::Private => format!("E:100:Cannot access private property C{d}::$p{k}"),
        _ if related(w, s, d) => ok(d),
        _ => format!("E:100:Cannot access protected property C{d}::$p{k}"),
    }
}

// ------------------------------------------------------------------ program

/// The probes of one scope: `call_m{k}($o)` and `read_p{k}($o)`, as methods
/// of class `s` or as free functions.
fn probes(h: &mut H, method: bool, prefix: &str) -> Vec<hir_lang::ItemId> {
    let mut out = Vec::new();
    for k in 0..NAMES {
        for read in [false, true] {
            let mut ps = Vec::new();
            if method {
                ps.push(h.this_param().0);
            }
            ps.push(h.param("o", ParamKind::Normal, None, false).0);
            let o = h.uname("o");
            let e = if read {
                h.field(o, &format!("p{k}"))
            } else {
                h.method(o, &format!("m{k}"), &[])
            };
            let r = h.ret(Some(e));
            let body = h.block(&[], Some(r));
            let name = format!("{prefix}{}{k}", if read { "read_p" } else { "call_m" });
            out.push(if method {
                h.method_item(&name, Vis::Public, &ps, body)
            } else {
                h.func(&name, &ps, body, DefaultEval::PerCall)
            });
        }
    }
    out
}

fn echo(h: &mut H, args: &[ExprId]) -> StmtId {
    let e = h.uname("echo");
    let c = h.call(e, args);
    h.stmt(c)
}

/// Builds, resolves, compiles, and runs the world's probes; returns what
/// each access printed, in (scope, class, member) order.
fn run(w: &World) -> Vec<String> {
    let n = w.parent.len();
    let mut h = H::new();
    let mut classes = Vec::new();
    for c in 0..n {
        let mut fields = Vec::new();
        let mut items = Vec::new();
        for k in 0..NAMES {
            if let Some(v) = w.props[c][k] {
                let d = h.str(&format!("C{c}.p{k}"));
                fields.push(h.prop(&format!("p{k}"), v, Some(d)));
            }
            if let Some(v) = w.methods[c][k] {
                let tp = h.this_param().0;
                let s = h.str(&format!("C{c}.m{k}"));
                let r = h.ret(Some(s));
                let body = h.block(&[], Some(r));
                items.push(h.method_item(&format!("m{k}"), v, &[tp], body));
            }
        }
        items.extend(probes(&mut h, true, &format!("s{c}_")));
        let base = w.parent[c].map(|p| format!("C{p}"));
        classes.push(h.class(&format!("C{c}"), base.as_deref(), &fields, &items));
    }
    let free = probes(&mut h, false, "g_");
    let mut stmts = Vec::new();
    for s in std::iter::once(None).chain((0..n).map(Some)) {
        for c in 0..n {
            for k in 0..NAMES {
                for read in [false, true] {
                    let kind = if read { "read_p" } else { "call_m" };
                    let cr = h.item_ref(&format!("C{c}"), classes[c]);
                    let f = h.extern_ref("mox.new");
                    let obj = h.call(f, &[cr]);
                    let probe = match s {
                        None => {
                            let g = h.uname(&format!("g_{kind}{k}"));
                            h.call(g, &[obj])
                        }
                        Some(s) => {
                            let sr = h.item_ref(&format!("C{s}"), classes[s]);
                            let f = h.extern_ref("mox.new");
                            let so = h.call(f, &[sr]);
                            h.method(so, &format!("s{s}_{kind}{k}"), &[obj])
                        }
                    };
                    let body = {
                        let st = echo(&mut h, &[probe]);
                        h.block(&[st], None)
                    };
                    let ty = h.ty(Ty::Any);
                    let eb = h.local("e");
                    let bind = h.pbind(eb);
                    let pat = h.pat(hir_lang::Pat::TypeTest {
                        ty,
                        pat: Some(bind),
                    });
                    let ev = h.var(eb);
                    let code = h.intrinsic("err_code", &[ev]);
                    let ev = h.var(eb);
                    let payload = h.intrinsic("err_payload", &[ev]);
                    let e1 = h.str("E:");
                    let e2 = h.str(":");
                    let st = echo(&mut h, &[e1, code, e2, payload]);
                    let cb = h.block(&[st], None);
                    let arm = h.arm(pat, None, cb);
                    let t = h.try_(body, &[arm], None);
                    stmts.push(h.stmt(t));
                }
            }
        }
    }
    let body = h.block(&stmts, None);
    let mut items = classes.clone();
    items.extend(free);
    let (hir, names) = h.finish(&items, Some(body));
    let mut env = MapEnv::new();
    if let Some(echo) = names.get("echo") {
        env = env.with_prelude(
            hir_lang::Name::new(echo),
            Namespace::Value,
            Export::new(hir_lang::Res::Extern(echo), DefKind::Extern),
        );
    }
    let unit = hir.unit();
    let res = Resolver::new(Policy::php())
        .with_env(&env)
        .resolve(hir, &names)
        .unwrap_or_else(|e| panic!("{e}"));
    let msgs: Vec<String> = res
        .diagnostics()
        .iter()
        .map(|d| d.message(&names))
        .collect();
    assert!(res.is_clean(), "{msgs:?}");
    let hir = res.hir(unit).cloned().unwrap_or_else(|| panic!("unit"));
    let out = Compiler::new(
        Options::new()
            .with_body(BodyMode::Entry)
            .with_intrinsics(Intrinsics::mox()),
    )
    .compile(&hir, &names)
    .unwrap_or_else(|e| panic!("compile: {e}"));
    let printed = Arc::new(Mutex::new(Vec::new()));
    let host = common::host(printed.clone());
    let program = Program::load(out.module().clone(), &host).unwrap_or_else(|e| panic!("{e}"));
    let mut vm = Vm::new(&program);
    vm.run(out.entry(), &[])
        .unwrap_or_else(|e| panic!("run: {e:?}"));
    printed.lock().map(|v| v.clone()).unwrap_or_default()
}

fn expected(w: &World) -> Vec<String> {
    let n = w.parent.len();
    let mut out = Vec::new();
    for s in std::iter::once(None).chain((0..n).map(Some)) {
        for c in 0..n {
            for k in 0..NAMES {
                out.push(call(w, s, c, k));
                out.push(read(w, s, c, k));
            }
        }
    }
    out
}

fn check(seed: u64) {
    let w = world(seed);
    let got = run(&w);
    let want = expected(&w);
    assert_eq!(got.len(), want.len(), "{w:?}");
    for (i, (g, e)) in got.iter().zip(&want).enumerate() {
        assert_eq!(g, e, "access {i} of {w:?}");
    }
}

/// Cases per run (`BCGEN_CASES` overrides, for long runs).
fn cases() -> u32 {
    std::env::var("BCGEN_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(300)
}

proptest! {
    #![proptest_config(ProptestConfig { cases: cases(), ..ProptestConfig::default() })]

    #[test]
    fn dispatch_and_visibility_match_the_php_model(seed in any::<u64>()) {
        check(seed);
    }
}

#[test]
fn the_generator_reaches_every_visibility_outcome() {
    let (mut private_call, mut protected_call, mut private_read, mut undefined, mut changed) =
        (0, 0, 0, 0, 0);
    let mut shared = 0;
    for seed in 0..400u64 {
        let w = world(seed);
        for line in expected(&w) {
            private_call += usize::from(line.contains("private method"));
            protected_call += usize::from(line.contains("protected method"));
            private_read += usize::from(line.contains("private property"));
            undefined += usize::from(line == "E:104:");
        }
        let n = w.parent.len();
        for k in 0..NAMES {
            let decls = |t: &Vec<[Option<Vis>; NAMES]>| t.iter().filter(|m| m[k].is_some()).count();
            shared += usize::from(decls(&w.methods) > 4 || decls(&w.props) > 4);
        }
        for c in 0..n {
            for k in 0..NAMES {
                changed += usize::from(lookup(&w, &w.methods, c, k).is_some_and(|x| x.2));
            }
        }
    }
    for (name, n) in [
        ("private calls", private_call),
        ("protected calls", protected_call),
        ("private reads", private_read),
        ("undefined", undefined),
        ("redeclared privates", changed),
        ("names with shared checks", shared),
    ] {
        assert!(n >= 20, "{name}: {n}");
    }
}
