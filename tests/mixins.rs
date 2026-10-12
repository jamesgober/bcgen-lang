//! Mixin (PHP trait) flattening against a model of PHP: random graphs of
//! mixins that use mixins, with `insteadof` and `as` rules PHP accepts, used
//! by classes with methods of their own. The model transcribes PHP 8's
//! `zend_traits_copy_functions`/`zend_add_trait_method`; every name of a
//! class must call, through bcgen-lang and bvm-lang, the method the model
//! says (a non-public one is refused, an absent one undefined), and every
//! method in the model's table must have been compiled for the class.
//!
//! resolve-lang 0.4 builds the same tables independently
//! (`ResolvedUnit::members`); where it differs from the model the
//! difference is counted and printed (`resolve_lang_differences`), not
//! asserted: it is resolve-lang's to fix.

mod common;

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use bcgen_lang::{BodyMode, Compiler, Intrinsics, Options};
use bvm_lang::{Program, Vm};
use common::hb::H;
use std::collections::{BTreeMap, BTreeSet};

use hir_lang::{Def, ItemId, MixinAction, MixinRule, Res, StmtId, Ty, Vis};
use proptest::prelude::*;
use resolve_lang::{DefKind, Export, MapEnv, Namespace, Policy, Resolver};

const METHODS: usize = 4;

/// How many class members resolve-lang's tables gave differently from the
/// model (a resolve-lang issue; reported, not asserted).
static RESOLVE_DIFFERENCES: AtomicU64 = AtomicU64::new(0);

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

fn vis(rng: &mut Rng) -> Vis {
    [Vis::Public, Vis::Public, Vis::Protected, Vis::Private][rng.below(4) as usize]
}

/// A `use` of `mixins` (by index) whose rules PHP accepts: every name two
/// used mixins provide gets an `insteadof` choosing one; aliases take fresh
/// names; an unqualified rule names a method only one used mixin has.
/// Returns the item and the names the use brings in.
fn mixin_use(
    h: &mut H,
    rng: &mut Rng,
    mixins: &[usize],
    provides: &[BTreeSet<String>],
    fresh: &mut u32,
) -> (ItemId, BTreeSet<String>) {
    let names: Vec<String> = mixins.iter().map(|m| format!("T{m}")).collect();
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let mut rules = Vec::new();
    let mut brought: BTreeSet<String> = BTreeSet::new();
    let mut providers: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for &m in mixins {
        for n in &provides[m] {
            providers.entry(n.clone()).or_default().push(m);
            brought.insert(n.clone());
        }
    }
    // Conflicts: one winner each.
    for (name, ps) in &providers {
        if ps.len() < 2 {
            continue;
        }
        let w = ps[rng.below(ps.len() as u64) as usize];
        let from = h.ty_name(&format!("T{w}"));
        let others: Vec<_> = ps
            .iter()
            .filter(|&&o| o != w)
            .map(|o| h.ty_name(&format!("T{o}")))
            .collect();
        let others = h.b.list(&others);
        rules.push(MixinRule {
            method: h.ident(name),
            from: Some(from),
            action: MixinAction::Insteadof(others),
        });
    }
    let all: Vec<(String, Vec<usize>)> = providers.into_iter().collect();
    for _ in 0..rng.below(4) {
        if all.is_empty() {
            break;
        }
        let (name, ps) = &all[rng.below(all.len() as u64) as usize];
        let single = ps.len() == 1;
        let t = ps[rng.below(ps.len() as u64) as usize];
        let qualified = !single || rng.below(2) == 0;
        let from = qualified.then(|| h.ty_name(&format!("T{t}")));
        let method = h.ident(name);
        if rng.below(2) == 0 {
            *fresh += 1;
            let alias = format!("a{fresh}");
            let v = (rng.below(2) == 0).then(|| vis(rng));
            rules.push(MixinRule {
                method,
                from,
                action: MixinAction::Alias {
                    name: Some(h.ident(&alias)),
                    vis: v,
                },
            });
            brought.insert(alias);
        } else {
            rules.push(MixinRule {
                method,
                from,
                action: MixinAction::Alias {
                    name: None,
                    vis: Some(vis(rng)),
                },
            });
        }
    }
    (h.mixin_use(&refs, &rules), brought)
}

/// Builds a random program; returns it with the class items and every
/// method name a class may have.
fn program(
    seed: u64,
) -> (
    hir_lang::Hir,
    intern_lang::Interner,
    Vec<ItemId>,
    Vec<String>,
) {
    let mut rng = Rng(seed | 1);
    let mut h = H::new();
    let nm = 1 + rng.below(4) as usize;
    let mut provides: Vec<BTreeSet<String>> = Vec::new();
    let mut fresh = 0u32;
    let mut items = Vec::new();
    for t in 0..nm {
        let mut members = Vec::new();
        let mut mine: BTreeSet<String> = BTreeSet::new();
        for m in 0..METHODS {
            if rng.below(2) == 0 {
                let tp = h.this_param().0;
                let s = h.str(&format!("T{t}.m{m}"));
                let r = h.ret(Some(s));
                let body = h.block(&[], Some(r));
                let v = vis(&mut rng);
                members.push(h.method_item(&format!("m{m}"), v, &[tp], body));
                mine.insert(format!("m{m}"));
            }
        }
        // Mixins use earlier mixins (no cycles).
        if t > 0 && rng.below(2) == 0 {
            let k = 1 + rng.below(t.min(2) as u64) as usize;
            let mut used: Vec<usize> = (0..k).map(|_| rng.below(t as u64) as usize).collect();
            used.sort_unstable();
            used.dedup();
            let (u, brought) = mixin_use(&mut h, &mut rng, &used, &provides, &mut fresh);
            members.push(u);
            mine.extend(brought);
        }
        provides.push(mine);
        items.push(h.class_full(&format!("T{t}"), None, &[], &[], &members, false, true));
    }
    let mut classes = Vec::new();
    let mut names: BTreeSet<String> = BTreeSet::new();
    for c in 0..1 + rng.below(3) as usize {
        let mut members = Vec::new();
        for m in 0..METHODS {
            if rng.below(4) == 0 {
                let tp = h.this_param().0;
                let s = h.str(&format!("C{c}.m{m}"));
                let r = h.ret(Some(s));
                let body = h.block(&[], Some(r));
                members.push(h.method_item(&format!("m{m}"), Vis::Public, &[tp], body));
                names.insert(format!("m{m}"));
            }
        }
        let k = 1 + rng.below(nm.min(3) as u64) as usize;
        let mut used: Vec<usize> = (0..k).map(|_| rng.below(nm as u64) as usize).collect();
        used.sort_unstable();
        used.dedup();
        let (u, brought) = mixin_use(&mut h, &mut rng, &used, &provides, &mut fresh);
        names.extend(brought);
        members.push(u);
        let class = h.class(&format!("C{c}"), None, &[], &members);
        classes.push(class);
        items.push(class);
    }
    let names: Vec<String> = names.into_iter().collect();
    // Calls of every name a class may have, from the global scope.
    let mut stmts: Vec<StmtId> = Vec::new();
    for (c, &class) in classes.iter().enumerate() {
        for name in &names {
            let cr = h.item_ref(&format!("C{c}"), class);
            let f = h.extern_ref("mox.new");
            let o = h.call(f, &[cr]);
            let call = h.method(o, name, &[]);
            let e = h.uname("echo");
            let ec = h.call(e, &[call]);
            let st = h.stmt(ec);
            let body = h.block(&[st], None);
            let ty = h.ty(Ty::Any);
            let eb = h.local("e");
            let bind = h.pbind(eb);
            let pat = h.pat(hir_lang::Pat::TypeTest {
                ty,
                pat: Some(bind),
            });
            let ev = h.var(eb);
            let code = h.intrinsic("err_code", &[ev]);
            let mark = h.str("E");
            let e = h.uname("echo");
            let ec = h.call(e, &[mark, code]);
            let cs = h.stmt(ec);
            let cb = h.block(&[cs], None);
            let arm = h.arm(pat, None, cb);
            let t = h.try_(body, &[arm], None);
            stmts.push(h.stmt(t));
        }
    }
    let body = h.block(&stmts, None);
    let (hir, interner) = h.finish(&items, Some(body));
    (hir, interner, classes, names)
}

/// One method of a model table: its item and visibility, and whether it is
/// the container's own (own members win over mixin ones).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Fm {
    item: ItemId,
    vis: Vis,
    own: bool,
}

/// PHP's effective method table of `container` (a class or mixin item),
/// in insertion order, computed from the HIR (mixins first, memoized).
fn php_table(
    hir: &hir_lang::Hir,
    names: &intern_lang::Interner,
    container: ItemId,
    memo: &mut BTreeMap<ItemId, Vec<(String, Fm)>>,
) -> Vec<(String, Fm)> {
    if let Some(t) = memo.get(&container) {
        return t.clone();
    }
    let hir_lang::ItemKind::Class(def) = hir.item(container).kind else {
        return Vec::new();
    };
    let text = |sym: hir_lang::Symbol| names.resolve(sym).unwrap_or("").to_string();
    let item_of = |ty: hir_lang::TyId| -> Option<ItemId> {
        let hir_lang::Ty::Path(p) = *hir.ty(ty) else {
            return None;
        };
        match hir.path(p).res {
            Res::Def(d) => match d.def() {
                Def::Item(i) => Some(i),
                Def::Variant(_) => None,
            },
            _ => None,
        }
    };
    let mut table: Vec<(String, Fm)> = Vec::new();
    for &m in hir.list(def.items) {
        let it = *hir.item(m);
        if let (hir_lang::ItemKind::Fn(_), Some(n)) = (it.kind, it.name) {
            table.push((
                text(n.sym),
                Fm {
                    item: m,
                    vis: it.vis,
                    own: true,
                },
            ));
        }
    }
    for &u in hir.list(def.items) {
        let hir_lang::ItemKind::MixinUse(ud) = hir.item(u).kind else {
            continue;
        };
        let traits: Vec<ItemId> = hir
            .list(ud.mixins)
            .iter()
            .filter_map(|&t| item_of(t))
            .collect();
        let tables: Vec<Vec<(String, Fm)>> = traits
            .iter()
            .map(|&t| php_table(hir, names, t, memo))
            .collect();
        let rules = hir.list(ud.rules);
        let mut exclude: BTreeSet<(ItemId, String)> = BTreeSet::new();
        // aliases[i]: the trait each `as` rule applies to.
        let mut aliases: Vec<(ItemId, String, Option<String>, Option<Vis>)> = Vec::new();
        for r in rules {
            let method = text(r.method.sym);
            match r.action {
                MixinAction::Insteadof(others) => {
                    for &o in hir.list(others) {
                        if let Some(oi) = item_of(o) {
                            exclude.insert((oi, method.clone()));
                        }
                    }
                }
                MixinAction::Alias { name, vis } => {
                    let t = match r.from.and_then(item_of) {
                        Some(t) => Some(t),
                        // Unqualified: the one used trait that has it.
                        None => traits
                            .iter()
                            .zip(&tables)
                            .find(|(_, tab)| tab.iter().any(|(n, _)| *n == method))
                            .map(|(&t, _)| t),
                    };
                    if let Some(t) = t {
                        aliases.push((t, method, name.map(|n| text(n.sym)), vis));
                    }
                }
            }
        }
        for (&t, tab) in traits.iter().zip(&tables) {
            for (name, f) in tab {
                for (at, am, alias, vis) in &aliases {
                    if *at == t && am == name {
                        if let Some(alias) = alias {
                            let copy = Fm {
                                vis: vis.unwrap_or(f.vis),
                                own: false,
                                ..*f
                            };
                            add(&mut table, alias, copy);
                        }
                    }
                }
                if !exclude.contains(&(t, name.clone())) {
                    let mut copy = Fm { own: false, ..*f };
                    for (at, am, alias, vis) in &aliases {
                        if *at == t && am == name && alias.is_none() {
                            if let Some(v) = vis {
                                copy.vis = *v;
                            }
                        }
                    }
                    add(&mut table, name, copy);
                }
            }
        }
    }
    memo.insert(container, table.clone());
    table
}

/// `zend_add_trait_method`: an own member wins; the same method at the
/// same visibility is no conflict; the generator makes no other conflict.
fn add(table: &mut Vec<(String, Fm)>, name: &str, f: Fm) {
    match table.iter().find(|(n, _)| n == name) {
        Some((_, e)) if e.own => {}
        Some(_) => {}
        None => table.push((name.to_string(), f)),
    }
}

fn check(seed: u64) {
    let (hir, names, classes, methods) = program(seed);
    let mut env = MapEnv::new();
    if let Some(echo) = names.get("echo") {
        env = env.with_prelude(
            hir_lang::Name::new(echo),
            Namespace::Value,
            Export::new(Res::Extern(echo), DefKind::Extern),
        );
    }
    let unit = hir.unit();
    let res = Resolver::new(Policy::php())
        .with_env(&env)
        .resolve(hir, &names)
        .unwrap_or_else(|e| panic!("{e}"));
    // The programs are ones PHP accepts: resolution is clean.
    let problems: Vec<String> = res
        .diagnostics()
        .iter()
        .map(|d| d.message(&names))
        .collect();
    assert!(res.is_clean(), "{problems:?}");
    let ru = res.unit(unit).unwrap_or_else(|| panic!("unit"));
    let hir = ru.hir().clone();
    let out = Compiler::new(
        Options::new()
            .with_body(BodyMode::Entry)
            .with_intrinsics(Intrinsics::mox()),
    )
    .compile(&hir, &names)
    .unwrap_or_else(|e| panic!("compile: {e}"));
    // The expected output, from the PHP model; resolve-lang's tables are
    // compared on the side.
    let mut want: Vec<String> = Vec::new();
    let mut memo = BTreeMap::new();
    for &class in &classes {
        let table = php_table(&hir, &names, class, &mut memo);
        let members = ru.members(class).unwrap_or(&[]);
        for name in &methods {
            let model = table.iter().find(|(n, _)| n == name).map(|(_, f)| *f);
            let resolved = members
                .iter()
                .find(|m| {
                    m.namespace == Namespace::Value
                        && names.resolve(m.name.sym) == Some(name.as_str())
                        && matches!(m.res, Res::Def(_))
                })
                .map(|m| (m.res, m.vis));
            let agrees = match (model, resolved) {
                (None, None) => true,
                (Some(f), Some((Res::Def(d), vis))) => d.def() == Def::Item(f.item) && vis == f.vis,
                _ => false,
            };
            if !agrees {
                RESOLVE_DIFFERENCES.fetch_add(1, Ordering::Relaxed);
            }
            want.push(match model {
                None => "E104".into(),
                Some(f) if f.vis != Vis::Public => "E100".into(),
                Some(f) => {
                    let label = method_label(&hir, &names, f.item);
                    assert!(out.method(class, f.item).is_some(), "{label} not compiled");
                    label
                }
            });
        }
    }
    let printed = Arc::new(Mutex::new(Vec::new()));
    let host = common::host(printed.clone());
    let program = Program::load(out.module().clone(), &host).unwrap_or_else(|e| panic!("{e}"));
    let mut vm = Vm::new(&program);
    vm.run(out.entry(), &[])
        .unwrap_or_else(|e| panic!("run: {e:?}"));
    let got = printed.lock().map(|v| v.clone()).unwrap_or_default();
    assert_eq!(got, want, "seed {seed}");
}

/// The string a generated method returns.
fn method_label(hir: &hir_lang::Hir, names: &intern_lang::Interner, item: ItemId) -> String {
    let hir_lang::ItemKind::Fn(def) = hir.item(item).kind else {
        return String::new();
    };
    let Some(body) = def.body else {
        return String::new();
    };
    let hir_lang::Expr::Block(b) = *hir.expr(body) else {
        return String::new();
    };
    let Some(tail) = b.tail else {
        return String::new();
    };
    let hir_lang::Expr::Return(Some(v)) = *hir.expr(tail) else {
        return String::new();
    };
    match *hir.expr(v) {
        hir_lang::Expr::Lit(hir_lang::Lit::Str(t)) => hir.str(t).to_string(),
        _ => {
            let _ = names;
            String::new()
        }
    }
}

/// Cases per run (`BCGEN_CASES` overrides, for long runs).
fn cases() -> u32 {
    std::env::var("BCGEN_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(400)
}

proptest! {
    #![proptest_config(ProptestConfig { cases: cases(), ..ProptestConfig::default() })]

    #[test]
    fn flattening_matches_the_php_model(seed in any::<u64>()) {
        check(seed);
    }
}

/// Counts where resolve-lang's member tables differ from the model over a
/// fixed range of seeds, and prints it (`--nocapture`).
#[test]
fn resolve_lang_differences() {
    let before = RESOLVE_DIFFERENCES.load(Ordering::Relaxed);
    for seed in 0..200u64 {
        check(seed);
    }
    let n = RESOLVE_DIFFERENCES.load(Ordering::Relaxed) - before;
    println!("resolve-lang member tables differ from the PHP model on {n} members");
}

/// Prints one seed's program and resolve-lang's tables
/// (`BCGEN_SEED=n cargo test --test mixins debug_seed -- --ignored --nocapture`).
#[test]
#[ignore = "a debugging aid"]
fn debug_seed() {
    let seed: u64 = std::env::var("BCGEN_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let (hir, names, classes, methods) = program(seed);
    println!("{}", hir_lang::print(&hir, &names));
    let unit = hir.unit();
    let res = Resolver::new(Policy::php())
        .resolve(hir, &names)
        .unwrap_or_else(|e| panic!("{e}"));
    let ru = res.unit(unit).unwrap_or_else(|| panic!("unit"));
    for &c in &classes {
        for m in ru.members(c).unwrap_or(&[]) {
            println!(
                "class {c:?}: {:?} {:?} {:?} {:?} mixin {:?}",
                names.resolve(m.name.sym),
                m.namespace,
                m.res,
                m.vis,
                m.mixin
            );
        }
    }
    println!("{methods:?}");
}
