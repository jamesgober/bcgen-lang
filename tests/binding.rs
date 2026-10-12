//! Argument binding (LSB §5.15): a call of a known function is arranged at
//! compile time; the same call through the function's value is bound by the
//! VM through the function's parameter list. For random parameter lists
//! (every kind, defaults, by-reference parameters) and random argument
//! lists (positional, named, unknown names, spreads, named spreads), both
//! give the same parameter values or the same error, and the reference
//! interpreter agrees with both.

mod common;

use common::hb::H;
use common::progs::Rng;
use common::{Outcome, Profile, check};
use hir_lang::{Arg, ArgKind, DefaultEval, ExprId, ParamKind};
use proptest::prelude::*;

const NAMES: &[&str] = &["a", "b", "c", "d", "e"];

fn case(seed: u64) -> (hir_lang::Hir, intern_lang::Interner) {
    let mut r = Rng::new(seed);
    let mut h = H::new();
    // Parameters, kinds in LSB order.
    let mut kinds: Vec<ParamKind> = (0..r.below(5))
        .map(|_| {
            r.pick(&[
                ParamKind::PositionalOnly,
                ParamKind::Normal,
                ParamKind::Normal,
                ParamKind::Rest,
                ParamKind::NamedOnly,
                ParamKind::RestNamed,
            ])
        })
        .collect();
    let rank = |k: &ParamKind| match k {
        ParamKind::PositionalOnly => 0,
        ParamKind::Normal => 1,
        ParamKind::Rest => 2,
        ParamKind::NamedOnly => 3,
        _ => 4,
    };
    kinds.sort_by_key(rank);
    kinds.dedup_by(|a, b| *a == *b && matches!(a, ParamKind::Rest | ParamKind::RestNamed));
    let mut params = Vec::new();
    let mut binders = Vec::new();
    for (i, &k) in kinds.iter().enumerate() {
        let rest = matches!(k, ParamKind::Rest | ParamKind::RestNamed);
        let default = (!rest && r.chance(40)).then(|| h.int(100 + i as i64));
        let (p, b) = h.param(NAMES[i], k, default, false);
        params.push(p);
        binders.push(b);
    }
    let vals: Vec<ExprId> = binders.iter().map(|&b| h.var(b)).collect();
    let out = h.array(&vals);
    let body = h.block(&[], Some(out));
    let f = h.func("f", &params, body, DefaultEval::PerCall);
    // Arguments: a spec, built twice (HIR is a tree); names unique.
    #[derive(Clone, Copy)]
    enum Spec {
        Pos(i64),
        Named(&'static str, i64),
        Spread(i64, i64),
        SpreadNamed(&'static str, i64),
    }
    let mut spec = Vec::new();
    let mut used: Vec<&str> = Vec::new();
    for _ in 0..r.below(6) {
        let v = r.below(50) as i64;
        spec.push(match r.below(8) {
            0..=3 => Spec::Pos(v),
            4 | 5 => {
                let n = if r.chance(85) { r.pick(NAMES) } else { "zz" };
                if used.contains(&n) {
                    continue;
                }
                used.push(n);
                Spec::Named(n, v)
            }
            6 => Spec::Spread(v, r.below(50) as i64),
            _ => Spec::SpreadNamed(r.pick(NAMES), v),
        });
    }
    let build = |h: &mut H| -> Vec<Arg> {
        spec.iter()
            .map(|s| match *s {
                Spec::Pos(v) => {
                    let e = h.int(v);
                    Arg::positional(e)
                }
                Spec::Named(n, v) => {
                    let e = h.int(v);
                    h.named(n, e)
                }
                Spec::Spread(a, b) => {
                    let (x, y) = (h.int(a), h.int(b));
                    let list = h.array(&[x, y]);
                    Arg {
                        kind: ArgKind::Spread,
                        value: list,
                        place: false,
                    }
                }
                Spec::SpreadNamed(n, v) => {
                    let k = h.str(n);
                    let e = h.int(v);
                    let map = h.map(&[(Some(k), e)]);
                    Arg {
                        kind: ArgKind::SpreadNamed,
                        value: map,
                        place: false,
                    }
                }
            })
            .collect()
    };
    // [try f(args), try (f as a value)(args)]
    let guarded = |h: &mut H, e: ExprId| {
        let x = h.local("x");
        let px = h.pbind(x);
        let vx = h.var(x);
        let arm = h.arm(px, None, vx);
        h.try_(e, &[arm], None)
    };
    let fd = h.item_ref("f", f);
    let args = build(&mut h);
    let direct = h.call_args(fd, &args);
    let direct = guarded(&mut h, direct);
    let g = h.local("g");
    let fv = h.item_ref("f", f);
    let lg = h.let_(g, Some(fv));
    let vg = h.var(g);
    let args = build(&mut h);
    let dynamic = h.call_args(vg, &args);
    let dynamic = guarded(&mut h, dynamic);
    let both = h.array(&[direct, dynamic]);
    let main = h.block(&[lg], Some(both));
    h.finish(&[f], Some(main))
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 3000, ..ProptestConfig::default() })]

    #[test]
    fn arranged_and_dynamic_calls_bind_alike(seed in any::<u64>()) {
        let (hir, names) = case(seed);
        let o = check(&hir, &names, Profile::PHP);
        if let Outcome::Value(common::RV::Map(pair)) = o {
            prop_assert_eq!(pair.len(), 2);
            prop_assert_eq!(&pair[0].1, &pair[1].1, "{}", hir_lang::print(&hir, &names));
        }
    }
}
