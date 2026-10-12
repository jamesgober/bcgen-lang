//! The differential oracle: random well-formed dynamic programs run through
//! bcgen-lang and bvm-lang, and through the reference interpreter in
//! `tests/common/reference.rs`. Results, printed output, error kinds, and
//! error locations (the HIR node of the raising instruction) must be
//! identical, under both array profiles.

mod common;

use common::{Outcome, Profile, check, progs};
use proptest::prelude::*;

fn run(seed: u64) {
    let (hir, names) = progs::program(seed);
    let _ = check(&hir, &names, Profile::PHP);
    let _ = check(&hir, &names, Profile::REFERENCE);
    // Code for a reference-counting VM clears dead registers: no result
    // may change.
    let _ = check(&hir, &names, Profile::PHP_CLEAR);
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 3000, ..ProptestConfig::default() })]

    #[test]
    fn compiled_programs_agree_with_the_reference(seed in any::<u64>()) {
        run(seed);
    }
}

/// The generator must reach every outcome the comparison is about: values,
/// runtime errors, thrown values, and traps, with few cases left
/// unspecified.
#[test]
fn the_generator_covers_every_outcome() {
    let (mut values, mut raised, mut thrown, mut traps, mut open) = (0, 0, 0, 0, 0);
    let n = 2000u64;
    for seed in 0..n {
        let (hir, names) = progs::program(seed);
        eprintln!("seed {seed}");
        match check(&hir, &names, Profile::PHP) {
            Outcome::Value(_) => values += 1,
            Outcome::Raised { .. } => raised += 1,
            Outcome::Thrown { .. } => thrown += 1,
            Outcome::Trap { .. } => traps += 1,
            Outcome::Unspecified | Outcome::Budget => open += 1,
        }
    }
    println!("values {values} raised {raised} thrown {thrown} traps {traps} open {open}");
    assert!(values > n / 10, "values {values}");
    assert!(raised > n / 20, "raised {raised}");
    assert!(thrown > n / 50, "thrown {thrown}");
    assert!(traps > 0, "traps {traps}");
    assert!(open < n / 4, "open {open}");
}

/// The generator reaches the 0.3 forms: `let_place`, `pow`, `bit_not`,
/// saturating shifts, and union type tests.
#[test]
fn the_generator_reaches_the_0_3_forms() {
    use hir_lang::{Expr, IdKind, OpKind, Pat, Ty};
    let (mut let_place, mut pow, mut bit_not, mut saturate, mut union) = (0, 0, 0, 0, 0);
    for seed in 0..1000u64 {
        let (hir, _) = progs::program(seed);
        for i in 0..hir.count(IdKind::Expr) {
            let Some(e) = hir_lang::ExprId::from_index(i) else {
                continue;
            };
            match *hir.expr(e) {
                Expr::LetPlace { .. } => let_place += 1,
                Expr::Op { op, .. } => {
                    pow += usize::from(op.kind == OpKind::Pow);
                    bit_not += usize::from(op.kind == OpKind::BitNot);
                    saturate += usize::from(op.policy.shift == Some(hir_lang::Shift::Saturate));
                }
                _ => {}
            }
        }
        for i in 0..hir.count(IdKind::Pat) {
            let Some(p) = hir_lang::PatId::from_index(i) else {
                continue;
            };
            if let Pat::TypeTest { ty, .. } = *hir.pat(p) {
                let inner = match *hir.ty(ty) {
                    Ty::Nullable(t) => t,
                    _ => ty,
                };
                union += usize::from(matches!(hir.ty(inner), Ty::Union(_)));
            }
        }
    }
    println!("let_place {let_place} pow {pow} bit_not {bit_not} saturate {saturate} union {union}");
    for (name, n) in [
        ("let_place", let_place),
        ("pow", pow),
        ("bit_not", bit_not),
        ("saturate", saturate),
        ("union", union),
    ] {
        assert!(n >= 20, "{name}: {n}");
    }
}

/// A long run over consecutive seeds (`BCGEN_SEEDS=1000000 BCGEN_START=0
/// cargo test --release --test differential many_seeds -- --ignored`).
#[test]
#[ignore = "a long run"]
fn many_seeds() {
    let n: u64 = std::env::var("BCGEN_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(10_000);
    let start: u64 = std::env::var("BCGEN_START")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    for seed in start..start + n {
        let r = std::panic::catch_unwind(|| run(seed));
        assert!(r.is_ok(), "seed {seed} disagrees");
    }
}

/// Seeds that once disagreed, kept as regressions (each found a real bug):
/// a positional argument overwriting a named one in static arrangement; a
/// value-less `break` out of a labeled block; a block returning its own
/// local's freed register; `[$v; n]` aliasing its element; `return $local`
/// across a `finally` that writes it; a static captured by reference and
/// rebound; an identity cast treated as a fresh value; a place root read
/// before a value that rebinds it (reference); a loop clearing the
/// register of the variable it is assigned to; a by-value capture of a
/// `global` alias.
#[test]
fn regressions() {
    for seed in [
        384u64,
        18_204_896_487_283_575_504,
        561_219_781_297_418_254,
        1_459_748_986_233_993_778,
        673_093_343_114_015_330,
        18_346_056_200_050_775_952,
        1_310_342_498_134_303_474,
        6_586_930_659_798_921_448,
        17_230_388_835_655_610_194,
        2_859_279_790_412_779_944,
        15_893_534_721_177_827_994,
    ] {
        run(seed);
    }
}

/// Prints one seed's program, both outcomes, and the disassembly
/// (`BCGEN_SEED=n cargo test --test differential debug_seed -- --ignored --nocapture`).
#[test]
#[ignore = "a debugging aid"]
fn debug_seed() {
    let seed: u64 = std::env::var("BCGEN_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let php = std::env::var("BCGEN_REF").is_err();
    let profile = if php {
        Profile::PHP
    } else {
        Profile::REFERENCE
    };
    let (hir, names) = progs::program(seed);
    println!("{}", hir_lang::print(&hir, &names));
    let out = common::compile(&hir, &names, profile);
    println!("{}", bytecode_lang::disassemble(out.module()));
    let r = common::run_reference(&hir, &names, profile, 2_000_000);
    let b = common::run_compiled(&out, 50_000_000);
    for o in [&r.0, &b.0] {
        if let Outcome::Raised {
            node: hir_lang::NodeRef::Expr(e),
            ..
        }
        | Outcome::Thrown {
            node: hir_lang::NodeRef::Expr(e),
            ..
        } = o
        {
            println!(
                "node {e:?}: {:?} at {:?}",
                hir.expr(*e),
                hir.origin(hir_lang::NodeRef::Expr(*e)).span
            );
        }
    }
    println!("reference: {r:?}");
    println!("bvm:       {b:?}");
}
