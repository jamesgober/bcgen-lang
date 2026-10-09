//! PHP key coercion: the compiled `<php_key>` helper against a direct
//! implementation of PHP's canonical-integer-string rule, on random keys.

mod common;

use common::hb::H;
use common::{Outcome, Profile, RV, check};
use proptest::prelude::*;

/// `{ let m = []; m[key] = 1; m }` with the key given as a string, float,
/// bool, or null literal.
fn keyed(key: impl FnOnce(&mut H) -> hir_lang::ExprId) -> RV {
    let mut h = H::new();
    let m = h.local("m");
    let e = h.array(&[]);
    let lm = h.let_(m, Some(e));
    let vm = h.var(m);
    let k = key(&mut h);
    let ix = h.index(vm, k);
    let one = h.int(1);
    let a = h.assign(ix, one);
    let s = h.stmt(a);
    let vm2 = h.var(m);
    let body = h.block(&[lm, s], Some(vm2));
    let (hir, names) = h.finish(&[], Some(body));
    match check(&hir, &names, Profile::PHP) {
        Outcome::Value(RV::Map(entries)) => {
            entries.into_iter().next().map(|e| e.0).unwrap_or(RV::Nil)
        }
        o => panic!("{o:?}"),
    }
}

/// PHP's rule, written out: optional `-`, no leading zero (but `0`), not
/// `-0`, decimal digits only, within `i64`.
fn php_int(s: &str) -> Option<i64> {
    let digits = s.strip_prefix('-').unwrap_or(s);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if digits.len() > 1 && digits.starts_with('0') {
        return None;
    }
    if s == "-0" {
        return None;
    }
    s.parse().ok()
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 400, ..ProptestConfig::default() })]

    #[test]
    fn string_keys_become_integers_exactly_when_canonical(s in "-?[0-9]{0,21}|[-+ 0-9a]{0,4}") {
        let got = keyed(|h| h.str(&s));
        let want = match php_int(&s) {
            Some(i) => RV::Int(i),
            None => RV::Str(s.as_bytes().to_vec()),
        };
        prop_assert_eq!(got, want);
    }

    #[test]
    fn float_keys_truncate(f in -1e20f64..1e20) {
        let got = keyed(|h| h.float(f));
        let want = if f >= 9_223_372_036_854_775_808.0 { i64::MAX } else if f <= -9_223_372_036_854_775_808.0 { i64::MIN } else { f.trunc() as i64 };
        prop_assert_eq!(got, RV::Int(want));
    }
}

#[test]
fn edge_keys() {
    assert_eq!(keyed(|h| h.str("-9223372036854775808")), RV::Int(i64::MIN));
    assert_eq!(
        keyed(|h| h.str("9223372036854775808")),
        RV::Str(b"9223372036854775808".to_vec())
    );
    assert_eq!(keyed(|h| h.str("-0")), RV::Str(b"-0".to_vec()));
    assert_eq!(keyed(|h| h.str("0")), RV::Int(0));
    assert_eq!(keyed(|h| h.float(f64::NAN)), RV::Int(0));
    assert_eq!(keyed(|h| h.boolean(true)), RV::Int(1));
    assert_eq!(keyed(|h| h.nil()), RV::Str(Vec::new()));
}
