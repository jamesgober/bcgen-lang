//! The intrinsic table (D27) end to end: every mapping of
//! `Intrinsics::mox()` compiled and run on bvm-lang with test host functions
//! that implement PHP 8's semantics for scalars (`php` below), and every
//! guarded fast path checked against them.
//!
//! The central property: for every operand combination of a scalar pool,
//! the compiled intrinsic gives exactly what the PHP host function gives,
//! and calls the host exactly for the operands outside its documented
//! domain (`in_domain`, transcribed from the `Fast` documentation). So the
//! inline paths are PHP-exact where they run, and run exactly where the docs
//! say.

mod common;

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use bcgen_lang::{
    Arity, BodyMode, CompileError, Compiler, Fast, Intrinsics, Lowering, LsbOp, Options,
};
use bvm_lang::{Host, HostCtx, HostError, Program, Value, Vm};
use bytecode_lang::{ErrorKind, Kind};
use common::hb::H;
use common::{RV, to_rv};
use hir_lang::{ExprId, Lit, Pat};

// ---------------------------------------------------------------- PHP

/// A PHP scalar (and arrays, for casts).
#[derive(Clone, Debug, PartialEq)]
enum P {
    Null,
    Bool(bool),
    Int(i64),
    Float(f64),
    Str(Vec<u8>),
    Arr(Vec<(P, P)>),
}

type PR = Result<P, ErrorKind>;

mod php {
    use std::cmp::Ordering;

    use super::{P, PR};
    use bytecode_lang::ErrorKind;

    #[derive(Clone, Copy, Debug)]
    pub enum Num {
        I(i64),
        F(f64),
    }

    fn ws(c: u8) -> bool {
        matches!(c, b' ' | b'\t' | b'\n' | b'\r' | 0x0B | 0x0C)
    }

    /// PHP 8's numeric strings: optional surrounding whitespace, a sign,
    /// digits with an optional fraction and exponent.
    pub fn numeric(s: &[u8]) -> Option<Num> {
        let t: Vec<u8> = s.to_vec();
        let start = t.iter().position(|&c| !ws(c))?;
        let end = t.iter().rposition(|&c| !ws(c))? + 1;
        let body = &t[start..end];
        let text = std::str::from_utf8(body).ok()?;
        let b = text.as_bytes();
        let mut i = 0;
        if i < b.len() && (b[i] == b'+' || b[i] == b'-') {
            i += 1;
        }
        let d0 = i;
        while i < b.len() && b[i].is_ascii_digit() {
            i += 1;
        }
        let int_digits = i - d0;
        let mut float = false;
        if i < b.len() && b[i] == b'.' {
            float = true;
            i += 1;
            let f0 = i;
            while i < b.len() && b[i].is_ascii_digit() {
                i += 1;
            }
            if int_digits == 0 && i == f0 {
                return None;
            }
        } else if int_digits == 0 {
            return None;
        }
        if i < b.len() && (b[i] == b'e' || b[i] == b'E') {
            float = true;
            i += 1;
            if i < b.len() && (b[i] == b'+' || b[i] == b'-') {
                i += 1;
            }
            let e0 = i;
            while i < b.len() && b[i].is_ascii_digit() {
                i += 1;
            }
            if i == e0 {
                return None;
            }
        }
        if i != b.len() {
            return None;
        }
        if !float {
            if let Ok(v) = text.parse::<i64>() {
                return Some(Num::I(v));
            }
        }
        text.parse::<f64>().ok().map(Num::F)
    }

    pub fn truthy(v: &P) -> bool {
        match v {
            P::Null => false,
            P::Bool(b) => *b,
            P::Int(i) => *i != 0,
            P::Float(f) => *f != 0.0,
            P::Str(s) => !(s.is_empty() || s == b"0"),
            P::Arr(a) => !a.is_empty(),
        }
    }

    /// PHP's float to string (enough of it for these tests: shortest
    /// round trip, integral values without a fraction).
    pub fn float_str(f: f64) -> String {
        if f.is_nan() {
            "NAN".into()
        } else if f.is_infinite() {
            if f > 0.0 { "INF".into() } else { "-INF".into() }
        } else if f == 0.0 && f.is_sign_negative() {
            "-0".into()
        } else if f == f.trunc() && f.abs() < 1e15 {
            format!("{}", f as i64)
        } else {
            format!("{f:?}")
        }
    }

    pub fn to_str(v: &P) -> Result<Vec<u8>, ErrorKind> {
        Ok(match v {
            P::Null => Vec::new(),
            P::Bool(true) => b"1".to_vec(),
            P::Bool(false) => Vec::new(),
            P::Int(i) => i.to_string().into_bytes(),
            P::Float(f) => float_str(*f).into_bytes(),
            P::Str(s) => s.clone(),
            P::Arr(_) => b"Array".to_vec(),
        })
    }

    fn to_f(n: Num) -> f64 {
        match n {
            Num::I(i) => i as f64,
            Num::F(f) => f,
        }
    }

    fn cmp_num(a: Num, b: Num) -> Option<Ordering> {
        match (a, b) {
            (Num::I(x), Num::I(y)) => Some(x.cmp(&y)),
            _ => to_f(a).partial_cmp(&to_f(b)),
        }
    }

    fn as_num(v: &P) -> Option<Num> {
        match v {
            P::Int(i) => Some(Num::I(*i)),
            P::Float(f) => Some(Num::F(*f)),
            _ => None,
        }
    }

    /// PHP 8's loose comparison; `None` when unordered (NaN).
    pub fn cmp(a: &P, b: &P) -> Option<Ordering> {
        match (a, b) {
            (P::Null, P::Null) => Some(Ordering::Equal),
            (P::Null, P::Str(s)) => Some(b"".as_slice().cmp(s.as_slice())),
            (P::Str(s), P::Null) => Some(s.as_slice().cmp(b"".as_slice())),
            (P::Bool(_) | P::Null, _) | (_, P::Bool(_) | P::Null) => {
                Some(truthy(a).cmp(&truthy(b)))
            }
            (P::Str(x), P::Str(y)) => match (numeric(x), numeric(y)) {
                (Some(m), Some(n)) => cmp_num(m, n),
                _ => Some(x.cmp(y)),
            },
            (P::Str(s), n) | (n, P::Str(s)) if as_num(n).is_some() => {
                let flip = matches!(a, P::Str(_));
                let num = as_num(n)?;
                let o = match numeric(s) {
                    Some(m) => cmp_num(num, m),
                    None => to_str(n).ok().map(|t| t.cmp(s)),
                };
                if flip { o.map(Ordering::reverse) } else { o }
            }
            (P::Arr(x), P::Arr(y)) => Some(x.len().cmp(&y.len())),
            (P::Arr(_), _) => Some(Ordering::Greater),
            (_, P::Arr(_)) => Some(Ordering::Less),
            _ => cmp_num(as_num(a)?, as_num(b)?),
        }
    }

    pub fn loose_eq(a: &P, b: &P) -> bool {
        match (a, b) {
            (P::Arr(x), P::Arr(y)) => {
                x.len() == y.len()
                    && x.iter()
                        .all(|(k, v)| y.iter().any(|(k2, v2)| identical(k, k2) && loose_eq(v, v2)))
            }
            _ => cmp(a, b) == Some(Ordering::Equal),
        }
    }

    pub fn identical(a: &P, b: &P) -> bool {
        match (a, b) {
            (P::Null, P::Null) => true,
            (P::Bool(x), P::Bool(y)) => x == y,
            (P::Int(x), P::Int(y)) => x == y,
            (P::Float(x), P::Float(y)) => x == y,
            (P::Str(x), P::Str(y)) => x == y,
            (P::Arr(x), P::Arr(y)) => {
                x.len() == y.len()
                    && x.iter()
                        .zip(y)
                        .all(|((k, v), (k2, v2))| identical(k, k2) && identical(v, v2))
            }
            _ => false,
        }
    }

    /// PHP's (int) cast.
    pub fn to_int(v: &P) -> i64 {
        match v {
            P::Null | P::Bool(false) => 0,
            P::Bool(true) => 1,
            P::Int(i) => *i,
            P::Float(f) => dval_to_lval(*f),
            P::Str(s) => {
                // The leading numeric prefix.
                let t = String::from_utf8_lossy(s).trim_start().to_string();
                let mut end = 0;
                let b = t.as_bytes();
                if end < b.len() && (b[end] == b'-' || b[end] == b'+') {
                    end += 1;
                }
                while end < b.len()
                    && (b[end].is_ascii_digit()
                        || b[end] == b'.'
                        || b[end] == b'e'
                        || b[end] == b'E')
                {
                    end += 1;
                }
                let mut cut = end;
                while cut > 0 {
                    if let Some(n) = numeric(&b[..cut]) {
                        return match n {
                            Num::I(i) => i,
                            Num::F(f) => dval_to_lval_cap(f),
                        };
                    }
                    cut -= 1;
                }
                0
            }
            P::Arr(a) => i64::from(!a.is_empty()),
        }
    }

    /// PHP 7/8's `zend_dval_to_lval` on 64-bit platforms, transcribed from
    /// `Zend/zend_operators.{h,c}` with its own float arithmetic (an
    /// independent model of the inline bit computation): NaN and the
    /// infinities are 0, `[-2^63, 2^63)` truncates, anything else is taken
    /// modulo 2^64 (`fmod`, then into the signed range).
    pub fn dval_to_lval(d: f64) -> i64 {
        const TWO_63: f64 = 9_223_372_036_854_775_808.0;
        const TWO_64: f64 = 18_446_744_073_709_551_616.0;
        if !d.is_finite() {
            return 0;
        }
        if (-TWO_63..TWO_63).contains(&d) {
            return d as i64;
        }
        // `zend_dval_to_lval_slow`: every step is exact (|d| >= 2^63 makes
        // `d` a multiple of 2^11).
        let mut dmod = d % TWO_64;
        if dmod < 0.0 {
            dmod += TWO_64;
        }
        if dmod >= TWO_63 {
            dmod -= TWO_64;
        }
        dmod as i64
    }

    /// `zend_dval_to_lval_cap`: what a numeric string's float part becomes
    /// (out of range saturates).
    pub fn dval_to_lval_cap(d: f64) -> i64 {
        if d.is_nan() { 0 } else { d as i64 }
    }

    fn arith_num(v: &P) -> Result<Num, ErrorKind> {
        match v {
            P::Null => Ok(Num::I(0)),
            P::Bool(b) => Ok(Num::I(i64::from(*b))),
            P::Int(i) => Ok(Num::I(*i)),
            P::Float(f) => Ok(Num::F(*f)),
            P::Str(s) => numeric(s).ok_or(ErrorKind::TypeError),
            P::Arr(_) => Err(ErrorKind::TypeError),
        }
    }

    pub fn modulo(a: &P, b: &P) -> PR {
        let x = to_int(&num_p(arith_num(a)?));
        let y = to_int(&num_p(arith_num(b)?));
        if y == 0 {
            return Err(ErrorKind::DivByZero);
        }
        Ok(P::Int(if y == -1 { 0 } else { x % y }))
    }

    fn num_p(n: Num) -> P {
        match n {
            Num::I(i) => P::Int(i),
            Num::F(f) => P::Float(f),
        }
    }

    pub fn pow(a: &P, b: &P) -> PR {
        let (x, y) = (arith_num(a)?, arith_num(b)?);
        Ok(match (x, y) {
            (Num::I(b @ -1..=1), Num::I(e)) if e >= 0 => P::Int(match b {
                0 if e == 0 => 1,
                -1 if e % 2 == 1 => -1,
                -1 => 1,
                b => b,
            }),
            (Num::I(b), Num::I(e)) if e >= 0 => {
                match u32::try_from(e)
                    .ok()
                    .and_then(|e| i128::from(b).checked_pow(e))
                {
                    Some(r) => match i64::try_from(r) {
                        Ok(v) => P::Int(v),
                        Err(_) => P::Float(r as f64),
                    },
                    // The exact power does not fit: its nearest float
                    // (OPS `promote`), sign from the exponent's parity.
                    None => {
                        let m = (b.unsigned_abs() as f64).powf(e as f64);
                        P::Float(if b < 0 && e % 2 == 1 { -m } else { m })
                    }
                }
            }
            _ => P::Float(to_f(x).powf(to_f(y))),
        })
    }

    pub fn shift(a: &P, b: &P, left: bool) -> PR {
        let x = to_int(&num_p(arith_num(a)?));
        let n = to_int(&num_p(arith_num(b)?));
        if n < 0 {
            return Err(ErrorKind::ShiftOutOfRange);
        }
        Ok(P::Int(if n >= 64 {
            if left || x >= 0 { 0 } else { -1 }
        } else if left {
            x.wrapping_shl(n as u32)
        } else {
            x >> n
        }))
    }

    pub fn to_number(a: &P) -> PR {
        Ok(num_p(arith_num(a)?))
    }

    pub fn bit_not(a: &P) -> PR {
        match a {
            P::Int(i) => Ok(P::Int(!i)),
            P::Float(f) => Ok(P::Int(!to_int(&P::Float(*f)))),
            P::Str(s) => Ok(P::Str(s.iter().map(|c| !c).collect())),
            _ => Err(ErrorKind::TypeError),
        }
    }

    pub fn to_float(a: &P) -> f64 {
        match a {
            P::Float(f) => *f,
            P::Str(s) => match numeric(s) {
                Some(n) => to_f(n),
                None => to_int(a) as f64,
            },
            other => to_int(other) as f64,
        }
    }
}

/// Runs the PHP semantics of `mox.<name>`.
fn php_call(name: &str, args: &[P]) -> PR {
    use std::cmp::Ordering;
    let a = args.first().cloned().unwrap_or(P::Null);
    let b = args.get(1).cloned().unwrap_or(P::Null);
    Ok(match name {
        "concat" => {
            let mut s = php::to_str(&a)?;
            s.extend(php::to_str(&b)?);
            P::Str(s)
        }
        "concat_n" => {
            let mut s = Vec::new();
            for p in args {
                s.extend(php::to_str(p)?);
            }
            P::Str(s)
        }
        "mod" => return php::modulo(&a, &b),
        "pow" => return php::pow(&a, &b),
        "shl" => return php::shift(&a, &b, true),
        "shr" => return php::shift(&a, &b, false),
        "xor" => P::Bool(php::truthy(&a) ^ php::truthy(&b)),
        "loose_eq" => P::Bool(php::loose_eq(&a, &b)),
        "loose_ne" => P::Bool(!php::loose_eq(&a, &b)),
        "identical" => P::Bool(php::identical(&a, &b)),
        "not_identical" => P::Bool(!php::identical(&a, &b)),
        "lt" => P::Bool(php::cmp(&a, &b) == Some(Ordering::Less)),
        "le" => P::Bool(matches!(
            php::cmp(&a, &b),
            Some(Ordering::Less | Ordering::Equal)
        )),
        "gt" => P::Bool(php::cmp(&b, &a) == Some(Ordering::Less)),
        "ge" => P::Bool(matches!(
            php::cmp(&b, &a),
            Some(Ordering::Less | Ordering::Equal)
        )),
        "spaceship" => P::Int(match php::cmp(&a, &b) {
            Some(Ordering::Less) => -1,
            Some(Ordering::Equal) => 0,
            _ => 1,
        }),
        "to_number" => return php::to_number(&a),
        "bit_not" => return php::bit_not(&a),
        "cast_int" => P::Int(php::to_int(&a)),
        "cast_float" => P::Float(php::to_float(&a)),
        "cast_string" => P::Str(php::to_str(&a)?),
        "cast_bool" => P::Bool(php::truthy(&a)),
        "cast_array" => match a {
            P::Arr(_) => a,
            P::Null => P::Arr(Vec::new()),
            v => P::Arr(vec![(P::Int(0), v)]),
        },
        // Objects are the runtime's: markers the tests recognize.
        "cast_object" => P::Str(b"object".to_vec()),
        "clone" => a,
        "instanceof" => P::Bool(false),
        _ => return Err(ErrorKind::TypeError),
    })
}

fn from_vm(ctx: &HostCtx<'_>, v: Value) -> P {
    match v {
        Value::Nil => P::Null,
        Value::Bool(b) => P::Bool(b),
        Value::Int(i) => P::Int(i),
        Value::Float(f) => P::Float(f),
        _ => match ctx.kind(v) {
            Kind::Str => P::Str(ctx.str_bytes(v).unwrap_or(b"").to_vec()),
            Kind::Map | Kind::Array => P::Arr(
                ctx.entries(v)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|(k, x)| (from_vm(ctx, k), from_vm(ctx, x)))
                    .collect(),
            ),
            _ => P::Null,
        },
    }
}

fn to_vm(ctx: &mut HostCtx<'_>, p: &P) -> Result<Value, HostError> {
    Ok(match p {
        P::Null => Value::Nil,
        P::Bool(b) => Value::Bool(*b),
        P::Int(i) => Value::Int(*i),
        P::Float(f) => Value::Float(*f),
        P::Str(s) => ctx.new_str(s)?,
        P::Arr(entries) => {
            let mut es = Vec::new();
            for (k, v) in entries {
                es.push((to_vm(ctx, k)?, to_vm(ctx, v)?));
            }
            ctx.new_map(&es)?
        }
    })
}

/// The comparable form of a PHP result.
fn rv(p: &PR) -> RV {
    match p {
        Ok(P::Null) => RV::Nil,
        Ok(P::Bool(b)) => RV::Bool(*b),
        Ok(P::Int(i)) => RV::Int(*i),
        Ok(P::Float(f)) => RV::float(*f),
        Ok(P::Str(s)) => RV::Str(s.clone()),
        Ok(P::Arr(es)) => RV::Map(
            es.iter()
                .map(|(k, v)| (rv(&Ok(k.clone())), rv(&Ok(v.clone()))))
                .collect(),
        ),
        Err(k) => RV::Error(k.code()),
    }
}

type Calls = Arc<Mutex<BTreeMap<String, u64>>>;

/// A host with every `mox.*` function, counting calls.
fn mox_host(calls: Calls) -> Host {
    let mut host = Host::new();
    for (name, def) in Intrinsics::mox().iter() {
        let Some((module, func)) = def.lowering().host() else {
            continue;
        };
        let _ = name;
        let func = func.to_string();
        let calls = calls.clone();
        let _ = host.register(module, &func.clone(), move |ctx, args| {
            if let Ok(mut c) = calls.lock() {
                *c.entry(func.clone()).or_insert(0) += 1;
            }
            let ps: Vec<P> = args.iter().map(|&v| from_vm(ctx, v)).collect();
            match php_call(&func, &ps) {
                Ok(p) => to_vm(ctx, &p),
                Err(k) => Err(HostError::Raise(k)),
            }
        });
    }
    host
}

fn lit(h: &mut H, p: &P) -> ExprId {
    match p {
        P::Null => h.nil(),
        P::Bool(b) => h.boolean(*b),
        P::Int(i) => h.int(*i),
        P::Float(f) => h.float(*f),
        P::Str(s) => h.str(std::str::from_utf8(s).unwrap_or("")),
        P::Arr(es) => {
            let entries: Vec<(Option<ExprId>, ExprId)> = es
                .iter()
                .map(|(k, v)| {
                    let k = lit(h, k);
                    let v = lit(h, v);
                    (Some(k), v)
                })
                .collect();
            h.map(&entries)
        }
    }
}

/// `try { e } catch (x) { x }`: an error becomes its error value.
fn guarded(h: &mut H, e: ExprId) -> ExprId {
    let x = h.local("x");
    let px = h.pbind(x);
    let vx = h.var(x);
    let arm = h.arm(px, None, vx);
    h.try_(e, &[arm], None)
}

/// Evaluates `mox.<name>(args)` for every argument list, each guarded;
/// returns the results and the host calls made.
fn evaluate(name: &str, cases: &[Vec<P>]) -> (Vec<RV>, Calls) {
    let mut h = H::new();
    let full = format!("mox.{name}");
    let mut es = Vec::new();
    for args in cases {
        let a: Vec<ExprId> = args.iter().map(|p| lit(&mut h, p)).collect();
        let e = h.intrinsic(&full, &a);
        es.push(guarded(&mut h, e));
    }
    let out = h.array(&es);
    let (hir, names) = h.finish(&[], Some(out));
    let opts = Options::new()
        .with_body(BodyMode::Entry)
        .with_intrinsics(Intrinsics::mox());
    let out = Compiler::new(opts)
        .compile(&hir, &names)
        .unwrap_or_else(|e| panic!("{name}: {e}"));
    let calls: Calls = Arc::new(Mutex::new(BTreeMap::new()));
    let program = Program::load(out.module().clone(), &mox_host(calls.clone()))
        .unwrap_or_else(|e| panic!("load: {e}"));
    let mut vm = Vm::new(&program);
    let v = vm
        .run(out.entry(), &[])
        .unwrap_or_else(|e| panic!("{name}: {e}"));
    let RV::Map(results) = to_rv(&vm, v, 0) else {
        panic!("not an array");
    };
    (results.into_iter().map(|(_, r)| r).collect(), calls)
}

/// The operands where the fast path runs, as `Fast` documents them.
fn in_domain(f: Fast, args: &[P]) -> bool {
    use P::*;
    let scalar4 = |p: &P| matches!(p, Null | Bool(_) | Int(_) | Float(_));
    let a = args.first().unwrap_or(&Null);
    let b = args.get(1).unwrap_or(&Null);
    match f {
        Fast::Concat => matches!((a, b), (Str(_), Str(_))),
        Fast::ConcatN => args.iter().all(|p| matches!(p, Str(_))),
        Fast::IntRem | Fast::IntShl | Fast::IntShr | Fast::IntSpaceship => {
            matches!((a, b), (Int(_), Int(_)))
        }
        Fast::NumPow => matches!(a, Int(_) | Float(_)) && matches!(b, Int(_) | Float(_)),
        Fast::ScalarXor => scalar4(a) && scalar4(b),
        Fast::LooseEq | Fast::LooseNe => match (a, b) {
            (Str(x), Str(y)) => x == y,
            _ => scalar4(a) && std::mem::discriminant(a) == std::mem::discriminant(b),
        },
        Fast::StrictEq | Fast::StrictNe => {
            (scalar4(a) || matches!(a, Str(_))) && (scalar4(b) || matches!(b, Str(_)))
        }
        Fast::Lt | Fast::Le | Fast::Gt | Fast::Ge => {
            matches!((a, b), (Int(_), Int(_)) | (Float(_), Float(_)))
        }
        Fast::NumIdentity => matches!(a, Int(_) | Float(_)),
        Fast::IntBitNot => matches!(a, Int(_)),
        Fast::ToInt => matches!(a, Int(_) | Float(_) | Bool(_) | Null),
        Fast::ToFloat => matches!(a, Float(_) | Int(_) | Bool(_) | Null),
        Fast::ToStr => matches!(a, Str(_)),
        Fast::ToBool => scalar4(a),
        Fast::ToArray => matches!(a, Arr(_)),
        _ => false,
    }
}

fn pool() -> Vec<P> {
    let mut v = vec![P::Null, P::Bool(false), P::Bool(true)];
    for i in [0, 1, -1, 2, 7, -7, 64, 100, i64::MAX, i64::MIN, 1 << 53] {
        v.push(P::Int(i));
    }
    for f in [
        0.0,
        -0.0,
        1.0,
        1.5,
        -2.5,
        2.0,
        0.5,
        1e300,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        9007199254740993.0,
        1e19,
        -1e19,
        9_223_372_036_854_775_808.0,
        -9_223_372_036_854_775_808.0,
        18_446_744_073_709_551_616.0,
    ] {
        v.push(P::Float(f));
    }
    for s in [
        "",
        "0",
        "1",
        "1.0",
        " 1",
        "1e3",
        "1000",
        "abc",
        "abd",
        "-7",
        "0x1A",
        "9007199254740993",
    ] {
        v.push(P::Str(s.as_bytes().to_vec()));
    }
    v
}

/// Whether two results agree: exactly, or (a float `pow`, where the VM's
/// shared `ls_pow` and the platform's `powf` may differ in the last bit)
/// within one unit in the last place.
fn agree(name: &str, got: &RV, want: &RV) -> bool {
    match (got, want) {
        (RV::Float(x), RV::Float(y)) if name == "pow" => {
            let (x, y) = (f64::from_bits(*x), f64::from_bits(*y));
            x.to_bits() == y.to_bits()
                || (x.is_finite()
                    && y.is_finite()
                    && (x.to_bits() as i64 - y.to_bits() as i64).abs() <= 1)
        }
        _ => got == want,
    }
}

fn check_fast(name: &str, fast: Fast, cases: Vec<Vec<P>>) {
    let (got, calls) = evaluate(name, &cases);
    assert_eq!(got.len(), cases.len());
    let mut outside = 0u64;
    for (args, g) in cases.iter().zip(&got) {
        let want = rv(&php_call(name, args));
        assert!(
            agree(name, g, &want),
            "mox.{name}({args:?}): compiled {g:?}, PHP {want:?}"
        );
        if !in_domain(fast, args) {
            outside += 1;
        }
    }
    let called = calls
        .lock()
        .map(|c| c.get(name).copied().unwrap_or(0))
        .unwrap_or(0);
    assert_eq!(
        called, outside,
        "mox.{name}: host calls outside the fast domain"
    );
}

#[test]
fn every_binary_fast_path_is_php_exact_on_its_domain() {
    let pool = pool();
    let pairs: Vec<Vec<P>> = pool
        .iter()
        .flat_map(|a| pool.iter().map(move |b| vec![a.clone(), b.clone()]))
        .collect();
    for (name, fast) in [
        ("concat", Fast::Concat),
        ("mod", Fast::IntRem),
        ("pow", Fast::NumPow),
        ("shl", Fast::IntShl),
        ("shr", Fast::IntShr),
        ("xor", Fast::ScalarXor),
        ("loose_eq", Fast::LooseEq),
        ("loose_ne", Fast::LooseNe),
        ("identical", Fast::StrictEq),
        ("not_identical", Fast::StrictNe),
        ("lt", Fast::Lt),
        ("le", Fast::Le),
        ("gt", Fast::Gt),
        ("ge", Fast::Ge),
        ("spaceship", Fast::IntSpaceship),
    ] {
        check_fast(name, fast, pairs.clone());
    }
}

#[test]
fn every_unary_fast_path_is_php_exact_on_its_domain() {
    let mut pool = pool();
    pool.push(P::Arr(vec![(P::Int(0), P::Int(1))]));
    pool.push(P::Arr(Vec::new()));
    let singles: Vec<Vec<P>> = pool.iter().map(|p| vec![p.clone()]).collect();
    for (name, fast) in [
        ("to_number", Fast::NumIdentity),
        ("bit_not", Fast::IntBitNot),
        ("cast_int", Fast::ToInt),
        ("cast_float", Fast::ToFloat),
        ("cast_string", Fast::ToStr),
        ("cast_bool", Fast::ToBool),
        ("cast_array", Fast::ToArray),
    ] {
        check_fast(name, fast, singles.clone());
    }
}

#[test]
fn concat_n_takes_any_number_of_parts() {
    let pool = pool();
    let mut cases: Vec<Vec<P>> = vec![Vec::new()];
    for n in 1..=4usize {
        for start in (0..pool.len()).step_by(3) {
            cases.push(
                (0..n)
                    .map(|i| pool[(start + i * 7) % pool.len()].clone())
                    .collect(),
            );
        }
    }
    // All strings: the fast path.
    cases.push(vec![
        P::Str(b"a".to_vec()),
        P::Str(b"".to_vec()),
        P::Str(b"bc".to_vec()),
    ]);
    check_fast("concat_n", Fast::ConcatN, cases);
}

#[test]
fn host_only_intrinsics_always_call_the_host() {
    for (name, args) in [
        ("clone", vec![P::Int(3)]),
        ("cast_object", vec![P::Null]),
        ("instanceof", vec![P::Int(1), P::Str(b"Foo".to_vec())]),
    ] {
        let (got, calls) = evaluate(name, std::slice::from_ref(&args));
        assert_eq!(got, vec![rv(&php_call(name, &args))]);
        assert_eq!(
            calls.lock().map(|c| c.get(name).copied()).ok().flatten(),
            Some(1)
        );
    }
}

/// Known PHP 8 results, through the whole mapping (fast path or host).
#[test]
fn php_results_through_the_mox_mapping() {
    let s = |x: &str| P::Str(x.as_bytes().to_vec());
    for (name, args, want) in [
        ("loose_eq", vec![s("1e3"), s("1000")], P::Bool(true)),
        ("loose_eq", vec![s("abc"), P::Int(0)], P::Bool(false)),
        ("loose_eq", vec![P::Null, P::Bool(false)], P::Bool(true)),
        ("loose_eq", vec![P::Int(1), P::Float(1.0)], P::Bool(true)),
        ("identical", vec![P::Int(1), P::Float(1.0)], P::Bool(false)),
        ("identical", vec![s("1"), P::Int(1)], P::Bool(false)),
        ("lt", vec![s("abc"), s("abd")], P::Bool(true)),
        ("lt", vec![s("10"), s("9")], P::Bool(false)),
        ("spaceship", vec![P::Int(7), P::Int(3)], P::Int(1)),
        ("concat", vec![s("n="), P::Int(5)], s("n=5")),
        ("mod", vec![P::Int(-7), P::Int(3)], P::Int(-1)),
        ("mod", vec![s("5"), P::Int(3)], P::Int(2)),
        ("mod", vec![P::Float(7.9), P::Int(2)], P::Int(1)),
        ("pow", vec![P::Int(2), P::Int(-1)], P::Float(0.5)),
        (
            "pow",
            vec![P::Int(2), P::Int(64)],
            P::Float(18446744073709551616.0),
        ),
        ("shl", vec![P::Int(1), P::Int(64)], P::Int(0)),
        ("shr", vec![P::Int(-8), P::Int(100)], P::Int(-1)),
        ("xor", vec![P::Int(1), s("0")], P::Bool(true)),
        ("cast_int", vec![s("12abc")], P::Int(12)),
        ("cast_bool", vec![s("0")], P::Bool(false)),
        ("bit_not", vec![P::Int(0)], P::Int(-1)),
    ] {
        let (got, _) = evaluate(name, std::slice::from_ref(&args));
        assert_eq!(got, vec![rv(&Ok(want))], "mox.{name}({args:?})");
    }
    // Errors keep their kind: modulo by zero, a negative shift.
    let (got, _) = evaluate("mod", &[vec![P::Int(1), P::Int(0)]]);
    assert_eq!(got, vec![RV::Error(ErrorKind::DivByZero.code())]);
    let (got, _) = evaluate("shl", &[vec![P::Int(1), P::Int(-1)]]);
    assert_eq!(got, vec![RV::Error(ErrorKind::ShiftOutOfRange.code())]);
}

/// ISSUES P41: `(int)` of a float is PHP 7/8's `zend_dval_to_lval` on
/// 64-bit platforms, inline: truncation in range, 0 for NaN and the
/// infinities, modulo 2^64 outside. Expected values are PHP's (and the
/// independent `fmod` transcription agrees on each).
#[test]
fn float_to_int_wraps_modulo_two_to_the_64_like_php() {
    const VECTORS: [(f64, i64); 22] = [
        (0.0, 0),
        (-0.0, 0),
        (1.9, 1),
        (-1.9, -1),
        (9_007_199_254_740_993.0, 9_007_199_254_740_992),
        (9_223_372_036_854_774_784.0, 9_223_372_036_854_774_784),
        (-9_223_372_036_854_775_808.0, i64::MIN),
        (9_223_372_036_854_775_808.0, i64::MIN),
        (9_223_372_036_854_777_856.0, -9_223_372_036_854_773_760),
        (-9_223_372_036_854_777_856.0, 9_223_372_036_854_773_760),
        (1e19, -8_446_744_073_709_551_616),
        (-1e19, 8_446_744_073_709_551_616),
        (1.5e19, -3_446_744_073_709_551_616),
        (18_446_744_073_709_551_616.0, 0),
        (18_446_744_073_709_555_712.0, 4096),
        (-18_446_744_073_709_555_712.0, -4096),
        (1e20, 7_766_279_631_452_241_920),
        (-1e20, -7_766_279_631_452_241_920),
        (1e300, 0),
        (f64::INFINITY, 0),
        (f64::NEG_INFINITY, 0),
        (f64::NAN, 0),
    ];
    let cases: Vec<Vec<P>> = VECTORS.iter().map(|&(f, _)| vec![P::Float(f)]).collect();
    let (got, calls) = evaluate("cast_int", &cases);
    for ((f, want), g) in VECTORS.iter().zip(&got) {
        assert_eq!(*g, RV::Int(*want), "(int){f:e}");
        assert_eq!(php::dval_to_lval(*f), *want, "model (int){f:e}");
    }
    // All inline: the host is never called for a float.
    let called = calls
        .lock()
        .map(|c| c.get("cast_int").copied().unwrap_or(0))
        .unwrap_or(0);
    assert_eq!(called, 0);
}

/// Random floats over the whole bit space against the `fmod` model.
#[test]
fn float_to_int_matches_the_model_on_random_bits() {
    let mut x = 0x9E37_79B9_7F4A_7C15u64;
    let mut cases: Vec<Vec<P>> = Vec::new();
    for _ in 0..4_000 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        cases.push(vec![P::Float(f64::from_bits(x))]);
    }
    let (got, _) = evaluate("cast_int", &cases);
    for (c, g) in cases.iter().zip(&got) {
        let P::Float(f) = c[0] else { unreachable!() };
        assert_eq!(*g, RV::Int(php::dval_to_lval(f)), "(int){f:e}");
    }
}

#[test]
fn the_core_coroutine_and_iteration_intrinsics_are_lsb_sequences() {
    let t = Intrinsics::core();
    for (name, op) in [
        ("resume", LsbOp::Resume),
        ("resume_throw", LsbOp::ResumeThrow),
        ("coro_close", LsbOp::CoroClose),
        ("coro_key", LsbOp::CoroKey),
        ("coro_result", LsbOp::CoroResult),
        ("coro_status", LsbOp::CoroStatus),
        ("iter", LsbOp::Iter),
    ] {
        assert_eq!(
            t.get(name).map(|d| d.lowering().clone()),
            Some(Lowering::Lsb(op))
        );
    }
}

#[test]
fn unknown_intrinsics_and_bad_arity_are_precise_errors() {
    let mut h = H::new();
    let one = h.int(1);
    let e = h.intrinsic("mox.nope", &[one]);
    let (hir, names) = h.finish(&[], Some(e));
    let opts = Options::new().with_intrinsics(Intrinsics::mox());
    let err = Compiler::new(opts.clone())
        .compile(&hir, &names)
        .unwrap_err();
    assert!(
        matches!(err, CompileError::UnknownIntrinsic { .. }),
        "{err:?}"
    );
    assert_eq!(err.node(), Some(hir_lang::NodeRef::Expr(e)));
    let mut h = H::new();
    let one = h.int(1);
    let e = h.intrinsic("mox.loose_eq", &[one]);
    let (hir, names) = h.finish(&[], Some(e));
    let err = Compiler::new(opts).compile(&hir, &names).unwrap_err();
    assert!(
        matches!(err, CompileError::IntrinsicArity { arity, found: 1, .. } if arity == Arity::exact(2)),
        "{err:?}"
    );
    assert!(err.to_string().contains("takes 2 operands, not 1"));
    // 256 parts: more than an import window carries.
    let mut h = H::new();
    let parts: Vec<ExprId> = (0..256).map(|_| h.str("x")).collect();
    let e = h.intrinsic("mox.concat_n", &parts);
    let (hir, names) = h.finish(&[], Some(e));
    let err = Compiler::new(Options::new().with_intrinsics(Intrinsics::mox()))
        .compile(&hir, &names)
        .unwrap_err();
    assert!(
        matches!(err, CompileError::IntrinsicArity { found: 256, .. }),
        "{err:?}"
    );
}

#[test]
fn a_custom_table_maps_names_to_any_lowering() {
    // `lang.eq` as a fast path over the host's `rt.eq`, `lang.len` as LSB.
    let table = Intrinsics::new()
        .with_fast("lang.eq", Fast::StrictEq, "mox", "identical")
        .with_lsb("lang.len", LsbOp::Len)
        .with_host("lang.dup", Arity::exact(1), "mox", "clone");
    let mut h = H::new();
    let (a, b) = (h.int(3), h.int(3));
    let eq = h.intrinsic("lang.eq", &[a, b]);
    let s = h.str("abcd");
    let len = h.intrinsic("lang.len", &[s]);
    let x = h.int(9);
    let dup = h.intrinsic("lang.dup", &[x]);
    let out = h.array(&[eq, len, dup]);
    let (hir, names) = h.finish(&[], Some(out));
    let compiled = Compiler::new(
        Options::new()
            .with_body(BodyMode::Entry)
            .with_intrinsics(table),
    )
    .compile(&hir, &names)
    .unwrap_or_else(|e| panic!("{e}"));
    let calls: Calls = Arc::new(Mutex::new(BTreeMap::new()));
    let program = Program::load(compiled.module().clone(), &mox_host(calls.clone()))
        .unwrap_or_else(|e| panic!("{e}"));
    let mut vm = Vm::new(&program);
    let v = vm
        .run(compiled.entry(), &[])
        .unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(
        to_rv(&vm, v, 0),
        RV::Map(vec![
            (RV::Int(0), RV::Bool(true)),
            (RV::Int(1), RV::Int(4)),
            (RV::Int(2), RV::Int(9)),
        ])
    );
    let c = calls.lock().map(|c| c.clone()).unwrap_or_default();
    assert_eq!(c.get("identical"), None);
    assert_eq!(c.get("clone"), Some(&1));
}

#[test]
fn the_mox_foreach_template_compiles_through_the_table() {
    // Pattern from HIR §9.4 with the table's `iter`: unchanged by the table.
    let mut h = H::new();
    let one = h.int(1);
    let two = h.int(2);
    let coll = h.array(&[one, two]);
    let it = h.local("it");
    let iter = h.intrinsic("iter", &[coll]);
    let lit_ = h.let_(it, Some(iter));
    let vit = h.var(it);
    let next = h.intrinsic("iter_next", &[vit]);
    let null = h.pat(Pat::Lit(Lit::Null));
    let brk = h.brk(None, None);
    let a1 = h.arm(null, None, brk);
    let w = h.pat(Pat::Wild);
    let unit = h.nil();
    let a2 = h.arm(w, None, unit);
    let m = h.match_(next, &[a1, a2]);
    let lp = h.loop_(None, m, None);
    let body = h.block(&[lit_], Some(lp));
    let (hir, names) = h.finish(&[], Some(body));
    let opts = Options::new().with_intrinsics(Intrinsics::mox());
    assert!(Compiler::new(opts).compile(&hir, &names).is_ok());
}
