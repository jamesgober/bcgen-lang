//! Shared test support: a terse HIR builder, the reference interpreter, the
//! random program generator, and running compiled modules on bvm-lang.

#![allow(dead_code)]

pub mod hb;
pub mod progs;
pub mod reference;

use std::sync::{Arc, Mutex};

use bcgen_lang::{ArraySemantics, BodyMode, Compiled, Compiler, KeyCoercion, Options};
use bvm_lang::{Host, HostError, Limits, Program, Value, Vm, VmError};
use bytecode_lang::{ErrorKind, Kind};
use hir_lang::{Hir, NodeRef};
use intern_lang::Interner;

/// A comparable run result.
#[derive(Clone, Debug, PartialEq)]
pub enum RV {
    Nil,
    Bool(bool),
    Int(i64),
    /// Float bits, every NaN one canonical NaN.
    Float(u64),
    Char(char),
    Str(Vec<u8>),
    Map(Vec<(RV, RV)>),
    Func,
    Error(u32),
    Other(u32),
}

impl RV {
    pub fn float(f: f64) -> RV {
        RV::Float(if f.is_nan() {
            f64::NAN.to_bits()
        } else {
            f.to_bits()
        })
    }
}

/// How a run ended.
#[derive(Clone, Debug, PartialEq)]
pub enum Outcome {
    Value(RV),
    Raised {
        code: u32,
        node: NodeRef,
    },
    Thrown {
        value: RV,
        node: NodeRef,
    },
    Trap {
        code: u32,
        node: NodeRef,
    },
    /// The semantics leave the result open; the case says nothing.
    Unspecified,
    /// A budget ran out; the case says nothing.
    Budget,
}

/// The profile both sides run under.
#[derive(Clone, Copy, Debug)]
pub struct Profile {
    pub php_arrays: bool,
    pub php_keys: bool,
    /// Compile for a reference-counting VM (dead reference registers are
    /// cleared); the run stays on the tracing profile, so the comparison
    /// shows the clearing changes no result.
    pub clear: bool,
}

impl Profile {
    pub const PHP: Profile = Profile {
        php_arrays: true,
        php_keys: true,
        clear: false,
    };
    pub const REFERENCE: Profile = Profile {
        php_arrays: false,
        php_keys: false,
        clear: false,
    };
    pub const PHP_CLEAR: Profile = Profile {
        php_arrays: true,
        php_keys: true,
        clear: true,
    };

    pub fn options(self) -> Options {
        Options::new()
            .with_body(BodyMode::Entry)
            .with_arrays(if self.php_arrays {
                ArraySemantics::Php
            } else {
                ArraySemantics::Reference
            })
            .with_keys(if self.php_keys {
                KeyCoercion::Php
            } else {
                KeyCoercion::None
            })
            .with_reference_counting(self.clear)
    }
}

/// The host functions the tests use: `echo` (prints its arguments,
/// concatenated) and `fail` (raises `TypeError`).
pub fn host(out: Arc<Mutex<Vec<String>>>) -> Host {
    let mut h = Host::new();
    let o = out.clone();
    let _ = h.register("host", "echo", move |ctx, args| {
        let mut line = String::new();
        for &a in args {
            line.push_str(&show_host(ctx, a));
        }
        if let Ok(mut v) = o.lock() {
            v.push(line);
        }
        Ok(Value::Nil)
    });
    let _ = h.register("host", "fail", |_, _| {
        Err(HostError::Raise(ErrorKind::TypeError))
    });
    h
}

fn show_host(ctx: &bvm_lang::HostCtx<'_>, v: Value) -> String {
    match v {
        Value::Nil => String::new(),
        Value::Bool(true) => "1".into(),
        Value::Bool(false) => String::new(),
        Value::Int(i) => i.to_string(),
        Value::UInt(u) => u.to_string(),
        Value::Float(f) => format!("{f:?}"),
        Value::F32(f) => format!("{:?}", f64::from(f)),
        Value::Char(c) => c.to_string(),
        Value::Obj(_) => match ctx.kind(v) {
            Kind::Str => String::from_utf8_lossy(ctx.str_bytes(v).unwrap_or(b"")).into_owned(),
            Kind::Map | Kind::Array => "Array".into(),
            Kind::Function => "Closure".into(),
            Kind::Error => format!("E{:04}", ctx.error_code(v).unwrap_or(0)),
            Kind::Iter => "Iterator".into(),
            _ => "?".into(),
        },
        _ => "?".into(),
    }
}

/// A VM value as a comparable result.
pub fn to_rv(vm: &Vm<'_>, v: Value, depth: usize) -> RV {
    match v {
        Value::Nil => RV::Nil,
        Value::Bool(b) => RV::Bool(b),
        Value::Int(i) => RV::Int(i),
        Value::UInt(u) => RV::Int(u as i64),
        Value::Float(f) => RV::float(f),
        Value::F32(f) => RV::float(f64::from(f)),
        Value::Char(c) => RV::Char(c),
        Value::Obj(_) => match vm.kind(v) {
            Kind::Str => RV::Str(vm.str_bytes(v).unwrap_or(b"").to_vec()),
            Kind::Map if depth < 16 => RV::Map(
                vm.entries(v)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|(k, x)| (to_rv(vm, k, depth + 1), to_rv(vm, x, depth + 1)))
                    .collect(),
            ),
            Kind::Function => RV::Func,
            Kind::Error => RV::Error(vm.error_code(v).unwrap_or(0)),
            Kind::Nil => RV::Nil,
            k => RV::Other(u32::from(k.code())),
        },
        _ => RV::Other(99),
    }
}

/// Compiles `hir` under `profile`.
pub fn compile(hir: &Hir, names: &Interner, profile: Profile) -> Compiled {
    match Compiler::new(profile.options()).compile(hir, names) {
        Ok(c) => c,
        Err(e) => panic!("compile error: {e}"),
    }
}

/// Compiles and runs the unit's entry on bvm-lang; the outcome and what
/// `echo` printed.
pub fn run_bvm(hir: &Hir, names: &Interner, profile: Profile, fuel: u64) -> (Outcome, Vec<String>) {
    let out = compile(hir, names, profile);
    run_compiled(&out, fuel)
}

pub fn run_compiled(out: &Compiled, fuel: u64) -> (Outcome, Vec<String>) {
    let printed = Arc::new(Mutex::new(Vec::new()));
    let program = match Program::load(out.module().clone(), &host(printed.clone())) {
        Ok(p) => p,
        Err(e) => panic!(
            "load error: {e}\n{}",
            bytecode_lang::disassemble(out.module())
        ),
    };
    let limits = Limits::new()
        .with_fuel(fuel)
        .with_depth(400)
        .with_memory(256 << 20);
    let mut vm = Vm::with_limits(&program, limits);
    let r = vm.run(out.entry(), &[]);
    let origin = |func: bytecode_lang::FuncId, pc: u32| -> NodeRef {
        match out.origin(func, pc) {
            Some(n) => n,
            None => panic!("no origin for {func} @{pc}"),
        }
    };
    let outcome = match r {
        Ok(v) => Outcome::Value(to_rv(&vm, v, 0)),
        Err(VmError::Raised { kind, func, pc, .. }) => match kind {
            ErrorKind::StackOverflow => Outcome::Budget,
            _ => Outcome::Raised {
                code: kind.code(),
                node: origin(func, pc),
            },
        },
        Err(VmError::Thrown { value, func, pc }) => Outcome::Thrown {
            value: to_rv(&vm, value, 0),
            node: origin(func, pc),
        },
        Err(VmError::Trap { kind, func, pc }) => match kind {
            ErrorKind::OutOfFuel | ErrorKind::OutOfMemory => Outcome::Budget,
            _ => Outcome::Trap {
                code: kind.code(),
                node: origin(func, pc),
            },
        },
        Err(e) => panic!("unexpected VM error: {e:?}"),
    };
    let printed = printed.lock().map(|v| v.clone()).unwrap_or_default();
    (outcome, printed)
}

/// Runs the reference interpreter.
pub fn run_reference(
    hir: &Hir,
    names: &Interner,
    profile: Profile,
    steps: u64,
) -> (Outcome, Vec<String>) {
    let mut it = reference::Interp::new(
        hir,
        names,
        reference::Config {
            php_arrays: profile.php_arrays,
            php_keys: profile.php_keys,
            max_steps: steps,
        },
    );
    let o = it.run_module();
    (o, it.out)
}

/// Runs both and asserts they agree (unless the case is unspecified or ran
/// out of budget on either side). Returns the agreed outcome.
pub fn check(hir: &Hir, names: &Interner, profile: Profile) -> Outcome {
    let (r, rp) = run_reference(hir, names, profile, 2_000_000);
    let (b, bp) = run_bvm(hir, names, profile, 50_000_000);
    if matches!(r, Outcome::Unspecified | Outcome::Budget) || matches!(b, Outcome::Budget) {
        return r;
    }
    assert_eq!(
        b,
        r,
        "bvm (left) and reference (right) disagree\n{}",
        hir_lang::print(hir, names)
    );
    assert_eq!(bp, rp, "printed output differs");
    r
}
