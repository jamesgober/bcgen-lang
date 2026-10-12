//! Mox's operators through the intrinsic table (decision D27): a Mox
//! lowering turns `==`, `.`, `**`, `<=>` into named intrinsics;
//! `Intrinsics::mox()` compiles each to an inline fast path where LSB's
//! semantics are PHP's (two ints, two strings, ...) and to a call of the
//! runtime's host function everywhere else. The host functions here are
//! small stand-ins for LexerSketch's runtime that print when they run.
//!
//! The program, in Mox source:
//!
//! ```text
//! [1 == 1, "1e3" == "1000", "a" . "b", "n=" . 5, 2 ** 10, 3 <=> 7]
//! ```
//!
//! Run with `cargo run --example mox_intrinsics`.

use bcgen_lang::{BodyMode, Compiler, Intrinsics, Options};
use bvm_lang::{Host, HostError, Program, Value, Vm};
use bytecode_lang::ErrorKind;
use hir_lang::{Builder, Effects, Expr, ExprId, Intrinsic, Item, ItemKind, List};
use intern_lang::Interner;

fn intrinsic(b: &mut Builder, names: &mut Interner, name: &str, args: &[ExprId]) -> ExprId {
    let sym = names.intern(name);
    let args = b.list(args);
    b.expr(Expr::Intrinsic {
        kind: Intrinsic::Named(sym),
        generic_args: List::EMPTY,
        args,
    })
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut names = Interner::new();
    let mut b = Builder::new();
    let mut es = Vec::new();
    let (one, one2) = (b.int(1), b.int(1));
    es.push(intrinsic(&mut b, &mut names, "mox.loose_eq", &[one, one2]));
    let (x, y) = (b.str_lit("1e3"), b.str_lit("1000"));
    es.push(intrinsic(&mut b, &mut names, "mox.loose_eq", &[x, y]));
    let (a, c) = (b.str_lit("a"), b.str_lit("b"));
    es.push(intrinsic(&mut b, &mut names, "mox.concat", &[a, c]));
    let (n, five) = (b.str_lit("n="), b.int(5));
    es.push(intrinsic(&mut b, &mut names, "mox.concat", &[n, five]));
    let (two, ten) = (b.int(2), b.int(10));
    es.push(intrinsic(&mut b, &mut names, "mox.pow", &[two, ten]));
    let (three, seven) = (b.int(3), b.int(7));
    es.push(intrinsic(
        &mut b,
        &mut names,
        "mox.spaceship",
        &[three, seven],
    ));
    let list = b.list(&es);
    let arr = b.expr(Expr::Array(list));
    let root = b.item(Item::new(
        None,
        ItemKind::Module {
            items: List::EMPTY,
            body: Some(arr),
            effects: Effects::NONE,
        },
    ));
    let hir = b.finish(root)?;

    let opts = Options::new()
        .with_body(BodyMode::Entry)
        .with_intrinsics(Intrinsics::mox());
    let out = Compiler::new(opts).compile(&hir, &names)?;

    // Stand-ins for the runtime: only the operands outside each fast path
    // reach them (`"1e3" == "1000"` and `"n=" . 5` here).
    let mut host = Host::new();
    host.register("mox", "loose_eq", |ctx, args| {
        println!("host: mox.loose_eq (numeric strings compare as numbers)");
        let num = |v: Value| -> Option<f64> {
            std::str::from_utf8(ctx.str_bytes(v)?)
                .ok()?
                .trim()
                .parse()
                .ok()
        };
        match args {
            [l, r] => Ok(Value::Bool(num(*l).is_some() && num(*l) == num(*r))),
            _ => Err(HostError::Raise(ErrorKind::ArgumentError)),
        }
    });
    host.register("mox", "concat", |ctx, args| {
        println!("host: mox.concat (converts to strings)");
        let mut s = Vec::new();
        for &a in args {
            match a {
                Value::Int(i) => s.extend(i.to_string().into_bytes()),
                v => s.extend(ctx.str_bytes(v).unwrap_or(b"")),
            }
        }
        ctx.new_str(&s)
    });
    for f in ["pow", "spaceship"] {
        host.register("mox", f, |_, _| Err(HostError::Raise(ErrorKind::TypeError)));
    }
    let program = Program::load(out.module().clone(), &host)?;
    let mut vm = Vm::new(&program);
    let v = vm.run(out.entry(), &[])?;
    for (_, x) in vm.entries(v).unwrap_or_default() {
        match x {
            Value::Obj(_) => println!(
                "{:?}",
                String::from_utf8_lossy(vm.str_bytes(x).unwrap_or(b""))
            ),
            x => println!("{x}"),
        }
    }
    Ok(())
}
