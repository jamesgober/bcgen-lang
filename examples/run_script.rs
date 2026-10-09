//! The Tier-1 path: build a small HIR unit (the shape a lowering produces),
//! compile it with `bcgen_lang::compile`, and run it on bvm-lang with a host
//! function that prints.
//!
//! The program, in Mox-like source:
//!
//! ```text
//! function fib($n) { return $n < 2 ? $n : fib($n - 1) + fib($n - 2); }
//! echo(fib(20));
//! ```
//!
//! Run with `cargo run --example run_script`.

use bvm_lang::{Host, Program, Value, Vm};
use hir_lang::{
    Builder, Def, Effects, Expr, Item, ItemId, ItemKind, Name, Ns, OpKind, Path, Res, Segment,
};
use intern_lang::Interner;

fn path(b: &mut Builder, name: Name, res: Res) -> hir_lang::ExprId {
    let seg = Segment::new(name, b.origin());
    let segs = b.list(&[seg]);
    let p = b.path(Path {
        res,
        ..Path::new(segs, Ns::Value)
    });
    b.expr(Expr::Path(p))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut names = Interner::new();
    let mut b = Builder::new();
    let fib = Name::new(names.intern("fib"));
    // The function is the builder's first item, so calls can name it now.
    let me = ItemId::from_index(0).ok_or("item id")?;
    let fib_res = Res::Def(b.def(Def::Item(me)));

    let (param, n) = b.local_param(Name::new(names.intern("n")));
    let un = b.use_binder(n);
    let two = b.int(2);
    let small = b.op(OpKind::Lt, &[un, two]);
    let un2 = b.use_binder(n);
    let mut calls = Vec::new();
    for k in [1, 2] {
        let callee = path(&mut b, fib, fib_res);
        let un = b.use_binder(n);
        let kk = b.int(k);
        let arg = b.op(OpKind::Sub, &[un, kk]);
        calls.push(b.call(callee, &[arg]));
    }
    let sum = b.op(OpKind::Add, &calls);
    let pick = b.expr(Expr::If {
        cond: small,
        then: un2,
        else_: Some(sum),
    });
    let body = b.block(&[], Some(pick));
    let func = b.func(fib, &[param], body);
    assert_eq!(func, me);

    // The module body: echo(fib(20)).
    let echo = names.intern("echo");
    let callee = path(&mut b, Name::new(echo), Res::Extern(echo));
    let f = path(&mut b, fib, fib_res);
    let twenty = b.int(20);
    let value = b.call(f, &[twenty]);
    let print = b.call(callee, &[value]);
    let items = b.list(&[func]);
    let root = b.item(Item::new(
        None,
        ItemKind::Module {
            items,
            body: Some(print),
            effects: Effects::NONE,
        },
    ));
    let hir = b.finish(root)?;

    let out = bcgen_lang::compile(&hir, &names)?;
    println!("{}", bytecode_lang::disassemble(out.module()));

    let mut host = Host::new();
    host.register("host", "echo", |_, args| {
        for a in args {
            println!("echo: {a}");
        }
        Ok(Value::Nil)
    });
    let program = Program::load(out.module().clone(), &host)?;
    let mut vm = Vm::new(&program);
    vm.run(out.entry(), &[])?;
    Ok(())
}
