//! Classes (0.4): a HIR unit with two classes, compiled with the Mox
//! intrinsic table (whose `mox.new` is a class operation) and run on
//! bvm-lang. It shows a constructor, an inherited method calling an
//! overridden one through `$this`, a default property value, `instanceof`,
//! and a visibility violation raised as `TypeError` with PHP's message.
//!
//! The program, in Mox source:
//!
//! ```text
//! class Shape {
//!     protected $name;
//!     function __construct($name) { $this->name = $name; }
//!     function describe() { echo($this->name, $this->area()); }
//!     function area() { return 0; }
//! }
//! class Square extends Shape {
//!     public $side = 3;
//!     function area() { return $this->side * $this->side; }
//! }
//! $s = new Square("square");
//! $s->describe();
//! echo($s instanceof Shape);
//! $s->name;            // Cannot access protected property Shape::$name
//! ```
//!
//! Run with `cargo run --example classes`.

use bcgen_lang::{BodyMode, Compiler, Intrinsics, Options};
use bvm_lang::{Host, Program, Value, Vm, VmError};
use hir_lang::{
    Binder, BinderId, BinderKind, Builder, ClassDef, Def, Effects, Expr, ExprId, FieldDef, FnDef,
    Ident, Intrinsic, Item, ItemId, ItemKind, List, Name, Ns, OpKind, Param, ParamId, ParamKind,
    Path, Res, Segment, Span, Ty, Vis,
};
use intern_lang::Interner;

struct Unit {
    b: Builder,
    names: Interner,
}

impl Unit {
    fn name(&mut self, s: &str) -> Name {
        Name::new(self.names.intern(s))
    }

    fn path(&mut self, s: &str, ns: Ns, res: Res) -> hir_lang::PathId {
        let seg = Segment::new(self.name(s), self.b.origin());
        let segs = self.b.list(&[seg]);
        self.b.path(Path {
            res,
            ..Path::new(segs, ns)
        })
    }

    /// A path naming a unit item (a class, in value or type position).
    fn item_path(&mut self, s: &str, item: ItemId, ns: Ns) -> hir_lang::PathId {
        let d = self.b.def(Def::Item(item));
        self.path(s, ns, Res::Def(d))
    }

    /// A call of a host function (`echo`) or of a Mox operation (`mox.new`).
    fn call_extern(&mut self, s: &str, args: &[ExprId]) -> ExprId {
        let sym = self.names.intern(s);
        let p = self.path(s, Ns::Value, Res::Extern(sym));
        let callee = self.b.expr(Expr::Path(p));
        self.b.call(callee, args)
    }

    fn param(&mut self, s: &str, kind: ParamKind) -> (ParamId, BinderId) {
        let n = self.name(s);
        let binder = self
            .b
            .binder(Binder::new(n, BinderKind::Param).with_mutable(true));
        let pat = self.b.bind(binder);
        let p = self.b.param(Param {
            kind,
            ..Param::new(pat)
        });
        (p, binder)
    }

    fn field(&mut self, base: ExprId, s: &str) -> ExprId {
        let sym = self.names.intern(s);
        self.b.expr(Expr::Field {
            base,
            member: hir_lang::Member::Named(sym),
            span: Span::empty(0),
        })
    }

    /// `$this->prop`.
    fn this_field(&mut self, this: BinderId, s: &str) -> ExprId {
        let t = self.b.use_binder(this);
        self.field(t, s)
    }

    fn method_call(&mut self, receiver: ExprId, s: &str) -> ExprId {
        let method = Ident::new(self.names.intern(s), Span::empty(0));
        self.b.expr(Expr::MethodCall {
            receiver,
            method,
            generic_args: List::EMPTY,
            args: List::EMPTY,
        })
    }

    fn method(&mut self, s: &str, params: &[ParamId], body: ExprId) -> ItemId {
        let n = self.name(s);
        let params = self.b.list(params);
        self.b.item(
            Item::new(
                Some(n),
                ItemKind::Fn(FnDef {
                    params,
                    body: Some(body),
                    effects: Effects::THROWS,
                    ..FnDef::default()
                }),
            )
            .with_vis(Vis::Public),
        )
    }

    fn prop(&mut self, s: &str, vis: Vis, default: Option<ExprId>) -> hir_lang::FieldId {
        let name = Some(Ident::new(self.names.intern(s), Span::empty(0)));
        self.b.field(FieldDef {
            name,
            vis,
            ty: None,
            default,
        })
    }

    fn class(
        &mut self,
        s: &str,
        base: Option<(&str, ItemId)>,
        fields: &[hir_lang::FieldId],
        items: &[ItemId],
    ) -> ItemId {
        let bases = match base {
            Some((bs, bi)) => {
                let p = self.item_path(bs, bi, Ns::Type);
                let t = self.b.ty(Ty::Path(p));
                self.b.list(&[t])
            }
            None => List::EMPTY,
        };
        let n = self.name(s);
        let def = ClassDef {
            bases,
            fields: self.b.list(fields),
            items: self.b.list(items),
            ..ClassDef::default()
        };
        self.b
            .item(Item::new(Some(n), ItemKind::Class(def)).with_vis(Vis::Public))
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut u = Unit {
        b: Builder::new(),
        names: Interner::new(),
    };

    // class Shape
    let (this, me) = u.param("this", ParamKind::Receiver);
    let (pn, n) = u.param("name", ParamKind::Normal);
    let target = u.this_field(me, "name");
    let value = u.b.use_binder(n);
    let set = u.b.expr(Expr::Assign {
        target,
        op: None,
        value,
    });
    let body = u.b.block(&[], Some(set));
    let ctor = u.method("__construct", &[this, pn], body);
    let (this, me) = u.param("this", ParamKind::Receiver);
    let name = u.this_field(me, "name");
    let t = u.b.use_binder(me);
    let area = u.method_call(t, "area");
    let echo = u.call_extern("echo", &[name, area]);
    let body = u.b.block(&[], Some(echo));
    let describe = u.method("describe", &[this], body);
    let (this, _) = u.param("this", ParamKind::Receiver);
    let zero = u.b.int(0);
    let area0 = u.method("area", &[this], zero);
    let name_prop = u.prop("name", Vis::Protected, None);
    let shape = u.class("Shape", None, &[name_prop], &[ctor, describe, area0]);

    // class Square extends Shape
    let (this, me) = u.param("this", ParamKind::Receiver);
    let a = u.this_field(me, "side");
    let b = u.this_field(me, "side");
    let product = u.b.op(OpKind::Mul, &[a, b]);
    let area1 = u.method("area", &[this], product);
    let three = u.b.int(3);
    let side = u.prop("side", Vis::Public, Some(three));
    let square = u.class("Square", Some(("Shape", shape)), &[side], &[area1]);

    // The module body.
    let sn = u.name("s");
    let s =
        u.b.binder(Binder::new(sn, BinderKind::Local).with_mutable(true));
    let class = u.item_path("Square", square, Ns::Value);
    let class = u.b.expr(Expr::Path(class));
    let label = u.b.str_lit("square");
    let obj = u.call_extern("mox.new", &[class, label]);
    let ps = u.b.bind(s);
    let let_s = u.b.let_stmt(ps, Some(obj));
    let vs = u.b.use_binder(s);
    let describe = u.method_call(vs, "describe");
    let st1 = u.b.expr_stmt(describe);
    let vs = u.b.use_binder(s);
    let shape_ref = u.item_path("Shape", shape, Ns::Value);
    let shape_ref = u.b.expr(Expr::Path(shape_ref));
    let sym = u.names.intern("mox.instanceof");
    let args = u.b.list(&[vs, shape_ref]);
    let test = u.b.expr(Expr::Intrinsic {
        kind: Intrinsic::Named(sym),
        generic_args: List::EMPTY,
        args,
    });
    let echo = u.call_extern("echo", &[test]);
    let st2 = u.b.expr_stmt(echo);
    let vs = u.b.use_binder(s);
    let denied = u.field(vs, "name");
    let body = u.b.block(&[let_s, st1, st2], Some(denied));
    let items = u.b.list(&[shape, square]);
    let root = u.b.item(Item::new(
        None,
        ItemKind::Module {
            items,
            body: Some(body),
            effects: Effects::THROWS,
        },
    ));
    let hir = u.b.finish(root)?;

    let opts = Options::new()
        .with_body(BodyMode::Entry)
        .with_intrinsics(Intrinsics::mox());
    let out = Compiler::new(opts).compile(&hir, &u.names)?;
    println!(
        "Square's struct type: {:?}",
        out.class_type(square).map(|t| t.index())
    );

    let mut host = Host::new();
    host.register("host", "echo", |ctx, args| {
        let parts: Vec<String> = args
            .iter()
            .map(|&a| match ctx.str_bytes(a) {
                Some(b) => String::from_utf8_lossy(b).into_owned(),
                None => a.to_string(),
            })
            .collect();
        println!("echo: {}", parts.join(" "));
        Ok(Value::Nil)
    });
    // The Mox runtime's slow paths (not reached by this program).
    for (_, def) in Intrinsics::mox().iter() {
        if let Some((m, f)) = def.lowering().host() {
            let _ = host.register(m, f, |_, _| Ok(Value::Nil));
        }
    }
    let entry = out.entry();
    let program = Program::load(out.into_module(), &host)?;
    let mut vm = Vm::new(&program);
    match vm.run(entry, &[]) {
        Err(VmError::Raised { kind, payload, .. }) => println!(
            "raised {kind:?}: {}",
            String::from_utf8_lossy(vm.str_bytes(payload).unwrap_or(b""))
        ),
        other => println!("unexpected: {other:?}"),
    }
    Ok(())
}
