//! Named intrinsics, compiled through the [`Intrinsics`](crate::Intrinsics)
//! table: an LSB sequence, a host call, or a guarded fast path over a host
//! call (LexerSketch decision D27).
//!
//! A fast path evaluates the operands straight into the host call's window,
//! tests their kinds, and runs the inline sequence where it computes exactly
//! the intrinsic's result (the domains are documented on
//! [`Fast`](crate::Fast)); everywhere else the same window is handed to the
//! host function, so the slow path costs no moves. No fast path invokes an
//! LSB hook: its result does not depend on which hooks a module binds.

use alloc::vec::Vec;

use bytecode_lang::{
    Const, ImportId, Inst, IntTy, Kind, Label, Overflow, Policy, Prim as BPrim, Reg, Shift, ValType,
};
use hir_lang::{ExprId, NodeRef, Symbol};
use intern_lang::Lookup;

use super::{Dst, Gen, Step, Task, Val};
use crate::error::CompileError;
use crate::func::FnCx;
use crate::intrinsics::{Fast, Lowering, LsbOp};

/// The continuation of a named intrinsic, once its operands are evaluated.
#[derive(Clone, Copy, Debug)]
pub(crate) enum IntrinsicStep {
    /// An LSB sequence over `n` operands on the value stack.
    Lsb {
        op: LsbOp,
        n: usize,
        dst: Dst,
        node: NodeRef,
    },
    /// A host call (with an optional fast path) whose operands are in the
    /// window.
    Host {
        fast: Option<Fast>,
        import: ImportId,
        win: (u32, Reg),
        argc: u8,
        dst: Dst,
        node: NodeRef,
    },
}

impl<L: Lookup> Gen<'_, '_, L> {
    /// `Intrinsic::Named(name)` applied to `args`.
    pub(crate) fn intrinsic_expr(
        &mut self,
        e: ExprId,
        name: Symbol,
        args: &[ExprId],
        dst: Dst,
    ) -> Result<(), CompileError> {
        let node = NodeRef::Expr(e);
        let text = self.cx.text(name);
        let Some(def) = self.cx.opts.intrinsics().get(&text) else {
            return Err(CompileError::UnknownIntrinsic {
                name,
                node,
                span: self.cx.span(node),
            });
        };
        if !def.arity().accepts(args.len()) {
            return Err(CompileError::IntrinsicArity {
                node,
                span: self.cx.span(node),
                arity: def.arity(),
                found: u32::try_from(args.len()).unwrap_or(u32::MAX),
            });
        }
        let (fast, module, func) = match def.lowering() {
            Lowering::Lsb(op) => {
                let op = *op;
                self.tasks
                    .push(Task::Step(Step::Intrinsic(IntrinsicStep::Lsb {
                        op,
                        n: args.len(),
                        dst,
                        node,
                    })));
                for i in (0..args.len()).rev() {
                    let d = self.operand_dst(args, i);
                    if let Some(&x) = args.get(i) {
                        self.tasks.push(Task::Expr(x, d));
                    }
                }
                return Ok(());
            }
            Lowering::Host { module, name } => (None, module.clone(), name.clone()),
            Lowering::Fast { fast, module, name } => (Some(*fast), module.clone(), name.clone()),
        };
        // `accepts` bounds the count by 255.
        let argc = u8::try_from(args.len()).unwrap_or(u8::MAX);
        let import = self.cx.import(&module, &func, argc);
        let shape = alloc::vec![ValType::Dyn; args.len() + 1];
        let win = self.fx.window(&shape);
        let mut ts: Vec<Task> = Vec::with_capacity(args.len() * 2 + 1);
        for (i, &a) in args.iter().enumerate() {
            ts.extend(self.store_expr_tasks(a, FnCx::slot(win.1, i + 1)));
        }
        ts.push(Task::Step(Step::Intrinsic(IntrinsicStep::Host {
            fast,
            import,
            win,
            argc,
            dst,
            node,
        })));
        self.sched_all(ts);
        Ok(())
    }

    pub(crate) fn intrinsic_step(&mut self, s: IntrinsicStep) -> Result<(), CompileError> {
        match s {
            IntrinsicStep::Lsb { op, n, dst, node } => {
                self.at(node);
                let vals = self.pop_n(n);
                let r = self.result_reg(dst);
                self.lsb_op(op, &vals, r);
                for v in vals {
                    self.release(v);
                }
                self.produced(r, dst);
            }
            IntrinsicStep::Host {
                fast,
                import,
                win,
                argc,
                dst,
                node,
            } => {
                self.at(node);
                let r = self.result_reg(dst);
                let args: Vec<Reg> = (0..usize::from(argc))
                    .map(|i| FnCx::slot(win.1, i + 1))
                    .collect();
                let slow = self.label();
                let done = self.label();
                if let Some(f) = fast {
                    self.fast_path(f, &args, r, slow);
                    self.jmp(done);
                }
                self.bind(slow);
                self.emit(Inst::CallImport {
                    dst: win.1,
                    import,
                    argc,
                });
                self.emit(Inst::Mov { dst: r, src: win.1 });
                self.bind(done);
                self.fx.release_window(win.0, win.1);
                self.produced(r, dst);
            }
        }
        Ok(())
    }

    /// The built-in LSB intrinsics (LSB semantics, hooks included).
    fn lsb_op(&mut self, op: LsbOp, args: &[Val], r: Reg) {
        let a = args.first().map_or(Reg(0), |v| v.reg);
        let b = args.get(1).map_or(Reg(0), |v| v.reg);
        match op {
            LsbOp::Concat => self.emit(Inst::DConcat {
                dst: r,
                lhs: a,
                rhs: b,
            }),
            LsbOp::Len => {
                let n = self.fx.temp(ValType::I64);
                self.emit(Inst::DLen { dst: n, src: a });
                self.emit(Inst::ToDyn {
                    dst: r,
                    src: n,
                    from: BPrim::I64,
                });
                self.fx.release(n);
            }
            LsbOp::Truthy | LsbOp::Not => {
                let t = self.fx.temp(ValType::Bool);
                if op == LsbOp::Truthy {
                    self.emit(Inst::DTruthy { dst: t, src: a });
                } else {
                    self.emit(Inst::DNot { dst: t, src: a });
                }
                self.emit(Inst::ToDyn {
                    dst: r,
                    src: t,
                    from: BPrim::Bool,
                });
                self.fx.release(t);
            }
            LsbOp::TypeOf => {
                let t = self.fx.temp(ValType::U8);
                self.emit(Inst::TypeOf { dst: t, src: a });
                self.emit(Inst::ToDyn {
                    dst: r,
                    src: t,
                    from: BPrim::U8,
                });
                self.fx.release(t);
            }
            LsbOp::Iter => {
                // PHP iterates a snapshot: a copy-on-write `dup` first.
                if self.php() {
                    let t = self.fx.temp(ValType::Dyn);
                    self.dup_into(t, a);
                    self.emit(Inst::DIterNew { dst: r, src: t });
                    self.fx.release(t);
                } else {
                    self.emit(Inst::DIterNew { dst: r, src: a });
                }
            }
            LsbOp::IterNext => {
                // nil when done, else the pair [key, value].
                let has = self.fx.temp(ValType::Bool);
                let v = self.fx.temp(ValType::Dyn);
                let k = self.fx.temp(ValType::Dyn);
                let done = self.label();
                let end = self.label();
                self.emit(Inst::IterNext {
                    has,
                    iter: a,
                    val: v,
                });
                self.jump_on(has, done, false);
                self.emit(Inst::IterKey { dst: k, iter: a });
                let m = self.new_map();
                self.emit(Inst::MapPush { map: m, src: k });
                if self.php() {
                    self.dup_into(v, v);
                }
                self.emit(Inst::MapPush { map: m, src: v });
                self.emit(Inst::Mov { dst: r, src: m });
                self.fx.release(m);
                self.jmp(end);
                self.bind(done);
                self.emit(Inst::LoadNil { dst: r });
                self.bind(end);
                self.fx.release(k);
                self.fx.release(v);
                self.fx.release(has);
            }
            LsbOp::Resume => self.emit(Inst::Resume {
                dst: r,
                coro: a,
                src: b,
            }),
            LsbOp::ResumeThrow => self.emit(Inst::ResumeThrow {
                dst: r,
                coro: a,
                src: b,
            }),
            LsbOp::CoroClose => self.emit(Inst::CoroClose {
                dst: r,
                coro: a,
                src: b,
            }),
            LsbOp::CoroKey => self.emit(Inst::CoroKey { dst: r, coro: a }),
            LsbOp::CoroResult => self.emit(Inst::CoroResult { dst: r, coro: a }),
            LsbOp::CoroStatus => {
                let t = self.fx.temp(ValType::U8);
                self.emit(Inst::CoroStatus { dst: t, coro: a });
                self.emit(Inst::ToDyn {
                    dst: r,
                    src: t,
                    from: BPrim::U8,
                });
                self.fx.release(t);
            }
            LsbOp::ErrCode => {
                let t = self.fx.temp(ValType::U32);
                self.emit(Inst::ErrCode { dst: t, src: a });
                self.emit(Inst::ToDyn {
                    dst: r,
                    src: t,
                    from: BPrim::U32,
                });
                self.fx.release(t);
            }
            LsbOp::ErrPayload => self.emit(Inst::ErrPayload { dst: r, src: a }),
        }
    }

    // ------------------------------------------------------------ guards

    /// Jumps to `slow` unless `src` has kind `kind`.
    fn need_kind(&mut self, src: Reg, kind: Kind, slow: Label) {
        let b = self.fx.temp(ValType::Bool);
        self.emit(Inst::IsKind { dst: b, src, kind });
        self.jump_on(b, slow, false);
        self.fx.release(b);
    }

    /// Jumps to `slow` unless `src` is an `int` or a `float`.
    fn need_number(&mut self, src: Reg, slow: Label) {
        let b = self.fx.temp(ValType::Bool);
        let ok = self.label();
        self.emit(Inst::IsKind {
            dst: b,
            src,
            kind: Kind::Int,
        });
        self.jump_on(b, ok, true);
        self.emit(Inst::IsKind {
            dst: b,
            src,
            kind: Kind::Float,
        });
        self.jump_on(b, slow, false);
        self.bind(ok);
        self.fx.release(b);
    }

    /// The kind code of `src` (LSB §2.2) in a new `u8` temporary.
    fn kind_code(&mut self, src: Reg) -> Reg {
        let t = self.fx.temp(ValType::U8);
        self.emit(Inst::TypeOf { dst: t, src });
        t
    }

    /// `b = (t <op> k)` for a `u8` kind code.
    fn code_cmp(&mut self, b: Reg, t: Reg, k: u8, le: bool) {
        let c = self.fx.temp(ValType::U8);
        self.emit(Inst::LoadInt {
            dst: c,
            val: i32::from(k),
            ty: IntTy::U8,
        });
        self.emit(if le {
            Inst::ILe {
                dst: b,
                lhs: t,
                rhs: c,
                ty: IntTy::U8,
            }
        } else {
            Inst::IEq {
                dst: b,
                lhs: t,
                rhs: c,
                ty: IntTy::U8,
            }
        });
        self.fx.release(c);
    }

    /// Jumps to `slow` unless the kind code `t` is `nil`, `bool`, `int`, or
    /// `float` (codes 0 to 3), or also `str` (5) when `str_ok`.
    fn need_scalar(&mut self, t: Reg, str_ok: bool, slow: Label) {
        let b = self.fx.temp(ValType::Bool);
        let ok = self.label();
        self.code_cmp(b, t, 3, true);
        if str_ok {
            self.jump_on(b, ok, true);
            self.code_cmp(b, t, 5, false);
        }
        self.jump_on(b, slow, false);
        self.bind(ok);
        self.fx.release(b);
    }

    /// A `bool` register boxed into `r`.
    fn box_bool(&mut self, r: Reg, b: Reg) {
        self.emit(Inst::ToDyn {
            dst: r,
            src: b,
            from: BPrim::Bool,
        });
    }

    /// Emits the fast path of `f` over `args` into `r`; jumps to `slow` for
    /// operands outside its domain. Falls through when done.
    fn fast_path(&mut self, f: Fast, args: &[Reg], r: Reg, slow: Label) {
        let a = args.first().copied().unwrap_or(Reg(0));
        let b = args.get(1).copied().unwrap_or(Reg(0));
        match f {
            Fast::Concat => {
                self.need_kind(a, Kind::Str, slow);
                self.need_kind(b, Kind::Str, slow);
                self.emit(Inst::DConcat {
                    dst: r,
                    lhs: a,
                    rhs: b,
                });
            }
            Fast::ConcatN => self.fast_concat_n(args, r, slow),
            Fast::IntRem => {
                self.need_kind(a, Kind::Int, slow);
                self.need_kind(b, Kind::Int, slow);
                let pol = Policy::new().with_div_zero(bytecode_lang::DivZero::Error);
                self.emit(Inst::DRem {
                    dst: r,
                    lhs: a,
                    rhs: b,
                    pol,
                });
            }
            Fast::NumPow => {
                self.need_number(a, slow);
                self.need_number(b, slow);
                let pol = Policy::new().with_overflow(Overflow::Promote);
                self.emit(Inst::DPow {
                    dst: r,
                    lhs: a,
                    rhs: b,
                    pol,
                });
            }
            Fast::IntShl | Fast::IntShr => {
                self.need_kind(a, Kind::Int, slow);
                self.need_kind(b, Kind::Int, slow);
                let pol = Policy::new().with_shift(Shift::Saturate);
                self.emit(if f == Fast::IntShl {
                    Inst::DShl {
                        dst: r,
                        lhs: a,
                        rhs: b,
                        pol,
                    }
                } else {
                    Inst::DShr {
                        dst: r,
                        lhs: a,
                        rhs: b,
                        pol,
                    }
                });
            }
            Fast::ScalarXor => {
                let ta = self.kind_code(a);
                let tb = self.kind_code(b);
                self.need_scalar(ta, false, slow);
                self.need_scalar(tb, false, slow);
                let x = self.fx.temp(ValType::Bool);
                let y = self.fx.temp(ValType::Bool);
                self.emit(Inst::DTruthy { dst: x, src: a });
                self.emit(Inst::DTruthy { dst: y, src: b });
                self.emit(Inst::BXor {
                    dst: x,
                    lhs: x,
                    rhs: y,
                });
                self.box_bool(r, x);
                for t in [y, x, tb, ta] {
                    self.fx.release(t);
                }
            }
            Fast::LooseEq | Fast::LooseNe => self.fast_loose_eq(a, b, r, f == Fast::LooseNe, slow),
            Fast::StrictEq | Fast::StrictNe => {
                self.fast_strict_eq(a, b, r, f == Fast::StrictNe, slow);
            }
            Fast::Lt | Fast::Le | Fast::Gt | Fast::Ge => self.fast_order(f, a, b, r, slow),
            Fast::IntSpaceship => {
                self.need_kind(a, Kind::Int, slow);
                self.need_kind(b, Kind::Int, slow);
                let t = self.fx.temp(ValType::Bool);
                let (less, equal, done) = (self.label(), self.label(), self.label());
                self.emit(Inst::DLt {
                    dst: t,
                    lhs: a,
                    rhs: b,
                });
                self.jump_on(t, less, true);
                self.emit(Inst::DEq {
                    dst: t,
                    lhs: a,
                    rhs: b,
                });
                self.jump_on(t, equal, true);
                self.emit(Inst::DLoadInt { dst: r, val: 1 });
                self.jmp(done);
                self.bind(less);
                self.emit(Inst::DLoadInt { dst: r, val: -1 });
                self.jmp(done);
                self.bind(equal);
                self.emit(Inst::DLoadInt { dst: r, val: 0 });
                self.bind(done);
                self.fx.release(t);
            }
            Fast::NumIdentity => {
                self.need_number(a, slow);
                self.emit(Inst::Mov { dst: r, src: a });
            }
            Fast::IntBitNot => {
                self.need_kind(a, Kind::Int, slow);
                self.emit(Inst::DBitNot {
                    dst: r,
                    src: a,
                    pol: Policy::new(),
                });
            }
            Fast::ToInt | Fast::ToFloat => self.fast_to_number(f == Fast::ToFloat, a, r, slow),
            Fast::ToStr => {
                self.need_kind(a, Kind::Str, slow);
                self.emit(Inst::Mov { dst: r, src: a });
            }
            Fast::ToBool => {
                let t = self.kind_code(a);
                self.need_scalar(t, false, slow);
                let x = self.fx.temp(ValType::Bool);
                self.emit(Inst::DTruthy { dst: x, src: a });
                self.box_bool(r, x);
                self.fx.release(x);
                self.fx.release(t);
            }
            Fast::ToArray => {
                self.need_kind(a, Kind::Map, slow);
                self.emit(Inst::Mov { dst: r, src: a });
            }
        }
    }

    /// Every part a `str`: one `str_concat_n` over unboxed copies.
    fn fast_concat_n(&mut self, args: &[Reg], r: Reg, slow: Label) {
        for &p in args {
            self.need_kind(p, Kind::Str, slow);
        }
        if args.is_empty() {
            let s = self.cx.mb.string("");
            let k = self.cx.mb.constant(Const::Str(s));
            self.emit(Inst::DLoadConst { dst: r, k });
            return;
        }
        let shape = alloc::vec![ValType::Str; args.len()];
        let parts = self.fx.window(&shape);
        for (i, &p) in args.iter().enumerate() {
            self.emit(Inst::FromDyn {
                dst: FnCx::slot(parts.1, i),
                src: p,
                to: BPrim::Str,
            });
        }
        let s = self.fx.temp(ValType::Str);
        self.emit(Inst::StrConcatN {
            dst: s,
            first: parts.1,
            count: u8::try_from(args.len()).unwrap_or(u8::MAX),
        });
        self.emit(Inst::ToDyn {
            dst: r,
            src: s,
            from: BPrim::Str,
        });
        self.fx.release(s);
        self.fx.release_window(parts.0, parts.1);
    }

    /// PHP 8's `==` where it is LSB's `deq`: the same scalar kind, or two
    /// strings with equal bytes (equal however PHP would compare them).
    fn fast_loose_eq(&mut self, a: Reg, b: Reg, r: Reg, negate: bool, slow: Label) {
        let ta = self.kind_code(a);
        let tb = self.kind_code(b);
        let t = self.fx.temp(ValType::Bool);
        let (strings, done) = (self.label(), self.label());
        self.emit(Inst::IEq {
            dst: t,
            lhs: ta,
            rhs: tb,
            ty: IntTy::U8,
        });
        self.jump_on(t, slow, false);
        self.code_cmp(t, ta, 3, true);
        self.jump_on(t, strings, false);
        self.emit(Inst::DEq {
            dst: t,
            lhs: a,
            rhs: b,
        });
        if negate {
            self.emit(Inst::BNot { dst: t, src: t });
        }
        self.box_bool(r, t);
        self.jmp(done);
        self.bind(strings);
        self.code_cmp(t, ta, 5, false);
        self.jump_on(t, slow, false);
        let sa = self.fx.temp(ValType::Str);
        let sb = self.fx.temp(ValType::Str);
        self.emit(Inst::FromDyn {
            dst: sa,
            src: a,
            to: BPrim::Str,
        });
        self.emit(Inst::FromDyn {
            dst: sb,
            src: b,
            to: BPrim::Str,
        });
        self.emit(Inst::StrEq {
            dst: t,
            lhs: sa,
            rhs: sb,
        });
        // Different bytes may still be equal numbers ("1e3" == "1000").
        self.jump_on(t, slow, false);
        self.emit(Inst::LoadBool {
            dst: t,
            val: !negate,
        });
        self.box_bool(r, t);
        self.bind(done);
        for x in [sb, sa, t, tb, ta] {
            self.fx.release(x);
        }
    }

    /// PHP's `===` on scalars: equal kinds and equal values.
    fn fast_strict_eq(&mut self, a: Reg, b: Reg, r: Reg, negate: bool, slow: Label) {
        let ta = self.kind_code(a);
        let tb = self.kind_code(b);
        self.need_scalar(ta, true, slow);
        self.need_scalar(tb, true, slow);
        let t = self.fx.temp(ValType::Bool);
        let (differ, done) = (self.label(), self.label());
        self.emit(Inst::IEq {
            dst: t,
            lhs: ta,
            rhs: tb,
            ty: IntTy::U8,
        });
        self.jump_on(t, differ, false);
        self.emit(Inst::DEq {
            dst: t,
            lhs: a,
            rhs: b,
        });
        if negate {
            self.emit(Inst::BNot { dst: t, src: t });
        }
        self.box_bool(r, t);
        self.jmp(done);
        self.bind(differ);
        self.emit(Inst::LoadBool {
            dst: t,
            val: negate,
        });
        self.box_bool(r, t);
        self.bind(done);
        for x in [t, tb, ta] {
            self.fx.release(x);
        }
    }

    /// Two `int`s or two `float`s: LSB's numeric order.
    fn fast_order(&mut self, f: Fast, a: Reg, b: Reg, r: Reg, slow: Label) {
        let ta = self.kind_code(a);
        let tb = self.kind_code(b);
        let t = self.fx.temp(ValType::Bool);
        let num = self.label();
        self.emit(Inst::IEq {
            dst: t,
            lhs: ta,
            rhs: tb,
            ty: IntTy::U8,
        });
        self.jump_on(t, slow, false);
        self.code_cmp(t, ta, 2, false);
        self.jump_on(t, num, true);
        self.code_cmp(t, ta, 3, false);
        self.jump_on(t, slow, false);
        self.bind(num);
        self.emit(match f {
            Fast::Lt => Inst::DLt {
                dst: t,
                lhs: a,
                rhs: b,
            },
            Fast::Le => Inst::DLe {
                dst: t,
                lhs: a,
                rhs: b,
            },
            Fast::Gt => Inst::DGt {
                dst: t,
                lhs: a,
                rhs: b,
            },
            _ => Inst::DGe {
                dst: t,
                lhs: a,
                rhs: b,
            },
        });
        self.box_bool(r, t);
        for x in [t, tb, ta] {
            self.fx.release(x);
        }
    }

    /// `(int)` or `(float)` of a number, a `bool`, or nil.
    fn fast_to_number(&mut self, float: bool, a: Reg, r: Reg, slow: Label) {
        let t = self.fx.temp(ValType::Bool);
        let (own, other, boolean, nil, done) = (
            self.label(),
            self.label(),
            self.label(),
            self.label(),
            self.label(),
        );
        let (same, cross) = if float {
            (Kind::Float, Kind::Int)
        } else {
            (Kind::Int, Kind::Float)
        };
        self.emit(Inst::IsKind {
            dst: t,
            src: a,
            kind: same,
        });
        self.jump_on(t, own, true);
        self.emit(Inst::IsKind {
            dst: t,
            src: a,
            kind: Kind::Bool,
        });
        self.jump_on(t, boolean, true);
        self.emit(Inst::IsKind {
            dst: t,
            src: a,
            kind: Kind::Nil,
        });
        self.jump_on(t, nil, true);
        if float {
            self.emit(Inst::IsKind {
                dst: t,
                src: a,
                kind: cross,
            });
            self.jump_on(t, other, true);
        }
        self.jmp(slow);
        self.bind(own);
        self.emit(Inst::Mov { dst: r, src: a });
        self.jmp(done);
        let i = self.fx.temp(ValType::I64);
        if float {
            // An int: the nearest float, ties to even.
            self.bind(other);
            self.emit(Inst::FromDyn {
                dst: i,
                src: a,
                to: BPrim::I64,
            });
            self.int_to_dyn_float(r, i);
            self.jmp(done);
        }
        self.bind(boolean);
        self.emit(Inst::FromDyn {
            dst: t,
            src: a,
            to: BPrim::Bool,
        });
        self.emit(Inst::BoolToInt {
            dst: i,
            src: t,
            ty: IntTy::I64,
        });
        if float {
            self.int_to_dyn_float(r, i);
        } else {
            self.emit(Inst::ToDyn {
                dst: r,
                src: i,
                from: BPrim::I64,
            });
        }
        self.jmp(done);
        self.bind(nil);
        if float {
            let k = self.cx.mb.constant(Const::f64(0.0));
            self.emit(Inst::DLoadConst { dst: r, k });
        } else {
            self.emit(Inst::DLoadInt { dst: r, val: 0 });
        }
        self.bind(done);
        self.fx.release(i);
        self.fx.release(t);
    }

    /// `r` = the `i64` in `i` as a dynamic float.
    fn int_to_dyn_float(&mut self, r: Reg, i: Reg) {
        let f = self.fx.temp(ValType::F64);
        self.emit(Inst::IntToF64 {
            dst: f,
            src: i,
            ty: IntTy::I64,
        });
        self.emit(Inst::ToDyn {
            dst: r,
            src: f,
            from: BPrim::F64,
        });
        self.fx.release(f);
    }
}
