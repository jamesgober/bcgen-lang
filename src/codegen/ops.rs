//! OPS operations on dynamic values (HIR §12, LSB §5.6).
//!
//! The arithmetic with a dynamic instruction maps one to one, carrying the
//! op's policy in the instruction. The rest dispatch on the operands' kinds:
//! `int` operands use the typed `i64` instruction, numbers with a `float` use
//! the `f64` one (converting `int` operands, OPS's mixed rule), and anything
//! else is a `TypeError` raised by unboxing. Every sequence writes its
//! destination last, so a raising operation leaves it untouched (LSB §4.3).

use bytecode_lang::{
    FloatConv, FloatTy, Inst, IntConv, IntOp, IntPair, IntTy, Kind, Prim as BPrim, Reg, ValType,
};
use hir_lang::{NodeRef, Op, OpKind, Overflow, Policy, Prim, Ty, TyId};
use intern_lang::Lookup;

use super::Gen;
use crate::error::{CompileError, Unsupported};

/// The LSB policy byte for a HIR policy (absent fields are not consulted).
pub(crate) fn policy(p: Policy) -> bytecode_lang::Policy {
    let mut q = bytecode_lang::Policy::new();
    if let Some(o) = p.overflow {
        q = q.with_overflow(overflow(o));
    }
    if let Some(d) = p.div_zero {
        q = q.with_div_zero(match d {
            hir_lang::DivZero::Error => bytecode_lang::DivZero::Error,
            hir_lang::DivZero::Trap => bytecode_lang::DivZero::Trap,
        });
    }
    if let Some(s) = p.shift {
        q = q.with_shift(match s {
            hir_lang::Shift::Error => bytecode_lang::Shift::Error,
            hir_lang::Shift::Mask => bytecode_lang::Shift::Mask,
            hir_lang::Shift::Saturate => bytecode_lang::Shift::Saturate,
        });
    }
    if let Some(f) = p.float_to_int {
        q = q.with_float_to_int(match f {
            hir_lang::FloatToInt::Error => bytecode_lang::FloatToInt::Error,
            hir_lang::FloatToInt::Saturate => bytecode_lang::FloatToInt::Saturate,
        });
    }
    q
}

fn overflow(o: Overflow) -> bytecode_lang::Overflow {
    match o {
        Overflow::Error => bytecode_lang::Overflow::Error,
        Overflow::Wrap => bytecode_lang::Overflow::Wrap,
        Overflow::Trap => bytecode_lang::Overflow::Trap,
        Overflow::Promote => bytecode_lang::Overflow::Promote,
    }
}

/// The float-to-integer conversion to `ty` under a HIR policy's
/// `float_to_int` (absent: `error`).
fn float_conv(ty: IntTy, p: Policy) -> FloatConv {
    FloatConv::new(ty).with_float_to_int(match p.float_to_int {
        Some(hir_lang::FloatToInt::Saturate) => bytecode_lang::FloatToInt::Saturate,
        _ => bytecode_lang::FloatToInt::Error,
    })
}

/// The LSB integer type of a HIR primitive (`isize`/`usize` are 64-bit).
pub(crate) fn int_ty(p: Prim) -> Option<IntTy> {
    Some(match p {
        Prim::I8 => IntTy::I8,
        Prim::I16 => IntTy::I16,
        Prim::I32 => IntTy::I32,
        Prim::I64 | Prim::Isize => IntTy::I64,
        Prim::U8 => IntTy::U8,
        Prim::U16 => IntTy::U16,
        Prim::U32 => IntTy::U32,
        Prim::U64 | Prim::Usize => IntTy::U64,
        _ => return None,
    })
}

/// The `to_dyn`/`from_dyn` primitive of an integer type.
pub(crate) fn bprim(t: IntTy) -> BPrim {
    match t {
        IntTy::I8 => BPrim::I8,
        IntTy::I16 => BPrim::I16,
        IntTy::I32 => BPrim::I32,
        IntTy::I64 => BPrim::I64,
        IntTy::U8 => BPrim::U8,
        IntTy::U16 => BPrim::U16,
        IntTy::U32 => BPrim::U32,
        IntTy::U64 => BPrim::U64,
    }
}

/// Emits `dst = op(args)` for `dyn` operands and a `dyn` destination.
pub(crate) fn emit_op<L: Lookup>(
    g: &mut Gen<'_, '_, L>,
    op: Op,
    args: &[Reg],
    dst: Reg,
    node: NodeRef,
) -> Result<(), CompileError> {
    let a = args.first().copied().unwrap_or(Reg(0));
    let b = args.get(1).copied().unwrap_or(Reg(0));
    let pol = policy(op.policy);
    match op.kind {
        OpKind::Add => g.emit(Inst::DAdd {
            dst,
            lhs: a,
            rhs: b,
            pol,
        }),
        OpKind::Sub => g.emit(Inst::DSub {
            dst,
            lhs: a,
            rhs: b,
            pol,
        }),
        OpKind::Mul => g.emit(Inst::DMul {
            dst,
            lhs: a,
            rhs: b,
            pol,
        }),
        OpKind::Div => g.emit(Inst::DDiv {
            dst,
            lhs: a,
            rhs: b,
            pol,
        }),
        OpKind::Rem => g.emit(Inst::DRem {
            dst,
            lhs: a,
            rhs: b,
            pol,
        }),
        OpKind::FloorDiv => g.emit(Inst::DFloorDiv {
            dst,
            lhs: a,
            rhs: b,
            pol,
        }),
        OpKind::FloorMod => g.emit(Inst::DFloorMod {
            dst,
            lhs: a,
            rhs: b,
            pol,
        }),
        OpKind::Shl => g.emit(Inst::DShl {
            dst,
            lhs: a,
            rhs: b,
            pol,
        }),
        OpKind::Shr => g.emit(Inst::DShr {
            dst,
            lhs: a,
            rhs: b,
            pol,
        }),
        OpKind::Neg => g.emit(Inst::DNeg { dst, src: a, pol }),
        OpKind::Pow => g.emit(Inst::DPow {
            dst,
            lhs: a,
            rhs: b,
            pol,
        }),
        OpKind::And | OpKind::Or | OpKind::Xor => logic2(g, op.kind, a, b, dst, pol),
        OpKind::Not => {
            // Logical negation of truthiness (HIR v3 `not`, LSB `dnot`).
            let x = g.fx.temp(ValType::Bool);
            g.emit(Inst::DNot { dst: x, src: a });
            g.emit(Inst::ToDyn {
                dst,
                src: x,
                from: BPrim::Bool,
            });
            g.fx.release(x);
        }
        OpKind::BitNot => g.emit(Inst::DBitNot { dst, src: a, pol }),
        OpKind::Eq | OpKind::Ne | OpKind::Lt | OpKind::Le | OpKind::Gt | OpKind::Ge => {
            let t = g.fx.temp(ValType::Bool);
            emit_cmp(g, op.kind, t, a, b);
            g.emit(Inst::ToDyn {
                dst,
                src: t,
                from: BPrim::Bool,
            });
            g.fx.release(t);
        }
        OpKind::Min | OpKind::Max => num2(g, op.kind, a, b, dst),
        OpKind::IeeeRem => float2(g, a, b, dst, |dst, lhs, rhs| Inst::FIeeeRem {
            dst,
            lhs,
            rhs,
            ty: FloatTy::F64,
        }),
        OpKind::TotalCmp => {
            let x = to_f64(g, a);
            let y = to_f64(g, b);
            let t = g.fx.temp(ValType::I8);
            g.emit(Inst::FTotalCmp {
                dst: t,
                lhs: x,
                rhs: y,
                ty: FloatTy::F64,
            });
            g.emit(Inst::ToDyn {
                dst,
                src: t,
                from: BPrim::I8,
            });
            for r in [t, y, x] {
                g.fx.release(r);
            }
        }
        OpKind::Fma => {
            let c = args.get(2).copied().unwrap_or(Reg(0));
            let x = to_f64(g, a);
            let y = to_f64(g, b);
            let z = to_f64(g, c);
            g.emit(Inst::FFma {
                dst: z,
                lhs: x,
                rhs: y,
                ty: FloatTy::F64,
            });
            g.emit(Inst::ToDyn {
                dst,
                src: z,
                from: BPrim::F64,
            });
            for r in [z, y, x] {
                g.fx.release(r);
            }
        }
        OpKind::Sqrt => float1(g, a, dst, |dst, src| Inst::FSqrt {
            dst,
            src,
            ty: FloatTy::F64,
        }),
        OpKind::Floor => float1(g, a, dst, |dst, src| Inst::FFloor {
            dst,
            src,
            ty: FloatTy::F64,
        }),
        OpKind::Ceil => float1(g, a, dst, |dst, src| Inst::FCeil {
            dst,
            src,
            ty: FloatTy::F64,
        }),
        OpKind::Trunc => float1(g, a, dst, |dst, src| Inst::FTrunc {
            dst,
            src,
            ty: FloatTy::F64,
        }),
        OpKind::Round => float1(g, a, dst, |dst, src| Inst::FRound {
            dst,
            src,
            ty: FloatTy::F64,
        }),
        OpKind::RoundEven => {
            float1(g, a, dst, |dst, src| Inst::FRoundEven {
                dst,
                src,
                ty: FloatTy::F64,
            });
        }
        OpKind::Abs => g.emit(Inst::DAbs { dst, src: a, pol }),
        OpKind::IntCast(t) => {
            let ty = int_ty(t).unwrap_or(IntTy::I64);
            let over = overflow(op.policy.overflow.unwrap_or(Overflow::Error));
            let x = unbox(g, a, ValType::I64, BPrim::I64);
            let y = g.fx.temp(ValType::int(ty));
            g.emit(Inst::IntCast {
                dst: y,
                src: x,
                conv: IntConv::new(IntTy::I64, ty, over),
            });
            g.emit(Inst::ToDyn {
                dst,
                src: y,
                from: bprim(ty),
            });
            g.fx.release(y);
            g.fx.release(x);
        }
        OpKind::FloatToInt(t) => {
            let ty = int_ty(t).unwrap_or(IntTy::I64);
            let x = unbox(g, a, ValType::F64, BPrim::F64);
            let y = g.fx.temp(ValType::int(ty));
            g.emit(Inst::F64ToInt {
                dst: y,
                src: x,
                conv: float_conv(ty, op.policy),
            });
            g.emit(Inst::ToDyn {
                dst,
                src: y,
                from: bprim(ty),
            });
            g.fx.release(y);
            g.fx.release(x);
        }
        OpKind::Zext(t) | OpKind::Sext(t) | OpKind::Narrow(t) => {
            let ty = int_ty(t).unwrap_or(IntTy::I64);
            let narrow = matches!(op.kind, OpKind::Narrow(_));
            // Dynamic integers are `i64`: widening is only to 64 bits.
            if !narrow && ty.bits() != 64 {
                return Err(g.cx.unsupported(Unsupported::Conversion, node));
            }
            let x = unbox(g, a, ValType::I64, BPrim::I64);
            let y = g.fx.temp(ValType::int(ty));
            let pair = IntPair::new(IntTy::I64, ty);
            g.emit(match op.kind {
                OpKind::Zext(_) => Inst::Zext {
                    dst: y,
                    src: x,
                    pair,
                },
                OpKind::Sext(_) => Inst::Sext {
                    dst: y,
                    src: x,
                    pair,
                },
                _ => Inst::Trunc {
                    dst: y,
                    src: x,
                    pair,
                },
            });
            g.emit(Inst::ToDyn {
                dst,
                src: y,
                from: bprim(ty),
            });
            g.fx.release(y);
            g.fx.release(x);
        }
        OpKind::IntToFloat(t) => {
            let x = unbox(g, a, ValType::I64, BPrim::I64);
            if t == Prim::F32 {
                let y = g.fx.temp(ValType::F32);
                g.emit(Inst::IntToF32 {
                    dst: y,
                    src: x,
                    ty: IntTy::I64,
                });
                g.emit(Inst::ToDyn {
                    dst,
                    src: y,
                    from: BPrim::F32,
                });
                g.fx.release(y);
            } else {
                let y = g.fx.temp(ValType::F64);
                g.emit(Inst::IntToF64 {
                    dst: y,
                    src: x,
                    ty: IntTy::I64,
                });
                g.emit(Inst::ToDyn {
                    dst,
                    src: y,
                    from: BPrim::F64,
                });
                g.fx.release(y);
            }
            g.fx.release(x);
        }
        OpKind::Bitcast(t) => match t {
            Prim::I64 | Prim::U64 | Prim::Isize | Prim::Usize => {
                let ty = int_ty(t).unwrap_or(IntTy::I64);
                let x = unbox(g, a, ValType::F64, BPrim::F64);
                let y = g.fx.temp(ValType::int(ty));
                g.emit(Inst::FloatToBits { dst: y, src: x, ty });
                g.emit(Inst::ToDyn {
                    dst,
                    src: y,
                    from: bprim(ty),
                });
                g.fx.release(y);
                g.fx.release(x);
            }
            Prim::F64 => {
                let x = unbox(g, a, ValType::I64, BPrim::I64);
                let y = g.fx.temp(ValType::F64);
                g.emit(Inst::BitsToFloat {
                    dst: y,
                    src: x,
                    ty: IntTy::I64,
                });
                g.emit(Inst::ToDyn {
                    dst,
                    src: y,
                    from: BPrim::F64,
                });
                g.fx.release(y);
                g.fx.release(x);
            }
            _ => return Err(g.cx.unsupported(Unsupported::Conversion, node)),
        },
        OpKind::BoolToInt(t) => {
            let ty = int_ty(t).unwrap_or(IntTy::I64);
            let x = unbox(g, a, ValType::Bool, BPrim::Bool);
            let y = g.fx.temp(ValType::int(ty));
            g.emit(Inst::BoolToInt { dst: y, src: x, ty });
            g.emit(Inst::ToDyn {
                dst,
                src: y,
                from: bprim(ty),
            });
            g.fx.release(y);
            g.fx.release(x);
        }
        OpKind::F32ToF64 => {
            // Dynamic floats are already `f64`: a checked identity.
            let x = unbox(g, a, ValType::F64, BPrim::F64);
            g.emit(Inst::ToDyn {
                dst,
                src: x,
                from: BPrim::F64,
            });
            g.fx.release(x);
        }
        OpKind::F64ToF32 => {
            let x = unbox(g, a, ValType::F64, BPrim::F64);
            let y = g.fx.temp(ValType::F32);
            g.emit(Inst::F64ToF32 { dst: y, src: x });
            g.emit(Inst::ToDyn {
                dst,
                src: y,
                from: BPrim::F32,
            });
            g.fx.release(y);
            g.fx.release(x);
        }
        OpKind::CharFromU32 => {
            let x = unbox(g, a, ValType::U32, BPrim::U32);
            let y = g.fx.temp(ValType::Char);
            g.emit(Inst::CharFromU32 { dst: y, src: x });
            g.emit(Inst::ToDyn {
                dst,
                src: y,
                from: BPrim::Char,
            });
            g.fx.release(y);
            g.fx.release(x);
        }
    }
    Ok(())
}

/// A dynamic comparison into a `bool` register.
pub(crate) fn emit_cmp<L: Lookup>(
    g: &mut Gen<'_, '_, L>,
    kind: OpKind,
    dst: Reg,
    lhs: Reg,
    rhs: Reg,
) {
    g.emit(match kind {
        OpKind::Eq => Inst::DEq { dst, lhs, rhs },
        OpKind::Ne => Inst::DNe { dst, lhs, rhs },
        OpKind::Lt => Inst::DLt { dst, lhs, rhs },
        OpKind::Le => Inst::DLe { dst, lhs, rhs },
        OpKind::Gt => Inst::DGt { dst, lhs, rhs },
        _ => Inst::DGe { dst, lhs, rhs },
    });
}

/// `from_dyn` into a new register of type `ty` (`TypeError` on a kind
/// mismatch, `ArithOverflow` when an integer does not fit).
fn unbox<L: Lookup>(g: &mut Gen<'_, '_, L>, src: Reg, ty: ValType, to: BPrim) -> Reg {
    let r = g.fx.temp(ty);
    g.emit(Inst::FromDyn { dst: r, src, to });
    r
}

/// A number as `f64`: an `int` converted (round to nearest even), a `float`
/// as is, anything else a `TypeError`.
fn to_f64<L: Lookup>(g: &mut Gen<'_, '_, L>, src: Reg) -> Reg {
    let f = g.fx.temp(ValType::F64);
    let isi = g.fx.temp(ValType::Bool);
    let float = g.label();
    let done = g.label();
    g.emit(Inst::IsKind {
        dst: isi,
        src,
        kind: Kind::Int,
    });
    g.jump_on(isi, float, false);
    let i = g.fx.temp(ValType::I64);
    g.emit(Inst::FromDyn {
        dst: i,
        src,
        to: BPrim::I64,
    });
    g.emit(Inst::IntToF64 {
        dst: f,
        src: i,
        ty: IntTy::I64,
    });
    g.fx.release(i);
    g.jmp(done);
    g.bind(float);
    g.emit(Inst::FromDyn {
        dst: f,
        src,
        to: BPrim::F64,
    });
    g.bind(done);
    g.fx.release(isi);
    f
}

fn float1<L: Lookup>(g: &mut Gen<'_, '_, L>, a: Reg, dst: Reg, make: fn(Reg, Reg) -> Inst) {
    let x = to_f64(g, a);
    g.emit(make(x, x));
    g.emit(Inst::ToDyn {
        dst,
        src: x,
        from: BPrim::F64,
    });
    g.fx.release(x);
}

fn float2<L: Lookup>(
    g: &mut Gen<'_, '_, L>,
    a: Reg,
    b: Reg,
    dst: Reg,
    make: fn(Reg, Reg, Reg) -> Inst,
) {
    let x = to_f64(g, a);
    let y = to_f64(g, b);
    g.emit(make(x, x, y));
    g.emit(Inst::ToDyn {
        dst,
        src: x,
        from: BPrim::F64,
    });
    g.fx.release(y);
    g.fx.release(x);
}

/// `min`/`max`: integers compare as integers; otherwise as `f64` (OPS §4:
/// NaN wins, `-0.0 < +0.0`).
fn num2<L: Lookup>(g: &mut Gen<'_, '_, L>, kind: OpKind, a: Reg, b: Reg, dst: Reg) {
    let ia = g.fx.temp(ValType::Bool);
    let ib = g.fx.temp(ValType::Bool);
    let float = g.label();
    let done = g.label();
    g.emit(Inst::IsKind {
        dst: ia,
        src: a,
        kind: Kind::Int,
    });
    g.emit(Inst::IsKind {
        dst: ib,
        src: b,
        kind: Kind::Int,
    });
    g.emit(Inst::BAnd {
        dst: ia,
        lhs: ia,
        rhs: ib,
    });
    g.jump_on(ia, float, false);
    let x = g.fx.temp(ValType::I64);
    let y = g.fx.temp(ValType::I64);
    g.emit(Inst::FromDyn {
        dst: x,
        src: a,
        to: BPrim::I64,
    });
    g.emit(Inst::FromDyn {
        dst: y,
        src: b,
        to: BPrim::I64,
    });
    let op = IntOp::new(IntTy::I64);
    g.emit(if kind == OpKind::Min {
        Inst::IMin {
            dst: x,
            lhs: x,
            rhs: y,
            op,
        }
    } else {
        Inst::IMax {
            dst: x,
            lhs: x,
            rhs: y,
            op,
        }
    });
    g.emit(Inst::ToDyn {
        dst,
        src: x,
        from: BPrim::I64,
    });
    g.fx.release(y);
    g.fx.release(x);
    g.jmp(done);
    g.bind(float);
    let fx = to_f64(g, a);
    let fy = to_f64(g, b);
    g.emit(if kind == OpKind::Min {
        Inst::FMin {
            dst: fx,
            lhs: fx,
            rhs: fy,
            ty: FloatTy::F64,
        }
    } else {
        Inst::FMax {
            dst: fx,
            lhs: fx,
            rhs: fy,
            ty: FloatTy::F64,
        }
    });
    g.emit(Inst::ToDyn {
        dst,
        src: fx,
        from: BPrim::F64,
    });
    g.fx.release(fy);
    g.fx.release(fx);
    g.bind(done);
    g.fx.release(ib);
    g.fx.release(ia);
}

/// `and`/`or`/`xor`: logical on two bools, bitwise (the dynamic instruction,
/// with its hook) otherwise.
fn logic2<L: Lookup>(
    g: &mut Gen<'_, '_, L>,
    kind: OpKind,
    a: Reg,
    b: Reg,
    dst: Reg,
    pol: bytecode_lang::Policy,
) {
    let ia = g.fx.temp(ValType::Bool);
    let ib = g.fx.temp(ValType::Bool);
    let int = g.label();
    let done = g.label();
    g.emit(Inst::IsKind {
        dst: ia,
        src: a,
        kind: Kind::Bool,
    });
    g.emit(Inst::IsKind {
        dst: ib,
        src: b,
        kind: Kind::Bool,
    });
    g.emit(Inst::BAnd {
        dst: ia,
        lhs: ia,
        rhs: ib,
    });
    g.jump_on(ia, int, false);
    g.emit(Inst::FromDyn {
        dst: ia,
        src: a,
        to: BPrim::Bool,
    });
    g.emit(Inst::FromDyn {
        dst: ib,
        src: b,
        to: BPrim::Bool,
    });
    g.emit(match kind {
        OpKind::And => Inst::BAnd {
            dst: ia,
            lhs: ia,
            rhs: ib,
        },
        OpKind::Or => Inst::BOr {
            dst: ia,
            lhs: ia,
            rhs: ib,
        },
        _ => Inst::BXor {
            dst: ia,
            lhs: ia,
            rhs: ib,
        },
    });
    g.emit(Inst::ToDyn {
        dst,
        src: ia,
        from: BPrim::Bool,
    });
    g.jmp(done);
    g.bind(int);
    g.emit(match kind {
        OpKind::And => Inst::DAnd {
            dst,
            lhs: a,
            rhs: b,
            pol,
        },
        OpKind::Or => Inst::DOr {
            dst,
            lhs: a,
            rhs: b,
            pol,
        },
        _ => Inst::DXor {
            dst,
            lhs: a,
            rhs: b,
            pol,
        },
    });
    g.bind(done);
    g.fx.release(ib);
    g.fx.release(ia);
}

/// The primitive a cast's target type names, if it is one.
fn cast_prim(hir: &hir_lang::Hir, ty: TyId) -> Option<Prim> {
    match *hir.ty(ty) {
        Ty::Prim(p) => Some(p),
        Ty::Path(p) => match hir.path(p).res {
            hir_lang::Res::Prim(p) => Some(p),
            _ => None,
        },
        _ => None,
    }
}

/// `expr as ty` in the dynamic profile: a run-time conversion by kind.
pub(crate) fn emit_cast<L: Lookup>(
    g: &mut Gen<'_, '_, L>,
    ty: TyId,
    pol: Policy,
    src: Reg,
    dst: Reg,
    node: NodeRef,
) -> Result<(), CompileError> {
    let hir = g.cx.hir;
    let mut ty = ty;
    let mut nullable = false;
    if let Ty::Nullable(inner) = *hir.ty(ty) {
        nullable = true;
        ty = inner;
    }
    let done = g.label();
    if nullable {
        let isn = g.fx.temp(ValType::Bool);
        let go = g.label();
        g.emit(Inst::IsKind {
            dst: isn,
            src,
            kind: Kind::Nil,
        });
        g.jump_on(isn, go, false);
        g.emit(Inst::LoadNil { dst });
        g.jmp(done);
        g.bind(go);
        g.fx.release(isn);
    }
    match *hir.ty(ty) {
        Ty::Any | Ty::Infer => {
            if dst != src {
                g.emit(Inst::Mov { dst, src });
            }
        }
        Ty::Union(_) | Ty::Intersection(_) => {
            // A union or intersection type converts nothing: a value whose
            // kind it admits passes unchanged, any other is a TypeError.
            let Some(kinds) = kind_set(hir, ty) else {
                return Err(g.cx.unsupported(Unsupported::Cast, node));
            };
            let ok = g.label();
            g.test_kinds(src, kinds, ok);
            g.raise_type_error();
            g.bind(ok);
            if dst != src {
                g.emit(Inst::Mov { dst, src });
            }
        }
        _ => {
            let Some(p) = cast_prim(hir, ty) else {
                return Err(g.cx.unsupported(Unsupported::Cast, node));
            };
            cast_to_prim(g, p, pol, src, dst, done);
        }
    }
    g.bind(done);
    Ok(())
}

fn cast_to_prim<L: Lookup>(
    g: &mut Gen<'_, '_, L>,
    p: Prim,
    pol: Policy,
    src: Reg,
    dst: Reg,
    done: bytecode_lang::Label,
) {
    let k = g.fx.temp(ValType::Bool);
    match p {
        Prim::Bool => {
            g.emit(Inst::DTruthy { dst: k, src });
            g.emit(Inst::ToDyn {
                dst,
                src: k,
                from: BPrim::Bool,
            });
        }
        Prim::Str => {
            // Formatting numbers is a runtime-library call, not a cast.
            let bad = g.label();
            g.emit(Inst::IsKind {
                dst: k,
                src,
                kind: Kind::Str,
            });
            g.jump_on(k, bad, false);
            g.emit(Inst::Mov { dst, src });
            g.jmp(done);
            g.bind(bad);
            g.raise_type_error();
        }
        Prim::Char => {
            let notc = g.label();
            g.emit(Inst::IsKind {
                dst: k,
                src,
                kind: Kind::Char,
            });
            g.jump_on(k, notc, false);
            g.emit(Inst::Mov { dst, src });
            g.jmp(done);
            g.bind(notc);
            let x = unbox(g, src, ValType::U32, BPrim::U32);
            let c = g.fx.temp(ValType::Char);
            g.emit(Inst::CharFromU32 { dst: c, src: x });
            g.emit(Inst::ToDyn {
                dst,
                src: c,
                from: BPrim::Char,
            });
            g.fx.release(c);
            g.fx.release(x);
        }
        Prim::F32 | Prim::F64 => {
            let notb = g.label();
            g.emit(Inst::IsKind {
                dst: k,
                src,
                kind: Kind::Bool,
            });
            g.jump_on(k, notb, false);
            let b = unbox(g, src, ValType::Bool, BPrim::Bool);
            let i = g.fx.temp(ValType::I64);
            g.emit(Inst::BoolToInt {
                dst: i,
                src: b,
                ty: IntTy::I64,
            });
            let f = g.fx.temp(ValType::F64);
            g.emit(Inst::IntToF64 {
                dst: f,
                src: i,
                ty: IntTy::I64,
            });
            g.emit(Inst::ToDyn {
                dst,
                src: f,
                from: BPrim::F64,
            });
            g.fx.release(f);
            g.fx.release(i);
            g.fx.release(b);
            g.jmp(done);
            g.bind(notb);
            let f = to_f64(g, src);
            if p == Prim::F32 {
                let s = g.fx.temp(ValType::F32);
                g.emit(Inst::F64ToF32 { dst: s, src: f });
                g.emit(Inst::ToDyn {
                    dst,
                    src: s,
                    from: BPrim::F32,
                });
                g.fx.release(s);
            } else {
                g.emit(Inst::ToDyn {
                    dst,
                    src: f,
                    from: BPrim::F64,
                });
            }
            g.fx.release(f);
        }
        _ => {
            let ty = int_ty(p).unwrap_or(IntTy::I64);
            let over = overflow(pol.overflow.unwrap_or(Overflow::Error));
            let y = g.fx.temp(ValType::int(ty));
            let notint = g.label();
            let notfloat = g.label();
            let boxit = g.label();
            g.emit(Inst::IsKind {
                dst: k,
                src,
                kind: Kind::Int,
            });
            g.jump_on(k, notint, false);
            let x = unbox(g, src, ValType::I64, BPrim::I64);
            g.emit(Inst::IntCast {
                dst: y,
                src: x,
                conv: IntConv::new(IntTy::I64, ty, over),
            });
            g.fx.release(x);
            g.jmp(boxit);
            g.bind(notint);
            g.emit(Inst::IsKind {
                dst: k,
                src,
                kind: Kind::Float,
            });
            g.jump_on(k, notfloat, false);
            let f = unbox(g, src, ValType::F64, BPrim::F64);
            g.emit(Inst::F64ToInt {
                dst: y,
                src: f,
                conv: float_conv(ty, pol),
            });
            g.fx.release(f);
            g.jmp(boxit);
            g.bind(notfloat);
            // A bool is 0 or 1; anything else fails to unbox as a bool.
            let b = unbox(g, src, ValType::Bool, BPrim::Bool);
            g.emit(Inst::BoolToInt { dst: y, src: b, ty });
            g.fx.release(b);
            g.bind(boxit);
            g.emit(Inst::ToDyn {
                dst,
                src: y,
                from: bprim(ty),
            });
            g.fx.release(y);
        }
    }
    g.fx.release(k);
}

/// A set of dynamic kinds, one bit per LSB kind code (§2.2).
pub(crate) type KindSet = u16;

/// Every kind.
pub(crate) const ALL_KINDS: KindSet = u16::MAX;

/// The kinds a type admits in the dynamic profile, for a type test or a
/// checked cast: primitives by their kind, tuples and arrays as maps, `?T`
/// adds `nil`, a union the kinds of any member, an intersection the kinds of
/// every member, `never` none. `None` for a type the dynamic profile cannot
/// test (a path to a declared type, a function type, ...). Iterative: an
/// explicit stack, so nested unions of intersections of any depth cost no
/// native stack.
pub(crate) fn kind_set(hir: &hir_lang::Hir, ty: TyId) -> Option<KindSet> {
    /// A union or intersection being combined: its members, the next one
    /// to visit, and the set so far.
    struct Frame {
        union: bool,
        members: hir_lang::List<TyId>,
        next: usize,
        acc: KindSet,
        nullable: bool,
    }
    fn bit(k: Kind) -> KindSet {
        1 << k.code()
    }
    fn prim_set(p: Prim) -> KindSet {
        match p {
            Prim::Bool => bit(Kind::Bool),
            Prim::F32 | Prim::F64 => bit(Kind::Float),
            Prim::Char => bit(Kind::Char),
            Prim::Str => bit(Kind::Str),
            _ => bit(Kind::Int),
        }
    }
    let mut stack: alloc::vec::Vec<Frame> = alloc::vec::Vec::new();
    let mut next = Some(ty);
    loop {
        // Resolve one type to a set, or open a frame for a compound.
        let mut done: Option<KindSet> = None;
        if let Some(t) = next.take() {
            let mut t = t;
            let mut nullable = false;
            if let Ty::Nullable(inner) = *hir.ty(t) {
                nullable = true;
                t = inner;
            }
            let null = if nullable { bit(Kind::Nil) } else { 0 };
            match *hir.ty(t) {
                Ty::Any | Ty::Infer => done = Some(ALL_KINDS),
                Ty::Never => done = Some(null),
                Ty::Tuple(_) | Ty::Array { .. } | Ty::Slice(_) => {
                    done = Some(bit(Kind::Map) | null);
                }
                Ty::Prim(p) => done = Some(prim_set(p) | null),
                Ty::Path(p) => match hir.path(p).res {
                    hir_lang::Res::Prim(p) => done = Some(prim_set(p) | null),
                    _ => return None,
                },
                Ty::Union(list) | Ty::Intersection(list) => {
                    let union = matches!(hir.ty(t), Ty::Union(_));
                    stack.push(Frame {
                        union,
                        members: list,
                        next: 0,
                        acc: if union { 0 } else { ALL_KINDS },
                        nullable,
                    });
                }
                _ => return None,
            }
        }
        if let Some(set) = done {
            match stack.last_mut() {
                None => return Some(set),
                Some(f) => {
                    if f.union {
                        f.acc |= set;
                    } else {
                        f.acc &= set;
                    }
                }
            }
        }
        // The next member of the innermost open compound, or close it.
        loop {
            let f = stack.last_mut()?;
            if let Some(&m) = hir.list(f.members).get(f.next) {
                f.next += 1;
                next = Some(m);
                break;
            }
            let f = stack.pop()?;
            let set = f.acc | if f.nullable { bit(Kind::Nil) } else { 0 };
            match stack.last_mut() {
                None => return Some(set),
                Some(p) => {
                    if p.union {
                        p.acc |= set;
                    } else {
                        p.acc &= set;
                    }
                }
            }
        }
    }
}

impl<L: Lookup> Gen<'_, '_, L> {
    /// Jumps to `ok` when the kind of `v` is in `kinds` (falls through
    /// otherwise; every kind: always jumps).
    pub(crate) fn test_kinds(&mut self, v: Reg, kinds: KindSet, ok: bytecode_lang::Label) {
        if kinds == ALL_KINDS {
            self.jmp(ok);
            return;
        }
        let b = self.fx.temp(ValType::Bool);
        for code in 0..=14u8 {
            if kinds & (1 << code) == 0 {
                continue;
            }
            let Some(kind) = Kind::from_code(code) else {
                continue;
            };
            self.emit(Inst::IsKind {
                dst: b,
                src: v,
                kind,
            });
            self.jump_on(b, ok, true);
        }
        self.fx.release(b);
    }
}
