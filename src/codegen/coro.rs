//! Coroutines (LSB §5.13, HIR §8.7): `yield`, keyed `yield`, `yield from`,
//! `await`, and `spawn`.
//!
//! LSB coroutines are stackful, so only generators need a frame of their
//! own: a function or closure with `YIELD` compiles to a callable that makes
//! a coroutine of its body (see `entry.rs`), while `ASYNC` alone changes
//! nothing about the function, whose `await`s suspend whichever task runs
//! it.

use bytecode_lang::{Inst, IntTy, Kind, Reg, ValType};
use hir_lang::{ExprId, NodeRef};
use intern_lang::Lookup;

use super::{Dst, Gen, Rel, Step, Task, Val};

/// The continuation steps of the coroutine forms.
#[derive(Clone, Copy, Debug)]
pub(crate) enum CoroStep {
    /// Pops the value (when there is one) and the key below it (when
    /// there is one), and yields.
    Yield {
        key: bool,
        value: bool,
        dst: Dst,
        node: NodeRef,
    },
    /// Pops the inner generator or iterable and delegates to it.
    YieldFrom { dst: Dst, node: NodeRef },
    /// Pops the awaitable and awaits it.
    Await { dst: Dst, node: NodeRef },
    /// Pops the callable and starts a task running it.
    Spawn { dst: Dst, node: NodeRef },
}

/// The coroutine state codes `coro_status` reports (LSB §5.13).
const AWAITING: i32 = 3;
const RETURNED: i32 = 4;

impl<L: Lookup> Gen<'_, '_, L> {
    /// `yield key => value`: the key first, then the value.
    pub(crate) fn yield_expr(
        &mut self,
        e: ExprId,
        key: Option<ExprId>,
        value: Option<ExprId>,
        dst: Dst,
    ) {
        let node = NodeRef::Expr(e);
        let mut ts: alloc::vec::Vec<Task> = alloc::vec::Vec::with_capacity(4);
        if let Some(k) = key {
            let d = if value.is_none_or(|v| self.simple(v)) {
                Dst::Any
            } else {
                Dst::Temp
            };
            ts.push(Task::Expr(k, d));
        }
        if let Some(v) = value {
            // The yielded value leaves the frame: copied when shared (PHP).
            let dup = self.needs_dup(v);
            ts.push(Task::Expr(v, Dst::Any));
            if dup {
                ts.push(Task::Deliver { dst: Dst::Any, dup });
            }
        }
        ts.push(Task::Step(Step::Coro(CoroStep::Yield {
            key: key.is_some(),
            value: value.is_some(),
            dst,
            node,
        })));
        self.sched_all(ts);
    }

    /// Schedules a form whose single operand is evaluated first.
    pub(crate) fn coro_unary(&mut self, operand: ExprId, step: CoroStep) {
        self.sched([Task::Expr(operand, Dst::Temp), Task::Step(Step::Coro(step))]);
    }

    pub(crate) fn coro_step(&mut self, s: CoroStep) -> Result<(), crate::error::CompileError> {
        match s {
            CoroStep::Yield {
                key,
                value,
                dst,
                node,
            } => {
                self.at(node);
                let v = if value {
                    self.pop()
                } else {
                    let r = self.fx.temp(ValType::Dyn);
                    self.emit(Inst::LoadNil { dst: r });
                    Val {
                        reg: r,
                        rel: Rel::Temp,
                    }
                };
                let k = key.then(|| self.pop());
                let r = self.result_reg(dst);
                match k {
                    Some(k) => self.emit(Inst::YieldKv {
                        dst: r,
                        key: k.reg,
                        src: v.reg,
                    }),
                    None => self.emit(Inst::Yield { dst: r, src: v.reg }),
                }
                if let Some(k) = k {
                    self.release(k);
                }
                self.release(v);
                // The sent value arrives from outside the frame.
                if self.php() && dst != Dst::Discard {
                    self.dup_into(r, r);
                }
                self.produced(r, dst);
            }
            CoroStep::YieldFrom { dst, node } => {
                self.at(node);
                let inner = self.pop();
                let r = self.result_reg(dst);
                self.yield_from(inner.reg, r);
                self.release(inner);
                self.produced(r, dst);
            }
            CoroStep::Await { dst, node } => {
                self.at(node);
                let v = self.pop();
                let r = self.result_reg(dst);
                self.emit(Inst::Await { dst: r, src: v.reg });
                self.release(v);
                self.produced(r, dst);
            }
            CoroStep::Spawn { dst, node } => {
                self.at(node);
                let callee = self.pop();
                // `spawn`'s window is its result only: zero arguments.
                let win = self.fx.window(&[ValType::Dyn]);
                self.emit(Inst::Spawn {
                    dst: win.1,
                    callee: callee.reg,
                    argc: 0,
                });
                self.release(callee);
                self.deliver(
                    Val {
                        reg: win.1,
                        rel: Rel::Win(win.0),
                    },
                    dst,
                    false,
                );
            }
        }
        Ok(())
    }

    /// `r = yield from inner` (HIR §8.7): a coroutine is driven, each of its
    /// values re-yielded under its own key, the values sent to this
    /// generator forwarded with `resume` and errors thrown into it with
    /// `resume_throw`, an `await` passed through; the result is its return
    /// value. Any other value is iterated (`diter_new`), each entry yielded
    /// under its key, and the result is nil.
    fn yield_from(&mut self, inner: Reg, r: Reg) {
        let b = self.fx.temp(ValType::Bool);
        let st = self.fx.temp(ValType::U8);
        let code = self.fx.temp(ValType::U8);
        let k = self.fx.temp(ValType::Dyn);
        let v = self.fx.temp(ValType::Dyn);
        let sent = self.fx.temp(ValType::Dyn);
        let err = self.fx.temp(ValType::Dyn);
        let (iterable, end, top, check, handler) = (
            self.label(),
            self.label(),
            self.label(),
            self.label(),
            self.label(),
        );
        self.emit(Inst::IsKind {
            dst: b,
            src: inner,
            kind: Kind::Coroutine,
        });
        self.jump_on(b, iterable, false);
        // Already returned: its return value, without resuming it.
        let not_done = self.label();
        self.emit(Inst::CoroStatus {
            dst: st,
            coro: inner,
        });
        self.state_is(b, st, code, RETURNED);
        self.jump_on(b, not_done, false);
        self.emit(Inst::CoroResult {
            dst: r,
            coro: inner,
        });
        self.jmp(end);
        self.bind(not_done);
        self.emit(Inst::LoadNil { dst: sent });
        self.bind(top);
        self.emit(Inst::Resume {
            dst: v,
            coro: inner,
            src: sent,
        });
        self.bind(check);
        self.emit(Inst::CoroStatus {
            dst: st,
            coro: inner,
        });
        let not_returned = self.label();
        self.state_is(b, st, code, RETURNED);
        self.jump_on(b, not_returned, false);
        self.emit(Inst::Mov { dst: r, src: v });
        self.jmp(end);
        self.bind(not_returned);
        let yielded = self.label();
        self.state_is(b, st, code, AWAITING);
        self.jump_on(b, yielded, false);
        self.emit(Inst::Await { dst: sent, src: v });
        self.jmp(top);
        self.bind(yielded);
        self.emit(Inst::CoroKey {
            dst: k,
            coro: inner,
        });
        // An error thrown into this generator at the re-yield goes to the
        // inner one.
        let (start, stop) = (self.label(), self.label());
        self.bind(start);
        self.emit(Inst::YieldKv {
            dst: sent,
            key: k,
            src: v,
        });
        self.bind(stop);
        self.jmp(top);
        self.fx.f.try_region(start, stop, handler, err);
        self.bind(handler);
        self.emit(Inst::ResumeThrow {
            dst: v,
            coro: inner,
            src: err,
        });
        self.jmp(check);
        // Not a coroutine: iterate it.
        self.bind(iterable);
        let it = self.fx.temp(ValType::Dyn);
        let next = self.label();
        let done = self.label();
        self.emit(Inst::DIterNew {
            dst: it,
            src: inner,
        });
        self.bind(next);
        self.emit(Inst::IterNext {
            has: b,
            iter: it,
            val: v,
        });
        self.jump_on(b, done, false);
        self.emit(Inst::IterKey { dst: k, iter: it });
        self.emit(Inst::YieldKv {
            dst: sent,
            key: k,
            src: v,
        });
        self.jmp(next);
        self.bind(done);
        self.emit(Inst::LoadNil { dst: r });
        self.bind(end);
        for t in [it, err, sent, v, k, code, st, b] {
            self.fx.release(t);
        }
    }

    /// `b = (st == code)` for a coroutine state code.
    fn state_is(&mut self, b: Reg, st: Reg, code: Reg, state: i32) {
        self.emit(Inst::LoadInt {
            dst: code,
            val: state,
            ty: IntTy::U8,
        });
        self.emit(Inst::IEq {
            dst: b,
            lhs: st,
            rhs: code,
            ty: IntTy::U8,
        });
    }
}
