//! Per-function state: registers, windows, scopes, jump targets, and the
//! origin of every instruction.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use bytecode_lang::{FunctionBuilder, Inst, Label, Reg, ValType};
use hir_lang::{BinderId, ExprId, NodeRef};

/// Whether a register of this type can keep a heap object alive.
fn holds_refs(ty: ValType) -> bool {
    matches!(ty, ValType::Dyn | ValType::Str | ValType::Ref(_))
}

/// A jump target: a loop, or a labeled block.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Target {
    /// The label binder that names it, if any.
    pub(crate) label: Option<BinderId>,
    /// A loop (`continue` may target it), or a block.
    pub(crate) is_loop: bool,
    /// Where `break` goes.
    pub(crate) brk: Label,
    /// Where `continue` goes (loops only).
    pub(crate) cont: Label,
    /// Where a `break` value goes.
    pub(crate) result: Reg,
    /// How many `finally` contexts were open when the target was entered.
    pub(crate) fin_depth: usize,
    /// A unique id, so `finally` dispatch can number its targets.
    pub(crate) id: u32,
}

/// A jump that leaves a `finally` region and resumes after its body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Exit {
    /// `return`, with the value in the completion register.
    Return,
    /// `break` out of target `id`, with a value (in the completion register)
    /// or not.
    Break(u32, bool),
    /// `continue` target `id`.
    Continue(u32),
}

/// An open `try ... finally` (or `defer`): its completion registers, the
/// entry of its single `finally` copy, and the exits that pass through it.
#[derive(Clone, Debug)]
pub(crate) struct Fin {
    /// The completion kind (`i8`): 0 normal, 1 return, 2 throw, 3 + n exit n.
    pub(crate) kind: Reg,
    /// The completion value (`dyn`): the return value, break value, or error.
    pub(crate) value: Reg,
    /// The `finally` body's first instruction.
    pub(crate) entry: Label,
    /// The exits that leave through this `finally`, numbered from 3.
    pub(crate) exits: Vec<Exit>,
    /// The `try`/`defer` node, the origin of the dispatch and rethrow.
    pub(crate) node: NodeRef,
}

/// The labels and registers of an open `try`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct TryState {
    /// The `try` expression (`None` for a `defer`).
    pub(crate) e: Option<ExprId>,
    /// The `try` or `defer` node: the origin of its exits.
    pub(crate) node: NodeRef,
    /// The `finally` body (or the deferred expression).
    pub(crate) finally: Option<ExprId>,
    /// Where the value of the whole `try` goes.
    pub(crate) result: Option<Reg>,
    /// The catch region: (start, start pc, end, handler, catch register).
    pub(crate) catch: Option<(Label, u32, Label, Label, Reg)>,
    /// The finally region: (start, start pc, end, handler).
    pub(crate) fin: Option<(Label, u32, Label, Label)>,
    /// After the whole `try`.
    pub(crate) end: Label,
}

/// A binder allocated in an open scope.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Scoped {
    pub(crate) binder: BinderId,
    pub(crate) reg: Reg,
    pub(crate) start: Label,
}

/// The state of the function being generated.
pub(crate) struct FnCx {
    pub(crate) f: FunctionBuilder,
    /// The node of every instruction emitted so far.
    pub(crate) origins: Vec<NodeRef>,
    /// The node new instructions are attributed to.
    pub(crate) node: NodeRef,
    /// The node whose location the builder currently writes.
    pub(crate) located: Option<NodeRef>,
    types: Vec<ValType>,
    live: Vec<bool>,
    free: BTreeMap<ValType, Vec<Reg>>,
    shapes: Vec<Vec<ValType>>,
    windows: Vec<Vec<Reg>>,
    pub(crate) scopes: Vec<usize>,
    pub(crate) scoped: Vec<Scoped>,
    pub(crate) targets: Vec<Target>,
    pub(crate) fins: Vec<Fin>,
    pub(crate) tries: Vec<TryState>,
    pub(crate) next_target: u32,
    /// Clear registers holding references when they die (see
    /// [`Options::with_reference_counting`](crate::Options::with_reference_counting)).
    pub(crate) clear: bool,
    /// The last instruction ended a block (a jump, return, throw): code
    /// here is unreachable until a label is bound, so nothing is cleared.
    pub(crate) dead: bool,
}

impl FnCx {
    pub(crate) fn new(f: FunctionBuilder, params: &[ValType], node: NodeRef) -> Self {
        let n = params.len();
        FnCx {
            f,
            origins: Vec::new(),
            node,
            located: None,
            types: params.to_vec(),
            live: alloc::vec![true; n],
            free: BTreeMap::new(),
            shapes: Vec::new(),
            windows: Vec::new(),
            scopes: Vec::new(),
            scoped: Vec::new(),
            targets: Vec::new(),
            fins: Vec::new(),
            tries: Vec::new(),
            next_target: 0,
            clear: false,
            dead: false,
        }
    }

    /// Emits one instruction, attributed to the current node.
    pub(crate) fn emit(&mut self, inst: Inst) -> u32 {
        self.origins.push(self.node);
        self.dead = matches!(
            inst,
            Inst::Ret { .. }
                | Inst::RetVoid { .. }
                | Inst::Throw { .. }
                | Inst::Raise { .. }
                | Inst::Unreachable { .. }
                | Inst::TailCall { .. }
                | Inst::TailCallIndirect { .. }
        );
        self.f.emit(inst)
    }

    /// Declares a register, mirroring its type.
    fn declare(&mut self, ty: ValType) -> Reg {
        let r = self.f.reg(ty);
        if r.index() == self.types.len() {
            self.types.push(ty);
            self.live.push(true);
        }
        r
    }

    /// A register of type `ty` no live value uses: a freed one, or a new one.
    pub(crate) fn temp(&mut self, ty: ValType) -> Reg {
        if let Some(r) = self.free.get_mut(&ty).and_then(Vec::pop) {
            if let Some(l) = self.live.get_mut(r.index()) {
                *l = true;
            }
            return r;
        }
        self.declare(ty)
    }

    /// Returns a register to its type's pool. Registers outside the mirror
    /// (only after a builder overflow, reported at the end) are ignored.
    pub(crate) fn release(&mut self, r: Reg) {
        let Some(&ty) = self.types.get(r.index()) else {
            return;
        };
        if let Some(l) = self.live.get_mut(r.index()) {
            debug_assert!(*l, "register {r} released twice");
            if !*l {
                return;
            }
            *l = false;
        }
        if self.clear && !self.dead && holds_refs(ty) {
            let _ = self.emit(Inst::LoadNil { dst: r });
        }
        self.free.entry(ty).or_default().push(r);
    }

    /// The declared type of `r`.
    pub(crate) fn type_of(&self, r: Reg) -> ValType {
        self.types.get(r.index()).copied().unwrap_or(ValType::Dyn)
    }

    /// A window of consecutive registers of the given types (a call's
    /// result and arguments); returns its shape id and first register.
    pub(crate) fn window(&mut self, shape: &[ValType]) -> (u32, Reg) {
        let id = match self.shapes.iter().position(|s| s.as_slice() == shape) {
            Some(i) => i,
            None => {
                self.shapes.push(shape.to_vec());
                self.windows.push(Vec::new());
                self.shapes.len() - 1
            }
        };
        let id32 = u32::try_from(id).unwrap_or(u32::MAX);
        if let Some(base) = self.windows.get_mut(id).and_then(Vec::pop) {
            return (id32, base);
        }
        let base = Reg(u16::try_from(self.types.len()).unwrap_or(u16::MAX));
        for &ty in shape {
            let _ = self.declare(ty);
        }
        (id32, base)
    }

    /// Returns a window to its shape's pool.
    pub(crate) fn release_window(&mut self, shape: u32, base: Reg) {
        if self.clear && !self.dead {
            let n = self.shapes.get(shape as usize).map_or(0, Vec::len);
            for i in 0..n {
                let ty = self
                    .shapes
                    .get(shape as usize)
                    .and_then(|s| s.get(i))
                    .copied()
                    .unwrap_or(ValType::Bool);
                if holds_refs(ty) {
                    let _ = self.emit(Inst::LoadNil {
                        dst: Self::slot(base, i),
                    });
                }
            }
        }
        if let Some(w) = self.windows.get_mut(shape as usize) {
            debug_assert!(!w.contains(&base), "window {base} released twice");
            w.push(base);
        }
    }

    /// The registers of a window: its base plus `i`.
    pub(crate) fn slot(base: Reg, i: usize) -> Reg {
        Reg(base.0.saturating_add(u16::try_from(i).unwrap_or(u16::MAX)))
    }
}

#[cfg(test)]
mod tests {
    use bytecode_lang::{ModuleBuilder, ValType};
    use hir_lang::{ItemId, NodeRef};

    use super::FnCx;

    fn cx() -> FnCx {
        let mut m = ModuleBuilder::new();
        let f = m.function("f", &[ValType::Dyn], &[ValType::Dyn]);
        let node = NodeRef::Item(ItemId::from_index(0).unwrap_or_else(unreachable_id));
        FnCx::new(f, &[ValType::Dyn], node)
    }

    fn unreachable_id() -> ItemId {
        panic!("id 0 exists")
    }

    #[test]
    fn temporaries_are_reused_per_type() {
        let mut fx = cx();
        let a = fx.temp(ValType::Dyn);
        let b = fx.temp(ValType::Bool);
        assert_ne!(a, b);
        fx.release(a);
        assert_eq!(fx.temp(ValType::Dyn), a);
        // A bool temporary never comes back as a dyn one.
        fx.release(b);
        assert_ne!(fx.temp(ValType::Dyn), b);
        assert_eq!(fx.type_of(b), ValType::Bool);
    }

    #[test]
    fn windows_are_consecutive_and_pooled_by_shape() {
        let mut fx = cx();
        let shape = [ValType::Dyn, ValType::Dyn, ValType::I64];
        let (s, base) = fx.window(&shape);
        assert_eq!(fx.type_of(FnCx::slot(base, 2)), ValType::I64);
        let (_, other) = fx.window(&shape);
        assert_ne!(base, other);
        fx.release_window(s, base);
        assert_eq!(fx.window(&shape).1, base);
        // A different shape never reuses it.
        assert_ne!(fx.window(&[ValType::Dyn]).1, base);
    }
}
