//! The module-level driver: declares every function, global, and import of
//! the unit, then generates function bodies from a work queue (closures and
//! generator entries are discovered while generating and queued, never
//! generated recursively).

use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::string::String;
use alloc::vec::Vec;

use bytecode_lang::{
    Callee, Const, ExportItem, FuncId, FunctionBuilder, GlobalId, Hook, ImportId, ModuleBuilder,
    Param as LParam, ParamKind as LParamKind, ParamList, StrId, TypeDef, TypeId, ValType,
};
use hir_lang::{
    BinderId, Def, DefaultEval, Effects, Expr, ExprId, Hir, ItemId, ItemKind, Lit, NodeRef,
    ParamId, ParamKind, PatId, Res, Span, Symbol,
};
use intern_lang::Lookup;

use crate::analysis::Analysis;
use crate::error::{CompileError, Unsupported};
use crate::options::{BodyMode, Locate, Options};
use crate::output::Compiled;

/// The most parameters a function may have when one has a default: the
/// width of the presence mask (LSB §5.15).
pub(crate) const MAX_PARAMS_WITH_DEFAULTS: usize = 64;

/// The most signature parameters (and call-window arguments) LSB carries.
pub(crate) const MAX_ARITY: usize = 255;

/// The module-wide types every function uses.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Types {
    /// `map dyn -> dyn`: arrays, maps, records.
    pub(crate) map: TypeId,
    /// `cell dyn`: the register type of references (shared variables,
    /// by-reference parameters; LSB §5.17).
    pub(crate) cell: TypeId,
    /// `iter dyn -> dyn`: typed iteration over maps.
    pub(crate) iter: TypeId,
}

/// Where a variable lives in the function being generated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Slot {
    /// In a `dyn` register.
    Reg(bytecode_lang::Reg),
    /// In a reference (LSB §5.17), held by a `ref cell` register.
    Cell(bytecode_lang::Reg),
    /// In a module global (`global $x`, `static $x`, a global captured by
    /// reference).
    Global(GlobalId),
    /// In a reference held by a module global: a global or static shared by
    /// reference.
    GlobalCell(GlobalId),
    /// A `let_place` alias: an index into the function's evaluated places.
    Place(u32),
}

/// A parameter, as the calling convention sees it.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PInfo {
    pub(crate) id: ParamId,
    pub(crate) kind: ParamKind,
    pub(crate) name: Option<Symbol>,
    pub(crate) by_ref: bool,
    pub(crate) default: Option<ExprId>,
    pub(crate) pat: PatId,
}

impl PInfo {
    pub(crate) fn of(hir: &Hir, id: ParamId) -> PInfo {
        let p = hir.param(id);
        let name = match *hir.pat(p.pat) {
            hir_lang::Pat::Bind { binder, .. } | hir_lang::Pat::Ident { binder, .. } => {
                hir.binder(binder).map(|b| b.name.sym)
            }
            _ => None,
        };
        PInfo {
            id,
            kind: p.kind,
            name,
            by_ref: p.by_ref,
            default: p.default,
            pat: p.pat,
        }
    }

    /// Filled from positional arguments.
    pub(crate) fn positional(&self) -> bool {
        matches!(self.kind, ParamKind::PositionalOnly | ParamKind::Normal)
    }

    /// Filled from named arguments.
    pub(crate) fn nameable(&self) -> bool {
        matches!(self.kind, ParamKind::Normal | ParamKind::NamedOnly) && self.name.is_some()
    }

    /// A rest parameter (positional or named).
    pub(crate) fn rest(&self) -> bool {
        matches!(self.kind, ParamKind::Rest | ParamKind::RestNamed)
    }

    /// Must be supplied: no default, not a rest parameter.
    pub(crate) fn required(&self) -> bool {
        self.default.is_none() && !self.rest()
    }

    /// The register type of the parameter: a by-reference parameter
    /// receives a reference (a by-reference rest parameter, a collection of
    /// them).
    pub(crate) fn reg_type(&self, types: &Types) -> ValType {
        if self.by_ref && !self.rest() {
            ValType::Ref(types.cell)
        } else {
            ValType::Dyn
        }
    }
}

/// A function item.
#[derive(Clone, Debug)]
pub(crate) struct FnInfo {
    /// The function every call reaches: it carries the parameter list (a
    /// generator's makes the coroutine). `None` for a bodyless (host)
    /// function.
    pub(crate) callable: Option<FuncId>,
    /// A generator's coroutine body (same signature as the callable).
    pub(crate) gen_body: Option<FuncId>,
    pub(crate) params: Vec<PInfo>,
    /// The signature: parameters, then the presence mask.
    pub(crate) sig: Vec<ValType>,
    pub(crate) has_mask: bool,
    /// Per parameter, the global holding a default evaluated once.
    pub(crate) once: Vec<Option<GlobalId>>,
    pub(crate) name: String,
}

/// A capture of a closure, in upvalue order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Cap {
    /// The value of a variable at creation.
    Value(BinderId),
    /// The reference of a shared variable.
    Cell(BinderId),
    /// The reference that will hold the closure itself (its self binder).
    SelfCell(BinderId),
    /// The default of parameter `n`, evaluated once at creation.
    Once(usize),
}

/// A function body waiting to be generated.
pub(crate) enum Job {
    /// A function item's code (a generator's coroutine body).
    Body {
        item: ItemId,
        f: FunctionBuilder,
    },
    /// A generator's callable: makes the coroutine of `body` from its
    /// captures (passed as leading arguments) and parameters.
    GenEntry {
        f: FunctionBuilder,
        body: FuncId,
        /// The capture types, read with `get_upval`.
        caps: Vec<ValType>,
        /// The signature.
        sig: Vec<ValType>,
        node: NodeRef,
    },
    Closure {
        e: ExprId,
        f: FunctionBuilder,
        caps: Vec<Cap>,
        /// Captured variables that alias globals (no upvalue).
        aliases: Vec<(BinderId, Slot)>,
        /// A generator closure's body: its captures arrive as the leading
        /// parameters, not as upvalues.
        caps_in_params: bool,
    },
    Start {
        f: FunctionBuilder,
        result: Option<GlobalId>,
    },
    Entry {
        f: FunctionBuilder,
    },
    Getter {
        f: FunctionBuilder,
        global: Option<GlobalId>,
    },
    PhpKey {
        f: FunctionBuilder,
    },
}

/// The module being generated.
pub(crate) struct Cx<'a, L: Lookup> {
    pub(crate) hir: &'a Hir,
    pub(crate) names: &'a L,
    pub(crate) opts: &'a Options,
    pub(crate) locator: Option<&'a dyn Locate>,
    pub(crate) mb: ModuleBuilder,
    pub(crate) an: Analysis,
    pub(crate) types: Types,
    pub(crate) fns: BTreeMap<ItemId, FnInfo>,
    pub(crate) globals: BTreeMap<ItemId, GlobalId>,
    pub(crate) imports: BTreeMap<(String, String, u8), ImportId>,
    pub(crate) jobs: VecDeque<Job>,
    pub(crate) php_key: Option<FuncId>,
    /// Per binder: (generation of the function that assigned it, slot).
    pub(crate) slots: Vec<(u32, Slot)>,
    /// The generation of the function being generated.
    pub(crate) epoch: u32,
    pub(crate) emitted: u64,
    pub(crate) origins: BTreeMap<u32, Vec<NodeRef>>,
    pub(crate) closures: u32,
    pub(crate) statics: u32,
    pub(crate) file: StrId,
}

impl<L: Lookup> Cx<'_, L> {
    /// The text of a symbol (empty for a symbol of another interner).
    pub(crate) fn text(&self, sym: Symbol) -> String {
        self.names
            .resolve_with(sym, |s| String::from(s))
            .unwrap_or_default()
    }

    /// The span of a node.
    pub(crate) fn span(&self, node: NodeRef) -> Span {
        self.hir.origin(node).span
    }

    pub(crate) fn unsupported(&self, feature: Unsupported, node: NodeRef) -> CompileError {
        CompileError::Unsupported {
            feature,
            node,
            span: self.span(node),
        }
    }

    pub(crate) fn err_at(
        &self,
        node: NodeRef,
        make: fn(NodeRef, Span) -> CompileError,
    ) -> CompileError {
        make(node, self.span(node))
    }

    /// The slot of `b` in the current function.
    pub(crate) fn slot(&self, b: BinderId) -> Option<Slot> {
        self.slots
            .get(b.index())
            .filter(|(g, _)| *g == self.epoch)
            .map(|&(_, s)| s)
    }

    pub(crate) fn set_slot(&mut self, b: BinderId, s: Slot) {
        if let Some(e) = self.slots.get_mut(b.index()) {
            *e = (self.epoch, s);
        }
    }

    /// Where a global item lives.
    pub(crate) fn global_slot(&self, item: ItemId) -> Option<Slot> {
        let g = *self.globals.get(&item)?;
        Some(if self.an.cell_globals.contains(&item) {
            Slot::GlobalCell(g)
        } else {
            Slot::Global(g)
        })
    }

    pub(crate) fn is_cell(&self, b: BinderId) -> bool {
        self.an.cell.get(b.index()).copied().unwrap_or(false)
    }

    /// The item a resolution names in this unit, or the error for a
    /// resolution the compiler cannot use as a value.
    pub(crate) fn local_item(
        &self,
        res: Res,
        node: NodeRef,
    ) -> Result<Option<ItemId>, CompileError> {
        match res {
            Res::Def(d) => {
                if d.unit() != self.hir.unit() {
                    return Err(self.unsupported(Unsupported::ForeignUnit, node));
                }
                match d.def() {
                    Def::Item(i) => Ok(Some(i)),
                    Def::Variant(_) => Err(self.unsupported(Unsupported::Record, node)),
                }
            }
            _ => Ok(None),
        }
    }

    /// The import for host symbol `module`.`name` called with `arity`
    /// arguments (each `dyn`, returning `dyn`).
    pub(crate) fn import(&mut self, module: &str, name: &str, arity: u8) -> ImportId {
        let key = (String::from(module), String::from(name), arity);
        if let Some(&id) = self.imports.get(&key) {
            return id;
        }
        let params = alloc::vec![ValType::Dyn; usize::from(arity)];
        let sig = self.mb.func_type(&params, &[ValType::Dyn]);
        let id = self.mb.import(module, name, sig);
        let _ = self.imports.insert(key, id);
        id
    }

    /// Splits a host symbol at its last `.`: `mox.concat` is `mox`.`concat`;
    /// a name without `.` belongs to the default host module.
    pub(crate) fn host_name(&self, sym: Symbol) -> (String, String) {
        let text = self.text(sym);
        match text.rfind('.') {
            Some(i) if i > 0 && i + 1 < text.len() => {
                (String::from(&text[..i]), String::from(&text[i + 1..]))
            }
            _ => (String::from(self.opts.host_module()), text),
        }
    }

    /// The direct-call function of PHP key coercion, declared on first use.
    pub(crate) fn php_key(&mut self) -> FuncId {
        if let Some(f) = self.php_key {
            return f;
        }
        let f = self
            .mb
            .function("<php_key>", &[ValType::Dyn], &[ValType::Dyn]);
        let id = f.id();
        self.php_key = Some(id);
        self.jobs.push_back(Job::PhpKey { f });
        id
    }

    /// The LSB parameter list of a HIR parameter list (LSB §5.15): HIR's
    /// `rest` collects into a map (`rest_map`, PHP 8.1's `...$args`: extra
    /// positional arguments under `0, 1, ...`, and unknown named ones when
    /// there is no `rest_named`). A `normal` or `named_only` parameter whose
    /// pattern binds no single name (or repeats an earlier name) gets a
    /// name no source argument can spell, so it binds by position only.
    pub(crate) fn param_list(&mut self, params: &[PInfo]) -> ParamList {
        let mut used: BTreeSet<Symbol> = BTreeSet::new();
        let mut out: Vec<LParam> = Vec::with_capacity(params.len());
        for (i, p) in params.iter().enumerate() {
            let kind = match p.kind {
                ParamKind::Receiver | ParamKind::PositionalOnly => LParamKind::PositionalOnly,
                ParamKind::Normal => LParamKind::Normal,
                ParamKind::NamedOnly => LParamKind::NamedOnly,
                ParamKind::Rest => LParamKind::RestMap,
                ParamKind::RestNamed => LParamKind::RestNamed,
            };
            let name = if kind.takes_names() {
                let text = match p.name {
                    Some(s) if used.insert(s) => self.text(s),
                    _ => alloc::format!("\0#{i}"),
                };
                Some(self.mb.string(&text))
            } else {
                None
            };
            let mut lp = LParam::new(kind, name);
            if p.by_ref {
                lp = lp.by_ref();
            }
            if p.default.is_some() && !p.rest() {
                lp = lp.with_default();
            }
            out.push(lp);
        }
        ParamList::new(out)
    }

    /// The constant a literal loads, or `None` for `null` (the default of a
    /// `dyn` global). Errors for literals the dynamic profile cannot hold.
    pub(crate) fn lit_const(
        &mut self,
        lit: Lit,
        node: NodeRef,
    ) -> Result<Option<Const>, CompileError> {
        Ok(Some(match lit {
            Lit::Null => return Ok(None),
            Lit::Bool(b) => Const::Bool(b),
            Lit::Int(i) => Const::Int(int_value(i).ok_or_else(|| {
                self.err_at(node, |node, span| CompileError::LiteralOutOfRange {
                    node,
                    span,
                })
            })?),
            // An `f32` literal is exactly representable (HIR validates it),
            // so its `f64` bits are its value; dynamic floats are `f64`.
            Lit::Float(f) => Const::F64(f.bits),
            Lit::Char(c) => Const::Char(c),
            Lit::Str(t) => {
                let s = self.mb.string(self.hir.str(t));
                Const::Str(s)
            }
            Lit::Bytes(t) => Const::Bytes(self.hir.text(t).to_vec()),
            Lit::BigInt(_) => return Err(self.unsupported(Unsupported::BigInt, node)),
        }))
    }
}

/// Checks a parameter list against LSB's limits (64 parameters when one has
/// a default; 255 signature entries, `extra` leading ones included).
pub(crate) fn check_params(
    params: &[PInfo],
    extra: usize,
    node: NodeRef,
    span: Span,
) -> Result<(), CompileError> {
    let has_mask = params.iter().any(|p| p.default.is_some());
    let limit = if has_mask {
        MAX_PARAMS_WITH_DEFAULTS
    } else {
        MAX_ARITY
    };
    let total = params.len() + usize::from(has_mask) + extra;
    if params.len() > limit || total > MAX_ARITY {
        return Err(CompileError::TooManyParams {
            node,
            span,
            limit: u32::try_from(limit.min(MAX_ARITY.saturating_sub(extra))).unwrap_or(0),
        });
    }
    Ok(())
}

/// Whether a function or closure with these effects is a generator: its
/// calls make coroutines (LSB §5.13). `ASYNC` alone is not: coroutines are
/// stackful, so an async function runs on its caller's task and its `await`s
/// suspend that task.
pub(crate) fn is_generator(effects: Effects) -> bool {
    effects.contains(Effects::YIELD)
}

/// The `i64` an integer literal denotes, if it has one.
pub(crate) fn int_value(i: hir_lang::IntLit) -> Option<i64> {
    if i.negative {
        if i.value <= 1u64 << 63 {
            Some((i.value as i64).wrapping_neg())
        } else {
            None
        }
    } else {
        i64::try_from(i.value).ok()
    }
}

/// The LSB signature of each hook (LSB §5.8): operand count, and whether it
/// returns a value.
fn hook_shape(h: Hook) -> (usize, bool) {
    match h {
        Hook::Neg
        | Hook::BitNot
        | Hook::Truthy
        | Hook::Iter
        | Hook::Len
        | Hook::Spawn
        | Hook::Abs => (1, true),
        Hook::SetIndex | Hook::SetProp => (3, false),
        Hook::CallShape => (3, true),
        _ => (2, true),
    }
}

/// Compiles a unit.
pub(crate) fn compile<L: Lookup>(
    hir: &Hir,
    names: &L,
    opts: &Options,
    locator: Option<&dyn Locate>,
) -> Result<Compiled, CompileError> {
    let an = Analysis::new(hir);
    if let Some(item) = an.unsupported_item {
        let node = NodeRef::Item(item);
        return Err(CompileError::Unsupported {
            feature: Unsupported::Class,
            node,
            span: hir.origin(node).span,
        });
    }
    let mut mb = ModuleBuilder::new();
    let map = mb.add_type(TypeDef::Map {
        key: ValType::Dyn,
        value: ValType::Dyn,
    });
    let cell = mb.add_type(TypeDef::Cell(ValType::Dyn));
    let iter = mb.add_type(TypeDef::Iter {
        key: ValType::Dyn,
        value: ValType::Dyn,
    });
    let file = mb.string(opts.file());
    let binders = hir.count(hir_lang::IdKind::Binder);
    let mut cx = Cx {
        hir,
        names,
        opts,
        locator,
        mb,
        an,
        types: Types { map, cell, iter },
        fns: BTreeMap::new(),
        globals: BTreeMap::new(),
        imports: BTreeMap::new(),
        jobs: VecDeque::new(),
        php_key: None,
        slots: alloc::vec![(u32::MAX, Slot::Global(GlobalId(0))); binders],
        epoch: 0,
        emitted: 0,
        origins: BTreeMap::new(),
        closures: 0,
        statics: 0,
        file,
    };

    // Hooks bound to host functions.
    for (hook, module, name) in opts.hooks() {
        let (arity, result) = hook_shape(*hook);
        let params = alloc::vec![ValType::Dyn; arity];
        let results: &[ValType] = if result { &[ValType::Dyn] } else { &[] };
        let sig = cx.mb.func_type(&params, results);
        let imp = cx.mb.import(module, name, sig);
        cx.mb.hook(*hook, Callee::Import(imp));
    }

    declare_functions(&mut cx)?;
    let mut prelude = declare_globals(&mut cx)?;
    let root = hir.root();
    let body = match hir.item(root).kind {
        ItemKind::Module { body, .. } => body,
        _ => None,
    };

    // The start function: initializers, defaults evaluated once, nested
    // module bodies, and (in `Start` mode) the body.
    let start_body = matches!(opts.body(), BodyMode::Start) && body.is_some();
    let result = if start_body {
        Some(cx.mb.global("<result>", ValType::Dyn, true, None))
    } else {
        None
    };
    prelude |= start_body;
    let start = if prelude {
        let f = cx.mb.function("<start>", &[], &[]);
        let id = f.id();
        cx.jobs.push_back(Job::Start { f, result });
        Some(id)
    } else {
        None
    };
    let entry = {
        let f = cx.mb.function("<entry>", &[], &[ValType::Dyn]);
        let id = f.id();
        if matches!(opts.body(), BodyMode::Entry) {
            cx.jobs.push_back(Job::Entry { f });
        } else {
            cx.jobs.push_back(Job::Getter { f, global: result });
        }
        id
    };

    while let Some(job) = cx.jobs.pop_front() {
        crate::codegen::run_job(&mut cx, job)?;
    }

    if let Some(s) = start {
        cx.mb.set_start(s);
    }
    cx.mb.export("<entry>", ExportItem::Func(entry));
    // Root-level functions, under their names (the first of a name wins).
    let mut exported: BTreeSet<String> = BTreeSet::new();
    if let ItemKind::Module { items, .. } = hir.item(root).kind {
        for &item in hir.list(items) {
            if let Some(info) = cx.fns.get(&item) {
                if let Some(callable) = info.callable {
                    if !info.name.is_empty()
                        && !exported.contains(&info.name)
                        && info.name != "<entry>"
                    {
                        cx.mb.export(&info.name, ExportItem::Func(callable));
                        let _ = exported.insert(info.name.clone());
                    }
                }
            }
        }
    }
    let functions: Vec<(ItemId, FuncId)> = cx
        .fns
        .iter()
        .filter_map(|(&item, info)| info.callable.map(|b| (item, b)))
        .collect();
    let module = cx.mb.finish()?;
    let count = module.functions().len();
    let mut origins: Vec<Vec<NodeRef>> = Vec::with_capacity(count);
    for i in 0..count {
        let i = u32::try_from(i).unwrap_or(u32::MAX);
        origins.push(cx.origins.remove(&i).unwrap_or_default());
    }
    Ok(Compiled {
        module,
        entry,
        start,
        result,
        functions,
        origins,
    })
}

/// Declares every function item's callable (so calls may refer to any
/// function, in any order), a generator's coroutine body, and the
/// once-evaluated default globals.
fn declare_functions<L: Lookup>(cx: &mut Cx<'_, L>) -> Result<(), CompileError> {
    let fns = cx.an.fns.clone();
    for item in fns {
        let node = NodeRef::Item(item);
        let it = *cx.hir.item(item);
        let ItemKind::Fn(def) = it.kind else {
            continue;
        };
        let params: Vec<PInfo> = cx
            .hir
            .list(def.params)
            .iter()
            .map(|&p| PInfo::of(cx.hir, p))
            .collect();
        if params.iter().any(|p| p.kind == ParamKind::Receiver) {
            return Err(cx.unsupported(Unsupported::Class, node));
        }
        check_params(&params, 0, node, cx.span(node))?;
        let name = it.name.map(|n| cx.text(n.sym)).unwrap_or_default();
        let has_mask = params.iter().any(|p| p.default.is_some());
        let mut sig: Vec<ValType> = params.iter().map(|p| p.reg_type(&cx.types)).collect();
        if has_mask {
            sig.push(ValType::I64);
        }
        let mut once = alloc::vec![None; params.len()];
        let (callable, gen_body) = if def.body.is_some() {
            if def.defaults == DefaultEval::Once {
                for (i, p) in params.iter().enumerate() {
                    if p.default.is_some() {
                        let mut gname = name.clone();
                        gname.push_str("$default");
                        if let Some(slot) = once.get_mut(i) {
                            *slot = Some(cx.mb.global(&gname, ValType::Dyn, true, None));
                        }
                    }
                }
            }
            let fname = if name.is_empty() {
                String::from("<fn>")
            } else {
                name.clone()
            };
            let list = cx.param_list(&params);
            let mut f = cx.mb.function(&fname, &sig, &[ValType::Dyn]);
            f.set_params(list);
            let id = f.id();
            if is_generator(def.effects) {
                let mut gname = fname;
                gname.push_str("$gen");
                let g = cx.mb.function(&gname, &sig, &[ValType::Dyn]);
                let gid = g.id();
                cx.jobs.push_back(Job::Body { item, f: g });
                cx.jobs.push_back(Job::GenEntry {
                    f,
                    body: gid,
                    caps: Vec::new(),
                    sig: sig.clone(),
                    node,
                });
                (Some(id), Some(gid))
            } else {
                cx.jobs.push_back(Job::Body { item, f });
                (Some(id), None)
            }
        } else {
            (None, None)
        };
        let _ = cx.fns.insert(
            item,
            FnInfo {
                callable,
                gen_body,
                params,
                sig,
                has_mask,
                once,
                name,
            },
        );
    }
    Ok(())
}

/// Declares globals and constants; returns whether any needs code in the
/// start function (a non-literal initializer, a once-evaluated default, or
/// a nested module body).
fn declare_globals<L: Lookup>(cx: &mut Cx<'_, L>) -> Result<bool, CompileError> {
    let mut code = cx.fns.values().any(|f| f.once.iter().any(Option::is_some));
    let items = cx.an.globals.clone();
    for item in items {
        let it = *cx.hir.item(item);
        let (init, mutable) = match it.kind {
            ItemKind::Global { init, mutable, .. } => (init, mutable),
            ItemKind::Const { value, .. } => (value, false),
            _ => continue,
        };
        let name = it.name.map(|n| cx.text(n.sym)).unwrap_or_default();
        let lit = init.and_then(|e| match *cx.hir.expr(e) {
            Expr::Lit(l) => Some((e, l)),
            _ => None,
        });
        let g = match (init, lit) {
            // Shared by reference: the start function puts a reference here.
            _ if cx.an.cell_globals.contains(&item) => {
                code = true;
                cx.mb.global(&name, ValType::Dyn, true, None)
            }
            (None, _) => cx.mb.global(&name, ValType::Dyn, mutable, None),
            (Some(_), Some((e, l))) => {
                let k = cx.lit_const(l, NodeRef::Expr(e))?;
                let k = k.map(|k| cx.mb.constant(k));
                cx.mb.global(&name, ValType::Dyn, mutable, k)
            }
            (Some(_), None) => {
                code = true;
                // Initialized by the start function, so writable there.
                cx.mb.global(&name, ValType::Dyn, true, None)
            }
        };
        let _ = cx.globals.insert(item, g);
    }
    // Nested modules with bodies run in the start function.
    let nested = !cx.an.module_bodies.is_empty();
    Ok(code || nested)
}

#[cfg(test)]
mod tests {
    use hir_lang::IntLit;

    use super::int_value;

    #[test]
    fn integer_literals_in_the_dynamic_range() {
        assert_eq!(int_value(IntLit::signed(i64::MIN)), Some(i64::MIN));
        assert_eq!(int_value(IntLit::signed(i64::MAX)), Some(i64::MAX));
        assert_eq!(int_value(IntLit::new(1 << 63)), None);
        assert_eq!(
            int_value(IntLit {
                value: (1 << 63) + 1,
                negative: true,
                suffix: None
            }),
            None
        );
        assert_eq!(int_value(IntLit::new(0)), Some(0));
    }
}
