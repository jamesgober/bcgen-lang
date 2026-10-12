//! Declares the unit's classes in the module: a struct type per class and
//! interface, a token global per class and interface, storage for static
//! properties and constants, a function per method (per class, for a mixin's
//! methods), and the synthetic functions every struct carries (see
//! [`crate::class`]). Bodies are generated later from the job queue.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use bytecode_lang::{Field, FuncId, GlobalId, Method, StructDef, TypeDef, ValType};
use hir_lang::{DefaultEval, Expr, ItemId, ItemKind, NodeRef, ParamKind, Vis};
use intern_lang::Lookup;

use crate::class::{CKind, ClassId, ClassTable, Ns, lsb_name};
use crate::error::{ClassProblem, CompileError, Unsupported};
use crate::unit::{ClassJob, ClassRt, Cx, FnInfo, FnKey, Job, PInfo, check_params, is_generator};

/// Declares every class, interface, and mixin member of the unit.
pub(crate) fn declare_classes<L: Lookup>(cx: &mut Cx<'_, L>) -> Result<(), CompileError> {
    let items = cx.an.classes.clone();
    if items.is_empty() {
        return Ok(());
    }
    let limit = cx.opts.max_instructions();
    let mut emitted = cx.emitted;
    let table = ClassTable::build(cx.hir, cx.names, &items, &mut |n| {
        emitted = emitted.saturating_add(n);
        if emitted > limit {
            Err(CompileError::BudgetExceeded { limit })
        } else {
            Ok(())
        }
    })?;
    cx.emitted = emitted;
    cx.ct = table;
    let n = cx.ct.len();
    cx.crt = alloc::vec![ClassRt::default(); n];
    let mut registry = false;
    for c in 0..n {
        let Some(d) = cx.ct.classes.get(c) else {
            continue;
        };
        if d.kind == CKind::Mixin {
            continue;
        }
        let ty = cx.mb.reserve_type();
        let mut gname = d.lsb.clone();
        gname.push_str("::class");
        let token = cx.mb.global(&gname, ValType::Dyn, true, None);
        if let Some(rt) = cx.crt.get_mut(c) {
            rt.ty = Some(ty);
            rt.token = Some(token);
        }
        registry = true;
    }
    if registry {
        cx.registry = Some(cx.mb.global("<classes>", ValType::Dyn, true, None));
    }
    for c in 0..n {
        let c = ClassId::try_from(c).unwrap_or(ClassId::MAX);
        declare_storage(cx, c)?;
    }
    for c in 0..n {
        let c = ClassId::try_from(c).unwrap_or(ClassId::MAX);
        declare_methods(cx, c)?;
    }
    let mut accessors: BTreeMap<GlobalId, FuncId> = BTreeMap::new();
    for c in 0..n {
        let c = ClassId::try_from(c).unwrap_or(ClassId::MAX);
        define_struct(cx, c, &mut accessors)?;
    }
    Ok(())
}

/// The text of a symbol.
fn text<L: Lookup>(cx: &Cx<'_, L>, sym: hir_lang::Symbol) -> String {
    cx.text(sym)
}

/// Globals for the static properties (a reference each, made by the start
/// function) and constants of class `c`, mixin copies included.
fn declare_storage<L: Lookup>(cx: &mut Cx<'_, L>, c: ClassId) -> Result<(), CompileError> {
    let Some(d) = cx.ct.get(c) else {
        return Ok(());
    };
    if d.kind == CKind::Mixin {
        return Ok(());
    }
    let lsb = d.lsb.clone();
    let statics = d.statics.clone();
    let consts = d.consts.clone();
    for s in statics {
        let mut name = lsb.clone();
        name.push_str("::$");
        name.push_str(&text(cx, s.name));
        let g = cx.mb.global(&name, ValType::Dyn, true, None);
        let _ = cx.member_globals.insert((c, s.item), g);
    }
    for k in consts {
        let mut name = lsb.clone();
        name.push_str("::");
        name.push_str(&text(cx, k.name));
        let value = match cx.hir.item(k.item).kind {
            ItemKind::Const { value, .. } => value,
            _ => None,
        };
        let lit = value.and_then(|e| match *cx.hir.expr(e) {
            Expr::Lit(l) => Some((e, l)),
            _ => None,
        });
        let g = match lit {
            Some((e, l)) => {
                let konst = cx.lit_const(l, NodeRef::Expr(e))?;
                let konst = konst.map(|k| cx.mb.constant(k));
                cx.mb.global(&name, ValType::Dyn, false, konst)
            }
            // Initialized by the start function (or nil, for an interface
            // constant without a value).
            None => cx.mb.global(&name, ValType::Dyn, true, None),
        };
        let _ = cx.member_globals.insert((c, k.item), g);
    }
    Ok(())
}

/// The function of every method class `c` holds (its own and its mixins'),
/// declared once per method item (aliases share it).
fn declare_methods<L: Lookup>(cx: &mut Cx<'_, L>, c: ClassId) -> Result<(), CompileError> {
    let Some(d) = cx.ct.get(c) else {
        return Ok(());
    };
    if d.kind != CKind::Class {
        return Ok(());
    }
    let lsb = d.lsb.clone();
    let methods = d.methods.clone();
    let destructor = cx.opts.destructor().map(String::from);
    for m in methods {
        let node = NodeRef::Item(m.item);
        let mname = text(cx, m.name);
        if destructor.as_deref() == Some(mname.as_str()) && m.body {
            let ItemKind::Fn(def) = cx.hir.item(m.item).kind else {
                continue;
            };
            if m.is_static || cx.hir.list(def.params).len() != 1 {
                return Err(CompileError::Class {
                    problem: ClassProblem::BadDestructor,
                    node,
                    span: cx.span(node),
                });
            }
            if m.vis != Vis::Private {
                cx.destructor = Some(lsb_name(Ns::Method, &mname, None));
            }
        }
        if !m.body || cx.methods.contains_key(&(c, m.item)) {
            continue;
        }
        declare_method(cx, c, &lsb, m.item)?;
    }
    Ok(())
}

/// One method of class `c`: its function (a generator's entry and body), as
/// a function item is declared, with the receiver first.
fn declare_method<L: Lookup>(
    cx: &mut Cx<'_, L>,
    c: ClassId,
    lsb: &str,
    item: ItemId,
) -> Result<(), CompileError> {
    let node = NodeRef::Item(item);
    let it = *cx.hir.item(item);
    let ItemKind::Fn(def) = it.kind else {
        return Ok(());
    };
    let hir = cx.hir;
    let mut params: Vec<PInfo> = hir
        .list(def.params)
        .iter()
        .map(|&p| PInfo::of(hir, p))
        .collect();
    if params.iter().skip(1).any(|p| p.kind == ParamKind::Receiver) {
        return Err(cx.unsupported(Unsupported::Class, node));
    }
    let hidden_recv = params.first().is_none_or(|p| p.kind != ParamKind::Receiver);
    if hidden_recv {
        params.insert(0, PInfo::hidden_receiver());
    }
    check_params(&params, 0, node, cx.span(node))?;
    let mut name = String::from(lsb);
    name.push_str("::");
    if let Some(n) = it.name {
        name.push_str(&text(cx, n.sym));
    }
    let has_mask = params.iter().any(|p| p.default.is_some());
    let mut sig: Vec<ValType> = params.iter().map(|p| p.reg_type(&cx.types)).collect();
    if has_mask {
        sig.push(ValType::I64);
    }
    let mut once = alloc::vec![None; params.len()];
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
    let list = cx.param_list(&params);
    let mut f = cx.mb.function(&name, &sig, &[ValType::Dyn]);
    f.set_params(list);
    let id = f.id();
    let key = FnKey::Method(c, item);
    let gen_body = if is_generator(def.effects) {
        let mut gname = name.clone();
        gname.push_str("$gen");
        let g = cx.mb.function(&gname, &sig, &[ValType::Dyn]);
        let gid = g.id();
        cx.jobs.push_back(Job::Body { key, f: g });
        cx.jobs.push_back(Job::GenEntry {
            f,
            body: gid,
            caps: Vec::new(),
            sig: sig.clone(),
            node,
        });
        Some(gid)
    } else {
        cx.jobs.push_back(Job::Body { key, f });
        None
    };
    let _ = cx.methods.insert(
        (c, item),
        FnInfo {
            callable: Some(id),
            gen_body,
            params,
            sig,
            has_mask,
            once,
            name,
            class: Some(c),
            hidden_recv,
        },
    );
    Ok(())
}

/// A synthetic function of class `c`, queued for generation.
fn synthetic<L: Lookup>(
    cx: &mut Cx<'_, L>,
    name: &str,
    params: &[ValType],
    what: ClassJob,
) -> FuncId {
    let f = cx.mb.function(name, params, &[ValType::Dyn]);
    let id = f.id();
    cx.jobs.push_back(Job::Class { f, what });
    id
}

/// The accessor returning global `g` (shared by every struct naming it).
fn accessor<L: Lookup>(
    cx: &mut Cx<'_, L>,
    accessors: &mut BTreeMap<GlobalId, FuncId>,
    g: GlobalId,
    name: &str,
) -> FuncId {
    if let Some(&f) = accessors.get(&g) {
        return f;
    }
    let f = synthetic(cx, name, &[ValType::Dyn], ClassJob::Accessor(g));
    let _ = accessors.insert(g, f);
    f
}

/// The shared marker function interface markers name.
fn marker<L: Lookup>(cx: &mut Cx<'_, L>) -> FuncId {
    if let Some(f) = cx.marker {
        return f;
    }
    let f = synthetic(cx, "<marker>", &[ValType::Dyn], ClassJob::Marker);
    cx.marker = Some(f);
    f
}

/// Defines class `c`'s struct type: its layout, its parent, and its method
/// table (see the naming table in [`crate::class`]).
fn define_struct<L: Lookup>(
    cx: &mut Cx<'_, L>,
    c: ClassId,
    accessors: &mut BTreeMap<GlobalId, FuncId>,
) -> Result<(), CompileError> {
    let Some(rt) = cx.crt.get(c as usize).copied() else {
        return Ok(());
    };
    let Some(ty) = rt.ty else {
        return Ok(());
    };
    let Some(d) = cx.ct.get(c).cloned() else {
        return Ok(());
    };
    let mut table: BTreeMap<String, FuncId> = BTreeMap::new();
    let private = |vis: Vis| (vis == Vis::Private).then_some(d.lsb.as_str());
    for m in d.methods.iter().filter(|m| m.body) {
        let Some(f) = cx.methods.get(&(c, m.item)).and_then(|i| i.callable) else {
            continue;
        };
        let name = lsb_name(Ns::Method, &text(cx, m.name), private(m.vis));
        let _ = table.entry(name).or_insert(f);
    }
    let mut alloc_name = d.lsb.clone();
    alloc_name.push_str("::new");
    let alloc = synthetic(cx, &alloc_name, &[ValType::Dyn], ClassJob::Alloc(c));
    let _ = table.insert(String::from("::new"), alloc);
    let mut test_name = d.lsb.clone();
    test_name.push_str("::test");
    let test = synthetic(
        cx,
        &test_name,
        &[ValType::Dyn, ValType::Dyn],
        ClassJob::Test(c),
    );
    let _ = table.insert(String::from("::test"), test);
    let mut name_fn = d.lsb.clone();
    name_fn.push_str("::class");
    let name = synthetic(cx, &name_fn, &[ValType::Dyn], ClassJob::Name(c));
    let _ = table.insert(String::from("::class"), name);
    if let Some(rt) = cx.crt.get_mut(c as usize) {
        rt.alloc = Some(alloc);
    }
    let ifaces = cx.ct.ifaces.get(c as usize).cloned().unwrap_or_default();
    for &i in &ifaces {
        let Some(id) = cx.ct.get(i) else { continue };
        let mut name = String::from("::is ");
        name.push_str(&id.lsb);
        let f = marker(cx);
        let _ = table.insert(name, f);
    }
    for s in &d.statics {
        let Some(&g) = cx.member_globals.get(&(c, s.item)) else {
            continue;
        };
        let name = lsb_name(Ns::Static, &text(cx, s.name), private(s.vis));
        let fname = alloc::format!("{}::{name}", d.lsb);
        let f = accessor(cx, accessors, g, &fname);
        let _ = table.insert(name, f);
    }
    // Constants: the class's own, then those of the interfaces it
    // implements (struct inheritance does not reach interfaces).
    let mut consts: Vec<(ClassId, crate::class::ItemM)> =
        d.consts.iter().map(|k| (c, *k)).collect();
    for &i in &ifaces {
        if i == c {
            continue;
        }
        if let Some(id) = cx.ct.get(i) {
            consts.extend(id.consts.iter().map(|k| (i, *k)));
        }
    }
    for (holder, k) in consts {
        let Some(&g) = cx.member_globals.get(&(holder, k.item)) else {
            continue;
        };
        let holder_lsb = cx.ct.get(holder).map(|h| h.lsb.clone()).unwrap_or_default();
        let private_in = (k.vis == Vis::Private).then_some(holder_lsb.as_str());
        let name = lsb_name(Ns::Const, &text(cx, k.name), private_in);
        if table.contains_key(&name) {
            continue;
        }
        let fname = alloc::format!("{holder_lsb}::{name}");
        let f = accessor(cx, accessors, g, &fname);
        let _ = table.insert(name, f);
    }
    let layout = cx.ct.layout.get(c as usize).cloned().unwrap_or_default();
    let fields: Vec<Field> = layout
        .iter()
        .map(|s| Field {
            name: cx.mb.string(&s.lsb),
            ty: ValType::Dyn,
        })
        .collect();
    let methods: Vec<Method> = table
        .into_iter()
        .map(|(name, func)| Method {
            name: cx.mb.string(&name),
            func,
        })
        .collect();
    cx.emitted = cx
        .emitted
        .saturating_add((fields.len() + methods.len()) as u64);
    let limit = cx.opts.max_instructions();
    if cx.emitted > limit {
        return Err(CompileError::BudgetExceeded { limit });
    }
    let parent = d
        .parent
        .and_then(|p| cx.crt.get(p as usize))
        .and_then(|r| r.ty);
    let name = cx.mb.string(&d.lsb);
    cx.mb.define_type(
        ty,
        TypeDef::Struct(StructDef {
            name,
            parent,
            fields,
            methods,
        }),
    );
    Ok(())
}
