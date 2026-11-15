// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Give the MIR lowering's machine word the wasm32 width.
//!
//! The MIR lowering models address and index arithmetic in a 64-bit machine
//! word: `ptrtoint ptr to i64`, `copy i64` of a `usize`, `mul`/`add i64` with
//! `const i64` strides, `inttoptr i64`, and `i64` loads/stores of word slots.
//! On a native target that word IS `usize`. In a wasm32 session `usize` and
//! pointers are 32 bits, so the same instructions cross widths (`copy i64` of
//! a `u32`), which the wasm lane refuses, or over-read memory (`load i64` of a
//! four-byte `usize` slot), which it cannot see: its operand gate checks value
//! types, not access extents.
//!
//! This pass partitions each function's `i64` values into classes joined by
//! the operations that must share one width: a `BinOp`/`UnOp`/`Overflow`/
//! `ICmp`/`Select` over them, a same-type `Copy`, a branch argument and its
//! block parameter, and the loads and stores through one `Alloca`. A class is
//! a WORD when it touches a pointer-width fact: a `ptrtoint`/`inttoptr`, a
//! 32-bit integer operand, a `copy` from or to a 32-bit integer, a GEP index,
//! a memory byte count, or a 32-bit call parameter, return, block parameter or
//! aggregate lane. It is GENUINE when it touches a Rust-typed `i64` fact — an
//! `i64` signature parameter or result, call argument or result, aggregate
//! field, an operand of a bit operation whose value depends on the width
//! (`ctlz`/`cttz`/`bswap`/`bitreverse`/`rotl`/`rotr`, which the MIR lowering
//! emits at the receiver's own Rust type) — or any use this pass does not
//! model. A WORD class is retyped to `i32`: exactly the instructions the
//! lowering emits for its word on a 32-bit target, so its arithmetic wraps,
//! compares and extends at the width rustc's layout gives `usize`. A class
//! carrying both facts is refused by name, never guessed; a class with neither
//! keeps its `i64`. A class reached only through a computed (`inttoptr`) field
//! address and constants — an iterator model's `usize` count or cursor —
//! therefore carries no fact here, so the MIR lowering states such a field's
//! width itself (`usize_field_ty`).
//!
//! The bridge's own `__trustcg_*` helpers take their lengths as native words
//! too. [`helper_word_params`] names those parameters; they are narrowed in a
//! helper's declaration and in its definition alike, so the linked wasm
//! signatures agree.
//!
//! The pass grants no authority: the rewritten module is checked by the wasm
//! lane's operand-width gate and the CFG structural checker like any other,
//! and its evidence is the wasm32 execution differential against LLVM.

use std::collections::{HashMap, HashSet};

use trust_ir::{
    BinOp, BlockId, CastOp, Constant, FuncId, FuncTy, FuncTyId, Function, IdSpaceExhausted, Inst,
    Module, Ty, UnOp, ValueId,
};

/// The parameters of a bridge-synthesized `__trustcg_*` helper that carry a
/// `usize` (a length, count or index) in the native `i64` word. Every other
/// parameter keeps its declared type (an `array_fill` value, a `slice_cmp`
/// signedness flag); a helper family absent here keeps its `i64` words and
/// fails closed at the first word it meets.
fn helper_word_params(symbol: &str) -> &'static [usize] {
    let family = |prefix: &str| symbol.starts_with(prefix);
    if family("__trustcg_vec_sort_") || family("__trustcg_slice_contains_") {
        &[1]
    } else if family("__trustcg_array_fill_") {
        &[2]
    } else if family("__trustcg_slice_eq_") || family("__trustcg_slice_cmp_") {
        &[1, 3]
    } else if family("__trustcg_slice_reverse_") {
        &[1, 2]
    } else {
        &[]
    }
}

/// Retype every WORD class of every function in `module` to `i32`.
pub(crate) fn narrow_native_words(module: &mut Module) -> Result<(), String> {
    narrow_native_words_through(module, Module::intern_func_type)
}

/// [`narrow_native_words`] with the func-type table door its helper
/// signatures are interned through passed in ([`narrow_helper_signatures`]).
/// Production passes `Module::intern_func_type`, whose one refusal
/// ([`IdSpaceExhausted`]) needs a table that already holds id `u32::MAX`, i.e.
/// 2^32 rows; a unit test passes a door that refuses, so the refusal is
/// observed at this pass's boundary, the one the wasm32 lane calls.
///
/// A door refusal ends the pass with its `[TCG-IR-ID-EXHAUSTED]` error before
/// any function body is retyped; helpers before the refused one may already
/// be narrowed, and the wasm32 lane refuses the codegen unit on any error.
fn narrow_native_words_through(
    module: &mut Module,
    intern: impl FnMut(&mut Module, FuncTy) -> Result<FuncTyId, IdSpaceExhausted>,
) -> Result<(), String> {
    // A helper family outside [`helper_word_params`] (the BTreeMap, `vec_*`
    // and `slice_repeat` families) bakes in 64-bit layouts or
    // needs `alloc`/`std`; it is not ported, so a module naming one is refused.
    if let Some(f) = module
        .functions
        .iter()
        .find(|f| f.name.starts_with("__trustcg_") && helper_word_params(&f.name).is_empty())
    {
        return Err(format!(
            "[TCG-WASM32-HELPER] `{}`: this bridge helper family is modeled for 64-bit targets \
             only and is not ported to wasm32; failing closed",
            f.name
        ));
    }
    check_c_memory_libcalls(module)?;
    narrow_helper_signatures(module, intern)?;
    let sigs: HashMap<FuncId, (Vec<Ty>, Vec<Ty>)> = module
        .functions
        .iter()
        .filter_map(|f| {
            let ft = module.func_type(f.ty)?;
            Some((f.id, (ft.params.clone(), ft.returns.clone())))
        })
        .collect();
    for index in 0..module.functions.len() {
        let func = &module.functions[index];
        if func.blocks.is_empty() {
            continue;
        }
        // The wasm lane's own typing, so every class is decided on exactly
        // the types its operand-width gate will check.
        let types = trust_cg_codegen::wasm::value_types(module, func)
            .map_err(|err| format!("[TCG-WASM32-WORD] `{}`: {err}", func.name))?;
        let classes = Classes::gather(module, func, &types, &sigs);
        let words = classes.resolve(&func.name)?;
        if !words.is_empty() {
            retype(&mut module.functions[index], &types, &words)?;
        }
    }
    Ok(())
}

/// Refuse a declaration of a C bulk-memory routine whose type is not its C
/// prototype on wasm32, `(i32, i32, i32) -> i32` (`void *memcpy(void *, const
/// void *, size_t)`, `memmove`, `void *memset(void *, int, size_t)`, `int
/// memcmp(const void *, const void *, size_t)`). A wasm import is typed, and
/// wasm-ld binds a call whose declared type differs from the definition's to a
/// synthesized stub that traps (reporting only a warning), so a mismatched
/// declaration would link and trap at run time.
///
/// A prototype slot accepts exactly the types the wasm lane carries as a
/// 32-bit word: an opaque or typed pointer or reference (a user `extern "C"`
/// declaration arrives with `*mut u8`/`*const u8` pointers), `i32`/`u32`, and
/// `isize`/`usize`. Each of these is an `i32` in the import's wasm type.
fn check_c_memory_libcalls(module: &Module) -> Result<(), String> {
    let word = |ty: &Ty| {
        matches!(
            ty,
            Ty::Ptr
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::I32
                | Ty::U32
                | Ty::Isize
                | Ty::Usize
        )
    };
    for func in module.functions.iter().filter(|f| f.blocks.is_empty()) {
        if !matches!(
            func.name.as_str(),
            "memcpy" | "memmove" | "memset" | "memcmp"
        ) {
            continue;
        }
        let exact = module.func_type(func.ty).is_some_and(|ft| {
            !ft.is_vararg
                && ft.params.len() == 3
                && ft.params.iter().all(word)
                && ft.returns.len() == 1
                && ft.returns.iter().all(word)
        });
        if !exact {
            return Err(format!(
                "[TCG-WASM32-LIBCALL] `{}` is declared with a type other than its C prototype \
                 `(i32, i32, i32) -> i32`; wasm-ld would bind its calls to a trapping stub, so \
                 failing closed",
                func.name
            ));
        }
    }
    Ok(())
}

/// Narrow the [`helper_word_params`] of every helper declaration and
/// definition in `module`: the signature, and a definition's entry parameters.
/// Each narrowed signature is interned through `intern`
/// (`Module::intern_func_type` in production; see
/// [`narrow_native_words_through`]).
///
/// A refusal is `[TCG-IR-ID-EXHAUSTED]`: the module's FuncTyId space is full,
/// which is not the unported-family refusal `[TCG-WASM32-HELPER]`. The helper
/// it names is left as declared; helpers before it may already be narrowed,
/// and the wasm32 lane refuses the whole module on this error.
fn narrow_helper_signatures(
    module: &mut Module,
    mut intern: impl FnMut(&mut Module, FuncTy) -> Result<FuncTyId, IdSpaceExhausted>,
) -> Result<(), String> {
    for index in 0..module.functions.len() {
        let mask = helper_word_params(&module.functions[index].name);
        let Some(declared) = module.func_type(module.functions[index].ty).cloned() else {
            continue;
        };
        let mut narrowed = declared.clone();
        for &i in mask {
            if let Some(t @ Ty::I64) = narrowed.params.get_mut(i) {
                *t = Ty::I32;
            }
        }
        if narrowed == declared {
            continue;
        }
        let ty = intern(module, narrowed).map_err(|refusal| {
            format!(
                "[TCG-IR-ID-EXHAUSTED] `{}`: narrowing its wasm32 word parameters needs a \
                 func-type row the trust-ir module refused ({refusal}); failing closed",
                module.functions[index].name
            )
        })?;
        let func = &mut module.functions[index];
        func.ty = ty;
        let entry = func.entry;
        if let Some(block) = func.blocks.iter_mut().find(|b| b.id == entry) {
            for &i in mask {
                if let Some((_, t @ Ty::I64)) = block.params.get_mut(i) {
                    *t = Ty::I32;
                }
            }
        }
    }
    Ok(())
}

fn is_word_int(ty: &Ty) -> bool {
    matches!(ty, Ty::I32 | Ty::U32)
}

/// A unary operation whose result at `i32` differs from its result at `i64`
/// on the same low 32 bits, so retyping it would change the value.
fn width_sensitive_unop(op: UnOp) -> bool {
    matches!(op, UnOp::CtLz | UnOp::CtTz | UnOp::BSwap | UnOp::BitReverse)
}

/// The type of lane `field` of an aggregate type, when it is a plain one.
fn lane_ty(module: &Module, ty: &Ty, field: u32) -> Option<Ty> {
    match ty {
        Ty::Array(elem, _) => module.ty(*elem).cloned(),
        Ty::Tuple(tys) => tys.get(field as usize).cloned(),
        Ty::Struct(id) => module
            .struct_def(*id)?
            .fields
            .get(field as usize)
            .map(|f| f.ty.clone()),
        _ => None,
    }
}

/// The union-find over one function's `i64` values, with each root's facts.
#[derive(Default)]
struct Classes {
    parent: HashMap<ValueId, ValueId>,
    word: HashSet<ValueId>,
    /// Why each root became a WORD (first reason), for conflict reports.
    word_reason: HashMap<ValueId, String>,
    /// A root's GENUINE fact, with the first reason it was recorded.
    genuine: HashMap<ValueId, String>,
}

impl Classes {
    fn find(&mut self, v: ValueId) -> ValueId {
        let p = *self.parent.entry(v).or_insert(v);
        if p == v {
            return v;
        }
        let root = self.find(p);
        self.parent.insert(v, root);
        root
    }

    fn union(&mut self, a: ValueId, b: ValueId) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        self.parent.insert(rb, ra);
        if self.word.remove(&rb) {
            self.word.insert(ra);
        }
        if let Some(reason) = self.word_reason.remove(&rb) {
            self.word_reason.entry(ra).or_insert(reason);
        }
        if let Some(reason) = self.genuine.remove(&rb) {
            self.genuine.entry(ra).or_insert(reason);
        }
    }

    fn mark_word(&mut self, v: ValueId, why: impl FnOnce() -> String) {
        let r = self.find(v);
        self.word.insert(r);
        self.word_reason.entry(r).or_insert_with(why);
    }

    fn mark_genuine(&mut self, v: ValueId, why: impl FnOnce() -> String) {
        let r = self.find(v);
        self.genuine.entry(r).or_insert_with(why);
    }

    fn gather(
        module: &Module,
        func: &Function,
        types: &HashMap<ValueId, Ty>,
        sigs: &HashMap<FuncId, (Vec<Ty>, Vec<Ty>)>,
    ) -> Self {
        let mut c = Classes::default();
        let ty = |v: &ValueId| types.get(v);
        let is64 = |v: &ValueId| matches!(types.get(v), Some(Ty::I64));
        let is32 = |v: &ValueId| types.get(v).is_some_and(is_word_int);
        let params: HashMap<BlockId, &Vec<(ValueId, Ty)>> =
            func.blocks.iter().map(|b| (b.id, &b.params)).collect();
        let returns: &[Ty] = sigs.get(&func.id).map_or(&[], |s| &s.1);

        // Loads and stores through one `Alloca` (reached through
        // address-preserving copies) share the slot's width.
        let allocas: HashSet<ValueId> = func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter(|n| matches!(n.inst, Inst::Alloca { .. }))
            .filter_map(|n| n.results.first().copied())
            .collect();
        let mut ptr_src: HashMap<ValueId, ValueId> = HashMap::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let (
                Inst::Copy { operand, .. }
                | Inst::Cast {
                    op: CastOp::PtrToPtr,
                    operand,
                    ..
                },
                Some(r),
            ) = (&node.inst, node.results.first())
            {
                ptr_src.insert(*r, *operand);
            }
        }
        let alloca_of = |mut p: ValueId| -> Option<ValueId> {
            for _ in 0..64 {
                if allocas.contains(&p) {
                    return Some(p);
                }
                p = *ptr_src.get(&p)?;
            }
            None
        };
        let mut slot_rep: HashMap<ValueId, ValueId> = HashMap::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            let (ptr, v) = match (&node.inst, node.results.first()) {
                (
                    Inst::Load {
                        ty: Ty::I64, ptr, ..
                    },
                    Some(r),
                ) => (*ptr, *r),
                (
                    Inst::Store {
                        ty: Ty::I64,
                        ptr,
                        value,
                        ..
                    },
                    _,
                ) if is64(value) => (*ptr, *value),
                _ => continue,
            };
            if let Some(slot) = alloca_of(ptr) {
                let rep = *slot_rep.entry(slot).or_insert(v);
                c.union(rep, v);
            }
        }

        for (v, t) in params.get(&func.entry).into_iter().flat_map(|p| p.iter()) {
            if *t == Ty::I64 {
                c.mark_genuine(*v, || "a signature parameter".to_owned());
            }
        }
        // An `i64` operation's values share one class; a 32-bit integer among
        // its operands makes that class a word.
        let join = |c: &mut Classes, result: Option<ValueId>, operands: &[ValueId]| {
            let mut members = result
                .into_iter()
                .chain(operands.iter().copied().filter(is64));
            let Some(anchor) = members.next() else { return };
            for m in members {
                c.union(anchor, m);
            }
            if operands.iter().any(is32) {
                c.mark_word(anchor, || {
                    "a 32-bit integer operand of an i64 word operation".to_owned()
                });
            }
        };
        // A value crossing into a slot of type `to`.
        let cross = |c: &mut Classes, v: ValueId, to: &Ty, what: &str| {
            if !is64(&v) {
                return;
            }
            if is_word_int(to) {
                c.mark_word(v, || format!("a 32-bit {what}"));
            } else {
                c.mark_genuine(v, || format!("a {to:?} {what}"));
            }
        };
        let edge = |c: &mut Classes, target: &BlockId, args: &[ValueId]| {
            let Some(ps) = params.get(target) else { return };
            for (arg, (p, pt)) in args.iter().zip(ps.iter()) {
                match (is64(arg), *pt == Ty::I64) {
                    (true, true) => c.union(*arg, *p),
                    (false, true) if is32(arg) => {
                        c.mark_word(*p, || "a block parameter fed a 32-bit integer".to_owned());
                    }
                    (true, false) => cross(c, *arg, pt, "block parameter"),
                    _ => {}
                }
            }
        };
        for block in &func.blocks {
            for node in &block.body {
                let r0 = node.results.first().copied();
                // Operands this arm models; every other `i64` operand is GENUINE.
                let mut modeled: Vec<ValueId> = Vec::new();
                match &node.inst {
                    Inst::Const { ty: Ty::I64, .. } => {}
                    Inst::Copy {
                        ty: Ty::I64,
                        operand,
                    } => {
                        modeled.push(*operand);
                        match (ty(operand), r0) {
                            (Some(Ty::I64), Some(r)) => c.union(r, *operand),
                            (Some(t), Some(r)) if is_word_int(t) => {
                                c.mark_word(r, || format!("`copy i64` of a {t:?}"));
                            }
                            (t, Some(r)) => {
                                c.mark_genuine(r, || format!("`copy i64` of a {t:?}"));
                            }
                            _ => {}
                        }
                    }
                    Inst::Copy { ty: t, operand } if is_word_int(t) && is64(operand) => {
                        modeled.push(*operand);
                        c.mark_word(*operand, || format!("`copy {t:?}` of an i64"));
                    }
                    Inst::BinOp {
                        op: op @ (BinOp::RotL | BinOp::RotR),
                        ty: Ty::I64,
                        lhs,
                        rhs,
                    } => {
                        modeled.extend([*lhs, *rhs]);
                        join(&mut c, r0.filter(is64), &[*lhs, *rhs]);
                        c.mark_genuine(*lhs, || format!("an i64 `{op}` operand"));
                    }
                    Inst::BinOp {
                        ty: Ty::I64,
                        lhs,
                        rhs,
                        ..
                    }
                    | Inst::Overflow {
                        ty: Ty::I64,
                        lhs,
                        rhs,
                        ..
                    } => {
                        modeled.extend([*lhs, *rhs]);
                        join(&mut c, r0.filter(is64), &[*lhs, *rhs]);
                    }
                    Inst::ICmp {
                        ty: Ty::I64,
                        lhs,
                        rhs,
                        ..
                    } => {
                        modeled.extend([*lhs, *rhs]);
                        join(&mut c, None, &[*lhs, *rhs]);
                    }
                    Inst::UnOp {
                        op,
                        ty: Ty::I64,
                        operand,
                    } => {
                        modeled.push(*operand);
                        join(&mut c, r0.filter(is64), &[*operand]);
                        if width_sensitive_unop(*op) {
                            c.mark_genuine(*operand, || format!("an i64 `{op}` operand"));
                        }
                    }
                    Inst::Select {
                        ty: Ty::I64,
                        then_val,
                        else_val,
                        ..
                    } => {
                        modeled.extend([*then_val, *else_val]);
                        join(&mut c, r0.filter(is64), &[*then_val, *else_val]);
                    }
                    Inst::Cast {
                        op,
                        src_ty,
                        dst_ty,
                        operand,
                    } => {
                        modeled.push(*operand);
                        match (op, src_ty, dst_ty) {
                            (CastOp::PtrToInt, _, Ty::I64) => {
                                if let Some(r) = r0 {
                                    c.mark_word(r, || "a `ptrtoint` to i64".to_owned());
                                }
                            }
                            (CastOp::IntToPtr, Ty::I64, _) => {
                                c.mark_word(*operand, || "an `inttoptr` from i64".to_owned());
                            }
                            // Width changes whose other side may take either
                            // width; the retype turns a same-width one into a
                            // copy.
                            (CastOp::Trunc, Ty::I64, _)
                            | (CastOp::ZExt | CastOp::SExt, _, Ty::I64) => {}
                            _ => {
                                if src_ty == &Ty::I64 {
                                    c.mark_genuine(*operand, || format!("a {op:?} from i64"));
                                }
                                if let (Ty::I64, Some(r)) = (dst_ty, r0) {
                                    c.mark_genuine(r, || format!("a {op:?} to i64"));
                                }
                            }
                        }
                    }
                    Inst::Load { ty: Ty::I64, .. } => {}
                    Inst::Store {
                        ty: Ty::I64,
                        ptr,
                        value,
                        ..
                    } => {
                        modeled.push(*value);
                        let rep = alloca_of(*ptr).and_then(|s| slot_rep.get(&s).copied());
                        if let (true, Some(rep)) = (is32(value), rep) {
                            c.mark_word(rep, || "a slot stored a 32-bit integer".to_owned());
                        }
                    }
                    Inst::InsertField {
                        ty: agg,
                        field,
                        value,
                        ..
                    } => {
                        modeled.push(*value);
                        if let Some(lane) = lane_ty(module, agg, *field) {
                            cross(&mut c, *value, &lane, "aggregate lane");
                        }
                    }
                    Inst::GEP { indices, .. } => {
                        for i in indices {
                            modeled.push(*i);
                            if is64(i) {
                                c.mark_word(*i, || "a GEP index".to_owned());
                            }
                        }
                    }
                    Inst::MemCopy { bytes, .. } | Inst::MemSet { bytes, .. } => {
                        modeled.push(*bytes);
                        if is64(bytes) {
                            c.mark_word(*bytes, || "a memory byte count".to_owned());
                        }
                    }
                    Inst::ExtractElement { index, .. } | Inst::InsertElement { index, .. } => {
                        // The element index is width-agnostic in the wasm lane.
                        modeled.push(*index);
                    }
                    Inst::Alloca {
                        count: Some(count), ..
                    } => modeled.push(*count),
                    Inst::Call { callee, args } => {
                        if let Some((ps, _)) = sigs.get(callee) {
                            for (arg, p) in args.iter().zip(ps) {
                                modeled.push(*arg);
                                cross(&mut c, *arg, p, "call parameter");
                            }
                        }
                    }
                    Inst::CallIndirect { sig, args, .. } => {
                        if let Some(ft) = module.func_type(*sig) {
                            for (arg, p) in args.iter().zip(&ft.params) {
                                modeled.push(*arg);
                                cross(&mut c, *arg, p, "call parameter");
                            }
                        }
                    }
                    Inst::Return { values } => {
                        for (v, t) in values.iter().zip(returns) {
                            modeled.push(*v);
                            cross(&mut c, *v, t, "return");
                        }
                    }
                    Inst::Br { target, args } => {
                        modeled.extend(args.iter().copied());
                        edge(&mut c, target, args);
                    }
                    Inst::CondBr {
                        then_target,
                        then_args,
                        else_target,
                        else_args,
                        ..
                    } => {
                        modeled.extend(then_args.iter().chain(else_args).copied());
                        edge(&mut c, then_target, then_args);
                        edge(&mut c, else_target, else_args);
                    }
                    Inst::Switch {
                        value,
                        default,
                        default_args,
                        cases,
                        ..
                    } => {
                        modeled.push(*value);
                        modeled.extend(default_args.iter().copied());
                        edge(&mut c, default, default_args);
                        for case in cases {
                            modeled.extend(case.args.iter().copied());
                            edge(&mut c, &case.target, &case.args);
                        }
                    }
                    _ => {}
                }
                node.inst.visit_value_operands(|v| {
                    if is64(&v) && !modeled.contains(&v) {
                        c.mark_genuine(v, || format!("an operand of `{}`", inst_name(&node.inst)));
                    }
                });
                // A result this pass did not type as a word operation is a
                // Rust-typed `i64` (a call result, a field, an atomic, ...).
                let modeled_result = matches!(
                    node.inst,
                    Inst::Const { ty: Ty::I64, .. }
                        | Inst::Copy { ty: Ty::I64, .. }
                        | Inst::BinOp { ty: Ty::I64, .. }
                        | Inst::Overflow { ty: Ty::I64, .. }
                        | Inst::UnOp { ty: Ty::I64, .. }
                        | Inst::Select { ty: Ty::I64, .. }
                        | Inst::Load { ty: Ty::I64, .. }
                        | Inst::Cast { .. }
                );
                if !modeled_result {
                    for r in node.results.iter().filter(|r| is64(r)) {
                        c.mark_genuine(*r, || format!("a result of `{}`", inst_name(&node.inst)));
                    }
                }
            }
        }
        c
    }

    /// Every value of a WORD class, or the first class that is both a word
    /// and genuine.
    fn resolve(mut self, func: &str) -> Result<HashSet<ValueId>, String> {
        let mut roots: Vec<ValueId> = self.word.iter().copied().collect();
        roots.sort_by_key(|v| v.index());
        for root in &roots {
            if let Some(genuine) = self.genuine.get(root) {
                let word = self.word_reason.get(root).cloned().unwrap_or_default();
                return Err(format!(
                    "[TCG-WASM32-WORD] `{func}`: value %{} is a pointer-width word ({word}) and \
                     a Rust-typed i64 ({genuine}); the wasm32 word width cannot be decided, so \
                     failing closed",
                    root.index()
                ));
            }
        }
        let roots: HashSet<ValueId> = roots.into_iter().collect();
        let members: Vec<ValueId> = self.parent.keys().copied().collect();
        Ok(members
            .into_iter()
            .filter(|v| roots.contains(&self.find(*v)))
            .collect())
    }
}

fn inst_name(inst: &Inst) -> String {
    let debug = format!("{inst:?}");
    debug
        .split(|c: char| !c.is_alphanumeric())
        .next()
        .unwrap_or("instruction")
        .to_owned()
}

/// A 64-bit constant as the 32-bit word it denotes: its value must be
/// representable in 32 bits, signed or unsigned.
fn narrow_const(value: &Constant, func: &str) -> Result<Constant, String> {
    match value {
        Constant::Int(v) if (i128::from(i32::MIN)..=i128::from(u32::MAX)).contains(v) => {
            Ok(Constant::Int(i128::from(*v as u32 as i32)))
        }
        other => Err(format!(
            "[TCG-WASM32-WORD] `{func}`: the word constant {other:?} does not fit the 32-bit \
             wasm32 word"
        )),
    }
}

/// `operand : from` reinterpreted as `to`, both 32-bit integers.
fn same_width(from: &Ty, to: &Ty, operand: ValueId) -> Inst {
    if from == to {
        Inst::Copy {
            ty: to.clone(),
            operand,
        }
    } else {
        Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: from.clone(),
            dst_ty: to.clone(),
            operand,
        }
    }
}

fn retype(
    func: &mut Function,
    types: &HashMap<ValueId, Ty>,
    words: &HashSet<ValueId>,
) -> Result<(), String> {
    let name = func.name.clone();
    let word = |v: &ValueId| words.contains(v);
    let is32 = |v: &ValueId| types.get(v).is_some_and(is_word_int);
    let narrow_align = |align: &Option<u64>| align.map(|a| a.min(4));
    for block in &mut func.blocks {
        for (v, t) in &mut block.params {
            if word(v) {
                *t = Ty::I32;
            }
        }
        for node in &mut block.body {
            let r0 = node.results.first().copied();
            let res_word = r0.as_ref().is_some_and(word);
            let replacement = match &node.inst {
                Inst::Const { ty: Ty::I64, value } if res_word => Some(Inst::Const {
                    ty: Ty::I32,
                    value: narrow_const(value, &name)?,
                }),
                Inst::Copy {
                    ty: Ty::I64,
                    operand,
                } if res_word => {
                    let from = match types.get(operand) {
                        Some(Ty::I64) => Ty::I32,
                        Some(t) if is_word_int(t) => t.clone(),
                        other => {
                            return Err(format!(
                                "[TCG-WASM32-WORD] `{name}`: word copy of a {other:?}"
                            ));
                        }
                    };
                    Some(same_width(&from, &Ty::I32, *operand))
                }
                Inst::Copy { ty, operand } if is_word_int(ty) && word(operand) => {
                    Some(same_width(&Ty::I32, ty, *operand))
                }
                Inst::BinOp {
                    op,
                    ty: Ty::I64,
                    lhs,
                    rhs,
                } if res_word => Some(Inst::BinOp {
                    op: *op,
                    ty: Ty::I32,
                    lhs: *lhs,
                    rhs: *rhs,
                }),
                Inst::Overflow {
                    op,
                    ty: Ty::I64,
                    lhs,
                    rhs,
                } if res_word => Some(Inst::Overflow {
                    op: *op,
                    ty: Ty::I32,
                    lhs: *lhs,
                    rhs: *rhs,
                }),
                Inst::ICmp {
                    op,
                    ty: Ty::I64,
                    lhs,
                    rhs,
                } if word(lhs) || word(rhs) || (is32(lhs) && is32(rhs)) => Some(Inst::ICmp {
                    op: *op,
                    ty: Ty::I32,
                    lhs: *lhs,
                    rhs: *rhs,
                }),
                Inst::UnOp {
                    op,
                    ty: Ty::I64,
                    operand,
                } if res_word => Some(Inst::UnOp {
                    op: *op,
                    ty: Ty::I32,
                    operand: *operand,
                }),
                Inst::Select {
                    ty: Ty::I64,
                    cond,
                    then_val,
                    else_val,
                } if res_word => Some(Inst::Select {
                    ty: Ty::I32,
                    cond: *cond,
                    then_val: *then_val,
                    else_val: *else_val,
                }),
                Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty,
                    dst_ty: Ty::I64,
                    operand,
                } if res_word => Some(Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: src_ty.clone(),
                    dst_ty: Ty::I32,
                    operand: *operand,
                }),
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::I64,
                    dst_ty,
                    operand,
                } if word(operand) => Some(Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::I32,
                    dst_ty: dst_ty.clone(),
                    operand: *operand,
                }),
                Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I64,
                    dst_ty,
                    operand,
                } if word(operand) => Some(if is_word_int(dst_ty) {
                    same_width(&Ty::I32, dst_ty, *operand)
                } else {
                    Inst::Cast {
                        op: CastOp::Trunc,
                        src_ty: Ty::I32,
                        dst_ty: dst_ty.clone(),
                        operand: *operand,
                    }
                }),
                Inst::Cast {
                    op: op @ (CastOp::ZExt | CastOp::SExt),
                    src_ty,
                    dst_ty: Ty::I64,
                    operand,
                } if res_word => Some(if is_word_int(src_ty) {
                    same_width(src_ty, &Ty::I32, *operand)
                } else {
                    Inst::Cast {
                        op: *op,
                        src_ty: src_ty.clone(),
                        dst_ty: Ty::I32,
                        operand: *operand,
                    }
                }),
                Inst::Load {
                    ty: Ty::I64,
                    ptr,
                    volatile,
                    align,
                } if res_word => Some(Inst::Load {
                    ty: Ty::I32,
                    ptr: *ptr,
                    volatile: *volatile,
                    align: narrow_align(align),
                }),
                Inst::Store {
                    ty: Ty::I64,
                    ptr,
                    value,
                    volatile,
                    align,
                } if word(value) || is32(value) => Some(Inst::Store {
                    ty: Ty::I32,
                    ptr: *ptr,
                    value: *value,
                    volatile: *volatile,
                    align: narrow_align(align),
                }),
                Inst::Switch { value, cases, .. } if word(value) => {
                    for case in cases {
                        narrow_const(&case.value, &name)?;
                    }
                    None
                }
                _ => None,
            };
            if let Some(inst) = replacement {
                node.inst = inst;
            }
        }
    }
    // Every word must now be typed i32 by its definition.
    for block in &func.blocks {
        for node in &block.body {
            let Some(r) = node.results.first() else {
                continue;
            };
            let declared = match &node.inst {
                Inst::Const { ty, .. }
                | Inst::Copy { ty, .. }
                | Inst::BinOp { ty, .. }
                | Inst::Overflow { ty, .. }
                | Inst::UnOp { ty, .. }
                | Inst::Select { ty, .. }
                | Inst::Load { ty, .. } => Some(ty),
                Inst::Cast { dst_ty, .. } => Some(dst_ty),
                _ => None,
            };
            if word(r) && declared == Some(&Ty::I64) {
                return Err(format!(
                    "[TCG-WASM32-WORD] `{name}`: word value %{} kept its i64 definition; \
                     failing closed",
                    r.index()
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(text: &str) -> Module {
        trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("parse: {e}\n{text}"))
    }

    const HEADER: &str = "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
        type ty.0 = i8\n\ntype ty.1 = i16\n\ntype ty.2 = i32\n\ntype ty.3 = i64\n\n";

    #[test]
    fn pointer_add_word_becomes_i32() {
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (ptr, u32) -> (ptr)\n\n\
             fn @add(functy.0) {{\n\
             bb0(%1: ptr, %2: u32):\n\
             \x20   %5 = ptrtoint ptr %1 to i64\n\
             \x20   %6 = copy i64 %2\n\
             \x20   %7 = const i64 4\n\
             \x20   %8 = mul i64 %6, %7\n\
             \x20   %9 = add i64 %5, %8\n\
             \x20   %10 = inttoptr i64 %9 to ptr\n\
             \x20   ret %10\n\
             }}\n"
        ));
        narrow_native_words(&mut m).unwrap();
        let text = m.to_string();
        assert!(text.contains("ptrtoint ptr %1 to i32"), "{text}");
        assert!(text.contains("bitcast u32 %2 to i32"), "{text}");
        assert!(text.contains("const i32 4"), "{text}");
        assert!(text.contains("mul i32 %6, %7"), "{text}");
        assert!(text.contains("inttoptr i32 %9 to ptr"), "{text}");
        let body = &text[text.find("fn @add").expect("function")..];
        assert!(!body.contains("i64"), "{text}");
    }

    #[test]
    fn word_slot_load_narrows_through_its_alloca() {
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (u32) -> (u32)\n\n\
             fn @slot(functy.0) {{\n\
             bb0(%1: u32):\n\
             \x20   %2 = alloca i64\n\
             \x20   %3 = copy i64 %1\n\
             \x20   store i64 %3, ptr %2\n\
             \x20   %4 = load i64, ptr %2\n\
             \x20   %5 = copy u32 %4\n\
             \x20   ret %5\n\
             }}\n"
        ));
        narrow_native_words(&mut m).unwrap();
        let text = m.to_string();
        assert!(text.contains("store i32 %3, ptr %2"), "{text}");
        assert!(text.contains("load i32, ptr %2"), "{text}");
        assert!(text.contains("bitcast i32 %4 to u32"), "{text}");
    }

    #[test]
    fn a_32_bit_call_parameter_narrows_its_argument() {
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (ptr, u32) -> ()\n\n\
             functy.1 = (ptr, i32) -> ()\n\n\
             fn @sink(functy.1) {{\n}}\n\n\
             fn @caller(functy.0) {{\n\
             bb0(%1: ptr, %2: u32):\n\
             \x20   %3 = copy i64 %2\n\
             \x20   %4 = const i64 2\n\
             \x20   %5 = mul i64 %3, %4\n\
             \x20   call @func.0(%1, %5)\n\
             \x20   ret\n\
             }}\n"
        ));
        narrow_native_words(&mut m).unwrap();
        let text = m.to_string();
        assert!(text.contains("mul i32 %3, %4"), "{text}");
    }

    #[test]
    fn helper_length_parameters_narrow_in_the_definition() {
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (ptr, i64) -> ()\n\n\
             fn @__trustcg_vec_sort_u32(functy.0) {{\n\
             bb0(%1: ptr, %2: i64):\n\
             \x20   %3 = const i64 1\n\
             \x20   %4 = icmp ult i64 %3, %2\n\
             \x20   condbr %4, bb1, bb2\n\
             bb1:\n\
             \x20   ret\n\
             bb2:\n\
             \x20   ret\n\
             }}\n"
        ));
        narrow_native_words(&mut m).unwrap();
        let text = m.to_string();
        assert!(text.contains("bb0(%1: ptr, %2: i32)"), "{text}");
        assert!(text.contains("icmp ult i32 %3, %2"), "{text}");
        assert!(text.contains("= (ptr, i32) -> ()"), "{text}");
    }

    #[test]
    fn a_refused_helper_signature_intern_is_an_id_space_refusal() {
        // A real `Module::intern_func_type` refusal needs a func-type table
        // already holding id `u32::MAX` (2^32 rows), so the door is replaced
        // by one that refuses the way it does. The refusal is taken at the
        // whole pass's boundary, the one the wasm32 lane calls, so a pass that
        // dropped it and went on would fail here. `@add` is narrowed whenever
        // the pass reaches the function bodies (the production-door run at the
        // end), so an unchanged module also shows the pass stopped at the
        // refusal.
        let src = format!(
            "{HEADER}functy.0 = (ptr, i64) -> ()\n\n\
             functy.1 = (ptr, u32) -> (ptr)\n\n\
             fn @__trustcg_vec_sort_u32(functy.0) {{\n\
             bb0(%1: ptr, %2: i64):\n\
             \x20   ret\n\
             }}\n\n\
             fn @add(functy.1) {{\n\
             bb0(%1: ptr, %2: u32):\n\
             \x20   %5 = ptrtoint ptr %1 to i64\n\
             \x20   %6 = copy i64 %2\n\
             \x20   %9 = add i64 %5, %6\n\
             \x20   %10 = inttoptr i64 %9 to ptr\n\
             \x20   ret %10\n\
             }}\n"
        );
        let mut m = parse(&src);
        let full_table = |_: &mut Module, _: FuncTy| -> Result<FuncTyId, IdSpaceExhausted> {
            Err(IdSpaceExhausted::of::<FuncTyId>())
        };
        let err = narrow_native_words_through(&mut m, full_table).unwrap_err();
        assert!(err.starts_with("[TCG-IR-ID-EXHAUSTED] "), "{err}");
        assert!(!err.contains("[TCG-WASM32-HELPER]"), "{err}");
        assert!(err.contains("`__trustcg_vec_sort_u32`"), "{err}");
        assert!(err.contains("the FuncTyId id space is exhausted"), "{err}");
        // Nothing was narrowed: the helper keeps its i64 signature and entry
        // parameter, and no body was retyped.
        assert_eq!(m.to_string(), parse(&src).to_string());
        // The same module through the production door is narrowed, so the
        // assertion above does not hold vacuously.
        let mut narrowed = parse(&src);
        narrow_native_words(&mut narrowed).unwrap();
        let text = narrowed.to_string();
        assert!(text.contains("bb0(%1: ptr, %2: i32)"), "{text}");
        assert!(text.contains("add i32 %5, %6"), "{text}");
    }

    #[test]
    fn an_unported_helper_family_is_refused() {
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (ptr, i64) -> ()\n\n\
             fn @__trustcg_btm_get(functy.0) {{\n}}\n"
        ));
        let err = narrow_native_words(&mut m).unwrap_err();
        assert!(err.contains("[TCG-WASM32-HELPER]"), "{err}");
    }

    #[test]
    fn a_void_memcpy_declaration_is_refused() {
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (ptr, ptr, i32) -> ()\n\n\
             fn @memcpy(functy.0) {{\n}}\n"
        ));
        let err = narrow_native_words(&mut m).unwrap_err();
        assert!(err.contains("[TCG-WASM32-LIBCALL]"), "{err}");
        assert!(err.contains("`memcpy`"), "{err}");
    }

    #[test]
    fn c_prototype_memory_libcalls_are_accepted() {
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (ptr, ptr, i32) -> (ptr)\n\n\
             functy.1 = (ptr, i32, i32) -> (ptr)\n\n\
             functy.2 = (ptr, ptr, i32) -> (i32)\n\n\
             fn @memmove(functy.0) {{\n}}\n\n\
             fn @memset(functy.1) {{\n}}\n\n\
             fn @memcmp(functy.2) {{\n}}\n"
        ));
        narrow_native_words(&mut m).unwrap();
    }

    #[test]
    fn typed_pointer_memory_libcall_declarations_are_accepted() {
        // The shapes a user `extern "C"` block lowers to: typed pointers, a C
        // `int` and a `usize` length.
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (*mut u8, i32, u32) -> (*mut u8)\n\n\
             functy.1 = (*const u8, *const u8, u32) -> (i32)\n\n\
             functy.2 = (*mut u8, *const u8, u32) -> (*mut u8)\n\n\
             fn @memset(functy.0) {{\n}}\n\n\
             fn @memcmp(functy.1) {{\n}}\n\n\
             fn @memcpy(functy.2) {{\n}}\n\n\
             fn @memmove(functy.2) {{\n}}\n"
        ));
        narrow_native_words(&mut m).unwrap();
    }

    #[test]
    fn a_wide_memory_libcall_declaration_is_refused() {
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (*mut u8, i32, u64) -> (*mut u8)\n\n\
             fn @memset(functy.0) {{\n}}\n"
        ));
        let err = narrow_native_words(&mut m).unwrap_err();
        assert!(err.contains("[TCG-WASM32-LIBCALL]"), "{err}");
        assert!(err.contains("`memset`"), "{err}");
    }

    #[test]
    fn genuine_i64_arithmetic_is_kept() {
        let src = format!(
            "{HEADER}functy.0 = (i64, i64) -> (i64)\n\n\
             fn @g(functy.0) {{\n\
             bb0(%1: i64, %2: i64):\n\
             \x20   %3 = const i64 7\n\
             \x20   %4 = mul i64 %1, %3\n\
             \x20   %5 = add i64 %4, %2\n\
             \x20   ret %5\n\
             }}\n"
        );
        let mut m = parse(&src);
        narrow_native_words(&mut m).unwrap();
        assert_eq!(m.to_string(), parse(&src).to_string());
    }

    #[test]
    fn a_word_mixed_with_a_rust_i64_is_refused() {
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (ptr, i64) -> (i64)\n\n\
             fn @mix(functy.0) {{\n\
             bb0(%1: ptr, %2: i64):\n\
             \x20   %3 = ptrtoint ptr %1 to i64\n\
             \x20   %4 = add i64 %3, %2\n\
             \x20   ret %4\n\
             }}\n"
        ));
        let err = narrow_native_words(&mut m).unwrap_err();
        assert!(err.contains("[TCG-WASM32-WORD]"), "{err}");
        assert!(err.contains("signature parameter"), "{err}");
    }

    #[test]
    fn out_of_range_word_constant_is_refused() {
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (ptr) -> (ptr)\n\n\
             fn @far(functy.0) {{\n\
             bb0(%1: ptr):\n\
             \x20   %2 = ptrtoint ptr %1 to i64\n\
             \x20   %3 = const i64 8589934592\n\
             \x20   %4 = add i64 %2, %3\n\
             \x20   %5 = inttoptr i64 %4 to ptr\n\
             \x20   ret %5\n\
             }}\n"
        ));
        let err = narrow_native_words(&mut m).unwrap_err();
        assert!(err.contains("does not fit the 32-bit"), "{err}");
    }

    #[test]
    fn a_width_sensitive_bit_op_on_a_word_is_refused_not_retyped() {
        // `ctlz`/`rotl` give different answers at 32 and 64 bits on the same
        // low bits, so a word class reaching one cannot be narrowed.
        for op in ["%4 = ctlz i64 %3", "%4 = rotl i64 %3, %3"] {
            let mut m = parse(&format!(
                "{HEADER}functy.0 = (ptr) -> (ptr)\n\n\
                 fn @bits(functy.0) {{\n\
                 bb0(%1: ptr):\n\
                 \x20   %3 = ptrtoint ptr %1 to i64\n\
                 \x20   {op}\n\
                 \x20   %5 = inttoptr i64 %4 to ptr\n\
                 \x20   ret %5\n\
                 }}\n"
            ));
            let err = narrow_native_words(&mut m).unwrap_err();
            assert!(err.contains("[TCG-WASM32-WORD]"), "{op}: {err}");
        }
    }

    #[test]
    fn a_genuine_i64_bit_op_keeps_its_width() {
        let mut m = parse(&format!(
            "{HEADER}functy.0 = (i64, u32) -> (u32)\n\n\
             fn @lz(functy.0) {{\n\
             bb0(%1: i64, %2: u32):\n\
             \x20   %3 = zext u32 %2 to i64\n\
             \x20   %4 = rotl i64 %1, %3\n\
             \x20   %5 = ctlz i64 %4\n\
             \x20   %6 = trunc i64 %5 to u32\n\
             \x20   ret %6\n\
             }}\n"
        ));
        narrow_native_words(&mut m).unwrap();
        let text = m.to_string();
        assert!(text.contains("rotl i64 %1, %3"), "{text}");
        assert!(text.contains("ctlz i64 %4"), "{text}");
    }
}
