// trust-cg-codegen/module_merge.rs - Batch N per-function trust-ir modules into one
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Assemble N single-function trust-ir [`Module`]s into ONE multi-function
//! module, remapping the module-scoped identifiers so the merged module is a
//! faithful, semantics-preserving union of its inputs.
//!
//! This is the load-bearing NEW glue for module-batching (design brief
//! `docs/module-batching-design-2026-07-04.md`, Strategy A): the bridge lowers
//! each `MonoItem::Fn` to a one-function module (that function at `FuncId(0)`
//! plus extern *declarations* of its siblings), and this pass batches a
//! codegen-unit's per-function modules into one so the backend's already-proven
//! multi-function object emitter, the CT-5 parallel fan-out, and the OPT-4
//! inliner all see intra-module callees.
//!
//! # What gets remapped
//! Every input module numbers its own module-scoped ids from zero, so a naive
//! concatenation would alias them. [`merge_modules`] remaps ALL of:
//!
//! * **`FuncId`** — declarations are **deduplicated by symbol name** and a
//!   *definition* UPGRADES a matching declaration. So module A's `Inst::Call` to
//!   its sibling B (an extern declaration inside A) resolves, in the merged
//!   module, to B's actual DEFINITION — turning a cross-object relocation into
//!   an intra-object local branch. FuncIds are then dense (`functions[i].id ==
//!   FuncId(i)`), and every `FuncId` reference in a body is rewritten to its new
//!   dense id (the backend adapter resolves callees by the `.id` field —
//!   `trust-cg-lower/src/adapter.rs`).
//! * **`FuncTyId`** — the per-module `func_types` tables are concatenated
//!   (no dedup; duplicate signatures are harmless) and every reference
//!   (`Function.ty`, `Inst::CallIndirect.sig`, an embedded `Ty::Func`, a
//!   `ClosureTy::func`) is shifted by that module's base offset. Every shift is
//!   bounds-checked against the SOURCE module's table so a dangling input id can
//!   never silently alias another module's entry.
//! * **`StructId` / `EnumId` / `RecordId`** (the NAMED type tables) — assigned
//!   dense merged ids keyed by NAME (first-encounter order), with the embedded
//!   `def.id` field rewritten to match its table position. Two modules that
//!   define the same name are DEDUPLICATED to one entry, and the merge VERIFIES
//!   (post-remap, field-for-field including offsets/size/align/repr and enum
//!   discriminants, field names, and concrete layout descriptors) that every
//!   contributor is structurally identical — a
//!   same-name definition with different structure is REJECTED (fail-closed: a
//!   wrong identification would change layout, i.e. miscompile). Differently
//!   named types never dedup, even when structurally identical (keeping both is
//!   always sound).
//! * **`TyId` (the `types` table)** — entries are UNNAMED pure structure, so
//!   they are hash-consed: each entry is recursively remapped (following
//!   intra-table `TyId` links; struct/enum/record/closure/functy ids are leaves
//!   resolved through the maps above) and interned by content. Identical
//!   entries across modules collapse to one id — this is what lets two sibling
//!   modules that both define `struct S { a: [i64; 4] }` pass the same-name
//!   structural verification. A `TyId` cycle that never bottoms out through the
//!   `types` table alone (an infinite by-value type) is rejected.
//! * **`ClosureTyId`** — the `closure_types` tables are concatenated with a
//!   base offset (no dedup; entries are unnamed and duplicates are sound); the
//!   embedded `func: FuncTyId` and capture types are remapped.
//! * **Debug-info `files`** — paths are interned (exact-path dedup) and every
//!   `InstrNode::span.file` and lexical `ScopeData::span.file` index is
//!   rewritten. A module that carries either kind of span but no file table
//!   cannot be merged with one that has a file table (its span file indices
//!   would silently mis-resolve) — that mix is rejected.
//! * **`globals` / `GlobalId` / global-address stubs** (design Step 4 — the
//!   soundness-sensitive one: a missed or mis-remapped reference is a silent
//!   WRONG DATA ADDRESS). The per-module `globals` tables are merged
//!   name-keyed: byte-identical same-name entries DEDUPLICATE to one; an
//!   initializer-less external IMPORT (how the bridge references a
//!   `static mut` / thread-local defined in another object) is UPGRADED by a
//!   same-name definition exactly like a function declaration (guarded: type /
//!   mutability / TLS-model must match and the definition must itself be
//!   externally linkable, else separate compilation would not have linked);
//!   any other same-name disagreement is REJECTED. Global references in
//!   bodies are then remapped BOTH ways they occur:
//!   - `Inst::GlobalAddr { global: GlobalId }` — a plain index remap;
//!   - the `0xFADE`-tagged **global-address stubs**: opaque
//!     top-level `Inst::Const { value: Constant::Int }` payloads whose type is
//!     a supported thin pointer/reference carrier or legacy `Ty::I64`, packing
//!     `module.globals[index] + offset` (see [`crate::global_stub`], the
//!     shared payload codec; the typed carrier gate plus its predicate exactly
//!     mirror the lower adapter's authoritative consumer).
//!     Every such typed body constant that matches the stub predicate is decoded
//!     and re-packed to the merged global index (offset preserved). Other
//!     declared types remain numeric data even when their high bits match the
//!     in-band tag.
//!   DEFENSE IN DEPTH, because a wrong data address is the worst class: (i)
//!   a pre-count of every stub in every winner body must equal the number the
//!   remap rewrote AND an independent post-merge recount (no stub missed or
//!   invented); (ii) the structural self-check re-decodes every merged stub —
//!   index in range, re-encode round-trips bit-exactly; (iii)
//!   [`verify_global_reference_preservation`] re-walks every merged body in
//!   LOCKSTEP with its source body and proves each global reference (stub or
//!   `GlobalAddr`) resolves to the SAME-NAMED global at the SAME offset as it
//!   did in its source module, and every non-stub integer constant is
//!   bit-identical.
//!
//! Remap coverage is EXHAUSTIVE by construction: the instruction/type walkers
//! match every `Inst` and `Ty` variant with no wildcard arm, so a new trust-ir
//! variant fails compilation here instead of being silently passed through.
//!
//! # Fail-closed deferrals
//! A wrong remap is a call to the wrong function or a value of the wrong layout:
//! a silent miscompile. This pass therefore REJECTS everything it does not
//! remap, so it can never silently mis-remap a table it does not handle:
//!
//! * **Global-reference ambiguity is fail-closed**: the `0xFADE` stub tag is
//!   IN-BAND within supported thin pointer/reference address carriers and the
//!   legacy `Ty::I64` carrier. At the one position the backend decodes (a
//!   top-level body `Inst::Const` with one of those carrier types) the merge
//!   remaps exactly what the decoder would decode. Unsigned numeric declarations
//!   are never decoded, eliminating collisions with U64/U128/Usize data.
//!   Everywhere the backend does NOT decode — an integer nested inside an
//!   aggregate/array/record constant, a `Switch`
//!   case value, a global-initializer element — a tag-shaped integer is
//!   REJECTED outright: it is almost certainly plain data, but a structural
//!   merge cannot prove no consumer will ever treat it as a stub, so the
//!   module simply does not batch. A top-level stub whose index is OUT OF
//!   RANGE for its own module's `globals` (which the adapter fails closed on)
//!   is likewise rejected rather than merged into a table where a sibling's
//!   global could silently capture it. Global initializers must not embed
//!   `FnDef`/`Closure` constants (module-scoped `FuncId`s; producers use
//!   name-relative `SymbolAddr` there), and an initializer-less global must
//!   be a well-formed external import — anything else is rejected.
//! * **Proof tables are not mergeable**: `proof_obligations` carry module-scoped
//!   `ProofId`s and OPAQUE formula payloads (schema-defined strings that may
//!   textually reference this module's id numbering), which no structural remap
//!   can soundly rewrite; `proof_certificates` bind evidence to the ORIGINAL
//!   module's exact content (lineage digests), so they cannot vouch for a merged
//!   module; `obligation_diagnostics` and `spec_modules` reference those
//!   obligations/anchors. All four are rejected non-empty — the merged module's
//!   obligations must be regenerated downstream (trust-cg's per-compile lowering
//!   certs ARE regenerated: `Compiler::compile(emit_proofs)` derives them from
//!   the machine IR, not from these tables). For the same opacity reason a
//!   non-empty `Function::summary` (contract formulas) and a call-site
//!   `ProofContext` (obligation-id references) are rejected. Marker-style
//!   [`trust_ir::ProofAnnotation`]s carry no module-scoped ids and ride along
//!   unchanged.
//! * **Refinement tables are not mergeable yet**: universes and predicates are
//!   content-interned, so concatenating or offsetting their ids would violate
//!   canonical identity. More importantly, the downstream adapter does not yet
//!   carry validated predicate provenance into LIR. Modules carrying either
//!   table (and therefore any valid `Ty::Refine`) are rejected and compiled
//!   separately rather than silently erasing the predicate.
//! * **First-class function values are MERGED** (the former fn-pointer
//!   deferral is lifted — the last ineligibility class): direct `Ty::Func` in
//!   a signature or block parameter is a remapped `FuncTyId`; a
//!   `Constant::FnDef(FuncId)` / capture-free `Constant::Closure` (including
//!   inside aggregate constants and `Switch` case values) has its embedded
//!   `FuncId` rewritten through the same name-keyed map direct calls use;
//!   `Inst::CallIndirect` carries only a runtime callee VALUE (its static
//!   identity, when any, is a `FnDef` constant — covered above) plus a
//!   remapped `sig: FuncTyId`. `Constant::SymbolAddr` is name-relative
//!   (nothing module-scoped to remap; symbol names are preserved verbatim by
//!   the merge): zero-addend body constants and initializer uses are allowed,
//!   while non-zero-addend body constants remain ineligible because the
//!   adapter fails closed on that form. For the same batch-quality reason a
//!   `Constant::Closure` with CAPTURES (the adapter lowers only capture-free
//!   closures as bare fn pointers) and the `Inst::SeqMap*` sequence ops (not
//!   yet lowered by the adapter; the `SeqMap.fwd` `FuncId` remap is
//!   implemented and unit-tested for the day they are) stay ineligible.
//!   `Constant::Bytes` is batchable only as a complete top-level `[u8; N]`
//!   body constant with a checked element type, length, and UTF-8 claim;
//!   nested Bytes fields and Bytes initializers remain adapter/object-writer
//!   gaps and are deferred.
//!   Function-identity preservation is proven per merge by
//!   [`verify_function_identity_preservation`] — a name-keyed lockstep walk
//!   (independent of the remap bookkeeping) requiring every `FuncId` in a
//!   merged body (`Call`/`Invoke` callees, `FnDef`/`Closure` constants at any
//!   constant depth, `SeqMap.fwd`) to resolve to the SAME-NAMED function it
//!   named in its source module, every `CallIndirect.sig`/`Function.ty` to a
//!   name-resolved-structurally-IDENTICAL signature, and every non-identity
//!   constant leaf to ride through bit-identical.
//! * **Dialect ops are rejected**: `Inst::DialectOp` is namespaced and opaque —
//!   its attributes may encode module-scoped ids in dialect-defined payloads
//!   (`AttrValue::Bytes`/`Str`/ints) that no structural remap can see. (This
//!   also closes a latent gap: a dialect op's `result_tys` were previously not
//!   remapped at all.)
//! * `FatPtrKind::TraitObject { trait_id }` passes through unchanged: there is
//!   no module-level trait table for it to index (nothing to remap and nothing
//!   that can dangle); producers own cross-module trait-id agreement exactly as
//!   they do under separate compilation.
//!
//! After assembling the module a structural self-check (`structural_self_check`)
//! re-derives the invariants directly (dense ids in every table, no
//! dropped/duplicate entry, every id reference resolvable — checked by an
//! INDEPENDENT read-only walker, not the remap code) and, when every input
//! validated clean, the canonical [`trust_ir_build::validate_module`] walker is
//! run over the result as a second backstop. Any violation returns `Err`.

use std::collections::{HashMap, HashSet};

use trust_ir::ty::FatPtrKind;
use trust_ir::value::GlobalId;
use trust_ir::{
    ClosureTy, Constant, EnumDef, FieldDef, FuncId, FuncTy, FuncTyId, Function, Global, Inst,
    Linkage, Module, RecordDef, StructDef, Ty,
};
use trust_ir::{ClosureTyId, EnumId, EnumVariant, RecordId, StructId, TyId};

use crate::global_stub::{decode_global_addr_stub, encode_global_addr_stub};

/// Merge N per-function trust-ir modules into one multi-function module.
///
/// See the module docs for the remap + fail-closed contract. Returns `Err` with
/// a human-readable reason on any unsupported input or any structural violation
/// detected after the merge (fail-closed — a merge that cannot be proven sound
/// is never returned).
pub fn merge_modules(modules: &[Module]) -> Result<Module, String> {
    if modules.is_empty() {
        return Err("merge_modules: no input modules to merge".to_string());
    }

    // --- 1. Per-module preconditions (global-free + supported-construct). ----
    for (i, m) in modules.iter().enumerate() {
        precheck_module(m, i)?;
    }

    // --- 2. Target consistency. All inputs must target the same machine. -----
    let target_info = modules[0].target_info.clone();
    for (i, m) in modules.iter().enumerate() {
        if m.target_info != target_info {
            return Err(format!(
                "merge_modules: module {i} (`{}`) target_info differs from module 0 (`{}`); \
                 cannot batch functions compiled for different targets",
                m.name, modules[0].name
            ));
        }
    }

    // --- 3. Assign dense FuncIds by symbol; a definition upgrades a decl. -----
    let mut name_to_dense: HashMap<String, u32> = HashMap::new();
    let mut dense_names: Vec<String> = Vec::new();
    // winners[dense] = (module_index, &Function) chosen for that symbol.
    let mut winners: Vec<Option<(usize, &Function)>> = Vec::new();
    for (i, m) in modules.iter().enumerate() {
        for f in &m.functions {
            let dense = if let Some(&d) = name_to_dense.get(&f.name) {
                d
            } else {
                let d = u32::try_from(dense_names.len()).map_err(|_| {
                    "merge_modules: merged function table exceeds u32 id space".to_string()
                })?;
                name_to_dense.insert(f.name.clone(), d);
                dense_names.push(f.name.clone());
                winners.push(None);
                d
            };
            let slot = &mut winners[dense as usize];
            match slot {
                None => *slot = Some((i, f)),
                Some((prev_mod, prev_fn)) => {
                    let incoming_def = f.has_body();
                    let existing_def = prev_fn.has_body();
                    if incoming_def && existing_def {
                        return Err(format!(
                            "merge_modules: duplicate definition of function `{}` \
                             (defined in both module {prev_mod} and module {i}); \
                             batching requires at most one definition per symbol",
                            f.name
                        ));
                    }
                    // A definition upgrades a declaration; two declarations keep
                    // the first (they resolve to the same undefined external).
                    if incoming_def && !existing_def {
                        *slot = Some((i, f));
                    }
                }
            }
        }
    }

    // Per-module FuncId remap: old `f.id` (index into a module's own numbering)
    // -> dense id (resolved through the shared symbol name).
    let mut fid_maps: Vec<HashMap<u32, u32>> = Vec::with_capacity(modules.len());
    for m in modules {
        let mut map = HashMap::new();
        for f in &m.functions {
            map.insert(f.id.index(), name_to_dense[&f.name]);
        }
        fid_maps.push(map);
    }

    // --- 3b. Merge the globals tables (name-keyed dedup + decl->def upgrade,
    // mismatches fail closed) and build the per-module index remaps every
    // body global reference (stub or GlobalAddr) is rewritten through. -------
    let globals_merge = assign_globals(modules)?;

    // --- 4. Assign merged ids for the NAMED type tables (by name). -----------
    let structs_nt = assign_named(
        modules,
        "struct",
        |m| &m.structs,
        |d: &StructDef| (d.name.as_str(), d.id.index()),
    )?;
    let enums_nt = assign_named(
        modules,
        "enum",
        |m| &m.enums,
        |d: &EnumDef| (d.name.as_str(), d.id.index()),
    )?;
    let records_nt = assign_named(
        modules,
        "record",
        |m| &m.records,
        |d: &RecordDef| (d.name.as_str(), d.id.index()),
    )?;

    // --- 5. Base offsets for the CONCATENATED (unnamed, no-dedup) tables. ----
    let func_ty_base = concat_bases(modules, "func_types", |m| m.func_types.len())?;
    let closure_base = concat_bases(modules, "closure_types", |m| m.closure_types.len())?;

    // --- 6. Per-module remap contexts. ----------------------------------------
    let mut s_maps = structs_nt.per_module;
    let mut e_maps = enums_nt.per_module;
    let mut r_maps = records_nt.per_module;
    let mut g_maps = globals_merge.per_module;
    let mut maps: Vec<ModMaps> = Vec::with_capacity(modules.len());
    for (i, m) in modules.iter().enumerate() {
        maps.push(ModMaps {
            func_ty_base: func_ty_base[i],
            func_ty_len: m.func_types.len(),
            closure_base: closure_base[i],
            closure_len: m.closure_types.len(),
            struct_map: std::mem::take(&mut s_maps[i]),
            enum_map: std::mem::take(&mut e_maps[i]),
            record_map: std::mem::take(&mut r_maps[i]),
            global_map: std::mem::take(&mut g_maps[i]),
            ty_map: HashMap::new(),
            file_map: HashMap::new(),
            files_len: m.files.len(),
        });
    }

    // --- 7. Debug-info file table: intern by exact path, per-module index map.
    let mut merged_files: Vec<String> = Vec::new();
    for (i, m) in modules.iter().enumerate() {
        for (j, path) in m.files.iter().enumerate() {
            let idx = match merged_files.iter().position(|p| p == path) {
                Some(p) => p,
                None => {
                    merged_files.push(path.clone());
                    merged_files.len() - 1
                }
            };
            let idx = u32::try_from(idx).map_err(|_| {
                "merge_modules: merged debug file table exceeds u32 id space".to_string()
            })?;
            let j = u32::try_from(j).map_err(|_| {
                format!("merge_modules: module {i} debug file table exceeds u32 id space")
            })?;
            maps[i].file_map.insert(j, idx);
        }
    }

    // --- 8. Hash-cons the `types` tables (structural interning). -------------
    let mut interner = TypeInterner::default();
    for (i, m) in modules.iter().enumerate() {
        for tid in 0..m.types.len() {
            let tid = u32::try_from(tid).map_err(|_| {
                format!("merge_modules: module {i} types table exceeds u32 id space")
            })?;
            interner.intern(modules, &maps, i, tid)?;
        }
    }
    for ((mod_idx, old_tid), merged_tid) in &interner.memo {
        maps[*mod_idx].ty_map.insert(*old_tid, *merged_tid);
    }
    let merged_types = interner.merged;

    // --- 9. Merged func_types (concat + content remap). ----------------------
    let mut merged_func_types: Vec<FuncTy> = Vec::new();
    for (i, m) in modules.iter().enumerate() {
        for ft in &m.func_types {
            let params = ft
                .params
                .iter()
                .map(|t| remap_ty_final(t, &maps[i]))
                .collect::<Result<Vec<_>, _>>()?;
            let returns = ft
                .returns
                .iter()
                .map(|t| remap_ty_final(t, &maps[i]))
                .collect::<Result<Vec<_>, _>>()?;
            merged_func_types.push(FuncTy {
                params,
                returns,
                is_vararg: ft.is_vararg,
            });
        }
    }

    // --- 10. Merged closure_types (concat + content remap). ------------------
    let mut merged_closure_types: Vec<ClosureTy> = Vec::new();
    for (i, m) in modules.iter().enumerate() {
        let mm = &maps[i];
        for ct in &m.closure_types {
            merged_closure_types.push(ClosureTy {
                func: FuncTyId::new(shifted(
                    ct.func.index(),
                    mm.func_ty_base,
                    mm.func_ty_len,
                    "ClosureTy::func func_type",
                )?),
                captures: ct
                    .captures
                    .iter()
                    .map(|t| remap_ty_final(t, mm))
                    .collect::<Result<Vec<_>, _>>()?,
            });
        }
    }

    // --- 11. Merged NAMED tables: remap winners + verify every contributor. --
    let merged_structs = materialize_named(
        "struct",
        modules,
        &structs_nt.contributors,
        |d, dense, mi| remap_struct_def(d, dense, &maps[mi]),
        |d: &StructDef| d.name.as_str(),
    )?;
    let merged_enums = materialize_named(
        "enum",
        modules,
        &enums_nt.contributors,
        |d, dense, mi| remap_enum_def(d, dense, &maps[mi]),
        |d: &EnumDef| d.name.as_str(),
    )?;
    let merged_records = materialize_named(
        "record",
        modules,
        &records_nt.contributors,
        |d, dense, mi| remap_record_def(d, dense, &maps[mi]),
        |d: &RecordDef| d.name.as_str(),
    )?;

    // --- 12. Materialize the merged functions in dense order. -----------------
    // DEFENSE (i), the stub COUNT tooth: pre-count every global-address stub in
    // every winner body (an INDEPENDENT walk, before any rewrite); the remap
    // below must rewrite exactly this many, and the structural self-check
    // recounts the merged output against the same number — a stub can be
    // neither missed nor invented.
    let expected_stub_count: usize = winners
        .iter()
        .map(|w| {
            w.map(|(_, f)| count_global_addr_stubs(f))
                .unwrap_or_default()
        })
        .sum();
    let mut remapped_stub_count = 0usize;
    let any_files = !merged_files.is_empty();
    let mut merged_functions: Vec<Function> = Vec::with_capacity(dense_names.len());
    for (dense, name) in dense_names.iter().enumerate() {
        let (mod_idx, orig) = winners[dense].ok_or_else(|| {
            format!("merge_modules: internal error — no winner recorded for symbol `{name}`")
        })?;
        let mm = &maps[mod_idx];
        let mut f = orig.clone();
        f.id = FuncId::new(u32::try_from(dense).expect("dense fits u32 (bounded above)"));
        f.ty = FuncTyId::new(shifted(
            orig.ty.index(),
            mm.func_ty_base,
            mm.func_ty_len,
            "Function.ty func_type",
        )?);
        if let Some(scopes) = &mut f.scopes {
            for scope in scopes {
                if let Some(span) = &mut scope.span {
                    if mm.files_len == 0 {
                        if any_files {
                            return Err(format!(
                                "merge_modules: function `{}` (module {mod_idx}) carries lexical \
                                 scope spans but its module has no debug file table, while another \
                                 input defines one; its span file indices would mis-resolve \
                                 after merging — fail-closed",
                                f.name
                            ));
                        }
                        // No module in this merge has a file table: spans are
                        // line/col-only by convention — carried unchanged.
                    } else {
                        span.file = mapped(&mm.file_map, span.file, "debug-info scope file")?;
                    }
                }
            }
        }
        for block in &mut f.blocks {
            for (_, ty) in &mut block.params {
                *ty = remap_ty_final(ty, mm)?;
            }
            for node in &mut block.body {
                remap_inst(
                    &mut node.inst,
                    mm,
                    &fid_maps[mod_idx],
                    &mut remapped_stub_count,
                )?;
                if let Some(span) = &mut node.span {
                    if mm.files_len == 0 {
                        if any_files {
                            return Err(format!(
                                "merge_modules: function `{}` (module {mod_idx}) carries source \
                                 spans but its module has no debug file table, while another \
                                 input defines one; its span file indices would mis-resolve \
                                 after merging — fail-closed",
                                f.name
                            ));
                        }
                        // No module in this merge has a file table: spans are
                        // line/col-only by convention — carried unchanged.
                    } else {
                        span.file = mapped(&mm.file_map, span.file, "debug-info file")?;
                    }
                }
            }
        }
        merged_functions.push(f);
    }

    // DEFENSE (i) enforcement half 1: the remap must have rewritten EXACTLY
    // the pre-counted stubs (a skipped instruction walk would show here; the
    // self-check below independently recounts the assembled output).
    if remapped_stub_count != expected_stub_count {
        return Err(format!(
            "merge_modules: global-address stub count mismatch — {expected_stub_count} stub(s) \
             counted in the input winner bodies but {remapped_stub_count} remapped; a missed \
             stub is a silent wrong data address — fail-closed"
        ));
    }

    // --- 13. Assemble the merged module. --------------------------------------
    let expected = MergeExpectations {
        functions: dense_names.len(),
        func_types: merged_func_types.len(),
        structs: merged_structs.len(),
        enums: merged_enums.len(),
        records: merged_records.len(),
        closure_types: merged_closure_types.len(),
        types: merged_types.len(),
        files: merged_files.len(),
        globals: globals_merge.merged.len(),
        global_addr_stubs: expected_stub_count,
    };
    let mut merged = Module::new(modules[0].name.clone());
    merged.functions = merged_functions;
    merged.func_types = merged_func_types;
    merged.structs = merged_structs;
    merged.enums = merged_enums;
    merged.records = merged_records;
    merged.closure_types = merged_closure_types;
    merged.types = merged_types;
    merged.files = merged_files;
    merged.globals = globals_merge.merged;
    merged.target_info = target_info;

    // --- 14. Fail-closed structural self-check + canonical validator backstop.
    structural_self_check(&merged, &expected)?;

    // DEFENSE (iii): lockstep source-vs-merged walk proving every global
    // reference resolves to the SAME-NAMED global at the SAME offset it did in
    // its source module (independent of the remap code AND of the self-check).
    verify_global_reference_preservation(modules, &winners, &merged)?;

    // DEFENSE (iv): lockstep source-vs-merged walk proving every FUNCTION
    // identity — `Call`/`Invoke` callees, `FnDef`/`Closure` constants at any
    // depth, `SeqMap.fwd` — resolves to the SAME-NAMED function it named in
    // its source module, every `CallIndirect.sig` / `Function.ty` signature is
    // name-resolved structurally identical, and every non-identity constant
    // leaf is bit-identical. A missed or wrong-but-in-range FuncId remap in a
    // function-pointer VALUE is a call to the WRONG function — the worst
    // class; this check is independent of the remap bookkeeping.
    verify_function_identity_preservation(modules, &winners, &merged)?;

    // Independent, comprehensive cross-check: if every INPUT validated clean,
    // the merge (a pure id-remap + concat) must also validate clean. This
    // catches any reference the hand-rolled self-check missed.
    let inputs_clean = modules
        .iter()
        .all(|m| trust_ir_build::validate_module(m).is_empty());
    if inputs_clean {
        let errors = trust_ir_build::validate_module(&merged);
        if !errors.is_empty() {
            return Err(format!(
                "merge_modules: merged module failed canonical validation ({} error(s)); \
                 first: {:?}",
                errors.len(),
                errors[0]
            ));
        }
    }

    Ok(merged)
}

/// Whether `m` satisfies every PER-MODULE batching precondition
/// ([`precheck_module`]) — i.e. it carries none of the constructs the merge
/// fails closed on (opaque proof/refinement tables, unsupported constant and
/// dialect/sequence forms, dangling references, …). Callers can use this to
/// pre-filter a candidate
/// batch down to its mergeable subset (compiling the rejected modules
/// separately, exactly as under separate compilation). Purely ADVISORY:
/// [`merge_modules`] re-validates every input itself, so a stale or wrong
/// answer here can only change WHICH modules get batched, never admit an
/// unsupported construct into a merge.
pub fn module_batch_eligible(m: &Module) -> Result<(), String> {
    precheck_module(m, 0)
}

// ---------------------------------------------------------------------------
// Precheck (fail-closed input gate)
// ---------------------------------------------------------------------------

/// Reject any input module carrying a construct this slice does not remap.
/// Sound by construction: refusing what it cannot remap means it can never
/// silently mis-remap.
fn precheck_module(m: &Module, idx: usize) -> Result<(), String> {
    let reject_nonempty = |what: &str, len: usize, why: &str| -> Result<(), String> {
        if len != 0 {
            Err(format!(
                "merge_modules: module {idx} (`{}`) has {len} {what}; {why} — fail-closed",
                m.name
            ))
        } else {
            Ok(())
        }
    };
    // Globals: the table itself is merged (Step 4), so it is validated rather
    // than rejected. Name-keyed identity requires unique names per module; an
    // initializer-less global is only meaningful as a linkable external
    // IMPORT (the object writer rejects anything else); initializer payloads
    // must carry nothing module-scoped (`FnDef`/`Closure` embed `FuncId`s —
    // producers use name-relative `SymbolAddr` in initializers) and no
    // stub-shaped integer (initializer elements are raw data the backend
    // never decodes as a stub; see the module docs on tag ambiguity).
    let mut global_names: HashSet<&str> = HashSet::new();
    for g in &m.globals {
        if !global_names.insert(g.name.as_str()) {
            return Err(format!(
                "merge_modules: module {idx} (`{}`) declares global `{}` more than once; \
                 ambiguous name-keyed identity — fail-closed",
                m.name, g.name
            ));
        }
        if g.initializer.is_none()
            && !matches!(
                g.linkage,
                Linkage::External | Linkage::Weak | Linkage::LinkOnce
            )
        {
            return Err(format!(
                "merge_modules: module {idx} (`{}`) global `{}` has no initializer but \
                 non-external linkage {:?}; not a well-formed cross-object import — fail-closed",
                m.name, g.name, g.linkage
            ));
        }
        if let Some(init) = &g.initializer {
            check_global_initializer_constant(init, &m.name, idx, &g.name)?;
        }
    }
    reject_nonempty(
        "proof obligation(s)",
        m.proof_obligations.len(),
        "obligations carry module-scoped ProofIds and OPAQUE formula payloads that may \
         reference this module's id numbering; a structural merge cannot soundly rewrite \
         them (regenerate obligations against the merged module instead)",
    )?;
    reject_nonempty(
        "proof certificate(s)",
        m.proof_certificates.len(),
        "certificate evidence binds the ORIGINAL module's exact content (lineage digests), \
         so it cannot vouch for a merged module",
    )?;
    reject_nonempty(
        "obligation diagnostic(s)",
        m.obligation_diagnostics.len(),
        "diagnostics reference the (unmergeable) proof-obligation table",
    )?;
    reject_nonempty(
        "spec module(s)",
        m.spec_modules.len(),
        "spec cross-reference anchors bind to the source module's symbols/obligations",
    )?;
    reject_nonempty(
        "refinement universe(s)",
        m.universes.len(),
        "universes are content-interned and cannot be concatenated without re-interning every \
         predicate reference; the downstream adapter also cannot carry validated refinement \
         provenance yet",
    )?;
    reject_nonempty(
        "refinement predicate(s)",
        m.predicates.len(),
        "predicates are content-interned and cannot be concatenated without remapping their \
         universe/child ids; the downstream adapter also cannot carry validated refinement \
         provenance yet",
    )?;

    // Signatures MAY name function-pointer types directly (`Ty::Func` is a
    // remapped `FuncTyId`, base-shifted with a source-range bounds check like
    // every other signature reference) — the former fn-pointer deferral is
    // lifted. Aggregate/table types are likewise supported.

    // Bodies: no dangling references, no backend-fail-closed constant forms
    // (non-zero-addend body `SymbolAddr`, captured closure constants), no
    // sequence ops, no opaque dialect ops, no proof-context obligation
    // references.
    for f in &m.functions {
        if f.summary.as_ref().is_some_and(|s| !s.is_empty()) {
            return Err(format!(
                "merge_modules: module {idx} (`{}`) function `{}` carries a non-empty \
                 separate-compilation summary (contract ProofFormulas); formula payloads are \
                 opaque and may name module-scoped ids this merge renumbers — fail-closed",
                m.name, f.name
            ));
        }
        for b in &f.blocks {
            // Block parameters of fn-pointer type are runtime VALUES (no
            // static FuncId); their `Ty::Func` id is remapped like any other
            // embedded type — nothing to gate here anymore.
            for node in &b.body {
                if node
                    .proof_context
                    .as_ref()
                    .is_some_and(|pc| !pc.assumes.is_empty() || !pc.establishes.is_empty())
                {
                    return Err(format!(
                        "merge_modules: module {idx} (`{}`) function `{}` has a call site \
                         carrying a ProofContext that references module proof-obligation ids; \
                         the obligations table is not merged — fail-closed",
                        m.name, f.name
                    ));
                }
                match &node.inst {
                    Inst::GlobalAddr { global } => {
                        if global.index() as usize >= m.globals.len() {
                            return Err(format!(
                                "merge_modules: module {idx} (`{}`) function `{}` references \
                                 global id {} but the module has only {} global(s); a dangling \
                                 reference cannot be remapped — fail-closed",
                                m.name,
                                f.name,
                                global.index(),
                                m.globals.len()
                            ));
                        }
                    }
                    // `Inst::CallIndirect` is MERGEABLE: the callee is a
                    // runtime ValueId (its static identity, when any, is a
                    // `FnDef`/`Closure` constant, remapped + lockstep-verified
                    // elsewhere) and `sig` is a remapped `FuncTyId`.
                    Inst::SeqMap { .. } | Inst::SeqMapAddK { .. } | Inst::SeqMapNot { .. } => {
                        return Err(format!(
                            "merge_modules: module {idx} (`{}`) function `{}` uses a sequence op \
                             (Inst::SeqMap*); the backend adapter fails closed on SeqMap*, so \
                             batching it would only trade a per-fn fail-closed for a whole-batch \
                             fallback (the SeqMap.fwd FuncId remap itself is implemented and \
                             unit-tested for when the adapter lowers these)",
                            m.name, f.name
                        ));
                    }
                    Inst::DialectOp(_) => {
                        return Err(format!(
                            "merge_modules: module {idx} (`{}`) function `{}` uses a dialect op; \
                             dialect ops are namespaced/opaque and their attributes may encode \
                             module-scoped ids in dialect-defined payloads a structural remap \
                             cannot see — fail-closed",
                            m.name, f.name
                        ));
                    }
                    Inst::Const { ty, value } => {
                        if let Some(why) = body_constant_batch_deferred(m, ty, value) {
                            return Err(format!(
                                "merge_modules: module {idx} (`{}`) function `{}` embeds a \
                                 constant the backend fails closed on ({why}); batching it \
                                 would only trade a per-fn fail-closed for a whole-batch \
                                 fallback",
                                m.name, f.name
                            ));
                        }
                        // A `FnDef`/`Closure` FuncId must resolve within its
                        // OWN module's function table (mirrors the dangling
                        // `GlobalAddr` check): a dangling id cannot be
                        // remapped, so reject it here rather than poison the
                        // batch when the remap fails closed mid-merge.
                        if let Some(fid) = constant_dangling_funcid(value, m) {
                            return Err(format!(
                                "merge_modules: module {idx} (`{}`) function `{}` embeds a \
                                 function constant referencing FuncId({}) with no matching \
                                 function in its module; a dangling reference cannot be \
                                 remapped — fail-closed",
                                m.name,
                                f.name,
                                fid.index()
                            ));
                        }
                        // Top-level supported thin pointer/reference and legacy
                        // Ty::I64 integer constants are the ONE position the
                        // backend decodes as a global-address stub — the merge
                        // remaps exactly there, so the stub must resolve within
                        // its OWN module's globals (the adapter fails closed on
                        // an out-of-range stub; merging one into a larger table
                        // could let a SIBLING silently capture it).
                        if let Some((stub_idx, _)) = decode_body_global_addr_stub(ty, value) {
                            if stub_idx as usize >= m.globals.len() {
                                return Err(format!(
                                    "merge_modules: module {idx} (`{}`) function `{}` \
                                         carries a global-address stub referencing global \
                                         index {stub_idx} but the module has only {} \
                                         global(s); the backend would fail closed on it, and \
                                         remapping it could capture a sibling's global — \
                                         fail-closed",
                                    m.name,
                                    f.name,
                                    m.globals.len()
                                ));
                            }
                        } else if !matches!(value, Constant::Int(_))
                            && let Some(tagged) = constant_tagged_int_anywhere(value)
                        {
                            // A stub-shaped integer NESTED inside a constant the
                            // backend treats as raw data: refuse to guess.
                            return Err(format!(
                                "merge_modules: module {idx} (`{}`) function `{}` embeds the \
                                 stub-tagged integer {tagged:#x} inside a nested constant, a \
                                 position the backend does not decode as a global-address \
                                 stub; cannot prove it is plain data — fail-closed",
                                m.name, f.name
                            ));
                        }
                    }
                    Inst::Switch { cases, .. } => {
                        for c in cases {
                            if let Some(why) = constant_batch_deferred(&c.value) {
                                return Err(format!(
                                    "merge_modules: module {idx} (`{}`) function `{}` has a \
                                     switch case embedding a constant the backend fails closed \
                                     on ({why}); fail-closed",
                                    m.name, f.name
                                ));
                            }
                            if let Some(fid) = constant_dangling_funcid(&c.value, m) {
                                return Err(format!(
                                    "merge_modules: module {idx} (`{}`) function `{}` has a \
                                     switch case referencing FuncId({}) with no matching \
                                     function in its module — fail-closed",
                                    m.name,
                                    f.name,
                                    fid.index()
                                ));
                            }
                            if let Some(tagged) = constant_tagged_int_anywhere(&c.value) {
                                return Err(format!(
                                    "merge_modules: module {idx} (`{}`) function `{}` has a \
                                     switch case carrying the stub-tagged integer {tagged:#x}; \
                                     switch cases are never decoded as global-address stubs, \
                                     but a tag-shaped case value cannot be proven plain data — \
                                     fail-closed",
                                    m.name, f.name
                                ));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

/// Body-constant forms the batch DEFERS because the backend adapter fails
/// closed on them (`trust-cg-lower/src/adapter.rs`): admitting one would only
/// convert that function's per-fn fail-closed into a whole-batch fallback.
/// NOT a remap-soundness restriction — nothing here is module-scoped:
///
/// * `Constant::SymbolAddr` is name-relative (merge-invariant). The adapter
///   lowers addend-zero body constants, while non-zero addends remain
///   unsupported;
/// * a `Constant::Closure` WITH captures has no adapter lowering (only the
///   capture-free form lowers, as a bare function pointer);
/// * `Constant::Bytes` lowers as a complete top-level `[u8; N]` body constant,
///   but not yet as a field nested inside another aggregate constant.
///
/// `FnDef` and capture-free `Closure` constants — at any depth, including
/// inside aggregate/record constants and `Switch` case values — are BATCHABLE:
/// their `FuncId`s are remapped by [`remap_constant`], range-checked by
/// [`check_constant_in_range`], and name-identity-verified by
/// [`verify_function_identity_preservation`]. Exhaustive over `Constant`.
fn body_constant_batch_deferred(module: &Module, ty: &Ty, c: &Constant) -> Option<&'static str> {
    if let Constant::Bytes { data, utf8 } = c {
        let Ty::Array(element, len) = ty else {
            return Some(
                "Constant::Bytes requires a top-level [u8; N] declared type in the adapter",
            );
        };
        if module.types.get(element.as_usize()) != Some(&Ty::U8) {
            return Some(
                "Constant::Bytes requires a top-level [u8; N] declared type whose element TyId resolves to U8",
            );
        }
        if u64::try_from(data.len()).ok() != Some(*len) {
            return Some(
                "Constant::Bytes payload length does not match its top-level [u8; N] declared type",
            );
        }
        if *utf8 && std::str::from_utf8(data).is_err() {
            return Some("Constant::Bytes carries a false UTF-8 validity claim");
        }
        return None;
    }
    constant_batch_deferred(c)
}

fn constant_batch_deferred(c: &Constant) -> Option<&'static str> {
    match c {
        Constant::SymbolAddr { addend: 0, .. } => None,
        Constant::SymbolAddr { .. } => Some(
            "Constant::SymbolAddr with a non-zero addend in a function body — the adapter \
                  lowers only the bare-symbol (addend zero) form",
        ),
        Constant::Closure { captures, .. } => {
            if captures.is_empty() {
                None
            } else {
                Some(
                    "Constant::Closure with captures — the adapter lowers only capture-free \
                      closure constants",
                )
            }
        }
        Constant::FnDef(_) => None,
        // A canonical U128 scalar has faithful field materialization. Bytes is
        // supported only as the complete top-level body constant checked by
        // `body_constant_batch_deferred`; the aggregate filler cannot yet
        // materialize it as a nested array field.
        Constant::U128(_) => None,
        Constant::Bytes { .. } => Some(
            "nested Constant::Bytes — only a complete top-level [u8; N] body constant is lowered",
        ),
        Constant::Aggregate(v)
        | Constant::Array(v)
        | Constant::Vector(v)
        | Constant::Sequence(v)
        | Constant::Set(v) => v.iter().find_map(constant_batch_deferred),
        Constant::Record(fields) => fields.iter().find_map(|(_, e)| constant_batch_deferred(e)),
        Constant::Int(_) | Constant::Float(_) | Constant::Bool(_) | Constant::PhantomData => None,
    }
}

/// Decode the importer's in-band body stub only at its exact typed carriers.
///
/// Rustc const operands may retain any supported thin reference/raw-pointer
/// spelling; `Ty::I64` remains the legacy vtable/address carrier. `Rc` is
/// excluded because its ownership ABI is unsupported, and `Func` because these
/// are data-global rather than code-pointer stubs. This predicate must stay
/// identical to the lower adapter's gate.
fn decode_body_global_addr_stub(ty: &Ty, value: &Constant) -> Option<(u64, u32)> {
    if !matches!(
        ty,
        Ty::I64 | Ty::Ptr | Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_)
    ) {
        return None;
    }
    let Constant::Int(value) = value else {
        return None;
    };
    decode_global_addr_stub(*value)
}

/// First `FuncId` embedded in `c` (a `FnDef` or `Closure` at any constant
/// depth) that has NO matching function in module `m` — the precheck mirror of
/// the dangling-`GlobalAddr` gate. Resolution is by the `Function.id` FIELD
/// (not table position), exactly how the FuncId remap map is keyed and how the
/// backend adapter resolves function-symbol constants. Exhaustive.
fn constant_dangling_funcid(c: &Constant, m: &Module) -> Option<FuncId> {
    let dangling = |fid: FuncId| -> Option<FuncId> {
        if m.functions.iter().any(|f| f.id == fid) {
            None
        } else {
            Some(fid)
        }
    };
    match c {
        Constant::FnDef(fid) => dangling(*fid),
        Constant::Closure { func, captures } => {
            dangling(*func).or_else(|| captures.iter().find_map(|e| constant_dangling_funcid(e, m)))
        }
        Constant::Aggregate(v)
        | Constant::Array(v)
        | Constant::Vector(v)
        | Constant::Sequence(v)
        | Constant::Set(v) => v.iter().find_map(|e| constant_dangling_funcid(e, m)),
        Constant::Record(fields) => fields
            .iter()
            .find_map(|(_, e)| constant_dangling_funcid(e, m)),
        // v24 U128 / v25 Bytes: FuncId-free scalar leaves.
        Constant::Int(_)
        | Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData => None,
    }
}

/// First integer leaf ANYWHERE in `c` (including `c` itself) whose bit pattern
/// matches the global-address stub predicate ([`decode_global_addr_stub`]).
/// Used to fail closed on tag-shaped integers at positions the backend never
/// decodes as stubs (nested constants, switch cases, global initializers) —
/// see the module docs on in-band tag ambiguity. Exhaustive over `Constant`.
fn constant_tagged_int_anywhere(c: &Constant) -> Option<i128> {
    match c {
        Constant::Int(v) => decode_global_addr_stub(*v).map(|_| *v),
        Constant::Aggregate(v)
        | Constant::Array(v)
        | Constant::Vector(v)
        | Constant::Sequence(v)
        | Constant::Set(v) => v.iter().find_map(constant_tagged_int_anywhere),
        Constant::Record(fields) => fields
            .iter()
            .find_map(|(_, e)| constant_tagged_int_anywhere(e)),
        Constant::Closure { captures, .. } => {
            captures.iter().find_map(constant_tagged_int_anywhere)
        }
        // v24 U128 / v25 Bytes: a stub is a tagged u64 packed in i128 —
        // neither carrier can be stub-shaped.
        Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::FnDef(_)
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData => None,
    }
}

/// Validate one global-initializer constant: nothing module-scoped may be
/// embedded (`FnDef`/`Closure` carry `FuncId`s; producers use name-relative
/// `SymbolAddr` in initializers, which needs no remap) and no stub-shaped
/// integer may appear (initializer elements are raw data bytes the backend
/// never decodes as stubs).
fn check_global_initializer_constant(
    init: &Constant,
    module_name: &str,
    idx: usize,
    global_name: &str,
) -> Result<(), String> {
    if let Some(reason) = unsupported_initializer_constant_reason(init) {
        return Err(format!(
            "merge_modules: module {idx} (`{module_name}`) global `{global_name}` initializer \
             contains {reason} — fail-closed"
        ));
    }
    if let Some(tagged) = constant_tagged_int_anywhere(init) {
        return Err(format!(
            "merge_modules: module {idx} (`{module_name}`) global `{global_name}` initializer \
             contains the stub-tagged integer {tagged:#x}; initializer data is never decoded \
             as a global-address stub, but a tag-shaped element cannot be proven plain data — \
             fail-closed"
        ));
    }
    Ok(())
}

/// Explain the first unsupported constant shape embedded in an INITIALIZER.
/// Unlike [`constant_is_unsupported`] (body constants), `SymbolAddr` is ALLOWED
/// here: it is name-relative (nothing to remap) and is exactly how producers
/// place function/data addresses into initializers (vtable slots, fn tables).
fn unsupported_initializer_constant_reason(c: &Constant) -> Option<&'static str> {
    match c {
        Constant::FnDef(_) | Constant::Closure { .. } => Some(
            "a module-scoped function constant (FnDef/Closure); initializers must use \
             name-relative SymbolAddr",
        ),
        Constant::Aggregate(v)
        | Constant::Array(v)
        | Constant::Vector(v)
        | Constant::Sequence(v)
        | Constant::Set(v) => v.iter().find_map(unsupported_initializer_constant_reason),
        Constant::Record(fields) => fields
            .iter()
            .find_map(|(_, e)| unsupported_initializer_constant_reason(e)),
        // v24 U128: the object writer's initializer emission has no verified
        // 16-byte unsigned path yet — fail closed until the B1 adoption wave.
        Constant::U128(_) => Some(
            "a U128 constant; verified 16-byte unsigned initializer emission is not implemented",
        ),
        // v25 Bytes: same — the byte-array initializer path lands with B7.
        Constant::Bytes { .. } => {
            Some("a Bytes constant; verified byte-sequence initializer emission is not implemented")
        }
        Constant::Int(_)
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData => None,
    }
}

/// Count the global-address stubs in one function body: top-level
/// supported thin-pointer/reference or legacy-I64 `Inst::Const {
/// value: Constant::Int }` payloads matching the decode predicate — the EXACT
/// set the backend decodes and the merge remaps.
fn count_global_addr_stubs(f: &Function) -> usize {
    f.blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .filter(|node| {
            matches!(
                &node.inst,
                Inst::Const { ty, value }
                    if decode_body_global_addr_stub(ty, value).is_some()
            )
        })
        .count()
}

// ---------------------------------------------------------------------------
// Globals-table merge (name-keyed dedup + decl->def upgrade)
// ---------------------------------------------------------------------------

/// The merged globals table plus per-module old-index -> merged-index maps.
struct GlobalsAssign {
    merged: Vec<Global>,
    per_module: Vec<HashMap<u32, u32>>,
}

/// Whether `g` is a cross-object IMPORT declaration (no initializer). The
/// precheck already guarantees an initializer-less global has external-ish
/// linkage.
fn global_is_import(g: &Global) -> bool {
    g.initializer.is_none()
}

/// Whether a same-name import/definition pair may be unified decl->def, like a
/// function declaration upgraded by its definition. Sound only when every
/// OBSERVABLE attribute agrees and the definition is itself externally
/// linkable: under separate compilation the import's undefined external is
/// resolved by the linker to exactly such a definition, so unifying them
/// intra-object preserves link semantics. A definition the linker could NOT
/// have seen (Internal/Private) must not silently satisfy an import.
fn global_upgrade_compatible(import: &Global, def: &Global) -> bool {
    import.name == def.name
        && import.ty == def.ty
        && import.mutable == def.mutable
        && import.tls == def.tls
        && matches!(
            def.linkage,
            Linkage::External | Linkage::Weak | Linkage::LinkOnce
        )
}

/// Merge the per-module `globals` tables name-keyed (first-encounter order,
/// deterministic): byte-identical same-name entries dedup to one merged entry;
/// an import is upgraded by a compatible same-name definition (and vice-versa
/// order); ANY other same-name disagreement fails closed — a wrong
/// identification would alias two distinct objects or change initializer
/// bytes, i.e. read/write the wrong data.
fn assign_globals(modules: &[Module]) -> Result<GlobalsAssign, String> {
    let mut name_to_dense: HashMap<String, u32> = HashMap::new();
    let mut merged: Vec<Global> = Vec::new();
    // Which module contributed the current winner (for error messages).
    let mut winner_mod: Vec<usize> = Vec::new();
    let mut per_module: Vec<HashMap<u32, u32>> = Vec::with_capacity(modules.len());
    for (i, m) in modules.iter().enumerate() {
        let mut map = HashMap::new();
        for (gi, g) in m.globals.iter().enumerate() {
            let gi = u32::try_from(gi).map_err(|_| {
                format!("merge_modules: module {i} globals table exceeds u32 id space")
            })?;
            let dense = match name_to_dense.get(&g.name) {
                None => {
                    let d = u32::try_from(merged.len()).map_err(|_| {
                        "merge_modules: merged globals table exceeds u32 id space".to_string()
                    })?;
                    name_to_dense.insert(g.name.clone(), d);
                    merged.push(g.clone());
                    winner_mod.push(i);
                    d
                }
                Some(&d) => {
                    let w = &merged[d as usize];
                    if g == w {
                        // Byte-identical redeclaration. Two IMPORTS of one
                        // external object trivially denote the same storage —
                        // dedup. Two byte-identical DEFINITIONS dedup only
                        // when doing so cannot be observed: immutable data
                        // (every read sees the same bytes; these are private
                        // per-object copies whose address identity is not
                        // guaranteed) with linker-dedupable or module-local
                        // linkage. Identical MUTABLE definitions are TWO
                        // distinct writable objects under separate
                        // compilation — unifying them would alias writes —
                        // and two strong-External definitions would have been
                        // a duplicate-symbol link error: both fail closed.
                        let both_imports = global_is_import(g);
                        let dedupable_defs = !g.mutable
                            && matches!(
                                g.linkage,
                                Linkage::Internal
                                    | Linkage::Private
                                    | Linkage::Weak
                                    | Linkage::LinkOnce
                            );
                        if !(both_imports || dedupable_defs) {
                            return Err(format!(
                                "merge_modules: global `{}` is DEFINED identically by module \
                                 {} (`{}`) and module {i} (`{}`) but is {}; unifying two \
                                 distinct definitions could alias writes or mask a duplicate \
                                 symbol — fail-closed",
                                g.name,
                                winner_mod[d as usize],
                                modules[winner_mod[d as usize]].name,
                                m.name,
                                if g.mutable {
                                    "mutable storage"
                                } else {
                                    "a strong external definition"
                                }
                            ));
                        }
                    } else if global_is_import(w)
                        && !global_is_import(g)
                        && global_upgrade_compatible(w, g)
                    {
                        // decl -> def upgrade.
                        merged[d as usize] = g.clone();
                        winner_mod[d as usize] = i;
                    } else if !global_is_import(w)
                        && global_is_import(g)
                        && global_upgrade_compatible(g, w)
                    {
                        // Existing definition already satisfies this import.
                    } else {
                        return Err(format!(
                            "merge_modules: global `{}` is declared with DIFFERENT content by \
                             module {} (`{}`) and module {i} (`{}`) (initializer/mutability/\
                             linkage/type/TLS mismatch beyond a compatible import<->definition \
                             pair); a wrong identification would resolve to the wrong data — \
                             fail-closed",
                            g.name,
                            winner_mod[d as usize],
                            modules[winner_mod[d as usize]].name,
                            m.name
                        ));
                    }
                    d
                }
            };
            map.insert(gi, dense);
        }
        per_module.push(map);
    }
    Ok(GlobalsAssign { merged, per_module })
}

// ---------------------------------------------------------------------------
// Per-module remap context + primitive id remaps
// ---------------------------------------------------------------------------

/// Everything needed to rewrite one source module's id references into the
/// merged id spaces.
struct ModMaps {
    /// `FuncTyId` shift (concatenated `func_types`).
    func_ty_base: u32,
    /// Source module's `func_types` length (bounds check before shifting).
    func_ty_len: usize,
    /// `ClosureTyId` shift (concatenated `closure_types`).
    closure_base: u32,
    /// Source module's `closure_types` length.
    closure_len: usize,
    /// Old `StructId` index -> merged dense id (name-unified).
    struct_map: HashMap<u32, u32>,
    /// Old `EnumId` index -> merged dense id (name-unified).
    enum_map: HashMap<u32, u32>,
    /// Old `RecordId` index -> merged dense id (name-unified).
    record_map: HashMap<u32, u32>,
    /// Old `globals` index -> merged dense index (name-unified globals table);
    /// consulted by BOTH global-reference forms (`Inst::GlobalAddr` ids and
    /// `0xFADE` global-address stubs).
    global_map: HashMap<u32, u32>,
    /// Old `TyId` index -> merged interned id (hash-consed `types`).
    ty_map: HashMap<u32, u32>,
    /// Old `files` index -> merged interned index.
    file_map: HashMap<u32, u32>,
    /// Source module's `files` length.
    files_len: usize,
}

/// Shift a concatenated-table id by `base`, first bounds-checking it against
/// the SOURCE module's table so a dangling input id can never silently alias
/// another module's entry after the shift.
fn shifted(idx: u32, base: u32, len: usize, what: &str) -> Result<u32, String> {
    if (idx as usize) >= len {
        return Err(format!(
            "merge_modules: {what} id {idx} is out of range for its source module \
             (table has {len} entr{})",
            if len == 1 { "y" } else { "ies" }
        ));
    }
    idx.checked_add(base)
        .ok_or_else(|| format!("merge_modules: remapped {what} exceeds u32 id space"))
}

/// Resolve an old id through a per-module map; a missing entry is a dangling
/// reference in the input — fail-closed.
fn mapped(map: &HashMap<u32, u32>, idx: u32, what: &str) -> Result<u32, String> {
    map.get(&idx).copied().ok_or_else(|| {
        format!(
            "merge_modules: {what} id {idx} has no matching definition in its source module \
             (dangling reference)"
        )
    })
}

/// Compute concat base offsets (with u32 id-space checks) for an unnamed table.
fn concat_bases(
    modules: &[Module],
    what: &str,
    len: impl Fn(&Module) -> usize,
) -> Result<Vec<u32>, String> {
    let mut bases = vec![0u32; modules.len()];
    let mut acc: u32 = 0;
    for (i, m) in modules.iter().enumerate() {
        bases[i] = acc;
        acc = acc
            .checked_add(u32::try_from(len(m)).map_err(|_| {
                format!("merge_modules: module {i} {what} table exceeds u32 id space")
            })?)
            .ok_or_else(|| format!("merge_modules: merged {what} table exceeds u32 id space"))?;
    }
    Ok(bases)
}

// ---------------------------------------------------------------------------
// Type remap (exhaustive over `Ty`)
// ---------------------------------------------------------------------------

/// Remap every module-scoped id embedded in a `Ty`. `resolve_tyid` supplies the
/// `TyId` mapping (a plain map lookup after interning; the interner itself
/// during interning). Exhaustive match: a new `Ty` variant fails compilation
/// here instead of being silently passed through un-remapped.
fn remap_ty(
    ty: &Ty,
    m: &ModMaps,
    resolve_tyid: &mut dyn FnMut(u32) -> Result<u32, String>,
) -> Result<Ty, String> {
    Ok(match ty {
        Ty::Func(ftid) => Ty::Func(FuncTyId::new(shifted(
            ftid.index(),
            m.func_ty_base,
            m.func_ty_len,
            "Ty::Func func_type",
        )?)),
        Ty::Closure(cid) => Ty::Closure(ClosureTyId::new(shifted(
            cid.index(),
            m.closure_base,
            m.closure_len,
            "Ty::Closure closure_type",
        )?)),
        Ty::Struct(sid) => Ty::Struct(StructId::new(mapped(
            &m.struct_map,
            sid.index(),
            "Ty::Struct struct",
        )?)),
        Ty::Enum(eid) => Ty::Enum(EnumId::new(mapped(&m.enum_map, eid.index(), "Ty::Enum enum")?)),
        Ty::Record(rid) => Ty::Record(RecordId::new(mapped(
            &m.record_map,
            rid.index(),
            "Ty::Record record",
        )?)),
        Ty::Array(tid, n) => Ty::Array(TyId::new(resolve_tyid(tid.index())?), *n),
        Ty::Set(tid, repr) => Ty::Set(TyId::new(resolve_tyid(tid.index())?), *repr),
        Ty::Sequence(tid) => Ty::Sequence(TyId::new(resolve_tyid(tid.index())?)),
        Ty::Refine(_, _) => {
            return Err(
                "merge_modules: Ty::Refine is not batch-mergeable until content-interned \
                 predicate provenance is remapped and consumed — fail-closed"
                    .to_string(),
            );
        }
        Ty::FatPtr(FatPtrKind::Slice(tid)) => {
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(resolve_tyid(tid.index())?)))
        }
        // `Str` carries nothing; `TraitObject::trait_id` indexes no module
        // table (nothing to remap, nothing that can dangle) — pass through.
        Ty::FatPtr(k @ (FatPtrKind::Str | FatPtrKind::TraitObject { .. })) => Ty::FatPtr(*k),
        Ty::Vector(inner, n) => Ty::Vector(Box::new(remap_ty(inner, m, resolve_tyid)?), *n),
        Ty::Ref(inner) => Ty::Ref(Box::new(remap_ty(inner, m, resolve_tyid)?)),
        Ty::RefMut(inner) => Ty::RefMut(Box::new(remap_ty(inner, m, resolve_tyid)?)),
        Ty::PtrConst(inner) => Ty::PtrConst(Box::new(remap_ty(inner, m, resolve_tyid)?)),
        Ty::PtrMut(inner) => Ty::PtrMut(Box::new(remap_ty(inner, m, resolve_tyid)?)),
        Ty::Rc(inner) => Ty::Rc(Box::new(remap_ty(inner, m, resolve_tyid)?)),
        Ty::Tuple(elems) => Ty::Tuple(
            elems
                .iter()
                .map(|t| remap_ty(t, m, resolve_tyid))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Ptr
        | Ty::Unit
        // trust-ir v25 B1 scalars + Error: table-reference-free leaves,
        // nothing to shift (Error never merges — rejected upstream).
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::Error
        | Ty::Never => ty.clone(),
    })
}

/// [`remap_ty`] with the FINAL (post-interning) `TyId` map.
fn remap_ty_final(ty: &Ty, m: &ModMaps) -> Result<Ty, String> {
    remap_ty(ty, m, &mut |tid| mapped(&m.ty_map, tid, "TyId types-table"))
}

/// Hash-consing interner for the unnamed `types` tables. Each entry is
/// recursively remapped (following intra-table `TyId` links) and interned by
/// its fully-remapped content, so identical entries across modules collapse to
/// one merged id. Deterministic: entries are visited in (module, index) order.
#[derive(Default)]
struct TypeInterner {
    merged: Vec<Ty>,
    index: HashMap<Ty, u32>,
    memo: HashMap<(usize, u32), u32>,
    in_progress: HashSet<(usize, u32)>,
}

impl TypeInterner {
    fn intern(
        &mut self,
        modules: &[Module],
        maps: &[ModMaps],
        mod_idx: usize,
        tyid: u32,
    ) -> Result<u32, String> {
        if let Some(&d) = self.memo.get(&(mod_idx, tyid)) {
            return Ok(d);
        }
        if !self.in_progress.insert((mod_idx, tyid)) {
            return Err(format!(
                "merge_modules: module {mod_idx} types-table entry {tyid} participates in a \
                 TyId cycle that never bottoms out (an infinite by-value type) — fail-closed"
            ));
        }
        let entry = modules[mod_idx].types.get(tyid as usize).ok_or_else(|| {
            format!(
                "merge_modules: TyId types-table id {tyid} has no matching definition in its \
                 source module (dangling reference)"
            )
        })?;
        let remapped = remap_ty(entry, &maps[mod_idx], &mut |tid| {
            self.intern(modules, maps, mod_idx, tid)
        })?;
        self.in_progress.remove(&(mod_idx, tyid));
        let id = match self.index.get(&remapped) {
            Some(&i) => i,
            None => {
                let i = u32::try_from(self.merged.len()).map_err(|_| {
                    "merge_modules: merged types table exceeds u32 id space".to_string()
                })?;
                self.merged.push(remapped.clone());
                self.index.insert(remapped, i);
                i
            }
        };
        self.memo.insert((mod_idx, tyid), id);
        Ok(id)
    }
}

// ---------------------------------------------------------------------------
// Named-table assignment + materialization (structs / enums / records)
// ---------------------------------------------------------------------------

/// Name-keyed merged-id assignment for a NAMED type table. Same-name entries
/// across modules share one dense merged id (first-encounter order); every
/// contributor is recorded so [`materialize_named`] can verify structural
/// identity post-remap.
struct NamedAssign<'a, D> {
    /// contributors[dense] = every (module_index, def) that claimed that name.
    contributors: Vec<Vec<(usize, &'a D)>>,
    /// Per-module old-id -> dense-id maps.
    per_module: Vec<HashMap<u32, u32>>,
}

fn assign_named<'a, D>(
    modules: &'a [Module],
    what: &str,
    table: impl Fn(&'a Module) -> &'a [D],
    key: impl for<'b> Fn(&'b D) -> (&'b str, u32),
) -> Result<NamedAssign<'a, D>, String> {
    let mut name_to_dense: HashMap<String, u32> = HashMap::new();
    let mut contributors: Vec<Vec<(usize, &'a D)>> = Vec::new();
    let mut per_module: Vec<HashMap<u32, u32>> = Vec::with_capacity(modules.len());
    for (i, m) in modules.iter().enumerate() {
        let mut map = HashMap::new();
        for d in table(m) {
            let (name, old_id) = key(d);
            let dense = match name_to_dense.get(name) {
                Some(&x) => x,
                None => {
                    let x = u32::try_from(contributors.len()).map_err(|_| {
                        format!("merge_modules: merged {what} table exceeds u32 id space")
                    })?;
                    name_to_dense.insert(name.to_string(), x);
                    contributors.push(Vec::new());
                    x
                }
            };
            contributors[dense as usize].push((i, d));
            if map.insert(old_id, dense).is_some() {
                return Err(format!(
                    "merge_modules: module {i} (`{}`) declares {what} id {old_id} more than \
                     once; ambiguous source table — fail-closed",
                    m.name
                ));
            }
        }
        per_module.push(map);
    }
    Ok(NamedAssign {
        contributors,
        per_module,
    })
}

/// Materialize a name-unified table: remap the first contributor (the winner)
/// per dense id, then VERIFY every other contributor remaps to an IDENTICAL
/// definition (field-for-field, post-remap). A same-name definition with
/// different structure is rejected — a wrong identification would change
/// layout, i.e. miscompile.
fn materialize_named<D: PartialEq>(
    what: &str,
    modules: &[Module],
    contributors: &[Vec<(usize, &D)>],
    mut remap: impl FnMut(&D, u32, usize) -> Result<D, String>,
    name_of: impl Fn(&D) -> &str,
) -> Result<Vec<D>, String> {
    let mut out = Vec::with_capacity(contributors.len());
    for (dense, contribs) in contributors.iter().enumerate() {
        let dense_id = u32::try_from(dense).expect("dense fits u32 (bounded at assignment)");
        let (wm, wd) = contribs[0];
        let winner = remap(wd, dense_id, wm)?;
        for &(am, ad) in &contribs[1..] {
            let alt = remap(ad, dense_id, am)?;
            if alt != winner {
                return Err(format!(
                    "merge_modules: {what} `{}` is defined with DIFFERENT structure by \
                     module {wm} (`{}`) and module {am} (`{}`); identically-named types must \
                     be structurally identical (post-remap) to merge — fail-closed, a wrong \
                     identification would change layout",
                    name_of(&winner),
                    modules[wm].name,
                    modules[am].name
                ));
            }
        }
        out.push(winner);
    }
    Ok(out)
}

fn remap_field_defs(fields: &[FieldDef], mm: &ModMaps) -> Result<Vec<FieldDef>, String> {
    fields
        .iter()
        .map(|f| {
            Ok(FieldDef {
                name: f.name.clone(),
                ty: remap_ty_final(&f.ty, mm)?,
                offset: f.offset,
            })
        })
        .collect()
}

fn remap_struct_def(sd: &StructDef, dense: u32, mm: &ModMaps) -> Result<StructDef, String> {
    Ok(StructDef {
        id: StructId::new(dense),
        name: sd.name.clone(),
        fields: remap_field_defs(&sd.fields, mm)?,
        size: sd.size,
        align: sd.align,
        repr: sd.repr,
    })
}

fn remap_enum_def(ed: &EnumDef, dense: u32, mm: &ModMaps) -> Result<EnumDef, String> {
    Ok(EnumDef {
        id: EnumId::new(dense),
        name: ed.name.clone(),
        variants: ed
            .variants
            .iter()
            .map(|v| {
                Ok(EnumVariant {
                    name: v.name.clone(),
                    fields: v
                        .fields
                        .iter()
                        .map(|t| remap_ty_final(t, mm))
                        .collect::<Result<Vec<_>, String>>()?,
                    field_names: v.field_names.clone(),
                })
            })
            .collect::<Result<Vec<_>, String>>()?,
        discriminants: ed.discriminants.clone(),
        repr: ed.repr,
        layout: ed.layout.clone(),
    })
}

fn remap_record_def(rd: &RecordDef, dense: u32, mm: &ModMaps) -> Result<RecordDef, String> {
    Ok(RecordDef {
        id: RecordId::new(dense),
        name: rd.name.clone(),
        fields: remap_field_defs(&rd.fields, mm)?,
    })
}

// ---------------------------------------------------------------------------
// Instruction / constant remap (exhaustive over `Inst`)
// ---------------------------------------------------------------------------

/// Rewrite every module-scoped id inside one instruction: embedded `Ty`s
/// (through [`remap_ty_final`]), `FuncId`s, the `CallIndirect` signature,
/// global references (`Inst::GlobalAddr` ids and typed top-level
/// `Constant::Int` global-address stubs, re-packed via [`crate::global_stub`]
/// codec; `stub_count` is incremented per stub rewritten so the caller can
/// enforce the none-missed count invariant), and constants (including
/// `Switch` case values). Exhaustive match: a new `Inst` variant fails
/// compilation here instead of being silently skipped. [`precheck_module`]
/// additionally gates which forms may appear in the current slice; the
/// handled-but-prechecked-away forms (`SeqMap*`, adapter-fail-closed constant
/// shapes) keep the remap forward-compatible.
fn remap_inst(
    inst: &mut Inst,
    mm: &ModMaps,
    fid_map: &HashMap<u32, u32>,
    stub_count: &mut usize,
) -> Result<(), String> {
    let remap_fid = |fid: &mut FuncId| -> Result<(), String> {
        let new = fid_map.get(&fid.index()).ok_or_else(|| {
            format!(
                "merge_modules: instruction references FuncId({}) with no matching function in \
                 its source module",
                fid.index()
            )
        })?;
        *fid = FuncId::new(*new);
        Ok(())
    };
    let rt = |ty: &mut Ty| -> Result<(), String> {
        *ty = remap_ty_final(ty, mm)?;
        Ok(())
    };
    match inst {
        // One embedded value/pointee type.
        Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Overflow { ty, .. }
        | Inst::ICmp { ty, .. }
        | Inst::FCmp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Store { ty, .. }
        | Inst::Alloca { ty, .. }
        | Inst::HeapAlloc { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicStore { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::CmpXchg { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. }
        | Inst::SeqMapAddK { ty, .. }
        | Inst::SeqMapNot { ty, .. }
        | Inst::GEP { pointee_ty: ty, .. }
        | Inst::PtrData { ptr_ty: ty, .. } => rt(ty)?,
        // Two embedded types.
        Inst::Cast { src_ty, dst_ty, .. } => {
            rt(src_ty)?;
            rt(dst_ty)?;
        }
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ..
        }
        | Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            ..
        } => {
            rt(ptr_ty)?;
            rt(metadata_ty)?;
        }
        // Binding-frame slot types.
        Inst::OpenFrame { def } => {
            for slot in &mut def.slots {
                rt(&mut slot.ty)?;
            }
        }
        // Type + constant payload. A top-level supported thin pointer/reference
        // or legacy Ty::I64 integer constant is the ONE position the backend
        // decodes as a global-address stub, so it is the ONE position the merge
        // re-packs (the typed decode predicate is an exact mirror of the
        // adapter's). Everything else defers to the constant walker, which
        // rejects tag-shaped integers anywhere the backend would NOT decode them.
        Inst::Const { ty, value } => {
            rt(ty)?;
            if let Some((stub_idx, offset)) = decode_body_global_addr_stub(ty, value) {
                let stub_idx =
                    u32::try_from(stub_idx).expect("stub index fits u32 (16-bit encode field)");
                let merged_idx = mapped(&mm.global_map, stub_idx, "global-address stub global")?;
                let new = encode_global_addr_stub(u64::from(merged_idx), u64::from(offset))
                    .map_err(|e| format!("merge_modules: {e}"))?;
                *value = Constant::Int(new);
                *stub_count += 1;
            } else if !matches!(value, Constant::Int(_)) {
                // A plain (non-stub or non-address-carrier) constant carries no global id.
                // Walk it for embedded function ids and preserve every numeric
                // leaf bit-identically.
                remap_constant(value, fid_map)?;
            }
        }
        // Case values are constants (may embed FuncIds).
        Inst::Switch { cases, .. } => {
            for case in cases.iter_mut() {
                remap_constant(&mut case.value, fid_map)?;
            }
        }
        // Direct function references.
        Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => remap_fid(callee)?,
        Inst::SeqMap { ty, fwd, .. } => {
            rt(ty)?;
            remap_fid(fwd)?;
        }
        Inst::CallIndirect { sig, .. } => {
            *sig = FuncTyId::new(shifted(
                sig.index(),
                mm.func_ty_base,
                mm.func_ty_len,
                "CallIndirect.sig func_type",
            )?);
        }
        // Direct global reference by id: a plain index remap through the
        // name-unified merged globals table.
        Inst::GlobalAddr { global } => {
            let new = mapped(&mm.global_map, global.index(), "Inst::GlobalAddr global")?;
            *global = GlobalId::new(new);
        }
        // Rejected by the precheck; hitting it here is a gate bypass.
        Inst::DialectOp(_) => {
            return Err(
                "merge_modules: Inst::DialectOp reached the remapper (precheck bypass); \
                 dialect ops are opaque and are fail-closed"
                    .to_string(),
            );
        }
        // No module-scoped payload (values/blocks are function-local).
        Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Return { .. }
        | Inst::NullPtr
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. }
        | Inst::BindSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. } => {}
    }
    Ok(())
}

/// Rewrite `FuncId`s embedded in a constant (`FnDef`, `Closure`, and their
/// nested aggregate constants). Constants embed no type-table ids. Exhaustive.
fn remap_constant(c: &mut Constant, fid_map: &HashMap<u32, u32>) -> Result<(), String> {
    let remap_fid = |fid: &mut FuncId| -> Result<(), String> {
        let new = fid_map.get(&fid.index()).ok_or_else(|| {
            format!(
                "merge_modules: constant references FuncId({}) with no matching function in its \
                 source module",
                fid.index()
            )
        })?;
        *fid = FuncId::new(*new);
        Ok(())
    };
    match c {
        Constant::FnDef(fid) => remap_fid(fid)?,
        Constant::Closure { func, captures } => {
            remap_fid(func)?;
            for cap in captures {
                remap_constant(cap, fid_map)?;
            }
        }
        Constant::Aggregate(v)
        | Constant::Array(v)
        | Constant::Vector(v)
        | Constant::Sequence(v)
        | Constant::Set(v) => {
            for e in v {
                remap_constant(e, fid_map)?;
            }
        }
        Constant::Record(fields) => {
            for (_, e) in fields {
                remap_constant(e, fid_map)?;
            }
        }
        // This walker only ever sees NON-decoded constant positions: the
        // interiors of aggregate constants and `Switch` case values (the one
        // decoded position — a typed top-level `Inst::Const` integer — is
        // intercepted in `remap_inst` before recursing here). A stub-shaped
        // integer here is almost certainly plain data, but it cannot be
        // proven so — fail closed rather than guess (see module docs).
        Constant::Int(v) => {
            if decode_global_addr_stub(*v).is_some() {
                return Err(format!(
                    "merge_modules: the stub-tagged integer {v:#x} appears at a constant \
                     position the backend does not decode as a global-address stub (nested \
                     constant / switch case); cannot prove it is plain data — fail-closed"
                ));
            }
        }
        // v24 U128 / v25 Bytes: FuncId-free and never stub-shaped — nothing
        // to remap.
        Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData => {}
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Structural self-check (independent, read-only re-derivation)
// ---------------------------------------------------------------------------

/// Expected merged-table sizes, computed by the merge bookkeeping and
/// re-verified against the assembled module (a mismatch means an entry was
/// dropped or duplicated).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct MergeExpectations {
    pub(crate) functions: usize,
    pub(crate) func_types: usize,
    pub(crate) structs: usize,
    pub(crate) enums: usize,
    pub(crate) records: usize,
    pub(crate) closure_types: usize,
    pub(crate) types: usize,
    pub(crate) files: usize,
    pub(crate) globals: usize,
    /// Total global-address stubs pre-counted across the input winner bodies;
    /// the self-check independently recounts the merged bodies against this
    /// (DEFENSE (i) half 2 — a stub can be neither missed nor invented).
    pub(crate) global_addr_stubs: usize,
}

/// Merged-table sizes used for reference-resolvability checks.
struct TableCounts {
    functions: u32,
    func_types: usize,
    structs: usize,
    enums: usize,
    records: usize,
    closure_types: usize,
    globals: usize,
    types: usize,
}

/// Re-derive the merge invariants directly from the assembled module and return
/// `Err` on any violation. This is the fail-closed gate: a wrong remap surfaces
/// here as a dangling / out-of-range / duplicate / non-dense reference. The
/// walkers here are read-only and INDEPENDENT of the remap code so a remap bug
/// cannot hide its own tracks.
pub(crate) fn structural_self_check(
    merged: &Module,
    expected: &MergeExpectations,
) -> Result<(), String> {
    let check_len = |what: &str, actual: usize, exp: usize| -> Result<(), String> {
        if actual != exp {
            return Err(format!(
                "merge_modules self-check: expected {exp} merged {what}, found {actual} \
                 (an entry was dropped or duplicated)"
            ));
        }
        Ok(())
    };
    check_len("function(s)", merged.functions.len(), expected.functions)?;
    check_len("func_type(s)", merged.func_types.len(), expected.func_types)?;
    check_len("struct(s)", merged.structs.len(), expected.structs)?;
    check_len("enum(s)", merged.enums.len(), expected.enums)?;
    check_len("record(s)", merged.records.len(), expected.records)?;
    check_len(
        "closure type(s)",
        merged.closure_types.len(),
        expected.closure_types,
    )?;
    check_len("types-table entr(ies)", merged.types.len(), expected.types)?;
    check_len("debug file(s)", merged.files.len(), expected.files)?;
    check_len("global(s)", merged.globals.len(), expected.globals)?;

    let counts = TableCounts {
        functions: u32::try_from(merged.functions.len())
            .map_err(|_| "merge_modules self-check: function count exceeds u32".to_string())?,
        func_types: merged.func_types.len(),
        structs: merged.structs.len(),
        enums: merged.enums.len(),
        records: merged.records.len(),
        closure_types: merged.closure_types.len(),
        globals: merged.globals.len(),
        types: merged.types.len(),
    };

    // Globals: unique names; an initializer-less global must be a linkable
    // external import (mirrors the precheck, re-derived on the OUTPUT).
    let mut global_names: HashSet<&str> = HashSet::new();
    for g in &merged.globals {
        if !global_names.insert(g.name.as_str()) {
            return Err(format!(
                "merge_modules self-check: duplicate global name `{}`",
                g.name
            ));
        }
        if g.initializer.is_none()
            && !matches!(
                g.linkage,
                Linkage::External | Linkage::Weak | Linkage::LinkOnce
            )
        {
            return Err(format!(
                "merge_modules self-check: global `{}` has no initializer but non-external \
                 linkage {:?} (not a well-formed import)",
                g.name, g.linkage
            ));
        }
        if let Some(init) = &g.initializer
            && let Some(tagged) = constant_tagged_int_anywhere(init)
        {
            return Err(format!(
                "merge_modules self-check: global `{}` initializer contains the \
                     stub-tagged integer {tagged:#x}",
                g.name
            ));
        }
    }

    // Functions: dense ids, unique symbols, resolvable signature.
    let mut seen_names: HashSet<&str> = HashSet::new();
    for (i, f) in merged.functions.iter().enumerate() {
        if f.id.index() as usize != i {
            return Err(format!(
                "merge_modules self-check: function `{}` at position {i} has non-dense id {} \
                 (expected {i})",
                f.name,
                f.id.index()
            ));
        }
        if !seen_names.insert(f.name.as_str()) {
            return Err(format!(
                "merge_modules self-check: duplicate function symbol `{}`",
                f.name
            ));
        }
        if f.ty.index() as usize >= counts.func_types {
            return Err(format!(
                "merge_modules self-check: function `{}` has Function.ty FuncTyId({}) out of range \
                 (only {} func_type(s))",
                f.name,
                f.ty.index(),
                counts.func_types
            ));
        }
    }

    // Named type tables: dense embedded ids + unique names.
    let mut struct_names: HashSet<&str> = HashSet::new();
    for (i, sd) in merged.structs.iter().enumerate() {
        if sd.id.index() as usize != i {
            return Err(format!(
                "merge_modules self-check: struct `{}` at position {i} has non-dense id {} \
                 (expected {i})",
                sd.name,
                sd.id.index()
            ));
        }
        if !struct_names.insert(sd.name.as_str()) {
            return Err(format!(
                "merge_modules self-check: duplicate struct name `{}`",
                sd.name
            ));
        }
    }
    let mut enum_names: HashSet<&str> = HashSet::new();
    for (i, ed) in merged.enums.iter().enumerate() {
        if ed.id.index() as usize != i {
            return Err(format!(
                "merge_modules self-check: enum `{}` at position {i} has non-dense id {} \
                 (expected {i})",
                ed.name,
                ed.id.index()
            ));
        }
        if !enum_names.insert(ed.name.as_str()) {
            return Err(format!(
                "merge_modules self-check: duplicate enum name `{}`",
                ed.name
            ));
        }
    }
    let mut record_names: HashSet<&str> = HashSet::new();
    for (i, rd) in merged.records.iter().enumerate() {
        if rd.id.index() as usize != i {
            return Err(format!(
                "merge_modules self-check: record `{}` at position {i} has non-dense id {} \
                 (expected {i})",
                rd.name,
                rd.id.index()
            ));
        }
        if !record_names.insert(rd.name.as_str()) {
            return Err(format!(
                "merge_modules self-check: duplicate record name `{}`",
                rd.name
            ));
        }
    }

    // Table contents: every embedded id reference must resolve.
    for (i, ty) in merged.types.iter().enumerate() {
        check_ty_resolvable(ty, &counts, &format!("types-table entry {i}"))?;
    }
    for sd in &merged.structs {
        for field in &sd.fields {
            check_ty_resolvable(&field.ty, &counts, &format!("struct `{}`", sd.name))?;
        }
    }
    for ed in &merged.enums {
        for v in &ed.variants {
            for ty in &v.fields {
                check_ty_resolvable(
                    ty,
                    &counts,
                    &format!("enum `{}` variant `{}`", ed.name, v.name),
                )?;
            }
        }
    }
    for rd in &merged.records {
        for field in &rd.fields {
            check_ty_resolvable(&field.ty, &counts, &format!("record `{}`", rd.name))?;
        }
    }
    for (i, ct) in merged.closure_types.iter().enumerate() {
        if ct.func.index() as usize >= counts.func_types {
            return Err(format!(
                "merge_modules self-check: closure type {i} references FuncTyId({}) out of range \
                 (only {} func_type(s))",
                ct.func.index(),
                counts.func_types
            ));
        }
        for cap in &ct.captures {
            check_ty_resolvable(cap, &counts, &format!("closure type {i}"))?;
        }
    }
    for (i, ft) in merged.func_types.iter().enumerate() {
        for ty in ft.params.iter().chain(ft.returns.iter()) {
            check_ty_resolvable(ty, &counts, &format!("func_type {i}"))?;
        }
    }

    // Every id reference in every body must resolve; instruction and lexical
    // scope spans must index the merged file table when one exists. The lexical
    // scope table is an indexed tree too: entry zero is its sole root, every
    // later parent points strictly backward, and every instruction scope index
    // resolves in the enclosing function.
    // Global-address stubs are re-decoded and recounted here (DEFENSE (i)
    // half 2 + (ii)): every stub must decode to an in-range merged global, its
    // re-encode must round-trip bit-exactly, and the TOTAL must equal the input
    // pre-count — a missed remap that left a dangling source index, or a walk
    // that skipped or fabricated a stub, surfaces here.
    let mut merged_stub_count = 0usize;
    for f in &merged.functions {
        let scope_count = f.scopes.as_ref().map_or(0, Vec::len);
        if let Some(scopes) = &f.scopes {
            if scopes.is_empty() {
                return Err(format!(
                    "merge_modules self-check: function `{}` carries an empty lexical scope \
                     table; use None when no scope tree is available",
                    f.name
                ));
            }
            for (index, scope) in scopes.iter().enumerate() {
                match (index, scope.parent) {
                    (0, None) => {}
                    (0, Some(parent)) => {
                        return Err(format!(
                            "merge_modules self-check: function `{}` lexical scope 0 must be the \
                             root, but names parent {parent}",
                            f.name
                        ));
                    }
                    (_, Some(parent)) if (parent as usize) < index => {}
                    (_, Some(parent)) => {
                        return Err(format!(
                            "merge_modules self-check: function `{}` lexical scope {index} names \
                             non-earlier parent {parent}",
                            f.name
                        ));
                    }
                    (_, None) => {
                        return Err(format!(
                            "merge_modules self-check: function `{}` lexical scope {index} is a \
                             second root",
                            f.name
                        ));
                    }
                }
                if let Some(span) = &scope.span
                    && !merged.files.is_empty()
                    && span.file as usize >= merged.files.len()
                {
                    return Err(format!(
                        "merge_modules self-check: function `{}` has a lexical scope span file \
                         index {} out of range (only {} file(s))",
                        f.name,
                        span.file,
                        merged.files.len()
                    ));
                }
            }
        }
        for b in &f.blocks {
            for (_, ty) in &b.params {
                check_ty_resolvable(ty, &counts, &f.name)?;
            }
            for node in &b.body {
                check_inst_in_range(&node.inst, &counts, &f.name)?;
                if let Some(scope) = node.scope
                    && scope as usize >= scope_count
                {
                    return Err(format!(
                        "merge_modules self-check: function `{}` instruction names lexical scope \
                         index {scope} out of range (only {scope_count} scope(s))",
                        f.name
                    ));
                }
                if let Inst::Const { ty, value } = &node.inst
                    && decode_body_global_addr_stub(ty, value).is_some()
                {
                    merged_stub_count += 1;
                }
                if let Some(span) = &node.span
                    && !merged.files.is_empty()
                    && span.file as usize >= merged.files.len()
                {
                    return Err(format!(
                        "merge_modules self-check: function `{}` has a span file index {} out of \
                         range (only {} file(s))",
                        f.name,
                        span.file,
                        merged.files.len()
                    ));
                }
            }
        }
    }
    if merged_stub_count != expected.global_addr_stubs {
        return Err(format!(
            "merge_modules self-check: expected {} global-address stub(s) in the merged bodies \
             (the input pre-count) but found {merged_stub_count}; a stub was missed or \
             invented — a silent wrong data address",
            expected.global_addr_stubs
        ));
    }
    Ok(())
}

/// Read-only per-instruction reference check (exhaustive over `Inst`, mirroring
/// the remap coverage but implemented independently).
fn check_inst_in_range(inst: &Inst, c: &TableCounts, fname: &str) -> Result<(), String> {
    let check_fid = |fid: FuncId| -> Result<(), String> {
        if fid.index() >= c.functions {
            Err(format!(
                "merge_modules self-check: function `{fname}` calls FuncId({}) which is out of \
                 range (only {} function(s))",
                fid.index(),
                c.functions
            ))
        } else {
            Ok(())
        }
    };
    match inst {
        Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Overflow { ty, .. }
        | Inst::ICmp { ty, .. }
        | Inst::FCmp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Store { ty, .. }
        | Inst::Alloca { ty, .. }
        | Inst::HeapAlloc { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicStore { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::CmpXchg { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. }
        | Inst::SeqMapAddK { ty, .. }
        | Inst::SeqMapNot { ty, .. }
        | Inst::GEP { pointee_ty: ty, .. }
        | Inst::PtrData { ptr_ty: ty, .. } => check_ty_resolvable(ty, c, fname)?,
        Inst::Cast { src_ty, dst_ty, .. } => {
            check_ty_resolvable(src_ty, c, fname)?;
            check_ty_resolvable(dst_ty, c, fname)?;
        }
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ..
        }
        | Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            ..
        } => {
            check_ty_resolvable(ptr_ty, c, fname)?;
            check_ty_resolvable(metadata_ty, c, fname)?;
        }
        Inst::OpenFrame { def } => {
            for slot in &def.slots {
                check_ty_resolvable(&slot.ty, c, fname)?;
            }
        }
        Inst::Const { ty, value } => {
            check_ty_resolvable(ty, c, fname)?;
            // A top-level supported thin pointer/reference or legacy Ty::I64
            // integer matching the stub predicate IS a global-address reference
            // downstream (the adapter decodes exactly these typed carriers):
            // its index must resolve in the merged globals table and its
            // re-encode must round-trip bit-exactly (DEFENSE (ii)). Other
            // numeric declarations remain plain data.
            if let Some((stub_idx, offset)) = decode_body_global_addr_stub(ty, value) {
                let Constant::Int(v) = value else {
                    unreachable!("typed global-address stub decoder accepts only Constant::Int")
                };
                if stub_idx as usize >= c.globals {
                    return Err(format!(
                        "merge_modules self-check: function `{fname}` carries a \
                             global-address stub referencing global index {stub_idx} out of \
                             range (only {} global(s)) — a wrong data address",
                        c.globals
                    ));
                }
                match encode_global_addr_stub(stub_idx, u64::from(offset)) {
                    Ok(re) if re == *v => {}
                    other => {
                        return Err(format!(
                            "merge_modules self-check: function `{fname}` global-address \
                                 stub {v:#x} does not round-trip through the shared codec \
                                 (re-encode gave {other:?})"
                        ));
                    }
                }
            } else if !matches!(value, Constant::Int(_)) {
                check_constant_in_range(value, c.functions, fname)?;
            }
        }
        Inst::Switch { cases, .. } => {
            for case in cases {
                check_constant_in_range(&case.value, c.functions, fname)?;
            }
        }
        Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => check_fid(*callee)?,
        Inst::SeqMap { ty, fwd, .. } => {
            check_ty_resolvable(ty, c, fname)?;
            check_fid(*fwd)?;
        }
        Inst::CallIndirect { sig, .. } => {
            if sig.index() as usize >= c.func_types {
                return Err(format!(
                    "merge_modules self-check: function `{fname}` CallIndirect.sig FuncTyId({}) out \
                     of range (only {} func_type(s))",
                    sig.index(),
                    c.func_types
                ));
            }
        }
        Inst::GlobalAddr { global } => {
            if global.index() as usize >= c.globals {
                return Err(format!(
                    "merge_modules self-check: function `{fname}` references global id {} out \
                     of range (only {} global(s))",
                    global.index(),
                    c.globals
                ));
            }
        }
        // A merged module from this pass must be dialect-free.
        Inst::DialectOp(_) => {
            return Err(format!(
                "merge_modules self-check: function `{fname}` carries an opaque dialect op in a \
                 merge that must be dialect-free"
            ));
        }
        Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Return { .. }
        | Inst::NullPtr
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. }
        | Inst::BindSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. } => {}
    }
    Ok(())
}

/// Read-only constant reference check (exhaustive over `Constant`).
fn check_constant_in_range(c: &Constant, func_count: u32, fname: &str) -> Result<(), String> {
    match c {
        Constant::FnDef(fid) => {
            if fid.index() >= func_count {
                return Err(format!(
                    "merge_modules self-check: function `{fname}` FnDef constant references \
                     FuncId({}) out of range (only {func_count} function(s))",
                    fid.index()
                ));
            }
        }
        Constant::Closure { func, captures } => {
            if func.index() >= func_count {
                return Err(format!(
                    "merge_modules self-check: function `{fname}` Closure constant references \
                     FuncId({}) out of range (only {func_count} function(s))",
                    func.index()
                ));
            }
            for cap in captures {
                check_constant_in_range(cap, func_count, fname)?;
            }
        }
        Constant::Aggregate(v)
        | Constant::Array(v)
        | Constant::Vector(v)
        | Constant::Sequence(v)
        | Constant::Set(v) => {
            for e in v {
                check_constant_in_range(e, func_count, fname)?;
            }
        }
        Constant::Record(fields) => {
            for (_, e) in fields {
                check_constant_in_range(e, func_count, fname)?;
            }
        }
        // Only NON-decoded positions reach this walker (top-level Const
        // integers are handled in `check_inst_in_range`): a stub-shaped
        // integer here must have been rejected by the precheck — its
        // presence in the OUTPUT is a gate bypass.
        Constant::Int(v) => {
            if decode_global_addr_stub(*v).is_some() {
                return Err(format!(
                    "merge_modules self-check: function `{fname}` carries the stub-tagged \
                     integer {v:#x} at a constant position the backend does not decode as a \
                     global-address stub (precheck bypass)"
                ));
            }
        }
        // v24 U128: FuncId-free and never stub-shaped (a stub is u64-sized,
        // canonically spelled Int) — nothing to remap.
        Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData => {}
    }
    Ok(())
}

/// Read-only type reference check (exhaustive over `Ty`): every embedded
/// module-table id must be in range for its merged table. One level deep —
/// the referenced table entries are themselves checked table-by-table in
/// [`structural_self_check`].
fn check_ty_resolvable(ty: &Ty, c: &TableCounts, loc: &str) -> Result<(), String> {
    let oob = |kind: &str, id: u32, count: usize| -> String {
        format!(
            "merge_modules self-check: {loc} references {kind} id {id} out of range \
             (only {count} entr{})",
            if count == 1 { "y" } else { "ies" }
        )
    };
    match ty {
        Ty::Func(id) => {
            if id.index() as usize >= c.func_types {
                return Err(oob("func_type", id.index(), c.func_types));
            }
        }
        Ty::Struct(id) => {
            if id.index() as usize >= c.structs {
                return Err(oob("struct", id.index(), c.structs));
            }
        }
        Ty::Enum(id) => {
            if id.index() as usize >= c.enums {
                return Err(oob("enum", id.index(), c.enums));
            }
        }
        Ty::Record(id) => {
            if id.index() as usize >= c.records {
                return Err(oob("record", id.index(), c.records));
            }
        }
        Ty::Closure(id) => {
            if id.index() as usize >= c.closure_types {
                return Err(oob("closure_type", id.index(), c.closure_types));
            }
        }
        Ty::Array(tid, _) | Ty::Set(tid, _) | Ty::Sequence(tid) => {
            if tid.index() as usize >= c.types {
                return Err(oob("types-table", tid.index(), c.types));
            }
        }
        Ty::Refine(_, _) => {
            return Err(format!(
                "merge_modules self-check: {loc} contains Ty::Refine, but refinement \
                 predicate provenance is not batch-mergeable yet"
            ));
        }
        Ty::FatPtr(FatPtrKind::Slice(tid)) => {
            if tid.index() as usize >= c.types {
                return Err(oob("types-table", tid.index(), c.types));
            }
        }
        Ty::FatPtr(FatPtrKind::Str | FatPtrKind::TraitObject { .. }) => {}
        Ty::Vector(inner, _)
        | Ty::Ref(inner)
        | Ty::RefMut(inner)
        | Ty::PtrConst(inner)
        | Ty::PtrMut(inner)
        | Ty::Rc(inner) => check_ty_resolvable(inner, c, loc)?,
        Ty::Tuple(elems) => {
            for e in elems {
                check_ty_resolvable(e, c, loc)?;
            }
        }
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Ptr
        | Ty::Unit
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::Error
        | Ty::Never => {}
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Lockstep global-reference preservation check (DEFENSE (iii))
// ---------------------------------------------------------------------------

/// Re-walk every merged function body IN LOCKSTEP with its source (winner)
/// body and prove, position by position, that the merge preserved the MEANING
/// of every global reference:
///
/// * a source global-address stub maps to a merged stub with the SAME byte
///   offset that resolves (through the merged `globals` table) to a global
///   with the SAME NAME the source stub resolved to in its own module;
/// * a source `Inst::GlobalAddr` maps to a merged `GlobalAddr` naming the
///   same-named global;
/// * a NON-stub integer constant is BIT-IDENTICAL (the remap must never touch
///   plain data);
/// * a stub is never invented where the source had none, and never dropped.
///
/// Independent by construction: this reads only the ORIGINAL inputs and the
/// FINAL output — none of the remap bookkeeping — so a bug in the remap or in
/// the structural self-check cannot hide here. Name identity is the right
/// semantic anchor: downstream (adapter -> `Opcode::GlobalRef { name }` ->
/// object symbol/reloc) every global resolves by NAME.
fn verify_global_reference_preservation(
    modules: &[Module],
    winners: &[Option<(usize, &Function)>],
    merged: &Module,
) -> Result<(), String> {
    let ierr = |what: &str, fname: &str| -> String {
        format!(
            "merge_modules global-preservation check: function `{fname}`: {what} — the merged \
             body no longer mirrors its source body — fail-closed"
        )
    };
    let mut source_stubs = 0usize;
    let mut merged_stubs = 0usize;
    for (dense, mf) in merged.functions.iter().enumerate() {
        let Some((mod_idx, sf)) = winners.get(dense).copied().flatten() else {
            return Err(ierr("no source winner recorded", &mf.name));
        };
        let src_mod = &modules[mod_idx];
        if sf.blocks.len() != mf.blocks.len() {
            return Err(ierr("block count changed", &mf.name));
        }
        for (sb, mb) in sf.blocks.iter().zip(mf.blocks.iter()) {
            if sb.body.len() != mb.body.len() {
                return Err(ierr("instruction count changed", &mf.name));
            }
            for (sn, mn) in sb.body.iter().zip(mb.body.iter()) {
                match (&sn.inst, &mn.inst) {
                    (
                        Inst::Const {
                            ty: sty,
                            value: sv_const,
                        },
                        Inst::Const {
                            ty: mty,
                            value: mv_const,
                        },
                    ) if matches!(sv_const, Constant::Int(_))
                        && matches!(mv_const, Constant::Int(_)) =>
                    {
                        let Constant::Int(sv) = sv_const else {
                            unreachable!()
                        };
                        let Constant::Int(mv) = mv_const else {
                            unreachable!()
                        };
                        match (
                            decode_body_global_addr_stub(sty, sv_const),
                            decode_body_global_addr_stub(mty, mv_const),
                        ) {
                            (Some((si, so)), Some((mi, mo))) => {
                                source_stubs += 1;
                                merged_stubs += 1;
                                if so != mo {
                                    return Err(ierr(
                                        &format!(
                                            "global-address stub byte offset changed ({so} -> {mo})"
                                        ),
                                        &mf.name,
                                    ));
                                }
                                let sname = src_mod
                                    .globals
                                    .get(si as usize)
                                    .map(|g| g.name.as_str())
                                    .ok_or_else(|| {
                                        ierr(
                                            &format!(
                                                "source stub references missing global index {si}"
                                            ),
                                            &mf.name,
                                        )
                                    })?;
                                let mname = merged
                                    .globals
                                    .get(mi as usize)
                                    .map(|g| g.name.as_str())
                                    .ok_or_else(|| {
                                        ierr(
                                            &format!(
                                                "merged stub references missing global index {mi}"
                                            ),
                                            &mf.name,
                                        )
                                    })?;
                                if sname != mname {
                                    return Err(ierr(
                                        &format!(
                                            "global-address stub RESOLVES TO A DIFFERENT GLOBAL: \
                                         source index {si} -> `{sname}`, merged index {mi} -> \
                                         `{mname}` (a silent wrong data address)"
                                        ),
                                        &mf.name,
                                    ));
                                }
                            }
                            (None, None) => {
                                if sv != mv {
                                    return Err(ierr(
                                        &format!(
                                            "plain integer constant changed ({sv:#x} -> {mv:#x})"
                                        ),
                                        &mf.name,
                                    ));
                                }
                            }
                            (Some(_), None) => {
                                return Err(ierr(
                                    "a global-address stub was DESTROYED by the merge",
                                    &mf.name,
                                ));
                            }
                            (None, Some(_)) => {
                                return Err(ierr(
                                    "a global-address stub was INVENTED by the merge",
                                    &mf.name,
                                ));
                            }
                        }
                    }
                    (Inst::GlobalAddr { global: sg }, Inst::GlobalAddr { global: mg }) => {
                        let sname = src_mod
                            .globals
                            .get(sg.index() as usize)
                            .map(|g| g.name.as_str())
                            .ok_or_else(|| {
                                ierr("source GlobalAddr references a missing global", &mf.name)
                            })?;
                        let mname = merged
                            .globals
                            .get(mg.index() as usize)
                            .map(|g| g.name.as_str())
                            .ok_or_else(|| {
                                ierr("merged GlobalAddr references a missing global", &mf.name)
                            })?;
                        if sname != mname {
                            return Err(ierr(
                                &format!(
                                    "GlobalAddr resolves to a different global \
                                     (`{sname}` -> `{mname}`)"
                                ),
                                &mf.name,
                            ));
                        }
                    }
                    // A global reference must never change instruction FORM.
                    (Inst::GlobalAddr { .. }, _) | (_, Inst::GlobalAddr { .. }) => {
                        return Err(ierr(
                            "a GlobalAddr instruction changed shape across the merge",
                            &mf.name,
                        ));
                    }
                    (Inst::Const { ty, value }, _)
                        if decode_body_global_addr_stub(ty, value).is_some() =>
                    {
                        return Err(ierr(
                            "a stub-carrying Const instruction changed shape across the merge",
                            &mf.name,
                        ));
                    }
                    (_, Inst::Const { ty, value })
                        if decode_body_global_addr_stub(ty, value).is_some() =>
                    {
                        return Err(ierr(
                            "a stub-carrying Const instruction appeared from a different \
                             instruction shape",
                            &mf.name,
                        ));
                    }
                    // All other instruction pairs: id remaps are legitimate;
                    // global references cannot hide in them (stubs are only
                    // decoded at typed top-level Const integers, which the arms
                    // above cover exhaustively for both sides).
                    _ => {}
                }
            }
        }
    }
    if source_stubs != merged_stubs {
        return Err(format!(
            "merge_modules global-preservation check: {source_stubs} source stub(s) vs \
             {merged_stubs} merged stub(s) — count drift"
        ));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Lockstep function-identity preservation check (DEFENSE (iv))
// ---------------------------------------------------------------------------

/// Resolve a `FuncId` to its function NAME by the `Function.id` field — the
/// same resolution rule the remap map and the backend adapter use.
fn func_name_by_id(m: &Module, fid: FuncId) -> Result<&str, String> {
    m.functions
        .iter()
        .find(|f| f.id == fid)
        .map(|f| f.name.as_str())
        .ok_or_else(|| format!("FuncId({}) resolves to no function", fid.index()))
}

/// Re-walk every merged function body IN LOCKSTEP with its source (winner)
/// body and prove, position by position, that the merge preserved every
/// FUNCTION IDENTITY:
///
/// * a `Call`/`Invoke` callee and a `SeqMap.fwd` resolve (by the `Function.id`
///   field) to a function with the SAME NAME as in the source module;
/// * a `FnDef`/`Closure` constant — at ANY depth: nested aggregates, closure
///   captures, `Switch` case values — resolves to the same-named function;
/// * a `CallIndirect.sig` and each `Function.ty` resolve to a name-resolved
///   STRUCTURALLY IDENTICAL signature (arity, varargness, and every parameter/
///   return type compared with module-table ids resolved through their own
///   module's tables — named types by NAME, signature/closure/types-table
///   links followed recursively), and its `calling_conv` is unchanged;
/// * every instruction keeps its exact variant, and every non-identity
///   constant leaf (`Int`/`Float`/`Bool`/`SymbolAddr`/`PhantomData`) rides
///   through bit-identical (`Int` pairs that are BOTH global-address stubs are
///   owned by [`verify_global_reference_preservation`]).
///
/// Independent by construction: reads only the ORIGINAL inputs and the FINAL
/// output — none of the remap bookkeeping — so a bug in the remap or the
/// structural self-check cannot hide here. Name identity is the right semantic
/// anchor: downstream (adapter `translate_function_symbol_const` /
/// `Call` lowering -> `Opcode::GlobalRef`/`ExternRef`/call fixups -> object
/// symbol/reloc) every function resolves by NAME.
fn verify_function_identity_preservation(
    modules: &[Module],
    winners: &[Option<(usize, &Function)>],
    merged: &Module,
) -> Result<(), String> {
    let ierr = |what: &str, fname: &str| -> String {
        format!(
            "merge_modules function-identity check: function `{fname}`: {what} — a function \
             identity no longer mirrors its source body — fail-closed"
        )
    };
    for (dense, mf) in merged.functions.iter().enumerate() {
        let Some((mod_idx, sf)) = winners.get(dense).copied().flatten() else {
            return Err(ierr("no source winner recorded", &mf.name));
        };
        let src_mod = &modules[mod_idx];

        // The function's OWN signature must be name-resolved identical.
        func_tys_equal_name_resolved(src_mod, sf.ty, merged, mf.ty, TY_CMP_DEPTH_LIMIT)
            .map_err(|e| ierr(&format!("Function.ty signature diverged: {e}"), &mf.name))?;

        if sf.blocks.len() != mf.blocks.len() {
            return Err(ierr("block count changed", &mf.name));
        }
        for (sb, mb) in sf.blocks.iter().zip(mf.blocks.iter()) {
            if sb.body.len() != mb.body.len() {
                return Err(ierr("instruction count changed", &mf.name));
            }
            for (sn, mn) in sb.body.iter().zip(mb.body.iter()) {
                // The merge NEVER changes an instruction's variant — remaps
                // are strictly in-place field rewrites. Enforcing this for
                // EVERY pair means an identity-bearing form cannot morph into
                // (or hide behind) a different shape.
                if std::mem::discriminant(&sn.inst) != std::mem::discriminant(&mn.inst) {
                    return Err(ierr(
                        "an instruction changed variant across the merge",
                        &mf.name,
                    ));
                }
                match (&sn.inst, &mn.inst) {
                    (Inst::Call { callee: sc, .. }, Inst::Call { callee: mc, .. })
                    | (Inst::Invoke { callee: sc, .. }, Inst::Invoke { callee: mc, .. })
                    | (Inst::SeqMap { fwd: sc, .. }, Inst::SeqMap { fwd: mc, .. }) => {
                        let sname = func_name_by_id(src_mod, *sc)
                            .map_err(|e| ierr(&format!("source callee: {e}"), &mf.name))?;
                        let mname = func_name_by_id(merged, *mc)
                            .map_err(|e| ierr(&format!("merged callee: {e}"), &mf.name))?;
                        if sname != mname {
                            return Err(ierr(
                                &format!(
                                    "callee RESOLVES TO A DIFFERENT FUNCTION: source \
                                     FuncId({}) -> `{sname}`, merged FuncId({}) -> `{mname}` \
                                     (a call to the wrong function)",
                                    sc.index(),
                                    mc.index()
                                ),
                                &mf.name,
                            ));
                        }
                    }
                    (
                        Inst::CallIndirect {
                            sig: ss,
                            calling_conv: scc,
                            ..
                        },
                        Inst::CallIndirect {
                            sig: ms,
                            calling_conv: mcc,
                            ..
                        },
                    ) => {
                        if scc != mcc {
                            return Err(ierr(
                                "CallIndirect calling convention changed across the merge",
                                &mf.name,
                            ));
                        }
                        func_tys_equal_name_resolved(src_mod, *ss, merged, *ms, TY_CMP_DEPTH_LIMIT)
                            .map_err(|e| {
                                ierr(
                                    &format!(
                                        "CallIndirect.sig signature diverged (a silent ABI \
                                     change): {e}"
                                    ),
                                    &mf.name,
                                )
                            })?;
                    }
                    (Inst::Const { ty: sty, value: sv }, Inst::Const { ty: mty, value: mv })
                        if decode_body_global_addr_stub(sty, sv).is_some()
                            && decode_body_global_addr_stub(mty, mv).is_some() =>
                    {
                        // The independent global-reference preservation walk
                        // already proved this typed stub pair by symbol name and
                        // byte offset; its packed table index is expected to
                        // change across the merge.
                    }
                    (Inst::Const { value: sv, .. }, Inst::Const { value: mv, .. }) => {
                        constants_identity_preserved(sv, src_mod, mv, merged)
                            .map_err(|e| ierr(&e, &mf.name))?;
                    }
                    (Inst::Switch { cases: scs, .. }, Inst::Switch { cases: mcs, .. }) => {
                        if scs.len() != mcs.len() {
                            return Err(ierr("switch case count changed", &mf.name));
                        }
                        for (sc, mc) in scs.iter().zip(mcs.iter()) {
                            constants_identity_preserved(&sc.value, src_mod, &mc.value, merged)
                                .map_err(|e| ierr(&e, &mf.name))?;
                        }
                    }
                    // Every other same-variant pair carries no function
                    // identity (FuncIds live only in the forms above —
                    // enforced by the exhaustive `remap_inst`/
                    // `check_inst_in_range` walkers, which a new variant
                    // breaks at compile time).
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

/// Lockstep source-vs-merged CONSTANT walk for
/// [`verify_function_identity_preservation`]: identical variant shape at every
/// level; `FnDef`/`Closure` FuncIds must resolve to same-named functions;
/// every non-identity leaf must be bit-identical. Typed top-level global-address
/// stubs are intercepted by the instruction walker above after
/// [`verify_global_reference_preservation`] verifies them by name+offset.
fn constants_identity_preserved(
    sc: &Constant,
    src_mod: &Module,
    mc: &Constant,
    merged: &Module,
) -> Result<(), String> {
    match (sc, mc) {
        (Constant::FnDef(sf), Constant::FnDef(mf)) => {
            let sname = func_name_by_id(src_mod, *sf).map_err(|e| format!("source FnDef: {e}"))?;
            let mname = func_name_by_id(merged, *mf).map_err(|e| format!("merged FnDef: {e}"))?;
            if sname != mname {
                return Err(format!(
                    "FnDef constant RESOLVES TO A DIFFERENT FUNCTION: source FuncId({}) -> \
                     `{sname}`, merged FuncId({}) -> `{mname}` (an indirect call through it \
                     would dispatch to the wrong function)",
                    sf.index(),
                    mf.index()
                ));
            }
            Ok(())
        }
        (
            Constant::Closure {
                func: sf,
                captures: scaps,
            },
            Constant::Closure {
                func: mf,
                captures: mcaps,
            },
        ) => {
            let sname =
                func_name_by_id(src_mod, *sf).map_err(|e| format!("source Closure.func: {e}"))?;
            let mname =
                func_name_by_id(merged, *mf).map_err(|e| format!("merged Closure.func: {e}"))?;
            if sname != mname {
                return Err(format!(
                    "Closure constant RESOLVES TO A DIFFERENT FUNCTION: source FuncId({}) -> \
                     `{sname}`, merged FuncId({}) -> `{mname}`",
                    sf.index(),
                    mf.index()
                ));
            }
            if scaps.len() != mcaps.len() {
                return Err("Closure constant capture count changed".to_string());
            }
            for (s, m) in scaps.iter().zip(mcaps.iter()) {
                constants_identity_preserved(s, src_mod, m, merged)?;
            }
            Ok(())
        }
        (Constant::Aggregate(sv), Constant::Aggregate(mv))
        | (Constant::Array(sv), Constant::Array(mv))
        | (Constant::Vector(sv), Constant::Vector(mv))
        | (Constant::Sequence(sv), Constant::Sequence(mv))
        | (Constant::Set(sv), Constant::Set(mv)) => {
            if sv.len() != mv.len() {
                return Err("aggregate constant element count changed".to_string());
            }
            for (s, m) in sv.iter().zip(mv.iter()) {
                constants_identity_preserved(s, src_mod, m, merged)?;
            }
            Ok(())
        }
        (Constant::Record(sfs), Constant::Record(mfs)) => {
            if sfs.len() != mfs.len() {
                return Err("record constant field count changed".to_string());
            }
            for ((sn, s), (mn, m)) in sfs.iter().zip(mfs.iter()) {
                if sn != mn {
                    return Err(format!(
                        "record constant field name changed (`{sn}` -> `{mn}`)"
                    ));
                }
                constants_identity_preserved(s, src_mod, m, merged)?;
            }
            Ok(())
        }
        (Constant::Int(s), Constant::Int(m)) => {
            if s != m {
                Err(format!("integer constant changed ({s:#x} -> {m:#x})"))
            } else {
                Ok(())
            }
        }
        (Constant::U128(s), Constant::U128(m)) => {
            if s != m {
                Err(format!("U128 constant changed ({s:#x} -> {m:#x})"))
            } else {
                Ok(())
            }
        }
        (Constant::Bytes { data: sd, utf8: su }, Constant::Bytes { data: md, utf8: mu }) => {
            if sd != md || su != mu {
                Err("Bytes constant payload or UTF-8 claim changed".to_string())
            } else {
                Ok(())
            }
        }
        (Constant::Float(s), Constant::Float(m)) => {
            if s.to_bits() != m.to_bits() {
                Err("float constant changed (bit pattern)".to_string())
            } else {
                Ok(())
            }
        }
        (Constant::Bool(s), Constant::Bool(m)) => {
            if s != m {
                Err("bool constant changed".to_string())
            } else {
                Ok(())
            }
        }
        (
            Constant::SymbolAddr {
                symbol: ss,
                addend: sa,
            },
            Constant::SymbolAddr {
                symbol: ms,
                addend: ma,
            },
        ) => {
            // Name-relative: must ride through VERBATIM (nothing to remap).
            if ss != ms || sa != ma {
                Err(format!(
                    "SymbolAddr constant changed (`{ss}`+{sa} -> `{ms}`+{ma})"
                ))
            } else {
                Ok(())
            }
        }
        (Constant::PhantomData, Constant::PhantomData) => Ok(()),
        // Different variants: the merge never changes a constant's shape.
        // (This arm is the fail-closed catch-all — a NEW Constant variant
        // still breaks compilation in the exhaustive `remap_constant` /
        // `check_constant_in_range` walkers.)
        (s, m) => Err(format!(
            "constant changed variant across the merge ({s:?} -> {m:?})"
        )),
    }
}

/// Recursion budget for the name-resolved type comparison. The merge already
/// rejects type-table cycles that never bottom out (the interner errors), so
/// well-formed merged modules stay far below this; hitting it fails CLOSED.
const TY_CMP_DEPTH_LIMIT: u32 = 64;

/// Name-resolved structural equality of two `FuncTy`s living in DIFFERENT
/// modules' tables: arity, varargness, and each param/return compared via
/// [`tys_equal_name_resolved`].
fn func_tys_equal_name_resolved(
    sm: &Module,
    s_ftid: FuncTyId,
    mm: &Module,
    m_ftid: FuncTyId,
    depth: u32,
) -> Result<(), String> {
    let sft = sm
        .func_types
        .get(s_ftid.index() as usize)
        .ok_or_else(|| format!("source FuncTyId({}) out of range", s_ftid.index()))?;
    let mft = mm
        .func_types
        .get(m_ftid.index() as usize)
        .ok_or_else(|| format!("merged FuncTyId({}) out of range", m_ftid.index()))?;
    if sft.params.len() != mft.params.len()
        || sft.returns.len() != mft.returns.len()
        || sft.is_vararg != mft.is_vararg
    {
        return Err(format!(
            "signature shape changed ({}/{} params, {}/{} returns, vararg {}/{})",
            sft.params.len(),
            mft.params.len(),
            sft.returns.len(),
            mft.returns.len(),
            sft.is_vararg,
            mft.is_vararg
        ));
    }
    for (s, m) in sft
        .params
        .iter()
        .zip(mft.params.iter())
        .chain(sft.returns.iter().zip(mft.returns.iter()))
    {
        tys_equal_name_resolved(sm, s, mm, m, depth)?;
    }
    Ok(())
}

/// Structural type equality ACROSS two modules with every module-table id
/// resolved through its OWN module's tables: named types (struct/enum/record)
/// compare by NAME (their deep structural agreement is separately enforced by
/// the named-table merge verification); `Func`/`Closure`/types-table links are
/// followed recursively. Exhaustive over `Ty` — a new variant fails
/// compilation here. `depth` guards unbounded table cycles (fail-closed).
fn tys_equal_name_resolved(
    sm: &Module,
    s: &Ty,
    mm: &Module,
    m: &Ty,
    depth: u32,
) -> Result<(), String> {
    let Some(depth) = depth.checked_sub(1) else {
        return Err("type comparison exceeded the recursion budget (table cycle?)".to_string());
    };
    let mismatch = |what: &str| -> String {
        format!("type diverged across the merge ({what}: {s:?} vs {m:?})")
    };
    match (s, m) {
        (Ty::Func(sid), Ty::Func(mid)) => func_tys_equal_name_resolved(sm, *sid, mm, *mid, depth),
        (Ty::Closure(sid), Ty::Closure(mid)) => {
            let sct = sm
                .closure_types
                .get(sid.index() as usize)
                .ok_or_else(|| mismatch("dangling source closure type"))?;
            let mct = mm
                .closure_types
                .get(mid.index() as usize)
                .ok_or_else(|| mismatch("dangling merged closure type"))?;
            func_tys_equal_name_resolved(sm, sct.func, mm, mct.func, depth)?;
            if sct.captures.len() != mct.captures.len() {
                return Err(mismatch("closure capture count"));
            }
            for (sc, mc) in sct.captures.iter().zip(mct.captures.iter()) {
                tys_equal_name_resolved(sm, sc, mm, mc, depth)?;
            }
            Ok(())
        }
        (Ty::Struct(sid), Ty::Struct(mid)) => {
            let sn = sm
                .structs
                .iter()
                .find(|d| d.id == *sid)
                .map(|d| d.name.as_str())
                .ok_or_else(|| mismatch("dangling source struct id"))?;
            let mn = mm
                .structs
                .iter()
                .find(|d| d.id == *mid)
                .map(|d| d.name.as_str())
                .ok_or_else(|| mismatch("dangling merged struct id"))?;
            if sn != mn {
                return Err(mismatch("struct name"));
            }
            Ok(())
        }
        (Ty::Enum(sid), Ty::Enum(mid)) => {
            let sn = sm
                .enums
                .iter()
                .find(|d| d.id == *sid)
                .map(|d| d.name.as_str())
                .ok_or_else(|| mismatch("dangling source enum id"))?;
            let mn = mm
                .enums
                .iter()
                .find(|d| d.id == *mid)
                .map(|d| d.name.as_str())
                .ok_or_else(|| mismatch("dangling merged enum id"))?;
            if sn != mn {
                return Err(mismatch("enum name"));
            }
            Ok(())
        }
        (Ty::Record(sid), Ty::Record(mid)) => {
            let sn = sm
                .records
                .iter()
                .find(|d| d.id == *sid)
                .map(|d| d.name.as_str())
                .ok_or_else(|| mismatch("dangling source record id"))?;
            let mn = mm
                .records
                .iter()
                .find(|d| d.id == *mid)
                .map(|d| d.name.as_str())
                .ok_or_else(|| mismatch("dangling merged record id"))?;
            if sn != mn {
                return Err(mismatch("record name"));
            }
            Ok(())
        }
        (Ty::Array(stid, sn), Ty::Array(mtid, mn)) => {
            if sn != mn {
                return Err(mismatch("element count"));
            }
            let st = sm
                .types
                .get(stid.index() as usize)
                .ok_or_else(|| mismatch("dangling source types-table id"))?;
            let mt = mm
                .types
                .get(mtid.index() as usize)
                .ok_or_else(|| mismatch("dangling merged types-table id"))?;
            tys_equal_name_resolved(sm, st, mm, mt, depth)
        }
        (Ty::Set(stid, sr), Ty::Set(mtid, mr)) => {
            if sr != mr {
                return Err(mismatch("set representation"));
            }
            let st = sm
                .types
                .get(stid.index() as usize)
                .ok_or_else(|| mismatch("dangling source types-table id"))?;
            let mt = mm
                .types
                .get(mtid.index() as usize)
                .ok_or_else(|| mismatch("dangling merged types-table id"))?;
            tys_equal_name_resolved(sm, st, mm, mt, depth)
        }
        (Ty::Sequence(stid), Ty::Sequence(mtid))
        | (Ty::FatPtr(FatPtrKind::Slice(stid)), Ty::FatPtr(FatPtrKind::Slice(mtid))) => {
            let st = sm
                .types
                .get(stid.index() as usize)
                .ok_or_else(|| mismatch("dangling source types-table id"))?;
            let mt = mm
                .types
                .get(mtid.index() as usize)
                .ok_or_else(|| mismatch("dangling merged types-table id"))?;
            tys_equal_name_resolved(sm, st, mm, mt, depth)
        }
        (Ty::FatPtr(FatPtrKind::Str), Ty::FatPtr(FatPtrKind::Str)) => Ok(()),
        (
            Ty::FatPtr(FatPtrKind::TraitObject { trait_id: st }),
            Ty::FatPtr(FatPtrKind::TraitObject { trait_id: mt }),
        ) => {
            // Pass-through field (no module-level trait table): must be equal.
            if st != mt {
                return Err(mismatch("trait object id"));
            }
            Ok(())
        }
        (Ty::Vector(si, sn), Ty::Vector(mi, mn)) => {
            if sn != mn {
                return Err(mismatch("vector lane count"));
            }
            tys_equal_name_resolved(sm, si, mm, mi, depth)
        }
        (Ty::Ref(si), Ty::Ref(mi))
        | (Ty::RefMut(si), Ty::RefMut(mi))
        | (Ty::PtrConst(si), Ty::PtrConst(mi))
        | (Ty::PtrMut(si), Ty::PtrMut(mi))
        | (Ty::Rc(si), Ty::Rc(mi)) => tys_equal_name_resolved(sm, si, mm, mi, depth),
        (Ty::Tuple(se), Ty::Tuple(me)) => {
            if se.len() != me.len() {
                return Err(mismatch("tuple arity"));
            }
            for (st, mt) in se.iter().zip(me.iter()) {
                tys_equal_name_resolved(sm, st, mm, mt, depth)?;
            }
            Ok(())
        }
        (Ty::I8, Ty::I8)
        | (Ty::I16, Ty::I16)
        | (Ty::I32, Ty::I32)
        | (Ty::I64, Ty::I64)
        | (Ty::I128, Ty::I128)
        | (Ty::U8, Ty::U8)
        | (Ty::U16, Ty::U16)
        | (Ty::U32, Ty::U32)
        | (Ty::U64, Ty::U64)
        | (Ty::U128, Ty::U128)
        | (Ty::F16, Ty::F16)
        | (Ty::F32, Ty::F32)
        | (Ty::F64, Ty::F64)
        | (Ty::Bool, Ty::Bool)
        | (Ty::Ptr, Ty::Ptr)
        | (Ty::Unit, Ty::Unit)
        | (Ty::Never, Ty::Never) => Ok(()),
        // Different variants (fail-closed catch-all; a NEW Ty variant still
        // breaks compilation in the exhaustive remap_ty/check_ty_resolvable).
        _ => Err(mismatch("variant")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::proof::ProofContext;
    use trust_ir::{
        BinOp, Block, BlockId, CallingConv, DialectInst, EnumLayoutDescriptor, EnumTagEncoding,
        FunctionSummary, Global, ICmpOp, InstrNode, InterpretValue, Interpreter, Linkage,
        ObligationKind, ProofFormula, ProofId, ProofObligation, ProofStatus, ScopeData, SourceSpan,
        SwitchCase, ValueId,
    };
    use trust_ir_build::ModuleBuilder;

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    // ---- module builders (scalar; the bridge's per-function shape) -------

    /// Module A: defines `call_add_fn(a, b) = identity_fn(a) + b`, calling its
    /// sibling `identity_fn` through an extern DECLARATION (FuncId 1) — exactly
    /// the shape the bridge emits per function today.
    fn build_caller_module() -> Module {
        let mut mb = ModuleBuilder::new("mod_caller");
        let ft_call = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]); // FuncTyId 0
        let ft_ident = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]); // FuncTyId 1
        {
            let mut fb = mb.function("call_add_fn", ft_call); // FuncId 0
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let called = fb.call(FuncId::new(1), vec![a]); // -> sibling identity_fn (extern decl)
            let result = fb.add(Ty::I64, called, b);
            fb.ret(vec![result]);
            fb.build();
        }
        {
            // Bodyless external DECLARATION of the sibling (FuncId 1).
            let fb = mb.function("identity_fn", ft_ident);
            fb.build();
        }
        mb.build()
    }

    /// Module B: defines `identity_fn(a) = a` (FuncId 0).
    fn build_callee_module() -> Module {
        let mut mb = ModuleBuilder::new("mod_callee");
        let ft_ident = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]); // FuncTyId 0
        {
            let mut fb = mb.function("identity_fn", ft_ident); // FuncId 0
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            fb.ret(vec![a]);
            fb.build();
        }
        mb.build()
    }

    fn find_call_callee(f: &Function) -> Option<FuncId> {
        for b in &f.blocks {
            for node in &b.body {
                if let Inst::Call { callee, .. } = &node.inst {
                    return Some(*callee);
                }
            }
        }
        None
    }

    /// Expected sizes for the scalar caller+callee merge.
    fn scalar_expectations() -> MergeExpectations {
        MergeExpectations {
            functions: 2,
            func_types: 3,
            ..Default::default()
        }
    }

    // ---- module builders (aggregate; direct construction like the e2e ABI
    // tests, so ids and instruction shapes are explicit) -------------------

    fn tnode(inst: Inst, results: Vec<u32>) -> InstrNode {
        InstrNode {
            inst,
            results: results.into_iter().map(ValueId::new).collect(),
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        }
    }

    fn tblock(id: u32, params: Vec<(u32, Ty)>, body: Vec<InstrNode>) -> Block {
        Block {
            id: BlockId::new(id),
            params: params
                .into_iter()
                .map(|(val, ty)| (ValueId::new(val), ty))
                .collect(),
            body,
        }
    }

    fn tfunc(id: u32, name: &str, ty: u32, blocks: Vec<Block>) -> Function {
        Function {
            id: FuncId::new(id),
            name: name.to_string(),
            ty: FuncTyId::new(ty),
            entry: BlockId::new(0),
            blocks,
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::External,
            attrs: Default::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }
    }

    fn tsdef(id: u32, name: &str, field_tys: Vec<Ty>) -> StructDef {
        StructDef {
            id: StructId::new(id),
            name: name.to_string(),
            fields: field_tys
                .into_iter()
                .enumerate()
                .map(|(i, ty)| FieldDef {
                    name: format!("f{i}"),
                    ty,
                    offset: None,
                })
                .collect(),
            size: None,
            align: None,
            repr: Default::default(),
        }
    }

    fn tedef(id: u32, name: &str, variants: Vec<(&str, Vec<Ty>)>) -> EnumDef {
        EnumDef::new(
            EnumId::new(id),
            name,
            variants
                .into_iter()
                .map(|(vname, fields)| EnumVariant {
                    name: vname.to_string(),
                    fields,
                    field_names: Vec::new(),
                })
                .collect(),
        )
    }

    fn trdef(id: u32, name: &str, field_tys: Vec<Ty>) -> RecordDef {
        RecordDef {
            id: RecordId::new(id),
            name: name.to_string(),
            fields: field_tys
                .into_iter()
                .enumerate()
                .map(|(i, ty)| FieldDef {
                    name: format!("f{i}"),
                    ty,
                    offset: None,
                })
                .collect(),
        }
    }

    /// A module with one struct (local `StructId(0)`) and one function
    /// `fn_name(x: i64) -> i64` that round-trips `x` through field 0 of that
    /// struct (Undef + InsertField + ExtractField).
    fn one_struct_module(mod_name: &str, struct_name: &str, fn_name: &str) -> Module {
        let s = Ty::Struct(StructId::new(0));
        let mut m = Module::new(mod_name);
        m.structs = vec![tsdef(0, struct_name, vec![Ty::I64])];
        m.func_types = vec![FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        }];
        m.functions = vec![tfunc(
            0,
            fn_name,
            0,
            vec![tblock(
                0,
                vec![(0, Ty::I64)],
                vec![
                    tnode(Inst::Undef { ty: s.clone() }, vec![1]),
                    tnode(
                        Inst::InsertField {
                            ty: s.clone(),
                            aggregate: v(1),
                            field: 0,
                            value: v(0),
                        },
                        vec![2],
                    ),
                    tnode(
                        // Canonical trust-ir convention: ExtractField.ty is the
                        // FIELD (result) type, not the aggregate type.
                        Inst::ExtractField {
                            ty: Ty::I64,
                            aggregate: v(2),
                            field: 0,
                        },
                        vec![3],
                    ),
                    tnode(Inst::Return { values: vec![v(3)] }, vec![]),
                ],
            )],
        )];
        m
    }

    /// First `Ty::Struct` id referenced by any instruction of `f`.
    fn first_struct_ref(f: &Function) -> Option<u32> {
        for b in &f.blocks {
            for node in &b.body {
                let ty = match &node.inst {
                    Inst::Undef { ty }
                    | Inst::Alloca { ty, .. }
                    | Inst::InsertField { ty, .. }
                    | Inst::ExtractField { ty, .. } => ty,
                    _ => continue,
                };
                if let Ty::Struct(sid) = ty {
                    return Some(sid.index());
                }
            }
        }
        None
    }

    // ---- unit tests: FuncId/FuncTyId remap + decl->def dedup --------------

    #[test]
    fn merge_remaps_funcid_and_functyid_and_dedups_decl_into_def() {
        let a = build_caller_module();
        let b = build_callee_module();
        let merged = merge_modules(&[a, b]).expect("global-free scalar merge should succeed");

        // Dense functions, def/def (identity_fn's decl in A upgraded by B's def).
        assert_eq!(merged.functions.len(), 2, "both functions present, deduped");
        assert_eq!(merged.functions[0].id, FuncId::new(0));
        assert_eq!(merged.functions[0].name, "call_add_fn");
        assert!(merged.functions[0].has_body());
        assert_eq!(merged.functions[1].id, FuncId::new(1));
        assert_eq!(merged.functions[1].name, "identity_fn");
        assert!(
            merged.functions[1].has_body(),
            "A's extern DECLARATION of identity_fn must be UPGRADED to B's DEFINITION"
        );

        // FuncId remap: call_add_fn's Call now targets identity_fn's dense id (1).
        assert_eq!(
            find_call_callee(&merged.functions[0]),
            Some(FuncId::new(1)),
            "the sibling call must be remapped to identity_fn's merged dense FuncId"
        );

        // FuncTyId remap: A contributes func_types 0,1; B contributes 2.
        assert_eq!(merged.func_types.len(), 3, "func_types concatenated");
        assert_eq!(
            merged.functions[0].ty,
            FuncTyId::new(0),
            "call_add_fn keeps module A's base-0 signature"
        );
        assert_eq!(
            merged.functions[1].ty,
            FuncTyId::new(2),
            "identity_fn (from module B) is shifted by B's base offset (2)"
        );
        assert_eq!(merged.func_types[2].params, vec![Ty::I64]);
        assert_eq!(merged.func_types[2].returns, vec![Ty::I64]);

        // The merged module validates cleanly under the canonical walker.
        assert!(
            trust_ir_build::validate_module(&merged).is_empty(),
            "merged module must validate cleanly: {:?}",
            trust_ir_build::validate_module(&merged)
        );
    }

    // ---- unit tests: type/aggregate table remap ---------------------------

    #[test]
    fn merge_remaps_colliding_struct_ids_both_present() {
        // Two DISTINCT structs, both StructId(0) in their own modules: the id
        // collision must be resolved by remapping, with BOTH defs present and
        // every body reference retargeted.
        let a = one_struct_module("mod_sa", "APoint", "use_a");
        let b = one_struct_module("mod_sb", "BPair", "use_b");
        let merged = merge_modules(&[a, b]).expect("distinct-struct merge should succeed");

        assert_eq!(merged.structs.len(), 2, "both structs present");
        assert_eq!(merged.structs[0].name, "APoint");
        assert_eq!(merged.structs[0].id, StructId::new(0));
        assert_eq!(merged.structs[1].name, "BPair");
        assert_eq!(merged.structs[1].id, StructId::new(1));

        assert_eq!(
            first_struct_ref(&merged.functions[0]),
            Some(0),
            "use_a's instructions must reference APoint's merged id"
        );
        assert_eq!(
            first_struct_ref(&merged.functions[1]),
            Some(1),
            "use_b's instructions must be REMAPPED to BPair's merged id"
        );
        assert!(
            trust_ir_build::validate_module(&merged).is_empty(),
            "merged module must validate cleanly: {:?}",
            trust_ir_build::validate_module(&merged)
        );
    }

    #[test]
    fn merge_remaps_colliding_enum_and_record_ids() {
        // Module A: enum EA (id 0). Module B: enum EB (id 0) + record RB (id 0).
        let mut a = Module::new("mod_ea");
        a.enums = vec![tedef(0, "EA", vec![("V0", vec![Ty::I64])])];
        a.func_types = vec![FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        }];
        a.functions = vec![tfunc(
            0,
            "ea_fn",
            0,
            vec![tblock(
                0,
                vec![(0, Ty::I64)],
                vec![
                    tnode(
                        Inst::Alloca {
                            ty: Ty::Enum(EnumId::new(0)),
                            count: None,
                            align: None,
                        },
                        vec![1],
                    ),
                    tnode(Inst::Return { values: vec![v(0)] }, vec![]),
                ],
            )],
        )];
        let mut b = Module::new("mod_eb");
        let mut eb = tedef(0, "EB", vec![("W0", vec![]), ("W1", vec![Ty::I64])]);
        eb.variants[1].field_names = vec!["payload".to_string()];
        eb.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Direct { tag_offset: 0 },
            size: 16,
            align: 8,
            variant_field_offsets: vec![vec![], vec![8]],
        });
        b.enums = vec![eb];
        b.records = vec![trdef(0, "RB", vec![Ty::I64])];
        b.func_types = vec![FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        }];
        b.functions = vec![tfunc(
            0,
            "eb_fn",
            0,
            vec![tblock(
                0,
                vec![(0, Ty::I64)],
                vec![
                    tnode(
                        Inst::Alloca {
                            ty: Ty::Enum(EnumId::new(0)),
                            count: None,
                            align: None,
                        },
                        vec![1],
                    ),
                    tnode(
                        Inst::Undef {
                            ty: Ty::Record(RecordId::new(0)),
                        },
                        vec![2],
                    ),
                    tnode(Inst::Return { values: vec![v(0)] }, vec![]),
                ],
            )],
        )];

        let merged = merge_modules(&[a, b]).expect("enum/record merge should succeed");
        assert_eq!(merged.enums.len(), 2);
        assert_eq!(merged.enums[0].name, "EA");
        assert_eq!(merged.enums[0].id, EnumId::new(0));
        assert_eq!(merged.enums[1].name, "EB");
        assert_eq!(merged.enums[1].id, EnumId::new(1));
        assert_eq!(
            merged.enums[1].variants[1].field_names,
            vec!["payload".to_string()],
            "enum field-name fidelity metadata must survive remapping"
        );
        assert_eq!(
            merged.enums[1].layout,
            Some(EnumLayoutDescriptor {
                encoding: EnumTagEncoding::Direct { tag_offset: 0 },
                size: 16,
                align: 8,
                variant_field_offsets: vec![vec![], vec![8]],
            }),
            "normative enum layout descriptors must survive remapping"
        );
        assert_eq!(merged.records.len(), 1);
        assert_eq!(merged.records[0].name, "RB");
        assert_eq!(merged.records[0].id, RecordId::new(0));

        // B's body references must be remapped: Enum(0) -> Enum(1); Record(0)
        // keeps id 0 (records had no collision).
        let eb_fn = &merged.functions[1];
        let mut saw_enum = None;
        let mut saw_record = None;
        for node in &eb_fn.blocks[0].body {
            match &node.inst {
                Inst::Alloca {
                    ty: Ty::Enum(eid), ..
                } => saw_enum = Some(eid.index()),
                Inst::Undef {
                    ty: Ty::Record(rid),
                } => saw_record = Some(rid.index()),
                _ => {}
            }
        }
        assert_eq!(saw_enum, Some(1), "eb_fn's enum reference must be remapped");
        assert_eq!(saw_record, Some(0), "eb_fn's record reference resolves");
    }

    #[test]
    fn merge_dedups_identical_same_name_struct() {
        // Both modules define `Pair {i64, i64}` under the same name: one merged
        // entry, both functions pointing at it.
        let a = one_struct_module("mod_pa", "Pair", "pa_fn");
        let b = one_struct_module("mod_pb", "Pair", "pb_fn");
        let a2 = a.clone();
        let merged = merge_modules(&[a, b]).expect("identical same-name structs must dedup");
        assert_eq!(merged.structs.len(), 1, "same-name identical struct dedups");
        assert_eq!(merged.structs[0].name, "Pair");
        assert_eq!(first_struct_ref(&merged.functions[0]), Some(0));
        assert_eq!(first_struct_ref(&merged.functions[1]), Some(0));

        // The dedup'd def is structurally the input def (modulo the dense id).
        assert_eq!(merged.structs[0].fields, a2.structs[0].fields);
    }

    #[test]
    fn merge_rejects_same_name_different_structure() {
        let a = one_struct_module("mod_ca", "Pair", "ca_fn");
        let mut b = one_struct_module("mod_cb", "Pair", "cb_fn");
        b.structs[0] = tsdef(0, "Pair", vec![Ty::I64, Ty::I32]); // different layout!
        let err = merge_modules(&[a, b])
            .expect_err("same-name struct with different structure must fail closed");
        assert!(
            err.contains("DIFFERENT structure"),
            "rejection must name the structural conflict: {err}"
        );
        assert!(err.contains("Pair"), "rejection must name the type: {err}");
    }

    #[test]
    fn merge_remaps_intra_table_type_refs() {
        // Module A: struct Inner (id 0) + types[0] = I64 (used via Ty::Array).
        let mut a = Module::new("mod_ta");
        a.structs = vec![tsdef(0, "Inner", vec![Ty::I64])];
        a.types = vec![Ty::I64];
        a.func_types = vec![FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        }];
        a.functions = vec![tfunc(
            0,
            "ta_fn",
            0,
            vec![tblock(
                0,
                vec![(0, Ty::I64)],
                vec![
                    tnode(
                        Inst::Alloca {
                            ty: Ty::Array(TyId::new(0), 2),
                            count: None,
                            align: None,
                        },
                        vec![1],
                    ),
                    tnode(Inst::Return { values: vec![v(0)] }, vec![]),
                ],
            )],
        )];

        // Module B: struct Inner2 (id 0), struct Outer (id 1) whose FIELDS
        // reference Inner2 (an intra-struct-table ref) and an Array over the
        // types table; an enum whose VARIANT references Outer; types[0] = I64.
        let mut b = Module::new("mod_tb");
        b.structs = vec![
            tsdef(0, "Inner2", vec![Ty::I64]),
            tsdef(
                1,
                "Outer",
                vec![Ty::Struct(StructId::new(0)), Ty::Array(TyId::new(0), 4)],
            ),
        ];
        b.enums = vec![tedef(
            0,
            "EWrap",
            vec![("V", vec![Ty::Struct(StructId::new(1))])],
        )];
        b.types = vec![Ty::I64];
        b.func_types = vec![FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        }];
        b.functions = vec![tfunc(
            0,
            "tb_fn",
            0,
            vec![tblock(
                0,
                vec![(0, Ty::I64)],
                vec![
                    tnode(
                        Inst::Alloca {
                            ty: Ty::Struct(StructId::new(1)),
                            count: None,
                            align: None,
                        },
                        vec![1],
                    ),
                    tnode(Inst::Return { values: vec![v(0)] }, vec![]),
                ],
            )],
        )];

        let merged = merge_modules(&[a, b]).expect("intra-table-ref merge should succeed");

        // Dense merged structs: Inner@0 (module A), Inner2@1, Outer@2.
        assert_eq!(merged.structs.len(), 3);
        assert_eq!(merged.structs[0].name, "Inner");
        assert_eq!(merged.structs[1].name, "Inner2");
        assert_eq!(merged.structs[2].name, "Outer");

        // Intra-struct-table field ref remapped: Outer.f0 was Struct(0) in B
        // (Inner2) and must now be Struct(1).
        assert_eq!(
            merged.structs[2].fields[0].ty,
            Ty::Struct(StructId::new(1)),
            "Outer's struct-typed field must be remapped to Inner2's merged id"
        );
        // The types table is hash-consed: both modules' `I64` entries collapse.
        assert_eq!(merged.types, vec![Ty::I64], "types table interned/deduped");
        assert_eq!(
            merged.structs[2].fields[1].ty,
            Ty::Array(TyId::new(0), 4),
            "Outer's array field element TyId must resolve into the interned table"
        );
        // Enum variant field remapped: Struct(1) in B (Outer) -> Struct(2).
        assert_eq!(
            merged.enums[0].variants[0].fields[0],
            Ty::Struct(StructId::new(2)),
            "EWrap's variant field must be remapped to Outer's merged id"
        );
        // Bodies: A's array alloca resolves; B's Outer alloca remapped to 2.
        assert_eq!(first_struct_ref(&merged.functions[1]), Some(2));
        assert!(
            trust_ir_build::validate_module(&merged).is_empty(),
            "merged module must validate cleanly: {:?}",
            trust_ir_build::validate_module(&merged)
        );
    }

    // ---- unit tests: fail-closed gates ------------------------------------

    #[test]
    fn batch_eligibility_mirrors_the_precheck() {
        // The ADVISORY pre-filter (used by the bridge to batch a CGU's
        // eligible subset without one ineligible module poisoning the batch)
        // must agree with the precheck: clean per-fn modules — INCLUDING
        // well-formed global-bearing ones (Step 4) — are eligible; a
        // malformed globals table is not.
        assert!(module_batch_eligible(&build_caller_module()).is_ok());
        assert!(module_batch_eligible(&build_callee_module()).is_ok());
        // A well-formed cross-object import (how the bridge references a
        // `static mut`) is NOW eligible.
        let mut g = build_callee_module();
        g.globals.push(import_global("G_STATIC", true));
        assert!(
            module_batch_eligible(&g).is_ok(),
            "a well-formed global import must be batch-eligible (Step 4)"
        );
        // An initializer-less INTERNAL global is neither an import nor a
        // definition — malformed, ineligible.
        let mut bad = build_callee_module();
        bad.globals.push(Global {
            name: "G_BAD".to_string(),
            ty: Ty::I64,
            mutable: false,
            initializer: None,
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        let err = module_batch_eligible(&bad).expect_err("malformed global is ineligible");
        assert!(err.contains("import"), "reason should say why: {err}");
    }

    #[test]
    fn merge_accepts_global_bearing_module_and_carries_the_table() {
        // Step 4: a well-formed global-bearing module now MERGES; the globals
        // table rides into the merged module (dedup rules exercised below).
        let mut a = build_caller_module();
        a.globals.push(import_global("G_STATIC", true));
        let b = build_callee_module();
        let merged = merge_modules(&[a, b]).expect("global-bearing merge should succeed");
        assert_eq!(merged.globals.len(), 1);
        assert_eq!(merged.globals[0].name, "G_STATIC");
        assert!(merged.globals[0].initializer.is_none(), "import preserved");
    }

    #[test]
    fn merge_rejects_dangling_global_address_reference_in_body() {
        // Inst::GlobalAddr referencing a global the module does not have —
        // a dangling reference that cannot be remapped: fail closed.
        let mut b = build_callee_module();
        b.functions[0].blocks[0].body.insert(
            0,
            trust_ir::InstrNode::new(Inst::GlobalAddr {
                global: trust_ir::value::GlobalId::new(0),
            })
            .with_result(ValueId::new(99)),
        );
        let err = merge_modules(&[b]).expect_err("dangling GlobalAddr must be rejected");
        assert!(
            err.contains("global"),
            "reason should mention globals: {err}"
        );
        assert!(
            err.contains("dangling"),
            "reason should say dangling: {err}"
        );
    }

    // ---- unit tests: globals merge + 0xFADE stub remap (Step 4) -----------

    /// An immutable module-local byte-data global (the bridge's const-alloc /
    /// string-literal shape: `{owner}.const.allocN`, Internal, bytes).
    fn byte_global(name: &str, bytes: &[u8]) -> Global {
        Global {
            name: name.to_string(),
            ty: Ty::Ptr,
            mutable: false,
            initializer: Some(Constant::Aggregate(
                bytes
                    .iter()
                    .map(|&b| Constant::Int(i128::from(b)))
                    .collect(),
            )),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        }
    }

    /// A cross-object data import (the bridge's `static mut` reader shape).
    fn import_global(name: &str, mutable: bool) -> Global {
        Global {
            name: name.to_string(),
            ty: Ty::Ptr,
            mutable,
            initializer: None,
            linkage: Linkage::External,
            tls: None,
            align: None,
        }
    }

    #[test]
    fn unsupported_initializer_diagnostics_name_the_actual_constant_shape() {
        let cases = [
            (
                Constant::Aggregate(vec![Constant::FnDef(FuncId::new(0))]),
                "module-scoped function constant (FnDef/Closure)",
            ),
            (
                Constant::Aggregate(vec![Constant::U128(1)]),
                "U128 constant; verified 16-byte unsigned initializer emission is not implemented",
            ),
            (
                Constant::Aggregate(vec![Constant::Bytes {
                    data: b"TIR".to_vec(),
                    utf8: true,
                }]),
                "Bytes constant; verified byte-sequence initializer emission is not implemented",
            ),
        ];

        for (constant, expected) in cases {
            let error = check_global_initializer_constant(&constant, "fixture", 0, "global")
                .expect_err("unsupported initializer shape must fail closed");
            assert!(
                error.contains(expected),
                "diagnostic must name the actual unsupported shape `{expected}`: {error}"
            );
        }
    }

    fn typed_stub_node(carrier: Ty, idx: u64, off: u64, result: u32) -> InstrNode {
        tnode(
            Inst::Const {
                ty: carrier,
                value: Constant::Int(encode_global_addr_stub(idx, off).expect("valid stub")),
            },
            vec![result],
        )
    }

    /// `Inst::Const { ty: I64, value: Int(stub(idx, off)) }` — the bridge's
    /// legacy vtable/global-address emission shape.
    fn stub_node(idx: u64, off: u64, result: u32) -> InstrNode {
        typed_stub_node(Ty::I64, idx, off, result)
    }

    /// Module with the given globals and one `fn_name(x: i64) -> i64` whose
    /// body materializes each `(index, offset)` stub then returns `x`.
    fn globals_module(
        mod_name: &str,
        fn_name: &str,
        globals: Vec<Global>,
        stubs: &[(u64, u64)],
    ) -> Module {
        let mut m = Module::new(mod_name);
        m.globals = globals;
        m.func_types = vec![FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        }];
        let mut body = Vec::new();
        for (k, &(idx, off)) in stubs.iter().enumerate() {
            body.push(stub_node(idx, off, 1 + k as u32));
        }
        body.push(tnode(Inst::Return { values: vec![v(0)] }, vec![]));
        m.functions = vec![tfunc(
            0,
            fn_name,
            0,
            vec![tblock(0, vec![(0, Ty::I64)], body)],
        )];
        m
    }

    fn bytes_body_module(name: &str, nested: bool) -> Module {
        let array_ty = Ty::Array(trust_ir::TyId::new(0), 3);
        let (result_ty, value) = if nested {
            (
                Ty::Tuple(vec![array_ty]),
                Constant::Aggregate(vec![Constant::Bytes {
                    data: b"TIR".to_vec(),
                    utf8: true,
                }]),
            )
        } else {
            (
                array_ty,
                Constant::Bytes {
                    data: b"TIR".to_vec(),
                    utf8: true,
                },
            )
        };

        let mut module = Module::new(name);
        module.types = vec![Ty::U8];
        module.func_types = vec![FuncTy {
            params: vec![],
            returns: vec![result_ty.clone()],
            is_vararg: false,
        }];
        module.functions = vec![tfunc(
            0,
            name,
            0,
            vec![tblock(
                0,
                vec![],
                vec![
                    tnode(
                        Inst::Const {
                            ty: result_ty,
                            value,
                        },
                        vec![0],
                    ),
                    tnode(Inst::Return { values: vec![v(0)] }, vec![]),
                ],
            )],
        )];
        module
    }

    #[test]
    fn tag_shaped_unsigned_body_constant_remains_numeric() {
        let tagged = encode_global_addr_stub(0, 0x1234).expect("valid tag-shaped value");
        let mut m = globals_module("numeric", "numeric_fn", vec![], &[]);
        m.functions[0].blocks[0].body.insert(
            0,
            tnode(
                Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(tagged),
                },
                vec![9],
            ),
        );

        let merged = merge_modules(&[m]).expect("typed unsigned constant is not an address stub");
        assert!(merged.globals.is_empty());
        assert!(matches!(
            &merged.functions[0].blocks[0].body[0].inst,
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(value),
            } if *value == tagged
        ));
    }

    #[test]
    fn all_intentional_thin_pointer_stub_carriers_are_remapped() {
        for carrier in [
            Ty::I64,
            Ty::Ptr,
            Ty::Ref(Box::new(Ty::I32)),
            Ty::RefMut(Box::new(Ty::I32)),
            Ty::PtrConst(Box::new(Ty::I32)),
            Ty::PtrMut(Box::new(Ty::I32)),
        ] {
            let a = globals_module(
                "carrier_a",
                "carrier_a_fn",
                vec![byte_global("carrier.a", &[1])],
                &[],
            );
            let mut b = globals_module(
                "carrier_b",
                "carrier_b_fn",
                vec![byte_global("carrier.b", &[2])],
                &[],
            );
            b.functions[0].blocks[0]
                .body
                .insert(0, typed_stub_node(carrier.clone(), 0, 4, 9));

            let merged = merge_modules(&[a, b]).unwrap_or_else(|error| {
                panic!("{carrier:?} data-global stub must be batch-remapped: {error}")
            });
            let Inst::Const { ty, value } = &merged.functions[1].blocks[0].body[0].inst else {
                panic!("{carrier:?} stub instruction changed shape")
            };
            assert_eq!(ty, &carrier);
            assert_eq!(
                decode_body_global_addr_stub(ty, value),
                Some((1, 4)),
                "{carrier:?} stub must follow carrier.b after carrier.a is prepended"
            );
        }
    }

    #[test]
    fn bytes_batch_eligibility_matches_real_adapter_depth() {
        let top_level = bytes_body_module("top_level_bytes", false);
        assert!(
            trust_ir_build::validate_module(&top_level).is_empty(),
            "top-level Bytes fixture must be valid TrustIr"
        );
        trust_cg_lower::translate_module(&top_level)
            .expect("the adapter supports a complete top-level [u8; N] Bytes constant");
        module_batch_eligible(&top_level)
            .expect("a genuinely lowerable top-level Bytes constant should batch");
        let merged = merge_modules(&[top_level]).expect("top-level Bytes module should merge");
        trust_cg_lower::translate_module(&merged)
            .expect("batching must preserve top-level Bytes lowerability");

        let nested = bytes_body_module("nested_bytes", true);
        assert!(
            trust_ir_build::validate_module(&nested).is_empty(),
            "nested Bytes fixture must be valid TrustIr"
        );
        trust_cg_lower::translate_module(&nested)
            .expect_err("the aggregate filler does not yet lower a nested Bytes field");
        let reason = module_batch_eligible(&nested)
            .expect_err("batching must defer nested Bytes exactly like the adapter");
        assert!(
            reason.contains("nested Constant::Bytes"),
            "deferral must name the unsupported depth: {reason}"
        );

        let mut invalid_utf8 = bytes_body_module("invalid_utf8_bytes", false);
        let Inst::Const {
            value: Constant::Bytes { data, utf8 },
            ..
        } = &mut invalid_utf8.functions[0].blocks[0].body[0].inst
        else {
            panic!("Bytes fixture changed shape")
        };
        *data = vec![0xff, 0xfe, 0xfd];
        *utf8 = true;
        trust_cg_lower::translate_module(&invalid_utf8)
            .expect_err("the adapter rejects a false UTF-8 claim");
        let reason = module_batch_eligible(&invalid_utf8)
            .expect_err("batching must reject the same false UTF-8 claim");
        assert!(reason.contains("UTF-8"), "reason: {reason}");

        let mut wrong_len = bytes_body_module("wrong_len_bytes", false);
        let Inst::Const {
            value: Constant::Bytes { data, .. },
            ..
        } = &mut wrong_len.functions[0].blocks[0].body[0].inst
        else {
            panic!("Bytes fixture changed shape")
        };
        data.pop();
        trust_cg_lower::translate_module(&wrong_len)
            .expect_err("the adapter rejects a Bytes length mismatch");
        let reason = module_batch_eligible(&wrong_len)
            .expect_err("batching must reject the same Bytes length mismatch");
        assert!(reason.contains("length"), "reason: {reason}");
    }

    /// Decode every stub in `f` against `m.globals` -> `(global name, offset)`
    /// in body order — the SEMANTIC meaning of the function's data references.
    fn decoded_stub_names(m: &Module, f: &Function) -> Vec<(String, u32)> {
        f.blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .filter_map(|n| match &n.inst {
                Inst::Const {
                    value: Constant::Int(v),
                    ..
                } => decode_global_addr_stub(*v).map(|(i, o)| {
                    (
                        m.globals
                            .get(i as usize)
                            .map(|g| g.name.clone())
                            .unwrap_or_else(|| format!("<OUT OF RANGE {i}>")),
                        o,
                    )
                }),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn merge_remaps_colliding_global_stub_indices_to_the_right_globals() {
        // Both modules use LOCAL global index 0 (and 1) for DIFFERENT objects
        // — the exact collision batching creates. Each also imports the same
        // shared static. After merging, every stub must still resolve, BY
        // NAME, to the global it named in its source module, offsets intact.
        let a = globals_module(
            "mod_ga",
            "ga_fn",
            vec![
                byte_global("ga_fn.const.alloc1", &[1, 2, 3, 4, 5, 6, 7, 8]),
                import_global("SHARED_STATIC", true),
            ],
            &[(0, 4), (1, 0)],
        );
        let b = globals_module(
            "mod_gb",
            "gb_fn",
            vec![
                byte_global("gb_fn.const.alloc1", &[9, 9]),
                import_global("SHARED_STATIC", true),
            ],
            &[(0, 8), (1, 0)],
        );
        let merged = merge_modules(&[a, b]).expect("global-bearing merge should succeed");

        // Table: first-encounter order, shared import deduped to ONE entry.
        assert_eq!(merged.globals.len(), 3);
        assert_eq!(merged.globals[0].name, "ga_fn.const.alloc1");
        assert_eq!(merged.globals[1].name, "SHARED_STATIC");
        assert_eq!(merged.globals[2].name, "gb_fn.const.alloc1");
        assert!(merged.globals[1].initializer.is_none() && merged.globals[1].mutable);

        // THE soundness assertion: every stub resolves to the same-named
        // global + offset it did in its source module (gb_fn's index-0 stub
        // must NOT capture ga_fn's data).
        assert_eq!(
            decoded_stub_names(&merged, &merged.functions[0]),
            vec![
                ("ga_fn.const.alloc1".to_string(), 4),
                ("SHARED_STATIC".to_string(), 0)
            ]
        );
        assert_eq!(
            decoded_stub_names(&merged, &merged.functions[1]),
            vec![
                ("gb_fn.const.alloc1".to_string(), 8),
                ("SHARED_STATIC".to_string(), 0)
            ]
        );
        // And the raw index really moved (0 -> 2) for module B's data stub.
        let gb_first = merged.functions[1]
            .blocks
            .iter()
            .flat_map(|blk| blk.body.iter())
            .find_map(|n| match &n.inst {
                Inst::Const {
                    value: Constant::Int(vv),
                    ..
                } => decode_global_addr_stub(*vv),
                _ => None,
            })
            .expect("gb_fn keeps its stub");
        assert_eq!(
            gb_first,
            (2, 8),
            "module B's index-0 stub re-packed to merged index 2"
        );
    }

    #[test]
    fn merge_dedups_identical_global_imports_and_rejects_different_content() {
        // Identical imports dedup (exercised above); same-name DIFFERENT
        // initializer bytes must fail closed.
        let a = globals_module(
            "ma",
            "fa",
            vec![byte_global("dup.data", &[1, 2, 3])],
            &[(0, 0)],
        );
        let b = globals_module(
            "mb",
            "fb",
            vec![byte_global("dup.data", &[1, 2, 4])],
            &[(0, 0)],
        );
        let err = merge_modules(&[a, b])
            .expect_err("same-name globals with different bytes must fail closed");
        assert!(
            err.contains("DIFFERENT content"),
            "reason should flag the content conflict: {err}"
        );
    }

    #[test]
    fn merge_upgrades_global_import_to_definition_both_orders() {
        // A same-name import + externally-linkable definition unify decl->def
        // exactly like function declarations — in either encounter order.
        let mut def = byte_global("SHARED_TBL", &[7, 7, 7, 7]);
        def.linkage = Linkage::External;
        let import = Global {
            initializer: None,
            ..def.clone()
        };

        for (first, second, label) in [
            (import.clone(), def.clone(), "import then def"),
            (def.clone(), import.clone(), "def then import"),
        ] {
            let a = globals_module("ma", "fa", vec![first], &[(0, 0)]);
            let b = globals_module("mb", "fb", vec![second], &[(0, 0)]);
            let merged =
                merge_modules(&[a, b]).unwrap_or_else(|e| panic!("{label} must merge: {e}"));
            assert_eq!(merged.globals.len(), 1, "{label}: one unified global");
            assert!(
                merged.globals[0].initializer.is_some(),
                "{label}: the DEFINITION must win the unification"
            );
            // Both functions' stubs resolve to the unified global.
            assert_eq!(
                decoded_stub_names(&merged, &merged.functions[0]),
                vec![("SHARED_TBL".to_string(), 0)]
            );
            assert_eq!(
                decoded_stub_names(&merged, &merged.functions[1]),
                vec![("SHARED_TBL".to_string(), 0)]
            );
        }
    }

    #[test]
    fn merge_rejects_incompatible_import_def_pairs() {
        // Mutability mismatch between import and definition: fail closed.
        let mut def = byte_global("SHARED_TBL", &[7]);
        def.linkage = Linkage::External;
        let a = globals_module("ma", "fa", vec![import_global("SHARED_TBL", true)], &[]);
        let b = globals_module("mb", "fb", vec![def.clone()], &[(0, 0)]);
        let err = merge_modules(&[a, b])
            .expect_err("mutability mismatch between import and def must fail closed");
        assert!(err.contains("DIFFERENT content"), "reason: {err}");

        // An INTERNAL definition must not silently satisfy an import (the
        // linker could never have resolved the import to it).
        let internal_def = byte_global("SHARED_TBL", &[7]); // Internal linkage
        let a2 = globals_module("ma", "fa", vec![import_global("SHARED_TBL", false)], &[]);
        let b2 = globals_module("mb", "fb", vec![internal_def], &[(0, 0)]);
        let err2 = merge_modules(&[a2, b2])
            .expect_err("an Internal def must not satisfy an External import");
        assert!(err2.contains("DIFFERENT content"), "reason: {err2}");
    }

    #[test]
    fn merge_rejects_identical_mutable_definitions() {
        // Two byte-identical MUTABLE definitions are two distinct writable
        // objects under separate compilation; unifying them would alias
        // writes — fail closed.
        let mut g = byte_global("MUT_STATE", &[0, 0, 0, 0]);
        g.mutable = true;
        let a = globals_module("ma", "fa", vec![g.clone()], &[(0, 0)]);
        let b = globals_module("mb", "fb", vec![g], &[(0, 0)]);
        let err =
            merge_modules(&[a, b]).expect_err("identical mutable definitions must not be unified");
        assert!(err.contains("mutable"), "reason should say mutable: {err}");
    }

    #[test]
    fn merge_rejects_stub_referencing_missing_global() {
        // A stub whose index is out of range for its OWN module: the adapter
        // would fail closed on it; merging it into a bigger table could let a
        // sibling's global capture it — must be rejected up front.
        let a = globals_module(
            "ma",
            "fa",
            vec![byte_global("a.data", &[1])],
            &[(1, 0)], // index 1, but only 1 global
        );
        let err = merge_modules(&[a]).expect_err("out-of-range stub index must fail closed");
        assert!(
            err.contains("stub"),
            "reason should mention the stub: {err}"
        );
        assert!(
            err.contains("capture"),
            "reason should explain the capture hazard: {err}"
        );
    }

    #[test]
    fn merge_rejects_tag_shaped_ints_at_never_decoded_positions() {
        let tagged = encode_global_addr_stub(0, 0).unwrap();

        // (a) nested inside an aggregate constant in a body.
        let mut a = globals_module("ma", "fa", vec![byte_global("a.data", &[1])], &[]);
        a.functions[0].blocks[0].body.insert(
            0,
            tnode(
                Inst::Const {
                    ty: Ty::Tuple(vec![Ty::I64, Ty::I64]),
                    value: Constant::Aggregate(vec![Constant::Int(tagged), Constant::Int(1)]),
                },
                vec![9],
            ),
        );
        let err = merge_modules(&[a])
            .expect_err("tag-shaped int nested in an aggregate constant must fail closed");
        assert!(err.contains("stub-tagged"), "reason: {err}");

        // (b) a switch case value.
        let mut b = globals_module("mb", "fb", vec![], &[]);
        b.functions[0].blocks[0].body.insert(
            0,
            tnode(
                Inst::Switch {
                    value: v(0),
                    default: BlockId::new(0),
                    default_args: vec![],
                    cases: vec![SwitchCase {
                        value: Constant::Int(tagged),
                        target: BlockId::new(0),
                        args: vec![],
                    }],
                    exhaustive_enum_unreachable: false,
                },
                vec![],
            ),
        );
        let err = merge_modules(&[b]).expect_err("tag-shaped switch case value must fail closed");
        assert!(err.contains("stub-tagged"), "reason: {err}");

        // (c) a global-initializer element.
        let mut g = byte_global("c.data", &[1]);
        g.initializer = Some(Constant::Aggregate(vec![Constant::Int(tagged)]));
        let c = globals_module("mc", "fc", vec![g], &[]);
        let err = merge_modules(&[c]).expect_err("tag-shaped initializer element must fail closed");
        assert!(err.contains("stub-tagged"), "reason: {err}");
    }

    #[test]
    fn merge_remaps_global_addr_ids_preserving_the_named_global() {
        // Module B references its global #1 via Inst::GlobalAddr; after A's
        // globals are prepended the id must shift to the merged index of the
        // SAME-NAMED global.
        let a = globals_module("ma", "fa", vec![byte_global("a.data", &[1])], &[(0, 0)]);
        let mut b = globals_module(
            "mb",
            "fb",
            vec![byte_global("b.first", &[2]), byte_global("b.second", &[3])],
            &[],
        );
        b.functions[0].blocks[0].body.insert(
            0,
            trust_ir::InstrNode::new(Inst::GlobalAddr {
                global: trust_ir::value::GlobalId::new(1),
            })
            .with_result(ValueId::new(9)),
        );
        let merged = merge_modules(&[a, b]).expect("GlobalAddr merge should succeed");
        let ga = merged.functions[1]
            .blocks
            .iter()
            .flat_map(|blk| blk.body.iter())
            .find_map(|n| match &n.inst {
                Inst::GlobalAddr { global } => Some(global.index()),
                _ => None,
            })
            .expect("fb keeps its GlobalAddr");
        assert_eq!(
            merged.globals[ga as usize].name, "b.second",
            "GlobalAddr must follow its named global through the merge"
        );
    }

    #[test]
    fn structural_self_check_catches_stub_corruption_and_count_drift() {
        let a = globals_module("ma", "fa", vec![byte_global("a.data", &[1])], &[(0, 0)]);
        let b = globals_module("mb", "fb", vec![byte_global("b.data", &[2])], &[(0, 0)]);
        let exp = MergeExpectations {
            functions: 2,
            func_types: 2,
            globals: 2,
            global_addr_stubs: 2,
            ..Default::default()
        };

        // (i) a stub corrupted to an out-of-range index.
        let mut merged = merge_modules(&[a.clone(), b.clone()]).unwrap();
        for blk in &mut merged.functions[0].blocks {
            for n in &mut blk.body {
                if let Inst::Const {
                    value: value @ Constant::Int(_),
                    ..
                } = &mut n.inst
                    && matches!(value, Constant::Int(x) if decode_global_addr_stub(*x).is_some())
                {
                    *value = Constant::Int(encode_global_addr_stub(999, 0).unwrap());
                }
            }
        }
        let err =
            structural_self_check(&merged, &exp).expect_err("an out-of-range stub must be caught");
        assert!(err.contains("out of range"), "reason: {err}");

        // (ii) count drift: a stub silently DESTROYED (replaced by a plain
        // int — simulating a missed remap path that lost the stub).
        let mut merged = merge_modules(&[a.clone(), b.clone()]).unwrap();
        for blk in &mut merged.functions[0].blocks {
            for n in &mut blk.body {
                if let Inst::Const {
                    value: value @ Constant::Int(_),
                    ..
                } = &mut n.inst
                    && matches!(value, Constant::Int(x) if decode_global_addr_stub(*x).is_some())
                {
                    *value = Constant::Int(7);
                }
            }
        }
        let err = structural_self_check(&merged, &exp)
            .expect_err("a vanished stub must be caught by the count");
        assert!(
            err.contains("missed or") || err.contains("stub"),
            "reason: {err}"
        );

        // (iii) globals-table drift (an entry dropped).
        let mut merged = merge_modules(&[a, b]).unwrap();
        merged.globals.pop();
        let err =
            structural_self_check(&merged, &exp).expect_err("a dropped global must be caught");
        assert!(err.contains("dropped or duplicated"), "reason: {err}");
    }

    #[test]
    fn global_preservation_check_catches_wrong_but_in_range_remap() {
        // The nastiest failure mode: a stub remapped to a DIFFERENT but
        // IN-RANGE global — every structural bound holds, the value is a
        // perfectly well-formed stub, and the data address is silently WRONG.
        // Only the lockstep name-identity check can see it.
        let a = globals_module("ma", "fa", vec![byte_global("a.data", &[1])], &[(0, 4)]);
        let b = globals_module("mb", "fb", vec![byte_global("b.data", &[2])], &[(0, 8)]);
        let merged = merge_modules(&[a.clone(), b.clone()]).unwrap();
        let winners: Vec<Option<(usize, &Function)>> =
            vec![Some((0, &a.functions[0])), Some((1, &b.functions[0]))];
        let modules = [a.clone(), b.clone()];

        // Sanity: the honest merge passes the preservation check.
        verify_global_reference_preservation(&modules, &winners, &merged)
            .expect("an honest merge must pass the lockstep check");

        // Corrupt fa's stub to point at b.data's merged slot (index 1 —
        // IN RANGE, well-formed, wrong).
        let mut corrupted = merged.clone();
        for blk in &mut corrupted.functions[0].blocks {
            for n in &mut blk.body {
                if let Inst::Const {
                    value: value @ Constant::Int(_),
                    ..
                } = &mut n.inst
                    && matches!(value, Constant::Int(x) if decode_global_addr_stub(*x).is_some())
                {
                    *value = Constant::Int(encode_global_addr_stub(1, 4).unwrap());
                }
            }
        }
        // The structural self-check CANNOT see this (everything in range)...
        let exp = MergeExpectations {
            functions: 2,
            func_types: 2,
            globals: 2,
            global_addr_stubs: 2,
            ..Default::default()
        };
        structural_self_check(&corrupted, &exp)
            .expect("structural bounds all hold on the corrupted module");
        // ...but the lockstep name-identity check MUST.
        let err = verify_global_reference_preservation(&modules, &winners, &corrupted)
            .expect_err("a wrong-but-in-range stub remap must be caught");
        assert!(
            err.contains("DIFFERENT GLOBAL"),
            "reason must name the class: {err}"
        );

        // And an offset change is caught too.
        let mut corrupted2 = merged.clone();
        for blk in &mut corrupted2.functions[0].blocks {
            for n in &mut blk.body {
                if let Inst::Const {
                    value: value @ Constant::Int(_),
                    ..
                } = &mut n.inst
                    && matches!(value, Constant::Int(x) if decode_global_addr_stub(*x).is_some())
                {
                    *value = Constant::Int(encode_global_addr_stub(0, 12).unwrap());
                }
            }
        }
        let err = verify_global_reference_preservation(&modules, &winners, &corrupted2)
            .expect_err("a changed stub offset must be caught");
        assert!(err.contains("offset"), "reason: {err}");
    }

    #[test]
    fn merge_rejects_duplicate_definition() {
        // Two modules that BOTH define identity_fn — ambiguous, must fail closed.
        let b1 = build_callee_module();
        let b2 = build_callee_module();
        let err =
            merge_modules(&[b1, b2]).expect_err("two definitions of one symbol must be rejected");
        assert!(
            err.contains("duplicate definition"),
            "reason should flag the duplicate definition: {err}"
        );
    }

    #[test]
    fn merge_rejects_proof_obligation_bearing_module() {
        let mut a = build_caller_module();
        a.proof_obligations.push(ProofObligation::new(
            ProofId::new(0),
            ObligationKind::MemorySafety,
            ProofStatus::Pending,
            "vc",
        ));
        let b = build_callee_module();
        let err =
            merge_modules(&[a, b]).expect_err("proof-obligation-bearing input must be rejected");
        assert!(
            err.contains("proof obligation"),
            "reason should mention proof obligations: {err}"
        );
    }

    #[test]
    fn merge_rejects_refinement_predicate_table_instead_of_erasing_provenance() {
        let mut a = build_caller_module();
        a.predicates.push(trust_ir::pred::Pred::Top);

        let err = merge_modules(&[a])
            .expect_err("refinement-predicate-bearing input must remain fail-closed");
        assert!(
            err.contains("refinement predicate"),
            "reason should name refinement predicate provenance: {err}"
        );
    }

    #[test]
    fn merge_rejects_nonempty_function_summary() {
        let mut a = build_caller_module();
        a.functions[0].summary =
            Some(FunctionSummary::new().ensuring(ProofFormula::smtlib2("(> result 0)", "Bool")));
        let b = build_callee_module();
        let err = merge_modules(&[a, b]).expect_err("contract-carrying function must be rejected");
        assert!(
            err.contains("summary"),
            "reason should mention the summary: {err}"
        );
    }

    #[test]
    fn merge_rejects_proof_context_bearing_call() {
        let mut a = build_caller_module();
        for node in &mut a.functions[0].blocks[0].body {
            if matches!(node.inst, Inst::Call { .. }) {
                node.proof_context = Some(ProofContext {
                    assumes: vec![ProofId::new(0)],
                    establishes: vec![],
                });
            }
        }
        let b = build_callee_module();
        let err = merge_modules(&[a, b]).expect_err("ProofContext-carrying call must be rejected");
        assert!(
            err.contains("ProofContext"),
            "reason should mention the ProofContext: {err}"
        );
    }

    #[test]
    fn merge_rejects_dialect_op() {
        let mut b = build_callee_module();
        b.functions[0].blocks[0].body.insert(
            0,
            tnode(
                Inst::DialectOp(Box::new(DialectInst::new("verif", "noop"))),
                vec![],
            ),
        );
        let err = merge_modules(&[b]).expect_err("dialect ops must be rejected");
        assert!(
            err.contains("dialect"),
            "reason should mention dialect ops: {err}"
        );
    }

    #[test]
    fn merge_accepts_fn_pointer_signature_but_fails_closed_on_cyclic_sig() {
        // The fn-pointer SIGNATURE deferral is lifted: a func_type whose param
        // is a (well-formed) fn-pointer type now merges, with the embedded
        // FuncTyId base-shifted like every other signature reference.
        let mut a = build_caller_module();
        a.func_types[0].params[0] = Ty::Func(FuncTyId::new(1)); // -> ft_ident (acyclic)
        let merged = merge_modules(&[a]).expect("fn-pointer signatures now merge");
        assert_eq!(
            merged.func_types[0].params[0],
            Ty::Func(FuncTyId::new(1)),
            "single-module merge keeps the base-0 shift"
        );

        // A SELF-REFERENTIAL signature (ft0's param is fn-ptr-to-ft0 — an
        // infinite type no frontend produces) exceeds the name-resolved
        // comparison budget: fail-closed, never silently admitted.
        let mut b = build_caller_module();
        b.func_types[0].params[0] = Ty::Func(FuncTyId::new(0));
        let err = merge_modules(&[b]).expect_err("cyclic signature must fail closed");
        assert!(
            err.contains("recursion budget"),
            "reason should say why: {err}"
        );
    }

    // ---- unit tests: fn-pointer VALUE surface (the lifted last class) -----

    /// Target module: `fnptr_target(x) = x + x` at FuncId 0 and a DECOY
    /// `fnptr_decoy(x) = x + 1000` at FuncId 1 — same signature, visibly
    /// different math, so a wrong-but-in-range FuncId remap is detectable.
    fn build_fnptr_target_module() -> Module {
        let mut mb = ModuleBuilder::new("mod_fnptr_targets");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]); // FuncTyId 0
        {
            let mut fb = mb.function("fnptr_target", ft); // FuncId 0
            let entry = fb.create_block();
            let x = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let r = fb.add(Ty::I64, x, x);
            fb.ret(vec![r]);
            fb.build();
        }
        {
            let mut fb = mb.function("fnptr_decoy", ft); // FuncId 1
            let entry = fb.create_block();
            let x = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let k = fb.iconst(Ty::I64, 1000);
            let r = fb.add(Ty::I64, x, k);
            fb.ret(vec![r]);
            fb.build();
        }
        mb.build()
    }

    /// Caller module: `fnptr_caller(x)` materializes `FnDef(fnptr_target)`
    /// (declared as ITS OWN FuncId 1), threads it through a `Ty::Func` BLOCK
    /// PARAMETER, and invokes it via `CallIndirect` — the full fn-pointer
    /// value surface in one body.
    fn build_fnptr_caller_module() -> Module {
        let mut m = Module::new("mod_fnptr_caller");
        m.func_types.push(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        }); // FuncTyId 0
        let sig = FuncTyId::new(0);
        let entry = tblock(
            0,
            vec![(0, Ty::I64)],
            vec![
                tnode(
                    Inst::Const {
                        ty: Ty::Func(sig),
                        value: Constant::FnDef(FuncId::new(1)), // sibling decl
                    },
                    vec![1],
                ),
                tnode(
                    Inst::Br {
                        target: BlockId::new(1),
                        args: vec![v(1), v(0)],
                    },
                    vec![],
                ),
            ],
        );
        let join = tblock(
            1,
            vec![(2, Ty::Func(sig)), (3, Ty::I64)], // fn-pointer BLOCK PARAM
            vec![
                tnode(
                    Inst::CallIndirect {
                        callee: v(2),
                        sig,
                        args: vec![v(3)],
                        calling_conv: CallingConv::C,
                    },
                    vec![4],
                ),
                tnode(Inst::Return { values: vec![v(4)] }, vec![]),
            ],
        );
        m.functions
            .push(tfunc(0, "fnptr_caller", 0, vec![entry, join]));
        // Bodyless extern declaration of the target at LOCAL FuncId 1 (the
        // merge must remap it to the target's dense id — which differs).
        m.functions.push(tfunc(1, "fnptr_target", 0, vec![]));
        m
    }

    /// Find the first FnDef constant + the first CallIndirect sig in `f`.
    fn find_fnptr_refs(f: &Function) -> (Option<FuncId>, Option<FuncTyId>) {
        let mut fndef = None;
        let mut sig = None;
        for b in &f.blocks {
            for node in &b.body {
                match &node.inst {
                    Inst::Const {
                        value: Constant::FnDef(fid),
                        ..
                    } => fndef = fndef.or(Some(*fid)),
                    Inst::CallIndirect { sig: s, .. } => sig = sig.or(Some(*s)),
                    _ => {}
                }
            }
        }
        (fndef, sig)
    }

    #[test]
    fn merge_remaps_fnptr_value_surface_end_to_end() {
        let targets = build_fnptr_target_module();
        let caller = build_fnptr_caller_module();
        // BOTH are now batch-eligible (the last ineligibility class lifted).
        assert!(
            module_batch_eligible(&targets).is_ok(),
            "target module must be eligible"
        );
        assert!(
            module_batch_eligible(&caller).is_ok(),
            "fn-pointer caller module must be eligible: {:?}",
            module_batch_eligible(&caller)
        );

        // Merge order [targets, caller] FORCES a FuncId shift: the caller's
        // LOCAL FuncId(1) decl of `fnptr_target` must land on dense id 0;
        // an identity (missed) remap would leave it pointing at
        // `fnptr_decoy` (dense 1) — the wrong function.
        let merged = merge_modules(&[targets, caller]).expect("fn-pointer merge must succeed");
        assert_eq!(merged.functions.len(), 3, "decl->def dedup");
        assert_eq!(merged.functions[0].name, "fnptr_target");
        assert_eq!(merged.functions[1].name, "fnptr_decoy");
        assert_eq!(merged.functions[2].name, "fnptr_caller");

        let (fndef, sig) = find_fnptr_refs(&merged.functions[2]);
        assert_eq!(
            fndef,
            Some(FuncId::new(0)),
            "FnDef constant must resolve to fnptr_target's DEFINITION (dense 0)"
        );
        // The caller's FuncTyId 0 is shifted by the targets module's table
        // length (1) — and the block param's Ty::Func must agree.
        assert_eq!(
            sig,
            Some(FuncTyId::new(1)),
            "CallIndirect.sig must be base-shifted into the merged table"
        );
        assert_eq!(
            merged.functions[2].blocks[1].params[0].1,
            Ty::Func(FuncTyId::new(1)),
            "fn-pointer BLOCK PARAM type must be remapped in lockstep with the sig"
        );
    }

    #[test]
    fn merge_remaps_fndef_inside_aggregates_and_closure_captures() {
        // FnDef/Closure constants at DEPTH: inside an aggregate constant and
        // inside a closure constant's captures. Every embedded FuncId must be
        // remapped; sibling plain data must ride through bit-identical.
        let targets = build_fnptr_target_module();
        let mut caller = build_fnptr_caller_module();
        caller.functions[0].blocks[0].body.insert(
            0,
            tnode(
                Inst::Const {
                    ty: Ty::Tuple(vec![
                        Ty::I64,
                        Ty::Func(FuncTyId::new(0)),
                        Ty::Func(FuncTyId::new(0)),
                    ]),
                    value: Constant::Aggregate(vec![
                        Constant::Int(5),
                        Constant::FnDef(FuncId::new(1)),
                        Constant::Closure {
                            func: FuncId::new(1),
                            captures: vec![Constant::Int(7)],
                        },
                    ]),
                },
                vec![9],
            ),
        );
        // A CAPTURED closure constant is adapter-fail-closed — the module is
        // (correctly) ineligible…
        let err = module_batch_eligible(&caller).expect_err("captured closure stays deferred");
        assert!(err.contains("captures"), "reason: {err}");
        // …so exercise the REMAP surface with a capture-free closure instead.
        if let Inst::Const {
            value: Constant::Aggregate(elems),
            ..
        } = &mut caller.functions[0].blocks[0].body[0].inst
        {
            elems[2] = Constant::Closure {
                func: FuncId::new(1),
                captures: vec![],
            };
        } else {
            panic!("test setup: aggregate constant not found");
        }
        assert!(module_batch_eligible(&caller).is_ok());

        let merged =
            merge_modules(&[targets, caller]).expect("aggregate fn-pointer merge must succeed");
        let Inst::Const {
            value: Constant::Aggregate(elems),
            ..
        } = &merged.functions[2].blocks[0].body[0].inst
        else {
            panic!("merged aggregate constant lost its shape");
        };
        assert_eq!(elems[0], Constant::Int(5), "plain data bit-identical");
        assert_eq!(
            elems[1],
            Constant::FnDef(FuncId::new(0)),
            "nested FnDef remapped to the target's dense id"
        );
        assert_eq!(
            elems[2],
            Constant::Closure {
                func: FuncId::new(0),
                captures: vec![]
            },
            "closure constant FuncId remapped"
        );
    }

    #[test]
    fn fn_pointer_eligibility_defers_adapter_failclosed_forms() {
        // A zero-addend body SymbolAddr is name-relative and the adapter lowers
        // it, so it is batchable and must ride through bit-identically.
        let mut sa = build_fnptr_caller_module();
        sa.functions[0].blocks[0].body.insert(
            0,
            tnode(
                Inst::Const {
                    ty: Ty::Ptr,
                    value: Constant::SymbolAddr {
                        symbol: "some_sym".to_string(),
                        addend: 0,
                    },
                },
                vec![9],
            ),
        );
        assert!(module_batch_eligible(&sa).is_ok());
        let merged = merge_modules(&[sa.clone()]).expect("bare SymbolAddr should batch");
        assert!(matches!(
            &merged.functions[0].blocks[0].body[0].inst,
            Inst::Const {
                value: Constant::SymbolAddr { symbol, addend: 0 },
                ..
            } if symbol == "some_sym"
        ));

        // A non-zero addend is still adapter-fail-closed and therefore remains
        // ineligible, avoiding a whole-batch fallback.
        if let Inst::Const {
            value: Constant::SymbolAddr { addend, .. },
            ..
        } = &mut sa.functions[0].blocks[0].body[0].inst
        {
            *addend = 1;
        }
        let err =
            module_batch_eligible(&sa).expect_err("non-zero-addend body SymbolAddr stays deferred");
        assert!(err.contains("non-zero addend"), "reason: {err}");

        // Dangling FnDef (no matching function): cannot be remapped.
        let mut dangling = build_fnptr_caller_module();
        if let Inst::Const { value, .. } = &mut dangling.functions[0].blocks[0].body[0].inst {
            *value = Constant::FnDef(FuncId::new(9));
        }
        let err = module_batch_eligible(&dangling).expect_err("dangling FnDef must fail closed");
        assert!(err.contains("no matching function"), "reason: {err}");

        // SeqMap*: adapter-fail-closed, stays deferred.
        let mut seq = build_fnptr_caller_module();
        seq.functions[0].blocks[0].body.insert(
            0,
            tnode(
                Inst::SeqMapNot {
                    ty: Ty::Sequence(TyId::new(0)),
                    seq: v(0),
                },
                vec![9],
            ),
        );
        let err = module_batch_eligible(&seq).expect_err("SeqMap* stays deferred");
        assert!(err.contains("SeqMap"), "reason: {err}");
    }

    #[test]
    fn fn_identity_check_catches_wrong_but_in_range_remaps() {
        // The nastiest failure mode for fn pointers: a FuncId remapped to a
        // DIFFERENT but IN-RANGE function — every structural bound holds and
        // only the name-keyed lockstep can see it.
        let targets = build_fnptr_target_module();
        let caller = build_fnptr_caller_module();
        let modules = [targets.clone(), caller.clone()];
        let merged = merge_modules(&modules).unwrap();
        let winners: Vec<Option<(usize, &Function)>> = vec![
            Some((0, &targets.functions[0])), // fnptr_target
            Some((0, &targets.functions[1])), // fnptr_decoy
            Some((1, &caller.functions[0])),  // fnptr_caller
        ];

        // Sanity: the honest merge passes.
        verify_function_identity_preservation(&modules, &winners, &merged)
            .expect("an honest merge must pass the fn-identity lockstep");

        // Corrupt the FnDef constant to the DECOY (in range, wrong).
        let mut corrupted = merged.clone();
        for b in &mut corrupted.functions[2].blocks {
            for n in &mut b.body {
                if let Inst::Const {
                    value: value @ Constant::FnDef(_),
                    ..
                } = &mut n.inst
                {
                    *value = Constant::FnDef(FuncId::new(1));
                }
            }
        }
        // The structural self-check CANNOT see this (everything in range)…
        let exp = MergeExpectations {
            functions: 3,
            func_types: 2,
            ..Default::default()
        };
        structural_self_check(&corrupted, &exp)
            .expect("structural bounds all hold on the corrupted module");
        // …but the name-keyed lockstep MUST.
        let err = verify_function_identity_preservation(&modules, &winners, &corrupted)
            .expect_err("a wrong-but-in-range FnDef remap must be caught");
        assert!(
            err.contains("DIFFERENT FUNCTION"),
            "reason must name the class: {err}"
        );

        // Corrupt a DIRECT call the same way (build_caller/build_callee pair).
        let a = build_caller_module();
        let b = build_callee_module();
        let dmods = [a.clone(), b.clone()];
        let dmerged = merge_modules(&dmods).unwrap();
        let dwinners: Vec<Option<(usize, &Function)>> = vec![
            Some((0, &a.functions[0])), // call_add_fn
            Some((1, &b.functions[0])), // identity_fn (def upgrades decl)
        ];
        verify_function_identity_preservation(&dmods, &dwinners, &dmerged).unwrap();
        let mut dcorrupt = dmerged.clone();
        for bl in &mut dcorrupt.functions[0].blocks {
            for n in &mut bl.body {
                if let Inst::Call { callee, .. } = &mut n.inst {
                    *callee = FuncId::new(0); // self — in range, wrong
                }
            }
        }
        let err = verify_function_identity_preservation(&dmods, &dwinners, &dcorrupt)
            .expect_err("a wrong-but-in-range Call callee must be caught");
        assert!(err.contains("DIFFERENT FUNCTION"), "reason: {err}");

        // Corrupt the CallIndirect sig to a DIFFERENT-SHAPED in-range functy:
        // a silent ABI change only the name-resolved sig comparison can see.
        let mut sig_targets = build_fnptr_target_module();
        sig_targets.func_types.push(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        }); // FuncTyId 1 in the targets module — different arity
        let smods = [sig_targets.clone(), caller.clone()];
        let smerged = merge_modules(&smods).unwrap();
        let swinners: Vec<Option<(usize, &Function)>> = vec![
            Some((0, &sig_targets.functions[0])),
            Some((0, &sig_targets.functions[1])),
            Some((1, &caller.functions[0])),
        ];
        verify_function_identity_preservation(&smods, &swinners, &smerged).unwrap();
        let mut scorrupt = smerged.clone();
        for b in &mut scorrupt.functions[2].blocks {
            for n in &mut b.body {
                if let Inst::CallIndirect { sig, .. } = &mut n.inst {
                    *sig = FuncTyId::new(1); // the 2-arg shape — in range, wrong
                }
            }
        }
        let err = verify_function_identity_preservation(&smods, &swinners, &scorrupt)
            .expect_err("a wrong-but-in-range CallIndirect.sig must be caught");
        assert!(
            err.contains("signature"),
            "reason must flag the sig divergence: {err}"
        );
    }

    // ---- unit tests: debug file table -------------------------------------

    #[test]
    fn merge_merges_file_tables_and_remaps_spans() {
        let mut a = build_caller_module();
        a.files = vec!["a.rs".to_string()];
        a.functions[0].scopes = Some(vec![ScopeData {
            parent: None,
            span: Some(SourceSpan {
                file: 0,
                line: 1,
                col: 0,
            }),
        }]);
        a.functions[0].blocks[0].body[0].scope = Some(0);
        a.functions[0].blocks[0].body[0].span = Some(SourceSpan {
            file: 0,
            line: 1,
            col: 1,
        });
        let mut b = build_callee_module();
        b.files = vec!["b.rs".to_string(), "a.rs".to_string()];
        b.functions[0].scopes = Some(vec![ScopeData {
            parent: None,
            span: Some(SourceSpan {
                file: 0,
                line: 2,
                col: 0,
            }),
        }]);
        b.functions[0].blocks[0].body[0].scope = Some(0);
        b.functions[0].blocks[0].body[0].span = Some(SourceSpan {
            file: 0, // "b.rs"
            line: 2,
            col: 2,
        });

        let merged = merge_modules(&[a, b]).expect("file-table merge should succeed");
        assert_eq!(
            merged.files,
            vec!["a.rs".to_string(), "b.rs".to_string()],
            "paths interned by exact path (b's duplicate `a.rs` dedups)"
        );
        assert_eq!(
            merged.functions[0].blocks[0].body[0].span,
            Some(SourceSpan {
                file: 0,
                line: 1,
                col: 1
            }),
            "module A's span keeps its (base-0) file index"
        );
        assert_eq!(
            merged.functions[1].blocks[0].body[0].span,
            Some(SourceSpan {
                file: 1,
                line: 2,
                col: 2
            }),
            "module B's `b.rs` span must be remapped to the interned index"
        );
        assert_eq!(
            merged.functions[0].scopes,
            Some(vec![ScopeData {
                parent: None,
                span: Some(SourceSpan {
                    file: 0,
                    line: 1,
                    col: 0,
                }),
            }]),
            "module A's lexical scope span keeps its file index"
        );
        assert_eq!(
            merged.functions[1].scopes,
            Some(vec![ScopeData {
                parent: None,
                span: Some(SourceSpan {
                    file: 1,
                    line: 2,
                    col: 0,
                }),
            }]),
            "module B's lexical scope span must be remapped with instruction spans"
        );
        assert_eq!(merged.functions[0].blocks[0].body[0].scope, Some(0));
        assert_eq!(merged.functions[1].blocks[0].body[0].scope, Some(0));
    }

    #[test]
    fn merge_rejects_spans_without_file_table_in_mixed_merge() {
        let mut a = build_caller_module();
        a.files = vec!["a.rs".to_string()];
        let mut b = build_callee_module(); // b.files stays EMPTY...
        b.functions[0].blocks[0].body[0].span = Some(SourceSpan {
            file: 0,
            line: 2,
            col: 2,
        }); // ...but b carries a span: its file index would mis-resolve.
        let err = merge_modules(&[a, b])
            .expect_err("span-without-file-table in a mixed merge must fail closed");
        assert!(
            err.contains("no debug file table"),
            "reason should explain the mis-resolution hazard: {err}"
        );
    }

    #[test]
    fn merge_rejects_scope_spans_without_file_table_in_mixed_merge() {
        let mut a = build_caller_module();
        a.files = vec!["a.rs".to_string()];
        let mut b = build_callee_module(); // b.files stays EMPTY...
        b.functions[0].scopes = Some(vec![ScopeData {
            parent: None,
            span: Some(SourceSpan {
                file: 0,
                line: 2,
                col: 0,
            }),
        }]); // ...but b carries a scope span: its file index would mis-resolve.
        let err = merge_modules(&[a, b])
            .expect_err("scope-span-without-file-table in a mixed merge must fail closed");
        assert!(
            err.contains("no debug file table"),
            "reason should explain the scope-span mis-resolution hazard: {err}"
        );
    }

    // ---- unit tests: structural self-check ---------------------------------

    #[test]
    fn structural_self_check_catches_out_of_range_call() {
        let a = build_caller_module();
        let b = build_callee_module();
        let mut merged = merge_modules(&[a, b]).unwrap();
        // Corrupt: retarget the sibling call to a non-existent FuncId.
        for node in &mut merged.functions[0].blocks[0].body {
            if let Inst::Call { callee, .. } = &mut node.inst {
                *callee = FuncId::new(99);
            }
        }
        let err = structural_self_check(&merged, &scalar_expectations())
            .expect_err("a dangling call must be caught by the self-check");
        assert!(err.contains("out of range"), "reason: {err}");
    }

    #[test]
    fn structural_self_check_catches_non_dense_id() {
        let a = build_caller_module();
        let b = build_callee_module();
        let mut merged = merge_modules(&[a, b]).unwrap();
        merged.functions[1].id = FuncId::new(7); // break density
        let err = structural_self_check(&merged, &scalar_expectations())
            .expect_err("a non-dense FuncId must be caught");
        assert!(err.contains("non-dense"), "reason: {err}");
    }

    #[test]
    fn structural_self_check_catches_dropped_function() {
        let a = build_caller_module();
        let b = build_callee_module();
        let merged = merge_modules(&[a, b]).unwrap();
        // Expecting 3 functions but only 2 present -> dropped/duplicated.
        let mut exp = scalar_expectations();
        exp.functions = 3;
        let err = structural_self_check(&merged, &exp)
            .expect_err("a wrong function count must be caught");
        assert!(err.contains("dropped or duplicated"), "reason: {err}");
    }

    #[test]
    fn structural_self_check_catches_malformed_scope_tree_and_dangling_scope_use() {
        let mut merged = merge_modules(&[build_caller_module(), build_callee_module()]).unwrap();
        merged.functions[0].scopes = Some(vec![ScopeData {
            parent: Some(0),
            span: None,
        }]);
        let err = structural_self_check(&merged, &scalar_expectations())
            .expect_err("scope zero with a parent must fail closed");
        assert!(err.contains("scope 0 must be the root"), "reason: {err}");

        merged.functions[0].scopes = Some(vec![
            ScopeData {
                parent: None,
                span: None,
            },
            ScopeData {
                parent: None,
                span: None,
            },
        ]);
        let err = structural_self_check(&merged, &scalar_expectations())
            .expect_err("a second lexical root must fail closed");
        assert!(err.contains("second root"), "reason: {err}");

        merged.functions[0].scopes = Some(vec![ScopeData {
            parent: None,
            span: None,
        }]);
        merged.functions[0].blocks[0].body[0].scope = Some(1);
        let err = structural_self_check(&merged, &scalar_expectations())
            .expect_err("a dangling instruction scope must fail closed");
        assert!(err.contains("scope index 1 out of range"), "reason: {err}");
    }

    #[test]
    fn structural_self_check_catches_corrupted_type_remap() {
        let agg_exp = MergeExpectations {
            functions: 2,
            func_types: 2,
            structs: 2,
            ..Default::default()
        };

        // (i) a body reference remapped to a non-existent struct id.
        let mut merged = merge_modules(&[
            one_struct_module("mod_sa", "APoint", "use_a"),
            one_struct_module("mod_sb", "BPair", "use_b"),
        ])
        .unwrap();
        for node in &mut merged.functions[1].blocks[0].body {
            if let Inst::Undef { ty } = &mut node.inst {
                *ty = Ty::Struct(StructId::new(99));
            }
        }
        let err = structural_self_check(&merged, &agg_exp)
            .expect_err("a dangling struct reference must be caught");
        assert!(err.contains("out of range"), "reason: {err}");

        // (ii) a corrupted (non-dense) embedded struct id.
        let mut merged = merge_modules(&[
            one_struct_module("mod_sa", "APoint", "use_a"),
            one_struct_module("mod_sb", "BPair", "use_b"),
        ])
        .unwrap();
        merged.structs[1].id = StructId::new(7);
        let err = structural_self_check(&merged, &agg_exp)
            .expect_err("a non-dense struct id must be caught");
        assert!(err.contains("non-dense"), "reason: {err}");
    }

    // ---- unit tests: the remap primitives in isolation ------------------
    // These exercise the FuncId/FuncTyId-in-constant and indirect-call remap
    // machinery directly (the forms `precheck_module` currently defers), so the
    // full remap surface stays covered and forward-compatible.

    fn test_maps(func_ty_base: u32, func_ty_len: usize) -> ModMaps {
        ModMaps {
            func_ty_base,
            func_ty_len,
            closure_base: 0,
            closure_len: 0,
            struct_map: HashMap::new(),
            enum_map: HashMap::new(),
            record_map: HashMap::new(),
            global_map: HashMap::new(),
            ty_map: HashMap::new(),
            file_map: HashMap::new(),
            files_len: 0,
        }
    }

    #[test]
    fn remap_inst_rewrites_fndef_constant_funcid() {
        let mut fid_map = HashMap::new();
        fid_map.insert(3u32, 7u32);
        let mut inst = Inst::Const {
            ty: Ty::Func(FuncTyId::new(0)),
            value: Constant::FnDef(FuncId::new(3)),
        };
        remap_inst(&mut inst, &test_maps(5, 1), &fid_map, &mut 0).unwrap();
        match inst {
            Inst::Const {
                ty: Ty::Func(ftid),
                value: Constant::FnDef(fid),
            } => {
                assert_eq!(fid, FuncId::new(7), "FnDef FuncId remapped via fid_map");
                assert_eq!(ftid, FuncTyId::new(5), "Const Ty::Func shifted by base");
            }
            other => panic!("unexpected inst after remap: {other:?}"),
        }
    }

    #[test]
    fn remap_inst_rewrites_callindirect_sig() {
        let fid_map = HashMap::new();
        let mut inst = Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: FuncTyId::new(1),
            args: vec![],
            calling_conv: CallingConv::C,
        };
        remap_inst(&mut inst, &test_maps(5, 2), &fid_map, &mut 0).unwrap();
        match inst {
            Inst::CallIndirect { sig, .. } => {
                assert_eq!(sig, FuncTyId::new(6), "CallIndirect.sig shifted by base");
            }
            other => panic!("unexpected inst: {other:?}"),
        }
    }

    #[test]
    fn remap_inst_rewrites_switch_case_constants() {
        let mut fid_map = HashMap::new();
        fid_map.insert(0u32, 4u32);
        let mut inst = Inst::Switch {
            value: v(0),
            default: BlockId::new(0),
            default_args: vec![],
            cases: vec![SwitchCase {
                value: Constant::FnDef(FuncId::new(0)),
                target: BlockId::new(1),
                args: vec![],
            }],
            exhaustive_enum_unreachable: false,
        };
        remap_inst(&mut inst, &test_maps(0, 0), &fid_map, &mut 0).unwrap();
        match inst {
            Inst::Switch { cases, .. } => {
                assert_eq!(
                    cases[0].value,
                    Constant::FnDef(FuncId::new(4)),
                    "switch case constants must be remapped like Const payloads"
                );
            }
            other => panic!("unexpected inst: {other:?}"),
        }
    }

    #[test]
    fn remap_ty_fails_closed_on_dangling_struct_id() {
        // A struct reference with NO matching definition in its source module
        // (empty struct map) must fail closed, never pass through un-remapped.
        let err = remap_ty_final(&Ty::Struct(StructId::new(0)), &test_maps(0, 0))
            .expect_err("a dangling struct-table reference must fail closed");
        assert!(err.contains("no matching definition"), "reason: {err}");
    }

    #[test]
    fn remap_ty_fails_closed_on_out_of_range_functy_shift() {
        // A FuncTyId beyond the SOURCE module's table must be rejected before
        // shifting (a blind shift would silently alias another module's entry).
        let err = remap_ty_final(&Ty::Func(FuncTyId::new(9)), &test_maps(0, 1))
            .expect_err("an out-of-source-range functy id must fail closed");
        assert!(err.contains("out of range"), "reason: {err}");
    }

    // ---- Step-0 de-risk: merged module compiles to ONE object ----------

    /// Parse an object's symbol table into `(name, is_defined)` pairs for the
    /// two natively-supported formats. Returns `None` for unrecognized formats
    /// so the caller can fall back to format-independent assertions.
    fn object_symbols(obj: &[u8]) -> Option<Vec<(String, bool)>> {
        if obj.len() >= 4 && obj[0..4] == [0xCF, 0xFA, 0xED, 0xFE] {
            return macho_symbols(obj);
        }
        if obj.len() >= 4 && obj[0..4] == [0x7F, b'E', b'L', b'F'] {
            return elf_symbols(obj);
        }
        None
    }

    fn read_cstr(bytes: &[u8], off: usize) -> Option<String> {
        let end = bytes.get(off..)?.iter().position(|&c| c == 0)? + off;
        Some(String::from_utf8_lossy(&bytes[off..end]).into_owned())
    }

    fn le_u32(b: &[u8], o: usize) -> Option<u32> {
        Some(u32::from_le_bytes(b.get(o..o + 4)?.try_into().ok()?))
    }
    fn le_u64(b: &[u8], o: usize) -> Option<u64> {
        Some(u64::from_le_bytes(b.get(o..o + 8)?.try_into().ok()?))
    }
    fn le_u16(b: &[u8], o: usize) -> Option<u16> {
        Some(u16::from_le_bytes(b.get(o..o + 2)?.try_into().ok()?))
    }

    fn macho_symbols(obj: &[u8]) -> Option<Vec<(String, bool)>> {
        // mach_header_64 is 32 bytes; ncmds at offset 16.
        let ncmds = le_u32(obj, 16)? as usize;
        let mut off = 32usize;
        for _ in 0..ncmds {
            let cmd = le_u32(obj, off)?;
            let cmdsize = le_u32(obj, off + 4)? as usize;
            if cmd == 0x2 {
                // LC_SYMTAB: symoff, nsyms, stroff, strsize
                let symoff = le_u32(obj, off + 8)? as usize;
                let nsyms = le_u32(obj, off + 12)? as usize;
                let stroff = le_u32(obj, off + 16)? as usize;
                let mut out = Vec::with_capacity(nsyms);
                for i in 0..nsyms {
                    let e = symoff + i * 16; // nlist_64 is 16 bytes
                    let n_strx = le_u32(obj, e)? as usize;
                    let n_type = *obj.get(e + 4)?;
                    // N_TYPE mask = 0x0e; N_SECT = 0x0e (defined in a section).
                    let defined = (n_type & 0x0e) == 0x0e;
                    let name = read_cstr(obj, stroff + n_strx)?;
                    out.push((name, defined));
                }
                return Some(out);
            }
            if cmdsize == 0 {
                break;
            }
            off += cmdsize;
        }
        Some(Vec::new())
    }

    fn elf_symbols(obj: &[u8]) -> Option<Vec<(String, bool)>> {
        let e_shoff = le_u64(obj, 40)? as usize;
        let e_shentsize = le_u16(obj, 58)? as usize;
        let e_shnum = le_u16(obj, 60)? as usize;
        // Find SHT_SYMTAB (2) and follow sh_link to its string table.
        for i in 0..e_shnum {
            let sh = e_shoff + i * e_shentsize;
            let sh_type = le_u32(obj, sh + 4)?;
            if sh_type == 2 {
                let sh_offset = le_u64(obj, sh + 24)? as usize;
                let sh_size = le_u64(obj, sh + 32)? as usize;
                let sh_link = le_u32(obj, sh + 40)? as usize;
                let sh_entsize = le_u64(obj, sh + 56)? as usize;
                let str_sh = e_shoff + sh_link * e_shentsize;
                let str_off = le_u64(obj, str_sh + 24)? as usize;
                let entsize = if sh_entsize == 0 { 24 } else { sh_entsize };
                let count = sh_size / entsize;
                let mut out = Vec::with_capacity(count);
                for k in 0..count {
                    let e = sh_offset + k * entsize;
                    let st_name = le_u32(obj, e)? as usize;
                    let st_shndx = le_u16(obj, e + 6)?; // SHN_UNDEF == 0
                    let name = read_cstr(obj, str_off + st_name)?;
                    out.push((name, st_shndx != 0));
                }
                return Some(out);
            }
        }
        Some(Vec::new())
    }

    fn sym_matches(name: &str, target: &str) -> bool {
        name == target || name == format!("_{target}")
    }

    /// STEP 0 (de-risk): merge two global-free functions (A calls sibling B),
    /// compile the MERGED module ONCE for x86-64, and prove the batching glue is
    /// sound end-to-end: one object with both symbols, B resolved INTRA-OBJECT
    /// (defined, not an undefined external), every proof cert verified, and the
    /// compile byte-for-byte deterministic.
    #[cfg(not(target_os = "windows"))]
    #[test]
    fn step0_merged_two_function_module_compiles_to_one_object() {
        use crate::compiler::{Compiler, CompilerConfig};
        use crate::target::Target;

        let merged = merge_modules(&[build_caller_module(), build_callee_module()])
            .expect("merge should succeed");

        let compile = || {
            Compiler::new(CompilerConfig {
                target: Target::X86_64,
                emit_proofs: true,
                ..CompilerConfig::default()
            })
            .compile(&merged)
            .expect("merged multi-function module should compile for x86-64")
        };

        let r1 = compile();
        let r2 = compile();

        // (a) ONE object with BOTH functions.
        assert_eq!(
            r1.metrics.function_count, 2,
            "merged object must contain both functions"
        );

        // (c) every proof certificate verified (emit_proofs fails closed on any
        // unverified entry, so a successful compile already implies this — assert
        // it explicitly as the gate).
        let proofs = r1.proofs.as_ref().expect("emit_proofs must yield a bundle");
        assert!(!proofs.is_empty(), "proof bundle must be non-empty");
        assert!(
            proofs.iter().all(|c| c.verified),
            "every proof certificate for the merged module must be verified"
        );

        // (d) deterministic: identical object + identical proof bundle.
        assert_eq!(
            r1.object_code, r2.object_code,
            "merged compile must be byte-identical across runs (determinism gate)"
        );
        assert_eq!(r1.proofs, r2.proofs, "proof bundle must be deterministic");

        // (b) B resolves INTRA-OBJECT LOCAL, not as an undefined external.
        if let Some(syms) = object_symbols(&r1.object_code) {
            let identity: Vec<&(String, bool)> = syms
                .iter()
                .filter(|(n, _)| sym_matches(n, "identity_fn"))
                .collect();
            assert!(
                !identity.is_empty(),
                "identity_fn must appear in the merged object's symbol table"
            );
            assert!(
                identity.iter().all(|(_, defined)| *defined),
                "identity_fn must be a DEFINED (intra-object) symbol in the merged object, \
                 never an undefined external: {identity:?}"
            );
            assert!(
                syms.iter()
                    .any(|(n, d)| sym_matches(n, "call_add_fn") && *d),
                "call_add_fn must also be a defined symbol"
            );

            // Contrast: compile module A ALONE — identity_fn is only an extern
            // declaration there, so it MUST be an undefined external. This proves
            // the merge is what turned an extern into an intra-object definition.
            if let Ok(a_only) = Compiler::new(CompilerConfig {
                target: Target::X86_64,
                emit_proofs: false,
                ..CompilerConfig::default()
            })
            .compile(&build_caller_module())
                && let Some(a_syms) = object_symbols(&a_only.object_code)
            {
                let a_identity: Vec<&(String, bool)> = a_syms
                    .iter()
                    .filter(|(n, _)| sym_matches(n, "identity_fn"))
                    .collect();
                assert!(
                    !a_identity.is_empty() && a_identity.iter().all(|(_, defined)| !*defined),
                    "in SEPARATE compilation identity_fn must be an UNDEFINED external \
                         (the contrast the merge eliminates): {a_identity:?}"
                );
            }
        }
    }

    // ---- Step-0 (aggregate): struct arg/return + enum match --------------

    /// Module A: `agg_caller(x) = pair_sum(make_pair(x+1, x*3))`, with BOTH
    /// callees as extern DECLARATIONS whose signatures carry the struct by
    /// value (arg AND return) — the real bridge per-function shape for
    /// aggregate-using siblings. `PairT` is this module's StructId(0).
    fn build_agg_caller_module() -> Module {
        let pair = Ty::Struct(StructId::new(0));
        let mut m = Module::new("agg_caller_mod");
        m.structs = vec![tsdef(0, "PairT", vec![Ty::I64, Ty::I64])];
        m.func_types = vec![
            FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            }, // 0: agg_caller
            FuncTy {
                params: vec![pair.clone()],
                returns: vec![Ty::I64],
                is_vararg: false,
            }, // 1: pair_sum (struct ARG)
            FuncTy {
                params: vec![Ty::I64, Ty::I64],
                returns: vec![pair.clone()],
                is_vararg: false,
            }, // 2: make_pair (struct RETURN)
        ];
        let body = vec![
            tnode(
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                },
                vec![1],
            ),
            tnode(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                },
                vec![2],
            ), // a = x + 1
            tnode(
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(3),
                },
                vec![3],
            ),
            tnode(
                Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(3),
                },
                vec![4],
            ), // b = x * 3
            tnode(
                Inst::Call {
                    callee: FuncId::new(2),
                    args: vec![v(2), v(4)],
                },
                vec![5],
            ), // p = make_pair(a, b)   [struct RETURN across the decl boundary]
            tnode(
                Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![v(5)],
                },
                vec![6],
            ), // s = pair_sum(p)       [struct ARG across the decl boundary]
            tnode(Inst::Return { values: vec![v(6)] }, vec![]),
        ];
        m.functions = vec![
            tfunc(
                0,
                "agg_caller",
                0,
                vec![tblock(0, vec![(0, Ty::I64)], body)],
            ),
            tfunc(1, "pair_sum", 1, vec![]),  // extern decl
            tfunc(2, "make_pair", 2, vec![]), // extern decl
        ];
        m
    }

    /// Module B: DEFINES `pair_sum` (struct arg, enum match inside) and
    /// `make_pair` (struct return). `PairT` is REDEFINED here (same name, same
    /// structure — the dedup path) as this module's own StructId(0), and the
    /// module-local enum `Choice` (EnumId 0) is matched through the bridge's
    /// real enum shape: alloca'd tagged storage, a tag-byte store per arm, a
    /// tag load, and a Switch dispatch.
    ///
    /// `extract_field_ty` is the DECLARED type on pair_sum's two `ExtractField`
    /// instructions. The trust-cg lowering adapter resolves the field type FROM
    /// a declared AGGREGATE type (pass `PairT` — the shape the e2e ABI corpus
    /// uses), while the trust-ir validator/reference interpreter declare the
    /// FIELD type itself (pass `Ty::I64`). The merge must remap both shapes
    /// correctly, so the compile proof uses the former and the semantic proof
    /// the latter.
    fn build_agg_callee_module(extract_field_ty: Ty) -> Module {
        let pair = Ty::Struct(StructId::new(0));
        let choice = Ty::Enum(EnumId::new(0));
        let mut m = Module::new("agg_callee_mod");
        m.structs = vec![tsdef(0, "PairT", vec![Ty::I64, Ty::I64])];
        m.enums = vec![tedef(0, "Choice", vec![("Lo", vec![]), ("Hi", vec![])])];
        m.func_types = vec![
            FuncTy {
                params: vec![pair.clone()],
                returns: vec![Ty::I64],
                is_vararg: false,
            }, // 0: pair_sum
            FuncTy {
                params: vec![Ty::I64, Ty::I64],
                returns: vec![pair.clone()],
                is_vararg: false,
            }, // 1: make_pair
        ];
        // pair_sum(p): match (p.f0 > p.f1 ? Choice::Hi : Choice::Lo) {
        //   Lo => p.f0 + p.f1, Hi => p.f0 - p.f1 }
        let bb0 = tblock(
            0,
            vec![(0, pair.clone())],
            vec![
                tnode(
                    Inst::ExtractField {
                        ty: extract_field_ty.clone(),
                        aggregate: v(0),
                        field: 0,
                    },
                    vec![1],
                ),
                tnode(
                    Inst::ExtractField {
                        ty: extract_field_ty.clone(),
                        aggregate: v(0),
                        field: 1,
                    },
                    vec![2],
                ),
                tnode(
                    Inst::ICmp {
                        op: ICmpOp::Sgt,
                        ty: Ty::I64,
                        lhs: v(1),
                        rhs: v(2),
                    },
                    vec![3],
                ),
                tnode(
                    Inst::Alloca {
                        ty: choice.clone(),
                        count: None,
                        align: None,
                    },
                    vec![4],
                ),
                tnode(
                    Inst::CondBr {
                        cond: v(3),
                        then_target: BlockId::new(2),
                        then_args: vec![],
                        else_target: BlockId::new(1),
                        else_args: vec![],
                    },
                    vec![],
                ),
            ],
        );
        let bb1 = tblock(
            1,
            vec![],
            vec![
                tnode(
                    Inst::Const {
                        ty: Ty::U8,
                        value: Constant::Int(0),
                    },
                    vec![5],
                ),
                tnode(
                    Inst::Store {
                        ty: Ty::U8,
                        ptr: v(4),
                        value: v(5),
                        volatile: false,
                        align: None,
                    },
                    vec![],
                ),
                tnode(
                    Inst::Br {
                        target: BlockId::new(3),
                        args: vec![],
                    },
                    vec![],
                ),
            ],
        );
        let bb2 = tblock(
            2,
            vec![],
            vec![
                tnode(
                    Inst::Const {
                        ty: Ty::U8,
                        value: Constant::Int(1),
                    },
                    vec![6],
                ),
                tnode(
                    Inst::Store {
                        ty: Ty::U8,
                        ptr: v(4),
                        value: v(6),
                        volatile: false,
                        align: None,
                    },
                    vec![],
                ),
                tnode(
                    Inst::Br {
                        target: BlockId::new(3),
                        args: vec![],
                    },
                    vec![],
                ),
            ],
        );
        let bb3 = tblock(
            3,
            vec![],
            vec![
                tnode(
                    Inst::Load {
                        ty: Ty::U8,
                        ptr: v(4),
                        volatile: false,
                        align: None,
                    },
                    vec![7],
                ),
                tnode(
                    Inst::Switch {
                        value: v(7),
                        default: BlockId::new(4),
                        default_args: vec![],
                        cases: vec![
                            SwitchCase {
                                value: Constant::Int(0),
                                target: BlockId::new(4),
                                args: vec![],
                            },
                            SwitchCase {
                                value: Constant::Int(1),
                                target: BlockId::new(5),
                                args: vec![],
                            },
                        ],
                        exhaustive_enum_unreachable: false,
                    },
                    vec![],
                ),
            ],
        );
        let bb4 = tblock(
            4,
            vec![],
            vec![
                tnode(
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: v(1),
                        rhs: v(2),
                    },
                    vec![8],
                ),
                tnode(Inst::Return { values: vec![v(8)] }, vec![]),
            ],
        );
        let bb5 = tblock(
            5,
            vec![],
            vec![
                tnode(
                    Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::I64,
                        lhs: v(1),
                        rhs: v(2),
                    },
                    vec![9],
                ),
                tnode(Inst::Return { values: vec![v(9)] }, vec![]),
            ],
        );
        // make_pair(a, b) -> PairT { a, b }
        let mp = tblock(
            0,
            vec![(0, Ty::I64), (1, Ty::I64)],
            vec![
                tnode(
                    Inst::Const {
                        ty: pair.clone(),
                        value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
                    },
                    vec![2],
                ),
                tnode(
                    Inst::InsertField {
                        ty: pair.clone(),
                        aggregate: v(2),
                        field: 0,
                        value: v(0),
                    },
                    vec![3],
                ),
                tnode(
                    Inst::InsertField {
                        ty: pair.clone(),
                        aggregate: v(3),
                        field: 1,
                        value: v(1),
                    },
                    vec![4],
                ),
                tnode(Inst::Return { values: vec![v(4)] }, vec![]),
            ],
        );
        m.functions = vec![
            tfunc(0, "pair_sum", 0, vec![bb0, bb1, bb2, bb3, bb4, bb5]),
            tfunc(1, "make_pair", 1, vec![mp]),
        ];
        m
    }

    /// The merged aggregate module must compute CORRECTLY under the trust-ir
    /// reference interpreter (memory model + canonical enum layout): a wrong
    /// struct/enum remap here is a wrong field offset or wrong tag — a wrong
    /// value, not just a validation error.
    #[test]
    fn merged_aggregate_module_computes_correctly_under_reference_interpreter() {
        // Reference-interpreter convention: ExtractField declares the FIELD type.
        let merged = merge_modules(&[build_agg_caller_module(), build_agg_callee_module(Ty::I64)])
            .expect("aggregate merge should succeed");
        assert_eq!(merged.structs.len(), 1, "PairT deduped to one definition");
        assert_eq!(merged.enums.len(), 1, "Choice present");
        assert_eq!(merged.functions.len(), 3, "caller + two upgraded defs");

        let interp = Interpreter::with_module(&merged);
        let run = |x: i128| -> i128 {
            let outcome = interp
                .execute_func(
                    FuncId::new(0),
                    [InterpretValue::int(Ty::I64, x).expect("i64 arg")],
                )
                .unwrap_or_else(|e| panic!("interpretation failed for x={x}: {e:?}"));
            outcome.returns[0].as_int().expect("i64 return").as_signed()
        };
        // x=5: a=6, b=15; 6 > 15 is false -> Lo arm -> 6 + 15 = 21.
        assert_eq!(run(5), 21, "Lo arm through the merged module");
        // x=-1: a=0, b=-3; 0 > -3 is true -> Hi arm -> 0 - (-3) = 3.
        assert_eq!(run(-1), 3, "Hi arm through the merged module");
    }

    /// STEP 0 (aggregate de-risk): merge two GLOBAL-FREE aggregate-using
    /// functions — A calls sibling `pair_sum` (struct BY-VALUE arg) and sibling
    /// `make_pair` (struct BY-VALUE return); `pair_sum` matches a module-local
    /// enum — compile the MERGED module ONCE for x86-64 and prove the extended
    /// batching glue end-to-end: one object, both callees INTRA-OBJECT-LOCAL
    /// definitions, and byte-identical determinism. The proof-required variant
    /// must promote its linker-visible call relocations only through the
    /// production composition: a solver-backed value proof for each relocation
    /// kind plus the ENC-9 reparse binding for the exact emitted object.
    #[cfg(not(target_os = "windows"))]
    #[test]
    fn step0_merged_aggregate_module_compiles_to_one_object() {
        use crate::compiler::{Compiler, CompilerConfig};
        use crate::target::{Target, TargetSpec};

        // Backend-adapter convention: ExtractField declares the AGGREGATE type
        // (the shape the e2e x86-64 aggregate-ABI corpus uses).
        let merged = merge_modules(&[
            build_agg_caller_module(),
            build_agg_callee_module(Ty::Struct(StructId::new(0))),
        ])
        .expect("aggregate merge should succeed");
        let target_spec =
            TargetSpec::parse("x86_64-apple-darwin").expect("x86-64 Mach-O target spec");

        let compile = || {
            Compiler::new_for_target_spec(
                CompilerConfig {
                    target: Target::X86_64,
                    emit_proofs: false,
                    ..CompilerConfig::default()
                },
                target_spec,
            )
            .compile(&merged)
            .expect("merged aggregate module should compile for x86-64")
        };

        let r1 = compile();
        let r2 = compile();

        // (a) ONE object with ALL THREE functions.
        assert_eq!(
            r1.metrics.function_count, 3,
            "merged object must contain the caller and both aggregate callees"
        );

        // (b) Proof-required production certification accepts the non-empty
        // relocation inventory only because the standing solver-backed BRANCH
        // proof is composed with the exact-object ENC-9 reparse binding. The
        // missing-binding and unproved-kind complements remain fail-closed in
        // object_inventory's unit tests.
        let proof_result = Compiler::new_for_target_spec(
            CompilerConfig {
                target: Target::X86_64,
                emit_proofs: true,
                ..CompilerConfig::default()
            },
            target_spec,
        )
        .compile(&merged)
        .expect("proved and reparse-bound call relocations must promote");
        let relocation_inventory = proof_result
            .proofs
            .as_ref()
            .and_then(|proofs| {
                proofs
                    .iter()
                    .find(|proof| proof.category == "relocation_inventory")
            })
            .expect("proof-required compile must carry relocation inventory authority");
        assert!(relocation_inventory.verified, "{relocation_inventory:?}");
        assert!(
            relocation_inventory
                .strength
                .contains("X86_64_RELOC_BRANCH")
                && relocation_inventory
                    .strength
                    .contains("solver-backed value proof")
                && relocation_inventory
                    .strength
                    .contains("ENC-9 reparse-enforced object"),
            "relocation authority must name both proof layers: {relocation_inventory:?}"
        );
        assert_eq!(
            proof_result.object_code, r1.object_code,
            "proof emission must not change the merged object bytes"
        );

        // (c) deterministic: identical object + identical proof bundle.
        assert_eq!(
            r1.object_code, r2.object_code,
            "merged aggregate compile must be byte-identical across runs"
        );
        assert!(r1.proofs.is_none() && r2.proofs.is_none());

        // (d) both callees resolve INTRA-OBJECT LOCAL (defined), never as
        // undefined externals.
        if let Some(syms) = object_symbols(&r1.object_code) {
            for callee in ["pair_sum", "make_pair"] {
                let hits: Vec<&(String, bool)> = syms
                    .iter()
                    .filter(|(n, _)| sym_matches(n, callee))
                    .collect();
                assert!(
                    !hits.is_empty(),
                    "{callee} must appear in the merged object's symbol table"
                );
                assert!(
                    hits.iter().all(|(_, defined)| *defined),
                    "{callee} must be a DEFINED (intra-object) symbol: {hits:?}"
                );
            }
            assert!(
                syms.iter().any(|(n, d)| sym_matches(n, "agg_caller") && *d),
                "agg_caller must also be a defined symbol"
            );

            // Contrast: compiled ALONE, module A's aggregate callees are
            // undefined externals — the merge is what internalized them.
            if let Ok(a_only) = Compiler::new(CompilerConfig {
                target: Target::X86_64,
                emit_proofs: false,
                ..CompilerConfig::default()
            })
            .compile(&build_agg_caller_module())
                && let Some(a_syms) = object_symbols(&a_only.object_code)
            {
                for callee in ["pair_sum", "make_pair"] {
                    let hits: Vec<&(String, bool)> = a_syms
                        .iter()
                        .filter(|(n, _)| sym_matches(n, callee))
                        .collect();
                    assert!(
                        !hits.is_empty() && hits.iter().all(|(_, defined)| !*defined),
                        "in SEPARATE compilation {callee} must be an UNDEFINED external: \
                             {hits:?}"
                    );
                }
            }
        }
    }
}
