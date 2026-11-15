// trust-cg-lower/handle_transport.rs - the v43 opaque-runtime-handle admission
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The consumer half of the trust-ir v43 NOMINAL OPAQUE RUNTIME HANDLE
//! (`Ty::Handle(HandleTy { name, runtime })`), decided once for every lane.
//!
//! # What a handle is, and what it is not
//!
//! A handle is ONE POINTER WORD of representation (`ty_layout` gives it a
//! pointer-width scalar, `TyShape::Handle`) that is deliberately **not
//! pointer-like**: `Ty::is_pointer_like` and `Ty::is_reference` are both
//! FALSE for it, it is never equal to `Ty::Ptr`, and no cast bridges the two
//! (trust-ir's `shape` refuses `Bitcast Ptr -> Handle` with
//! `LayoutError::OpaqueHandleCast`). Identity is the exact `(name, runtime)`
//! pair — `Handle(A) != Handle(B)`, so two runtimes can never exchange words.
//!
//! The reason the format spells a third thing, rather than reusing `Ptr` or a
//! `Ty::Dialect` row, is the reason this module exists: a `Ptr` can be FORGED
//! (`IntToPtr`, `Bitcast`, a `Load`, a constant, a field read), so a runtime
//! handle spelled `Ptr` has no origin guarantee at all; a `Dialect` type has
//! no machine representation, so a backend cannot pass one to a C entry point.
//! A handle is representation-bearing AND origin-pinned.
//!
//! # What this backend admits
//!
//! trust-ir-build permits exact-typed TRANSPORT only (its rule 7: copy,
//! select, an exact-typed call/return/branch edge), and admits as the only
//! ORIGINS the bodyless `External` C declarations pinned in
//! [`trust_ir_build::validate::TRUSTED_HANDLE_RUNTIMES`]. This backend admits
//! a STRICT SUBSET of that: the transport that reaches a PINNED RUNTIME ENTRY
//! POINT, as a whole pointer-width word in a value slot.
//!
//! | construct | verdict here |
//! |---|---|
//! | bare `Ty::Handle` param / result / return / block param | ADMITTED — lowers to the pointer-word opaque scalar ([`crate::adapter::translate_type`]) |
//! | `Copy` / `Select` at exactly that handle type | ADMITTED — register transport |
//! | `Call` / `Invoke` of a PINNED entry-point declaration, or of a function DEFINED in this module | ADMITTED |
//! | `CallIndirect` whose signature reaches a handle | REFUSED — an indirect callee has no statically pinned origin |
//! | a handle in a struct / enum / record / closure / array / tuple / vector / refinement / pointee / global | REFUSED — that is a LAYOUT, hence an address, hence a store and a re-read as an ordinary pointer |
//! | `Load` / `Store` / `Alloca` / `GEP` / `Cast` / `ICmp` / `BinOp` / atomics / `Const` / `Undef` / `DialectOp` at a handle type | REFUSED — dereference, index, field access, cast, structural comparison, forgery |
//! | a bodyless declaration reaching a handle that is not a pinned entry point | REFUSED — an unpinned origin |
//! | a function or global taking a PINNED SYMBOL's name without being that exact declaration | REFUSED — the `trust_bignum_nat_add(Ptr, Ptr) -> Ptr` forgery |
//!
//! # Why the pin is re-derived here
//!
//! The pin never travels on the wire: the format accepts any lexically valid
//! `(name, runtime)` pair, and which pairs name a TRUSTED runtime is a
//! validator decision. So this module reads
//! [`trust_ir_build::validate::HandleRegistry::pinned`] itself rather than
//! believing anything the module says about itself. An unpinned word has no
//! trusted producer; handing one to a C entry point would be a forgery
//! performed by the backend.
//!
//! On top of its own checks, a handle-bearing module must also satisfy
//! trust-ir-build's OWN handle rules ([`handle_validation_refusal`]). That
//! validator owns the invariant this backend depends on and cannot re-derive
//! from inline types alone: it carries the complete SSA value-type map, so it
//! is what catches an operand-level lie (a `Store { ty: Ptr }` whose stored
//! VALUE is handle-typed). Only the handle-class errors are consulted, so a
//! handle-free module's lowering is unchanged and an unrelated validity
//! quirk in a handle-bearing module is still not this gate's verdict.
//!
//! `Constant::SymbolAddr` — the third spelling of a link-time symbol, after a
//! function name and a global name — is deliberately left to that validator
//! alone: its walk already covers every constant tree in the module (global
//! initializers and body `Const`s, nested aggregates included), and a
//! module-wide constant walk on every handle-FREE module would be a cost the
//! rest of this gate does not pay.

use std::collections::BTreeSet;

use trust_ir::{
    FuncTy, FuncTyId, Function as TrustIrFunction, HandleTy, Inst, Linkage,
    Module as TrustIrModule, NominalTypeReachability, Ty,
};
use trust_ir_build::validate::{
    HandleRegistry, HandleRuntimePin, ValidationError, validate_module,
};

use crate::adapter::AdapterError;

/// Does any type occurrence in `module` spell a v43 handle?
///
/// One [`TrustIrModule::visit_types`] census — the cheap gate every lane runs
/// so a handle-free module pays nothing beyond the walk it already pays for
/// the rest of the shared floor.
#[must_use]
pub fn module_spells_a_handle(module: &TrustIrModule) -> bool {
    let mut found = false;
    module.visit_types(|ty| found |= ty.is_handle());
    found
}

/// THE v43 admission. `Ok(())` means every handle occurrence in `module` is
/// transport this backend can emit, to a runtime whose pin it re-derived.
///
/// Runs on every native entry and the wasm shared floor through
/// [`crate::adapter::reject_unconsumed_v41_target_neutral_surface`]. The
/// pinned-SYMBOL namespace clauses run even on a handle-free module; every
/// other clause is skipped when the census finds no handle.
pub fn admit_handle_surface(module: &TrustIrModule) -> Result<(), AdapterError> {
    let registry = HandleRegistry::pinned();
    // The symbol namespace is checked whether or not a handle is spelled: the
    // forgery it closes is precisely a module that names the real runtime's
    // entry points with ordinary `Ptr` signatures and no handle in sight.
    reject_pinned_symbol_impostors(module, registry)?;
    if !module_spells_a_handle(module) {
        return Ok(());
    }
    reject_unpinned_identities(module, registry)?;
    // THIS BACKEND'S OWN VERDICT FIRST, so a refusal names what trust-cg
    // cannot emit rather than deferring to the producer's rule name — and so
    // this gate stays fail-closed on its own even if trust-ir-build's rules
    // were ever relaxed.
    let nominal = module.nominal_type_reachability();
    reject_handle_bearing_definitions(module, &nominal)?;
    for function in &module.functions {
        admit_function(module, function, &nominal, registry)?;
    }
    // The producer-side invariant LAST: it is the belt-and-suspenders clause
    // for what an inline-type walk structurally cannot see, because it holds
    // the complete SSA value-type map. A `Store { ty: Ptr }` whose stored
    // VALUE is handle-typed passes every check above and is caught here.
    if let Some(detail) = handle_validation_refusal(module) {
        return Err(AdapterError::OpaqueHandleModuleInvalid {
            module: module.name.clone(),
            detail,
        });
    }
    Ok(())
}

/// The wasm lane's verdict: this backend has no channel through which a wasm
/// module could reach a pinned NATIVE C runtime, so a handle occurrence is
/// refused outright rather than lowered to an `i64` a wasm import could
/// forge. Kept separate from [`admit_handle_surface`] so the native lane's
/// admitted transport is not silently widened to a lane that cannot honor it.
pub fn refuse_handle_surface(module: &TrustIrModule, lane: &str) -> Result<(), AdapterError> {
    let mut refusal = None;
    module.visit_types(|ty| {
        if refusal.is_none()
            && let Some(handle) = ty.handle_ty()
        {
            refusal = Some(AdapterError::OpaqueHandleNotAdmitted {
                name: handle.name.clone(),
                runtime: handle.runtime.clone(),
                location: format!("module `{}` on the {lane} lane", module.name),
                detail: "this lane has no channel to a pinned native runtime entry point, so it \
                         can neither produce nor consume an opaque runtime handle; lowering the \
                         word here would let an import forge one"
                    .to_string(),
            });
        }
    });
    refusal.map_or(Ok(()), Err)
}

/// Every handle identity that occurs must be lexically well-formed AND have a
/// row in the pinned registry. First failure in module-walk order wins, so
/// the verdict is deterministic.
fn reject_unpinned_identities(
    module: &TrustIrModule,
    registry: &HandleRegistry,
) -> Result<(), AdapterError> {
    let mut refusal = None;
    module.visit_types(|ty| {
        if refusal.is_some() {
            return;
        }
        let Some(handle) = ty.handle_ty() else {
            return;
        };
        let detail = match handle.validate() {
            Err(error) => Some(error.to_string()),
            Ok(()) => registry.pin_for(handle).is_none().then(|| {
                format!(
                    "no trusted runtime pins this pair; the {} pinned runtime(s) are: {}",
                    registry.pins().len(),
                    pinned_runtime_list(registry)
                )
            }),
        };
        if let Some(detail) = detail {
            refusal = Some(AdapterError::UntrustedOpaqueHandleRuntime {
                name: handle.name.clone(),
                runtime: handle.runtime.clone(),
                location: format!("module `{}`", module.name),
                detail,
            });
        }
    });
    refusal.map_or(Ok(()), Err)
}

fn pinned_runtime_list(registry: &HandleRegistry) -> String {
    registry
        .pins()
        .iter()
        .map(|pin| format!("handle<{:?}, {:?}>", pin.name, pin.runtime))
        .collect::<Vec<_>>()
        .join(", ")
}

/// trust-ir-build's own handle verdict on this module, as a diagnostic string,
/// or `None` when its handle rules hold.
///
/// Only the handle-class errors are consulted. `validate_module` deliberately
/// lets a module carry constructs this backend refuses for unrelated reasons,
/// and an unrelated validity quirk must not be reported as a handle refusal.
#[must_use]
pub fn handle_validation_refusal(module: &TrustIrModule) -> Option<String> {
    validate_module(module).into_iter().find_map(|error| {
        matches!(
            error,
            ValidationError::InvalidHandleType { .. }
                | ValidationError::UntrustedHandleRuntime { .. }
                | ValidationError::HandleEntryPointSignatureMismatch { .. }
                | ValidationError::HandleEntryPointDefinedLocally { .. }
                | ValidationError::HandleEntryPointShadowedByGlobal { .. }
                | ValidationError::HandleEntryPointAddressTaken { .. }
                | ValidationError::HandleForeignDeclaration { .. }
                | ValidationError::InvalidHandleUse { .. }
        )
        .then(|| error.to_string())
    })
}

/// The pinned-SYMBOL namespace: a link-time symbol a trusted runtime exports
/// may be spelled ONLY as that runtime's exact pinned declaration.
///
/// A module that DEFINES `trust_bignum_nat_add`, or declares it with an
/// ordinary `Ptr` signature, or hangs the name on a global, would link against
/// the real runtime while being free to forge every word it hands back. That
/// is refused here exactly as trust-ir-build refuses it — including for the
/// runtime's own implementation, which is trusted source compiled by its own
/// toolchain, never a body this backend emits.
fn reject_pinned_symbol_impostors(
    module: &TrustIrModule,
    registry: &HandleRegistry,
) -> Result<(), AdapterError> {
    for global in &module.globals {
        if let Some((pin, _)) = registry.entry_for_symbol(&global.name) {
            return Err(handle_refusal(
                pin,
                format!("global `{}`", global.name),
                "a pinned runtime entry-point symbol names a C function, and a global wearing it \
                 shadows the declaration every handle origin has to go through",
            ));
        }
    }
    for function in &module.functions {
        let Some((pin, entry)) = registry.entry_for_symbol(&function.name) else {
            continue;
        };
        let expected = pin.func_ty(entry);
        let actual = module.func_type(function.ty);
        let exact = actual.is_some_and(|actual| *actual == expected)
            && function.calling_conv == pin.calling_conv
            && !function.attrs.naked
            && function
                .display_path
                .as_ref()
                .is_none_or(|path| path == entry.def_path);
        if !exact {
            return Err(handle_refusal(
                pin,
                format!("function `{}`", function.name),
                &format!(
                    "it takes the pinned entry-point symbol of role `{}` but not its pinned \
                     contract ({} {}, display path {:?} or unrecorded); a symbol that links the \
                     real runtime must declare exactly what the runtime exports",
                    entry.role,
                    pin.calling_conv,
                    format_func_ty(&expected),
                    entry.def_path,
                ),
            ));
        }
        if !function.is_declaration() || function.linkage != Linkage::External {
            return Err(handle_refusal(
                pin,
                format!("function `{}`", function.name),
                "a pinned entry point is the runtime's own C symbol: a local definition of it \
                 would let this module forge every handle the symbol produces",
            ));
        }
    }
    Ok(())
}

/// Any named definition or global whose type REACHES a handle. These are the
/// LAYOUT positions: a field offset, an element stride, a closure-environment
/// slot, a static's storage. Giving a handle any of them makes the word
/// addressable, and an addressable word can be stored and re-read as an
/// ordinary pointer — the exact forgery the type exists to prevent.
fn reject_handle_bearing_definitions(
    module: &TrustIrModule,
    nominal: &NominalTypeReachability<'_>,
) -> Result<(), AdapterError> {
    for definition in &module.structs {
        for field in &definition.fields {
            reject_reach(
                module,
                nominal,
                &field.ty,
                || format!("field `{}` of struct `{}`", field.name, definition.name),
                "a struct field has an OFFSET",
            )?;
        }
    }
    for definition in &module.records {
        for field in &definition.fields {
            reject_reach(
                module,
                nominal,
                &field.ty,
                || format!("field `{}` of record `{}`", field.name, definition.name),
                "a record field has an OFFSET",
            )?;
        }
    }
    for definition in &module.enums {
        for variant in &definition.variants {
            for (index, ty) in variant.fields.iter().enumerate() {
                reject_reach(
                    module,
                    nominal,
                    ty,
                    || {
                        format!(
                            "field {index} of variant `{}` of enum `{}`",
                            variant.name, definition.name
                        )
                    },
                    "an enum payload field shares an image with a tag",
                )?;
            }
        }
    }
    for (index, closure) in module.closure_types.iter().enumerate() {
        for capture in &closure.captures {
            reject_reach(
                module,
                nominal,
                capture,
                || format!("a capture of closure type {index}"),
                "a closure capture lives in an environment frame",
            )?;
        }
        if let Some(signature) = module.func_type(closure.func) {
            reject_signature_reach(
                module,
                nominal,
                signature,
                &format!("the apparent signature of closure type {index}"),
                "a closure is an indirect callee, so its handle slots have no statically pinned \
                 origin",
            )?;
        }
    }
    for global in &module.globals {
        reject_reach(
            module,
            nominal,
            &global.ty,
            || format!("global `{}`", global.name),
            "a global is STORAGE with a link-time address",
        )?;
    }
    for (index, ty) in module.types.iter().enumerate() {
        if ty.is_handle() {
            // A bare row is how a `TyId` NAMES a handle. Admitted.
            continue;
        }
        reject_reach(
            module,
            nominal,
            ty,
            || format!("type-table entry {index} ({ty:?})"),
            "a composite type that reaches a handle would give the word a layout",
        )?;
    }
    for (index, signature) in module.func_types.iter().enumerate() {
        reject_signature_reach(
            module,
            nominal,
            signature,
            &format!("signature functy.{index}"),
            "a handle crosses a call edge as a WHOLE pointer-word value or not at all",
        )?;
    }
    Ok(())
}

/// One function's handle surface: its block parameters and every instruction.
fn admit_function(
    module: &TrustIrModule,
    function: &TrustIrFunction,
    nominal: &NominalTypeReachability<'_>,
    registry: &HandleRegistry,
) -> Result<(), AdapterError> {
    if function.is_declaration() {
        // Declarations are the ONLY handle origins, so a bodyless declaration
        // whose signature reaches a handle must be a pinned entry point.
        // `reject_pinned_symbol_impostors` already established that a pinned
        // symbol carries its exact pinned contract.
        if registry.entry_for_symbol(&function.name).is_none()
            && let Some(signature) = module.func_type(function.ty)
            && let Some(slot) = first_handle_slot(nominal, signature)
        {
            return Err(unpinned_declaration_refusal(
                module, nominal, function, slot,
            ));
        }
        return Ok(());
    }
    for block in &function.blocks {
        for (_, ty) in &block.params {
            if ty.is_handle() {
                // Transport across a branch edge: a block parameter is an SSA
                // value slot, not storage.
                continue;
            }
            reject_reach(
                module,
                nominal,
                ty,
                || {
                    format!(
                        "a parameter of bb{} in function `{}`",
                        block.id.index(),
                        function.name
                    )
                },
                "a block parameter carries a handle as a WHOLE pointer-word value or not at all",
            )?;
        }
        for (index, node) in block.body.iter().enumerate() {
            let location = || {
                format!(
                    "function `{}` bb{}#{index}",
                    function.name,
                    block.id.index()
                )
            };
            // The instruction's INLINE types decide every non-call opcode:
            // `Load`/`Store`/`Alloca`/`GEP`/`Cast`/`ICmp`/`BinOp`/atomics/
            // `Const`/`Undef`/`DialectOp` all spell the type they act on.
            let mut inline_handle = None;
            node.inst.visit_types(|ty| {
                if inline_handle.is_none() && nominal.contains_handle(ty) {
                    inline_handle = Some(ty);
                }
            });
            if let Some(ty) = inline_handle {
                let transport = match &node.inst {
                    // Register transport at EXACTLY the handle type. The
                    // operand-level exactness is trust-ir-build's own rule 7
                    // check (it holds the SSA type map); what is decided here
                    // is that the opcode is transport at all.
                    Inst::Copy { ty, .. } | Inst::Select { ty, .. } => ty.is_handle(),
                    _ => false,
                };
                if !transport {
                    return Err(reach_refusal(
                        module,
                        nominal,
                        ty,
                        location(),
                        &format!(
                            "`{}` is not exact-typed transport: a handle may only be copied, \
                             selected, passed to or returned from a call whose callee is pinned \
                             or module-local, or carried across a branch edge",
                            inst_name(&node.inst)
                        ),
                    ));
                }
            }
            match &node.inst {
                // This is only the handle-origin census. Boundary enforcement
                // remains a separate mandatory floor; the boundary neither
                // authenticates a handle origin nor grants native admission.
                Inst::Call { callee, .. }
                | Inst::CallCannotUnwind { callee, .. }
                | Inst::Invoke { callee, .. } => {
                    admit_call_edge(module, nominal, registry, *callee, location)?;
                }
                Inst::CallIndirect { sig, .. }
                | Inst::CallIndirectCannotUnwind { sig, .. }
                | Inst::InvokeIndirect { sig, .. } => {
                    // ANY handle reach, bare included: unlike a direct call
                    // there is no callee to check against the registry.
                    if let Some(signature) = module.func_type(*sig)
                        && let Some(ty) = signature
                            .params
                            .iter()
                            .chain(&signature.returns)
                            .find(|ty| nominal.contains_handle(ty))
                    {
                        return Err(reach_refusal(
                            module,
                            nominal,
                            ty,
                            location(),
                            "an indirect callee is resolved at run time, so this backend cannot \
                             establish that the handle's origin is a pinned runtime entry point",
                        ));
                    }
                }
                _ => {}
            }
        }
    }
    Ok(())
}

/// A direct call/invoke edge whose signature reaches a handle is admitted only
/// when the callee is a PINNED entry point (the origin) or a function DEFINED
/// in this module (whose own body this same pass audits). Any other callee —
/// an unpinned foreign declaration, a dangling id — is refused.
fn admit_call_edge(
    module: &TrustIrModule,
    nominal: &NominalTypeReachability<'_>,
    registry: &HandleRegistry,
    callee: trust_ir::FuncId,
    location: impl Fn() -> String,
) -> Result<(), AdapterError> {
    let Some(function) = module.functions.iter().find(|func| func.id == callee) else {
        return Ok(());
    };
    let Some(signature) = module.func_type(function.ty) else {
        return Ok(());
    };
    let Some(slot) = first_handle_slot(nominal, signature) else {
        return Ok(());
    };
    if registry.entry_for_symbol(&function.name).is_some() || !function.is_declaration() {
        return Ok(());
    }
    Err(reach_refusal(
        module,
        nominal,
        slot,
        location(),
        &format!(
            "the callee `{}` is a bodyless declaration that is not a pinned runtime entry point, \
             so the handle it takes or returns has no trusted origin",
            function.name
        ),
    ))
}

/// `slot` is the first signature slot that reaches a handle, found by the
/// caller with [`first_handle_slot`].
fn unpinned_declaration_refusal(
    module: &TrustIrModule,
    nominal: &NominalTypeReachability<'_>,
    function: &TrustIrFunction,
    slot: &Ty,
) -> AdapterError {
    reach_refusal(
        module,
        nominal,
        slot,
        format!("declaration `{}`", function.name),
        "declarations are the ONLY handle origins, and this one is not a pinned runtime entry \
         point",
    )
}

/// The first parameter or return slot of `signature` that reaches a handle.
/// `None` exactly when no slot reaches one.
fn first_handle_slot<'s>(
    nominal: &NominalTypeReachability<'_>,
    signature: &'s FuncTy,
) -> Option<&'s Ty> {
    signature
        .params
        .iter()
        .chain(&signature.returns)
        .find(|ty| nominal.contains_handle(ty))
}

/// Refuse `ty` if it reaches a handle at all. Used for every LAYOUT slot,
/// where a bare handle is no more admissible than a nested one.
fn reject_reach(
    module: &TrustIrModule,
    nominal: &NominalTypeReachability<'_>,
    ty: &Ty,
    location: impl Fn() -> String,
    why: &str,
) -> Result<(), AdapterError> {
    if !nominal.contains_handle(ty) {
        return Ok(());
    }
    Err(reach_refusal(module, nominal, ty, location(), why))
}

/// Refuse a signature whose params/returns reach a handle anywhere but as a
/// BARE handle.
fn reject_signature_reach(
    module: &TrustIrModule,
    nominal: &NominalTypeReachability<'_>,
    signature: &FuncTy,
    location: &str,
    why: &str,
) -> Result<(), AdapterError> {
    for (index, ty) in signature
        .params
        .iter()
        .chain(&signature.returns)
        .enumerate()
    {
        if ty.is_handle() || !nominal.contains_handle(ty) {
            continue;
        }
        return Err(reach_refusal(
            module,
            nominal,
            ty,
            format!("{location} slot {index}"),
            why,
        ));
    }
    Ok(())
}

fn reach_refusal(
    module: &TrustIrModule,
    nominal: &NominalTypeReachability<'_>,
    ty: &Ty,
    location: String,
    why: &str,
) -> AdapterError {
    let handles = reachable_handle_identities(module, nominal, ty);
    let (name, runtime) = handles.iter().next().map_or_else(
        || ("<unknown>".to_string(), "<unknown>".to_string()),
        |handle| (handle.name.clone(), handle.runtime.clone()),
    );
    let reached = handles
        .iter()
        .map(|handle| format!("handle<{:?}, {:?}>", handle.name, handle.runtime))
        .collect::<Vec<_>>()
        .join(", ");
    AdapterError::OpaqueHandleNotAdmitted {
        name,
        runtime,
        location,
        detail: format!("{why} (type {ty:?} reaches {reached})"),
    }
}

fn handle_refusal(pin: &HandleRuntimePin, location: String, why: &str) -> AdapterError {
    AdapterError::OpaqueHandleNotAdmitted {
        name: pin.name.to_string(),
        runtime: pin.runtime.to_string(),
        location,
        detail: why.to_string(),
    }
}

/// Every handle identity reachable from `root`, following the module's named
/// type tables. Cycle-safe, and reached only on a REFUSAL path — the boolean
/// question is [`NominalTypeReachability::contains_handle`]'s, which is
/// indexed; this walk exists only to NAME what was reached.
fn reachable_handle_identities(
    module: &TrustIrModule,
    nominal: &NominalTypeReachability<'_>,
    root: &Ty,
) -> BTreeSet<HandleTy> {
    let mut identities = BTreeSet::new();
    let mut seen_types = BTreeSet::new();
    let mut seen_signatures = BTreeSet::new();
    let mut seen_structs = BTreeSet::new();
    let mut seen_records = BTreeSet::new();
    let mut seen_enums = BTreeSet::new();
    let mut seen_closures = BTreeSet::new();
    let mut pending = vec![root.clone()];
    while let Some(ty) = pending.pop() {
        let mut inline = Vec::new();
        ty.visit_types(|child| inline.push(child.clone()));
        for child in inline {
            if let Some(handle) = child.handle_ty() {
                identities.insert(handle.clone());
                continue;
            }
            if !nominal.contains_handle(&child) {
                continue;
            }
            match &child {
                Ty::Struct(id) => {
                    if !seen_structs.insert(*id) {
                        continue;
                    }
                    // Duplicate IDs conservatively contribute every matching
                    // definition, but a recursive edge expands this ID once.
                    for definition in module.structs.iter().filter(|def| def.id == *id) {
                        pending.extend(definition.fields.iter().map(|field| field.ty.clone()));
                    }
                }
                Ty::Record(id) => {
                    if !seen_records.insert(*id) {
                        continue;
                    }
                    for definition in module.records.iter().filter(|def| def.id == *id) {
                        pending.extend(definition.fields.iter().map(|field| field.ty.clone()));
                    }
                }
                Ty::Enum(id) => {
                    if !seen_enums.insert(*id) {
                        continue;
                    }
                    for definition in module.enums.iter().filter(|def| def.id == *id) {
                        for variant in &definition.variants {
                            pending.extend(variant.fields.iter().cloned());
                        }
                    }
                }
                Ty::Closure(id) => {
                    if !seen_closures.insert(*id) {
                        continue;
                    }
                    for closure in module
                        .closure_types
                        .iter()
                        .enumerate()
                        .filter(|(index, _)| *index == id.as_usize())
                        .map(|(_, closure)| closure)
                    {
                        pending.extend(closure.captures.iter().cloned());
                        push_signature(module, closure.func, &mut seen_signatures, &mut pending);
                    }
                }
                Ty::Func(id) => push_signature(module, *id, &mut seen_signatures, &mut pending),
                Ty::Array(id, _) | Ty::Sequence(id) | Ty::Set(id, _) | Ty::Refine(id, _) => {
                    if seen_types.insert(id.index())
                        && let Some(referent) = module.types.get(id.as_usize())
                    {
                        pending.push(referent.clone());
                    }
                }
                Ty::FatPtr(trust_ir::FatPtrKind::Slice(id)) => {
                    if seen_types.insert(id.index())
                        && let Some(referent) = module.types.get(id.as_usize())
                    {
                        pending.push(referent.clone());
                    }
                }
                _ => {}
            }
        }
    }
    identities
}

fn push_signature(
    module: &TrustIrModule,
    id: FuncTyId,
    seen: &mut BTreeSet<u32>,
    pending: &mut Vec<Ty>,
) {
    if !seen.insert(id.index()) {
        return;
    }
    if let Some(signature) = module.func_type(id) {
        pending.extend(signature.params.iter().chain(&signature.returns).cloned());
    }
}

fn format_func_ty(signature: &FuncTy) -> String {
    format!(
        "fn({}) -> ({})",
        signature
            .params
            .iter()
            .map(|ty| format!("{ty:?}"))
            .collect::<Vec<_>>()
            .join(", "),
        signature
            .returns
            .iter()
            .map(|ty| format!("{ty:?}"))
            .collect::<Vec<_>>()
            .join(", "),
    )
}

/// The opcode name a refusal reports. `Inst` has no stable name accessor, and
/// its `Debug` renders every operand, so a refusal message would otherwise
/// carry the whole instruction.
pub(crate) fn inst_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::BinOp { .. } => "BinOp",
        Inst::UnOp { .. } => "UnOp",
        Inst::Overflow { .. } => "Overflow",
        Inst::ICmp { .. } => "ICmp",
        Inst::FCmp { .. } => "FCmp",
        Inst::Cast { .. } => "Cast",
        Inst::Load { .. } => "Load",
        Inst::Store { .. } => "Store",
        Inst::MemCopy { .. } => "MemCopy",
        Inst::MemSet { .. } => "MemSet",
        Inst::Alloca { .. } => "Alloca",
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::GEP { .. } => "GEP",
        Inst::PtrData { .. } => "PtrData",
        Inst::PtrMetadata { .. } => "PtrMetadata",
        Inst::PtrFromParts { .. } => "PtrFromParts",
        Inst::Dealloc { .. } => "Dealloc",
        Inst::AtomicLoad { .. } => "AtomicLoad",
        Inst::AtomicStore { .. } => "AtomicStore",
        Inst::AtomicRMW { .. } => "AtomicRMW",
        Inst::CmpXchg { .. } => "CmpXchg",
        Inst::Fence { .. } => "Fence",
        Inst::Borrow { .. } => "Borrow",
        Inst::BorrowMut { .. } => "BorrowMut",
        Inst::EndBorrow { .. } => "EndBorrow",
        Inst::Retain { .. } => "Retain",
        Inst::Release { .. } => "Release",
        Inst::IsUnique { .. } => "IsUnique",
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Return { .. } => "Return",
        Inst::Unreachable => "Unreachable",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::CallCannotUnwind { .. } => "CallCannotUnwind",
        Inst::CallIndirectCannotUnwind { .. } => "CallIndirectCannotUnwind",
        Inst::CoroSuspend { .. } => "CoroSuspend",
        Inst::Invoke { .. } => "Invoke",
        Inst::LandingPad { .. } => "LandingPad",
        Inst::Resume { .. } => "Resume",
        Inst::AssertInvoke { .. } => "AssertInvoke",
        Inst::DropInvoke { .. } => "DropInvoke",
        Inst::InvokeIndirect { .. } => "InvokeIndirect",
        Inst::MakeAggregate { .. } => "MakeAggregate",
        Inst::MakeClosure { .. } => "MakeClosure",
        Inst::ArraySplat { .. } => "ArraySplat",
        Inst::ExtractField { .. } => "ExtractField",
        Inst::InsertField { .. } => "InsertField",
        Inst::ExtractElement { .. } => "ExtractElement",
        Inst::InsertElement { .. } => "InsertElement",
        Inst::SeqMapAddK { .. } => "SeqMapAddK",
        Inst::SeqMapNot { .. } => "SeqMapNot",
        Inst::SeqMap { .. } => "SeqMap",
        Inst::Const { .. } => "Const",
        Inst::NullPtr => "NullPtr",
        Inst::GlobalAddr { .. } => "GlobalAddr",
        Inst::Undef { .. } => "Undef",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        Inst::OpenFrame { .. } => "OpenFrame",
        Inst::BindSlot { .. } => "BindSlot",
        Inst::LoadSlot { .. } => "LoadSlot",
        Inst::CloseFrame { .. } => "CloseFrame",
        Inst::DialectOp(_) => "DialectOp",
        Inst::Drop { .. } => "Drop",
        Inst::TensorContract { .. } => "TensorContract",
        Inst::TensorMap { .. } => "TensorMap",
        Inst::TensorReduce { .. } => "TensorReduce",
        Inst::TensorView { .. } => "TensorView",
        Inst::TensorGather { .. } => "TensorGather",
        Inst::TensorScatter { .. } => "TensorScatter",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{
        ClosureTy, ClosureTyId, EnumDef, EnumId, EnumVariant, FieldDef, RecordDef, RecordId,
        StructDef, StructId, TyId,
    };

    #[test]
    fn call_boundary_handle_origins_remain_pinned_and_indirect_calls_refuse() {
        use trust_ir::{Block, BlockId, CallingConv, FuncId, InstrNode, ValueId};
        let handle = Ty::handle("Nat", "trust_bignum::Nat");
        let mut module = TrustIrModule::new("boundary-handle-origins");
        let signature = module
            .add_func_type(FuncTy {
                params: vec![handle.clone()],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let caller_signature = module
            .add_func_type(FuncTy {
                params: vec![handle.clone(), Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module.functions.push(TrustIrFunction::new(
            FuncId::new(1),
            "untrusted_handle_origin",
            signature,
            BlockId::new(0),
        ));
        let mut caller =
            TrustIrFunction::new(FuncId::new(0), "caller", caller_signature, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0))
            .with_param(ValueId::new(0), handle)
            .with_param(ValueId::new(1), Ty::Ptr);
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        caller.blocks.push(entry);
        let nominal = module.nominal_type_reachability();
        for (inst, reason) in [
            (
                Inst::CallCannotUnwind {
                    callee: FuncId::new(1),
                    args: vec![ValueId::new(0)],
                },
                "not a pinned runtime entry point",
            ),
            (
                Inst::CallIndirectCannotUnwind {
                    callee: ValueId::new(1),
                    sig: signature,
                    args: vec![ValueId::new(0)],
                    calling_conv: CallingConv::C,
                },
                "an indirect callee is resolved at run time",
            ),
        ] {
            let mut candidate = caller.clone();
            candidate.blocks[0].body.insert(0, InstrNode::new(inst));
            // Isolate this consumer's origin guard. This is not validation of
            // the module's unrelated validity or boundary target enforcement.
            let error = admit_function(&module, &candidate, &nominal, HandleRegistry::pinned())
                .expect_err("a call boundary grants no trusted handle origin");
            assert!(error.to_string().contains(reason), "{error}");
        }
    }

    #[test]
    fn call_boundary_diagnostics_keep_distinct_constructor_names() {
        assert_eq!(
            inst_name(&Inst::CallCannotUnwind {
                callee: trust_ir::FuncId::new(0),
                args: vec![],
            }),
            "CallCannotUnwind"
        );
        assert_eq!(
            inst_name(&Inst::CallIndirectCannotUnwind {
                callee: trust_ir::ValueId::new(0),
                sig: FuncTyId::new(0),
                args: vec![],
                calling_conv: trust_ir::CallingConv::C,
            }),
            "CallIndirectCannotUnwind"
        );
    }

    #[test]
    fn recursive_named_diagnostics_preserve_the_complete_handle_census() {
        // All table families deliberately use ID zero: their identities must
        // stay disjoint. Each new named-table guard has its own self-cycle,
        // and the families also form a mutually recursive graph.
        let mut module = TrustIrModule::new("recursive-handle-diagnostic");
        let structure = Ty::Struct(StructId::new(0));
        let record = Ty::Record(RecordId::new(0));
        let enumeration = Ty::Enum(EnumId::new(0));
        let closure = Ty::Closure(ClosureTyId::new(0));
        let handle = |name: &str| Ty::handle(name, "diagnostic::Runtime");
        let field = |name: &str, ty| FieldDef {
            name: name.to_string(),
            ty,
            offset: None,
        };
        module.structs.push(StructDef {
            origin: None,
            id: StructId::new(0),
            name: "S".to_string(),
            fields: vec![
                field("self", Ty::PtrConst(Box::new(structure.clone()))),
                field("record", record.clone()),
            ],
            size: None,
            align: None,
            repr: Default::default(),
        });
        // Even malformed duplicate named IDs must not hide a reachable handle
        // from the diagnostic. Validity remains a separate admission check.
        let mut duplicate = module.structs[0].clone();
        duplicate.fields = vec![field("extra", handle("D"))];
        module.structs.push(duplicate);
        module.records.push(RecordDef {
            id: RecordId::new(0),
            name: "R".to_string(),
            fields: vec![
                field("self", Ty::PtrConst(Box::new(record.clone()))),
                field("enum", enumeration.clone()),
            ],
        });
        module.enums.push(EnumDef::new(
            EnumId::new(0),
            "E",
            vec![EnumVariant {
                name: "V".to_string(),
                fields: vec![Ty::PtrConst(Box::new(enumeration.clone())), closure.clone()],
                field_names: vec![],
            }],
        ));
        let signature = module
            .add_func_type(FuncTy {
                params: vec![closure.clone()],
                returns: vec![Ty::Sequence(TyId::new(0)), handle("C")],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module.closure_types.push(ClosureTy {
            func: signature,
            captures: vec![closure.clone(), structure.clone(), handle("B")],
        });
        module.types.push(Ty::Tuple(vec![
            Ty::Array(TyId::new(0), 1),
            structure.clone(),
            handle("A"),
        ]));
        let expected = ["A", "B", "C", "D"]
            .into_iter()
            .map(|name| handle(name).handle_ty().unwrap().clone())
            .collect::<BTreeSet<_>>();
        let nominal = module.nominal_type_reachability();
        for root in [structure, record, enumeration, closure, Ty::Func(signature)] {
            assert_eq!(
                reachable_handle_identities(&module, &nominal, &root),
                expected,
                "root {root:?} must preserve every reachable identity"
            );
        }
        assert!(reachable_handle_identities(&module, &nominal, &Ty::I64).is_empty());
    }
}
