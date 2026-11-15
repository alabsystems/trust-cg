// Copyright 2026 Andrew Yates | Apache-2.0

//! Target facts and flat signature-pointee layouts from rustc, not inferred
//! from the bridge's structural tuple or its opaque aggregate ABI shells.

use super::*;
use rustc_target::callconv::PassMode;
use signature_layouts::PointeeLayout;

/// The aggregate-passing policy this bridge stamps on every module it emits:
/// the target's native C ABI classification (`NativeC`).
///
/// trust-ir `docs/SPEC_RATIFICATIONS.md` §17 ("Aggregate passing: one slot
/// predicate; the consumer classifies under NativeC; AlwaysMemory is
/// pre-lowered; Unclassified is an absence") defines what that stamp claims:
/// the CONSUMER classifies each by-value aggregate slot by the target's
/// ruleset for the edge's convention, and the PRODUCER claims that placement is
/// the one the other side of every edge uses, marking nothing to say so (no
/// `byval` / `sret` marking is required; that sentence of trust-ir's earlier
/// variant docs is retracted). Whether the claim is true is not decidable in
/// trust-ir. This bridge checks it against rustc's own `FnAbi` at every
/// declaration and call site it lowers, argument by argument, and what that
/// establishes differs by placement.
///
/// MEMORY-placed arguments — rustc's Rust ABI passes every sized
/// `BackendRepr::Memory` value larger than a pointer as `PassMode::Indirect {
/// on_stack: false }`, a pointer to a caller copy, while the C ruleset places
/// many of them in registers (at most 16 bytes, or an AArch64 homogeneous float
/// aggregate) or, on System V, as a `byval` stack copy — are §17's case: such a
/// slot must be pre-lowered or refused. On x86-64 and AArch64 (Apple and ELF;
/// not Windows) it is PRE-LOWERED: the indirect argument lane
/// (`MirLoweringCtx::indirect_arg_param_plan`) declares the argument as ONE
/// `Ptr`, every call site passes the address of a fresh copy and the callee
/// copies the pointee into its own slot. A `Ptr` parameter is not a by-value
/// aggregate slot in trust-ir's one predicate (`Module::is_by_value_aggregate_slot`),
/// so no slot is left for the consumer to classify, and §17 needs no second
/// pre-lowered spelling for it. The argument gate
/// (`MirLoweringCtx::check_param_abi_lanes`) compares that pointer against
/// rustc's placement, and one table decides every placement MODE
/// (`abi_reg_lanes::arg_memory_placement_verdict`, each cell a unit test): a
/// by-value declaration of a caller-made copy is refused unless trust-cg's own
/// classifier also passes it as one (AAPCS64 §6.8.2 B.4); a caller-made copy on
/// a target with no lane, a `byval` copy off x86-64 System V, and an ignored
/// argument are refused by name (`[TCG-ARG-ABI]`); and x86-64 System V `byval`
/// (C-ABI only) is ADMITTED BY A NAMED RULE — trust-cg's MEMORY class and its
/// all-or-nothing rule at exhaustion place it as a stack copy — not compared.
/// Every other target is refused before any lane is placed
/// (`check_aggregate_abi_scope`, `[TCG-AGGREGATE-ABI-SCOPE]`). An over-aligned
/// single-scalar newtype — one scalar to the bridge, a padded `Memory` value to
/// rustc — takes the same pointer through the lane's scalar sub-lane, and a
/// scalar declaration rustc places otherwise — a pointer carrier included — is
/// refused (`MirLoweringCtx::refuse_scalar_declared_memory_arg`, and
/// `check_scalar_return_abi` for a return). Measured across a real rlib x bin
/// boundary on aarch64-apple-darwin, 2026-09-29 (`targo --unverified`, no proof
/// claim): the `m145` matrix agrees with LLVM x LLVM in every cell that
/// compiles, and a 12-byte argument passed after eight `u64`s — the pointer on
/// the stack — agrees in all four cells.
///
/// REGISTER-placed arguments and returns are compared by `abi_reg_lanes`
/// (`trust_cg_param_placement` / `trust_cg_return_placement` against
/// `rustc_placement`, by `lanes_disagreement`; `aggregate_abi_scope` admitting
/// only the C / ordinary-Rust / SysV64 conventions it models; a memory-classed
/// return spelled as the hidden `sret` parameter the format defines). An
/// argument's MODE is compared per slot (`check_param_abi`: class, count,
/// per-lane extent and value offset); WHERE every argument lands is compared
/// per SIGNATURE (`MirLoweringCtx::check_signature_placement`): rustc's backend
/// value list and the declared one, both placed by trust-cg's own classifier
/// (AArch64 `classify_params_with` with the target's variant, x86-64
/// `x86_sysv_param_locations`), every live byte's register or stack byte
/// compared, register numbering and exhaustion included, for every
/// declaration the bridge emits. The families that check was built on
/// (`tests/signature_placement_families_xback.rs`, aarch64 natively and x86-64
/// under Rosetta): pairs at the last register of their class, narrow Rust-ABI
/// `Cast`s on the Darwin stack (now declared as the one integer rustc passes,
/// `narrow_cast_param_plan`; before, 7 shapes were silently wrong), closure
/// bodies and by-value closure environments (now on rustc's convention through
/// one closure-argument builder), and `extern "rust-call"` function items and
/// shims (now declared with the argument tuple's elements, as rustc's `FnAbi`
/// lists them, `rust_call_spread`). What a pass rests on — trust-cg's classifier
/// placing rustc's value alphabet as LLVM does, and the `PassMode` -> value
/// model — is shared by both sides of the comparison, so its evidence is that
/// matrix, test rung, not the check.
///
/// NOT covered: an intercepted collection (`Vec` / `String` / the maps, by
/// identity) passed
/// or returned by value, whose bridge value is a pointer to the bridge's OWN
/// slot layout rather than rustc's; and the x86-64 RETURN side reads
/// `abi_reg_lanes`' statement of the System V return rules, a copy of the
/// selector's, not the selector's own function. `LIMITATIONS.md` records each
/// ("Cross-backend `Memory`-argument ABI", "Register exhaustion"). A refusal of
/// every memory-placed argument was measured and not landed: it refuses the
/// all-bridge edges that agree (215 `core` roots on x86-64 Darwin before the
/// lane existed, and `m142_deref_store_leaf_offsets_match_llvm` on AArch64).
///
/// It stamped `Unclassified` until 2026-09-25. trust-ir defines that value
/// as "the producer did not establish the placement, and says so" and binds a
/// consumer that needs one to REFUSE rather than pick it (must-refuse corpus
/// rows `refuse/struct_passing_unclassified_*`); measured against this bridge,
/// trust-cg-lower refused every `extern "C"` function passing or returning an
/// aggregate by value (4 of 5 probe functions, only the scalar control
/// compiled). `Unclassified` was never this bridge's fact.
pub(super) const STRUCT_PASSING: trust_ir::StructPassingPolicy =
    trust_ir::StructPassingPolicy::NativeC;

pub(super) fn attach(ctx: &mut MirLoweringCtx<'_>) {
    ctx.module.target_info = Some(trust_ir::TargetInfo {
        triple: ctx.tcx.sess.opts.target_triple.to_string(),
        pointer_size: ctx.tcx.data_layout.pointer_size().bytes() as u32,
        endianness: match ctx.tcx.data_layout.endian {
            rustc_abi::Endian::Little => trust_ir::Endianness::Little,
            rustc_abi::Endian::Big => trust_ir::Endianness::Big,
        },
        abi: None,
        struct_passing: STRUCT_PASSING,
    });
    if let Some(layouts) = signature_pointees(ctx) {
        signature_layouts::install(&mut ctx.module, &layouts);
    }
}

fn signature_pointees(ctx: &MirLoweringCtx<'_>) -> Option<Vec<PointeeLayout>> {
    if !ctx.current_fn_c_abi || ctx.module.functions.len() != 1 {
        return None;
    }
    let abi = RustcFnAbiSource::Instance(ctx.instance)
        .query(ctx.tcx)
        .ok()?;
    let signature = ctx
        .module
        .func_types
        .get(ctx.module.functions[0].ty.index() as usize)?;
    if abi.conv != rustc_abi::CanonAbi::C
        || abi.c_variadic
        || signature.is_vararg
        || abi.args.len() != signature.params.len()
    {
        return None;
    }
    let mut layouts = Vec::new();
    for (arg, declared) in abi.args.iter().zip(&signature.params) {
        if !matches!(arg.mode, PassMode::Direct(_)) {
            return None;
        }
        let source = ctx.normalize_ty(arg.layout.ty);
        if rust_ty_to_trust_ir_ty(ctx.tcx, source).ok()?.ne(declared) {
            return None;
        }
        let shape = ctx.module.ty_layout_shape(declared).ok()?;
        if shape.size_bits != arg.layout.size.bits()
            || shape.align_bits != Some(arg.layout.align.bytes() * 8)
        {
            return None;
        }
        match source.kind() {
            ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => {
                let lowered = reference_pointee_to_trust_ir_ty(ctx.tcx, *pointee).ok()?;
                if matches!(lowered, TrustIrTy::Tuple(_)) {
                    layouts.push(flat_pointee(ctx.tcx, *pointee, lowered)?);
                } else if primitive_source(*pointee).is_none() {
                    return None;
                }
            }
            _ => {
                primitive_source(source)?;
            }
        }
    }
    match &abi.ret.mode {
        PassMode::Ignore if abi.ret.layout.ty.is_unit() && signature.returns.is_empty() => {}
        PassMode::Direct(_) if signature.returns.len() == 1 => {
            primitive_source(abi.ret.layout.ty)?;
            let mapped = rust_ty_to_trust_ir_ty(ctx.tcx, abi.ret.layout.ty).ok()?;
            if signature.returns[0] != mapped {
                return None;
            }
            let shape = ctx.module.ty_layout_shape(&mapped).ok()?;
            if shape.size_bits != abi.ret.layout.size.bits()
                || shape.align_bits != Some(abi.ret.layout.align.bytes() * 8)
            {
                return None;
            }
        }
        _ => return None,
    }
    Some(layouts)
}

fn primitive_source(ty: Ty<'_>) -> Option<()> {
    matches!(
        ty.kind(),
        ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64)
    )
    .then_some(())
}

fn flat_pointee<'tcx>(
    tcx: TyCtxt<'tcx>,
    source: Ty<'tcx>,
    lowered: TrustIrTy,
) -> Option<PointeeLayout> {
    let TrustIrTy::Tuple(declared) = &lowered else {
        return None;
    };
    if declared.is_empty() || declared.len() > 65_536 {
        return None;
    }
    let layout = tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(source))
        .ok()?;
    let fields: Vec<Ty<'tcx>> = match source.kind() {
        ty::Array(element, len) => {
            primitive_source(*element)?;
            let count = usize::try_from(len.try_to_target_usize(tcx)?).ok()?;
            if count != declared.len() {
                return None;
            }
            vec![*element; count]
        }
        ty::Tuple(fields) => fields.iter().collect(),
        ty::Adt(adt, args) if adt.is_struct() => adt
            .non_enum_variant()
            .fields
            .iter()
            .map(|f| f.ty(tcx, *args).skip_normalization())
            .collect(),
        _ => return None,
    };
    if fields.len() != declared.len() || layout.fields.count() != fields.len() {
        return None;
    }
    let mut offsets = Vec::with_capacity(fields.len());
    for (index, (source_field, declared_field)) in fields.iter().zip(declared).enumerate() {
        primitive_source(*source_field)?;
        if rust_ty_to_trust_ir_ty(tcx, *source_field)
            .ok()?
            .ne(declared_field)
        {
            return None;
        }
        offsets.push(layout.fields.offset(index).bytes());
    }
    Some(PointeeLayout {
        ty: lowered,
        size: layout.size.bytes(),
        align: layout.align.bytes(),
        offsets,
    })
}
