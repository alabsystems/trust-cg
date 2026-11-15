// trust-cg-irmid/passes/mod.rs - the mid-end's passes
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The passes. Each one rewrites ONE function and states what it did as a
//! [`PassWitness`]; it trusts nothing about its own correctness, because the
//! manager keeps a rewrite only when `trust_cg_verify::trust_ir_mid_tv`
//! accepts the witness. The analyses here (value typing, the removable table,
//! constant evaluation, allocation sizes) are deliberately the passes' own:
//! the checker derives the same facts independently.

use std::collections::{BTreeSet, HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::PassWitness;
use trust_ir::{Function, Inst, Module, Ty, ValueId};

mod addr_fold;
mod argpromo;
mod bounded_unroll;
mod branch_fold;
mod byaddr;
mod byaddr_reading;
mod byte_copy;
mod const_fold;
mod copy_prop;
mod crc_table;
mod ctp;
mod dce;
mod dead_param;
mod dead_slot;
mod field_access;
mod fill_call;
pub(crate) mod inline;
mod iv_sr;
mod lane_load;
mod licm;
mod loop_cf;
mod loops;
mod mem_call;
// Withheld from every default pipeline (OD-164): its pass runs only in the
// crate's tests.
#[cfg_attr(not(test), allow(dead_code))]
mod mem_cmp;
mod merge;
mod ptr_gep;
pub(crate) mod range;
mod select_branch;
mod simplify;
mod slots;
mod sroa;
mod store_fwd;
mod unroll;

pub(crate) use addr_fold::AddrFoldPass;
pub(crate) use argpromo::ArgPromo;
#[cfg(test)]
pub(crate) use argpromo::refusals as argpromo_refusals;
pub(crate) use bounded_unroll::BoundedUnroll;
pub(crate) use branch_fold::BranchFold;
pub(crate) use byaddr::{BYADDR_NAME, ByAddr};
pub(crate) use byte_copy::ByteCopyPass;
pub(crate) use const_fold::ConstFoldPass;
pub(crate) use copy_prop::CopyProp;
pub(crate) use crc_table::{CRC_TABLE_NAME, CrcTablePass};
pub(crate) use ctp::Ctp;
pub(crate) use dce::Dce;
pub(crate) use dead_param::DeadParamPass;
pub(crate) use dead_slot::DeadSlotRemoval;
pub(crate) use field_access::FieldAccessPass;
pub(crate) use fill_call::{FILL_CALL_NAME, FILL_CALL_WITHHELD};
pub(crate) use inline::{Inline, callee_first_order};
pub(crate) use iv_sr::IvStrength;
pub(crate) use lane_load::LaneLoadPass;
pub(crate) use licm::Licm;
pub(crate) use loop_cf::LoopClosedForm;
pub(crate) use mem_call::MemCallPass;
#[cfg(test)]
pub(crate) use mem_cmp::MemCmpPass;
pub(crate) use mem_cmp::{MEM_CMP_NAME, MEM_CMP_WITHHELD};
pub(crate) use merge::MergeBlocks;
pub(crate) use ptr_gep::PtrGep;
pub(crate) use range::RangeRules;
pub(crate) use select_branch::SelectBranch;
pub(crate) use simplify::{RespellPass, RetypeCopyPass, SimplifyPass};
#[cfg(test)]
pub(crate) use sroa::LIVENESS_VISITS;
pub(crate) use sroa::Sroa;
#[cfg(test)]
pub(crate) use sroa::refusals as sroa_refusals;
pub(crate) use store_fwd::StoreFwd;
pub(crate) use unroll::Unroll;

/// What a pass may read besides the function it rewrites.
pub(crate) struct PassContext<'m> {
    pub module: &'m Module,
    pub pointer_bits: u32,
}

/// One function-local rewrite.
pub(crate) trait MidPass {
    /// Stable name for evidence (`irmid:<name>`).
    fn name(&self) -> &'static str;

    /// The rewritten function and its witness, or `None` when the pass has
    /// nothing to do on `func`.
    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)>;

    /// Whether the manager visits callees before their callers for this pass
    /// (the inliner, which splices each callee's current body), rather than
    /// in module order.
    fn callee_first(&self) -> bool {
        false
    }
}

/// The evidence name of constant-table promotion, the pass
/// [`crate::MidConfig::promote_constant_tables`] withholds.
pub(crate) const CTP_NAME: &str = "ctp";

/// The evidence name of the inliner, the pass [`crate::MidConfig::inline`]
/// withholds.
pub(crate) const INLINE_NAME: &str = "inline";

/// The evidence name of argument promotion, the pass
/// [`crate::MidConfig::arg_promotion`] withholds.
pub(crate) const ARGPROMO_NAME: &str = "argpromo";

/// The passes [`crate::MidConfig::loop_passes`] withholds: the loop passes,
/// block merging, field-access lowering and the select-branch rules, which
/// copy instructions, move them to another block or give a result a new
/// type.
pub(crate) const LOOP_PASS_NAMES: [&str; 8] = [
    loop_cf::LOOP_CF_NAME,
    unroll::UNROLL_NAME,
    bounded_unroll::BOUNDED_UNROLL_NAME,
    licm::LICM_NAME,
    iv_sr::IV_SR_NAME,
    merge::MERGE_NAME,
    field_access::FIELD_ACCESS_NAME,
    select_branch::SELECT_BRANCH_NAME,
];

/// The wasm32 profile's pipeline, in order: the scalar cleanup first (it
/// respells the bridge's sign-reinterpreting copies as `bitcast`s (and its
/// copies of a thin pointer as another pointer type as `ptrtoptr`s), its
/// comparisons of typed pointers as comparisons at `ptr` and its `u32`
/// bulk-memory counts as `usize`s, spells
/// the bridge's field accesses through pointers as the loads and
/// stores they are (and respells the copies again, a pointer field's reads
/// now typed), turns the bridge's pointer chains into the byte-offset
/// `gep`s the memory passes read, folds constant expressions and respells
/// the bridge's integer `bool` constants and its integer constants spelled
/// out of their type's range, turns the C memory library calls whose counts
/// are now constants into bulk-memory instructions, makes byte-by-byte
/// copies `memcopy`s and forwards the stores a copy's frame slot held into
/// its destination, and removes the dead chain
/// arithmetic, so the inliner
/// sizes callees by what they will cost and copies no finding of theirs),
/// the memory cleanup (store forwarding, slot removal, scalar replacement,
/// copy propagation, dead-code elimination: a callee whose only `alloca` is
/// a temporary it promotes is spliced as a frameless body, also into a
/// caller's loop, where a spliced slot may not go),
/// then inlining (callees first; a callee
/// named in `never_inline` stays a call; an array the bridge passes or
/// returns by address bound to the `load` of its bytes), lane-load
/// scalarization of those loads, field-access lowering again (the spliced
/// writes of a lane now read as a scalar), and the cleanup again over the
/// spliced bodies, whose pointer parameters are now the callers' slots; then
/// store forwarding, the removal of slots it left unread, scalar replacement
/// of the slots still read, constant-table promotion of the tables still
/// read through a variable index, copy propagation, by-address cloning (a
/// call passing a pointer for an array parameter that the callee copies
/// into a slot of its own and only reads calls a clone reading the caller's
/// bytes instead; the clone's name carries argument promotion's mark and
/// shares its budget; before argument promotion, which would pass such a
/// parameter's lanes as values into a clone that still copies them into its
/// slot), argument promotion
/// (callees first: a slot whose address escapes only into calls of callees
/// that load and store through it at constant offsets is passed as values
/// to a clone; after the first scalar replacement, so the values it stores
/// are the SSA values the proofs of their definedness read), the
/// pointer-chain rewrite, copy propagation and dead-code elimination again
/// (a clone's copy of a callee's integer address chains now starts at the
/// clone's own allocation, and the chains' dead `ptrtoint`s would keep it in
/// memory), a second scalar
/// replacement (it dissolves those slots and the clones' private copies, and
/// a slot whose stored values were loads of a slot the first one promoted
/// may now store values it can reinterpret), copy propagation, constant
/// folding, the memory-call and byte-copy rewrites again (on the
/// counts inlining and argument promotion made constant, and the copies
/// inlining brought together) and algebraic simplification (scalar replacement's
/// packed pairs
/// read back as their parts, so a slice iterator's bounds are its pointers
/// again, and a slice's end minus its start read as its length), the
/// select-branch rules (an early exit's `switch` on a `select` becomes a
/// branch on its condition, and a `select` under that branch its arm), the
/// range rules (late, where inlining has bound callees' parameters and scalar
/// replacement has turned slot reloads into the values whose definitions the
/// facts are read from), closed-form induction (after the range rules have
/// removed the overflow checks they prove cannot fire, so an accumulator's
/// flag is dead), full unrolling of the constant-trip loops that remain,
/// interval-bounded unrolling of the loops whose trip count an interval
/// bounds, and their cleanup (constant folding of the per-copy induction
/// values, the select-branch rules on the copies' exit tests,
/// simplification, branch folding, address folding of the copies' integer
/// address chains into `gep`s of their slots, dead-code elimination, dead
/// block parameters, block merging, and store forwarding, slot removal and
/// scalar replacement of the arrays the copies now read at constant
/// offsets, and scalar replacement again: a slot whose stored values were
/// reads of a slot the one before promoted, an iterator adapter's state
/// copied out of its constructor's, is promotable only then), the
/// select-branch rules, the range rules and interval-bounded unrolling
/// again with that cleanup (a `Zip`'s state is in values only now, and its
/// index steps through a `select` the rules forward under the loop's
/// branch), constant folding, the select-branch rules and the range rules
/// again, block merging (an
/// unrolled inner loop's last header leaves the enclosing loop's parameters
/// hidden behind its own), the CRC-table rewrite (the unrolled bit-serial
/// CRC step over a byte becomes a table load) and block merging again,
/// loop-invariant code motion (on the loops that
/// remain, with every slot reload already a value), strength reduction of
/// the linear addresses left in them, and a last cleanup of the copies and
/// the dead `gep`s, `alloca`s, compares and constants they leave.
pub(crate) fn wasm32_pipeline(
    never_inline: &BTreeSet<String>,
    no_arg_promotion: &BTreeSet<String>,
) -> Vec<Box<dyn MidPass>> {
    vec![
        Box::new(RetypeCopyPass),
        Box::new(RespellPass),
        Box::new(CopyProp),
        Box::new(FieldAccessPass),
        Box::new(RetypeCopyPass),
        Box::new(PtrGep),
        Box::new(CopyProp),
        Box::new(ConstFoldPass),
        Box::new(MemCallPass::CONSTANT_COUNTS),
        Box::new(ByteCopyPass),
        Box::new(BranchFold),
        Box::new(Dce),
        Box::new(StoreFwd),
        Box::new(DeadSlotRemoval),
        Box::new(Sroa),
        Box::new(CopyProp),
        Box::new(Dce),
        Box::new(Inline::new(never_inline.clone())),
        Box::new(CopyProp),
        Box::new(LaneLoadPass),
        Box::new(FieldAccessPass),
        Box::new(RetypeCopyPass),
        Box::new(PtrGep),
        Box::new(CopyProp),
        Box::new(Dce),
        Box::new(StoreFwd),
        Box::new(DeadSlotRemoval),
        Box::new(Sroa),
        Box::new(Ctp),
        Box::new(CopyProp),
        Box::new(ByAddr::new(no_arg_promotion.clone())),
        Box::new(ArgPromo::new(no_arg_promotion.clone())),
        // Promotion of a typed by-value snapshot introduces scalar lane
        // reads of its original load. Scalarize those reads at the load
        // before slot removal, preserving the snapshot across later writes.
        Box::new(LaneLoadPass),
        Box::new(PtrGep),
        Box::new(CopyProp),
        Box::new(Dce),
        Box::new(Sroa),
        Box::new(CopyProp),
        Box::new(ConstFoldPass),
        Box::new(MemCallPass::CONSTANT_COUNTS),
        Box::new(ByteCopyPass),
        Box::new(SimplifyPass),
        Box::new(CopyProp),
        Box::new(SelectBranch),
        Box::new(RangeRules),
        Box::new(LoopClosedForm),
        Box::new(Unroll),
        Box::new(BoundedUnroll),
        Box::new(ConstFoldPass),
        Box::new(SelectBranch),
        Box::new(SimplifyPass),
        Box::new(CopyProp),
        Box::new(BranchFold),
        Box::new(AddrFoldPass),
        Box::new(CopyProp),
        Box::new(Dce),
        Box::new(DeadParamPass),
        Box::new(Dce),
        Box::new(MergeBlocks),
        Box::new(StoreFwd),
        Box::new(DeadSlotRemoval),
        Box::new(Sroa),
        Box::new(CopyProp),
        Box::new(Sroa),
        Box::new(CopyProp),
        Box::new(SelectBranch),
        Box::new(RangeRules),
        Box::new(BoundedUnroll),
        Box::new(ConstFoldPass),
        Box::new(SelectBranch),
        Box::new(SimplifyPass),
        Box::new(CopyProp),
        Box::new(BranchFold),
        Box::new(AddrFoldPass),
        Box::new(CopyProp),
        Box::new(Dce),
        Box::new(DeadParamPass),
        Box::new(Dce),
        Box::new(MergeBlocks),
        Box::new(StoreFwd),
        Box::new(DeadSlotRemoval),
        Box::new(Sroa),
        Box::new(CopyProp),
        Box::new(ConstFoldPass),
        Box::new(SelectBranch),
        Box::new(RangeRules),
        Box::new(MergeBlocks),
        Box::new(CrcTablePass),
        Box::new(MergeBlocks),
        Box::new(Licm),
        Box::new(IvStrength),
        Box::new(CopyProp),
        Box::new(Dce),
    ]
}

/// The single-result instruction defining each value.
pub(crate) fn sole_defs(func: &Function) -> HashMap<ValueId, &Inst> {
    let mut defs = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let [result] = node.results.as_slice() {
            defs.insert(*result, &node.inst);
        }
    }
    defs
}

/// The element count of `alloca T, count`: 1 without a count, `k` for an
/// integer constant `k >= 1` (the interpreter allocates `size(T) * k`
/// bytes); `None` for any other count.
pub(crate) fn alloca_count(defs: &HashMap<ValueId, &Inst>, count: Option<ValueId>) -> Option<u64> {
    let Some(count) = count else {
        return Some(1);
    };
    match defs.get(&count)? {
        Inst::Const {
            ty,
            value: trust_ir::Constant::Int(k),
        } if ty.is_integer() => u64::try_from(*k).ok().filter(|&k| k >= 1),
        _ => None,
    }
}

/// The pass-side typing: block parameters and the single-result instruction
/// forms whose result type is a field of the instruction; `None` otherwise.
pub(crate) fn value_types(func: &Function) -> HashMap<ValueId, Ty> {
    let mut types = HashMap::new();
    for block in &func.blocks {
        for (value, ty) in &block.params {
            types.insert(*value, ty.clone());
        }
        for node in &block.body {
            let [result] = node.results.as_slice() else {
                continue;
            };
            let ty = match &node.inst {
                Inst::Copy { ty, .. }
                | Inst::Load { ty, .. }
                | Inst::Const { ty, .. }
                | Inst::Select { ty, .. }
                | Inst::Undef { ty }
                | Inst::BinOp { ty, .. }
                | Inst::UnOp { ty, .. } => ty.clone(),
                Inst::Cast { dst_ty, .. } => dst_ty.clone(),
                Inst::ICmp { .. } | Inst::FCmp { .. } => Ty::Bool,
                Inst::Alloca { .. }
                | Inst::GEP { .. }
                | Inst::GlobalAddr { .. }
                | Inst::NullPtr => Ty::Ptr,
                _ => continue,
            };
            types.insert(*result, ty);
        }
    }
    types
}

/// [`value_types`], and an overflow operation's value (its type) and flag
/// (`bool`): the typing the loop copies' substitution checks read (an
/// `enumerate` counter is an `add.overflow`'s value).
pub(crate) fn value_types_with_overflow(func: &Function) -> HashMap<ValueId, Ty> {
    let mut types = value_types(func);
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let (Inst::Overflow { ty, .. }, [value, flag]) = (&node.inst, node.results.as_slice()) {
            types.insert(*value, ty.clone());
            types.insert(*flag, Ty::Bool);
        }
    }
    types
}

/// Drop the debug names of removed values.
pub(crate) fn drop_names(func: &mut Function, removed: &HashSet<ValueId>) {
    if let Some(names) = &mut func.value_names {
        names.retain(|(value, _)| !removed.contains(value));
    }
}

/// Lane `field` of the record type `ty` (a struct, a tuple or an array): its
/// byte offset and type, from trust-ir's layout (a tuple without a declared
/// layout by the interpreter's C-style rule: each element at the next offset
/// its alignment divides). The bridge's field access through a pointer reads
/// or writes exactly these bytes.
pub(crate) fn record_lane(module: &Module, ty: &Ty, field: u32) -> Option<(u64, Ty)> {
    let size_of = |ty: &Ty| module.ty_layout_shape(ty).ok()?.size_bytes();
    match ty {
        Ty::Struct(id) => {
            let lane_ty = module
                .struct_def(*id)?
                .fields
                .get(field as usize)?
                .ty
                .clone();
            let bits = module.struct_field_offset_bits(*id, field).ok()?;
            (bits % 8 == 0).then_some((bits / 8, lane_ty))
        }
        Ty::Tuple(elems) => {
            let lane_ty = elems.get(field as usize)?.clone();
            if let Some(descriptor) = module.tuple_layout_descriptor(ty).ok()? {
                return Some((*descriptor.field_offsets.get(field as usize)?, lane_ty));
            }
            let mut offset = 0u64;
            for (i, elem) in elems.iter().enumerate() {
                let bits = module.ty_layout_shape(elem).ok()?.align_bits?;
                let align = (bits % 8 == 0 && bits > 0).then_some(bits / 8)?;
                offset = offset.div_ceil(align).checked_mul(align)?;
                if i == field as usize {
                    return Some((offset, lane_ty));
                }
                offset = offset.checked_add(size_of(elem)?)?;
            }
            None
        }
        Ty::Array(elem, count) if u64::from(field) < *count => {
            let elem = module.ty(*elem)?.clone();
            let stride = size_of(&elem)?;
            Some((u64::from(field).checked_mul(stride)?, elem))
        }
        _ => None,
    }
}

/// Integer `(bits, signed)` of `ty` at `pointer_bits`.
pub(crate) fn int_shape(ty: &Ty, pointer_bits: u32) -> Option<(u32, bool)> {
    Some(match ty {
        Ty::I8 => (8, true),
        Ty::I16 => (16, true),
        Ty::I32 => (32, true),
        Ty::I64 => (64, true),
        Ty::I128 => (128, true),
        Ty::U8 => (8, false),
        Ty::U16 => (16, false),
        Ty::U32 => (32, false),
        Ty::U64 => (64, false),
        Ty::U128 => (128, false),
        Ty::Isize => (pointer_bits, true),
        Ty::Usize => (pointer_bits, false),
        _ => return None,
    })
}
