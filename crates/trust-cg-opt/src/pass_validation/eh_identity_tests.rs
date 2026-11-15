//! Exact invoke custody participates in both cached and region validation.

use super::{
    ValidationVerdict, function_digest,
    region::{same_eh_metadata, validate_regions},
};
use trust_cg_ir::function::{EhCallSiteBindings, EhInvokeBinding};
use trust_cg_ir::regs::X0;
use trust_cg_ir::{
    AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand, Signature,
};

fn function() -> MachFunction {
    let mut function = MachFunction::new("eh_identity".into(), Signature::new(vec![], vec![]));
    function.eh_metadata.call_site_bindings = EhCallSiteBindings::ExactInstructions(vec![
        EhInvokeBinding {
            call_inst: InstId(7),
            call_block: BlockId(2),
            landing_pad_block: BlockId(3),
        },
        EhInvokeBinding {
            call_inst: InstId(8),
            call_block: BlockId(4),
            landing_pad_block: BlockId(5),
        },
    ]);
    function
}

#[test]
fn identical_exact_call_custody_keeps_digest_and_metadata_equality() {
    let before = function();
    let after = before.clone();
    assert_eq!(function_digest(&before), function_digest(&after));
    assert!(same_eh_metadata(&before, &after));
}

#[test]
fn mode_and_each_exact_call_identity_field_invalidate_both_reuse_paths() {
    let before = function();
    for change in 0..7 {
        let mut after = before.clone();
        let EhCallSiteBindings::ExactInstructions(bindings) =
            &mut after.eh_metadata.call_site_bindings
        else {
            unreachable!()
        };
        match change {
            0 => after.eh_metadata.call_site_bindings = EhCallSiteBindings::LegacyBlocks,
            1 => bindings.clear(),
            2 => bindings[0].call_inst = InstId(9),
            3 => bindings[0].call_block = BlockId(6),
            4 => bindings[0].landing_pad_block = BlockId(7),
            5 => bindings.swap(0, 1),
            6 => bindings.push(bindings[0]),
            _ => unreachable!(),
        }
        assert_ne!(
            function_digest(&before),
            function_digest(&after),
            "change {change}"
        );
        assert!(!same_eh_metadata(&before, &after), "change {change}");
    }
}

#[test]
fn exact_empty_and_legacy_empty_are_distinct_validation_subjects() {
    let before = MachFunction::new("empty".into(), Signature::new(vec![], vec![]));
    let mut after = before.clone();
    after.eh_metadata.call_site_bindings = EhCallSiteBindings::ExactInstructions(vec![]);
    assert_ne!(function_digest(&before), function_digest(&after));
    assert!(!same_eh_metadata(&before, &after));
}

fn indirect_call(cannot_unwind: bool) -> MachFunction {
    let mut function = MachFunction::new(
        "call_unwind_identity".into(),
        Signature::new(vec![], vec![]),
    );
    let mut call = MachInst::new(AArch64Opcode::Blr, vec![MachOperand::PReg(X0)]);
    if cannot_unwind {
        call.flags.insert(InstFlags::CANNOT_UNWIND_CALL);
    }
    let call = function.push_inst(call);
    function.append_inst(function.entry, call);
    let ret = function.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    function.append_inst(function.entry, ret);
    function
}

#[test]
fn unchanged_call_unwind_mark_keeps_region_validation_and_identity() {
    for cannot_unwind in [false, true] {
        let before = indirect_call(cannot_unwind);
        let after = before.clone();
        assert_eq!(function_digest(&before), function_digest(&after));
        assert_eq!(
            validate_regions(&before, &after).verdict,
            ValidationVerdict::Validated
        );
    }
}

#[test]
fn changing_call_unwind_mark_invalidates_region_validation_in_both_directions() {
    for cannot_unwind in [false, true] {
        let before = indirect_call(cannot_unwind);
        let mut after = before.clone();
        let call = after.block(after.entry).insts[0];
        if cannot_unwind {
            after
                .inst_mut(call)
                .flags
                .remove(InstFlags::CANNOT_UNWIND_CALL);
        } else {
            after
                .inst_mut(call)
                .flags
                .insert(InstFlags::CANNOT_UNWIND_CALL);
        }
        assert_ne!(function_digest(&before), function_digest(&after));
        let verdict = validate_regions(&before, &after).verdict;
        assert!(
            matches!(verdict, ValidationVerdict::Unproved(ref reason) if reason.contains("differs")),
            "cannot_unwind={cannot_unwind}: {verdict:?}"
        );
    }
}

#[test]
fn encoding_only_call_mark_remains_outside_the_semantic_effect_key() {
    let before = indirect_call(true);
    let mut after = before.clone();
    let call = after.block(after.entry).insts[0];
    after
        .inst_mut(call)
        .flags
        .insert(InstFlags::PROOF_REORDERABLE);
    assert_ne!(function_digest(&before), function_digest(&after));
    assert_eq!(
        validate_regions(&before, &after).verdict,
        ValidationVerdict::Validated
    );
}
