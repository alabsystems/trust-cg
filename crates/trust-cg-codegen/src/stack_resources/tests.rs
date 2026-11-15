// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Layout-only observations are not frame-depth or stack-limit authority.

use crate::frame::{try_compute_frame_layout, try_compute_frame_layout_dynamic};
use crate::{FunctionQualityMetrics, PreparationMetrics};
use trust_cg_ir::aarch64_regs::X0;
use trust_cg_ir::function::{Signature, StackSlot, StackSlotSizeSource};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, SpecialReg};
use trust_cg_verify::aarch64_stack_limit::{StackLimitViolationKind, frame_depth};

fn function(name: &str, instructions: Vec<MachInst>) -> MachFunction {
    let mut function = MachFunction::new(name.to_owned(), Signature::new(vec![], vec![]));
    for instruction in instructions {
        let id = function.push_inst(instruction);
        function.append_inst(function.entry, id);
    }
    function
}

fn ret() -> MachInst {
    MachInst::new(AArch64Opcode::Ret, vec![])
}

#[test]
fn static_stack_frame_unknown_is_distinct_from_real_zero_frame() {
    assert!(PreparationMetrics::default().static_stack_frame().is_none());
    assert!(
        FunctionQualityMetrics::default()
            .static_stack_frame
            .is_none()
    );
    let function = function("zero_frame", vec![ret()]);
    let layout = try_compute_frame_layout(&function, 0, true).unwrap();
    assert_eq!(layout.total_frame_size, 0);
    let metrics = PreparationMetrics {
        frame_layout: Some(layout),
        ..PreparationMetrics::default()
    };
    let report = metrics.static_stack_frame().unwrap();
    assert_eq!(report.static_frame_bytes, 0);
    assert!(!report.has_dynamic_allocation);
    assert!(report.uses_red_zone);
    assert!(metrics.stack_limit_certificate.is_none());
}

#[test]
fn static_stack_frame_retains_real_fixed_layout_without_u10() {
    let mut function = function("fixed_frame", vec![ret()]);
    function.alloc_stack_slot(StackSlot::new(64, 16));
    let layout = try_compute_frame_layout(&function, 32, false).unwrap();
    assert!(layout.total_frame_size >= 64);
    let bytes = layout.total_frame_size;
    let metrics = PreparationMetrics {
        frame_layout: Some(layout),
        ..PreparationMetrics::default()
    };
    for _ in 0..100 {
        let report = metrics.static_stack_frame().unwrap();
        assert_eq!(report.static_frame_bytes, bytes);
        assert!(!report.has_dynamic_allocation);
        assert!(!report.uses_red_zone);
    }
    assert!(function.stack_limit.is_none());
    assert!(metrics.stack_limit_certificate.is_none());
}

#[test]
fn static_stack_frame_marks_real_runtime_slot_without_inventing_total() {
    let mut function = function("runtime_frame", vec![ret()]);
    function.alloc_stack_slot(StackSlot::new_dynamic(StackSlotSizeSource::Unknown, 16));
    let layout = try_compute_frame_layout_dynamic(&function, 0, true).unwrap();
    assert!(layout.has_dynamic_alloc);
    let static_bytes = layout.total_frame_size;
    let metrics = PreparationMetrics {
        frame_layout: Some(layout),
        ..PreparationMetrics::default()
    };
    let report = metrics.static_stack_frame().unwrap();
    assert_eq!(report.static_frame_bytes, static_bytes);
    assert!(report.has_dynamic_allocation);
    assert!(!report.uses_red_zone);
    assert!(metrics.stack_limit_certificate.is_none());
}

#[test]
fn static_stack_frame_observation_does_not_require_or_claim_cfg_depth_model() {
    let function = function(
        "unknown_body_stack",
        vec![
            MachInst::new(
                AArch64Opcode::SubRR,
                vec![
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::PReg(X0),
                ],
            ),
            ret(),
        ],
    );
    // The actual independent model cannot bound this SP write. Observing the
    // static layout still succeeds: it is deliberately NOT a final-depth bound.
    assert_eq!(
        frame_depth(&function).unwrap_err().kind,
        StackLimitViolationKind::FrameDepth
    );
    let before = format!("{function:?}");
    let layout = try_compute_frame_layout(&function, 0, false).unwrap();
    let bytes = layout.total_frame_size;
    let metrics = PreparationMetrics {
        frame_layout: Some(layout),
        ..PreparationMetrics::default()
    };
    assert_eq!(
        metrics.static_stack_frame().unwrap().static_frame_bytes,
        bytes
    );
    assert_eq!(format!("{function:?}"), before);
    assert!(metrics.stack_limit_certificate.is_none());
}
