// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Artifact metadata retains actual static-frame observations. Name-only and
//! replay metadata cannot reconstruct one or grant stack/proof authority.

use super::*;

#[test]
fn quality_metadata_preserves_static_dynamic_and_red_zone_frame_reports() {
    for report in [
        crate::StaticStackFrameReport {
            static_frame_bytes: 0,
            has_dynamic_allocation: false,
            uses_red_zone: false,
        },
        crate::StaticStackFrameReport {
            static_frame_bytes: 64,
            has_dynamic_allocation: false,
            uses_red_zone: false,
        },
        crate::StaticStackFrameReport {
            static_frame_bytes: 96,
            has_dynamic_allocation: true,
            uses_red_zone: false,
        },
        crate::StaticStackFrameReport {
            static_frame_bytes: 128,
            has_dynamic_allocation: false,
            uses_red_zone: true,
        },
    ] {
        let metrics = FunctionQualityMetrics {
            name: "observed_frame".to_owned(),
            code_size_bytes: 64,
            instruction_count: 16,
            spill_slot_count: 2,
            branch_count: 3,
            static_stack_frame: Some(report),
            ..Default::default()
        };
        let metadata = FunctionArtifactMetadata::from_quality_metrics(&metrics);

        assert_eq!(metadata.static_stack_frame, metrics.static_stack_frame);
        assert!(metadata.static_stack_frame.is_some());
        assert_eq!(metadata.name, metrics.name);
        assert_eq!(metadata.code_size_bytes, None);
        assert_eq!(metadata.instruction_count, Some(16));
        assert_eq!(metadata.spill_slot_count, Some(2));
        assert_eq!(metadata.branch_count, Some(3));
    }
}

#[test]
fn quality_metadata_keeps_unreported_static_stack_frame_missing() {
    let metrics = FunctionQualityMetrics {
        name: "unreported_frame".to_owned(),
        ..Default::default()
    };
    assert!(metrics.static_stack_frame.is_none());

    let metadata = FunctionArtifactMetadata::from_quality_metrics(&metrics);
    assert_eq!(metadata.name, "unreported_frame");
    assert!(metadata.static_stack_frame.is_none());
}

#[test]
fn name_only_metadata_does_not_invent_static_stack_frame() {
    let metadata = FunctionArtifactMetadata::from_trust_ir_name("name_only");
    assert_eq!(metadata.name, "name_only");
    assert!(metadata.static_stack_frame.is_none());
    assert!(metadata.code_size_bytes.is_none());
    assert!(metadata.instruction_count.is_none());
    assert!(metadata.spill_slot_count.is_none());
    assert!(metadata.branch_count.is_none());
}

#[test]
fn executable_replay_metadata_keeps_static_stack_frame_missing() {
    let replay =
        JitReplayReportMetadata::from_symbol_entries([("second", 16, 8), ("first", 0, 16)]);
    let functions = functions_from_executable_replay_metadata(&replay);

    assert_eq!(functions.len(), 2);
    assert_eq!(functions[0].name, "first");
    assert_eq!(functions[0].code_size_bytes, Some(16));
    assert_eq!(functions[1].name, "second");
    assert_eq!(functions[1].code_size_bytes, Some(8));
    for metadata in functions {
        assert!(metadata.static_stack_frame.is_none());
        assert!(metadata.instruction_count.is_none());
        assert!(metadata.spill_slot_count.is_none());
        assert!(metadata.branch_count.is_none());
    }
}

#[cfg(target_arch = "aarch64")]
#[test]
fn actual_aarch64_jit_report_survives_common_artifact_payload() {
    let module = trust_ir::parser::parse_module(
        r#"module "stack_artifact"

functy.0 = (i64) -> (i64)

fn @frame_identity(functy.0) {
bb0(%0: i64):
    ret %0
}
"#,
    )
    .expect("canonical identity module parses");
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "whole identity module is valid: {errors:?}"
    );
    let result = Compiler::new(CompilerConfig::jit_fast(Target::Aarch64))
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("actual AArch64 identity compilation succeeds");
    let metrics = result
        .per_function_metrics
        .iter()
        .find(|metrics| metrics.name == "frame_identity")
        .expect("actual identity function metrics");
    let report = metrics
        .static_stack_frame
        .expect("actual preparation reports its static frame");
    assert!(metrics.stack_limit.is_none());
    assert!(result.stack_limits.is_none());
    let symbol_offset = result
        .buffer
        .symbol_offsets()
        .get("frame_identity")
        .copied()
        .expect("actual identity symbol");
    let allocated_size = result.buffer.allocated_size();

    let payload = executable_payload_from_result(result);
    let metadata = payload
        .functions
        .iter()
        .find(|metadata| metadata.name == "frame_identity")
        .expect("common artifact retains identity metadata");
    assert_eq!(metadata.static_stack_frame, Some(report));
    assert_eq!(payload.buffer.allocated_size(), allocated_size);
    assert_eq!(
        payload
            .buffer
            .symbol_offsets()
            .get("frame_identity")
            .copied(),
        Some(symbol_offset)
    );

    type Identity = extern "C" fn(i64) -> i64;
    // SAFETY: the validated function signature is (i64) -> i64, and the
    // payload retains the executable allocation for the entire typed call.
    let identity = unsafe { payload.buffer.get_fn_bound::<Identity>("frame_identity") }
        .expect("common artifact retains the callable identity owner");
    assert_eq!(identity.as_ref()(239), 239);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
#[cfg(target_arch = "aarch64")]
fn permit_unlicensed() -> crate::CodegenLicensePolicy {
    crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
}
