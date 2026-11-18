// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Original writer producer custody, not target semantics or independent proof.
//! Keep strict arena admission unchanged; test the actual producer's repair.

use super::*;
use sha2::{Digest, Sha256};
use trust_cg_codegen::CoreHostJitTarget;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups};

fn original_capture() -> serde_json::Value {
    serde_json::from_str(include_str!(
        "../tests/fixtures/ty_original_scalar_action.json"
    ))
    .unwrap()
}

fn assert_original_module_image(restored: &trust_ir::Module, capture: &serde_json::Value) {
    assert!(
        restored.drop_glue.is_empty(),
        "original capture has no drop glue"
    );
    assert!(
        restored.closure_layouts.is_empty(),
        "original capture has no closure layouts"
    );
    // The immutable pre-v58 JSON omitted both empty tables; the current
    // serializer emits them. Add ONLY these empty expected fields. Keep
    // the original capture's omission precondition for each table, too.
    // Do not round-trip the
    // expected JSON through Module or drop fields from the actual image:
    // either would conceal unrelated schema/source changes.
    let mut expected = capture["module"].clone();
    for table in ["drop_glue", "closure_layouts"] {
        assert!(
            expected
                .as_object_mut()
                .unwrap()
                .insert(table.to_owned(), serde_json::Value::Array(vec![]))
                .is_none(),
            "legacy capture must omit {table}"
        );
    }
    assert_eq!(
        serde_json::to_value(restored).unwrap(),
        expected,
        "restored original module differs from immutable capture"
    );
}

fn original() -> trust_ir::Module {
    let capture = original_capture();
    let mut module: trust_ir::Module = serde_json::from_value(capture["module"].clone()).unwrap();
    assert!(module.target_info.is_none());
    assert_eq!(module.functions.len(), 10);
    assert_eq!(module.functions[3].id.index(), 60_002);
    let host = CoreHostJitTarget::detect().unwrap();
    module.target_info = Some(host.trust_ir_target_info().clone());
    let mut restored = module.clone();
    restored.target_info = None;
    assert_original_module_image(&restored, &capture);
    module
}

#[test]
fn legacy_empty_schema_tables_are_the_only_original_image_compatibility() {
    let capture = original_capture();
    let module: trust_ir::Module = serde_json::from_value(capture["module"].clone()).unwrap();
    assert_original_module_image(&module, &capture);
}

#[test]
#[should_panic(expected = "original capture has no drop glue")]
fn original_image_refuses_nonempty_actual_drop_glue() {
    let capture = original_capture();
    let mut module: trust_ir::Module = serde_json::from_value(capture["module"].clone()).unwrap();
    module.drop_glue.push(trust_ir::DropGlueEntry {
        glue: trust_ir::FuncId::new(60_002),
        ty: trust_ir::Ty::I64,
    });
    assert_original_module_image(&module, &capture);
}

#[test]
#[should_panic(expected = "legacy capture must omit drop_glue")]
fn original_image_never_overwrites_an_authored_drop_glue_field() {
    let mut capture = original_capture();
    let module: trust_ir::Module = serde_json::from_value(capture["module"].clone()).unwrap();
    capture["module"]["drop_glue"] = serde_json::json!([{"glue": 60_002, "ty": "I64"}]);
    assert_original_module_image(&module, &capture);
}

#[test]
#[should_panic(expected = "legacy capture must omit closure_layouts")]
fn original_image_never_overwrites_an_authored_closure_layout_field() {
    let mut capture = original_capture();
    let module: trust_ir::Module = serde_json::from_value(capture["module"].clone()).unwrap();
    capture["module"]["closure_layouts"] = serde_json::json!([{"unknown": true}]);
    assert_original_module_image(&module, &capture);
}

#[test]
#[should_panic(expected = "original capture has no closure layouts")]
fn original_image_refuses_nonempty_actual_closure_layouts() {
    let capture = original_capture();
    let mut module: trust_ir::Module = serde_json::from_value(capture["module"].clone()).unwrap();
    module
        .closure_layouts
        .push(trust_ir::ClosureLayoutDescriptor {
            closure: trust_ir::ClosureTyId::new(0),
            size: 0,
            align: 1,
            capture_offsets: vec![],
            origin: None,
        });
    assert_original_module_image(&module, &capture);
}

#[test]
#[should_panic(expected = "restored original module differs from immutable capture")]
fn original_image_still_refuses_unrelated_actual_source_mutation() {
    let capture = original_capture();
    let mut module: trust_ir::Module = serde_json::from_value(capture["module"].clone()).unwrap();
    module.name.push_str("_changed");
    assert_original_module_image(&module, &capture);
}

#[test]
#[should_panic(expected = "restored original module differs from immutable capture")]
fn original_image_preserves_unknown_expected_fields_in_the_exact_comparison() {
    let mut capture = original_capture();
    let module: trust_ir::Module = serde_json::from_value(capture["module"].clone()).unwrap();
    capture["module"]["unexpected_serializer_field"] = serde_json::Value::Bool(true);
    assert_original_module_image(&module, &capture);
}

#[test]
fn actual_original_writer_ownership_passes_without_relaxation_and_keeps_exact_bytes() {
    let module = original();
    let source = &module.functions[3];
    assert_eq!(source.blocks.len(), 16);
    assert_eq!(
        source.blocks.iter().map(|b| b.body.len()).sum::<usize>(),
        117
    );
    let (lir, context) = trust_cg_lower::translate_function_with_license(
        source,
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    for (level, prior_bytes_sha) in [
        (
            OptLevel::O0,
            "c7eb1d7a19852725e814e91e7034645494e6dd0ed45835883cbc562de7863ffe",
        ),
        (
            OptLevel::O1,
            "40123fc376d61d244ee3684cf6698ae81e9d0fda28be036c4caadfddd4cfb3b1",
        ),
        (
            OptLevel::O2,
            "8786f06c1ecc2d696678ec5e6afe350f4c712e8fcf123d0506469ff7a613a8f9",
        ),
        (
            OptLevel::O3,
            "ebeb52afd6a942ad91f62c3d1f65fe8187cae85dd4a32b87a678d064cb39a1f4",
        ),
    ] {
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: level,
            verify: false,
            ..PipelineConfig::for_target("aarch64-apple-darwin")
        });
        let (machine, _) = pipeline
            .prepare_function_with_metrics_and_trust_ir_module(
                &lir,
                Some(&context),
                &module,
                source,
            )
            .unwrap();
        let observed = layout(&machine)
            .unwrap_or_else(|error| panic!("actual {level:?} strict arena custody: {error}"));
        let (bytes, fixups) = encode_function_with_fixups(&machine).unwrap();
        assert!(fixups.is_empty());
        assert_eq!(
            format!("{:x}", Sha256::digest(&bytes)),
            prior_bytes_sha,
            "retirement must not change ANY linked native byte in this checkpoint"
        );
        if matches!(level, OptLevel::O2 | OptLevel::O3) {
            for id in [107, 110, 124] {
                let id = InstId(id);
                assert!(!observed.linked.contains(&id));
                assert!(machine.blocks.iter().all(|b| !b.insts.contains(&id)));
                let retired = machine.inst(id);
                assert_eq!(retired.opcode, M::Nop);
                assert!(retired.operands.is_empty());
                assert_eq!(retired.flags, M::Nop.default_flags());
                assert!(machine.inst_lowering_provenance(id).is_source_attributed());
            }
        }
        println!(
            "TY_SCALAR_WRITER_PRODUCER_CUSTODY level={level:?} linked={} strict_arena=true original_bytes_sha256={prior_bytes_sha} target_semantics=false replay=false native_credit=false",
            observed.linked.len()
        );
    }
}

#[test]
fn actual_writer_unowned_real_payload_and_duplicate_owners_still_refuse() {
    let module = original();
    let source = &module.functions[3];
    let (lir, context) = trust_cg_lower::translate_function_with_license(
        source,
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        verify: false,
        ..PipelineConfig::for_target("aarch64-apple-darwin")
    });
    let (machine, _) = pipeline
        .prepare_function_with_metrics_and_trust_ir_module(&lir, Some(&context), &module, source)
        .unwrap();
    let original_layout = layout(&machine).unwrap();
    for opcode in [M::LdrRI, M::MulRR] {
        let live = original_layout
            .linked
            .iter()
            .copied()
            .find(|id| machine.inst(*id).opcode == opcode)
            .unwrap();
        let mut mutant = machine.clone();
        mutant.insts[107] = machine.inst(live).clone();
        assert!(
            layout(&mutant).is_err(),
            "unowned real {opcode:?} must not become an inert tombstone"
        );
    }
    let mut mutant = machine.clone();
    let entry = mutant.entry;
    let duplicate = mutant.block(entry).insts[0];
    mutant.block_mut(entry).insts.push(duplicate);
    assert!(
        layout(&mutant).is_err(),
        "duplicate linked ownership remains invalid"
    );
}
