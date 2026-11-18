// Copyright 2026 Andrew Yates | Apache-2.0
//! Actual ordinary source -> LIR -> object allocation-input custody.
//! Explicit unverified compilation, certificates off; no memory proof credit.
use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
use trust_cg_lower::{CodegenLicensePolicy, UnlicensedBodyPolicy};
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

fn source(value: i128) -> Module {
    let mut m = ModuleBuilder::new("source_allocation_custody");
    let sig = m.add_func_type(vec![], vec![Ty::I64]);
    let mut f = m.function("two_allocations", sig);
    let b = f.create_block();
    f.switch_to_block(b);
    let a = f.alloca(Ty::I64);
    let c = f.alloca(Ty::I64);
    let n = f.iconst(Ty::I64, value);
    f.store(Ty::I64, a, n);
    f.store(Ty::I64, c, n);
    let x = f.load(Ty::I64, a);
    let y = f.load(Ty::I64, c);
    let result = f.add(Ty::I64, x, y);
    f.ret(vec![result]);
    f.build();
    m.build().unwrap()
}
fn compiler() -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            parallel: false,
            emit_proofs: false,
            aarch64_force_frame_pointers: true,
            ..Default::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").unwrap(),
    )
    .with_codegen_license(
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
}
fn compile(m: &Module) -> trust_cg_codegen::CompilationResult {
    compiler().compile(m).unwrap()
}

#[test]
fn actual_object_retains_both_same_size_source_allocations() {
    let m = source(42);
    let output = compile(&m);
    assert!(output.proofs.is_none());
    let [frame] = output.aarch64_frame_inputs.as_slice() else {
        panic!("complete population")
    };
    let input = frame
        .bound_source_stack_allocations(&output.object_code, &m)
        .unwrap();
    let [a, b] = input.records() else {
        panic!("complete Alloca census")
    };
    assert_ne!(a.source_result(), b.source_result());
    assert_ne!(a.stack_slot(), b.stack_slot());
    assert_eq!(a.geometry(), b.geometry());
    assert_eq!(a.source_type(), &Ty::I64);
    assert!(serde_json::to_value(input).unwrap().is_object());
    let request = trust_cg_codegen::aot_frame_inputs::AotSourceAllocationRequest::new(
        &output.object_code,
        &m,
    )
    .unwrap();
    assert_eq!(
        frame.bound_source_stack_allocations_for(&request).unwrap(),
        input
    );
    let original_request = frame
        .source_allocation_request_from_original(&output.object_code, &m)
        .unwrap();
    assert!(std::ptr::eq(original_request.adapter_input(), &m));
    assert_eq!(
        frame
            .bound_source_stack_allocations_for(&original_request)
            .unwrap(),
        input
    );
}

#[test]
fn valid_foreign_object_and_changed_source_or_layout_cannot_reuse_inputs() {
    let m = source(42);
    let output = compile(&m);
    let frame = &output.aarch64_frame_inputs[0];
    let foreign = compile(&source(43));
    assert_ne!(output.object_code, foreign.object_code);
    assert!(
        frame
            .bound_source_stack_allocations(&foreign.object_code, &m)
            .is_err()
    );
    assert!(
        frame
            .source_allocation_request_from_original(&foreign.object_code, &m)
            .is_err()
    );
    assert!(
        frame
            .bound_source_stack_allocations(&output.object_code, &source(43))
            .is_err()
    );
    assert!(
        frame
            .source_allocation_request_from_original(&output.object_code, &source(43))
            .is_err()
    );
    let mut changed = frame.clone();
    changed.layout.as_mut().unwrap().total_frame_size += 16;
    changed.layout.as_mut().unwrap().spill_area_size += 16;
    assert!(
        changed
            .bound_source_stack_allocations(&output.object_code, &m)
            .is_err()
    );
    assert!(
        changed
            .source_allocation_request_from_original(&output.object_code, &m)
            .is_err()
    );
    let mut changed = frame.clone();
    changed.stack_slots[0].align *= 2;
    assert!(
        changed
            .bound_source_stack_allocations(&output.object_code, &m)
            .is_err()
    );
    assert!(
        changed
            .source_allocation_request_from_original(&output.object_code, &m)
            .is_err()
    );
    let mut changed = frame.clone();
    changed.symbol = "another_function".into();
    assert!(
        changed
            .bound_source_stack_allocations(&output.object_code, &m)
            .is_err()
    );
    assert!(
        changed
            .source_allocation_request_from_original(&output.object_code, &m)
            .is_err()
    );
    let mut changed = frame.clone();
    changed.source_stack_allocations = Err("no actual producer source mapping".into());
    assert!(
        changed
            .bound_source_stack_allocations(&output.object_code, &m)
            .is_err()
    );
    assert!(
        changed
            .source_allocation_request_from_original(&output.object_code, &m)
            .is_err()
    );
}

#[test]
fn actual_legalized_input_remains_distinct_from_original_and_survives_result_clone() {
    use trust_cg_codegen::dialect_legalization::{
        DialectGrammar, DialectLegalizationRegistry, DialectRegistration, LegalizationEvidence,
        TypeRule,
    };
    let mut original = source(42);
    let nominal = Ty::Dialect(Box::new(trust_ir::DialectTy::new(
        "allocation_test",
        "word",
        1,
    )));
    original.types.push(nominal.clone());
    let mut registrations = DialectLegalizationRegistry::default_registrations();
    registrations.push(DialectRegistration {
        namespace: "allocation_test".into(),
        version: 1,
        owner: "ordinary AOT allocation-input transport control".into(),
        grammar: DialectGrammar::Exact(Vec::new()),
        ops: Vec::new(),
        types: ["word", "other_word"]
            .into_iter()
            .map(|name| TypeRule {
                name: name.into(),
                version: 1,
                carrier: Ty::I64,
                rule: format!("allocation_test.{name}/i64"),
                evidence: LegalizationEvidence::CheckedTransportSubstitution,
            })
            .collect(),
    });
    let registry = DialectLegalizationRegistry::new(registrations).unwrap();
    let output = compiler()
        .with_dialect_legalization_registry(registry.clone())
        .compile(&original)
        .unwrap();
    assert!(output.proofs.is_none());
    assert!(output.dialect_legalization.is_some());
    let retained = output.clone();
    drop(output);
    let frame = &retained.aarch64_frame_inputs[0];
    assert!(
        frame
            .bound_source_stack_allocations(&retained.object_code, &original)
            .is_err()
    );
    let request = frame
        .source_allocation_request_from_original(&retained.object_code, &original)
        .unwrap();
    assert!(!std::ptr::eq(request.adapter_input(), &original));
    assert_eq!(original.types.last(), Some(&nominal));
    assert_eq!(request.adapter_input().types.last(), Some(&Ty::I64));
    assert_eq!(
        request.original_input_digest(),
        Some(original.stable_digest_under(trust_ir::imports::IdentityScheme::V3))
    );
    assert_eq!(
        frame
            .bound_source_stack_allocations_for(&request)
            .unwrap()
            .records()
            .len(),
        2
    );

    // A prepared endpoint is not an interchangeable original request, even
    // when it emits the same object. No preparation-semantic proof is minted.
    assert!(
        frame
            .source_allocation_request_from_original(&retained.object_code, request.adapter_input())
            .is_err()
    );
    let mut changed_prepared = request.adapter_input().clone();
    changed_prepared.functions[0].blocks[0].body.reverse();
    let changed = trust_cg_codegen::aot_frame_inputs::AotSourceAllocationRequest::new(
        &retained.object_code,
        &changed_prepared,
    )
    .unwrap();
    assert!(frame.bound_source_stack_allocations_for(&changed).is_err());

    // These distinct originals really compile to the same prepared module
    // and bytes. The original-bound batch must not cross between them.
    let mut other_original = original.clone();
    *other_original.types.last_mut().unwrap() = Ty::Dialect(Box::new(trust_ir::DialectTy::new(
        "allocation_test",
        "other_word",
        1,
    )));
    let other = compiler()
        .with_dialect_legalization_registry(registry)
        .compile(&other_original)
        .unwrap();
    assert_eq!(other.object_code, retained.object_code);
    assert!(
        other.aarch64_frame_inputs[0]
            .bound_source_stack_allocations_for(&request)
            .is_err()
    );
    let prepared_only = trust_cg_codegen::aot_frame_inputs::AotSourceAllocationRequest::new(
        &retained.object_code,
        request.adapter_input(),
    )
    .unwrap();
    assert_eq!(prepared_only.original_input_digest(), None);
    assert!(
        other.aarch64_frame_inputs[0]
            .bound_source_stack_allocations_for(&prepared_only)
            .is_ok()
    );
    let mut changed_original = original.clone();
    changed_original.types.push(Ty::U8);
    assert!(
        frame
            .source_allocation_request_from_original(&retained.object_code, &changed_original)
            .is_err()
    );
}
