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
fn compile(m: &Module) -> trust_cg_codegen::CompilationResult {
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
    .compile(m)
    .unwrap()
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
            .bound_source_stack_allocations(&output.object_code, &source(43))
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
    let mut changed = frame.clone();
    changed.stack_slots[0].align *= 2;
    assert!(
        changed
            .bound_source_stack_allocations(&output.object_code, &m)
            .is_err()
    );
    let mut changed = frame.clone();
    changed.symbol = "another_function".into();
    assert!(
        changed
            .bound_source_stack_allocations(&output.object_code, &m)
            .is_err()
    );
    let mut changed = frame.clone();
    changed.source_stack_allocations = Err("no actual producer source mapping".into());
    assert!(
        changed
            .bound_source_stack_allocations(&output.object_code, &m)
            .is_err()
    );
}
