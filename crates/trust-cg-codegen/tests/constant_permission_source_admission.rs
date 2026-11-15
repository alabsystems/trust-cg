// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Named source-contract findings must survive native and WASM admission.
//! These are ordinary consumer controls, not certificates or native executions.

use std::collections::HashMap;
use trust_cg_codegen::wasm;
use trust_cg_lower::adapter::{
    AdapterError, prepare_module_for_lir, translate_function, translate_function_with_license,
    translate_function_with_names, validate_codegen_prerequisites,
};
use trust_cg_lower::{CodegenLicensePolicy, GuardCarrierArch, translate_module_for_arch};
use trust_ir::{
    Constant, Endianness, Global, Inst, Linkage, Module, Producer, StructPassingPolicy, TargetInfo,
    Ty, Visibility,
};
use trust_ir_build::{ModuleBuilder, ValidationError};

fn retarget(module: &mut Module, wasm32: bool) {
    module.target_info = Some(if wasm32 {
        wasm::wasm32_target_info()
    } else {
        TargetInfo {
            triple: "aarch64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        }
    });
}

fn constant_source(ty: Ty, value: Constant, wasm32: bool) -> Module {
    let mut builder = ModuleBuilder::new("constant_permission_source_admission");
    let signature = builder.add_func_type(vec![], vec![ty.clone()]);
    let mut function = builder.function("value", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let result = function.const_value(ty, value);
    function.ret(vec![result]);
    function.build();
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    retarget(&mut module, wasm32);
    module
}

fn constant_verdict(module: &Module) -> String {
    let findings = trust_ir_build::validate_module(module);
    let mismatches: Vec<_> = findings
        .iter()
        .filter(|error| matches!(error, ValidationError::ConstTypeMismatch { .. }))
        .collect();
    assert_eq!(
        mismatches.len(),
        1,
        "one genuine malformed constant: {findings:?}"
    );
    mismatches[0].to_string()
}

fn native_refusal(error: AdapterError, expected: &str) {
    match error {
        AdapterError::TrustIrAdmissionRefused { error } => assert_eq!(error, expected),
        other => panic!("the shared source-contract verdict must refuse, got {other}"),
    }
}

fn assert_native_refused(module: &Module, expected: &str) {
    let before = module.clone();
    native_refusal(
        validate_codegen_prerequisites(module).unwrap_err(),
        expected,
    );
    native_refusal(
        translate_function(&module.functions[0], module).unwrap_err(),
        expected,
    );
    native_refusal(
        translate_function_with_license(
            &module.functions[0],
            module,
            &CodegenLicensePolicy::default(),
        )
        .unwrap_err(),
        expected,
    );
    native_refusal(
        translate_function_with_names(&module.functions[0], module, &HashMap::new()).unwrap_err(),
        expected,
    );
    native_refusal(
        translate_module_for_arch(module, GuardCarrierArch::AArch64).unwrap_err(),
        expected,
    );
    native_refusal(
        prepare_module_for_lir(module, GuardCarrierArch::AArch64).unwrap_err(),
        expected,
    );
    assert_eq!(*module, before);
}

fn direct_wasm(
    function: &trust_ir::Function,
    module: &Module,
) -> Result<u32, wasm::WasmLowerError> {
    wasm::lower_function(
        &mut wasm::WasmModule::new(),
        function,
        module,
        wasm::WasmFunctionEnv::empty(),
    )
}

/// [`direct_wasm`] stating Permit, for the sources that must lower.
fn permitted_direct_wasm(
    function: &trust_ir::Function,
    module: &Module,
) -> Result<u32, wasm::WasmLowerError> {
    wasm::lower_function_with_license(
        &mut wasm::WasmModule::new(),
        function,
        module,
        wasm::WasmFunctionEnv::empty(),
        &permit_unlicensed(),
    )
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Every source that must LOWER states `Permit`
/// explicitly; the refusals stay on the default entries, whose shared
/// source-contract verdict runs before the license.
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

fn wasm_refusal(error: wasm::WasmLowerError, expected: &str) {
    match error {
        wasm::WasmLowerError::CodegenAdmission(error) => assert_eq!(
            error,
            AdapterError::TrustIrAdmissionRefused {
                error: expected.into()
            }
            .to_string(),
        ),
        other => panic!("the shared source-contract verdict must refuse, got {other}"),
    }
}

fn assert_wasm_refused(module: &Module, expected: &str) {
    let before = module.clone();
    wasm_refusal(wasm::compile_module(module).unwrap_err(), expected);
    wasm_refusal(wasm::compile_object(module).unwrap_err(), expected);
    wasm_refusal(
        direct_wasm(&module.functions[0], module).unwrap_err(),
        expected,
    );
    assert_eq!(*module, before);
}

#[test]
fn pointer_width_constants_refuse_at_the_declared_target_without_carrier_truncation() {
    let cells = [
        (true, Ty::Usize, -1),
        (true, Ty::Usize, 1_i128 << 32),
        (true, Ty::Isize, (i32::MIN as i128) - 1),
        (true, Ty::Isize, 1_i128 << 31),
        (false, Ty::Usize, -1),
        (false, Ty::Usize, 1_i128 << 64),
        (false, Ty::Isize, (i64::MIN as i128) - 1),
        (false, Ty::Isize, 1_i128 << 63),
    ];
    for (wasm32, ty, value) in cells {
        let module = constant_source(ty, Constant::Int(value), wasm32);
        assert_eq!(module.pointer_bits(), if wasm32 { 32 } else { 64 });
        let expected = constant_verdict(&module);
        native_refusal(
            validate_codegen_prerequisites(&module).unwrap_err(),
            &expected,
        );
        if wasm32 {
            assert_wasm_refused(&module, &expected);
        } else {
            assert_native_refused(&module, &expected);
        }
    }
}

#[test]
fn fixed_width_nested_and_global_constants_use_the_same_canonical_type_verdict() {
    for (ty, value) in [
        (Ty::U8, Constant::Int(-1)),
        (Ty::U8, Constant::Int(256)),
        (Ty::I8, Constant::Int(-129)),
        (Ty::I8, Constant::Int(128)),
        (Ty::U64, Constant::Int(-1)),
        (Ty::I32, Constant::Bool(true)),
        (
            Ty::Tuple(vec![Ty::U8, Ty::I32]),
            Constant::Aggregate(vec![Constant::Int(256), Constant::Int(7)]),
        ),
    ] {
        let native = constant_source(ty, value, false);
        let expected = constant_verdict(&native);
        assert_native_refused(&native, &expected);
        let mut wasm = native.clone();
        retarget(&mut wasm, true);
        assert_eq!(constant_verdict(&wasm), expected);
        assert_wasm_refused(&wasm, &expected);
    }
    for wasm32 in [false, true] {
        let mut module = constant_source(Ty::I32, Constant::Int(7), wasm32);
        module.globals.push(Global {
            name: "nested_width".into(),
            ty: Ty::Tuple(vec![Ty::Usize, Ty::I32]),
            mutable: false,
            initializer: Some(Constant::Aggregate(vec![
                Constant::Int(1_i128 << module.pointer_bits()),
                Constant::Int(7),
            ])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Visibility::Default,
            retained: false,
        });
        let expected = constant_verdict(&module);
        native_refusal(
            validate_codegen_prerequisites(&module).unwrap_err(),
            &expected,
        );
        if wasm32 {
            assert_wasm_refused(&module, &expected);
        } else {
            assert_native_refused(&module, &expected);
        }
    }
}

fn source_answer(module: &Module) -> trust_ir::InterpretInt {
    let returned = trust_ir::Interpreter::with_module(module)
        .execute_func(module.functions[0].id, [])
        .expect("independent source execution of a genuinely valid value");
    assert_eq!(returned.returns.len(), 1);
    returned.returns[0].as_int().unwrap()
}

#[test]
fn genuine_32_64_and_fixed_width_boundaries_keep_source_values_and_consumer_admission() {
    let cells = [
        (true, Ty::Usize, u32::MAX as i128),
        (true, Ty::Isize, i32::MIN as i128),
        (true, Ty::Isize, i32::MAX as i128),
        (false, Ty::Usize, u64::MAX as i128),
        (false, Ty::Isize, i64::MIN as i128),
        (false, Ty::Isize, i64::MAX as i128),
        (true, Ty::U8, u8::MAX as i128),
        (true, Ty::I8, i8::MIN as i128),
        (true, Ty::U64, u64::MAX as i128),
        (false, Ty::U8, u8::MAX as i128),
        (false, Ty::I8, i8::MIN as i128),
        (false, Ty::U64, u64::MAX as i128),
    ];
    for (wasm32, ty, value) in cells {
        let module = constant_source(ty, Constant::Int(value), wasm32);
        let before = module.clone();
        assert!(trust_ir_build::validate_module(&module).is_empty());
        validate_codegen_prerequisites(&module).unwrap();
        let actual = source_answer(&module);
        if value < 0 {
            assert_eq!(actual.as_signed(), value);
        } else {
            assert_eq!(actual.as_unsigned(), value as u128);
        }
        if wasm32 {
            let bytes = wasm::compile_module_with_license(&module, &permit_unlicensed()).unwrap();
            wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
                .validate_all(&bytes)
                .unwrap();
            assert!(
                !wasm::compile_object_with_license(&module, &permit_unlicensed())
                    .unwrap()
                    .is_empty()
            );
            permitted_direct_wasm(&module.functions[0], &module).unwrap();
        } else {
            translate_function_with_license(&module.functions[0], &module, &permit_unlicensed())
                .unwrap();
            trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                &module,
                GuardCarrierArch::AArch64,
                trust_cg_lower::TlsDialect::default(),
                &permit_unlicensed(),
            )
            .unwrap();
        }
        assert_eq!(module, before);
    }
}

fn reference_source(mutable: bool, permission: bool) -> Module {
    let mut builder = ModuleBuilder::new("rust_reference_spelling");
    let signature = builder.add_func_type(vec![], vec![Ty::I32]);
    let mut function = builder.function("read", signature);
    function.set_producer(Producer::TRust);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let pointer = function.alloca(Ty::I32);
    let five = function.const_value(Ty::I32, Constant::Int(5));
    function.store(Ty::I32, pointer, five);
    let reference = if !permission {
        function.copy(Ty::Ptr, pointer)
    } else if mutable {
        function.borrow_mut(pointer)
    } else {
        function.borrow(pointer)
    };
    let result = function.load(Ty::I32, reference);
    if permission {
        function.end_borrow(reference);
    }
    function.ret(vec![result]);
    function.build();
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    retarget(&mut module, false);
    module
}

#[test]
fn actual_rust_borrow_mut_borrow_and_end_borrow_findings_refuse_all_consumers() {
    for mutable in [false, true] {
        let native = reference_source(mutable, true);
        let findings = trust_ir_build::validate_module(&native);
        let permissions: Vec<_> = findings
            .iter()
            .filter(|error| {
                matches!(
                    error,
                    ValidationError::RustReferenceAsPermissionBorrow { .. }
                )
            })
            .collect();
        assert_eq!(
            permissions.len(),
            2,
            "actual borrow and its real end: {findings:?}"
        );
        for error in &permissions {
            let ValidationError::RustReferenceAsPermissionBorrow {
                function,
                block,
                inst_index,
            } = error
            else {
                unreachable!()
            };
            assert_eq!(function, "read");
            let actual = native.functions[0]
                .blocks
                .iter()
                .find(|candidate| candidate.id.index() == *block)
                .unwrap();
            assert!(actual.body[*inst_index].inst.uses_borrow_permissions());
        }
        let expected = permissions[0].to_string();
        assert_native_refused(&native, &expected);
        let mut wasm = native.clone();
        retarget(&mut wasm, true);
        assert_wasm_refused(&wasm, &expected);

        // The stamp selects the shared producer rule; absence/another producer
        // does not retroactively confer Rust source meaning or native authority.
        for producer in [None, Some(Producer::TrustIr)] {
            let mut other = native.clone();
            other.functions[0].producer = producer;
            assert!(trust_ir_build::validate_module(&other).is_empty());
            validate_codegen_prerequisites(&other).unwrap();
        }
    }
    let native = reference_source(false, false);
    assert!(trust_ir_build::validate_module(&native).is_empty());
    validate_codegen_prerequisites(&native).unwrap();
    assert_eq!(source_answer(&native).as_signed(), 5);
    translate_function_with_license(&native.functions[0], &native, &permit_unlicensed()).unwrap();
    let mut wasm = native.clone();
    retarget(&mut wasm, true);
    let bytes = wasm::compile_module_with_license(&wasm, &permit_unlicensed()).unwrap();
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&bytes)
        .unwrap();
}

#[test]
fn stale_direct_functions_are_checked_and_unrelated_compatibility_residual_remains() {
    let good = constant_source(Ty::U8, Constant::Int(255), false);
    let bad = constant_source(Ty::U8, Constant::Int(-1), false);
    let expected = constant_verdict(&bad);
    native_refusal(
        translate_function(&bad.functions[0], &good).unwrap_err(),
        &expected,
    );
    let mut wasm_good = good.clone();
    retarget(&mut wasm_good, true);
    wasm_refusal(
        direct_wasm(&bad.functions[0], &wasm_good).unwrap_err(),
        &expected,
    );
    translate_function_with_license(&good.functions[0], &bad, &permit_unlicensed()).unwrap();
    let mut wasm_bad = bad.clone();
    retarget(&mut wasm_bad, true);
    permitted_direct_wasm(&good.functions[0], &wasm_bad).unwrap();
    assert_eq!(good, constant_source(Ty::U8, Constant::Int(255), false));
    assert_eq!(bad, constant_source(Ty::U8, Constant::Int(-1), false));

    let mut partial = good.clone();
    assert!(matches!(
        partial.functions[0].blocks[0].body.pop().unwrap().inst,
        Inst::Return { .. }
    ));
    assert!(
        trust_ir_build::validate_module(&partial)
            .iter()
            .any(|error| matches!(
                error,
                ValidationError::BlockMissingTerminator(_)
                    | ValidationError::MissingTerminator { .. }
            ))
    );
    validate_codegen_prerequisites(&partial)
        .expect("the named ratchet does not become blanket full-module validation");
}
