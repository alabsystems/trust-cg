// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Actual source Switch admission in native and WASM consumers. Valid source
//! execution and native LIR routing are checked; WASM bytes are independently
//! validated, not natively executed or assigned proof/certificate authority.

use std::collections::HashMap;
use trust_cg_codegen::wasm;
use trust_cg_lower::adapter::{
    AdapterError, translate_function, translate_function_with_license,
    translate_function_with_names, validate_codegen_prerequisites,
};
use trust_cg_lower::instructions::{Block as LirBlock, Opcode};
use trust_cg_lower::{CodegenLicensePolicy, GuardCarrierArch, translate_module_for_arch};
use trust_ir::{Constant, FuncId, Inst, Module, Ty};
use trust_ir_build::ValidationError;

#[path = "common/switch_case_source_contract.rs"]
mod support;
use support::{set_case, source, source_answer, wasm_source};

fn case_refusal(module: &Module) -> String {
    let errors = trust_ir_build::codegen_switch_case_literal_errors(module);
    let [ValidationError::ConstTypeMismatch { location, .. }] = errors.as_slice() else {
        panic!("the actual case alone earns one typed ConstTypeMismatch: {errors:?}");
    };
    assert_eq!(location, "function 'dispatch' bb7 switch case 0");
    errors[0].to_string()
}

fn native_refusal(error: AdapterError, expected: &str) {
    match error {
        AdapterError::TrustIrAdmissionRefused { error } => assert_eq!(error, expected),
        other => panic!("source case must earn the shared admission refusal, got {other}"),
    }
}

fn wasm_refusal(error: wasm::WasmLowerError, expected: &str) {
    match error {
        wasm::WasmLowerError::CodegenAdmission(error) => {
            assert_eq!(
                error,
                AdapterError::TrustIrAdmissionRefused {
                    error: expected.into()
                }
                .to_string()
            );
        }
        other => panic!("source case must earn the shared admission refusal, got {other}"),
    }
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
/// decision gate DG-73). Every source that must LOWER, and the duplicate-id
/// refusal, state `Permit` explicitly; the case refusals stay on the default
/// public entries, whose shared source-contract verdict runs before the
/// license.
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

#[test]
fn genuine_out_of_domain_cases_refuse_native_and_wasm_public_entries_by_type() {
    let cells = [
        (Ty::U8, Constant::Int(-1)),
        (Ty::U8, Constant::Int(256)),
        (Ty::I8, Constant::Int(-129)),
        (Ty::I8, Constant::Int(128)),
        (Ty::I8, Constant::Int(255)),
        (Ty::U16, Constant::Int(-1)),
        (Ty::U16, Constant::Int(1 << 16)),
        (Ty::I16, Constant::Int(-32_769)),
        (Ty::I16, Constant::Int(32_768)),
        (Ty::U32, Constant::Int(-1)),
        (Ty::U32, Constant::Int(1 << 32)),
        (Ty::I32, Constant::Int((i32::MIN as i128) - 1)),
        (Ty::I32, Constant::Int(1 << 31)),
        (Ty::U64, Constant::Int(-1)),
        (Ty::U64, Constant::Int(1 << 64)),
        (Ty::I64, Constant::Int((i64::MIN as i128) - 1)),
        (Ty::I64, Constant::Int(1 << 63)),
        (Ty::I32, Constant::Bool(true)),
        (Ty::I128, Constant::U128(u128::MAX)),
        (Ty::U128, Constant::U128(5)),
    ];
    for (ty, case) in cells {
        let native = source(ty, case);
        let retained = native.clone();
        let expected = case_refusal(&native);
        native_refusal(
            validate_codegen_prerequisites(&native).unwrap_err(),
            &expected,
        );
        native_refusal(
            translate_function(&native.functions[0], &native).unwrap_err(),
            &expected,
        );
        native_refusal(
            translate_function_with_license(
                &native.functions[0],
                &native,
                &CodegenLicensePolicy::default(),
            )
            .unwrap_err(),
            &expected,
        );
        native_refusal(
            translate_function_with_names(&native.functions[0], &native, &HashMap::new())
                .unwrap_err(),
            &expected,
        );
        native_refusal(
            translate_module_for_arch(&native, GuardCarrierArch::AArch64).unwrap_err(),
            &expected,
        );
        assert_eq!(native, retained);

        let wasm = wasm_source(&native);
        let retained = wasm.clone();
        assert_eq!(case_refusal(&wasm), expected);
        wasm_refusal(wasm::compile_module(&wasm).unwrap_err(), &expected);
        wasm_refusal(wasm::compile_object(&wasm).unwrap_err(), &expected);
        wasm_refusal(
            direct_wasm(&wasm.functions[0], &wasm).unwrap_err(),
            &expected,
        );
        assert_eq!(wasm, retained);
    }
}

fn return_constant(function: &trust_cg_lower::function::Function, block: LirBlock) -> i64 {
    let instructions = &function.blocks[&block].instructions;
    let constant = instructions
        .iter()
        .find(|instruction| matches!(instruction.opcode, Opcode::Iconst { .. }))
        .expect("the source successor binds its return constant");
    let Opcode::Iconst { imm, .. } = constant.opcode else {
        unreachable!()
    };
    let returned = instructions.last().unwrap();
    assert!(matches!(returned.opcode, Opcode::Return));
    assert_eq!(constant.results.len(), 1);
    assert_eq!(returned.args, constant.results);
    imm
}

#[test]
fn valid_signed_unsigned_boundaries_keep_native_case_and_default_routes_and_wasm_bytes() {
    // Expected LIR case carriers are independently stated: narrow native
    // equality zero-extends, while 32/64-bit equality preserves raw bits.
    let cells = [
        (Ty::I8, -128, 128),
        (Ty::I8, -1, 255),
        (Ty::I8, 127, 127),
        (Ty::U8, 0, 0),
        (Ty::U8, 255, 255),
        (Ty::I16, i16::MIN as i128, i16::MIN as u16 as i64),
        (Ty::I16, i16::MAX as i128, i16::MAX as i64),
        (Ty::U16, 0, 0),
        (Ty::U16, u16::MAX as i128, u16::MAX as i64),
        (Ty::I32, i32::MIN as i128, i32::MIN as i64),
        (Ty::I32, i32::MAX as i128, i32::MAX as i64),
        (Ty::U32, 0, 0),
        (Ty::U32, u32::MAX as i128, -1),
        (Ty::I64, i64::MIN as i128, i64::MIN),
        (Ty::I64, i64::MAX as i128, i64::MAX),
        (Ty::U64, 0, 0),
        (Ty::U64, u64::MAX as i128, -1),
    ];
    for (ty, hit, carrier) in cells {
        let module = source(ty.clone(), Constant::Int(hit));
        assert!(trust_ir_build::validate_module(&module).is_empty());
        assert!(trust_ir_build::codegen_switch_case_literal_errors(&module).is_empty());
        let (lir, _) =
            translate_function_with_license(&module.functions[0], &module, &permit_unlicensed())
                .unwrap();
        let entry = &lir.blocks[&lir.entry_block];
        let [instruction] = entry.instructions.as_slice() else {
            panic!("one retained source Switch")
        };
        let Opcode::Switch { cases, default } = &instruction.opcode else {
            panic!("actual lowered Switch")
        };
        let [(actual, target)] = cases.as_slice() else {
            panic!("one retained case")
        };
        assert_eq!(*actual, carrier);
        assert_ne!(target, default);
        assert_eq!(return_constant(&lir, *target), 10);
        assert_eq!(return_constant(&lir, *default), 20);
        let miss = if hit == 0 { 1 } else { 0 };
        assert_eq!(source_answer(&module, &ty, hit), 10);
        assert_eq!(source_answer(&module, &ty, miss), 20);

        let wasm = wasm_source(&module);
        assert!(trust_ir_build::validate_module(&wasm).is_empty());
        let bytes = wasm::compile_module_with_license(&wasm, &permit_unlicensed()).unwrap();
        wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
            .validate_all(&bytes)
            .unwrap();
        assert!(
            !wasm::compile_object_with_license(&wasm, &permit_unlicensed())
                .unwrap()
                .is_empty()
        );
        permitted_direct_wasm(&wasm.functions[0], &wasm).unwrap();
        assert_eq!(source_answer(&wasm, &ty, hit), 10);
        assert_eq!(source_answer(&wasm, &ty, miss), 20);
    }
}

#[test]
fn detached_and_stale_supplied_functions_are_checked_not_the_modules_old_case() {
    let good = source(Ty::U8, Constant::Int(255));
    let expected = case_refusal(&source(Ty::U8, Constant::Int(-1)));
    for detached in [false, true] {
        let mut changed = good.functions[0].clone();
        if detached {
            changed.id = FuncId::new(60_003);
        }
        set_case(&mut changed, Constant::Int(-1));
        native_refusal(translate_function(&changed, &good).unwrap_err(), &expected);
        native_refusal(
            translate_function_with_names(&changed, &good, &HashMap::new()).unwrap_err(),
            &expected,
        );
        let wasm = wasm_source(&good);
        wasm_refusal(direct_wasm(&changed, &wasm).unwrap_err(), &expected);
        assert_eq!(good, source(Ty::U8, Constant::Int(255)));
    }
    // Conversely a supplied corrected function sharing the stale module's
    // ID must not be refused for a case it does not contain.
    let stale = source(Ty::U8, Constant::Int(-1));
    let corrected = good.functions[0].clone();
    translate_function_with_license(&corrected, &stale, &permit_unlicensed()).unwrap();
    trust_cg_lower::translate_function_with_names_and_license(
        &corrected,
        &stale,
        &HashMap::new(),
        &permit_unlicensed(),
    )
    .unwrap();
    permitted_direct_wasm(&corrected, &wasm_source(&stale)).unwrap();
    assert_eq!(stale, source(Ty::U8, Constant::Int(-1)));
}

#[test]
fn non_switch_constant_type_refusal_and_existing_duplicate_identity_refusal_are_preserved() {
    let mut constant = source(Ty::U8, Constant::Int(255));
    constant.functions[0].blocks[0].body.insert(
        0,
        trust_ir::InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(-1),
        })
        .with_result(trust_ir::ValueId::new(99)),
    );
    let findings = trust_ir_build::validate_module(&constant);
    let expected = findings
        .iter()
        .find(|error| matches!(error,
            ValidationError::ConstTypeMismatch { location, .. } if !location.contains("switch case")))
        .expect("the retained non-Switch constant is genuinely out of its U8 type");
    assert!(trust_ir_build::codegen_switch_case_literal_errors(&constant).is_empty());
    // The named constant-type floor now consumes this genuine finding too;
    // unrelated compatibility findings are not converted into full validation.
    native_refusal(
        validate_codegen_prerequisites(&constant).unwrap_err(),
        &expected.to_string(),
    );

    let mut duplicate = source(Ty::U8, Constant::Int(255));
    let mut other = duplicate.functions[0].clone();
    other.name = "other".into();
    duplicate.functions.push(other);
    assert!(trust_ir_build::codegen_switch_case_literal_errors(&duplicate).is_empty());
    let error = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &duplicate,
        GuardCarrierArch::AArch64,
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap_err();
    assert!(
        matches!(error, AdapterError::UnsupportedInstruction(ref message)
        if message.contains("ambiguous FuncId(60002)")),
        "{error}"
    );
}
