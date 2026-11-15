use std::collections::HashMap;

use trust_cg_lower::{GuardCarrierArch, TlsDialect};
use trust_ir::{
    Block, BlockId, BodyGate, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty,
    ValueId,
};

fn literal_return() -> Module {
    let mut module = Module::new("v41_metadata");
    let signature = module
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "answer", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(42),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    module
}

/// The legacy ABSENCE of a codegen license (`body_gate: None`) is REFUSED by
/// the default policy on every entry (roadmap WS7.5, decision gate DG-73),
/// and lowers only under an explicit `Permit`.
#[test]
fn legacy_absence_of_codegen_metadata_is_refused_by_default_and_lowers_under_permit() {
    let module = literal_return();
    assert!(matches!(
        trust_cg_lower::translate_module(&module),
        Err(trust_cg_lower::AdapterError::UnlicensedBody { .. })
    ));
    assert!(matches!(
        trust_cg_lower::translate_function(&module.functions[0], &module),
        Err(trust_cg_lower::AdapterError::UnlicensedBody { .. })
    ));
    assert!(matches!(
        trust_cg_lower::translate_function_with_names(
            &module.functions[0],
            &module,
            &HashMap::new()
        ),
        Err(trust_cg_lower::AdapterError::UnlicensedBody { .. })
    ));
    let report = trust_ir_build::validate_module_report(&module);
    assert!(matches!(
        trust_cg_lower::translate_validated_module_strict_for_arch_with_tls_and_validation(
            &report,
            GuardCarrierArch::AArch64,
            TlsDialect::ElfLocalExec,
        ),
        Err(trust_cg_lower::AdapterError::UnlicensedBody { .. })
    ));

    assert!(permit_translate_module(&module).is_ok());
    assert!(
        trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed()
        )
        .is_ok()
    );
    assert!(
        trust_cg_lower::translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
            &report,
            GuardCarrierArch::AArch64,
            TlsDialect::ElfLocalExec,
            &permit_unlicensed(),
        )
        .is_ok()
    );
}

#[test]
fn explicit_body_gate_refusal_and_unknown_authorities_cannot_lower() {
    for gate in [
        BodyGate::Ungated,
        BodyGate::gated("unrecognized producer"),
        BodyGate::gated(""),
    ] {
        let mut module = literal_return();
        module.functions[0].body_gate = Some(gate);
        assert!(permit_translate_module(&module).is_err());
        assert!(
            trust_cg_lower::translate_function_with_license(
                &module.functions[0],
                &module,
                &permit_unlicensed()
            )
            .is_err()
        );
        assert!(
            trust_cg_lower::translate_function_with_names_and_license(
                &module.functions[0],
                &module,
                &HashMap::new(),
                &permit_unlicensed()
            )
            .is_err()
        );
        // A well-formed IR report is not a codegen license.
        let report = trust_ir_build::validate_module_report(&module);
        assert!(
            trust_cg_lower::translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
                &report,
                GuardCarrierArch::AArch64,
                TlsDialect::ElfLocalExec,
            &permit_unlicensed(),)
            .is_err()
        );
    }
}

#[test]
fn standalone_function_gate_is_checked_on_the_actual_argument() {
    let module = literal_return();
    let mut changed = module.functions[0].clone();
    changed.body_gate = Some(BodyGate::Ungated);
    assert!(
        trust_cg_lower::translate_function_with_license(&changed, &module, &permit_unlicensed())
            .is_err()
    );
    assert!(
        trust_cg_lower::translate_function_with_names_and_license(
            &changed,
            &module,
            &HashMap::new(),
            &permit_unlicensed()
        )
        .is_err()
    );
}

#[test]
fn unimplemented_module_assembly_and_function_abi_metadata_cannot_disappear() {
    let original = literal_return();
    for field in 0..3 {
        let mut module = original.clone();
        match field {
            0 => module
                .global_asm
                .push(".globl externally_visible_assembly_symbol".into()),
            1 => module.functions[0].attrs.naked = true,
            _ => module.functions[0].attrs.target_features.push("sve".into()),
        }
        assert!(
            permit_translate_module(&module).is_err(),
            "metadata field {field}"
        );
        let report = trust_ir_build::validate_module_report(&module);
        assert!(
            trust_cg_lower::translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
                &report,
                GuardCarrierArch::AArch64,
                TlsDialect::ElfLocalExec,
            &permit_unlicensed(),)
            .is_err(),
            "validated metadata field {field}"
        );
    }
}

/// Section placement is decided per target: a well-formed name lowers on the
/// default (AArch64) adapter entry, whose object emitter places or refuses it
/// by format; a malformed name and any name on x86-64 are refused here.
#[test]
fn global_sections_lower_on_aarch64_like_supported_symbol_attributes() {
    for field in 0..4 {
        let mut module = literal_return();
        let mut global = trust_ir::Global {
            name: "registration".into(),
            ty: Ty::I64,
            mutable: false,
            initializer: Some(Constant::Int(42)),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        };
        match field {
            0 => global.section = Some(".registration".into()),
            1 => global.visibility = trust_ir::Visibility::Hidden,
            2 => global.retained = true,
            _ => global.section = Some("bad name".into()),
        }
        module.globals.push(global);
        assert!(
            permit_translate_module(&module).is_err() == (field == 3),
            "global metadata field {field}"
        );
        if field == 0 {
            assert!(
                trust_cg_lower::reject_unconsumed_v41_surface(
                    &module,
                    trust_cg_lower::GuardCarrierArch::X86_64
                )
                .is_err(),
                "x86-64 has no explicit-section placement"
            );
        }
    }
}

#[test]
fn external_declaration_has_no_body_to_consume() {
    let mut module = literal_return();
    module.functions[0].blocks.clear();
    module.functions[0].body_gate = Some(BodyGate::Ungated);
    assert!(permit_translate_module(&module).unwrap().is_empty());
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
