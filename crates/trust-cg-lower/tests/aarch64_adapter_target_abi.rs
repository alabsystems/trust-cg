// Copyright 2026 Andrew Yates | Apache-2.0
//! The adapter's caller-extension decision must use the selected target ABI.

use trust_cg_lower::{GuardCarrierArch, TlsDialect, instructions::Opcode, types::Type};
use trust_ir::{
    Block, BlockId, CallingConv, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

fn target(dialect: TlsDialect) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: if dialect == TlsDialect::MachOTlv {
            "aarch64-apple-darwin"
        } else {
            "aarch64-unknown-linux-gnu"
        }
        .into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

fn caller(narrow: Ty, trailing_wide: usize, indirect: bool) -> Module {
    let mut module = Module::new("adapter_target_abi");
    module.target_info = Some(target(TlsDialect::ElfExecutable));
    let mut parameters = vec![Ty::I64, Ty::I128];
    parameters.extend(vec![Ty::I64; trailing_wide]);
    parameters.push(narrow);
    let callee_ty = module
        .add_func_type(FuncTy {
            params: parameters.clone(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut declaration = Function::new(FuncId::new(0), "observe", callee_ty, BlockId::new(0));
    declaration.blocks.clear();
    module
        .try_add_function(declaration)
        .expect("Module::try_add_function: test fixture");
    if indirect {
        parameters.insert(0, Ty::Func(callee_ty));
    }
    let caller_ty = module
        .add_func_type(FuncTy {
            params: parameters.clone(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(1), "caller", caller_ty, BlockId::new(0));
    let arguments = (usize::from(indirect)..parameters.len())
        .map(|index| ValueId::new(index as u32))
        .collect();
    let call = if indirect {
        Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: callee_ty,
            args: arguments,
            calling_conv: CallingConv::C,
        }
    } else {
        Inst::Call {
            callee: FuncId::new(0),
            args: arguments,
        }
    };
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: parameters
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (ValueId::new(index as u32), ty))
            .collect(),
        body: vec![
            InstrNode::new(call),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn caller_extensions_follow_target_i128_alignment_at_register_exhaustion() {
    for (narrow, scalar) in [
        (Ty::I8, Type::I8),
        (Ty::U8, Type::I8),
        (Ty::I16, Type::I16),
        (Ty::U16, Type::I16),
    ] {
        for indirect in [false, true] {
            for trailing_wide in [3, 4] {
                let module = caller(narrow.clone(), trailing_wide, indirect);
                let errors = trust_ir_build::validate_module(&module);
                assert!(errors.is_empty(), "{errors:?}");
                for dialect in [
                    TlsDialect::MachOTlv,
                    TlsDialect::ElfLocalExec,
                    TlsDialect::ElfInitialExec,
                    TlsDialect::ElfExecutable,
                    TlsDialect::ElfSharedObject,
                ] {
                    let mut module = module.clone();
                    module.target_info = Some(target(dialect));
                    let errors = trust_ir_build::validate_module(&module);
                    assert!(errors.is_empty(), "{errors:?}");
                    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                        &module,
                        GuardCarrierArch::AArch64,
                        dialect,
                        &permit_unlicensed(),
                    )
                    .unwrap();
                    let lir = &lowered
                        .iter()
                        .find(|(function, _)| function.name == "caller")
                        .unwrap()
                        .0;
                    let call = lir
                        .blocks
                        .values()
                        .flat_map(|block| &block.instructions)
                        .find(|instruction| {
                            matches!(
                                instruction.opcode,
                                Opcode::Call { .. } | Opcode::CallIndirect
                            )
                        })
                        .unwrap();
                    // The initial i64 occupies x0. AAPCS64 leaves x1 unused
                    // and places i128 in x2/x3; Darwin places it in x1/x2.
                    // Four following i64s therefore leave only Darwin's x7
                    // free for the final narrow parameter. With three i64s,
                    // both ABIs still pass that parameter in a register.
                    let register = trailing_wide == 3 || dialect == TlsDialect::MachOTlv;
                    let expected = if register { Type::I32 } else { scalar.clone() };
                    let value = call.args.last().unwrap();
                    let actual = lir
                        .value_types
                        .get(value)
                        .or_else(|| {
                            lir.blocks
                                .values()
                                .flat_map(|block| &block.params)
                                .find_map(|(parameter, ty)| (parameter == value).then_some(ty))
                        })
                        .expect("call argument must have a declared or produced LIR type");
                    assert_eq!(
                        actual, &expected,
                        "{narrow:?} indirect={indirect} trailing={trailing_wide} {dialect:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn unsupported_aarch64_object_target_cannot_borrow_darwin_call_abi() {
    for indirect in [false, true] {
        let module = caller(Ty::I8, 4, indirect);
        let error = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            GuardCarrierArch::AArch64,
            TlsDialect::RejectThreadLocals,
            &permit_unlicensed(),
        )
        .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("requires a supported target ABI")
        );
    }
}

fn swift_aggregate() -> Module {
    let mut module = Module::new("swift_target_abi");
    let aggregate = Ty::Tuple(vec![Ty::I64, Ty::I64]);
    let signature = module
        .add_func_type(FuncTy {
            params: vec![aggregate.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "swift_pair", signature, BlockId::new(0));
    function.calling_conv = CallingConv::Swift;
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), aggregate)],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    module
}

#[test]
fn swift_aggregate_preparation_cannot_cross_target_abis() {
    use trust_cg_lower::{prepare_module_for_lir, prepare_module_for_lir_with_tls};
    let source = swift_aggregate();
    let before = source.clone();
    let darwin = prepare_module_for_lir(&source, GuardCarrierArch::AArch64).unwrap();
    assert!(!std::ptr::eq(darwin.module(), &source));
    assert_eq!(darwin.module().functions[0].blocks[0].params.len(), 2);
    let (lir, report) = darwin
        .translate_with_tls_and_validation_with_license(TlsDialect::MachOTlv, &permit_unlicensed())
        .unwrap();
    report.replay_exact_module_bindings(&lir).unwrap();
    for dialect in [
        TlsDialect::ElfLocalExec,
        TlsDialect::ElfInitialExec,
        TlsDialect::ElfExecutable,
        TlsDialect::ElfSharedObject,
        TlsDialect::RejectThreadLocals,
    ] {
        let error = darwin
            .translate_with_tls_and_validation_with_license(dialect, &permit_unlicensed())
            .unwrap_err();
        assert!(
            error.to_string().contains("different target ABI"),
            "{error}"
        );
        // The explicit non-Darwin path must retain the aggregate and refuse its
        // unsupported calling convention, rather than silently scalarizing it.
        let prepared =
            prepare_module_for_lir_with_tls(&source, GuardCarrierArch::AArch64, dialect).unwrap();
        assert!(std::ptr::eq(prepared.module(), &source));
        let error = prepared
            .translate_with_tls_and_validation_with_license(dialect, &permit_unlicensed())
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("unsupported calling convention Swift"),
            "{error}"
        );
        let error = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &source,
            GuardCarrierArch::AArch64,
            dialect,
            &permit_unlicensed(),
        )
        .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("unsupported calling convention Swift"),
            "{error}"
        );
    }
    assert_eq!(source, before);
}

#[test]
fn target_independent_prepared_modules_remain_reusable_across_object_targets() {
    use trust_cg_lower::{prepare_module_for_lir, prepare_module_for_lir_with_tls};
    let source = caller(Ty::I8, 4, false);
    for preparation in [TlsDialect::MachOTlv, TlsDialect::ElfExecutable] {
        let prepared =
            prepare_module_for_lir_with_tls(&source, GuardCarrierArch::AArch64, preparation)
                .unwrap();
        assert!(std::ptr::eq(prepared.module(), &source));
        for translation in [TlsDialect::MachOTlv, TlsDialect::ElfExecutable] {
            let (lir, report) = prepared
                .translate_with_tls_and_validation_with_license(translation, &permit_unlicensed())
                .unwrap();
            report.replay_exact_module_bindings(&lir).unwrap();
        }
    }
    let legacy = prepare_module_for_lir(&source, GuardCarrierArch::AArch64).unwrap();
    legacy
        .translate_with_tls_and_validation_with_license(
            TlsDialect::ElfExecutable,
            &permit_unlicensed(),
        )
        .unwrap();
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
