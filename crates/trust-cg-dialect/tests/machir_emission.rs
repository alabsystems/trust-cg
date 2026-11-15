//! Direct public-emitter admission controls; these intentionally bypass conversion.

use trust_cg_dialect::dialects::conversions::register_all;
use trust_cg_dialect::dialects::machir::{
    MACHIR_ADD_RR, MACHIR_EOR_RR, MACHIR_MOVZ_I64, MACHIR_RET,
};
use trust_cg_dialect::id::{DialectOpId, OpId, ValueId};
use trust_cg_dialect::module::{DialectFunction, DialectModule};
use trust_cg_dialect::op::Attribute;
use trust_cg_dialect::registry::DialectRegistry;
use trust_cg_dialect::{EmitError, emit_mach_function};
use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{AArch64Opcode, MachOperand, Type, VReg};

fn identity_module() -> DialectModule {
    let mut registry = DialectRegistry::new();
    let (_, _, machir, _) = register_all(&mut registry);
    let mut function = DialectFunction::new("identity", vec![Type::I64], vec![Type::I64]).unwrap();
    function
        .append_op(
            function.entry_block().unwrap(),
            DialectOpId::new(machir, MACHIR_RET),
            vec![],
            vec![function.params[0].0],
            vec![],
            None,
        )
        .unwrap();
    let mut module = DialectModule::new("emission", registry);
    module.push_function(function);
    module
}

fn constant_module() -> DialectModule {
    let mut module = identity_module();
    let machir = module.registry.by_name("machir").unwrap();
    let function = &mut module.functions[0];
    let result = function.alloc_value().unwrap();
    let constant = function
        .append_op(
            function.entry_block().unwrap(),
            DialectOpId::new(machir, MACHIR_MOVZ_I64),
            vec![(result, Type::I64)],
            vec![],
            vec![("value".into(), Attribute::U64(7))],
            None,
        )
        .unwrap();
    function.blocks[0].ops = vec![constant, OpId(0)];
    function.ops[0].operands = vec![result];
    module
}

fn assert_refused(module: &DialectModule) {
    let before = format!("{module:?}");
    assert!(emit_mach_function(module, 0).is_err());
    assert_eq!(format!("{module:?}"), before);
}

#[test]
fn emission_boundary_missing_function_is_a_diagnostic() {
    let mut module = identity_module();
    for index in [1, usize::MAX] {
        let error = emit_mach_function(&module, index).unwrap_err();
        assert!(
            matches!(error, EmitError::MissingFunction { index: actual, functions: 1 } if actual == index)
        );
        assert!(error.to_string().contains(&index.to_string()));
    }
    module.functions.clear();
    assert!(matches!(
        emit_mach_function(&module, 0),
        Err(EmitError::MissingFunction {
            index: 0,
            functions: 0
        })
    ));
}

#[test]
fn emission_boundary_missing_op_is_a_diagnostic() {
    let mut module = identity_module();
    module.functions[0].blocks[0].ops[0] = OpId(u32::MAX);
    assert_refused(&module);
}

#[test]
fn emission_boundary_duplicate_op_placement_is_rejected() {
    let mut module = identity_module();
    module.functions[0].blocks[0].ops.push(OpId(0));
    assert_refused(&module);
}

#[test]
fn emission_boundary_no_entry_block_is_rejected() {
    let mut module = identity_module();
    module.functions[0].blocks.clear();
    assert_refused(&module);
}

#[test]
fn emission_boundary_multiple_blocks_are_not_flattened() {
    let mut module = identity_module();
    module.functions[0].new_block().unwrap();
    assert_refused(&module);
}

#[test]
fn emission_boundary_block_parameters_are_not_dropped() {
    let mut module = identity_module();
    module.functions[0].blocks[0]
        .params
        .push((ValueId(99), Type::I64));
    assert_refused(&module);
}

#[test]
fn emission_boundary_duplicate_parameter_identity_is_rejected() {
    let mut module = identity_module();
    let parameter = module.functions[0].params[0].clone();
    module.functions[0].params.push(parameter);
    assert_refused(&module);
}

#[test]
fn emission_boundary_result_cannot_replace_parameter() {
    let mut module = constant_module();
    let parameter = module.functions[0].params[0].0;
    module.functions[0].ops[1].results[0].0 = parameter;
    module.functions[0].ops[0].operands[0] = parameter;
    assert_refused(&module);
}

#[test]
fn emission_boundary_result_type_must_match_opcode() {
    let mut module = constant_module();
    module.functions[0].ops[1].results[0].1 = Type::F64;
    assert_refused(&module);
}

#[test]
fn emission_boundary_operand_type_must_match_opcode() {
    let mut module = identity_module();
    let machir = module.registry.by_name("machir").unwrap();
    let function = &mut module.functions[0];
    function.params[0].1 = Type::F64;
    let parameter = function.params[0].0;
    let result = function.alloc_value().unwrap();
    let binary = function
        .append_op(
            function.entry_block().unwrap(),
            DialectOpId::new(machir, MACHIR_ADD_RR),
            vec![(result, Type::I64)],
            vec![parameter, parameter],
            vec![],
            None,
        )
        .unwrap();
    function.blocks[0].ops = vec![binary, OpId(0)];
    function.ops[0].operands = vec![result];
    assert_refused(&module);
}

#[test]
fn emission_boundary_return_cannot_define_a_result() {
    let mut module = identity_module();
    module.functions[0].ops[0]
        .results
        .push((ValueId(99), Type::I64));
    assert_refused(&module);
}

#[test]
fn emission_boundary_return_must_match_function_signature() {
    let mut module = identity_module();
    module.functions[0].results.clear();
    assert_refused(&module);
}

#[test]
fn emission_boundary_missing_return_is_rejected() {
    let mut module = identity_module();
    module.functions[0].blocks[0].ops.clear();
    module.functions[0].ops.clear();
    assert_refused(&module);
}

#[test]
fn emission_boundary_operation_after_return_is_rejected() {
    let mut module = constant_module();
    module.functions[0].ops[0].operands[0] = module.functions[0].params[0].0;
    module.functions[0].blocks[0].ops = vec![OpId(0), OpId(1)];
    assert_refused(&module);
}

#[test]
fn emission_boundary_block_reference_is_not_silently_dropped() {
    let mut module = identity_module();
    let entry = module.functions[0].entry_block().unwrap();
    module.functions[0].ops[0]
        .attrs
        .push(("target".into(), Attribute::Block(entry)));
    assert_refused(&module);
}

#[test]
fn emission_boundary_layout_checks_are_shared_by_conversion_legality_and_emission() {
    use trust_cg_dialect::conversion::{ConversionDriver, ConversionError};
    use trust_cg_dialect::pass::{Legality, PassError, validate_legality};
    for defect in 0..6 {
        let mut module = identity_module();
        let function = &mut module.functions[0];
        match defect {
            0 => function.blocks.clear(),
            1 => function.blocks.push(function.blocks[0].clone()),
            2 => function.blocks[0].ops.push(OpId(u32::MAX)),
            3 => function.blocks[0].ops.push(OpId(0)),
            4 => function.ops[0].id = OpId(99),
            5 => function.ops[0].attrs.push((
                "target".into(),
                Attribute::List(vec![Attribute::Block(trust_cg_dialect::id::BlockId(99))]),
            )),
            _ => unreachable!(),
        }
        let before = format!("{module:?}");
        assert!(matches!(
            emit_mach_function(&module, 0),
            Err(EmitError::InvalidFunction(_))
        ));
        assert!(matches!(
            validate_legality(&module, &Legality::new()),
            Err(PassError::LegalityViolation(_))
        ));
        assert!(matches!(
            ConversionDriver::new().run(&mut module),
            Err(ConversionError::InvalidFunction(_))
        ));
        assert_eq!(format!("{module:?}"), before);
    }
}

#[test]
fn emission_boundary_sparse_ids_and_unplaced_arena_entries_preserve_program_order() {
    let mut module = constant_module();
    let function = &mut module.functions[0];
    function.params[0].0 = ValueId(u32::MAX);
    function.ops[1].results[0].0 = ValueId(u32::MAX - 1);
    function.ops[0].operands[0] = ValueId(u32::MAX - 1);
    function.blocks[0].id = trust_cg_dialect::id::BlockId(97);
    // Tombstoned/unplaced ops are not part of the emitted program.
    function.ops.push(function.ops[0].clone());
    let before = format!("{module:?}");
    let output = emit_mach_function(&module, 0).unwrap();
    assert_eq!(output.next_vreg, 2);
    assert_eq!(output.blocks.len(), 1);
    assert_eq!(
        output
            .insts
            .iter()
            .map(|inst| inst.opcode)
            .collect::<Vec<_>>(),
        [
            AArch64Opcode::MovR,
            AArch64Opcode::Movz,
            AArch64Opcode::MovR,
            AArch64Opcode::Ret
        ]
    );
    assert_eq!(
        output.insts[1].operands,
        [
            MachOperand::VReg(VReg::new(1, RegClass::Gpr64)),
            MachOperand::Imm(7)
        ]
    );
    assert_eq!(
        output.insts[2].operands,
        [
            MachOperand::PReg(trust_cg_ir::regs::X0),
            MachOperand::VReg(VReg::new(1, RegClass::Gpr64))
        ]
    );
    assert!(output.insts[3].operands.is_empty());
    assert_eq!(output.insts[3].implicit_uses, [trust_cg_ir::regs::X0]);
    assert_eq!(format!("{module:?}"), before);
}

#[test]
fn emission_boundary_void_return_is_supported() {
    let mut module = identity_module();
    module.functions[0].results.clear();
    module.functions[0].ops[0].operands.clear();
    let output = emit_mach_function(&module, 0).unwrap();
    assert_eq!(output.insts.len(), 2);
    assert!(output.insts[1].operands.is_empty());
    assert!(output.signature.returns.is_empty());
}

#[test]
fn emission_boundary_i64_arguments_have_explicit_abi_transfers_and_liveins() {
    use trust_cg_ir::regs::{ARG_GPRS, FP, X0};
    for count in [1, 2, 8, 12] {
        let mut module = identity_module();
        let machir = module.registry.by_name("machir").unwrap();
        let mut function =
            DialectFunction::new("abi_arguments", vec![Type::I64; count], vec![Type::I64]).unwrap();
        function
            .append_op(
                function.entry_block().unwrap(),
                DialectOpId::new(machir, MACHIR_RET),
                vec![],
                vec![function.params[count - 1].0],
                vec![],
                None,
            )
            .unwrap();
        module.functions[0] = function;
        let output = emit_mach_function(&module, 0).unwrap();
        for (index, inst) in output.insts[..count].iter().enumerate() {
            let destination = MachOperand::VReg(VReg::new(index as u32, RegClass::Gpr64));
            if index < 8 {
                assert_eq!(inst.opcode, AArch64Opcode::MovR);
                assert_eq!(
                    inst.operands,
                    [destination, MachOperand::PReg(ARG_GPRS[index])]
                );
                assert_eq!(inst.implicit_uses, &ARG_GPRS[index + 1..count.min(8)]);
            } else {
                assert_eq!(inst.opcode, AArch64Opcode::LdrRI);
                assert_eq!(
                    inst.operands,
                    [
                        destination,
                        MachOperand::PReg(FP),
                        MachOperand::IncomingArg((index as i64 - 8) * 8)
                    ]
                );
                assert!(inst.implicit_uses.is_empty());
            }
        }
        assert_eq!(
            output.insts[count].operands,
            [
                MachOperand::PReg(X0),
                MachOperand::VReg(VReg::new(count as u32 - 1, RegClass::Gpr64))
            ]
        );
        assert!(output.insts[count + 1].operands.is_empty());
        assert_eq!(output.insts[count + 1].implicit_uses, [X0]);
    }
}

#[test]
fn emission_boundary_non_i64_abi_parameters_are_explicitly_unsupported() {
    for ty in [
        Type::I32,
        Type::F64,
        Type::I128,
        Type::Struct(vec![Type::I64]),
    ] {
        let mut module = identity_module();
        module.functions[0].params[0].1 = ty;
        // Even unused parameters affect ABI assignment and need admission.
        module.functions[0].results.clear();
        module.functions[0].ops[0].operands.clear();
        assert!(matches!(
            emit_mach_function(&module, 0),
            Err(EmitError::Unsupported(_))
        ));
    }
}

#[test]
fn emission_boundary_all_four_supported_opcodes_preserve_value_bindings() {
    let mut module = constant_module();
    let machir = module.registry.by_name("machir").unwrap();
    let function = &mut module.functions[0];
    let parameter = function.params[0].0;
    let mut previous = function.ops[1].results[0].0;
    function.blocks[0].ops.pop();
    for opcode in [MACHIR_ADD_RR, MACHIR_EOR_RR] {
        let result = function.alloc_value().unwrap();
        function
            .append_op(
                function.entry_block().unwrap(),
                DialectOpId::new(machir, opcode),
                vec![(result, Type::I64)],
                vec![parameter, previous],
                vec![],
                None,
            )
            .unwrap();
        previous = result;
    }
    function.ops[0].operands[0] = previous;
    function.blocks[0].ops.push(OpId(0));
    let output = emit_mach_function(&module, 0).unwrap();
    assert_eq!(output.next_vreg, 4);
    assert_eq!(
        output
            .insts
            .iter()
            .map(|inst| inst.opcode)
            .collect::<Vec<_>>(),
        [
            AArch64Opcode::MovR,
            AArch64Opcode::Movz,
            AArch64Opcode::AddRR,
            AArch64Opcode::EorRR,
            AArch64Opcode::MovR,
            AArch64Opcode::Ret
        ]
    );
    for index in [1, 2] {
        assert_eq!(
            output.insts[index + 1].operands,
            [
                MachOperand::VReg(VReg::new(index as u32 + 1, RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(index as u32, RegClass::Gpr64))
            ]
        );
    }
    assert_eq!(
        output.insts[4].operands,
        [
            MachOperand::PReg(trust_cg_ir::regs::X0),
            MachOperand::VReg(VReg::new(3, RegClass::Gpr64))
        ]
    );
}

#[test]
fn emission_boundary_only_the_selected_function_is_checked() {
    let mut module = identity_module();
    module.functions.push(module.functions[0].clone());
    module.functions[1].blocks.clear();
    assert!(emit_mach_function(&module, 0).is_ok());
    assert!(matches!(
        emit_mach_function(&module, 1),
        Err(EmitError::InvalidFunction(_))
    ));
}

#[test]
fn emission_boundary_registry_replacement_cannot_remove_canonical_type_checks() {
    struct EmptyMachir;
    impl trust_cg_dialect::dialect::Dialect for EmptyMachir {
        fn namespace(&self) -> &'static str {
            "machir"
        }
        fn ops(&self) -> &[trust_cg_dialect::dialect::OpDef] {
            &[]
        }
    }
    let mut module = constant_module();
    module.registry.register(Box::new(EmptyMachir));
    assert!(emit_mach_function(&module, 0).is_ok());
    module.functions[0].ops[1].results[0].1 = Type::F64;
    assert!(matches!(
        emit_mach_function(&module, 0),
        Err(EmitError::Malformed(_))
    ));
}

#[test]
fn emission_boundary_undefined_values_and_unimplemented_ops_remain_diagnostics() {
    let mut module = identity_module();
    module.functions[0].ops[0].operands[0] = ValueId(99);
    assert!(matches!(
        emit_mach_function(&module, 0),
        Err(EmitError::InvalidFunction(_))
    ));
    module.functions[0].ops[0].operands[0] = module.functions[0].params[0].0;
    module.functions[0].ops[0].op.op = trust_cg_dialect::id::OpCode(u16::MAX);
    assert!(matches!(
        emit_mach_function(&module, 0),
        Err(EmitError::Unsupported(_))
    ));
    module.functions[0].ops[0].op.dialect = module.registry.by_name("trust_ir").unwrap();
    assert!(matches!(
        emit_mach_function(&module, 0),
        Err(EmitError::UnexpectedDialect { .. })
    ));
}

#[test]
fn conversion_boundary_duplicate_definitions_are_not_sanitized_by_renumbering() {
    use trust_cg_dialect::conversion::{ConversionDriver, ConversionError};
    for result_collision in [false, true] {
        let mut module = constant_module();
        let parameter = module.functions[0].params[0].clone();
        if result_collision {
            module.functions[0].ops[1].results[0].0 = parameter.0;
            module.functions[0].ops[0].operands[0] = parameter.0;
        } else {
            module.functions[0].params.push(parameter);
        }
        let before = format!("{module:?}");
        assert!(matches!(
            ConversionDriver::new().run(&mut module),
            Err(ConversionError::InvalidFunction(_))
        ));
        assert_eq!(format!("{module:?}"), before);
    }
}

#[test]
fn conversion_boundary_undefined_value_cannot_alias_renumbered_parameter() {
    use trust_cg_dialect::conversion::{ConversionDriver, ConversionError};
    let mut module = identity_module();
    module.functions[0].params[0].0 = ValueId(99);
    // Source ValueId(0) is undefined, but used to alias destination parameter 0.
    let before = format!("{module:?}");
    assert!(matches!(
        ConversionDriver::new().run(&mut module),
        Err(ConversionError::InvalidFunction(_))
    ));
    assert_eq!(format!("{module:?}"), before);
}

#[test]
fn conversion_boundary_forward_result_cannot_alias_renumbered_parameter() {
    use trust_cg_dialect::conversion::{ConversionDriver, ConversionError};
    let mut module = constant_module();
    let machir = module.registry.by_name("machir").unwrap();
    let function = &mut module.functions[0];
    function.params[0].0 = ValueId(99);
    function.ops[1].results[0].0 = ValueId(0);
    let early = function
        .append_op(
            function.entry_block().unwrap(),
            DialectOpId::new(machir, MACHIR_ADD_RR),
            vec![(ValueId(100), Type::I64)],
            vec![ValueId(99), ValueId(0)],
            vec![],
            None,
        )
        .unwrap();
    function.ops[0].operands[0] = ValueId(100);
    function.blocks[0].ops = vec![early, OpId(1), OpId(0)];
    let before = format!("{module:?}");
    assert!(matches!(
        ConversionDriver::new().run(&mut module),
        Err(ConversionError::UnmappedValue {
            value: ValueId(0),
            ..
        })
    ));
    assert_eq!(format!("{module:?}"), before);
}

#[test]
fn conversion_boundary_valid_sparse_definitions_are_renumbered_without_aliasing() {
    use trust_cg_dialect::conversion::ConversionDriver;
    let mut module = constant_module();
    module.functions[0].params[0].0 = ValueId(99);
    module.functions[0].ops[1].results[0].0 = ValueId(0);
    module.functions[0].ops[0].operands[0] = ValueId(0);
    ConversionDriver::new().run(&mut module).unwrap();
    let function = &module.functions[0];
    assert_eq!(function.params[0].0, ValueId(0));
    assert_eq!(function.ops[0].results[0].0, ValueId(1));
    assert_eq!(function.ops[1].operands, [ValueId(1)]);
    assert!(emit_mach_function(&module, 0).is_ok());
}

#[test]
fn conversion_boundary_invalid_pattern_bindings_do_not_publish_a_rebuild() {
    use trust_cg_dialect::conversion::{
        ConversionDriver, ConversionError, ConversionPattern, Rewriter,
    };
    use trust_cg_dialect::op::DialectOp;
    struct BrokenBinding {
        source: DialectOpId,
        defect: u8,
    }
    impl ConversionPattern for BrokenBinding {
        fn source_op(&self) -> DialectOpId {
            self.source
        }
        fn rewrite(
            &self,
            op: &DialectOp,
            rewriter: &mut Rewriter<'_>,
        ) -> Result<(), ConversionError> {
            let result = rewriter.alloc_value()?;
            rewriter.emit(
                self.source,
                vec![(result, Type::I64)],
                vec![],
                op.attrs.clone(),
                None,
            )?;
            match self.defect {
                0 => {} // Omit the source-result binding.
                1 => rewriter.bind_result(op.results[0].0, ValueId(99)),
                2 => {
                    rewriter.bind_result(op.results[0].0, result);
                    rewriter.emit(
                        self.source,
                        vec![(result, Type::I64)],
                        vec![],
                        op.attrs.clone(),
                        None,
                    )?;
                }
                _ => unreachable!(),
            }
            Ok(())
        }
    }
    for defect in 0..3 {
        let mut module = constant_module();
        let source = module.functions[0].ops[1].op;
        let before = format!("{module:?}");
        let mut driver = ConversionDriver::new();
        driver.register(Box::new(BrokenBinding { source, defect }));
        let error = driver.run(&mut module).unwrap_err();
        if defect == 0 {
            assert!(matches!(error, ConversionError::UnmappedValue { .. }));
        } else {
            assert!(matches!(error, ConversionError::RewriteFailed(_)));
        }
        assert_eq!(format!("{module:?}"), before);
    }
}

#[test]
fn emission_boundary_unplaced_arena_cannot_change_live_type_environment() {
    use trust_cg_dialect::pass::{Legality, validate_legality};
    let mut module = constant_module();
    let mut orphan = module.functions[0].ops[1].clone();
    orphan.id = OpId(2);
    orphan.results = vec![(module.functions[0].ops[1].results[0].0, Type::F64)];
    module.functions[0].ops.push(orphan);
    validate_legality(&module, &Legality::new()).unwrap();
    assert!(emit_mach_function(&module, 0).is_ok());
}

#[test]
fn conversion_boundary_lower_module_rejects_invalid_source_before_conversion() {
    use trust_cg_dialect::conversion::ConversionError;
    use trust_cg_dialect::{LowerModuleError, lower_module};
    let mut module = identity_module();
    module.functions[0].params[0].0 = ValueId(99);
    let before = format!("{module:?}");
    assert!(matches!(
        lower_module(&mut module),
        Err(LowerModuleError::VerifToTrustIr(
            ConversionError::InvalidFunction(_)
        ))
    ));
    assert_eq!(format!("{module:?}"), before);
}
