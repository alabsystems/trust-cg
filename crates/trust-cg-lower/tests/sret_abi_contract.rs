//! Structural source/selector ABI controls. These do not execute generated
//! code or establish bridge FnAbi/native interoperability.

use std::collections::HashSet;

use trust_cg_ir::aarch64_regs as gpr;

use trust_cg_lower::function::{AbiSretParam, Signature};
use trust_cg_lower::instructions::{Block, DirectCallBinding, Instruction, Opcode, Value};
use trust_cg_lower::isel::{AArch64Opcode, ISelOperand, InstructionSelector};
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::X86InstructionSelector;
use trust_ir::{
    Block as IrBlock, BlockId, CallingConv, CastOp, Constant, FuncId, FuncTy, Function, Inst,
    InstrNode, Module, ParamAttrs, Ty, ValueId,
};

fn module_with_call(params: Vec<Ty>, sret: bool) -> Module {
    let mut module = Module::new("sret_contract");
    let signature = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut callee = Function::new(FuncId::new(0), "callee", signature, BlockId::new(0));
    callee.attrs.params = vec![ParamAttrs::default(); params.len()];
    if sret {
        callee.attrs.params[0].sret = true;
    }
    module.functions.push(callee);

    let mut caller = Function::new(FuncId::new(1), "caller", signature, BlockId::new(0));
    let mut entry = IrBlock::new(BlockId::new(0));
    // Source IDs deliberately differ from LIR's canonical Value(0..n).
    entry.params = params
        .into_iter()
        .enumerate()
        .map(|(index, ty)| (ValueId::new(11 + 3 * index as u32), ty))
        .collect();
    entry.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(0),
        args: entry.params.iter().map(|(value, _)| *value).collect(),
    }));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    caller.blocks.push(entry);
    module.functions.push(caller);
    module
}

#[test]
fn sret_narrow_eighth_real_gpr_is_extended_but_adjacent_stack_argument_is_not() {
    for (source_ty, carrier, signed) in [
        (Ty::I8, Type::I8, true),
        (Ty::U8, Type::I8, false),
        (Ty::I16, Type::I16, true),
        (Ty::U16, Type::I16, false),
    ] {
        for marked in [false, true] {
            // Independent FP arguments must not consume the GPR budget.
            let mut params = vec![Ty::Ptr, Ty::F32, Ty::F64];
            params.extend(std::iter::repeat_n(Ty::I64, 7));
            params.extend([source_ty.clone(), source_ty.clone()]);
            let module = module_with_call(params, marked);
            let (lir, _) = trust_cg_lower::translate_function_with_license(
                &module.functions[1],
                &module,
                &permit_unlicensed(),
            )
            .unwrap();
            assert_eq!(lir.sret_arg_callees.contains("callee"), marked);
            assert!(lir.abi_sret_param.is_none());
            let instructions = &lir.blocks[&lir.entry_block].instructions;
            let call = instructions
                .iter()
                .find(|inst| matches!(&inst.opcode, Opcode::Call { name, .. } if name == "callee"))
                .unwrap();
            let extensions: Vec<_> = instructions
                .iter()
                .filter(|inst| {
                    matches!(inst.opcode, Opcode::Sextend { .. } | Opcode::Uextend { .. })
                })
                .collect();
            assert_eq!(extensions.len(), usize::from(marked), "{source_ty:?}");
            if marked {
                let expected = if signed {
                    Opcode::Sextend {
                        from_ty: carrier.clone(),
                        to_ty: Type::I32,
                    }
                } else {
                    Opcode::Uextend {
                        from_ty: carrier.clone(),
                        to_ty: Type::I32,
                    }
                };
                assert_eq!(extensions[0].opcode, expected);
                assert_eq!(extensions[0].args, vec![Value(10)]);
                assert_eq!(extensions[0].results, vec![call.args[10]]);
                assert_eq!(lir.value_types[&call.args[10]], Type::I32);
            } else {
                assert_eq!(call.args[10], Value(10));
            }
            assert_eq!(call.args[11], Value(11));
            assert_eq!(lir.signature.params[11], carrier);
            assert!(
                lir.value_types
                    .get(&call.args[11])
                    .is_none_or(|hint| hint == &carrier)
            );

            let mut selector = InstructionSelector::new(lir.name.clone(), lir.signature.clone());
            selector.set_abi_variant(trust_cg_lower::abi::AArch64AbiVariant::Darwin);
            selector.seed_value_types(&lir.value_types);
            selector.seed_sret_param(lir.abi_sret_param).unwrap();
            selector.seed_sret_arg_callees(&lir.sret_arg_callees);
            selector
                .lower_formal_arguments(&lir.signature, lir.entry_block)
                .unwrap();
            selector
                .select_block(lir.entry_block, instructions)
                .unwrap();
            let machine = selector.finalize();
            let selected = &machine.blocks[&lir.entry_block].insts;
            let call_at = selected
                .iter()
                .position(|inst| inst.opcode == AArch64Opcode::Bl)
                .unwrap();
            assert_eq!(selected[call_at].implicit_uses.contains(&gpr::X8), marked);
            let store = if carrier == Type::I8 {
                AArch64Opcode::StrbRI
            } else {
                AArch64Opcode::StrhRI
            };
            assert_eq!(
                selected[..call_at]
                    .iter()
                    .filter(|inst| {
                        inst.opcode == store
                            && inst.operands.get(1) == Some(&ISelOperand::PReg(gpr::SP))
                    })
                    .count(),
                if marked { 1 } else { 2 }
            );
            if marked {
                assert!(selected[..call_at].iter().any(|inst| {
                    inst.opcode == AArch64Opcode::Copy
                        && inst.operands.first() == Some(&ISelOperand::PReg(gpr::W7))
                }));
            }
        }
    }
}

#[test]
fn sret_valid_declaration_preserves_sparse_source_parameter_identity() {
    let mut module = module_with_call(vec![Ty::Ptr, Ty::I64], true);
    let mut entry = IrBlock::new(BlockId::new(0));
    entry.params = vec![(ValueId::new(91), Ty::Ptr), (ValueId::new(27), Ty::I64)];
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    module.functions[0].blocks.push(entry);
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    assert_eq!(lir.abi_sret_param, Some(AbiSretParam { param_index: 0 }));
    assert_eq!(lir.signature.params, vec![Type::I64, Type::I64]);
    assert!(lir.signature.returns.is_empty());
    assert!(lir.sret_arg_callees.is_empty());
    let mut selector = InstructionSelector::new(lir.name.clone(), lir.signature.clone());
    selector.set_abi_variant(trust_cg_lower::abi::AArch64AbiVariant::Darwin);
    selector.seed_sret_param(lir.abi_sret_param).unwrap();
    selector
        .lower_formal_arguments(&lir.signature, lir.entry_block)
        .unwrap();
    let machine = selector.finalize();
    let sources: Vec<_> = machine.blocks[&lir.entry_block]
        .insts
        .iter()
        .filter_map(|inst| {
            if inst.opcode != AArch64Opcode::Copy {
                return None;
            }
            match inst.operands.get(1) {
                Some(ISelOperand::PReg(reg)) => Some(*reg),
                _ => None,
            }
        })
        .collect();
    assert_eq!(sources, vec![gpr::X8, gpr::X0]);
}

#[test]
fn sret_declarations_are_checked_on_own_function_and_direct_call_routes() {
    for malformed in 0..8 {
        let mut module = module_with_call(vec![Ty::Ptr, Ty::Ptr], true);
        match malformed {
            0 => module.func_types[0].params[0] = Ty::I64,
            1 => module.func_types[0].params[0] = Ty::F64,
            2 => {
                module.functions[0].attrs.params[0].sret = false;
                module.functions[0].attrs.params[1].sret = true;
            }
            3 => module.functions[0].attrs.params[1].sret = true,
            4 => module.functions[0].attrs.params.push(ParamAttrs {
                sret: true,
                ..Default::default()
            }),
            5 => module.func_types[0].returns = vec![Ty::I64],
            6 => module.func_types[0].returns = vec![Ty::Unit],
            7 => module.functions[0].attrs.params[0].byval = true,
            _ => unreachable!(),
        }
        // Keep source argument types aligned so a call-type mismatch cannot
        // accidentally stand in for the required ABI-declaration refusal.
        for ((_, actual), declared) in module.functions[1].blocks[0]
            .params
            .iter_mut()
            .zip(&module.func_types[0].params)
        {
            *actual = declared.clone();
        }
        let direct = trust_cg_lower::translate_function_with_license(
            &module.functions[1],
            &module,
            &permit_unlicensed(),
        )
        .unwrap_err();
        assert!(
            direct.to_string().contains("[TCG-SRET-ABI]"),
            "{malformed}: {direct}"
        );

        let mut own = module.functions[0].clone();
        let mut entry = IrBlock::new(BlockId::new(0));
        entry.params = module.func_types[0]
            .params
            .iter()
            .enumerate()
            .map(|(index, ty)| (ValueId::new(90 + index as u32), ty.clone()))
            .collect();
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        own.blocks.push(entry);
        let error =
            trust_cg_lower::translate_function_with_license(&own, &module, &permit_unlicensed())
                .unwrap_err();
        assert!(
            error.to_string().contains("[TCG-SRET-ABI]"),
            "{malformed}: {error}"
        );
    }
}

#[test]
fn sret_selectors_reject_competing_returns_and_malformed_buffer_arguments() {
    let marker = Some(AbiSretParam { param_index: 0 });
    for returns in [
        vec![Type::I64],
        vec![Type::F64],
        vec![Type::Struct(vec![Type::I64; 3])],
    ] {
        let signature = Signature {
            params: vec![Type::I64],
            returns: returns.clone(),
        };
        let mut a64 = InstructionSelector::new("bad_return".into(), signature.clone());
        a64.set_abi_variant(trust_cg_lower::abi::AArch64AbiVariant::Darwin);
        a64.seed_sret_param(marker).unwrap();
        assert!(
            a64.lower_formal_arguments(&signature, Block(0))
                .unwrap_err()
                .to_string()
                .contains("[TCG-SRET-ABI]")
        );
        let mut x86 = X86InstructionSelector::new("bad_return".into(), signature.clone());
        x86.seed_sret_param(marker).unwrap();
        assert!(
            x86.lower_formal_arguments(&signature, Block(0))
                .unwrap_err()
                .to_string()
                .contains("[TCG-SRET-ABI]")
        );

        let caller_sig = Signature {
            params: vec![Type::I64],
            returns: vec![],
        };
        let mut a64 = InstructionSelector::new("bad_call".into(), caller_sig.clone());
        a64.set_abi_variant(trust_cg_lower::abi::AArch64AbiVariant::Darwin);
        a64.seed_sret_arg_callees(&HashSet::from(["callee".into()]));
        a64.lower_formal_arguments(&caller_sig, Block(0)).unwrap();
        let error = a64
            .select_call("callee", &[Value(0)], &[Value(1)], &returns, Block(0))
            .unwrap_err();
        assert!(error.to_string().contains("[TCG-SRET-ABI]"));
        let mut x86 = X86InstructionSelector::new("bad_call".into(), caller_sig.clone());
        x86.seed_sret_arg_callees(&HashSet::from(["callee".into()]));
        x86.lower_formal_arguments(&caller_sig, Block(0)).unwrap();
        let error = x86
            .select_block(Block(0), &[call(vec![Value(0)], vec![Value(1)])])
            .unwrap_err();
        assert!(error.to_string().contains("[TCG-SRET-ABI]"));
    }
    for params in [vec![], vec![Type::I32], vec![Type::F64]] {
        let signature = Signature {
            params: params.clone(),
            returns: vec![],
        };
        let args = (0..params.len())
            .map(|index| Value(index as u32))
            .collect::<Vec<_>>();
        let mut a64 = InstructionSelector::new("bad_buffer".into(), signature.clone());
        a64.set_abi_variant(trust_cg_lower::abi::AArch64AbiVariant::Darwin);
        a64.seed_sret_arg_callees(&HashSet::from(["callee".into()]));
        a64.lower_formal_arguments(&signature, Block(0)).unwrap();
        assert!(
            a64.select_call("callee", &args, &[], &[], Block(0))
                .unwrap_err()
                .to_string()
                .contains("[TCG-SRET-ABI]")
        );
        let mut x86 = X86InstructionSelector::new("bad_buffer".into(), signature.clone());
        x86.seed_sret_arg_callees(&HashSet::from(["callee".into()]));
        x86.lower_formal_arguments(&signature, Block(0)).unwrap();
        assert!(
            x86.select_block(Block(0), &[call(args, vec![])])
                .unwrap_err()
                .to_string()
                .contains("[TCG-SRET-ABI]")
        );
    }
}

fn call(args: Vec<Value>, results: Vec<Value>) -> Instruction {
    Instruction {
        opcode: Opcode::Call {
            name: "callee".into(),
            binding: DirectCallBinding::Interposable,
        },
        args,
        results,
    }
}

#[test]
fn ordinary_pointer_first_void_indirect_calls_remain_supported() {
    let mut module = Module::new("ordinary_callback");
    let callee_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let caller_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut caller = Function::new(FuncId::new(0), "caller", caller_sig, BlockId::new(0));
    let mut entry = IrBlock::new(BlockId::new(0));
    entry.params = vec![(ValueId::new(91), Ty::Ptr), (ValueId::new(27), Ty::Ptr)];
    entry.body.push(InstrNode::new(Inst::CallIndirect {
        callee: ValueId::new(91),
        sig: callee_sig,
        args: vec![ValueId::new(27)],
        calling_conv: CallingConv::C,
    }));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    caller.blocks.push(entry);
    module.functions.push(caller);
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    assert!(lir.abi_sret_param.is_none());
    assert!(lir.sret_arg_callees.is_empty());
    assert_eq!(
        lir.blocks
            .values()
            .flat_map(|block| &block.instructions)
            .filter(|inst| matches!(inst.opcode, Opcode::CallIndirect))
            .count(),
        1
    );
}

/// Build `caller(ptr, ...)` that calls `callee` through a function pointer:
/// a `Const FnDef` (optionally reified to a raw `Ptr`) when `static_target`,
/// otherwise through its own first parameter, which has no provenance.
fn module_with_indirect_call(
    callee_params: Vec<Ty>,
    sret: bool,
    static_target: bool,
    reify: bool,
    edge_returns: Vec<Ty>,
) -> Module {
    let mut module = Module::new("sret_indirect_contract");
    let callee_sig = module
        .add_func_type(FuncTy {
            params: callee_params.clone(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut callee = Function::new(FuncId::new(0), "callee", callee_sig, BlockId::new(0));
    callee.linkage = trust_ir::Linkage::External;
    callee.attrs.params = vec![ParamAttrs::default(); callee_params.len()];
    if sret {
        callee.attrs.params[0].sret = true;
    }
    module.functions.push(callee);

    // A `Func`-typed callee must name the declaration's own FuncTyId at the
    // edge (nominal identity); only a disagreeing edge mints a second one.
    let edge_sig = if edge_returns.is_empty() {
        callee_sig
    } else {
        module
            .add_func_type(FuncTy {
                params: callee_params.clone(),
                returns: edge_returns.clone(),
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture")
    };
    let caller_sig = module
        .add_func_type(FuncTy {
            params: callee_params.clone(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut caller = Function::new(FuncId::new(1), "caller", caller_sig, BlockId::new(0));
    let mut entry = IrBlock::new(BlockId::new(0));
    entry.params = callee_params
        .iter()
        .enumerate()
        .map(|(index, ty)| (ValueId::new(index as u32), ty.clone()))
        .collect();
    let args: Vec<ValueId> = entry.params.iter().map(|(value, _)| *value).collect();
    let mut next = callee_params.len() as u32;
    let mut fresh = || {
        let value = ValueId::new(next);
        next += 1;
        value
    };
    let callee_value = if static_target {
        let constant = fresh();
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Func(callee_sig),
                value: Constant::FnDef(FuncId::new(0)),
            })
            .with_result(constant),
        );
        if reify {
            let raw = fresh();
            entry.body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    src_ty: Ty::Func(callee_sig),
                    dst_ty: Ty::Ptr,
                    operand: constant,
                })
                .with_result(raw),
            );
            raw
        } else {
            constant
        }
    } else {
        ValueId::new(0)
    };
    let mut node = InstrNode::new(Inst::CallIndirect {
        callee: callee_value,
        sig: edge_sig,
        args,
        calling_conv: CallingConv::C,
    });
    for _ in &edge_returns {
        let result = fresh();
        node = node.with_result(result);
    }
    entry.body.push(node);
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    caller.blocks.push(entry);
    module.functions.push(caller);
    module
}

/// Nine parameters after the hidden buffer: the eighth real GPR argument is a
/// narrow `I8` that must still be caller-extended (X8 does not consume an
/// argument register), and the ninth is a stack argument that must not be.
fn sret_pressure_params() -> Vec<Ty> {
    let mut params = vec![Ty::Ptr];
    params.extend(std::iter::repeat_n(Ty::I64, 7));
    params.extend([Ty::I8, Ty::I8]);
    params
}

#[test]
fn indirect_sret_identity_comes_from_the_resolved_declaration_only() {
    for reify in [false, true] {
        // Static provenance to a declaration carrying `sret`: the edge is
        // marked, and the narrow eighth GPR argument is extended as for a
        // direct sret call while the ninth (stack) argument is not.
        let module = module_with_indirect_call(sret_pressure_params(), true, true, reify, vec![]);
        let (lir, _) = trust_cg_lower::translate_function_with_license(
            &module.functions[1],
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        let instructions = &lir.blocks[&lir.entry_block].instructions;
        let call = instructions
            .iter()
            .find(|inst| matches!(inst.opcode, Opcode::CallIndirect))
            .expect("the edge stays an indirect call");
        assert_eq!(
            lir.sret_arg_indirect_callees,
            HashSet::from([call.args[0]]),
            "reify={reify}"
        );
        assert!(lir.sret_arg_callees.is_empty());
        let extensions: Vec<_> = instructions
            .iter()
            .filter(|inst| matches!(inst.opcode, Opcode::Sextend { .. }))
            .collect();
        assert_eq!(extensions.len(), 1, "reify={reify}");
        assert_eq!(extensions[0].args, vec![Value(8)]);
        assert_eq!(extensions[0].results, vec![call.args[9]]);
        assert_eq!(call.args[10], Value(9));

        // The selector then stages argument 0 into X8 and X8 rides the BLR.
        let mut selector = InstructionSelector::new(lir.name.clone(), lir.signature.clone());
        selector.set_abi_variant(trust_cg_lower::abi::AArch64AbiVariant::Darwin);
        selector.seed_value_types(&lir.value_types);
        selector.seed_sret_arg_indirect_callees(&lir.sret_arg_indirect_callees);
        selector
            .lower_formal_arguments(&lir.signature, lir.entry_block)
            .unwrap();
        selector
            .select_block(lir.entry_block, instructions)
            .unwrap();
        let machine = selector.finalize();
        let selected = &machine.blocks[&lir.entry_block].insts;
        let blr = selected
            .iter()
            .find(|inst| inst.opcode == AArch64Opcode::Blr)
            .expect("a BLR is emitted");
        assert!(
            blr.implicit_uses.contains(&gpr::X8),
            "reify={reify}: {blr:?}"
        );
        assert!(selected.iter().any(|inst| {
            inst.opcode == AArch64Opcode::Copy
                && inst.operands.first() == Some(&ISelOperand::PReg(gpr::W7))
        }));

        // The same declaration WITHOUT the attribute: an ordinary edge.
        let module = module_with_indirect_call(sret_pressure_params(), false, true, reify, vec![]);
        let (lir, _) = trust_cg_lower::translate_function_with_license(
            &module.functions[1],
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        assert!(lir.sret_arg_indirect_callees.is_empty());
    }

    // A pointer with no provenance (the caller's own parameter) carries no
    // hidden-buffer fact even though a matching sret declaration exists.
    let module = module_with_indirect_call(sret_pressure_params(), true, false, false, vec![]);
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[1],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    assert!(lir.sret_arg_indirect_callees.is_empty());
    assert!(
        lir.blocks[&lir.entry_block]
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::CallIndirect))
    );
}

#[test]
fn indirect_edge_that_disagrees_with_its_sret_declaration_is_refused() {
    // The declaration returns nothing through a hidden buffer; the edge
    // claims an I64 result over the same parameters.
    let module = module_with_indirect_call(vec![Ty::Ptr, Ty::I64], true, true, true, vec![Ty::I64]);
    let error = trust_cg_lower::translate_function_with_license(
        &module.functions[1],
        &module,
        &permit_unlicensed(),
    )
    .unwrap_err();
    let message = error.to_string();
    assert!(
        message.contains("[TCG-SRET-ABI]") && message.contains("resolves to `callee`"),
        "{message}"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
