// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::isel::{ISelFunction, ISelOperand, InstructionSelector};
use crate::{AArch64AbiVariant, GuardCarrierArch, TlsDialect};
use trust_ir::{FieldDef, StructDef, StructPassingPolicy, TargetInfo};
use trust_ir_build::ModuleBuilder;

fn original() -> Module {
    let mut m = ModuleBuilder::new_with_target_info(
        "ordinary_native_aggregate",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64-darwin".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let record = m.add_struct(StructDef {
        id: StructId::new(0),
        name: "OrdinaryResult".into(),
        fields: vec![
            FieldDef {
                name: "status".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "value".into(),
                ty: Ty::I64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    });
    let sig = m.add_func_type(vec![Ty::Ptr, Ty::U64], vec![Ty::Struct(record)]);
    let provider = m.declare_function("ordinary_pair_provider", sig);
    let sig = m.add_func_type(vec![Ty::Ptr, Ty::U64], vec![Ty::U64]);
    let mut f = m.function("ordinary_pair_consumer", sig);
    let b = f.create_block();
    let p = f.add_block_param(b, Ty::Ptr);
    let n = f.add_block_param(b, Ty::U64);
    f.switch_to_block(b);
    let result = f.call(provider, vec![p, n]);
    let status = f.extract_field(Ty::U64, result, 0);
    let _value = f.extract_field(Ty::I64, result, 1);
    f.ret(vec![status]);
    f.build();
    m.build().unwrap()
}
fn fixture() -> (Module, Function, crate::ProofContext) {
    let m = original();
    assert!(trust_ir_build::validate_module(&m).is_empty());
    let (mut rows, validation) =
        crate::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &m,
            GuardCarrierArch::AArch64,
            TlsDialect::MachOTlv,
            &crate::codegen_license::CodegenLicensePolicy::default()
                .with_unlicensed(crate::codegen_license::UnlicensedBodyPolicy::Permit),
        )
        .unwrap();
    validation
        .replay_strict_call_bindings_exhaustive(&rows)
        .unwrap();
    assert_eq!(rows.len(), 1);
    let (mut f, ctx) = rows.remove(0);
    // Unit transport input only: the real Core consumer separately owns the
    // catalog/source map. This numeric unit fixture grants no catalog license.
    for b in f.blocks.values_mut() {
        for i in &mut b.instructions {
            if let Opcode::Call { binding, .. } = &mut i.opcode
                && let DirectCallBinding::DeclaredExternalFunction { function } = *binding
            {
                *binding = DirectCallBinding::NativeDependency {
                    function,
                    dependency: trust_cg_ir::NativeDependencyId::new(7),
                };
            }
        }
    }
    (m, f, ctx)
}
fn select(f: &Function, ctx: &crate::ProofContext) -> ISelFunction {
    let mut s = InstructionSelector::new(f.name.clone(), f.signature.clone());
    s.enable_sealed_core_native_calls();
    s.set_abi_variant(AArch64AbiVariant::Darwin);
    s.seed_aggregate_call_intents(&ctx.aggregate_call_intents);
    s.seed_value_types(&f.value_types);
    s.seed_iconst_origins(f.blocks.values().map(|b| b.instructions.as_slice()));
    s.seed_function_value_use_counts(f);
    s.lower_formal_arguments(&f.signature, f.entry_block)
        .unwrap();
    for block in f.layout_order() {
        let b = &f.blocks[&block];
        if block != f.entry_block {
            s.define_block_params(&b.params);
        }
        s.select_block_with_provenance(
            block,
            &b.instructions,
            &b.source_locs,
            &f.trust_ir_origins[&block],
        )
        .unwrap();
    }
    s.finalize()
}
#[test]
fn aggregate_result_intent_binds_actual_slot_stores_and_conversion_ids() {
    let (m, f, ctx) = fixture();
    assert_eq!(ctx.aggregate_call_intents.calls().len(), 1);
    assert_eq!(ctx.aggregate_call_intents.fields().len(), 2);
    ctx.aggregate_call_intents.validate(&m, &f).unwrap();
    let mut stripped = ctx.clone();
    stripped.aggregate_call_intents = Default::default();
    assert_ne!(
        crate::retained_lir_proof_context_digest(&[(f.clone(), ctx.clone())]).unwrap(),
        crate::retained_lir_proof_context_digest(&[(f.clone(), stripped)]).unwrap(),
    );
    let selected = select(&f, &ctx);
    assert_eq!(selected.aggregate_materializations().len(), 1);
    let (ir, mapped) = selected
        .try_to_ir_func_with_aggregate_materializations()
        .unwrap();
    assert_eq!(mapped.len(), 1);
    assert_eq!(mapped[0].fields().len(), 2);
    mapped[0]
        .validate(&m, &f, &ctx.aggregate_call_intents, &selected, &ir)
        .unwrap();
    assert_eq!(mapped[0].plan().unresolved_requirements().len(), 6);
}

#[test]
fn aggregate_field_ids_refuse_stale_address_load_width_and_foreign_field() {
    let (m, f, ctx) = fixture();
    let selected = select(&f, &ctx);
    let (ir, mapped) = selected
        .try_to_ir_func_with_aggregate_materializations()
        .unwrap();
    let binding = &mapped[0];
    for mutation in 0..4 {
        let mut changed = ir.clone();
        let field = &binding.fields()[1];
        match mutation {
            0 => changed.inst_mut(field.address()).operands[2] = trust_cg_ir::MachOperand::Imm(0),
            1 => {
                changed.inst_mut(field.load()).operands[0] = trust_cg_ir::MachOperand::VReg(
                    trust_cg_ir::VReg::new(field.plan().result().id, trust_cg_ir::RegClass::Gpr32),
                )
            }
            2 => changed.inst_mut(field.load()).operands[2] = trust_cg_ir::MachOperand::Imm(8),
            _ => changed.blocks[binding.plan().block().0 as usize]
                .insts
                .swap(field.address().0 as usize, field.load().0 as usize),
        }
        assert!(
            binding
                .validate(&m, &f, &ctx.aggregate_call_intents, &selected, &changed)
                .is_err()
        );
    }
    let mut changed = binding.clone();
    changed.fields.swap(0, 1);
    assert!(
        changed
            .validate(&m, &f, &ctx.aggregate_call_intents, &selected, &ir)
            .is_err()
    );
}
#[test]
fn aggregate_result_mutated_source_layout_call_field_slot_and_word_refuse() {
    let (m, f, ctx) = fixture();
    let selected = select(&f, &ctx);
    let (ir, mapped) = selected
        .try_to_ir_func_with_aggregate_materializations()
        .unwrap();
    let binding = &mapped[0];
    let plan = binding.plan();
    let mut source = m.clone();
    source.structs[0].fields.swap(0, 1);
    assert!(
        binding
            .validate(&source, &f, &ctx.aggregate_call_intents, &selected, &ir)
            .is_err()
    );
    for mutation in 0..5 {
        let mut changed = f.clone();
        let call = &ctx.aggregate_call_intents.calls()[0];
        match mutation {
            0 => {
                if let Opcode::Call {
                    binding: DirectCallBinding::NativeDependency { dependency, .. },
                    ..
                } = &mut changed
                    .blocks
                    .get_mut(&call.lir_block())
                    .unwrap()
                    .instructions[call.lir_instruction()]
                .opcode
                {
                    *dependency = trust_cg_ir::NativeDependencyId::new(8);
                }
            }
            1 => {
                changed
                    .value_types
                    .insert(call.lir_result(), Type::Struct(vec![Type::I32, Type::I64]));
            }
            2 => {
                let field = &ctx.aggregate_call_intents.fields()[0];
                if let Opcode::StructGep { field_index, .. } = &mut changed
                    .blocks
                    .get_mut(&field.lir_block())
                    .unwrap()
                    .instructions[field.lir_instruction()]
                .opcode
                {
                    *field_index = 1;
                }
            }
            3 => {
                let field = &ctx.aggregate_call_intents.fields()[0];
                changed
                    .trust_ir_origins
                    .get_mut(&field.lir_block())
                    .unwrap()[field.lir_instruction()] = None;
            }
            4 => {
                changed.name = "foreign_consumer".into();
            }
            _ => unreachable!(),
        }
        assert!(
            binding
                .validate(&m, &changed, &ctx.aggregate_call_intents, &selected, &ir)
                .is_err(),
            "LIR mutation {mutation}"
        );
    }
    for mutation in 0..5 {
        let mut changed = selected.clone();
        match mutation {
            0 => changed.stack_slots[plan.slot() as usize].size = 8,
            1 => changed.stack_slots[plan.slot() as usize].align = 1,
            2 => {
                changed.blocks.get_mut(&plan.block()).unwrap().insts[plan.store_instructions()[1]]
                    .operands[2] = ISelOperand::Imm(0)
            }
            3 => {
                changed.blocks.get_mut(&plan.block()).unwrap().insts[plan.address_instruction()]
                    .operands[1] = ISelOperand::PReg(trust_cg_ir::regs::XZR)
            }
            4 => {
                changed
                    .blocks
                    .get_mut(&plan.block())
                    .unwrap()
                    .lowering_provenance[plan.call_instruction()] =
                    trust_cg_ir::LoweringProvenance::UNATTRIBUTED
            }
            _ => unreachable!(),
        }
        assert!(
            binding
                .validate(&m, &f, &ctx.aggregate_call_intents, &changed, &ir)
                .is_err(),
            "ISel mutation {mutation}"
        );
    }
    let mut changed = ir.clone();
    changed.inst_mut(binding.stores()[1]).operands[2] = trust_cg_ir::MachOperand::Imm(0);
    assert!(
        binding
            .validate(&m, &f, &ctx.aggregate_call_intents, &selected, &changed)
            .is_err()
    );
    let mut changed = ir.clone();
    changed.inst_mut(binding.call()).implicit_defs = &[];
    assert!(
        binding
            .validate(&m, &f, &ctx.aggregate_call_intents, &selected, &changed)
            .is_err()
    );
    let mut changed = binding.clone();
    changed.call = changed.stores[0];
    assert!(
        changed
            .validate(&m, &f, &ctx.aggregate_call_intents, &selected, &ir)
            .is_err()
    );
    let mut changed = selected.clone();
    changed.blocks.get_mut(&plan.block()).unwrap().insts[plan.store_instructions()[0]].operands
        [0] = ISelOperand::PReg(trust_cg_ir::regs::W0);
    assert!(
        binding
            .validate(&m, &f, &ctx.aggregate_call_intents, &changed, &ir)
            .is_err()
    );
    let mut changed = ctx.aggregate_call_intents.clone();
    changed.fields.pop();
    assert!(changed.validate(&m, &f).is_err());
    let mut changed = ctx.aggregate_call_intents.clone();
    changed.fields[1] = changed.fields[0].clone();
    assert!(changed.validate(&m, &f).is_err());
    let mut changed = m.clone();
    let call = &ctx.aggregate_call_intents.calls()[0];
    let body = &mut changed
        .functions
        .iter_mut()
        .find(|x| x.id == call.caller())
        .unwrap()
        .blocks[0]
        .body;
    if let Inst::Call { args, .. } = &mut body[call.source_instruction()].inst {
        args.swap(0, 1);
    }
    assert!(ctx.aggregate_call_intents.validate(&changed, &f).is_err());
}
