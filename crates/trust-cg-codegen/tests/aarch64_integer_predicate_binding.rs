// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Exact source/raw-selector/final-byte binding for scalar integer predicates.
//!
//! Public borrowed check results do not mint publication authority. The
//! independent finite oracle below does not call production predicate or
//! instruction encoders, and does not establish a machine-checked theorem.

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachOperand};
use trust_cg_lower::Function as LirFunction;
use trust_cg_lower::abi::AArch64AbiVariant;
use trust_cg_lower::isel::InstructionSelector;
use trust_cg_verify::aarch64_affine_lowering::{
    AffineByteError, TrustIrAffineLoweringError, check_aarch64_trust_ir_affine_bytes,
    check_aarch64_trust_ir_affine_lowering,
};
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode, Module, Ty,
    ValueId,
};

const OPS: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
];

fn value(id: u32) -> ValueId {
    ValueId::new(id)
}

fn predicate_source(ty: Ty, op: ICmpOp) -> Module {
    let mut module = Module::new("integer_predicate_binding");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![Ty::Bool],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(
        FuncId::new(3_000_000_001),
        format!("integer_{ty:?}_{op:?}"),
        signature,
        BlockId::new(71),
    );
    let (a, b, result) = (value(101), value(1_000_003), value(4_000_000_007));
    function.blocks.push(Block {
        id: function.entry,
        params: vec![(a, ty.clone()), (b, ty.clone())],
        body: vec![
            InstrNode::new(Inst::ICmp {
                op,
                ty,
                lhs: a,
                rhs: b,
            })
            .with_result(result),
            InstrNode::new(Inst::Return {
                values: vec![result],
            }),
        ],
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn actual_lower(module: &Module, ordinal: usize) -> (LirFunction, MachFunction) {
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[ordinal],
        module,
        &permit_unlicensed(),
    )
    .expect("test source must pass the actual TrustIR adapter");
    let machine = actual_select(&lir);
    (lir, machine)
}

fn actual_select(lir: &LirFunction) -> MachFunction {
    let mut selector = InstructionSelector::new(lir.name.clone(), lir.signature.clone());
    selector.set_abi_variant(AArch64AbiVariant::Aapcs64);
    selector.set_stack_slots(lir.stack_slots.clone());
    selector.seed_value_types(&lir.value_types);
    selector.seed_iconst_origins(lir.blocks.values().map(|b| b.instructions.as_slice()));
    selector.seed_function_value_use_counts(lir);
    selector
        .lower_formal_arguments(&lir.signature, lir.entry_block)
        .unwrap();
    for id in lir.layout_order() {
        let block = &lir.blocks[&id];
        selector
            .select_block_with_provenance(
                id,
                &block.instructions,
                &block.source_locs,
                &lir.trust_ir_origins[&id],
            )
            .unwrap();
    }
    selector
        .finalize_with_eh_info(&lir.eh_info)
        .unwrap()
        .to_ir_func()
}

fn actual_final_bytes(lir: &LirFunction, level: OptLevel) -> Result<Vec<u8>, String> {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: level,
        target_triple: "aarch64-unknown-linux-gnu".into(),
        verify: false,
        ..Default::default()
    });
    let machine = pipeline.prepare_function(lir).map_err(|e| e.to_string())?;
    let (bytes, fixups) = encode_function_with_fixups(&machine).map_err(|e| e.to_string())?;
    if !fixups.is_empty() {
        return Err(format!(
            "comparison leaf contains pending fixups: {fixups:?}"
        ));
    }
    Ok(bytes)
}

#[test]
fn all_integer_predicates_bind_real_linux_raw_and_o0_through_o3_bytes() {
    // Do not stop on the first missing feature. The original pre-extension
    // baseline must retain all 40 raw and 160 final-byte checker outcomes.
    let (mut rows, mut raw_attempts, mut byte_attempts) = (0, 0, 0);
    let (mut raw_accepted, mut byte_accepted) = (0, 0);
    let mut errors = Vec::new();
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        for op in OPS {
            let module = predicate_source(ty.clone(), op);
            let (lir, machine) = actual_lower(&module, 0);
            rows += 1;
            raw_attempts += 1;
            match check_aarch64_trust_ir_affine_lowering(&module, 0, &lir, &machine) {
                Ok(checked) => {
                    assert!(std::ptr::eq(checked.module(), &module));
                    assert!(std::ptr::eq(checked.source(), &module.functions[0]));
                    assert!(std::ptr::eq(checked.lir(), &lir));
                    assert!(std::ptr::eq(checked.machine(), &machine));
                    assert_eq!(checked.statistics().lowering.parameter_count, 2);
                    raw_accepted += 1;
                    println!("PREDICATE_CASE {ty:?} {op:?} raw accepted");
                }
                Err(error) => {
                    println!("PREDICATE_CASE {ty:?} {op:?} raw {error:?}");
                    errors.push(format!("{ty:?}/{op:?}/raw: {error:?}"));
                }
            }
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let bytes = match actual_final_bytes(&lir, level) {
                    Ok(bytes) => bytes,
                    Err(error) => {
                        errors.push(format!("{ty:?}/{op:?}/{level:?}/compile: {error}"));
                        continue;
                    }
                };
                byte_attempts += 1;
                match check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes) {
                    Ok(checked) => {
                        assert!(std::ptr::eq(checked.module(), &module));
                        assert!(std::ptr::eq(checked.source(), &module.functions[0]));
                        assert!(std::ptr::eq(checked.lir(), &lir));
                        assert!(std::ptr::eq(checked.code(), bytes.as_slice()));
                        assert_eq!(checked.statistics().machine_instructions, bytes.len() / 4);
                        byte_accepted += 1;
                        println!(
                            "PREDICATE_CASE {ty:?} {op:?} {level:?} accepted bytes={bytes:02x?}"
                        );
                    }
                    Err(error) => {
                        println!(
                            "PREDICATE_CASE {ty:?} {op:?} {level:?} {error:?} bytes={bytes:02x?}"
                        );
                        errors.push(format!("{ty:?}/{op:?}/{level:?}: {error:?}"));
                    }
                }
            }
        }
    }
    println!(
        "PREDICATE_CENSUS rows={rows} raw_attempts={raw_attempts} byte_attempts={byte_attempts} raw_accepted={raw_accepted} byte_accepted={byte_accepted} errors={}",
        errors.len()
    );
    assert_eq!((rows, raw_attempts, byte_attempts), (40, 40, 160));
    assert_eq!((raw_accepted, byte_accepted), (40, 160), "{errors:#?}");
}

fn boundary_bits(width: u32) -> [u64; 16] {
    let sign = 1_u64 << (width - 1);
    let mask = if width == 32 {
        u32::MAX as u64
    } else {
        u64::MAX
    };
    [
        0,
        1,
        2,
        3,
        15,
        16,
        0xff,
        0x100,
        sign - 2,
        sign - 1,
        sign,
        sign + 1,
        mask - 2,
        mask - 1,
        mask,
        mask ^ 0x55,
    ]
}

fn independent_predicate(op: ICmpOp, width: u32, a: u64, b: u64) -> bool {
    // Flipping the sign bit maps two's-complement order to unsigned order.
    let sign = 1_u64 << (width - 1);
    match op {
        ICmpOp::Eq => a == b,
        ICmpOp::Ne => a != b,
        ICmpOp::Slt => (a ^ sign) < (b ^ sign),
        ICmpOp::Sle => (a ^ sign) <= (b ^ sign),
        ICmpOp::Sgt => (a ^ sign) > (b ^ sign),
        ICmpOp::Sge => (a ^ sign) >= (b ^ sign),
        ICmpOp::Ult => a < b,
        ICmpOp::Ule => a <= b,
        ICmpOp::Ugt => a > b,
        ICmpOp::Uge => a >= b,
    }
}

fn independent_subtract_flags(width: u32, a: u64, b: u64) -> [bool; 4] {
    let sign = 1_u64 << (width - 1);
    let mask = if width == 32 {
        u32::MAX as u64
    } else {
        u64::MAX
    };
    let result = a.wrapping_sub(b) & mask;
    [
        result & sign != 0,
        result == 0,
        a >= b,
        ((a ^ b) & (a ^ result) & sign) != 0,
    ]
}

fn independent_condition(cc: u8, [n, z, c, v]: [bool; 4]) -> bool {
    match cc {
        0 => z,
        1 => !z,
        2 => c,
        3 => !c,
        4 => n,
        5 => !n,
        6 => v,
        7 => !v,
        8 => c && !z,
        9 => !c || z,
        10 => n == v,
        11 => n != v,
        12 => !z && n == v,
        13 => z || n != v,
        14 | 15 => true,
        _ => panic!("test condition outside A64 range"),
    }
}

#[test]
fn independent_integer_and_concrete_nzcv_oracles_agree_at_signed_boundaries() {
    // This test-side table is independent of the production ICmp-to-CC map.
    let conditions = [0, 1, 11, 13, 12, 10, 3, 9, 8, 2];
    let mut checks = 0;
    for width in [32, 64] {
        for (op, cc) in OPS.into_iter().zip(conditions) {
            let mut outcomes = [0, 0];
            for a in boundary_bits(width) {
                for b in boundary_bits(width) {
                    let expected = independent_predicate(op, width, a, b);
                    assert_eq!(
                        expected,
                        independent_condition(cc, independent_subtract_flags(width, a, b)),
                        "{width}/{op:?}/{a:#x}/{b:#x}"
                    );
                    outcomes[expected as usize] += 1;
                    checks += 1;
                }
            }
            assert!(outcomes.into_iter().all(|n| n > 0));
        }
    }
    assert_eq!(checks, 5_120);
}

fn words(instructions: &[u32]) -> Vec<u8> {
    instructions
        .iter()
        .flat_map(|word| word.to_le_bytes())
        .collect()
}

fn accept_every_stage(module: &Module, ordinal: usize) -> usize {
    let (lir, raw) = actual_lower(module, ordinal);
    check_aarch64_trust_ir_affine_lowering(module, ordinal, &lir, &raw).unwrap();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let bytes = actual_final_bytes(&lir, level).unwrap();
        check_aarch64_trust_ir_affine_bytes(module, ordinal, &lir, &bytes).unwrap();
    }
    5
}

fn affine_predicate_source(ty: Ty, op: ICmpOp) -> Module {
    let mut module = predicate_source(ty.clone(), op);
    let body = &mut module.functions[0].blocks[0].body;
    // Compare (a + 4095) - 17 with a copied b, then copy the Bool result.
    // Numeric overflow is modular; signed predicates inspect wrapped values.
    let mut prefix = vec![
        InstrNode::new(Inst::Const {
            ty: ty.clone(),
            value: Constant::Int(4095),
        })
        .with_result(value(42)),
        InstrNode::new(Inst::Const {
            ty: ty.clone(),
            value: Constant::Int(17),
        })
        .with_result(value(43)),
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: ty.clone(),
            lhs: value(101),
            rhs: value(42),
        })
        .with_result(value(44)),
        InstrNode::new(Inst::BinOp {
            op: BinOp::Sub,
            ty: ty.clone(),
            lhs: value(44),
            rhs: value(43),
        })
        .with_result(value(45)),
        InstrNode::new(Inst::Copy {
            ty: ty.clone(),
            operand: value(1_000_003),
        })
        .with_result(value(46)),
        InstrNode::new(Inst::ICmp {
            op,
            ty,
            lhs: value(45),
            rhs: value(46),
        })
        .with_result(value(4_000_000_007)),
        InstrNode::new(Inst::Copy {
            ty: Ty::Bool,
            operand: value(4_000_000_007),
        })
        .with_result(value(98)),
        InstrNode::new(Inst::Return {
            values: vec![value(98)],
        }),
    ];
    std::mem::swap(body, &mut prefix);
    module.functions[0].name.push_str("_affine");
    module
}

fn bool_constant_source(bit: bool) -> Module {
    let mut module = predicate_source(Ty::I64, ICmpOp::Eq);
    module.func_types[0].params.clear();
    module.functions[0].blocks[0].params.clear();
    module.functions[0].name = format!("bool_constant_{}", u8::from(bit));
    module.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(bit),
        })
        .with_result(value(4_000_000_007)),
        InstrNode::new(Inst::Copy {
            ty: Ty::Bool,
            operand: value(4_000_000_007),
        })
        .with_result(value(99)),
        InstrNode::new(Inst::Return {
            values: vec![value(99)],
        }),
    ];
    module
}

#[test]
fn typed_bool_constants_copies_and_wrapping_affine_inputs_bind_all_stages() {
    let mut checks = 0;
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        for op in OPS {
            checks += accept_every_stage(&affine_predicate_source(ty.clone(), op), 0);
        }
    }
    for bit in [false, true] {
        checks += accept_every_stage(&bool_constant_source(bit), 0);
    }
    assert_eq!(checks, 210);
    println!("AFFINE_BOOL_CENSUS source_rows=42 stage_checks={checks}");
}

#[test]
fn predicate_source_ordinal_and_exact_type_sidecars_cannot_be_substituted() {
    let mut module = predicate_source(Ty::U64, ICmpOp::Ult);
    let mut decoy = module.functions[0].clone();
    decoy.id = FuncId::new(17);
    decoy.name.push_str("_decoy");
    let Inst::ICmp { op, .. } = &mut decoy.blocks[0].body[0].inst else {
        unreachable!()
    };
    *op = ICmpOp::Ugt;
    module.functions.insert(0, decoy);
    let (lir, raw) = actual_lower(&module, 1);
    let bytes = actual_final_bytes(&lir, OptLevel::O2).unwrap();
    assert_eq!(accept_every_stage(&module, 1), 5);
    module.functions[0].name = module.functions[1].name.clone();
    assert!(matches!(
        check_aarch64_trust_ir_affine_lowering(&module, 0, &lir, &raw),
        Err(TrustIrAffineLoweringError::TrustIrLirMismatch)
    ));
    assert!(matches!(
        check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes),
        Err(AffineByteError::Source(
            TrustIrAffineLoweringError::TrustIrLirMismatch
        ))
    ));
    assert!(matches!(
        check_aarch64_trust_ir_affine_lowering(&module, 3_000_000_001, &lir, &raw),
        Err(TrustIrAffineLoweringError::InvalidTrustIr(_))
    ));
    // Return types and present sidecars must agree with independently inferred
    // types. An absent optional hint is not a semantic mismatch or proof input.
    let original = predicate_source(Ty::I32, ICmpOp::Slt);
    let (lir, raw) = actual_lower(&original, 0);
    let bytes = actual_final_bytes(&lir, OptLevel::O2).unwrap();
    let result = lir.blocks[&lir.entry_block]
        .instructions
        .iter()
        .find(|i| matches!(i.opcode, trust_cg_lower::instructions::Opcode::Icmp { .. }))
        .unwrap()
        .results[0];
    for mutation in 0..2 {
        let mut bad = lir.clone();
        match mutation {
            0 => {
                bad.value_types.insert(result, trust_cg_lower::Type::I32);
            }
            1 => {
                bad.signature.returns = vec![trust_cg_lower::Type::I32];
            }
            _ => unreachable!(),
        }
        assert!(check_aarch64_trust_ir_affine_lowering(&original, 0, &bad, &raw).is_err());
        assert!(check_aarch64_trust_ir_affine_bytes(&original, 0, &bad, &bytes).is_err());
    }
    let mut with_hint = lir.clone();
    if let Some(previous) = with_hint
        .value_types
        .insert(result, trust_cg_lower::Type::B1)
    {
        assert_eq!(previous, trust_cg_lower::Type::B1);
    }
    check_aarch64_trust_ir_affine_lowering(&original, 0, &with_hint, &raw).unwrap();
    check_aarch64_trust_ir_affine_bytes(&original, 0, &with_hint, &bytes).unwrap();
    let mut without_hint = with_hint;
    assert_eq!(
        without_hint.value_types.remove(&result),
        Some(trust_cg_lower::Type::B1)
    );
    check_aarch64_trust_ir_affine_lowering(&original, 0, &without_hint, &raw).unwrap();
    check_aarch64_trust_ir_affine_bytes(&original, 0, &without_hint, &bytes).unwrap();
    // Also exercise actual selection and all final pipelines without the hint,
    // instead of testing only an already-produced machine tuple.
    let reselected = actual_select(&without_hint);
    check_aarch64_trust_ir_affine_lowering(&original, 0, &without_hint, &reselected).unwrap();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let bytes = actual_final_bytes(&without_hint, level).unwrap();
        check_aarch64_trust_ir_affine_bytes(&original, 0, &without_hint, &bytes).unwrap();
    }
    for bit in [false, true] {
        let good = bool_constant_source(bit);
        let (lir, raw) = actual_lower(&good, 0);
        let mut bad = good.clone();
        let Inst::Const { value: literal, .. } = &mut bad.functions[0].blocks[0].body[0].inst
        else {
            unreachable!()
        };
        *literal = Constant::Int(i128::from(bit));
        assert!(check_aarch64_trust_ir_affine_lowering(&bad, 0, &lir, &raw).is_err());
        let mut bad_lir = lir.clone();
        let constant = bad_lir
            .blocks
            .get_mut(&bad_lir.entry_block)
            .unwrap()
            .instructions
            .iter_mut()
            .find(|i| {
                matches!(
                    i.opcode,
                    trust_cg_lower::instructions::Opcode::Iconst { .. }
                )
            })
            .unwrap();
        let trust_cg_lower::instructions::Opcode::Iconst { imm, .. } = &mut constant.opcode else {
            unreachable!()
        };
        *imm = 2;
        assert!(check_aarch64_trust_ir_affine_lowering(&good, 0, &bad_lir, &raw).is_err());
    }
}

#[test]
fn raw_predicate_wrong_conditions_operands_and_clobbered_flags_are_hard_failures() {
    let mut rejected = 0;
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        for op in OPS {
            let module = predicate_source(ty.clone(), op);
            let (lir, original) = actual_lower(&module, 0);
            check_aarch64_trust_ir_affine_lowering(&module, 0, &lir, &original).unwrap();
            let cmp = original
                .block(original.entry)
                .insts
                .iter()
                .copied()
                .find(|&id| original.inst(id).opcode == AArch64Opcode::CmpRR)
                .unwrap();
            let cset = original
                .block(original.entry)
                .insts
                .iter()
                .copied()
                .find(|&id| original.inst(id).opcode == AArch64Opcode::CSet)
                .unwrap();
            for mutation in 0..4 {
                let mut bad = original.clone();
                match mutation {
                    0 => {
                        let MachOperand::Imm(cc) = &mut bad.inst_mut(cset).operands[1] else {
                            panic!("actual CSET condition")
                        };
                        *cc ^= 1; // Exact logical complement for each admitted relation.
                    }
                    1 => {
                        bad.inst_mut(cmp).operands[1] = bad.inst(cmp).operands[0].clone();
                    }
                    2 => {
                        bad.inst_mut(cmp).opcode = AArch64Opcode::Tst;
                    }
                    3 => {
                        // Remove the producer without changing instruction identity/provenance.
                        bad.inst_mut(cmp).opcode = AArch64Opcode::Nop;
                        bad.inst_mut(cmp).operands.clear();
                    }
                    _ => unreachable!(),
                }
                let error = check_aarch64_trust_ir_affine_lowering(&module, 0, &lir, &bad)
                    .expect_err("target mutation acquired receipt");
                assert!(
                    !matches!(error, TrustIrAffineLoweringError::UnsupportedTrustIr(_)),
                    "supported source downgraded: {error:?}"
                );
                rejected += 1;
            }
            if !matches!(op, ICmpOp::Eq | ICmpOp::Ne) {
                let mut swapped = original.clone();
                swapped.inst_mut(cmp).operands.swap(0, 1);
                assert!(
                    check_aarch64_trust_ir_affine_lowering(&module, 0, &lir, &swapped).is_err()
                );
                rejected += 1;
            }
        }
    }
    assert_eq!(rejected, 192);
    println!("RAW_MUTANT_CENSUS rejected={rejected}");
}

#[test]
fn final_predicate_words_require_live_typed_flags_and_preserve_bool_width_equivalence() {
    // These are independent architectural bit templates, not production encoders.
    // CMP R0,R1; CSET R0,cc; RET. CSET stores inverted cc in CSINC encoding.
    let conditions = [0_u32, 1, 11, 13, 12, 10, 3, 9, 8, 2];
    let (mut accepted, mut rejected) = (0, 0);
    for (ty, sf) in [
        (Ty::I32, 0),
        (Ty::U32, 0),
        (Ty::I64, 1_u32 << 31),
        (Ty::U64, 1_u32 << 31),
    ] {
        for (op, cc) in OPS.into_iter().zip(conditions) {
            let module = predicate_source(ty.clone(), op);
            let (lir, _) = actual_lower(&module, 0);
            let cmp = 0x6b01_001f | sf;
            for result_sf in [0, 1_u32 << 31] {
                let cset = 0x1a9f_07e0 | result_sf | ((cc ^ 1) << 12);
                for sequence in [
                    vec![cmp, cset, 0xd65f_03c0],
                    vec![cmp, 0x1100_0409 | sf, cset, 0xd65f_03c0],
                ] {
                    check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &words(&sequence))
                        .unwrap();
                    accepted += 1;
                }
                for sequence in [
                    vec![cmp, cset ^ (1 << 12), 0xd65f_03c0],
                    vec![cmp ^ (1 << 31), cset, 0xd65f_03c0],
                    vec![0x6b00_001f | sf, cset, 0xd65f_03c0], // CMP a,a.
                    vec![cmp, 0xeb00_001f, cset, 0xd65f_03c0], // Clobber flags with CMP X0,X0.
                    vec![cmp, 0xea00_001f, cset, 0xd65f_03c0], // Unsupported TST writer.
                    vec![cset, 0xd65f_03c0],
                    vec![cmp, cset, 0xd420_0000, 0xd65f_03c0],
                ] {
                    let bytes = words(&sequence);
                    let error = check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes)
                        .expect_err("mutated final words acquired receipt");
                    assert!(
                        !matches!(error, AffineByteError::Source(_)),
                        "supported source downgraded: {error:?}"
                    );
                    rejected += 1;
                }
            }
            // Same-width signedness is condition semantics, not Ty spelling.
            if matches!(op, ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge) {
                let wrong_cc = match op {
                    ICmpOp::Slt => 3,
                    ICmpOp::Sle => 9,
                    ICmpOp::Sgt => 8,
                    ICmpOp::Sge => 2,
                    _ => unreachable!(),
                };
                let wrong = words(&[cmp, 0x9a9f_07e0 | ((wrong_cc ^ 1) << 12), 0xd65f_03c0]);
                assert!(matches!(
                    check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &wrong),
                    Err(AffineByteError::ReturnMismatch)
                ));
                rejected += 1;
            }
        }
    }
    assert_eq!((accepted, rejected), (160, 576));
    println!("BYTE_CONTROL_CENSUS accepted={accepted} rejected={rejected}");
    // Known Boolean 0/1 may be carried through W then X. This does not license
    // arbitrary W/X numerical reinterpretations or unknown high input bits.
    for bit in [false, true] {
        let module = bool_constant_source(bit);
        let (lir, _) = actual_lower(&module, 0);
        let bytes = words(&[
            0x5280_0009 | (u32::from(bit) << 5),
            0xaa09_03e0,
            0xd65f_03c0,
        ]);
        check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes).unwrap();
    }
    let module = predicate_source(Ty::I64, ICmpOp::Eq);
    let (lir, _) = actual_lower(&module, 0);
    let unknown_high = words(&[0x2a00_03e9, 0xeb01_013f, 0x9a9f_17e0, 0xd65f_03c0]);
    assert!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &unknown_high).is_err());
}

#[test]
fn bounds_guard_annotations_cannot_be_erased_into_pure_predicate_receipts() {
    let module = predicate_source(Ty::U64, ICmpOp::Ult);
    let (lir, raw) = actual_lower(&module, 0);
    let bytes = actual_final_bytes(&lir, OptLevel::O2).unwrap();
    check_aarch64_trust_ir_affine_lowering(&module, 0, &lir, &raw).unwrap();
    for op in [ICmpOp::Ult, ICmpOp::Eq] {
        for resultless in [false, true] {
            // These are deliberately manufactured guard-free target tuples,
            // not adapter output for the trap-bearing annotated source.
            let mut guarded = module.clone();
            let node = &mut guarded.functions[0].blocks[0].body[0];
            node.proofs.push(trust_ir::ProofAnnotation::InBounds);
            let Inst::ICmp { op: comparison, .. } = &mut node.inst else {
                unreachable!()
            };
            *comparison = op;
            if resultless {
                node.results.clear();
            }
            assert!(matches!(
                check_aarch64_trust_ir_affine_lowering(&guarded, 0, &lir, &raw),
                Err(TrustIrAffineLoweringError::UnsupportedTrustIr(_))
            ));
            assert!(matches!(
                check_aarch64_trust_ir_affine_bytes(&guarded, 0, &lir, &bytes),
                Err(AffineByteError::Source(
                    TrustIrAffineLoweringError::UnsupportedTrustIr(_)
                ))
            ));
        }
    }
    // A supported source paired with an extra target guard is instead a hard
    // target mismatch, never permission to downgrade the source to uncovered.
    let mut guarded_raw = raw.clone();
    let cmp = guarded_raw
        .block(guarded_raw.entry)
        .insts
        .iter()
        .copied()
        .find(|&id| guarded_raw.inst(id).opcode == AArch64Opcode::CmpRR)
        .unwrap();
    guarded_raw.inst_mut(cmp).opcode = AArch64Opcode::TrapBoundsCheck;
    let error = check_aarch64_trust_ir_affine_lowering(&module, 0, &lir, &guarded_raw)
        .err()
        .unwrap();
    assert!(matches!(error, TrustIrAffineLoweringError::Lowering(_)));
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/rosetta.rs"]
mod process;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/native_host.rs"]
mod native_host;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
mod native {
    use super::*;
    use sha2::{Digest, Sha256};
    use std::{fmt::Write, fs, path::Path, process::Command};

    const FUNCTIONS: usize = 80;
    // Forty W-input functions each exercise two upper32 poison patterns;
    // forty X-input functions exercise one full-width pattern. Each has
    // 16 lhs boundaries × (16 rhs boundaries + equal-lhs and lhs+1 probes).
    const CALLS: usize = (40 * 2 + 40) * 16 * 18;
    const CHECKS: usize = CALLS * 4;
    const RECORD_WORDS: usize = 11;

    fn hash_artifacts(directory: &Path) {
        fn visit(root: &Path, directory: &Path, rows: &mut Vec<(String, String)>) {
            for entry in fs::read_dir(directory).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    visit(root, &path, rows);
                } else if path.file_name().unwrap() != "SHA256SUMS" {
                    rows.push((
                        path.strip_prefix(root)
                            .unwrap()
                            .to_string_lossy()
                            .into_owned(),
                        format!("{:x}", Sha256::digest(fs::read(&path).unwrap())),
                    ));
                }
            }
        }
        let mut rows = Vec::new();
        visit(directory, directory, &mut rows);
        rows.sort();
        let manifest: String = rows
            .into_iter()
            .map(|(path, hash)| format!("{hash}  {path}\n"))
            .collect();
        fs::write(directory.join("SHA256SUMS"), manifest).unwrap();
    }

    /// One native evidence case: the TrustIR module, the integer width in
    /// bits, the predicate's index in `OPS`, and whether the source is the
    /// wrapping-affine variant.
    type NativeCase = (Module, u32, usize, bool);

    fn sources() -> (Vec<NativeCase>, String, String) {
        let mut cases = Vec::new();
        let mut assembly = String::from(".text\n");
        let mut declarations = String::new();
        let mut rows = String::new();
        // Independent assembly reference uses textual assembler mnemonics;
        // it does not consume the production condition or instruction encoder.
        let conditions = ["eq", "ne", "lt", "le", "gt", "ge", "lo", "ls", "hi", "hs"];
        for (ty, width) in [(Ty::I32, 32), (Ty::U32, 32), (Ty::I64, 64), (Ty::U64, 64)] {
            for (predicate, (op, cc)) in OPS.into_iter().zip(conditions).enumerate() {
                for affine in [false, true] {
                    let module = if affine {
                        affine_predicate_source(ty.clone(), op)
                    } else {
                        predicate_source(ty.clone(), op)
                    };
                    let name = &module.functions[0].name;
                    // Capture the complete machine return in X0, not the C Bool ABI.
                    // Saved output pointer survives BL; stack frame is 16-byte aligned.
                    let symbol = native_host::c_symbol(name);
                    writeln!(
                        assembly,
                        ".p2align 2\n.global cg_{name}\n.type cg_{name},%function\ncg_{name}:\n\
                        stp x29,x30,[sp,#-32]!\nmov x29,sp\nstr x2,[sp,#16]\nbl {symbol}\n\
                        ldr x2,[sp,#16]\nmrs x9,nzcv\nstp x0,x9,[x2]\nldp x29,x30,[sp],#32\nret\n\
                        .size cg_{name},.-cg_{name}"
                    )
                    .unwrap();
                    let r = if width == 32 { "w" } else { "x" };
                    writeln!(
                        assembly,
                        ".p2align 2\n.global ref_{name}\n.type ref_{name},%function\nref_{name}:"
                    )
                    .unwrap();
                    if affine {
                        writeln!(assembly, "add {r}0,{r}0,#4095\nsub {r}0,{r}0,#17").unwrap();
                    }
                    writeln!(assembly, "cmp {r}0,{r}1\ncset x0,{cc}\nmrs x9,nzcv\nstp x0,x9,[x2]\nret\n.size ref_{name},.-ref_{name}").unwrap();
                    writeln!(declarations, "extern void cg_{name}(uint64_t,uint64_t,uint64_t*);\nextern void ref_{name}(uint64_t,uint64_t,uint64_t*);").unwrap();
                    writeln!(
                        rows,
                        "{{{width},{predicate},{},cg_{name},ref_{name}}},",
                        u8::from(affine)
                    )
                    .unwrap();
                    cases.push((module, width, predicate, affine));
                }
            }
        }
        assembly.push_str(".section .note.GNU-stack,\"\",%progbits\n");
        assert_eq!(cases.len(), FUNCTIONS);
        let driver = DRIVER
            .replace("@DECLARATIONS@", &declarations)
            .replace("@ROWS@", &rows)
            .replace("@CALLS@", &CALLS.to_string())
            .replace("@CHECKS@", &CHECKS.to_string());
        (cases, assembly, driver)
    }

    const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
@DECLARATIONS@
typedef void (*function)(uint64_t,uint64_t,uint64_t*);
struct test_case { unsigned width, predicate, affine; function cg, reference; };
static const struct test_case cases[] = {
@ROWS@
};
static uint64_t boundary(unsigned i, unsigned width) {
    const uint64_t sign = UINT64_C(1) << (width-1);
    const uint64_t mask = width == 32 ? UINT32_MAX : UINT64_MAX;
    const uint64_t values[] = {0,1,2,3,15,16,0xff,0x100,sign-2,sign-1,sign,sign+1,mask-2,mask-1,mask,mask^0x55};
    return values[i];
}
static uint64_t predicate(unsigned op, unsigned width, uint64_t a, uint64_t b) {
    const uint64_t sign = UINT64_C(1) << (width-1);
    switch (op) {
    case 0:return a==b; case 1:return a!=b;
    case 2:return (a^sign)<(b^sign); case 3:return (a^sign)<=(b^sign);
    case 4:return (a^sign)>(b^sign); case 5:return (a^sign)>=(b^sign);
    case 6:return a<b; case 7:return a<=b; case 8:return a>b; case 9:return a>=b;
    default:return UINT64_MAX;
    }
}
static uint64_t flags(unsigned width, uint64_t a, uint64_t b) {
    const uint64_t sign = UINT64_C(1) << (width-1);
    const uint64_t mask = width == 32 ? UINT32_MAX : UINT64_MAX;
    const uint64_t r = (a-b)&mask;
    return ((uint64_t)((r&sign)!=0)<<31) | ((uint64_t)(r==0)<<30)
        | ((uint64_t)(a>=b)<<29) | ((uint64_t)(((a^b)&(a^r)&sign)!=0)<<28);
}
int main(int argc, char **argv) {
    if (argc != 2) return 90;
    FILE *records = fopen(argv[1],"wb"); if (!records) return 91;
    uint64_t calls=0, checks=0;
    for (unsigned row=0; row<sizeof(cases)/sizeof(cases[0]); ++row) {
        const struct test_case *c=&cases[row];
        const uint64_t mask=c->width==32 ? UINT32_MAX : UINT64_MAX;
        unsigned outcomes[2]={0,0};
        for (unsigned ai=0;ai<16;++ai) for (unsigned bi=0;bi<18;++bi) {
            const uint64_t a=boundary(ai,c->width);
            const uint64_t left=(a+(c->affine ? 4078 : 0))&mask;
            const uint64_t b=bi<16 ? boundary(bi,c->width) : (left+(bi-16))&mask;
            const uint64_t expected=predicate(c->predicate,c->width,left,b);
            for (unsigned poison=0;poison<(c->width==32 ? 2U : 1U);++poison) {
                const uint64_t upper_a=poison ? UINT64_C(0xaaaa555500000000) : UINT64_C(0xdeadbeef00000000);
                const uint64_t upper_b=poison ? UINT64_C(0x5555aaaa00000000) : UINT64_C(0xcafef00d00000000);
                const uint64_t input_a=a|(c->width==32 ? upper_a : 0);
                const uint64_t input_b=b|(c->width==32 ? upper_b : 0);
                uint64_t cg[2]={UINT64_MAX,UINT64_MAX}, as[2]={UINT64_MAX,UINT64_MAX};
                c->cg(input_a,input_b,cg); c->reference(input_a,input_b,as);
                const uint64_t record[]={row,c->width,c->predicate,c->affine,input_a,input_b,expected,cg[0],cg[1],as[0],as[1]};
                if (fwrite(record,sizeof(record),1,records)!=1) { fclose(records); return 92; }
                ++calls; ++outcomes[expected];
                if (cg[0]!=expected || as[0]!=expected || cg[0]!=as[0] || as[1]!=flags(c->width,left,b)) {
                    fprintf(stderr,"FAIL row=%u a=%016" PRIx64 " b=%016" PRIx64 " expected=%" PRIu64 " cg=%016" PRIx64 " as=%016" PRIx64 " asm_flags=%016" PRIx64 "\n",row,input_a,input_b,expected,cg[0],as[0],as[1]);
                    fclose(records); return 1;
                }
                checks+=4;
            }
        }
        if (!outcomes[0] || !outcomes[1]) { fclose(records); return 93; }
        printf("ROW %u width=%u predicate=%u affine=%u false=%u true=%u\n",row,c->width,c->predicate,c->affine,outcomes[0],outcomes[1]);
    }
    if (fclose(records)!=0) return 94;
    if (calls!=@CALLS@ || checks!=@CHECKS@) return 95;
    printf("PASS %" PRIu64 " actual pipeline calls, %" PRIu64 " assembly controls, %" PRIu64 " full-return/oracle checks\n",calls,calls,checks);
    return 0;
}
"#;

    #[test]
    fn real_native_integer_predicates_match_independent_c_and_assembly_at_all_tiers() {
        let directory_scratch = crate::fresh_dir::create("trust-cg-integer-predicate-native-");
        let directory = directory_scratch.to_path_buf();
        eprintln!("Integer-predicate native evidence={directory:?}");
        let (cases, assembly, driver) = sources();
        fs::write(
            directory.join("controls.S"),
            native_host::assembly(&assembly),
        )
        .unwrap();
        fs::write(directory.join("driver.c"), driver).unwrap();
        fs::write(directory.join("SCOPE.txt"), "Actual TrustIR adapter, host AAPCS64 ISel (Linux GNU ELF or Darwin Mach-O), Pipeline O0-O3, allocation, bytes and native execution. verify:true is diagnostic, not Formal or publication authority. Full X0 is an observed emitted-sequence property, not a C Bool ABI guarantee. CG final NZCV is retained diagnostically only; the independently assembled CMP/CSET reference has an explicit flag contract. Forty direct and forty wrapping-affine sources; both Boolean outcomes required per source. Native C uses only unsigned integer operations. Failed artifacts are retained; command records contain timeout bounds. Environment is inherited, not hermetic.\n").unwrap();
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let tier = directory.join(format!("{level:?}"));
            fs::create_dir(&tier).unwrap();
            let pipeline = Pipeline::new(PipelineConfig {
                opt_level: level,
                target_triple: native_host::TRIPLE.into(),
                verify: true,
                ..Default::default()
            });
            let mut functions = Vec::new();
            for (module, _, _, _) in &cases {
                let name = &module.functions[0].name;
                let (lir, raw) = actual_lower(module, 0);
                fs::write(tier.join(format!("{name}.trustir")), format!("{module:#?}")).unwrap();
                fs::write(tier.join(format!("{name}.lir")), format!("{lir:#?}")).unwrap();
                fs::write(tier.join(format!("{name}.raw.machir")), format!("{raw:#?}")).unwrap();
                check_aarch64_trust_ir_affine_lowering(module, 0, &lir, &raw).unwrap();
                let (machine, metrics) =
                    pipeline.prepare_function_with_metrics(&lir, None).unwrap();
                let (bytes, fixups) = encode_function_with_fixups(&machine).unwrap();
                assert!(fixups.is_empty());
                fs::write(tier.join(format!("{name}.machir")), format!("{machine:#?}")).unwrap();
                fs::write(
                    tier.join(format!("{name}.metrics")),
                    format!("{metrics:#?}"),
                )
                .unwrap();
                fs::write(tier.join(format!("{name}.bin")), &bytes).unwrap();
                check_aarch64_trust_ir_affine_bytes(module, 0, &lir, &bytes).unwrap();
                functions.push(machine);
            }
            let object = tier.join("predicates.o");
            let elf = pipeline.compile_module(&functions).unwrap();
            native_host::assert_native_object(&elf);
            fs::write(&object, elf).unwrap();
            let binary = tier.join("run");
            let mut link = Command::new("cc");
            link.arg(format!("-{level:?}"))
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror"])
                .args(native_host::link_hardening_args())
                .arg(directory.join("driver.c"))
                .arg(directory.join("controls.S"))
                .arg(&object)
                .arg("-o")
                .arg(&binary);
            fs::write(
                tier.join("link.command"),
                format!("{link:?}\ntimeout={:?}\n", process::codegen_link_timeout()),
            )
            .unwrap();
            let linked =
                process::command_output_with_timeout(&mut link, process::codegen_link_timeout())
                    .unwrap();
            fs::write(tier.join("link.stdout"), &linked.output.stdout).unwrap();
            fs::write(tier.join("link.stderr"), &linked.output.stderr).unwrap();
            fs::write(
                tier.join("link.status"),
                format!(
                    "status={:?} timed_out={}\n",
                    linked.output.status, linked.timed_out
                ),
            )
            .unwrap();
            hash_artifacts(&directory);
            assert!(
                !linked.timed_out && linked.output.status.success(),
                "{directory:?}: {}",
                String::from_utf8_lossy(&linked.output.stderr)
            );
            let records = tier.join("results.bin");
            let mut command = Command::new(&binary);
            command.arg(&records);
            fs::write(
                tier.join("run.command"),
                format!(
                    "{command:?}\ntimeout={:?}\n",
                    process::codegen_run_timeout()
                ),
            )
            .unwrap();
            let run =
                process::command_output_with_timeout(&mut command, process::codegen_run_timeout())
                    .unwrap();
            fs::write(tier.join("stdout.log"), &run.output.stdout).unwrap();
            fs::write(tier.join("stderr.log"), &run.output.stderr).unwrap();
            fs::write(
                tier.join("run.status"),
                format!(
                    "status={:?} timed_out={}\n",
                    run.output.status, run.timed_out
                ),
            )
            .unwrap();
            hash_artifacts(&directory);
            assert!(
                !run.timed_out && run.output.status.success(),
                "{directory:?}: {} {}",
                String::from_utf8_lossy(&run.output.stdout),
                String::from_utf8_lossy(&run.output.stderr)
            );
            let output = String::from_utf8(run.output.stdout).unwrap();
            assert_eq!(
                output
                    .lines()
                    .filter(|line| line.starts_with("ROW "))
                    .count(),
                FUNCTIONS
            );
            assert!(output.contains(&format!("PASS {CALLS} actual pipeline calls, {CALLS} assembly controls, {CHECKS} full-return/oracle checks")));
            assert_eq!(
                fs::metadata(&records).unwrap().len(),
                (CALLS * RECORD_WORDS * 8) as u64
            );
            // Independently replay the retained full-width results with Rust's
            // bit oracle too, rather than trusting only the C exit status.
            for bytes in fs::read(&records)
                .unwrap()
                .as_chunks::<{ RECORD_WORDS * 8 }>()
                .0
            {
                let row: Vec<_> = bytes
                    .as_chunks::<8>()
                    .0
                    .iter()
                    .map(|b| u64::from_le_bytes(*b))
                    .collect();
                let width = row[1] as u32;
                let mask = if width == 32 {
                    u32::MAX as u64
                } else {
                    u64::MAX
                };
                let a = ((row[4] & mask).wrapping_add(if row[3] == 1 { 4078 } else { 0 })) & mask;
                let b = row[5] & mask;
                let expected = u64::from(independent_predicate(OPS[row[2] as usize], width, a, b));
                assert_eq!((row[6], row[7], row[9]), (expected, expected, expected));
                let [n, z, c, v] = independent_subtract_flags(width, a, b);
                assert_eq!(
                    row[10],
                    ((n as u64) << 31)
                        | ((z as u64) << 30)
                        | ((c as u64) << 29)
                        | ((v as u64) << 28)
                );
            }
            println!(
                "NATIVE_PREDICATE_CENSUS tier={level:?} sources={FUNCTIONS} cg_calls={CALLS} asm_calls={CALLS} checks={CHECKS} retained={tier:?}"
            );
        }
        hash_artifacts(&directory);
    }
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
