//! Admission controls exercise the real selector, including its folding plans.
//! Invalid numeric declarations must fail before any instruction reads a carrier.

use super::*;
use trust_cg_ir::function::EnumTagWidth;

fn selector(types: &[Type]) -> (InstructionSelector, Block) {
    let mut selector = InstructionSelector::new(
        "arithmetic_admission".into(),
        Signature {
            params: Vec::new(),
            returns: Vec::new(),
        },
    );
    selector.set_abi_variant(AArch64AbiVariant::Aapcs64);
    let block = Block(0);
    selector.func.ensure_block(block);
    for (index, ty) in types.iter().enumerate() {
        let value = Value(index as u32);
        if *ty == Type::I128 {
            let lo = selector.new_vreg(RegClass::Gpr64);
            let hi = selector.new_vreg(RegClass::Gpr64);
            selector.define_i128_value(value, lo, hi);
        } else {
            let reg = selector.new_vreg(reg_class_for_type(ty));
            selector.define_value(value, ISelOperand::VReg(reg), ty.clone());
        }
    }
    (selector, block)
}

#[test]
fn integer_arithmetic_admits_only_its_declared_operand_pairs() {
    // The first six entries are the scalar integer contract. Addresses are
    // I64 in LIR. Typed vector arithmetic has its own opcodes, not Iadd &c.
    let types = [
        Type::B1,
        Type::I8,
        Type::I16,
        Type::I32,
        Type::I64,
        Type::I128,
        Type::F16,
        Type::F32,
        Type::F64,
        Type::V64,
        Type::V128,
        Type::Struct(vec![Type::I8, Type::I64, Type::I16]),
        Type::Array(Box::new(Type::I64), 2),
        Type::Enum {
            tag_width: EnumTagWidth::U8,
            variants: vec![vec![Type::I64]],
        },
    ];
    let matching = [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)];
    // Existing runtime-allocation arithmetic explicitly widens these operands.
    let promoted = [
        (0, 4),
        (4, 0),
        (1, 4),
        (4, 1),
        (2, 4),
        (4, 2),
        (3, 4),
        (4, 3),
    ];
    let mut problems = Vec::new();
    let mut cells = 0;
    let mut admitted = 0;
    for opcode in [
        Opcode::Iadd,
        Opcode::Isub,
        Opcode::Imul,
        Opcode::Sdiv,
        Opcode::Udiv,
    ] {
        for (left, lhs) in types.iter().enumerate() {
            for (right, rhs) in types.iter().enumerate() {
                let expected = matching.contains(&(left, right))
                    || (matches!(opcode, Opcode::Iadd | Opcode::Isub | Opcode::Imul)
                        && promoted.contains(&(left, right)));
                let (mut selector, block) = selector(&[lhs.clone(), rhs.clone()]);
                let result = selector.select_instruction(
                    &Instruction {
                        opcode: opcode.clone(),
                        args: vec![Value(0), Value(1)],
                        results: vec![Value(2)],
                    },
                    block,
                );
                let instructions = &selector.func.blocks[&block].insts;
                let named_refusal = matches!(
                    &result,
                    Err(ISelError::IntegerArithmeticOperands {
                        lhs: Value(0), lhs_ty, rhs: Value(1), rhs_ty, result: Value(2), ..
                    }) if lhs_ty == lhs && rhs_ty == rhs
                );
                cells += 1;
                admitted += usize::from(result.is_ok());
                if result.is_ok() != expected
                    || (!expected && (!named_refusal || !instructions.is_empty()))
                {
                    problems.push(format!(
                        "{opcode:?} {lhs:?} / {rhs:?}: expected_admitted={expected}, result={result:?}, emitted={instructions:?}"
                    ));
                }
            }
        }
    }
    eprintln!(
        "A64_INTEGER_ADMISSION cells={cells} expected_admitted=54 actual_admitted={admitted} problems={}",
        problems.len()
    );
    assert_eq!(cells, 980);
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

#[test]
fn aggregate_arithmetic_cannot_enter_immediate_or_mul_add_folds() {
    let aggregate = Type::Struct(vec![Type::I8, Type::I64, Type::I16]);
    let mut problems = Vec::new();
    for opcode in [Opcode::Iadd, Opcode::Isub] {
        for args in [[Value(0), Value(1)], [Value(1), Value(0)]] {
            let (mut selector, block) = selector(std::slice::from_ref(&aggregate));
            selector.iconst_origins.insert(Value(1), (Type::I64, 7));
            let result = selector.select_block(
                block,
                &[Instruction {
                    opcode: opcode.clone(),
                    args: args.to_vec(),
                    results: vec![Value(2)],
                }],
            );
            if !matches!(&result, Err(ISelError::IntegerArithmeticOperands { .. }))
                || !selector.func.blocks[&block].insts.is_empty()
            {
                problems.push(format!(
                    "{opcode:?} {args:?} immediate: {result:?}, {:?}",
                    selector.func.blocks[&block].insts
                ));
            }
        }
    }
    for (opcode, args) in [
        (Opcode::Iadd, [Value(3), Value(2)]),
        (Opcode::Isub, [Value(3), Value(2)]),
        (Opcode::Isub, [Value(2), Value(3)]),
    ] {
        let (mut selector, block) =
            selector(&[aggregate.clone(), aggregate.clone(), aggregate.clone()]);
        let result = selector.select_block(
            block,
            &[
                Instruction {
                    opcode: Opcode::Imul,
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: opcode.clone(),
                    args: args.to_vec(),
                    results: vec![Value(4)],
                },
            ],
        );
        if !matches!(&result, Err(ISelError::IntegerArithmeticOperands { .. }))
            || !selector.func.blocks[&block].insts.is_empty()
        {
            problems.push(format!(
                "{opcode:?} {args:?} mul fold: {result:?}, {:?}",
                selector.func.blocks[&block].insts
            ));
        }
    }
    eprintln!("A64_AGGREGATE_FOLDS cells=7 problems={}", problems.len());
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// The adapter spells a GEP's `base + index * stride` as `Imul` feeding a
/// byte-stride `ArrayGep`. With a numeric I64 base that is one MADD, the
/// shape the AArch64 address and induction-store rewrites read
/// (`trust-cg-llvm-import` `ary3_init_o2_e2e`); any other base or width
/// keeps the explicit MUL and ADD, and no base ever selects a narrow MADD.
#[test]
fn byte_address_with_a_one_use_product_selects_one_i64_madd() {
    let aggregate = Type::Struct(vec![Type::I8, Type::I64, Type::I16]);
    let gep = |base: Value| {
        [
            Instruction {
                opcode: Opcode::Imul,
                args: vec![Value(0), Value(1)],
                results: vec![Value(3)],
            },
            Instruction {
                opcode: Opcode::ArrayGep { elem_ty: Type::I8 },
                args: vec![base, Value(3)],
                results: vec![Value(4)],
            },
        ]
    };
    let opcodes = |selector: &InstructionSelector, block: Block| {
        selector.func.blocks[&block]
            .insts
            .iter()
            .map(|inst| inst.opcode)
            .collect::<Vec<_>>()
    };

    // Index, stride and base all I64: one MADD [dst, index, stride, base].
    let (mut fused, block) = selector(&[Type::I64, Type::I64, Type::I64]);
    fused
        .select_block(block, &gep(Value(2)))
        .expect("an I64 byte address selects");
    let insts = &fused.func.blocks[&block].insts;
    assert_eq!(opcodes(&fused, block), [AArch64Opcode::Madd], "{insts:?}");
    let operand = |value: u32| fused.value_map[&Value(value)].clone();
    assert_eq!(
        insts[0].operands[1..],
        [operand(0), operand(1), operand(2)],
        "MADD reads index * stride + base: {insts:?}"
    );
    assert_eq!(fused.value_map[&Value(4)], insts[0].operands[0]);
    assert_eq!(fused.value_types[&Value(4)], Type::I64);

    // A base that is not a numeric I64, or a narrower product, keeps the
    // explicit multiply and the address add.
    for types in [
        [Type::I64, Type::I64, aggregate.clone()],
        [Type::I32, Type::I32, Type::I32],
    ] {
        let (mut unfused, block) = selector(&types);
        let result = unfused.select_block(block, &gep(Value(2)));
        let emitted = opcodes(&unfused, block);
        assert!(
            result.is_ok()
                && emitted.contains(&AArch64Opcode::MulRR)
                && emitted.contains(&AArch64Opcode::AddRR)
                && !emitted.contains(&AArch64Opcode::Madd),
            "{types:?}: {result:?}, {emitted:?}"
        );
    }

    // A product with a second reader stays a standalone MUL.
    let (mut shared_product, block) = selector(&[Type::I64, Type::I64, Type::I64]);
    let mut shared = gep(Value(2)).to_vec();
    shared.push(Instruction {
        opcode: Opcode::Iadd,
        args: vec![Value(3), Value(0)],
        results: vec![Value(5)],
    });
    shared_product
        .select_block(block, &shared)
        .expect("a shared product selects");
    assert!(
        !opcodes(&shared_product, block).contains(&AArch64Opcode::Madd),
        "{:?}",
        shared_product.func.blocks[&block].insts
    );
}
