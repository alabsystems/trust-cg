//! Public standalone AArch64 lowering must reject unrecognized pseudo flags.
//!
//! These are exact byte/admission tests, not native-execution or proof claims.
//! The main Pipeline does not call these standalone helpers. Its independent
//! emission paths and ownership semantics are outside this regression target.

use trust_cg_codegen::lower::{
    LowerError, LowerResult, encode_function, lower_function, lower_function_no_frame,
};
use trust_cg_ir::function::{MachFunction, Signature, Type};
use trust_cg_ir::inst::{AArch64Opcode as Op, InstFlags, MachInst};
use trust_cg_ir::operand::MachOperand as Arg;
use trust_cg_ir::regs::{B0, D0, H0, NZCV, PReg, S0, V0, W0, X0, X1};

type LowerApi = fn(&mut MachFunction) -> Result<LowerResult, LowerError>;
const APIS: [(&str, LowerApi); 2] = [
    ("lower_function", lower_function),
    ("lower_function_no_frame", lower_function_no_frame),
];

fn function(name: &str, instructions: Vec<MachInst>) -> MachFunction {
    let mut function = MachFunction::new(
        name.into(),
        Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]),
    );
    for instruction in instructions {
        let id = function.push_inst(instruction);
        function.append_inst(function.entry, id);
    }
    let ret = MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[X0]);
    let id = function.push_inst(ret);
    function.append_inst(function.entry, id);
    function
}

fn words(bytes: &[u8]) -> Vec<u32> {
    assert_eq!(bytes.len() % 4, 0);
    bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|word| u32::from_le_bytes(*word))
        .collect()
}

#[test]
fn unknown_pseudos_fail_closed_in_both_public_lowering_apis() {
    let controls = [
        (
            MachInst::new(Op::AddRI, vec![Arg::PReg(X0), Arg::PReg(X0), Arg::Imm(1)]),
            0x91000400, // ADD X0, X0, #1
        ),
        (
            MachInst::new(Op::StrRI, vec![Arg::PReg(X0), Arg::PReg(X1), Arg::Imm(0)]),
            0xF9000020, // STR X0, [X1]
        ),
        (
            MachInst::new(Op::Brk, vec![Arg::Imm(1)]),
            0xD4200020, // BRK #1
        ),
    ];
    for (name, lower) in APIS {
        for (control, word) in &controls {
            let mut valid = function("valid_semantic_instruction", vec![control.clone()]);
            let result = lower(&mut valid).unwrap();
            assert_eq!(words(&result.code), vec![*word, 0xD65F03C0], "{name}");

            // Public MachInst flags are mutable. Their inconsistency with a
            // real opcode must be an error, never permission to erase it.
            let mut mutant = control.clone();
            mutant.flags = mutant.flags.union(InstFlags::IS_PSEUDO);
            let original = mutant.clone();
            let mut invalid = function("unknown_pseudo_instruction", vec![mutant]);
            assert!(
                matches!(
                    lower(&mut invalid),
                    Err(LowerError::UnresolvedPseudo(opcode)) if opcode == original.opcode
                ),
                "{name}: {:?} must not be silently erased",
                original.opcode
            );
            assert_eq!(invalid.insts[0].opcode, original.opcode, "{name}");
            assert_eq!(invalid.insts[0].operands, original.operands, "{name}");
            assert_eq!(invalid.insts[0].flags, original.flags, "{name}");
        }
    }
}

#[test]
fn named_copy_metadata_and_guard_survive_both_public_lowering_apis() {
    for (name, lower) in APIS {
        let mut input = function(
            "named_copy_metadata_guard",
            vec![
                MachInst::new(Op::Nop, vec![]),
                MachInst::new(Op::Copy, vec![Arg::PReg(X0), Arg::PReg(X0)]),
                MachInst::new(Op::Copy, vec![Arg::PReg(X0), Arg::PReg(X1)]),
                MachInst::new(Op::TrapNullIfZero, vec![Arg::PReg(X0)]),
            ],
        );
        let result = lower(&mut input).unwrap();
        assert_eq!(
            words(&result.code),
            vec![
                0xAA0103E0, // MOV X0, X1
                0xB5000040, // CBNZ X0, +2
                0xD4200020, // BRK #1
                0xD65F03C0, // RET
            ],
            "{name}"
        );
    }
}

#[test]
fn unknown_pseudos_fail_closed_in_direct_encode_function() {
    for (control, word) in [
        (
            MachInst::new(Op::AddRI, vec![Arg::PReg(X0), Arg::PReg(X0), Arg::Imm(1)]),
            0x91000400,
        ),
        (
            MachInst::new(Op::StrRI, vec![Arg::PReg(X0), Arg::PReg(X1), Arg::Imm(0)]),
            0xF9000020,
        ),
        (MachInst::new(Op::Brk, vec![Arg::Imm(1)]), 0xD4200020),
        (MachInst::new(Op::AlignNop, vec![]), 0xD503201F),
    ] {
        let valid = function("direct_valid", vec![control.clone()]);
        assert_eq!(
            words(&encode_function(&valid).unwrap()),
            vec![word, 0xD65F03C0]
        );

        let mut mutant = control;
        mutant.flags = mutant.flags.union(InstFlags::IS_PSEUDO);
        let original = mutant.clone();
        // A valid prefix must not turn a later failure into partial success.
        let invalid = function(
            "direct_unknown_pseudo",
            vec![
                MachInst::new(Op::AddRI, vec![Arg::PReg(X0), Arg::PReg(X0), Arg::Imm(1)]),
                mutant,
            ],
        );
        assert!(matches!(
            encode_function(&invalid),
            Err(LowerError::UnresolvedPseudo(opcode)) if opcode == original.opcode
        ));
        assert_eq!(invalid.insts[1].opcode, original.opcode);
        assert_eq!(invalid.insts[1].operands, original.operands);
        assert_eq!(invalid.insts[1].flags, original.flags);
    }
}

#[test]
fn direct_encoding_rejects_unresolved_or_malformed_copies_even_without_pseudo_flag() {
    for operands in [
        vec![Arg::PReg(X0), Arg::PReg(X1)],
        vec![],
        vec![Arg::PReg(X0)],
        vec![Arg::PReg(X0), Arg::PReg(W0)],
        vec![Arg::PReg(X0), Arg::PReg(D0)],
        vec![Arg::PReg(S0), Arg::PReg(D0)],
        vec![Arg::Imm(7), Arg::Imm(7)],
        vec![Arg::PReg(X0), Arg::PReg(X0), Arg::Imm(0)],
        vec![Arg::PReg(NZCV), Arg::PReg(NZCV)],
        vec![Arg::PReg(PReg::new(65535)), Arg::PReg(PReg::new(65535))],
    ] {
        for flags in [InstFlags::IS_PSEUDO, InstFlags::EMPTY] {
            let mut copy = MachInst::new(Op::Copy, operands.clone());
            copy.flags = flags;
            let input = function("direct_unresolved_copy", vec![copy]);
            assert!(
                matches!(
                    encode_function(&input),
                    Err(LowerError::UnresolvedPseudo(Op::Copy))
                ),
                "must reject copy operands {operands:?}, flags {flags:?}"
            );
            assert_eq!(input.insts[0].opcode, Op::Copy);
            assert_eq!(input.insts[0].operands, operands);
            assert_eq!(input.insts[0].flags, flags);
        }
    }
}

#[test]
fn direct_encoding_preserves_real_traps_and_rejects_pseudo_erasure() {
    // These traps are unconditional terminators, so a real control has no
    // following RET in the same block. Keep the structural gate meaningful.
    let trap_function = |instruction: MachInst| {
        let mut input = MachFunction::new("direct_trap".into(), Signature::new(vec![], vec![]));
        let id = input.push_inst(instruction);
        input.append_inst(input.entry, id);
        input
    };
    for opcode in [
        Op::TrapOverflow,
        Op::TrapBoundsCheck,
        Op::TrapNull,
        Op::TrapDivZero,
        Op::TrapShiftRange,
    ] {
        let control = MachInst::new(opcode, vec![]);
        let input = trap_function(control.clone());
        assert_eq!(words(&encode_function(&input).unwrap()), vec![0xD4200020]);
        let mut mutant = control;
        mutant.flags = mutant.flags.union(InstFlags::IS_PSEUDO);
        let input = trap_function(mutant);
        assert!(matches!(
            encode_function(&input),
            Err(LowerError::UnresolvedPseudo(found)) if found == opcode
        ));
    }
    for (opcode, operands) in [
        (Op::TrapNullIfZero, vec![Arg::PReg(X0)]),
        (Op::TrapDivZeroIfZero, vec![Arg::PReg(X0)]),
        (Op::TrapShiftRangeIfOOB, vec![Arg::PReg(X0), Arg::Imm(64)]),
        (
            Op::TrapBoundsCheckExact,
            vec![Arg::PReg(X0), Arg::PReg(X1), Arg::Imm(8)],
        ),
        (
            Op::TrapOverflowExact,
            vec![Arg::PReg(X0), Arg::PReg(X1), Arg::Imm(0)],
        ),
    ] {
        for flagged in [false, true] {
            let mut carrier = MachInst::new(opcode, operands.clone());
            if flagged {
                carrier.flags = carrier.flags.union(InstFlags::IS_PSEUDO);
            }
            let input = trap_function(carrier);
            assert!(matches!(
                encode_function(&input),
                Err(LowerError::UnresolvedPseudo(found)) if found == opcode
            ));
        }
    }
}

#[test]
fn direct_encoding_preserves_named_metadata_refcount_and_exact_identity_bytes() {
    // These named erasures are existing compatibility behavior, not a claim
    // that surviving Phi/StackAlloc or ownership operations are semantically
    // complete. Preserve both their zero-byte pseudo and real-NOP spellings.
    for opcode in [Op::Phi, Op::StackAlloc, Op::Nop, Op::Retain, Op::Release] {
        for flagged in [false, true] {
            let mut instruction = MachInst::new(opcode, vec![]);
            instruction.flags = if flagged {
                InstFlags::IS_PSEUDO
            } else {
                InstFlags::EMPTY
            };
            let input = function("direct_named_metadata", vec![instruction]);
            let expected = if flagged {
                vec![0xD65F03C0]
            } else {
                vec![0xD503201F, 0xD65F03C0]
            };
            assert_eq!(
                words(&encode_function(&input).unwrap()),
                expected,
                "{opcode:?}, flagged={flagged}"
            );
        }
    }
    for register in [X0, W0, V0, D0, S0, H0, B0] {
        for flagged in [false, true] {
            let mut copy = MachInst::new(Op::Copy, vec![Arg::PReg(register), Arg::PReg(register)]);
            copy.flags = if flagged {
                InstFlags::IS_PSEUDO
            } else {
                InstFlags::EMPTY
            };
            let input = function("direct_identity_copy", vec![copy]);
            let expected = if flagged {
                vec![0xD65F03C0]
            } else {
                vec![0xD503201F, 0xD65F03C0]
            };
            assert_eq!(
                words(&encode_function(&input).unwrap()),
                expected,
                "{register:?}, flagged={flagged}"
            );
        }
    }
}
