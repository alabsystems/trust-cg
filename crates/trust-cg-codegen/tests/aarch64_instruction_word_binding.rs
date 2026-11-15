// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! The per-compile binding of the verifier's instruction-derived obligations
//! (`trust_cg_verify::aarch64_instruction_word_proofs`, ledger L07-P2) to the
//! words the encoder emits.
//!
//! * For every admitted shape enumerated here, the live encoder's word is the
//!   verifier's re-derived word outside its hole bits, ENC-5 accepts it, and
//!   the obligation over it holds. An admitted shape the encoder rejected, or
//!   a different word, would fail ENC-5 in its default `enforce` mode.
//! * ENC-5 refuses a word that differs from the re-derived one, naming the
//!   binding.
//! * Native execution: programs whose instructions are the admitted families
//!   (move-wide constants, register copies, stack adjustments, compares and
//!   conditional branches, shifted-register adds, UMULH, direct calls, scalar
//!   loads and stores) compile through the JIT at O0 and O2 with the binding
//!   enforced and return what the same computation returns in Rust (the host
//!   compiler, LLVM) on every input of a battery.
//! * The raw MOVZ obligation holds but supplies no proof credit. The same
//!   constant publishes on the object and JIT routes only through an
//!   independently replayed source-bound body theorem. Evaluation-only source
//!   binding stays uncredited, and changed machine input does not match the
//!   retained source-bound export.
//!
//! These are tests of the encoder, verifier and publication boundary. A
//! production compile's credit comes from its independently checked replay;
//! the instruction-word equation by itself never grants that credit.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

#[cfg(feature = "verify")]
#[path = "common/function_words.rs"]
mod function_words;

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, Target};
use trust_cg_ir::{AArch64Opcode as Op, BlockId, MachInst, MachOperand as Arg, PReg, SpecialReg};
use trust_cg_verify::aarch64_instruction_word_proofs::{
    INSTRUCTION_WORD_OPCODES, Outcome, check_emitted_instruction_word, instruction_word,
    instruction_word_verdict,
};
use trust_cg_verify::lowering_proof::VerificationConfig;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

fn preg(n: u16) -> Arg {
    Arg::PReg(PReg::new(n))
}

/// A general-purpose register operand spelling for every view the encoder
/// accepts: X/W numbered registers, SP and ZR as physical registers and as
/// special registers, and one FP register the GPR forms must not admit.
fn registers() -> Vec<Arg> {
    vec![
        preg(0),
        preg(7),
        preg(29),
        preg(30),
        preg(31),
        preg(32),
        preg(37),
        preg(62),
        preg(63),
        preg(160),
        preg(161),
        preg(96),
        Arg::Special(SpecialReg::SP),
        Arg::Special(SpecialReg::XZR),
        Arg::Special(SpecialReg::WZR),
    ]
}

fn imm(value: i64) -> Arg {
    Arg::Imm(value)
}

/// Every instruction shape this test enumerates.
fn shapes() -> Vec<MachInst> {
    let regs = registers();
    let few: Vec<Arg> = vec![
        preg(1),
        preg(33),
        preg(31),
        preg(160),
        Arg::Special(SpecialReg::SP),
        Arg::Special(SpecialReg::WZR),
    ];
    let mut out = Vec::new();
    for opcode in [
        Op::Movz,
        Op::MovI,
        Op::MOVZWi,
        Op::MOVZXi,
        Op::Movn,
        Op::Movk,
    ] {
        for dst in &regs {
            for value in [0, 1, 0x1234, 0xffff, 0x1_0000, -1] {
                out.push(MachInst::new(opcode, vec![dst.clone(), imm(value)]));
                for shift in [0, 8, 16, 32, 48] {
                    out.push(MachInst::new(
                        opcode,
                        vec![dst.clone(), imm(value), imm(shift)],
                    ));
                }
            }
        }
    }
    for opcode in [Op::MovR, Op::MOVWrr, Op::MOVXrr] {
        for dst in &regs {
            for src in &regs {
                out.push(MachInst::new(opcode, vec![dst.clone(), src.clone()]));
            }
        }
    }
    for opcode in [Op::AddRI, Op::SubRI] {
        for dst in &regs {
            for src in &few {
                for value in [0, 1, 16, 4095, 4096, -1] {
                    out.push(MachInst::new(
                        opcode,
                        vec![dst.clone(), src.clone(), imm(value)],
                    ));
                }
            }
        }
    }
    for opcode in [Op::CmpRI, Op::CMPWri, Op::CMPXri] {
        for src in &regs {
            for value in [0, 1, 64, 4095, 4096] {
                out.push(MachInst::new(opcode, vec![src.clone(), imm(value)]));
            }
        }
    }
    for opcode in [Op::CmpRR, Op::CMPWrr, Op::CMPXrr] {
        for lhs in &regs {
            for rhs in &regs {
                out.push(MachInst::new(opcode, vec![lhs.clone(), rhs.clone()]));
            }
        }
    }
    for opcode in [
        Op::AddRRShift,
        Op::SubRRShift,
        Op::AddRRShiftLsr,
        Op::EorRRShift,
    ] {
        for dst in &regs {
            for lhs in &few {
                for rhs in &few {
                    for amount in [0, 1, 31, 32, 63] {
                        out.push(MachInst::new(
                            opcode,
                            vec![dst.clone(), lhs.clone(), rhs.clone(), imm(amount)],
                        ));
                    }
                }
            }
        }
    }
    for dst in &regs {
        for lhs in &few {
            for rhs in &few {
                out.push(MachInst::new(
                    Op::Umulh,
                    vec![dst.clone(), lhs.clone(), rhs.clone()],
                ));
            }
        }
    }
    for opcode in [Op::B, Op::TailCall, Op::Bl, Op::BL] {
        for offset in [0, 1, -1, (1 << 25) - 1, -(1 << 25), 1 << 25] {
            out.push(MachInst::new(opcode, vec![imm(offset)]));
        }
    }
    for opcode in [Op::BCond, Op::Bcc] {
        for cc in 0..16 {
            for offset in [0, 3, -2, (1 << 18) - 1, -(1 << 18), 1 << 18] {
                out.push(MachInst::new(opcode, vec![imm(cc), imm(offset)]));
            }
        }
    }
    let bases: Vec<Arg> = vec![
        preg(1),
        preg(29),
        preg(31),
        preg(33),
        preg(160),
        Arg::Special(SpecialReg::SP),
    ];
    for opcode in [
        Op::LdrRI,
        Op::StrRI,
        Op::LdrbRI,
        Op::StrbRI,
        Op::LdrhRI,
        Op::StrhRI,
        Op::LdrsbRI,
        Op::LdrshRI,
    ] {
        for data in &regs {
            for base in &bases {
                out.push(MachInst::new(opcode, vec![data.clone(), base.clone()]));
                for offset in [
                    0, 1, 2, 3, 4, 8, -1, -8, -256, -257, 255, 256, 4095, 8190, 32760, 32768,
                ] {
                    out.push(MachInst::new(
                        opcode,
                        vec![data.clone(), base.clone(), imm(offset)],
                    ));
                    if let Arg::PReg(base) = base {
                        out.push(MachInst::new(
                            opcode,
                            vec![
                                data.clone(),
                                Arg::MemOp {
                                    base: *base,
                                    offset,
                                },
                            ],
                        ));
                    }
                }
            }
        }
    }
    // Writeback: every transfer view against every base, the imm9 edges and
    // one step past them.
    for opcode in [
        Op::LdrPreIndex,
        Op::StrPreIndex,
        Op::LdrPostIndex,
        Op::StrPostIndex,
    ] {
        for data in &regs {
            for base in &bases {
                for offset in [0, 1, -1, 8, -16, 255, -256, 256, -257] {
                    out.push(MachInst::new(
                        opcode,
                        vec![data.clone(), base.clone(), imm(offset)],
                    ));
                }
                out.push(MachInst::new(opcode, vec![data.clone(), base.clone()]));
            }
        }
    }
    // Register offset: transfer views, bases, index views (W, X, both zero
    // registers, SP, an FP register) and every mode immediate the encoder
    // admits, the implicit one and three it refuses.
    let data_regs: Vec<Arg> = vec![
        preg(0),
        preg(30),
        preg(37),
        preg(31),
        preg(160),
        preg(161),
        preg(96),
        Arg::Special(SpecialReg::XZR),
    ];
    let indexes: Vec<Arg> = vec![
        preg(2),
        preg(34),
        preg(160),
        preg(161),
        preg(31),
        preg(96),
        Arg::Special(SpecialReg::WZR),
    ];
    for opcode in [
        Op::LdrRO,
        Op::StrRO,
        Op::LdrbRO,
        Op::LdrhRO,
        Op::StrbRO,
        Op::StrhRO,
        Op::LdrswRO,
    ] {
        for data in &data_regs {
            for base in &bases {
                for index in &indexes {
                    out.push(MachInst::new(
                        opcode,
                        vec![data.clone(), base.clone(), index.clone()],
                    ));
                    for mode in [4, 5, 6, 7, 12, 13, 14, 15, 0, 8, 16] {
                        out.push(MachInst::new(
                            opcode,
                            vec![data.clone(), base.clone(), index.clone(), imm(mode)],
                        ));
                    }
                }
            }
        }
    }
    out
}

#[test]
fn live_encoder_words_are_the_verifier_words_for_every_admitted_shape() {
    let config = VerificationConfig::default();
    let mut admitted: HashMap<Op, usize> = HashMap::new();
    let mut failures = Vec::new();
    let shapes = shapes();
    for inst in &shapes {
        let Some(derived) = instruction_word(inst) else {
            continue;
        };
        *admitted.entry(inst.opcode).or_default() += 1;
        let word = match encode_instruction(inst) {
            Ok(word) => word,
            Err(error) => {
                failures.push(format!(
                    "{inst:?}: admitted but the encoder refuses: {error:?}"
                ));
                continue;
            }
        };
        if word & !derived.hole_mask != derived.word {
            failures.push(format!(
                "{inst:?}: encoder {word:#010x}, verifier {:#010x}",
                derived.word
            ));
            continue;
        }
        if check_emitted_instruction_word(inst, word) != Some(Ok(())) {
            failures.push(format!("{inst:?}: binding rejects the encoder word"));
        }
        let outcome = A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None);
        if !matches!(outcome, DecodeCheckOutcome::Match) {
            failures.push(format!("{inst:?} {word:#010x}: ENC-5 {outcome:?}"));
        }
        match instruction_word_verdict(inst, &config).map(|verdict| verdict.outcome) {
            Some(Outcome::Holds(_)) => {}
            other => failures.push(format!("{inst:?}: obligation {other:?}")),
        }
    }
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    // Every listed opcode reached the enumeration with admitted shapes, and
    // the enumeration keeps its size: a shrinking admission is a change to
    // review, not a silent pass.
    let missing: Vec<Op> = INSTRUCTION_WORD_OPCODES
        .iter()
        .copied()
        .filter(|opcode| !admitted.contains_key(opcode))
        .collect();
    assert_eq!(missing, Vec::<Op>::new());
    let mut breakdown: Vec<(String, usize)> = admitted
        .iter()
        .map(|(opcode, count)| (format!("{opcode:?}"), *count))
        .collect();
    breakdown.sort();
    eprintln!("INSTRUCTION_WORD_ADMITTED {breakdown:?}");
    let total: usize = admitted.values().sum();
    assert_eq!((total, shapes.len()), (18_472, 71_115));
}

#[test]
fn add_sub_mixed_width_shapes_are_not_instruction_word_evidence() {
    let mut refused = 0;
    for inst in shapes() {
        if !matches!(inst.opcode, Op::AddRI | Op::SubRI) {
            continue;
        }
        let width = |arg: &Arg| match arg {
            Arg::PReg(p) if p.encoding() <= 31 => Some(64),
            Arg::PReg(p) if (32..=63).contains(&p.encoding()) => Some(32),
            Arg::Special(SpecialReg::SP) => Some(64),
            _ => None,
        };
        if let (Some(dst), Some(src), Arg::Imm(0..=4095)) = (
            width(&inst.operands[0]),
            width(&inst.operands[1]),
            &inst.operands[2],
        ) && dst != src
        {
            assert!(instruction_word(&inst).is_none(), "{inst:?}");
            refused += 1;
        }
    }
    assert_eq!(refused, 144);
}

#[test]
fn enc5_refuses_a_word_the_verifier_did_not_re_derive() {
    for (inst, word) in [
        (
            MachInst::new(Op::Movz, vec![preg(3), imm(0x1234)]),
            0xd282_4683u32,
        ),
        (
            MachInst::new(Op::CmpRI, vec![preg(34), imm(64)]),
            0x7101_005f,
        ),
        (
            MachInst::new(
                Op::LdrRI,
                vec![
                    preg(1),
                    Arg::MemOp {
                        base: PReg::new(31),
                        offset: 16,
                    },
                ],
            ),
            0xf940_0be1,
        ),
        (MachInst::new(Op::BCond, vec![imm(1), imm(3)]), 0x5400_0061),
    ] {
        assert!(matches!(
            A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None),
            DecodeCheckOutcome::Match
        ));
        for bit in [0, 5, 12, 22, 30] {
            let corrupted = word ^ (1 << bit);
            match A64DecodeCheck.check_one(&inst, &corrupted.to_le_bytes(), None) {
                DecodeCheckOutcome::Mismatch(error) => assert!(
                    error
                        .message
                        .contains("is not the verifier's re-derived word"),
                    "{inst:?} bit {bit}: {}",
                    error.message
                ),
                other => panic!("{inst:?} bit {bit}: {other:?}"),
            }
        }
    }
    // A branch to a symbolic target: the displacement bits are the fixup's.
    let call = MachInst::new(Op::Bl, vec![Arg::Symbol("callee".into())]);
    assert_eq!(
        check_emitted_instruction_word(&call, 0x9400_1234),
        Some(Ok(()))
    );
    let block = MachInst::new(Op::BCond, vec![imm(0), Arg::Block(BlockId(2))]);
    assert_eq!(
        check_emitted_instruction_word(&block, 0x5400_0460),
        Some(Ok(()))
    );
    assert!(matches!(
        check_emitted_instruction_word(&block, 0x5400_0461),
        Some(Err(_))
    ));
}

/// The functions the native test compiles, in this order.
const WIDE_CONSTANT: u64 = 0x1234_5678_9abc_def0;

fn native_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_instruction_word_binding");
    let unit = mb.add_func_type(vec![], vec![Ty::I64]);
    let one = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let two = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let ptr_one = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    {
        // 0: a wide constant (MOVZ + MOVK chain).
        let mut fb = mb.function("wide_constant", unit);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = fb.iconst(Ty::I64, i128::from(WIDE_CONSTANT as i64));
        fb.ret(vec![value]);
        fb.build();
    }
    {
        // 1: a small negative constant (MOVN).
        let mut fb = mb.function("negative_constant", unit);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = fb.iconst(Ty::I64, -2);
        fb.ret(vec![value]);
        fb.build();
    }
    {
        // 2: `a + (b >> 7) - (b << 3)` (shifted-register add/sub).
        let mut fb = mb.function("shifted_mix", two);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let seven = fb.iconst(Ty::I64, 7);
        let three = fb.iconst(Ty::I64, 3);
        let high = fb.binop(BinOp::LShr, Ty::I64, b, seven);
        let low = fb.binop(BinOp::Shl, Ty::I64, b, three);
        let sum = fb.add(Ty::I64, a, high);
        let result = fb.sub(Ty::I64, sum, low);
        fb.ret(vec![result]);
        fb.build();
    }
    {
        // 3: `a % 7` unsigned (UMULH by a magic constant).
        let mut fb = mb.function("rem_seven", one);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let seven = fb.iconst(Ty::I64, 7);
        let result = fb.binop(BinOp::URem, Ty::I64, a, seven);
        fb.ret(vec![result]);
        fb.build();
    }
    {
        // 4: `sum of 0..n` for signed n (CMP, B.cond, B).
        let mut fb = mb.function("triangle", one);
        let entry = fb.create_block();
        let head = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        let n = fb.add_block_param(entry, Ty::I64);
        let i = fb.add_block_param(head, Ty::I64);
        let acc = fb.add_block_param(head, Ty::I64);
        let total = fb.add_block_param(exit, Ty::I64);
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        fb.br(head, vec![zero, zero]);
        fb.switch_to_block(head);
        let more = fb.icmp(ICmpOp::Slt, Ty::I64, i, n);
        fb.condbr(more, body, vec![], exit, vec![acc]);
        fb.switch_to_block(body);
        let next_acc = fb.add(Ty::I64, acc, i);
        let one_value = fb.iconst(Ty::I64, 1);
        let next_i = fb.add(Ty::I64, i, one_value);
        fb.br(head, vec![next_i, next_acc]);
        fb.switch_to_block(exit);
        fb.ret(vec![total]);
        fb.build();
    }
    {
        // 5: store `v` at `p + 8`, return `p[1] + p[0]` (scalar STR/LDR).
        let mut fb = mb.function("store_load", ptr_one);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        let v = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let one_index = fb.iconst(Ty::I64, 1);
        let slot = fb.gep(Ty::I64, p, vec![one_index]);
        fb.store(Ty::I64, slot, v);
        let stored = fb.load(Ty::I64, slot);
        let first = fb.load(Ty::I64, p);
        let result = fb.add(Ty::I64, stored, first);
        fb.ret(vec![result]);
        fb.build();
    }
    {
        // 6: `wide_constant() ^ rem_seven(a)` (BL, register copies).
        let mut fb = mb.function("caller", one);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let wide = fb.call(trust_ir::FuncId::new(0), vec![]);
        let rem = fb.call(trust_ir::FuncId::new(3), vec![a]);
        let result = fb.binop(BinOp::Xor, Ty::I64, wide, rem);
        fb.ret(vec![result]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn inputs() -> Vec<i64> {
    let mut values = vec![
        0,
        1,
        2,
        6,
        7,
        8,
        63,
        64,
        100,
        1000,
        -1,
        -7,
        i64::MAX,
        i64::MIN,
    ];
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    for _ in 0..32 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        values.push(state as i64);
    }
    values
}

#[test]
fn native_programs_compile_with_the_binding_enforced_and_match_the_host() {
    let module = native_module();
    for level in [OptLevel::O0, OptLevel::O2] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = level;
        let jit = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| panic!("{level:?}: {error}"));
        let buffer = jit.buffer;
        let function = |name: &str| {
            buffer
                .get_fn_ptr_bound(name)
                .unwrap_or_else(|| panic!("{name} missing"))
                .as_ptr()
        };
        // SAFETY: each symbol is the function of the matching signature
        // compiled above, and the buffer outlives every call.
        let wide: extern "C" fn() -> i64 =
            unsafe { std::mem::transmute(function("wide_constant")) };
        let negative: extern "C" fn() -> i64 =
            unsafe { std::mem::transmute(function("negative_constant")) };
        let shifted: extern "C" fn(i64, i64) -> i64 =
            unsafe { std::mem::transmute(function("shifted_mix")) };
        let rem: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(function("rem_seven")) };
        let triangle: extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(function("triangle")) };
        let store_load: extern "C" fn(*mut i64, i64) -> i64 =
            unsafe { std::mem::transmute(function("store_load")) };
        let caller: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(function("caller")) };

        assert_eq!(wide() as u64, WIDE_CONSTANT, "{level:?}");
        assert_eq!(negative(), -2, "{level:?}");
        for a in inputs() {
            let expected_rem = ((a as u64) % 7) as i64;
            assert_eq!(rem(a), expected_rem, "{level:?} rem_seven({a})");
            assert_eq!(
                caller(a),
                (WIDE_CONSTANT as i64) ^ expected_rem,
                "{level:?} caller({a})"
            );
            for b in inputs().into_iter().take(12) {
                let expected = a
                    .wrapping_add(((b as u64) >> 7) as i64)
                    .wrapping_sub(b.wrapping_shl(3));
                assert_eq!(shifted(a, b), expected, "{level:?} shifted_mix({a}, {b})");
            }
            let mut cells = [a.wrapping_mul(3), 0];
            assert_eq!(
                store_load(cells.as_mut_ptr(), a),
                a.wrapping_add(a.wrapping_mul(3)),
                "{level:?} store_load({a})"
            );
            assert_eq!(cells[1], a, "{level:?}: the store landed at p + 8");
        }
        for n in [-5i64, 0, 1, 2, 10, 64, 1000] {
            let expected: i64 = (0..n.max(0)).sum();
            assert_eq!(triangle(n), expected, "{level:?} triangle({n})");
        }
    }
}

/// Instruction-word equations alone remain uncredited. The actual constant
/// leaf can publish only through the source-bound whole-body replay, whose
/// export must remain bound to the exact LIR and final allocated instructions.
#[cfg(feature = "verify")]
#[test]
fn proof_required_constant_uses_the_source_bound_body_owner() {
    use trust_cg_codegen::pipeline::{Pipeline, PipelineConfig};
    use trust_cg_verify::function_verifier::{
        INSTRUCTION_DERIVED_IS_NOT_CREDIT, InstructionOpcode, InstructionVerificationResult,
        REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT, verify_function,
    };
    use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
    use trust_cg_verify::source_bound_a64_body::{
        A64_BODY_NEEDS_REPLAY, A64_BODY_OBLIGATION_NAME, source_bound_a64_body,
    };
    use trust_cg_verify::{FunctionVerifier, SourceBoundObligationKind, VerificationConfig};

    let artifacts =
        std::env::var_os("TCG_CONSTANT_BODY_ARTIFACT_DIR").map(std::path::PathBuf::from);
    if let Some(path) = &artifacts {
        std::fs::create_dir_all(path).unwrap();
    }
    let save = |name: &str, bytes: &[u8]| {
        if let Some(path) = &artifacts {
            std::fs::write(path.join(name), bytes).unwrap();
        }
    };
    let mut mb = ModuleBuilder::new("instruction_word_fires");
    let unit = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("small_constant", unit);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let value = fb.iconst(Ty::I64, 0x1234);
    fb.ret(vec![value]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let (lir, context) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .expect("the constant fixture must translate");
    let triple = if cfg!(target_os = "macos") {
        "aarch64-apple-darwin"
    } else {
        "aarch64-unknown-linux-gnu"
    };
    let mut pipeline_config = PipelineConfig::for_target(triple);
    pipeline_config.opt_level = OptLevel::O0;
    let (machine, _) = Pipeline::new(pipeline_config)
        .with_proof_grade_aarch64_publication_if(true)
        .prepare_function_with_metrics(&lir, Some(&context))
        .expect("the constant fixture must lower");
    let owner = source_bound_a64_body(&lir, &machine).expect("actual source/body owner");
    assert_eq!(owner.obligation().name, A64_BODY_OBLIGATION_NAME);
    assert_eq!(owner.copies_and_constants().len(), 1);
    save("source.txt", format!("{module:#?}").as_bytes());
    save("lir.txt", format!("{lir:#?}").as_bytes());
    save("machine.txt", format!("{machine:#?}").as_bytes());
    save(
        "body.smt2",
        trust_cg_verify::ay_bridge::generate_smt2_query_raw(
            owner.obligation(),
            &trust_cg_verify::ay_bridge::AYConfig::default(),
        )
        .as_bytes(),
    );

    // Neither the instruction-derived equation nor an evaluation-only
    // source/body binding is an independently replayed proof.
    let raw = verify_function(&machine);
    let movz_rows: Vec<_> = raw
        .instructions
        .iter()
        .filter(|row| row.opcode == InstructionOpcode::AArch64(Op::Movz))
        .collect();
    assert_eq!(movz_rows.len(), 1);
    let movz_reason = format!(
        "{INSTRUCTION_DERIVED_IS_NOT_CREDIT}: `A64 instruction word Movz 0xd2824680` holds \
         (decided in-process for every input by term identity or exact bit routing)"
    );
    match &movz_rows[0].result {
        InstructionVerificationResult::Unverified { reason } => assert!(
            reason.starts_with(&movz_reason)
                && !reason.contains(REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT),
            "{reason}",
        ),
        other => panic!("instruction-word agreement is not proof credit: {other:?}"),
    }
    assert!(!raw.emitted_opcode_inventory().is_promotable());
    save("raw-report.txt", format!("{raw:#?}").as_bytes());

    let evaluation_only = FunctionVerifier::with_config(VerificationConfig::default());
    let request = evaluation_only.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let (captured, exported) =
        evaluation_only.verify_with_request_for_export(&machine, Some(&lir), &request);
    let without_replay = captured.report();
    assert!(without_replay.precondition_failure.is_none());
    assert!(exported.is_empty());
    let uncredited = without_replay
        .instructions
        .iter()
        .find(|row| row.opcode == InstructionOpcode::AArch64(Op::Movz))
        .unwrap();
    match &uncredited.result {
        InstructionVerificationResult::Unverified { reason } => {
            assert!(reason.starts_with(&movz_reason), "{reason}");
        }
        other => panic!("source binding without replay is not proof credit: {other:?}"),
    }
    assert!(!without_replay.emitted_opcode_inventory().is_promotable());
    save(
        "evaluation-only-report.txt",
        format!("{without_replay:#?}").as_bytes(),
    );

    let compiled = Compiler::new(CompilerConfig {
        target: Target::Aarch64,
        opt_level: OptLevel::O0,
        emit_proofs: true,
        parallel: false,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    .expect("the genuine source-bound constant theorem must replay before publication");
    let words = function_words::function_words(&compiled.object_code);
    assert_eq!(words.len(), 1);
    assert_eq!(words["small_constant"], [0xd2824680, 0xd65f03c0]);
    let proofs = compiled
        .proofs
        .as_ref()
        .expect("proof-required compile has certificates");
    assert!(!proofs.is_empty());
    assert!(proofs.iter().all(|p| p.verified));
    save("object.o", &compiled.object_code);
    save("proofs.txt", format!("{proofs:#?}").as_bytes());
    let bound: Vec<_> = proofs
        .iter()
        .filter_map(|p| {
            (p.rule_name == A64_BODY_OBLIGATION_NAME)
                .then_some((p, p.source_bound_obligation.as_ref()))
        })
        .collect();
    assert!(
        !bound.is_empty(),
        "the body must not publish on unrelated proof rows"
    );
    for (certificate, payload) in bound {
        assert_eq!(certificate.strength, "Formal");
        assert_eq!(certificate.function_name, "small_constant");
        let payload = payload.expect("a claimed source-bound proof retains its exact export");
        assert_eq!(payload.kind(), SourceBoundObligationKind::A64Body);
        assert_eq!(payload.function_name(), "small_constant");
        assert!(payload.matches_aarch64_input(&machine, Some(&lir)));
        let mut changed = machine.clone();
        let row = &mut changed.insts[movz_rows[0].inst_index];
        let Arg::Imm(value) = &mut row.operands[1] else {
            panic!("MOVZ immediate")
        };
        *value ^= 1;
        assert!(!payload.matches_aarch64_input(&changed, Some(&lir)));
    }

    // A successful replay above must not let its cached evidence cross into
    // a compile whose captured policy explicitly disables that replay.
    // The closure returns the compiler's own error type unchanged.
    #[allow(clippy::result_large_err)]
    let refused =
        trust_cg_verify::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
            Compiler::new(CompilerConfig {
                target: Target::Aarch64,
                opt_level: OptLevel::O0,
                emit_proofs: true,
                parallel: false,
                ..CompilerConfig::default()
            })
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
        });
    save("disabled-result.txt", format!("{refused:#?}").as_bytes());
    match refused {
        Err(trust_cg_codegen::compiler::CompileError::ProofPromotionRejected {
            reason, ..
        }) => {
            assert!(reason.contains(A64_BODY_NEEDS_REPLAY), "{reason}");
        }
        other => {
            panic!("proof-disabled compile must refuse even after successful replay: {other:?}")
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        use trust_cg_codegen::compiler::JitValidationMode;
        let installed = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O0,
            emit_proofs: true,
            parallel: false,
            jit_validation_mode_override: Some(JitValidationMode::AlwaysVerify),
            ..CompilerConfig::jit_fast(Target::Aarch64)
        })
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("the same original constant source must pass proof-required JIT publication");
        assert!(
            installed
                .validation
                .as_ref()
                .unwrap()
                .every_function_semantics_verified()
        );
        assert!(installed.buffer.all_function_semantics_verified());
        let certificate = installed.buffer.certificate("small_constant").unwrap();
        assert!(certificate.has_checked_semantics());
        assert!(certificate.is_verified());
        save("jit-certificate.json", certificate.to_json().as_bytes());
        save("jit-code.bin", installed.buffer.code_slice());
        save(
            "jit-validation.txt",
            format!("{:?}", installed.validation).as_bytes(),
        );
        installed.buffer.verify_published_code_integrity().unwrap();
        let pointer = installed.buffer.get_fn_ptr_bound("small_constant").unwrap();
        // The ModuleBuilder signature is exactly C () -> i64; the owning
        // executable buffer remains alive throughout this call.
        let call: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(pointer.as_ptr()) };
        assert_eq!(unsafe { call() }, 0x1234);
    }
    println!(
        "CONSTANT_SOURCE_BOUND_PUBLICATION words=2 raw_inventory=uncredited no_replay=uncredited changed_machine=refused"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
