// Copyright 2026 Andrew Yates | Apache-2.0
//! ENC-5 coverage of the forms the backend emits (ledger L10-P6).
//!
//! * The committed census (`aarch64_enc5_floor_census/darwin_floor.tsv`) is a
//!   measurement: the Darwin floor run with `TCG_DECODE_CHECK_CENSUS_DIR`
//!   set, reduced by `scripts/enc5_floor_census.py`. It lists every opcode
//!   the floor corpus emitted, each one's ENC-5 outcome tally, and real
//!   emitted (intent, word) samples. The emitted and still-undecoded opcode
//!   lists are pinned here, so a re-measurement changes them deliberately.
//! * Every census sample is replayed through ENC-5 and must reproduce its
//!   recorded outcome; every scalar FP and Advanced SIMD sample must match,
//!   and every single-bit corruption of its real word (each operand field,
//!   size/type/Q bit and fixed opcode bit) must be a mismatch.
//! * Assembler-produced words (`clang -target arm64-apple-macos`, read back
//!   with `otool -tvj`), independent of both the encoder and ENC-5, decode
//!   to their intents with the same all-bits corruption control.
//! * The live encoder's words decode for the shapes enumerated here, including
//!   every W/X view assignment of the integer-slice forms listed (register
//!   allocation mixes views, and the integer width comes from one
//!   width-selecting operand or the opcode); mixed H/S/D scalar FP views are
//!   mismatches. TrustIR lowerings that produce mixed views or a
//!   half-precision FCMP compile on both routes.
//! * A proof-grade route refuses a word ENC-5 does not decode; a
//!   compatibility route counts it.
//!
//! All of it is testing evidence about the encoder and the independent
//! decoder: agreement is redundancy, not a proof against a formal ISA model.

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::decode_check::{
    DecodeCheck, DecodeCheckOutcome, FixupHole, FixupHoleKind, UNDECODED_EMISSION_REFUSAL_TAG,
};
use trust_cg_codegen::pipeline::{Pipeline, PipelineConfig, PipelineError};
use trust_cg_ir::function::{MachFunction, Signature, Type};
use trust_cg_ir::{AArch64Opcode as Op, BlockId, MachInst, MachOperand as Arg, PReg, SpecialReg};

const CENSUS: &str = include_str!("aarch64_enc5_floor_census/darwin_floor.tsv");
/// The same floor measured before L10-P6's slices (source 8a772301a).
const CENSUS_BEFORE_L10_P6: &str =
    include_str!("aarch64_enc5_floor_census/darwin_floor_before_l10p6.tsv");

fn v(n: u16) -> Arg {
    Arg::PReg(PReg::new(64 + n))
}
fn d(n: u16) -> Arg {
    Arg::PReg(PReg::new(96 + n))
}
fn s(n: u16) -> Arg {
    Arg::PReg(PReg::new(128 + n))
}
fn h(n: u16) -> Arg {
    Arg::PReg(PReg::new(165 + n))
}
fn x(n: u16) -> Arg {
    Arg::PReg(PReg::new(n))
}
fn w(n: u16) -> Arg {
    Arg::PReg(PReg::new(32 + n))
}
fn imm(value: i64) -> Arg {
    Arg::Imm(value)
}
fn fimm(value: f64) -> Arg {
    Arg::FImm(value)
}

fn check(inst: &MachInst, word: u32, hole: Option<&FixupHole>) -> DecodeCheckOutcome {
    A64DecodeCheck.check_one(inst, &word.to_le_bytes(), hole)
}

/// Every single-bit corruption of `word` must be a mismatch.
fn assert_every_bit_flip_mismatches(inst: &MachInst, word: u32, failures: &mut Vec<String>) {
    for bit in 0..32 {
        let mutant = word ^ (1 << bit);
        if !matches!(check(inst, mutant, None), DecodeCheckOutcome::Mismatch(_)) {
            failures.push(format!(
                "{:?} {:?}: bit {bit} flip {mutant:#010x} of {word:#010x} was not a mismatch",
                inst.opcode, inst.operands
            ));
        }
    }
}

/// The opcodes of ENC-5's scalar FP and Advanced SIMD slice.
fn is_fp_simd(opcode: Op) -> bool {
    let name = format!("{opcode:?}");
    (name.starts_with('F') && name != "FrameAlloc")
        || name.starts_with("Neon")
        || matches!(opcode, Op::ScvtfRR | Op::UcvtfRR)
}

/// Words assembled by clang for aarch64-apple-macos and disassembled with
/// `otool -tvj`, with the machine-IR intent each one spells.
fn assembler_rows() -> Vec<(MachInst, u32)> {
    let row = |opcode, operands: Vec<Arg>, word: u32| (MachInst::new(opcode, operands), word);
    vec![
        row(Op::FaddRR, vec![s(1), s(2), s(3)], 0x1e23_2841),
        row(Op::FaddRR, vec![d(31), d(0), d(17)], 0x1e71_281f),
        row(Op::FaddRR, vec![h(5), h(6), h(7)], 0x1ee7_28c5),
        row(Op::FsubRR, vec![d(1), d(2), d(3)], 0x1e63_3841),
        row(Op::FmulRR, vec![s(9), s(10), s(11)], 0x1e2b_0949),
        row(Op::FdivRR, vec![d(4), d(5), d(6)], 0x1e66_18a4),
        row(Op::FmaxnmRR, vec![s(1), s(2), s(3)], 0x1e23_6841),
        row(Op::FminnmRR, vec![d(29), d(30), d(31)], 0x1e7f_7bdd),
        row(Op::FmaddRR, vec![d(1), d(2), d(3), d(4)], 0x1f43_1041),
        row(Op::FmaddRR, vec![s(31), s(30), s(29), s(28)], 0x1f1d_73df),
        row(Op::FmovFprFpr, vec![s(1), s(2)], 0x1e20_4041),
        row(Op::FmovFprFpr, vec![d(7), d(8)], 0x1e60_4107),
        row(Op::FabsRR, vec![d(1), d(2)], 0x1e60_c041),
        row(Op::FnegRR, vec![s(3), s(4)], 0x1e21_4083),
        row(Op::FsqrtRR, vec![d(5), d(6)], 0x1e61_c0c5),
        row(Op::FrintmRR, vec![s(1), s(2)], 0x1e25_4041),
        row(Op::FrintpRR, vec![d(1), d(2)], 0x1e64_c041),
        row(Op::FrintzRR, vec![d(31), d(30)], 0x1e65_c3df),
        // FRINTN (ties to even), Apple clang 21 with +fp16 for the H form.
        row(Op::FrintnRR, vec![s(1), s(2)], 0x1e24_4041),
        row(Op::FrintnRR, vec![d(31), d(30)], 0x1e64_43df),
        row(Op::FrintnRR, vec![h(31), h(17)], 0x1ee4_423f),
        row(Op::FcvtSD, vec![d(1), s(2)], 0x1e22_c041),
        row(Op::FcvtDS, vec![s(3), d(4)], 0x1e62_4083),
        row(Op::FcvtHS, vec![s(5), h(6)], 0x1ee2_40c5),
        row(Op::FcvtHD, vec![d(7), h(8)], 0x1ee2_c107),
        row(Op::FcvtSH, vec![h(9), s(10)], 0x1e23_c149),
        row(Op::FcvtDH, vec![h(11), d(12)], 0x1e63_c18b),
        row(Op::FmovImm, vec![s(1), fimm(2.0)], 0x1e20_1001),
        row(Op::FmovImm, vec![d(2), fimm(-0.125)], 0x1e78_1002),
        row(Op::FmovImm, vec![d(3), fimm(31.0)], 0x1e67_f003),
        row(Op::FmovImm, vec![s(4), fimm(1.0)], 0x1e2e_1004),
        row(Op::FcvtzsRR, vec![w(1), s(2)], 0x1e38_0041),
        row(Op::FcvtzsRR, vec![x(3), d(4)], 0x9e78_0083),
        row(Op::FcvtzuRR, vec![w(5), d(6)], 0x1e79_00c5),
        row(Op::FcvtzuRR, vec![x(7), s(8)], 0x9e39_0107),
        row(Op::ScvtfRR, vec![s(1), w(2)], 0x1e22_0041),
        row(Op::ScvtfRR, vec![d(3), x(4)], 0x9e62_0083),
        row(Op::UcvtfRR, vec![d(5), w(6)], 0x1e63_00c5),
        row(Op::UcvtfRR, vec![s(7), x(8)], 0x9e23_0107),
        row(Op::FmovFprGpr, vec![w(1), s(2)], 0x1e26_0041),
        row(Op::FmovFprGpr, vec![x(3), d(4)], 0x9e66_0083),
        row(Op::FmovGprFpr, vec![s(5), w(6)], 0x1e27_00c5),
        row(Op::FmovGprFpr, vec![d(7), x(8)], 0x9e67_0107),
        row(Op::NeonAddV, vec![v(1), v(2), v(3), imm(6)], 0x4ee3_8441),
        row(Op::NeonAddV, vec![v(1), v(2), v(3), imm(0)], 0x0e23_8441),
        row(Op::NeonSubV, vec![v(4), v(5), v(6), imm(5)], 0x6ea6_84a4),
        row(Op::NeonMulV, vec![v(7), v(8), v(9), imm(3)], 0x4e69_9d07),
        row(Op::NeonMlaV, vec![v(0), v(1), v(2), imm(5)], 0x4ea2_9420),
        row(Op::NeonSmaxV, vec![v(1), v(2), v(3), imm(5)], 0x4ea3_6441),
        row(Op::NeonSminV, vec![v(1), v(2), v(3), imm(1)], 0x4e23_6c41),
        row(Op::NeonUmaxV, vec![v(1), v(2), v(3), imm(3)], 0x6e63_6441),
        row(Op::NeonUminV, vec![v(1), v(2), v(3), imm(4)], 0x2ea3_6c41),
        row(Op::NeonCmgtV, vec![v(1), v(2), v(3), imm(5)], 0x4ea3_3441),
        row(Op::NeonCmgeV, vec![v(1), v(2), v(3), imm(6)], 0x4ee3_3c41),
        row(Op::NeonCmhiV, vec![v(1), v(2), v(3), imm(1)], 0x6e23_3441),
        row(Op::NeonCmhsV, vec![v(1), v(2), v(3), imm(2)], 0x2e63_3c41),
        row(Op::NeonCmeqV, vec![v(1), v(2), v(3), imm(5)], 0x6ea3_8c41),
        row(Op::NeonAndV, vec![v(1), v(2), v(3), imm(1)], 0x4e23_1c41),
        row(Op::NeonBicV, vec![v(1), v(2), v(3), imm(0)], 0x0e63_1c41),
        row(Op::NeonOrrV, vec![v(1), v(2), v(2), imm(1)], 0x4ea2_1c41),
        row(Op::NeonEorV, vec![v(1), v(2), v(3), imm(0)], 0x2e23_1c41),
        row(Op::NeonBitV, vec![v(1), v(2), v(3), imm(1)], 0x6ea3_1c41),
        row(Op::NeonFaddV, vec![v(1), v(2), v(3), imm(1)], 0x4e23_d441),
        row(Op::NeonFaddV, vec![v(1), v(2), v(3), imm(2)], 0x4e63_d441),
        row(Op::NeonFsubV, vec![v(1), v(2), v(3), imm(0)], 0x0ea3_d441),
        row(Op::NeonFmulV, vec![v(1), v(2), v(3), imm(2)], 0x6e63_dc41),
        row(Op::NeonFdivV, vec![v(1), v(2), v(3), imm(1)], 0x6e23_fc41),
        row(Op::NeonFmlaV, vec![v(1), v(2), v(3), imm(2)], 0x4e63_cc41),
        row(Op::NeonFmlsV, vec![v(1), v(2), v(3), imm(1)], 0x4ea3_cc41),
        row(Op::NeonFcmgtV, vec![v(1), v(2), v(3), imm(2)], 0x6ee3_e441),
        row(Op::NeonNotV, vec![v(1), v(2)], 0x6e20_5841),
        row(Op::NeonCntV, vec![v(1), v(2), imm(0)], 0x0e20_5841),
        row(Op::NeonRbitV, vec![v(1), v(2), imm(1)], 0x6e60_5841),
        row(Op::NeonRev64V, vec![v(1), v(2), imm(5)], 0x4ea0_0841),
        row(Op::NeonRev32V, vec![v(1), v(2), imm(1)], 0x6e20_0841),
        row(Op::NeonAbsV, vec![v(1), v(2), imm(5)], 0x4ea0_b841),
        row(Op::NeonSaddlpV, vec![v(1), v(2), imm(1)], 0x4e20_2841),
        row(Op::NeonUaddlpV, vec![v(1), v(2), imm(3)], 0x6e60_2841),
        row(Op::NeonUadalpV, vec![v(1), v(2), imm(5)], 0x6ea0_6841),
        row(Op::NeonScvtfV, vec![v(1), v(2), imm(2)], 0x4e61_d841),
        row(Op::NeonUcvtfV, vec![v(1), v(2), imm(1)], 0x6e21_d841),
        row(Op::NeonFcvtlV, vec![v(1), v(2)], 0x0e61_7841),
        row(Op::NeonFcvtl2V, vec![v(1), v(2)], 0x4e61_7841),
        row(Op::NeonSmlalV, vec![v(1), v(2), v(3), imm(5)], 0x0ea3_8041),
        row(Op::NeonSmlal2V, vec![v(1), v(2), v(3), imm(5)], 0x4ea3_8041),
        row(Op::NeonUmlalV, vec![v(1), v(2), v(3), imm(5)], 0x2ea3_8041),
        row(Op::NeonUmlal2V, vec![v(1), v(2), v(3), imm(5)], 0x6ea3_8041),
        row(Op::NeonSaddwV, vec![v(1), v(2), v(3), imm(5)], 0x0ea3_1041),
        row(Op::NeonSaddw2V, vec![v(1), v(2), v(3), imm(5)], 0x4ea3_1041),
        row(Op::NeonUaddwV, vec![v(1), v(2), v(3), imm(5)], 0x2ea3_1041),
        row(Op::NeonUaddw2V, vec![v(1), v(2), v(3), imm(5)], 0x6ea3_1041),
        row(
            Op::NeonFmlaLaneV,
            vec![v(1), v(2), v(19), imm(3), imm(1)],
            0x4fb3_1841,
        ),
        row(
            Op::NeonFmlaLaneV,
            vec![v(1), v(2), v(17), imm(1), imm(2)],
            0x4fd1_1841,
        ),
        row(
            Op::NeonDupElem,
            vec![v(1), v(2), imm(3), imm(4)],
            0x4e1c_0441,
        ),
        row(
            Op::NeonDupElem,
            vec![d(1), v(2), imm(15), imm(1)],
            0x0e1f_0441,
        ),
        row(Op::NeonDupGen, vec![v(1), x(2), imm(8)], 0x4e08_0c41),
        row(Op::NeonDupGen, vec![v(1), w(2), imm(2)], 0x4e02_0c41),
        row(
            Op::NeonInsGen,
            vec![v(1), w(3), imm(2), imm(4)],
            0x4e14_1c61,
        ),
        row(
            Op::NeonInsGen,
            vec![v(1), x(3), imm(1), imm(8)],
            0x4e18_1c61,
        ),
        row(
            Op::NeonUmovGen,
            vec![w(1), v(2), imm(7), imm(1)],
            0x0e0f_3c41,
        ),
        row(
            Op::NeonUmovGen,
            vec![w(1), v(2), imm(1), imm(4)],
            0x0e0c_3c41,
        ),
        row(
            Op::NeonUmovGen,
            vec![x(1), v(2), imm(1), imm(8)],
            0x4e18_3c41,
        ),
        row(Op::NeonDupScalarD, vec![d(1), v(2), imm(1)], 0x5e18_0441),
        row(Op::NeonMovi, vec![v(1), imm(0xa5)], 0x4f05_e4a1),
        row(Op::NeonMovi, vec![d(1), imm(0xff)], 0x0f07_e7e1),
        row(
            Op::NeonShlVImm,
            vec![v(1), v(2), imm(3), imm(5)],
            0x4f23_5441,
        ),
        row(
            Op::NeonShlVImm,
            vec![v(1), v(2), imm(63), imm(6)],
            0x4f7f_5441,
        ),
        row(
            Op::NeonSshrVImm,
            vec![v(1), v(2), imm(16), imm(3)],
            0x4f10_0441,
        ),
        row(
            Op::NeonUshrVImm,
            vec![v(1), v(2), imm(1), imm(1)],
            0x6f0f_0441,
        ),
        row(
            Op::NeonUshrVImm,
            vec![v(1), v(2), imm(64), imm(6)],
            0x6f40_0441,
        ),
        row(Op::NeonExtV, vec![v(1), v(2), v(3), imm(12)], 0x6e03_6041),
        row(Op::NeonUdotV, vec![v(1), v(2), v(3), imm(1)], 0x6e83_9441),
        row(Op::NeonUmaxv, vec![s(1), v(2), imm(5)], 0x6eb0_a841),
        row(Op::NeonAddpScalar, vec![d(1), v(2), imm(6)], 0x5ef1_b841),
        row(Op::NeonLd1Post, vec![v(1), x(2), imm(1)], 0x4cdf_7041),
        row(
            Op::NeonLd1Post,
            vec![v(1), Arg::Special(SpecialReg::SP), imm(6)],
            0x4cdf_7fe1,
        ),
        row(Op::NeonSt1Post, vec![v(1), x(2), imm(5)], 0x4c9f_7841),
        row(Op::NeonSt1Post, vec![v(1), x(2), imm(0)], 0x0c9f_7041),
        // The machine IR's 16B copy of an S or D value names the scalar
        // view (census samples `NeonOrrV r128 r129 r129 #1`, `r96 r98 r98 #1`).
        row(Op::NeonOrrV, vec![s(0), s(1), s(1), imm(1)], 0x4ea1_1c20),
        row(Op::NeonOrrV, vec![d(0), d(2), d(2), imm(1)], 0x4ea2_1c40),
        // FCMP (register, quiet): S/D through the flag-consumer obligation's
        // decoder, and the half-precision (FEAT_FP16) compare an F16 `fcmp`
        // lowers to (`-march=armv8.2-a+fp16`).
        row(Op::Fcmp, vec![s(1), s(2)], 0x1e22_2020),
        row(Op::Fcmp, vec![d(30), d(0)], 0x1e60_23c0),
        row(Op::Fcmp, vec![h(3), h(17)], 0x1ef1_2060),
        row(Op::Fcmp, vec![h(0), h(31)], 0x1eff_2000),
        row(Op::Fcmp, vec![h(31), h(0)], 0x1ee0_23e0),
    ]
}

#[test]
fn assembler_words_decode_and_every_single_bit_corruption_mismatches() {
    let rows = assembler_rows();
    let mut failures = Vec::new();
    let mut opcodes = BTreeSet::new();
    for (inst, word) in &rows {
        opcodes.insert(format!("{:?}", inst.opcode));
        match check(inst, *word, None) {
            DecodeCheckOutcome::Match => {}
            other => failures.push(format!(
                "{:?} {:?} = {word:#010x}: {other:?}",
                inst.opcode, inst.operands
            )),
        }
        assert_every_bit_flip_mismatches(inst, *word, &mut failures);
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(rows.len(), 125);
    // Every opcode of the FP/SIMD slice has an assembler row except the pair
    // memory forms (decoded by `aarch64_pair_memory`) and the FCSEL arm that
    // predates this slice.
    let expected: BTreeSet<String> = trust_cg_verify::coverage_gate::ALL_AARCH64_OPCODES
        .iter()
        .copied()
        .filter(|&op| is_fp_simd(op))
        .filter(|op| !matches!(op, Op::NeonLdpQPost | Op::NeonStpQPost | Op::FcselRR))
        .map(|op| format!("{op:?}"))
        .collect();
    assert_eq!(opcodes, expected);
}

/// The opcodes of ENC-5's integer slice (`aarch64::decode_check_int`).
const INTEGER_SLICE: [Op; 78] = [
    Op::AddTprelHi12,
    Op::AddTprelLo12,
    Op::LdrGottprel,
    Op::AddRRShift,
    Op::SubRRShift,
    Op::AddRRShiftLsr,
    Op::AddsRR,
    Op::SubsRR,
    Op::Neg,
    Op::AddsRI,
    Op::SubsRI,
    Op::Adc,
    Op::Sbc,
    Op::Adcs,
    Op::Sbcs,
    Op::BicRR,
    Op::AndRI,
    Op::OrrRI,
    Op::EorRI,
    Op::Tst,
    Op::RorRI,
    Op::Smulh,
    Op::Umulh,
    Op::Umull,
    Op::AddPCRel,
    Op::Adrp,
    Op::Adr,
    Op::LdrGot,
    Op::LdrTlvp,
    Op::LdrswRO,
    Op::Tbz,
    Op::Tbnz,
    Op::Ldadd,
    Op::Ldadda,
    Op::Ldaddal,
    Op::Ldaddl,
    Op::Ldclr,
    Op::Ldclra,
    Op::Ldclral,
    Op::Ldclrl,
    Op::Ldeor,
    Op::Ldeora,
    Op::Ldeoral,
    Op::Ldeorl,
    Op::Ldset,
    Op::Ldseta,
    Op::Ldsetal,
    Op::Ldsetl,
    Op::Ldsmax,
    Op::Ldsmaxa,
    Op::Ldsmaxal,
    Op::Ldsmaxl,
    Op::Ldsmin,
    Op::Ldsmina,
    Op::Ldsminal,
    Op::Ldsminl,
    Op::Ldumax,
    Op::Ldumaxa,
    Op::Ldumaxal,
    Op::Ldumaxl,
    Op::Ldumin,
    Op::Ldumina,
    Op::Lduminal,
    Op::Lduminl,
    Op::Swp,
    Op::Swpa,
    Op::Swpal,
    Op::Swpl,
    Op::Cas,
    Op::Casa,
    Op::Casal,
    Op::Casl,
    Op::Ldar,
    Op::Ldarb,
    Op::Ldarh,
    Op::Stlr,
    Op::Stlrb,
    Op::Stlrh,
];

fn is_integer_slice(opcode: Op) -> bool {
    INTEGER_SLICE.contains(&opcode)
        || matches!(
            opcode,
            Op::Dmb
                | Op::Dsb
                | Op::Isb
                | Op::Brk
                | Op::Nop
                | Op::TrapOverflow
                | Op::TrapBoundsCheck
                | Op::TrapNull
                | Op::TrapDivZero
                | Op::TrapShiftRange
                | Op::STRWui
                | Op::STRXui
                | Op::STRSui
                | Op::STRDui
                | Op::LdrLiteral
                | Op::BLR
        )
}

/// Integer words assembled by clang (`-march=armv8.1-a`, aarch64-apple-macos)
/// and read back with `otool -tvj`. Branch offsets are in words.
fn integer_assembler_rows() -> Vec<(MachInst, u32)> {
    let row = |opcode, operands: Vec<Arg>, word: u32| (MachInst::new(opcode, operands), word);
    let sp = || Arg::Special(SpecialReg::SP);
    let xzr = || Arg::Special(SpecialReg::XZR);
    let wzr = || Arg::Special(SpecialReg::WZR);
    vec![
        row(Op::AddRRShift, vec![x(0), x(1), x(2), imm(1)], 0x8b02_0420),
        row(Op::AddRRShift, vec![w(3), w(4), w(5), imm(31)], 0x0b05_7c83),
        row(Op::SubRRShift, vec![x(6), x(7), x(8), imm(63)], 0xcb08_fce6),
        row(
            Op::AddRRShiftLsr,
            vec![x(9), x(10), x(11), imm(8)],
            0x8b4b_2149,
        ),
        row(
            Op::AddRRShiftLsr,
            vec![w(12), w(13), w(14), imm(1)],
            0x0b4e_05ac,
        ),
        row(Op::AddsRR, vec![x(1), x(2), x(3)], 0xab03_0041),
        row(Op::AddsRR, vec![w(1), wzr(), w(3)], 0x2b03_03e1),
        row(Op::SubsRR, vec![xzr(), x(2), x(3)], 0xeb03_005f),
        row(Op::SubsRR, vec![w(4), w(5), w(6)], 0x6b06_00a4),
        row(Op::Neg, vec![x(1), x(2)], 0xcb02_03e1),
        row(Op::Neg, vec![w(3), w(4)], 0x4b04_03e3),
        row(Op::AddsRI, vec![x(1), sp(), imm(4095)], 0xb13f_ffe1),
        row(Op::AddsRI, vec![x(5), x(6), imm(0)], 0xb100_00c5),
        row(Op::SubsRI, vec![w(2), w(3), imm(1)], 0x7100_0462),
        row(Op::SubsRI, vec![xzr(), x(4), imm(7)], 0xf100_1c9f),
        row(Op::Adc, vec![x(1), x(2), x(3)], 0x9a03_0041),
        row(Op::Adc, vec![w(4), w(5), w(6)], 0x1a06_00a4),
        row(Op::Sbc, vec![x(7), x(8), x(9)], 0xda09_0107),
        row(Op::Adcs, vec![x(1), x(2), x(3)], 0xba03_0041),
        row(
            Op::Sbcs,
            vec![Arg::PReg(PReg::new(160)), x(4), x(2)],
            0xfa02_009f,
        ),
        row(Op::BicRR, vec![x(1), x(2), x(3)], 0x8a23_0041),
        row(Op::BicRR, vec![w(4), w(5), w(6)], 0x0a26_00a4),
        row(Op::AndRI, vec![w(1), w(0), imm(7)], 0x1200_0801),
        row(
            Op::AndRI,
            vec![x(0), x(1), imm(0x3333_3333_3333_3333)],
            0x9200_e420,
        ),
        row(Op::AndRI, vec![sp(), x(9), imm(-16)], 0x927c_ed3f),
        row(Op::OrrRI, vec![x(5), x(0), imm(1)], 0xb240_0005),
        row(Op::OrrRI, vec![w(1), w(0), imm(0xff00_ff00)], 0x3208_9c01),
        row(Op::EorRI, vec![x(0), x(4), imm(1)], 0xd240_0080),
        row(Op::EorRI, vec![w(2), w(3), imm(0x8000_0000)], 0x5201_0062),
        row(Op::Tst, vec![x(2), imm(1)], 0xf240_005f),
        row(Op::Tst, vec![x(0), imm(0xffff)], 0xf240_3c1f),
        row(Op::Tst, vec![w(1), imm(0xffff_fff0)], 0x721c_6c3f),
        row(Op::Tst, vec![x(1), x(2)], 0xea02_003f),
        row(Op::Tst, vec![w(3), w(4)], 0x6a04_007f),
        row(Op::RorRI, vec![x(1), x(2), imm(13)], 0x93c2_3441),
        row(Op::RorRI, vec![w(3), w(4), imm(31)], 0x1384_7c83),
        row(Op::Smulh, vec![x(2), x(0), x(1)], 0x9b41_7c02),
        row(Op::Umulh, vec![x(1), x(2), x(0)], 0x9bc0_7c41),
        row(Op::Umull, vec![x(2), w(1), w(0)], 0x9ba0_7c22),
        row(Op::LdrswRO, vec![x(2), x(1), x(0)], 0xb8a0_7822),
        row(Op::LdrswRO, vec![x(3), sp(), x(30)], 0xb8be_7be3),
        row(Op::Tbz, vec![w(2), imm(0), imm(2)], 0x3600_0042),
        row(Op::Tbnz, vec![x(3), imm(63), imm(-1)], 0xb7ff_ffe3),
        row(Op::Tbnz, vec![w(0), imm(31), imm(8191)], 0x37fb_ffe0),
        row(Op::Ldadd, vec![x(1), x(2), x(0)], 0xf821_0002),
        row(Op::Ldadda, vec![w(1), w(2), sp()], 0xb8a1_03e2),
        row(Op::Ldaddal, vec![x(3), x(4), x(5)], 0xf8e3_00a4),
        row(Op::Ldaddl, vec![w(6), w(7), x(8)], 0xb866_0107),
        row(Op::Ldclr, vec![w(1), w(2), x(0), imm(0)], 0x3821_1002),
        row(Op::Ldclra, vec![w(1), w(2), x(0), imm(1)], 0x78a1_1002),
        row(Op::Ldeoral, vec![w(2), w(1), x(0), imm(0)], 0x38e2_2001),
        row(Op::Ldsetl, vec![x(2), x(1), x(0)], 0xf862_3001),
        row(Op::Ldsmax, vec![x(2), x(1), x(0)], 0xf822_4001),
        row(Op::Ldsmina, vec![w(2), w(1), x(0)], 0xb8a2_5001),
        row(Op::Ldumaxal, vec![x(2), x(1), x(0)], 0xf8e2_6001),
        row(Op::Lduminl, vec![w(2), w(1), x(0)], 0xb862_7001),
        row(Op::Swp, vec![x(2), x(1), x(0)], 0xf822_8001),
        row(Op::Swpa, vec![w(2), w(1), x(0), imm(0)], 0x38a2_8001),
        row(Op::Swpal, vec![w(2), w(1), x(0), imm(1)], 0x78e2_8001),
        row(Op::Swpl, vec![w(2), w(1), x(0)], 0xb862_8001),
        row(Op::Cas, vec![x(3), x(2), x(0)], 0xc8a3_7c02),
        row(Op::Casa, vec![w(3), w(2), x(0)], 0x88e3_7c02),
        row(Op::Casal, vec![w(3), w(2), x(0), imm(0)], 0x08e3_fc02),
        row(Op::Casl, vec![w(3), w(2), sp(), imm(1)], 0x48a3_ffe2),
        row(Op::Ldar, vec![x(1), x(0)], 0xc8df_fc01),
        row(Op::Ldar, vec![w(1), sp()], 0x88df_ffe1),
        row(Op::Ldarb, vec![w(2), x(3)], 0x08df_fc62),
        row(Op::Ldarh, vec![w(4), x(5)], 0x48df_fca4),
        row(Op::Stlr, vec![x(1), x(0)], 0xc89f_fc01),
        row(Op::Stlrb, vec![w(2), x(3)], 0x089f_fc62),
        row(Op::Stlrh, vec![w(4), sp()], 0x489f_ffe4),
        row(Op::Dmb, vec![imm(0xb)], 0xd503_3bbf),
        row(Op::Dmb, vec![imm(0x9)], 0xd503_39bf),
        row(Op::Dsb, vec![imm(0xf)], 0xd503_3f9f),
        row(Op::Isb, vec![imm(0xf)], 0xd503_3fdf),
        row(Op::Brk, vec![], 0xd420_0020),
        row(Op::Brk, vec![imm(0xf000)], 0xd43e_0000),
        row(Op::Nop, vec![], 0xd503_201f),
        // Typed stores (scaled and unscaled), LDR (literal) in words, BLR.
        row(Op::STRWui, vec![w(1), x(2), imm(4)], 0xb900_0441),
        row(Op::STRWui, vec![w(1), x(2), imm(-4)], 0xb81f_c041),
        row(Op::STRXui, vec![x(3), sp(), imm(8)], 0xf900_07e3),
        row(
            Op::STRXui,
            vec![
                x(3),
                Arg::MemOp {
                    base: PReg::new(4),
                    offset: 32760,
                },
            ],
            0xf93f_fc83,
        ),
        row(Op::STRSui, vec![s(4), x(5), imm(-4)], 0xbc1f_c0a4),
        row(Op::STRSui, vec![s(4), x(5), imm(16380)], 0xbd3f_fca4),
        row(Op::STRDui, vec![d(6), x(7), imm(32760)], 0xfd3f_fce6),
        row(Op::STRDui, vec![d(6), sp(), imm(-256)], 0xfc10_03e6),
        row(Op::LdrLiteral, vec![x(1), imm(2)], 0x5800_0041),
        row(Op::LdrLiteral, vec![x(30), imm(-1)], 0x58ff_fffe),
        row(Op::BLR, vec![x(9)], 0xd63f_0120),
        // Mixed W/X views, as register allocation spells them: a `Bool`
        // (64-bit class) Trunc from a 32-bit value is `AND Xd, Wn, #1`, and
        // the masked-UMULL fusion names UMULL's sources in the 64-bit view.
        // The width-selecting operand (or the opcode) fixes the word's width.
        row(Op::AndRI, vec![x(0), w(0), imm(1)], 0x9240_0000),
        row(Op::Umull, vec![x(0), x(0), x(1)], 0x9ba1_7c00),
        // The unconditional trap pseudos are `BRK #1`.
        row(Op::TrapOverflow, vec![], 0xd420_0020),
        row(Op::TrapBoundsCheck, vec![], 0xd420_0020),
        row(Op::TrapNull, vec![], 0xd420_0020),
        row(Op::TrapDivZero, vec![], 0xd420_0020),
        row(Op::TrapShiftRange, vec![], 0xd420_0020),
    ]
}

#[test]
fn integer_assembler_words_decode_and_every_single_bit_corruption_mismatches() {
    let rows = integer_assembler_rows();
    let mut failures = Vec::new();
    let mut opcodes = BTreeSet::new();
    for (inst, word) in &rows {
        opcodes.insert(format!("{:?}", inst.opcode));
        match check(inst, *word, None) {
            DecodeCheckOutcome::Match => {}
            other => failures.push(format!(
                "{:?} {:?} = {word:#010x}: {other:?}",
                inst.opcode, inst.operands
            )),
        }
        assert_every_bit_flip_mismatches(inst, *word, &mut failures);
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(rows.len(), 96);
    // Rows for every integer-slice opcode that is not relocation-shaped (the
    // relocated forms are checked below) and not an LSE row not assembled.
    for opcode in INTEGER_SLICE {
        let relocated = matches!(
            opcode,
            Op::AddPCRel
                | Op::Adrp
                | Op::Adr
                | Op::LdrGot
                | Op::LdrTlvp
                | Op::LdrGottprel
                | Op::AddTprelHi12
                | Op::AddTprelLo12
        );
        let lse_unrowed = matches!(
            opcode,
            Op::Ldclral
                | Op::Ldclrl
                | Op::Ldeor
                | Op::Ldeora
                | Op::Ldeorl
                | Op::Ldset
                | Op::Ldseta
                | Op::Ldsetal
                | Op::Ldsmaxa
                | Op::Ldsmaxal
                | Op::Ldsmaxl
                | Op::Ldsmin
                | Op::Ldsminal
                | Op::Ldsminl
                | Op::Ldumax
                | Op::Ldumaxa
                | Op::Ldumaxl
                | Op::Ldumin
                | Op::Ldumina
                | Op::Lduminal
        );
        assert_eq!(
            opcodes.contains(&format!("{opcode:?}")),
            !relocated && !lse_unrowed,
            "{opcode:?}"
        );
    }
}

/// Relocated words: the placeholder field must be zero and the recorded
/// GlobalRef hole present (an absent or different hole mismatches); an ADR
/// naming a jump table keeps the patched offset for the final-layout
/// cross-check, so only its class, `op` and `Rd` are compared.
#[test]
fn relocated_and_jump_table_words_check_every_owned_field() {
    let global = FixupHole {
        offset_in_inst: 0,
        width: 4,
        kind: FixupHoleKind::GlobalRef,
    };
    let symbol = || Arg::Symbol("g".into());
    let mut failures = Vec::new();
    for (inst, word) in [
        (MachInst::new(Op::Adrp, vec![x(19), symbol()]), 0x9000_0013),
        (
            MachInst::new(Op::AddPCRel, vec![x(1), x(0), symbol()]),
            0x9100_0001,
        ),
        (
            MachInst::new(Op::LdrGot, vec![x(19), x(19), symbol()]),
            0xf940_0273,
        ),
        (
            MachInst::new(Op::LdrTlvp, vec![x(0), x(0), symbol()]),
            0xf940_0000,
        ),
        (
            MachInst::new(Op::LdrGottprel, vec![x(1), x(1), symbol()]),
            0xf940_0021,
        ),
        (
            MachInst::new(Op::AddTprelHi12, vec![x(1), x(1), symbol()]),
            0x9140_0021,
        ),
        (
            MachInst::new(Op::AddTprelLo12, vec![x(0), x(0), symbol()]),
            0x9100_0000,
        ),
    ] {
        assert!(
            matches!(check(&inst, word, Some(&global)), DecodeCheckOutcome::Match),
            "{inst:?}"
        );
        for bit in 0..32 {
            if !matches!(
                check(&inst, word ^ (1 << bit), Some(&global)),
                DecodeCheckOutcome::Mismatch(_)
            ) {
                failures.push(format!("{inst:?}: bit {bit}"));
            }
        }
        for other in [
            None,
            Some(FixupHole {
                kind: FixupHoleKind::Call,
                ..global
            }),
        ] {
            assert!(
                matches!(
                    check(&inst, word, other.as_ref()),
                    DecodeCheckOutcome::Mismatch(_)
                ),
                "{inst:?} with {other:?}"
            );
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // ADR of a jump table: every bit outside immlo (30:29) and immhi (23:5).
    let adr = MachInst::new(Op::Adr, vec![x(6), Arg::JumpTableIndex(0)]);
    let word = 0x1000_01a6;
    assert!(matches!(check(&adr, word, None), DecodeCheckOutcome::Match));
    for bit in 0..32 {
        let immediate = matches!(bit, 29 | 30 | 5..=23);
        let outcome = check(&adr, word ^ (1 << bit), None);
        assert_eq!(
            matches!(outcome, DecodeCheckOutcome::Mismatch(_)),
            !immediate,
            "ADR bit {bit}: {outcome:?}"
        );
    }
    // Resolved PC-relative and GOT forms compare their immediates.
    let resolved = MachInst::new(Op::Adr, vec![x(6), imm(-3)]);
    assert!(matches!(
        check(&resolved, 0x10ff_ffe6 | (0b01 << 29), None),
        DecodeCheckOutcome::Match
    ));
    assert!(matches!(
        check(&resolved, 0x10ff_ffe6, None),
        DecodeCheckOutcome::Mismatch(_)
    ));
}

/// For every shape built here, the encoder's word is the word ENC-5 decodes:
/// every arrangement selector, element size and lane the machine IR can name,
/// and each integer form in both register widths with one view per
/// instruction (mixed W/X views are the next test). A differential between two
/// independently written artifacts over the shapes it enumerates, not over
/// every operand list the encoder accepts.
#[test]
fn encoder_words_for_every_accepted_fp_simd_and_integer_shape_match() {
    use trust_cg_codegen::aarch64::encode::encode_instruction;
    let mut attempted = 0;
    let mut encoded = 0;
    let mut failures = Vec::new();
    let mut probe = |inst: MachInst| {
        attempted += 1;
        if let Ok(word) = encode_instruction(&inst) {
            encoded += 1;
            if !matches!(check(&inst, word, None), DecodeCheckOutcome::Match) {
                failures.push(format!(
                    "{:?} {:?} = {word:#010x}: {:?}",
                    inst.opcode,
                    inst.operands,
                    check(&inst, word, None)
                ));
            }
        }
    };
    let three = [
        Op::NeonAddV,
        Op::NeonSubV,
        Op::NeonMulV,
        Op::NeonMlaV,
        Op::NeonSmaxV,
        Op::NeonSminV,
        Op::NeonUmaxV,
        Op::NeonUminV,
        Op::NeonCmeqV,
        Op::NeonCmgtV,
        Op::NeonCmgeV,
        Op::NeonCmhiV,
        Op::NeonCmhsV,
        Op::NeonUdotV,
        Op::NeonSmlalV,
        Op::NeonSmlal2V,
        Op::NeonUmlalV,
        Op::NeonUmlal2V,
        Op::NeonUaddwV,
        Op::NeonUaddw2V,
        Op::NeonSaddwV,
        Op::NeonSaddw2V,
    ];
    for opcode in three {
        for arrangement in 0..=6 {
            probe(MachInst::new(
                opcode,
                vec![v(31), v(0), v(17), imm(arrangement)],
            ));
        }
    }
    for opcode in [
        Op::NeonFaddV,
        Op::NeonFsubV,
        Op::NeonFmulV,
        Op::NeonFdivV,
        Op::NeonFmlaV,
        Op::NeonFmlsV,
        Op::NeonFcmgtV,
    ] {
        for arrangement in 0..=2 {
            probe(MachInst::new(
                opcode,
                vec![v(3), v(30), v(16), imm(arrangement)],
            ));
        }
    }
    for opcode in [
        Op::NeonCntV,
        Op::NeonRbitV,
        Op::NeonRev32V,
        Op::NeonRev64V,
        Op::NeonAbsV,
        Op::NeonUaddlpV,
        Op::NeonSaddlpV,
        Op::NeonUadalpV,
        Op::NeonUmaxv,
        Op::NeonAddpScalar,
        Op::NeonLd1Post,
        Op::NeonSt1Post,
    ] {
        for arrangement in 0..=6 {
            let first = match opcode {
                Op::NeonUmaxv => s(9),
                Op::NeonAddpScalar => d(9),
                _ => v(9),
            };
            let second = match opcode {
                Op::NeonLd1Post | Op::NeonSt1Post => x(21),
                _ => v(22),
            };
            probe(MachInst::new(opcode, vec![first, second, imm(arrangement)]));
        }
    }
    for opcode in [Op::NeonScvtfV, Op::NeonUcvtfV] {
        for arrangement in 0..=2 {
            probe(MachInst::new(opcode, vec![v(5), v(27), imm(arrangement)]));
        }
    }
    for opcode in [Op::NeonFcvtlV, Op::NeonFcvtl2V, Op::NeonNotV] {
        probe(MachInst::new(opcode, vec![v(8), v(24)]));
    }
    for opcode in [
        Op::NeonAndV,
        Op::NeonOrrV,
        Op::NeonEorV,
        Op::NeonBicV,
        Op::NeonBitV,
    ] {
        for selector in [
            None,
            Some(0),
            Some(1),
            Some(2),
            Some(3),
            Some(4),
            Some(5),
            Some(6),
        ] {
            for dst in [v(4), d(4), s(4)] {
                let mut operands = vec![dst, v(13), v(29)];
                operands.extend(selector.map(imm));
                probe(MachInst::new(opcode, operands));
            }
        }
    }
    for (arrangement, lanes) in [(1, 4), (2, 2)] {
        for lane in 0..lanes {
            probe(MachInst::new(
                Op::NeonFmlaLaneV,
                vec![v(6), v(7), v(31), imm(lane), imm(arrangement)],
            ));
        }
    }
    for (bytes, lanes) in [(1i64, 16i64), (2, 8), (4, 4), (8, 2)] {
        for lane in 0..lanes {
            for dst in [v(2), d(2)] {
                probe(MachInst::new(
                    Op::NeonDupElem,
                    vec![dst, v(20), imm(lane), imm(bytes)],
                ));
            }
            let gpr = if bytes == 8 { x(11) } else { w(11) };
            probe(MachInst::new(
                Op::NeonInsGen,
                vec![v(2), gpr.clone(), imm(lane), imm(bytes)],
            ));
            probe(MachInst::new(
                Op::NeonUmovGen,
                vec![gpr, v(20), imm(lane), imm(bytes)],
            ));
        }
        for dst in [v(2), d(2)] {
            let gpr = if bytes == 8 { x(11) } else { w(11) };
            probe(MachInst::new(Op::NeonDupGen, vec![dst, gpr, imm(bytes)]));
        }
    }
    for lane in 0..2 {
        probe(MachInst::new(
            Op::NeonDupScalarD,
            vec![d(3), v(28), imm(lane)],
        ));
    }
    for value in [0, 1, 0x5a, 0xa5, 0xff] {
        for dst in [v(12), d(12)] {
            probe(MachInst::new(Op::NeonMovi, vec![dst, imm(value)]));
        }
    }
    for opcode in [Op::NeonShlVImm, Op::NeonUshrVImm, Op::NeonSshrVImm] {
        for arrangement in 0..=6i64 {
            let esize = 8i64 << (arrangement / 2).min(3);
            for shift in 0..=esize {
                probe(MachInst::new(
                    opcode,
                    vec![v(1), v(30), imm(shift), imm(arrangement)],
                ));
            }
        }
    }
    for bytes in [1, 4, 8, 12, 15] {
        probe(MachInst::new(
            Op::NeonExtV,
            vec![v(10), v(11), v(12), imm(bytes)],
        ));
    }
    // Integer slice over both widths, zero registers, SP bases and the
    // immediate domains the encoder accepts.
    for (gpr, zr) in [
        (x as fn(u16) -> Arg, Arg::Special(SpecialReg::XZR)),
        (w as fn(u16) -> Arg, Arg::Special(SpecialReg::WZR)),
    ] {
        for opcode in [Op::AddRRShift, Op::SubRRShift, Op::AddRRShiftLsr] {
            for amount in [0, 1, 17, 31, 32, 63, 64] {
                probe(MachInst::new(
                    opcode,
                    vec![gpr(3), gpr(29), gpr(30), imm(amount)],
                ));
            }
        }
        for opcode in [
            Op::AddsRR,
            Op::SubsRR,
            Op::Adc,
            Op::Sbc,
            Op::Adcs,
            Op::Sbcs,
            Op::BicRR,
        ] {
            probe(MachInst::new(opcode, vec![gpr(3), gpr(29), gpr(30)]));
            probe(MachInst::new(opcode, vec![zr.clone(), gpr(0), gpr(1)]));
        }
        probe(MachInst::new(Op::Neg, vec![gpr(7), gpr(8)]));
        for opcode in [Op::AddsRI, Op::SubsRI] {
            for value in [0, 1, 4095] {
                probe(MachInst::new(opcode, vec![gpr(1), gpr(2), imm(value)]));
                probe(MachInst::new(opcode, vec![zr.clone(), gpr(2), imm(value)]));
            }
        }
        for opcode in [Op::AndRI, Op::OrrRI, Op::EorRI] {
            for mask in [
                1i64,
                7,
                0xff00,
                0x5555_5555,
                0x8000_0000,
                -16,
                0x3333_3333_3333_3333,
                0x0f0f_0f0f_0f0f_0f0f,
            ] {
                probe(MachInst::new(opcode, vec![gpr(5), gpr(6), imm(mask)]));
            }
        }
        for mask in [1i64, 0xffff, 0xffff_fff0, 0x00ff_00ff_00ff_00ff] {
            probe(MachInst::new(Op::Tst, vec![gpr(9), imm(mask)]));
        }
        probe(MachInst::new(Op::Tst, vec![gpr(9), gpr(10)]));
        for amount in [0, 1, 13, 31, 63] {
            probe(MachInst::new(
                Op::RorRI,
                vec![gpr(11), gpr(12), imm(amount)],
            ));
        }
        for bit in [0, 5, 31, 32, 63] {
            for offset in [-8192, -1, 0, 1, 8191] {
                probe(MachInst::new(Op::Tbz, vec![gpr(4), imm(bit), imm(offset)]));
                probe(MachInst::new(Op::Tbnz, vec![gpr(4), imm(bit), imm(offset)]));
            }
        }
        for opcode in INTEGER_SLICE
            .into_iter()
            .filter(|op| {
                format!("{op:?}").starts_with("Ld") || format!("{op:?}").starts_with("Swp")
            })
            .filter(|op| {
                !matches!(
                    op,
                    Op::Ldar
                        | Op::Ldarb
                        | Op::Ldarh
                        | Op::LdrGot
                        | Op::LdrTlvp
                        | Op::LdrGottprel
                        | Op::LdrswRO
                )
            })
        {
            probe(MachInst::new(opcode, vec![gpr(1), gpr(2), x(3)]));
            probe(MachInst::new(
                opcode,
                vec![gpr(1), gpr(2), Arg::Special(SpecialReg::SP), imm(0)],
            ));
            probe(MachInst::new(opcode, vec![gpr(1), gpr(2), x(3), imm(1)]));
        }
        for opcode in [Op::Cas, Op::Casa, Op::Casal, Op::Casl] {
            probe(MachInst::new(opcode, vec![gpr(1), gpr(2), x(3)]));
            probe(MachInst::new(opcode, vec![gpr(1), gpr(2), x(3), imm(0)]));
        }
        for opcode in [
            Op::Ldar,
            Op::Ldarb,
            Op::Ldarh,
            Op::Stlr,
            Op::Stlrb,
            Op::Stlrh,
        ] {
            probe(MachInst::new(opcode, vec![gpr(1), x(3)]));
            probe(MachInst::new(
                opcode,
                vec![gpr(1), Arg::Special(SpecialReg::SP)],
            ));
        }
    }
    for opcode in [Op::Smulh, Op::Umulh] {
        probe(MachInst::new(opcode, vec![x(1), x(2), x(3)]));
    }
    probe(MachInst::new(Op::Umull, vec![x(1), w(2), w(3)]));
    probe(MachInst::new(Op::LdrswRO, vec![x(1), x(2), x(3)]));
    for option in 0..16 {
        for opcode in [Op::Dmb, Op::Dsb, Op::Isb] {
            probe(MachInst::new(opcode, vec![imm(option)]));
        }
    }
    // Scalar FP over every H/S/D width.
    for bank in [h, s, d] {
        for opcode in [
            Op::FaddRR,
            Op::FsubRR,
            Op::FmulRR,
            Op::FdivRR,
            Op::FminnmRR,
            Op::FmaxnmRR,
        ] {
            probe(MachInst::new(opcode, vec![bank(1), bank(30), bank(17)]));
        }
        probe(MachInst::new(
            Op::FmaddRR,
            vec![bank(1), bank(30), bank(17), bank(8)],
        ));
        for opcode in [
            Op::FnegRR,
            Op::FabsRR,
            Op::FsqrtRR,
            Op::FrintnRR,
            Op::FrintmRR,
            Op::FrintpRR,
            Op::FrintzRR,
            Op::FmovFprFpr,
        ] {
            probe(MachInst::new(opcode, vec![bank(19), bank(4)]));
        }
        for gpr in [w(3), x(3)] {
            probe(MachInst::new(Op::FcvtzsRR, vec![gpr.clone(), bank(25)]));
            probe(MachInst::new(Op::FcvtzuRR, vec![gpr.clone(), bank(25)]));
            probe(MachInst::new(Op::ScvtfRR, vec![bank(25), gpr.clone()]));
            probe(MachInst::new(Op::UcvtfRR, vec![bank(25), gpr.clone()]));
            probe(MachInst::new(Op::FmovFprGpr, vec![gpr.clone(), bank(25)]));
            probe(MachInst::new(Op::FmovGprFpr, vec![bank(25), gpr]));
        }
        for value in [0.125, 0.5, 1.0, -1.0, 2.0, 1.9375, -31.0, 17.0] {
            probe(MachInst::new(Op::FmovImm, vec![bank(6), fimm(value)]));
        }
        probe(MachInst::new(Op::Fcmp, vec![bank(1), bank(30)]));
    }
    for (opcode, dst, src) in [
        (Op::FcvtSD, d(1), s(2)),
        (Op::FcvtDS, s(1), d(2)),
        (Op::FcvtHS, s(1), h(2)),
        (Op::FcvtHD, d(1), h(2)),
        (Op::FcvtSH, h(1), s(2)),
        (Op::FcvtDH, h(1), d(2)),
    ] {
        probe(MachInst::new(opcode, vec![dst, src]));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // Denominators: every attempted shape and every one the encoder accepts.
    assert_eq!((attempted, encoded), (1774, 1584));
    // A bitwise op's trailing selector is the integer arrangement: the 64-bit
    // 4H/2S arrangements encode the 64-bit form (the encoder used to read any
    // nonzero selector as 16B), and a value outside 0..=6 is refused.
    for (selector, q) in [(0, 0), (1, 1), (2, 0), (3, 1), (4, 0), (5, 1), (6, 1)] {
        let word = encode_instruction(&MachInst::new(
            Op::NeonEorV,
            vec![v(1), v(2), v(3), imm(selector)],
        ))
        .expect("encodes");
        assert_eq!(word >> 30 & 1, q, "selector {selector}");
    }
    for selector in [7, -1] {
        assert!(
            encode_instruction(&MachInst::new(
                Op::NeonAndV,
                vec![v(1), v(2), v(3), imm(selector)],
            ))
            .is_err()
        );
    }
}

/// A slot of a mixed-view template: a general-purpose data register or zero
/// register whose W/X view varies, or a fixed operand.
enum Slot {
    Reg,
    Zero,
    Fixed(Arg),
}

/// Register allocation gives each operand the view of its value's class, so
/// one instruction can name registers in both widths: `AND Xd, Wn, #1` for a
/// Trunc to `Bool` (a 64-bit class) from a 32-bit value, and UMULL with 64-bit
/// sources from the masked-UMULL fusion. The machine IR's width comes from one
/// width-selecting operand or from the opcode; every other data register is
/// named by number. For every W/X assignment over the data registers of every
/// integer-slice form below, the encoder's word, when it accepts the shape,
/// is the word ENC-5 decodes, and every single-bit corruption of it is a
/// mismatch. Bases stay X/SP: ENC-5 (like its original memory arms) refuses a
/// W-view base.
#[test]
fn encoder_words_for_every_mixed_width_integer_view_match() {
    use Slot::{Fixed, Reg, Zero};
    use trust_cg_codegen::aarch64::encode::encode_instruction;
    let base = || Fixed(x(3));
    let mut templates: Vec<(Op, Vec<Slot>)> = Vec::new();
    for opcode in [Op::AddRRShift, Op::SubRRShift, Op::AddRRShiftLsr] {
        for amount in [1, 31] {
            templates.push((opcode, vec![Reg, Reg, Reg, Fixed(imm(amount))]));
        }
    }
    for opcode in [
        Op::AddsRR,
        Op::SubsRR,
        Op::Adc,
        Op::Sbc,
        Op::Adcs,
        Op::Sbcs,
        Op::BicRR,
    ] {
        templates.push((opcode, vec![Reg, Reg, Reg]));
        templates.push((opcode, vec![Zero, Reg, Reg]));
    }
    templates.push((Op::Neg, vec![Reg, Reg]));
    for opcode in [Op::AddsRI, Op::SubsRI] {
        templates.push((opcode, vec![Reg, Reg, Fixed(imm(4095))]));
        templates.push((opcode, vec![Zero, Reg, Fixed(imm(1))]));
    }
    for opcode in [Op::AndRI, Op::OrrRI, Op::EorRI] {
        for mask in [1, 0xff00, 0x5555_5555] {
            templates.push((opcode, vec![Reg, Reg, Fixed(imm(mask))]));
        }
    }
    templates.push((Op::Tst, vec![Reg, Reg]));
    templates.push((Op::Tst, vec![Reg, Fixed(imm(1))]));
    for amount in [0, 13] {
        templates.push((Op::RorRI, vec![Reg, Reg, Fixed(imm(amount))]));
    }
    for opcode in [Op::Smulh, Op::Umulh, Op::Umull] {
        templates.push((opcode, vec![Reg, Reg, Reg]));
    }
    templates.push((Op::AddPCRel, vec![Reg, Reg, Fixed(imm(8))]));
    templates.push((Op::Adrp, vec![Reg, Fixed(imm(4))]));
    templates.push((Op::Adr, vec![Reg, Fixed(imm(-4))]));
    for opcode in [Op::LdrGot, Op::LdrTlvp] {
        templates.push((opcode, vec![Reg, base(), Fixed(imm(16))]));
    }
    templates.push((Op::LdrswRO, vec![Reg, base(), Reg]));
    templates.push((Op::LdrLiteral, vec![Reg, Fixed(imm(12))]));
    for opcode in [Op::STRWui, Op::STRXui] {
        templates.push((opcode, vec![Reg, base(), Fixed(imm(8))]));
    }
    for opcode in [Op::Tbz, Op::Tbnz] {
        templates.push((opcode, vec![Reg, Fixed(imm(5)), Fixed(imm(12))]));
    }
    for opcode in INTEGER_SLICE {
        let name = format!("{opcode:?}");
        let lse = (name.starts_with("Ld") || name.starts_with("Swp"))
            && !matches!(
                opcode,
                Op::Ldar
                    | Op::Ldarb
                    | Op::Ldarh
                    | Op::LdrGot
                    | Op::LdrTlvp
                    | Op::LdrGottprel
                    | Op::LdrswRO
            );
        if lse || name.starts_with("Cas") {
            templates.push((opcode, vec![Reg, Reg, base()]));
            templates.push((opcode, vec![Reg, Reg, base(), Fixed(imm(0))]));
            templates.push((opcode, vec![Reg, Reg, base(), Fixed(imm(1))]));
        }
    }
    for opcode in [
        Op::Ldar,
        Op::Ldarb,
        Op::Ldarh,
        Op::Stlr,
        Op::Stlrb,
        Op::Stlrh,
    ] {
        templates.push((opcode, vec![Reg, base()]));
    }

    let (mut attempted, mut encoded, mut mixed) = (0, 0, 0);
    let mut failures = Vec::new();
    for (opcode, slots) in &templates {
        let varying = slots
            .iter()
            .filter(|slot| matches!(slot, Reg | Zero))
            .count();
        for views in 0u32..(1 << varying) {
            let mut next = 0;
            let operands: Vec<Arg> = slots
                .iter()
                .enumerate()
                .map(|(index, slot)| {
                    let Fixed(arg) = slot else {
                        let wide = views >> next & 1 == 1;
                        next += 1;
                        return match (slot, wide) {
                            (Zero, true) => Arg::Special(SpecialReg::XZR),
                            (Zero, false) => Arg::Special(SpecialReg::WZR),
                            (_, true) => x([5, 17, 26, 9][index]),
                            (_, false) => w([5, 17, 26, 9][index]),
                        };
                    };
                    arg.clone()
                })
                .collect();
            let inst = MachInst::new(*opcode, operands);
            attempted += 1;
            let Ok(word) = encode_instruction(&inst) else {
                continue;
            };
            encoded += 1;
            if views != 0 && views != (1 << varying) - 1 {
                mixed += 1;
            }
            match check(&inst, word, None) {
                DecodeCheckOutcome::Match => {
                    assert_every_bit_flip_mismatches(&inst, word, &mut failures)
                }
                other => failures.push(format!(
                    "{opcode:?} {:?} = {word:#010x}: {other:?}",
                    inst.operands
                )),
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // Denominators: every view assignment, every one the encoder accepts, and
    // the accepted ones that mix W and X views.
    assert_eq!((attempted, encoded, mixed), (772, 764, 411));

    // Scalar FP operands are different: ENC-5 requires one H/S/D width per
    // instruction, as its original FCMP and FCSEL arms did, and no machine-IR
    // convention names a width-selecting FP operand. The encoder reads `ftype`
    // from operand 0 and accepts most mixes built here (it refuses a half
    // FCSEL); each one it accepts is a mismatch (fail-closed on every route).
    let banks: [fn(u16) -> Arg; 3] = [h, s, d];
    let mut fp_mixed = 0;
    for (i, a) in banks.iter().enumerate() {
        for (j, b) in banks.iter().enumerate() {
            for (k, c) in banks.iter().enumerate() {
                let mut shapes = Vec::new();
                if i != j || j != k {
                    for opcode in [
                        Op::FaddRR,
                        Op::FsubRR,
                        Op::FmulRR,
                        Op::FdivRR,
                        Op::FminnmRR,
                        Op::FmaxnmRR,
                    ] {
                        shapes.push(MachInst::new(opcode, vec![a(1), b(2), c(3)]));
                    }
                    shapes.push(MachInst::new(Op::FcselRR, vec![a(1), b(2), c(3), imm(0)]));
                    shapes.push(MachInst::new(Op::FmaddRR, vec![a(1), b(2), c(3), a(4)]));
                }
                if k == 0 && i != j {
                    for opcode in [
                        Op::FnegRR,
                        Op::FabsRR,
                        Op::FsqrtRR,
                        Op::FmovFprFpr,
                        Op::FrintnRR,
                        Op::FrintmRR,
                        Op::Fcmp,
                    ] {
                        shapes.push(MachInst::new(opcode, vec![a(1), b(2)]));
                    }
                }
                for inst in shapes {
                    let Ok(word) = encode_instruction(&inst) else {
                        continue;
                    };
                    fp_mixed += 1;
                    assert!(
                        matches!(check(&inst, word, None), DecodeCheckOutcome::Mismatch(_)),
                        "{:?} {:?} = {word:#010x}",
                        inst.opcode,
                        inst.operands
                    );
                }
            }
        }
    }
    assert_eq!(fp_mixed, 204);
}

/// Real lowerings that name one register in both widths compile on the
/// compatibility and the proof-grade route: Trunc {I32, I16, U32, U16} to
/// `Bool` (`AND Xd, Wn, #1`), the masked-UMULL fusion (UMULL with 64-bit
/// source views) and each of the 12 F16 `fcmp` predicates (a half-precision
/// FCMP).
#[test]
fn mixed_width_and_half_precision_lowerings_compile_on_both_routes() {
    use trust_ir::{BinOp, CastOp, FCmpOp, Ty};
    use trust_ir_build::ModuleBuilder;
    type Body = Box<
        dyn Fn(&mut trust_ir_build::FunctionBuilder<'_>, &[trust_ir::ValueId]) -> trust_ir::ValueId,
    >;
    let compile = |params: Vec<Ty>, ret: Ty, body: Body| -> Vec<MachInst> {
        let mut builder = ModuleBuilder::new("enc5_mixed_views");
        let signature = builder.add_func_type(params.clone(), vec![ret]);
        let mut function = builder.function("f", signature);
        let entry = function.create_block();
        let args: Vec<_> = params
            .iter()
            .map(|ty| function.add_block_param(entry, ty.clone()))
            .collect();
        function.switch_to_block(entry);
        let result = body(&mut function, &args);
        function.ret(vec![result]);
        function.build();
        let module = builder.build().expect("ModuleBuilder::build: test fixture");
        assert!(trust_ir_build::validate::validate_module(&module).is_empty());
        let ir = module
            .functions
            .iter()
            .find(|f| f.name == "f")
            .expect("function");
        let (lir, _) = trust_cg_lower::adapter::translate_function_with_license(
            ir,
            &module,
            &permit_unlicensed(),
        )
        .expect("translates");
        let prepared = Pipeline::new(darwin_config())
            .prepare_function(&lir)
            .expect("prepares");
        for route in ["compatibility", "proof-grade"] {
            let pipeline = Pipeline::new(darwin_config())
                .with_proof_grade_aarch64_publication_if(route == "proof-grade");
            let object = pipeline
                .compile_module(std::slice::from_ref(&prepared))
                .unwrap_or_else(|error| panic!("{route} route: {error:?}"));
            assert_eq!(&object[..4], [0xcf, 0xfa, 0xed, 0xfe], "{route}");
        }
        prepared
            .block_order
            .iter()
            .flat_map(|&block| prepared.block(block).insts.iter())
            .map(|&id| prepared.inst(id).clone())
            .collect()
    };
    let encoding = |arg: &Arg| match arg {
        Arg::PReg(p) => p.encoding(),
        other => panic!("not a physical register: {other:?}"),
    };
    for from in [Ty::I32, Ty::I16, Ty::U32, Ty::U16] {
        let source = from.clone();
        let insts = compile(
            vec![from],
            Ty::Bool,
            Box::new(move |f, a| f.cast(CastOp::Trunc, source.clone(), Ty::Bool, a[0])),
        );
        assert!(
            insts.iter().any(|inst| inst.opcode == Op::AndRI
                && encoding(&inst.operands[0]) <= 30
                && (32..=62).contains(&encoding(&inst.operands[1]))),
            "no AND Xd, Wn, #1: {insts:?}"
        );
    }
    let insts = compile(
        vec![Ty::U64, Ty::U64],
        Ty::U64,
        Box::new(|f, a| {
            let low = f.iconst(Ty::U64, 0xFFFF_FFFF);
            let lhs = f.binop(BinOp::And, Ty::U64, a[0], low);
            let low = f.iconst(Ty::U64, 0xFFFF_FFFF);
            let rhs = f.binop(BinOp::And, Ty::U64, a[1], low);
            f.binop(BinOp::Mul, Ty::U64, lhs, rhs)
        }),
    );
    assert!(
        insts
            .iter()
            .any(|inst| inst.opcode == Op::Umull
                && inst.operands.iter().all(|arg| encoding(arg) <= 30)),
        "no UMULL with 64-bit source views: {insts:?}"
    );
    for predicate in [
        FCmpOp::OEq,
        FCmpOp::ONe,
        FCmpOp::OLt,
        FCmpOp::OLe,
        FCmpOp::OGt,
        FCmpOp::OGe,
        FCmpOp::UEq,
        FCmpOp::UNe,
        FCmpOp::ULt,
        FCmpOp::ULe,
        FCmpOp::UGt,
        FCmpOp::UGe,
    ] {
        let insts = compile(
            vec![Ty::F16, Ty::F16],
            Ty::Bool,
            Box::new(move |f, a| f.fcmp(predicate, Ty::F16, a[0], a[1])),
        );
        assert!(
            insts.iter().any(|inst| inst.opcode == Op::Fcmp
                && inst
                    .operands
                    .iter()
                    .all(|arg| (165..=196).contains(&encoding(arg)))),
            "{predicate:?}: no half-precision FCMP: {insts:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// The committed census
// ---------------------------------------------------------------------------

struct Sample {
    opcode: Op,
    policy: String,
    outcome: String,
    reason: String,
    word: u32,
    hole: Option<FixupHole>,
    inst: MachInst,
}

fn opcode_named(name: &str) -> Op {
    *trust_cg_verify::coverage_gate::ALL_AARCH64_OPCODES
        .iter()
        .find(|op| format!("{op:?}") == name)
        .unwrap_or_else(|| panic!("census names unknown opcode {name}"))
}

fn operand(token: &str) -> Arg {
    match token {
        "sp" => Arg::Special(SpecialReg::SP),
        "xzr" => Arg::Special(SpecialReg::XZR),
        "wzr" => Arg::Special(SpecialReg::WZR),
        "sym" => Arg::Symbol("census".into()),
        "esym" => Arg::ExactModuleSymbol("census".into()),
        "blk" => Arg::Block(BlockId(0)),
        "jt" => Arg::JumpTableIndex(0),
        _ => {
            if let Some(n) = token.strip_prefix('r') {
                Arg::PReg(PReg::new(n.parse().expect("register")))
            } else if let Some(value) = token.strip_prefix('#') {
                Arg::Imm(value.parse().expect("immediate"))
            } else if let Some(bits) = token.strip_prefix('f') {
                Arg::FImm(f64::from_bits(
                    u64::from_str_radix(bits, 16).expect("FImm bits"),
                ))
            } else if let Some(memory) = token.strip_prefix('m') {
                let (base, offset) = memory.split_once(':').expect("memory operand");
                Arg::MemOp {
                    base: PReg::new(base.parse().expect("base")),
                    offset: offset.parse().expect("offset"),
                }
            } else {
                panic!("unsupported census operand token {token}")
            }
        }
    }
}

fn hole(token: &str) -> Option<FixupHole> {
    if token == "-" {
        return None;
    }
    let mut parts = token.split(':');
    let kind = match parts.next() {
        Some("branch") => FixupHoleKind::Branch,
        Some("call") => FixupHoleKind::Call,
        Some("global") => FixupHoleKind::GlobalRef,
        Some("got") => FixupHoleKind::ExternRefGot,
        Some("tlv") => FixupHoleKind::TlsTlv,
        Some("constpool") => FixupHoleKind::ConstPool,
        other => panic!("unsupported hole kind {other:?}"),
    };
    Some(FixupHole {
        kind,
        offset_in_inst: parts.next().expect("offset").parse().expect("offset"),
        width: parts.next().expect("width").parse().expect("width"),
    })
}

struct Census {
    /// (opcode, policy, outcome, reason) -> instruction count.
    tallies: BTreeMap<(String, String, String, String), u64>,
    samples: Vec<Sample>,
}

fn census() -> Census {
    parse_census(CENSUS)
}

fn parse_census(text: &str) -> Census {
    let mut tallies = BTreeMap::new();
    let mut samples = Vec::new();
    for line in text.lines().filter(|line| !line.starts_with('#')) {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            ["T", opcode, policy, outcome, reason, count] => {
                tallies.insert(
                    (
                        opcode.to_string(),
                        policy.to_string(),
                        outcome.to_string(),
                        reason.to_string(),
                    ),
                    count.parse().expect("count"),
                );
            }
            ["E", ..] => {}
            [
                "S",
                opcode,
                policy,
                outcome,
                reason,
                word,
                hole_token,
                operands,
            ] => {
                let opcode = opcode_named(opcode);
                samples.push(Sample {
                    opcode,
                    policy: policy.to_string(),
                    outcome: outcome.to_string(),
                    reason: reason.to_string(),
                    word: u32::from_str_radix(word, 16).expect("word"),
                    hole: hole(hole_token),
                    inst: MachInst::new(
                        opcode,
                        operands
                            .split(' ')
                            .filter(|token| !token.is_empty())
                            .map(operand)
                            .collect(),
                    ),
                });
            }
            other => panic!("malformed census line {other:?}"),
        }
    }
    Census { tallies, samples }
}

fn outcome_name(outcome: &DecodeCheckOutcome) -> (&'static str, &'static str) {
    match outcome {
        DecodeCheckOutcome::Match => ("match", "-"),
        DecodeCheckOutcome::Allowlisted(reason) => ("allowlisted", reason),
        DecodeCheckOutcome::Mismatch(_) => ("mismatch", "-"),
    }
}

/// Replaying every committed sample reproduces its recorded outcome, and
/// every sample of the FP/SIMD and integer slices is a match whose every
/// single-bit corruption (outside fields a relocation or the final layout
/// owns) is a mismatch.
#[test]
fn census_samples_replay_and_new_slice_corruptions_mismatch() {
    let census = census();
    let mut failures = Vec::new();
    let (mut fp_simd_samples, mut integer_samples) = (0, 0);
    for sample in &census.samples {
        let outcome = check(&sample.inst, sample.word, sample.hole.as_ref());
        let (name, reason) = outcome_name(&outcome);
        if (name, reason) != (sample.outcome.as_str(), sample.reason.as_str()) {
            failures.push(format!(
                "{:?} {:?} = {:#010x}: recorded {} {}, replayed {outcome:?}",
                sample.opcode, sample.inst.operands, sample.word, sample.outcome, sample.reason
            ));
        }
        if sample.policy == "proof" && sample.outcome != "match" {
            failures.push(format!(
                "{:?}: a proof-grade sample must be decoded",
                sample.opcode
            ));
        }
        let fp_simd = is_fp_simd(sample.opcode);
        if !fp_simd && !is_integer_slice(sample.opcode) {
            continue;
        }
        if fp_simd {
            fp_simd_samples += 1;
        } else {
            integer_samples += 1;
        }
        if sample.outcome != "match" {
            failures.push(format!("{:?} sample is not a match", sample.opcode));
        }
        // Fields a relocation or the final layout owns are not ENC-5's: a
        // jump-table ADR's immediate and a branch-holed TBZ/TBNZ offset.
        let exempt: u32 = match (sample.opcode, sample.inst.operands.get(1), &sample.hole) {
            (Op::Adr, Some(Arg::JumpTableIndex(_)), None) => 0x60FF_FFE0,
            (Op::Tbz | Op::Tbnz, _, Some(_)) => 0x0007_FFE0,
            _ => 0,
        };
        for bit in (0..32).filter(|bit| exempt & (1 << bit) == 0) {
            let mutant = sample.word ^ (1 << bit);
            if !matches!(
                check(&sample.inst, mutant, sample.hole.as_ref()),
                DecodeCheckOutcome::Mismatch(_)
            ) {
                failures.push(format!(
                    "{:?} {:?}: bit {bit} flip {mutant:#010x} of {:#010x} was not a mismatch",
                    sample.opcode, sample.inst.operands, sample.word
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(
        (census.samples.len(), fp_simd_samples, integer_samples),
        CENSUS_SAMPLE_COUNTS
    );
}

// Pinned from the committed census; a re-measurement updates them.
const CENSUS_SAMPLE_COUNTS: (usize, usize, usize) = (1077, 303, 223);
const EMITTED: [&str; 227] = [
    "Adc",
    "AddPCRel",
    "AddRI",
    "AddRIShift12",
    "AddRR",
    "AddRRShift",
    "AddRRShiftLsr",
    "AddTlsdescLo12",
    "AddTprelHi12",
    "AddTprelLo12",
    "AddsRR",
    "Adr",
    "Adrp",
    "AlignNop",
    "AndRI",
    "AndRR",
    "AsrRI",
    "AsrRR",
    "B",
    "BCond",
    "Bfm",
    "Bl",
    "Blr",
    "BlrTlsdesc",
    "Br",
    "Brk",
    "CSet",
    "Cas",
    "Casa",
    "Casal",
    "Casl",
    "Cbnz",
    "Cbz",
    "Clrex",
    "CmpRI",
    "CmpRR",
    "Csel",
    "Csinc",
    "Dmb",
    "EorRI",
    "EorRR",
    "EorRRLsl",
    "EorRRLsr",
    "EorRRShift",
    "FabsRR",
    "FaddRR",
    "Fcmp",
    "FcselRR",
    "FcvtDH",
    "FcvtHD",
    "FcvtHS",
    "FcvtSD",
    "FcvtSH",
    "FcvtzsRR",
    "FcvtzuRR",
    "FdivRR",
    "FmaddRR",
    "FmaxnmRR",
    "FminnmRR",
    "FmovFprFpr",
    "FmovFprGpr",
    "FmovGprFpr",
    "FmovImm",
    "FmulRR",
    "FnegRR",
    "FrintmRR",
    "FrintpRR",
    "FrintzRR",
    "FsqrtRR",
    "FsubRR",
    "Ldaddal",
    "Ldar",
    "Ldarb",
    "Ldaxp",
    "Ldaxr",
    "Ldaxrb",
    "Ldaxrh",
    "Ldclr",
    "Ldclra",
    "Ldclral",
    "Ldclrl",
    "Ldeor",
    "Ldeora",
    "Ldeoral",
    "Ldeorl",
    "LdpPostIndex",
    "LdpRI",
    "LdrGot",
    "LdrGottprel",
    "LdrPostIndex",
    "LdrRI",
    "LdrRO",
    "LdrTlsdesc",
    "LdrTlvp",
    "LdrbRI",
    "LdrbRO",
    "LdrhRI",
    "LdrhRO",
    "LdrsbRI",
    "LdrshRI",
    "LdrswRO",
    "Ldset",
    "Ldseta",
    "Ldsetal",
    "Ldsetl",
    "Ldsmaxal",
    "Ldsminal",
    "Ldumaxal",
    "Lduminal",
    "Ldxp",
    "Ldxr",
    "Ldxrb",
    "Ldxrh",
    "LslRI",
    "LslRR",
    "LsrRI",
    "LsrRR",
    "MOVWrr",
    "MOVXrr",
    "Madd",
    "MovI",
    "MovR",
    "Movk",
    "Movn",
    "Movz",
    "Mrs",
    "Msub",
    "MulRR",
    "Neg",
    "NeonAbsV",
    "NeonAddV",
    "NeonAndV",
    "NeonBicV",
    "NeonCntV",
    "NeonDupElem",
    "NeonDupGen",
    "NeonDupScalarD",
    "NeonEorV",
    "NeonFaddV",
    "NeonFdivV",
    "NeonFmlaV",
    "NeonFmulV",
    "NeonFsubV",
    "NeonInsGen",
    "NeonLd1Post",
    "NeonLdpQPost",
    "NeonMovi",
    "NeonMulV",
    "NeonOrrV",
    "NeonRbitV",
    "NeonRev32V",
    "NeonRev64V",
    "NeonSaddlpV",
    "NeonScvtfV",
    "NeonShlVImm",
    "NeonSmlal2V",
    "NeonSmlalV",
    "NeonSshrVImm",
    "NeonSt1Post",
    "NeonStpQPost",
    "NeonSubV",
    "NeonUadalpV",
    "NeonUaddlpV",
    "NeonUdotV",
    "NeonUmlal2V",
    "NeonUmlalV",
    "NeonUmovGen",
    "NeonUshrVImm",
    "Nop",
    "OrnRR",
    "OrrRI",
    "OrrRR",
    "Rbit",
    "Ret",
    "RorRI",
    "SDiv",
    "Sbc",
    "Sbcs",
    "Sbfm",
    "ScvtfRR",
    "Smulh",
    "Smull",
    "Stlr",
    "Stlrb",
    "Stlxp",
    "Stlxr",
    "Stlxrb",
    "Stlxrh",
    "StpPreIndex",
    "StpRI",
    "StrRI",
    "StrRO",
    "StrbRI",
    "StrhRI",
    "Stxp",
    "Stxr",
    "Stxrb",
    "Stxrh",
    "SubRI",
    "SubRR",
    "SubRRShift",
    "SubsRI",
    "SubsRR",
    "Swp",
    "Swpa",
    "Swpal",
    "Swpl",
    "Sxtb",
    "Sxth",
    "Sxtw",
    "TailCall",
    "Tbnz",
    "TrapDivZero",
    "Tst",
    "UDiv",
    "Ubfm",
    "UcvtfRR",
    "Umulh",
    "Umull",
    "Uxtb",
    "Uxth",
    "Uxtw",
    "VolatileLdrRI",
    "VolatileLdrbRI",
    "VolatileLdrhRI",
    "VolatileStrRI",
    "VolatileStrhRI",
];
const STILL_ALLOWLISTED: [(&str, &str); 0] = [];
const CENSUS_TOTALS: (u64, u64, u64) = (5012456, 0, 297);
/// Before L10-P6, 127 of the then 325 opcodes had an arm (`check_one`'s own
/// match); since, every opcode but these 18 has one (FRINTN, the 326th,
/// included), and none of these reaches the encoder as a word: the opaque
/// LL/SC carriers the post-RA expansion replaces and the pseudo-instructions
/// callers skip. Since L04-P12 the five exact guard carriers have an arm that
/// refuses their word (only their expansion is ever emitted).
const ENC5_WITHOUT_ARM: [&str; 18] = [
    "LlscRmw8",
    "LlscRmw16",
    "LlscRmw32",
    "LlscRmw64",
    "LlscCmpSwap8",
    "LlscCmpSwap16",
    "LlscCmpSwap32",
    "LlscCmpSwap64",
    "LlscLoad128",
    "LlscStore128",
    "LlscRmw128",
    "LlscCmpSwap128",
    "Phi",
    "StackAlloc",
    "Copy",
    "TlsDescCall",
    "Retain",
    "Release",
];

/// The opcodes the floor emitted and the ones ENC-5 still does not decode
/// there are pinned; no scalar FP or Advanced SIMD form is among the latter,
/// and nothing emitted is a mismatch.
#[test]
fn census_emitted_and_undecoded_forms_are_pinned() {
    let census = census();
    let emitted: BTreeSet<&str> = census.tallies.keys().map(|key| key.0.as_str()).collect();
    assert_eq!(emitted.into_iter().collect::<Vec<_>>(), EMITTED);
    let allowlisted: BTreeSet<(&str, &str)> = census
        .tallies
        .keys()
        .filter(|key| key.2 == "allowlisted")
        .map(|key| (key.0.as_str(), key.3.as_str()))
        .collect();
    assert_eq!(
        allowlisted.into_iter().collect::<Vec<_>>(),
        STILL_ALLOWLISTED
    );
    for (opcode, _) in STILL_ALLOWLISTED {
        assert!(!is_fp_simd(opcode_named(opcode)), "{opcode}");
    }
    assert!(
        census.tallies.keys().all(|key| key.2 != "mismatch"),
        "a census run is a passing compile; a mismatch cannot be recorded"
    );
    // A proof-grade compile refuses an undecoded word, so every proof-grade
    // word the census recorded was decoded.
    assert!(
        census
            .tallies
            .keys()
            .filter(|key| key.1 == "proof")
            .all(|key| key.2 == "match"),
        "a proof-grade route recorded an undecoded word"
    );
    assert_eq!(census_totals(&census), CENSUS_TOTALS);
}

/// (instructions checked, of them allowlisted; proof-grade instructions).
fn census_totals(census: &Census) -> (u64, u64, u64) {
    let mut totals = (0, 0, 0);
    for (key, count) in &census.tallies {
        totals.0 += count;
        if key.2 == "allowlisted" {
            totals.1 += count;
        }
        if key.1 == "proof" {
            totals.2 += count;
        }
    }
    totals
}

/// The census measured before L10-P6: the same 227 opcodes, 114 of them
/// with undecoded words (113 to the catch-all, NEON 8B EOR to a named exit),
/// 435,921 of 5,012,423 checked instructions and 19 of the 297 proof-grade
/// ones. Every one of its real samples, including each undecoded one, is
/// now decoded to a match.
#[test]
fn every_sample_undecoded_before_l10_p6_now_decodes() {
    let before = parse_census(CENSUS_BEFORE_L10_P6);
    let emitted: BTreeSet<&str> = before.tallies.keys().map(|key| key.0.as_str()).collect();
    assert_eq!(emitted.into_iter().collect::<Vec<_>>(), EMITTED);
    let undecoded: BTreeSet<&str> = before
        .tallies
        .keys()
        .filter(|key| key.2 == "allowlisted")
        .map(|key| key.0.as_str())
        .collect();
    assert_eq!(undecoded.len(), 114);
    let proof_undecoded: u64 = before
        .tallies
        .iter()
        .filter(|(key, _)| key.1 == "proof" && key.2 == "allowlisted")
        .map(|(_, count)| count)
        .sum();
    assert_eq!(
        (census_totals(&before), proof_undecoded),
        ((5_012_423, 435_921, 297), 19)
    );
    let mut failures = Vec::new();
    let mut formerly_undecoded = 0;
    for sample in &before.samples {
        formerly_undecoded += usize::from(sample.outcome == "allowlisted");
        let outcome = check(&sample.inst, sample.word, sample.hole.as_ref());
        if !matches!(outcome, DecodeCheckOutcome::Match) {
            failures.push(format!(
                "{:?} {:?} = {:#010x} (recorded {}): {outcome:?}",
                sample.opcode, sample.inst.operands, sample.word, sample.outcome
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!((before.samples.len(), formerly_undecoded), (1083, 473));
}

/// The AArch64 opcodes ENC-5 has no arm for (its catch-all allowlist):
/// pseudo-instructions that never reach the encoder as a word, the opaque
/// LL/SC carriers the post-RA expansion replaces, and the forms the backend
/// refuses to encode. Every other opcode is decoded by an arm; since L04-P12
/// the five conditional trap carriers have one that refuses any word recorded
/// for them (only their expansion is emitted).
#[test]
fn enc5_opcodes_without_an_arm_are_pinned() {
    use trust_cg_codegen::aarch64::decode_check::A64_UNDECODED_FAMILY;
    let without_arm: Vec<String> = trust_cg_verify::coverage_gate::ALL_AARCH64_OPCODES
        .iter()
        .copied()
        .filter(|&op| {
            matches!(
                check(&MachInst::new(op, vec![]), 0, None),
                DecodeCheckOutcome::Allowlisted(reason) if reason == A64_UNDECODED_FAMILY
            )
        })
        .map(|op| format!("{op:?}"))
        .collect();
    assert_eq!(without_arm, ENC5_WITHOUT_ARM);
    assert_eq!(
        (
            trust_cg_verify::coverage_gate::ALL_AARCH64_OPCODES.len(),
            without_arm.len()
        ),
        (334, ENC5_WITHOUT_ARM.len())
    );
}

/// One post-allocation function: `MRS X0, FPCR` (a system-register key the
/// decoded-value model does not cover, so ENC-5 names it and decodes nothing)
/// followed by `RET`.
fn undecoded_mrs_function() -> MachFunction {
    let mut func = MachFunction::new(
        "reads_fpcr".to_string(),
        Signature::new(vec![], vec![Type::I64]),
    );
    let entry = func.entry;
    let mrs = func.push_inst(MachInst::new(Op::Mrs, vec![x(0), imm(0xDA20)]));
    func.append_inst(entry, mrs);
    let ret =
        func.push_inst(MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[trust_cg_ir::regs::X0]));
    func.append_inst(entry, ret);
    func
}

fn darwin_config() -> PipelineConfig {
    PipelineConfig {
        target_triple: "aarch64-apple-darwin".to_owned(),
        verify: false,
        ..Default::default()
    }
}

/// A proof-grade route refuses an emitted word ENC-5 does not decode, by
/// name; a compatibility route counts it and compiles.
#[test]
fn proof_grade_route_refuses_an_undecoded_emitted_form() {
    let func = undecoded_mrs_function();
    let word = 0xD53B_4400u32; // MRS X0, FPCR
    assert!(matches!(
        check(&MachInst::new(Op::Mrs, vec![x(0), imm(0xDA20)]), word, None),
        DecodeCheckOutcome::Allowlisted(_)
    ));
    let compatibility = Pipeline::new(darwin_config())
        .compile_module(std::slice::from_ref(&func))
        .expect("a compatibility route counts an undecoded word");
    assert_eq!(&compatibility[..4], [0xcf, 0xfa, 0xed, 0xfe]);
    match Pipeline::new(darwin_config())
        .with_proof_grade_aarch64_publication()
        .compile_module(std::slice::from_ref(&func))
    {
        Err(PipelineError::Encoding(message)) => {
            assert!(
                message.contains(UNDECODED_EMISSION_REFUSAL_TAG),
                "{message}"
            );
            assert!(message.contains("Mrs"), "{message}");
            assert!(
                message.contains("a64-value: shape outside the decoded value model"),
                "{message}"
            );
        }
        other => panic!("a proof-grade route must refuse the undecoded MRS word, got {other:?}"),
    }
}

/// Scalar FP, Advanced SIMD and integer-slice forms from real lowering
/// compile on a proof-grade route: every word they emit is decoded.
#[test]
fn proof_grade_route_compiles_fp_simd_and_integer_slice_forms() {
    use trust_ir::{BinOp, CastOp, Ty};
    use trust_ir_build::ModuleBuilder;
    let mut builder = ModuleBuilder::new("enc5_proof_grade");
    let signature = builder.add_func_type(vec![Ty::F64, Ty::F64, Ty::I64], vec![Ty::I64]);
    let mut function = builder.function("mix", signature);
    let entry = function.create_block();
    let a = function.add_block_param(entry, Ty::F64);
    let b = function.add_block_param(entry, Ty::F64);
    let n = function.add_block_param(entry, Ty::I64);
    function.switch_to_block(entry);
    let product = function.binop(BinOp::FMul, Ty::F64, a, b);
    let sum = function.binop(BinOp::FAdd, Ty::F64, product, a);
    let quotient = function.binop(BinOp::FDiv, Ty::F64, sum, b);
    let truncated = function.cast(CastOp::FPToSI, Ty::F64, Ty::I64, quotient);
    let seven = function.iconst(Ty::I64, 0x0F0F);
    let masked = function.binop(BinOp::And, Ty::I64, n, seven);
    let three = function.iconst(Ty::I64, 3);
    let scaled = function.binop(BinOp::Mul, Ty::I64, masked, three);
    let total = function.binop(BinOp::Add, Ty::I64, scaled, truncated);
    function.ret(vec![total]);
    function.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let ir = module
        .functions
        .iter()
        .find(|f| f.name == "mix")
        .expect("function");
    let (lir, _) =
        trust_cg_lower::adapter::translate_function_with_license(ir, &module, &permit_unlicensed())
            .expect("translates");
    let prepared = Pipeline::new(darwin_config())
        .prepare_function(&lir)
        .expect("prepares");
    let opcodes: BTreeSet<String> = prepared
        .block_order
        .iter()
        .flat_map(|&block| prepared.block(block).insts.iter())
        .map(|&id| format!("{:?}", prepared.inst(id).opcode))
        .collect();
    for required in ["FmulRR", "FaddRR", "FdivRR", "FcvtzsRR"] {
        assert!(
            opcodes.contains(required),
            "{required} not emitted: {opcodes:?}"
        );
    }
    let object = Pipeline::new(darwin_config())
        .with_proof_grade_aarch64_publication()
        .compile_module(std::slice::from_ref(&prepared))
        .expect("every emitted word is decoded on the proof-grade route");
    assert_eq!(&object[..4], [0xcf, 0xfa, 0xed, 0xfe]);
}

/// FRINTN reaches the backend only through the `trust-cg-aarch64-fp` dialect's
/// `frintn` (the rustc bridge's inline-assembly recognizer), which no Darwin
/// floor target lowers, so the committed census holds no FRINTN sample. Its
/// f32 and f64 lowerings emit one FRINTN with S or D registers and compile on
/// both routes; a proof-grade route refuses a word ENC-5 does not decode.
/// The emitted form's word decodes to a match and every single-bit
/// corruption of it is a mismatch.
#[test]
fn frintn_dialect_lowering_compiles_on_both_routes() {
    use trust_cg_codegen::aarch64::encode::encode_instruction;
    use trust_cg_lower::aarch64_fp_dialect::{Operation, instruction};
    use trust_ir::Ty;
    use trust_ir_build::ModuleBuilder;
    let mut failures = Vec::new();
    for (ty, bank) in [(Ty::F32, 128..=159u16), (Ty::F64, 96..=127)] {
        let mut builder = ModuleBuilder::new("enc5_frintn");
        let signature = builder.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let mut function = builder.function("round_ties_even", signature);
        let entry = function.create_block();
        let input = function.add_block_param(entry, ty.clone());
        function.switch_to_block(entry);
        let rounded = function.dialect_op(instruction(Operation::Frintn, ty.clone(), &[input]));
        function.ret(rounded);
        function.build();
        let module = builder.build().expect("ModuleBuilder::build: test fixture");
        let ir = module
            .functions
            .iter()
            .find(|f| f.name == "round_ties_even")
            .expect("function");
        let (lir, _) = trust_cg_lower::adapter::translate_function_with_license(
            ir,
            &module,
            &permit_unlicensed(),
        )
        .expect("translates");
        let prepared = Pipeline::new(darwin_config())
            .prepare_function(&lir)
            .expect("prepares");
        let frintn: Vec<MachInst> = prepared
            .block_order
            .iter()
            .flat_map(|&block| prepared.block(block).insts.iter())
            .map(|&id| prepared.inst(id).clone())
            .filter(|inst| inst.opcode == Op::FrintnRR)
            .collect();
        assert_eq!(frintn.len(), 1, "{ty:?}: {frintn:?}");
        assert!(
            frintn[0]
                .operands
                .iter()
                .all(|arg| matches!(arg, Arg::PReg(p) if bank.contains(&p.encoding()))),
            "{ty:?}: {:?}",
            frintn[0].operands
        );
        for route in ["compatibility", "proof-grade"] {
            let object = Pipeline::new(darwin_config())
                .with_proof_grade_aarch64_publication_if(route == "proof-grade")
                .compile_module(std::slice::from_ref(&prepared))
                .unwrap_or_else(|error| panic!("{ty:?} {route} route: {error:?}"));
            assert_eq!(&object[..4], [0xcf, 0xfa, 0xed, 0xfe], "{ty:?} {route}");
        }
        let word = encode_instruction(&frintn[0]).expect("encodes");
        assert!(
            matches!(check(&frintn[0], word, None), DecodeCheckOutcome::Match),
            "{ty:?} {:?} = {word:#010x}",
            frintn[0].operands
        );
        assert_every_bit_flip_mismatches(&frintn[0], word, &mut failures);
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The eight FEAT_CRC32 forms (ledger L03-P9), selected only inside a
/// function whose admission includes `crc`. No committed-census floor
/// measurement predates them, so their rows are here:
/// * words assembled by Apple clang 21 (`-march=armv8-a+crc`,
///   aarch64-apple-macos) and read back with `otool -tvj`, each decoding to
///   a match with every single-bit corruption a mismatch, including the
///   zero-register operands and the X data register of the doubleword forms;
/// * the live encoder's word for every W/X view of the three registers (the
///   width is the opcode's), each a match with the all-bits corruption
///   control, and SP refused by the encoder and a mismatch in ENC-5;
/// * a TrustIR `llvm.aarch64.crc32cx` call in a function stating `crc`
///   compiles on the compatibility and the proof-grade route.
#[test]
fn crc32_words_decode_and_compile_on_both_routes() {
    use trust_cg_codegen::aarch64::encode::encode_instruction;
    let zr = || Arg::Special(SpecialReg::WZR);
    let xzr = || Arg::Special(SpecialReg::XZR);
    let rows: [(Op, Vec<Arg>, u32); 9] = [
        (Op::Crc32B, vec![w(0), w(1), w(2)], 0x1ac2_4020),
        (Op::Crc32H, vec![w(3), w(4), w(5)], 0x1ac5_4483),
        (Op::Crc32W, vec![w(30), zr(), w(17)], 0x1ad1_4bfe),
        (Op::Crc32X, vec![w(6), w(7), x(8)], 0x9ac8_4ce6),
        (Op::Crc32Cb, vec![w(9), w(10), w(11)], 0x1acb_5149),
        (Op::Crc32Ch, vec![w(12), w(13), zr()], 0x1adf_55ac),
        (Op::Crc32Cw, vec![w(14), w(15), w(16)], 0x1ad0_59ee),
        (Op::Crc32Cx, vec![zr(), w(29), x(30)], 0x9ade_5fbf),
        (Op::Crc32X, vec![w(1), w(2), xzr()], 0x9adf_4c41),
    ];
    let mut failures = Vec::new();
    for (opcode, operands, word) in rows {
        let inst = MachInst::new(opcode, operands);
        match check(&inst, word, None) {
            DecodeCheckOutcome::Match => {}
            other => failures.push(format!("{opcode:?} {word:#010x}: {other:?}")),
        }
        assert_every_bit_flip_mismatches(&inst, word, &mut failures);
        // Another form's word is not this intent.
        for other in [Op::Crc32B, Op::Crc32Cx, Op::UDiv] {
            if other != opcode {
                let foreign = MachInst::new(other, inst.operands.clone());
                if matches!(check(&foreign, word, None), DecodeCheckOutcome::Match) {
                    failures.push(format!("{other:?} matched {opcode:?}'s word {word:#010x}"));
                }
            }
        }
    }
    let views = |n: u16| [w(n), x(n)];
    let mut encoded = 0;
    for opcode in [
        Op::Crc32B,
        Op::Crc32H,
        Op::Crc32W,
        Op::Crc32X,
        Op::Crc32Cb,
        Op::Crc32Ch,
        Op::Crc32Cw,
        Op::Crc32Cx,
    ] {
        for rd in views(3) {
            for rn in views(17) {
                for rm in views(30) {
                    let inst = MachInst::new(opcode, vec![rd.clone(), rn.clone(), rm]);
                    let word = encode_instruction(&inst).expect("every GPR view encodes");
                    encoded += 1;
                    if !matches!(check(&inst, word, None), DecodeCheckOutcome::Match) {
                        failures.push(format!("{opcode:?} {:?} = {word:#010x}", inst.operands));
                    }
                    assert_every_bit_flip_mismatches(&inst, word, &mut failures);
                }
            }
        }
        let sp = MachInst::new(opcode, vec![w(1), Arg::Special(SpecialReg::SP), w(2)]);
        assert!(
            encode_instruction(&sp).is_err(),
            "{opcode:?}: SP is not encodable"
        );
        let with_zr = MachInst::new(opcode, vec![w(1), zr(), w(2)]);
        let word = encode_instruction(&with_zr).expect("ZR encodes");
        if !matches!(check(&sp, word, None), DecodeCheckOutcome::Mismatch(_)) {
            failures.push(format!("{opcode:?}: an SP intent matched a ZR word"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(encoded, 64);

    use trust_ir::Ty;
    use trust_ir_build::ModuleBuilder;
    let mut builder = ModuleBuilder::new("enc5_crc32");
    let signature = builder.add_func_type(vec![Ty::U32, Ty::U64], vec![Ty::U32]);
    let intrinsic = builder.declare_function("llvm.aarch64.crc32cx", signature);
    let mut function = builder.function("crc_step", signature);
    let entry = function.create_block();
    let crc = function.add_block_param(entry, Ty::U32);
    let data = function.add_block_param(entry, Ty::U64);
    function.switch_to_block(entry);
    let out = function.call(intrinsic, vec![crc, data]);
    function.ret(vec![out]);
    function.build();
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    let ir = module
        .functions
        .iter_mut()
        .find(|f| f.name == "crc_step")
        .expect("function");
    ir.attrs.target_features = vec!["crc".to_owned()];
    let ir = ir.clone();
    let (lir, _) =
        trust_cg_lower::translate_function_with_license(&ir, &module, &permit_unlicensed())
            .expect("translates");
    let prepared = Pipeline::new(darwin_config())
        .prepare_function(&lir)
        .expect("prepares");
    let crc_words = prepared
        .block_order
        .iter()
        .flat_map(|&block| prepared.block(block).insts.iter())
        .filter(|&&id| prepared.inst(id).opcode == Op::Crc32Cx)
        .count();
    assert_eq!(crc_words, 1);
    for route in ["compatibility", "proof-grade"] {
        let object = Pipeline::new(darwin_config())
            .with_proof_grade_aarch64_publication_if(route == "proof-grade")
            .compile_module(std::slice::from_ref(&prepared))
            .unwrap_or_else(|error| panic!("{route} route: {error:?}"));
        assert_eq!(&object[..4], [0xcf, 0xfa, 0xed, 0xfe], "{route}");
    }
}

/// The trust-ir fixtures above are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Their lowering states `Permit` explicitly, so no
/// form is censused, or refused, because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
