// trust-cg-lift/disasm/aarch64 - AArch64 instruction decoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 instruction decoder.
//!
//! This module is the Phase 1 binary-lifting entry point. The decoded forms
//! mirror the low-level forward encoder fields so tests can assert
//! `decode(encode(fields)) == fields` without involving CFG or trust_ir recovery.
//!
//! # What this decoder is for
//!
//! It is a **development-time ORACLE**, and it is depended on as one:
//! `trust-cg-codegen`'s on-host AArch64 harness (`tests/common/a64_interp.rs`)
//! decodes the emitted `__TEXT,__text` with [`decode`] and interprets it,
//! because that box is x86 and native A64 execution is hardware-blocked. Nine
//! codegen test binaries grade the AArch64 backend through it. A word this
//! decoder accepts and mis-names is therefore a word the harness EXECUTES with
//! the wrong semantics, and a miscompile can pass green behind it. That makes
//! decode-or-reject fidelity a correctness property of this file, not a
//! convenience.
//!
//! # What it must never be used for
//!
//! * **It is not a trusted, shipped component and must not become one by
//!   accident.** `trust-cg-lift` is reachable only as a `dev-dependency` of
//!   `trust-cg-codegen`; dev-dependencies do not propagate, so no production
//!   binary, gate, or emitted artifact can contain it. `tests/crate_is_not_in_the_gate_path.rs`
//!   ENFORCES that: it fails if any non-dev edge to this crate appears.
//!   Promoting it (e.g. the ENC-5 aarch64 `decode_check` instantiation sketched
//!   in `trust-cg-codegen/src/decode_check.rs`) is a deliberate act that must
//!   update that test and re-run the objdump differential first.
//! * **It is not a full A64 disassembler.** It covers the surface trust-cg's
//!   AArch64 backend emits. `trust-disasm` is the decoder the trust-cg output
//!   gate depends on; the two are independent and neither validates the other.
//! * **Its acceptance set must never be widened for convenience.** Every arm
//!   below refuses what the architecture does not allocate. Refusing is always
//!   acceptable; approximating an unallocated or differently-allocated word onto
//!   a neighbouring instruction never is — that is precisely how a silently
//!   ACCEPTED case becomes a soundness hole with a delay fuse.
//!
//! # Allocation fidelity
//!
//! Every "unallocated" claim in this file was measured against Apple/LLVM 21
//! `objdump` on words assembled verbatim via `.incbin` (never hand-encoded), and
//! is regression-pinned by `tests/aarch64_allocation.rs`.

use thiserror::Error;

const AARCH64_NOP: u32 = 0xd503_201f;
const AARCH64_BRK_1: u32 = 0xd420_0020;

/// Errors produced while decoding a single AArch64 instruction word.
#[derive(Debug, Error, Clone, Copy, PartialEq, Eq)]
pub enum DecodeError {
    /// The word is in an instruction family this Phase 1 decoder does not cover.
    #[error("unsupported AArch64 instruction word 0x{word:08x}")]
    Unsupported { word: u32 },
    /// The word matched a known family but uses an unallocated/reserved field.
    #[error("unallocated AArch64 instruction word 0x{word:08x}: {reason}")]
    Unallocated { word: u32, reason: &'static str },
    /// The encoding is allocated, but this operand combination has no single
    /// architectural meaning and therefore cannot be lifted soundly.
    #[error("constrained-unpredictable AArch64 instruction word 0x{word:08x}: {reason}")]
    ConstrainedUnpredictable { word: u32, reason: &'static str },
}

/// A decoded AArch64 instruction in the Phase 1 MachIR-level representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
    AddSubShiftedReg(AddSubShiftedReg),
    LogicalShiftedReg(LogicalShiftedReg),
    LogicalImm(LogicalImm),
    AddSubImm(AddSubImm),
    AddSubCarry(AddSubCarry),
    MoveWide(MoveWide),
    BitfieldMove(BitfieldMove),
    PcRelAddress(PcRelAddress),
    CondBranch(CondBranch),
    UncondBranch(UncondBranch),
    BranchReg(BranchReg),
    TestBranch(TestBranch),
    LoadStoreUnsignedImm(LoadStoreUnsignedImm),
    LoadStoreUnscaled(LoadStoreUnscaled),
    LoadStoreIndexed(LoadStoreIndexed),
    LoadStoreRegister(LoadStoreRegister),
    LoadLiteral(LoadLiteral),
    LoadStorePair(LoadStorePair),
    LoadStoreAcquireRelease(LoadStoreAcquireRelease),
    LoadStoreExclusiveAcquireRelease(LoadStoreExclusiveAcquireRelease),
    CompareAndSwap(CompareAndSwap),
    LseAtomicRmw(LseAtomicRmw),
    CompareBranch(CompareBranch),
    DataProcessing2Source(DataProcessing2Source),
    DataProcessing3Source(DataProcessing3Source),
    ConditionalSelect(ConditionalSelect),
    FpArith(FpArith),
    FpCompare(FpCompare),
    FpIntConversion(FpIntConversion),
    FpUnary(FpUnary),
    FpPrecisionConvert(FpPrecisionConvert),
    FpImmediate(FpImmediate),
    Nop,
    Brk(Brk),
    SystemBarrier(SystemBarrier),
    SystemRegisterRead(SystemRegisterRead),
    NeonIntVec3Same(NeonIntVec3Same),
    NeonVecLogic(NeonVecLogic),
    NeonFpVec3Same(NeonFpVec3Same),
    NeonVecNot(NeonVecNot),
    NeonAcrossLanes(NeonAcrossLanes),
    NeonDupElement(NeonDupElement),
    NeonDupGeneral(NeonDupGeneral),
    NeonInsGeneral(NeonInsGeneral),
    NeonMoviByte(NeonMoviByte),
    NeonLdStSinglePostImm(NeonLdStSinglePostImm),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AddSubShiftedReg {
    pub sf: u8,
    pub op: u8,
    pub set_flags: bool,
    pub shift: u8,
    pub rm: u8,
    pub imm6: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LogicalShiftedReg {
    pub sf: u8,
    pub opc: u8,
    pub shift: u8,
    pub n: bool,
    pub rm: u8,
    pub imm6: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LogicalImm {
    pub sf: u8,
    pub opc: u8,
    pub n: bool,
    pub immr: u8,
    pub imms: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AddSubImm {
    pub sf: u8,
    pub op: u8,
    pub set_flags: bool,
    pub shift12: bool,
    pub imm12: u16,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AddSubCarry {
    pub sf: u8,
    pub op: u8,
    pub set_flags: bool,
    pub rm: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MoveWide {
    pub sf: u8,
    pub opc: u8,
    pub hw: u8,
    pub imm16: u16,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BitfieldMove {
    pub sf: u8,
    pub opc: u8,
    pub immr: u8,
    pub imms: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PcRelAddress {
    pub page: bool,
    pub imm21: i32,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CondBranch {
    pub imm19: u32,
    pub cond: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UncondBranch {
    pub link: bool,
    pub imm26: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BranchReg {
    pub opc: u8,
    pub rn: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TestBranch {
    pub nonzero: bool,
    pub bit: u8,
    pub imm14: u16,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoadStoreUnsignedImm {
    pub size: u8,
    pub vector: bool,
    pub opc: u8,
    pub imm12: u16,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoadStoreUnscaled {
    pub size: u8,
    pub vector: bool,
    pub opc: u8,
    pub imm9: i16,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoadStoreIndexed {
    pub size: u8,
    pub vector: bool,
    pub opc: u8,
    pub imm9: i16,
    pub mode: LoadStoreIndexMode,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoadStoreIndexMode {
    PostIndex,
    PreIndex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoadStoreRegister {
    pub size: u8,
    pub vector: bool,
    pub opc: u8,
    pub rm: u8,
    pub option: u8,
    pub shift: bool,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoadLiteral {
    pub opc: u8,
    pub vector: bool,
    pub imm19: u32,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoadStorePair {
    pub opc: u8,
    pub vector: bool,
    pub load: bool,
    pub mode: LoadStorePairAddressMode,
    pub imm7: u8,
    pub rt2: u8,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoadStorePairAddressMode {
    SignedOffset,
    PostIndex,
    PreIndex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoadStoreAcquireRelease {
    pub size: u8,
    pub load: bool,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoadStoreExclusiveAcquireRelease {
    pub size: u8,
    pub load: bool,
    pub rs: u8,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CompareAndSwap {
    pub size: u8,
    pub acquire: bool,
    pub release: bool,
    pub rs: u8,
    pub rn: u8,
    pub rt: u8,
}

/// LSE atomic read-modify-write operation — the `opc`/`o3` selector of the
/// `LD<op>` / `SWP` family. Each maps to a trust_ir `AtomicRMWOp` when a later
/// lifting phase recovers trust_ir (#378); the mapping mirrors the AArch64
/// isel's `select_atomic_rmw` emit choices.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LseAtomicRmwOp {
    /// `LDADD` (o3=0, opc=0b000) — trust_ir `AtomicRMWOp::Add`. Also the emit
    /// target of `Sub` (lowered as `NEG` + `LDADD`).
    Add,
    /// `LDCLR` (o3=0, opc=0b001) — bit-clear. trust_ir `AtomicRMWOp::And` is
    /// emitted as `MVN` + `LDCLR`.
    Clr,
    /// `LDEOR` (o3=0, opc=0b010) — trust_ir `AtomicRMWOp::Xor`.
    Eor,
    /// `LDSET` (o3=0, opc=0b011) — trust_ir `AtomicRMWOp::Or`.
    Set,
    /// `SWP` (o3=1, opc=0b000) — trust_ir `AtomicRMWOp::Xchg`.
    Swp,
    /// `LDSMAX` (o3=0, opc=0b100) — signed maximum. trust_ir `AtomicRMWOp::Max`.
    Smax,
    /// `LDSMIN` (o3=0, opc=0b101) — signed minimum. trust_ir `AtomicRMWOp::Min`.
    Smin,
    /// `LDUMAX` (o3=0, opc=0b110) — unsigned maximum. trust_ir `AtomicRMWOp::UMax`.
    Umax,
    /// `LDUMIN` (o3=0, opc=0b111) — unsigned minimum. trust_ir `AtomicRMWOp::UMin`.
    Umin,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LseAtomicRmw {
    pub size: u8,
    pub acquire: bool,
    pub release: bool,
    pub op: LseAtomicRmwOp,
    pub rs: u8,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CompareBranch {
    pub sf: u8,
    pub nonzero: bool,
    pub imm19: u32,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DataProcessing2Source {
    pub sf: u8,
    pub opcode: u8,
    pub rm: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DataProcessing3Source {
    pub sf: u8,
    pub op31: u8,
    pub o0: bool,
    pub rm: u8,
    pub ra: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConditionalSelect {
    pub sf: u8,
    pub op: bool,
    pub o2: bool,
    pub rm: u8,
    pub cond: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FpArith {
    pub ftype: u8,
    pub opcode: u8,
    pub rm: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FpCompare {
    pub ftype: u8,
    pub rm: u8,
    pub rn: u8,
    pub opc: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FpIntConversion {
    pub sf64: bool,
    pub ftype: u8,
    pub rmode: u8,
    pub opcode: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FpUnary {
    pub ftype: u8,
    pub opcode: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FpPrecisionConvert {
    pub src_ftype: u8,
    pub dst_ftype: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FpImmediate {
    pub ftype: u8,
    pub imm8: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Brk {
    pub imm16: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SystemBarrier {
    pub kind: SystemBarrierKind,
    pub crm: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SystemBarrierKind {
    Dsb,
    Dmb,
    Isb,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SystemRegisterRead {
    pub sysreg: u16,
    pub rt: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeonIntVec3Same {
    pub q: bool,
    pub u: bool,
    pub size: u8,
    pub opcode: u8,
    pub rm: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeonVecLogic {
    pub q: bool,
    pub u: bool,
    pub size: u8,
    pub rm: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeonFpVec3Same {
    pub q: bool,
    pub u: bool,
    pub bit23: bool,
    pub sz: u8,
    pub opcode: u8,
    pub rm: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeonVecNot {
    pub q: bool,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeonAcrossLanes {
    pub q: bool,
    pub u: bool,
    pub size: u8,
    pub opcode: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NeonElementSize {
    B,
    H,
    S,
    D,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeonDupElement {
    pub q: bool,
    pub element_size: NeonElementSize,
    pub lane: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeonDupGeneral {
    pub q: bool,
    pub element_size: NeonElementSize,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeonInsGeneral {
    pub element_size: NeonElementSize,
    pub lane: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeonMoviByte {
    pub q: bool,
    pub imm8: u8,
    pub rd: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeonLdStSinglePostImm {
    pub q: bool,
    pub load: bool,
    pub size: u8,
    pub rn: u8,
    pub rt: u8,
}

/// Decode one 32-bit AArch64 instruction word.
pub fn decode(word: u32) -> Result<Instruction, DecodeError> {
    if word == AARCH64_NOP {
        return Ok(Instruction::Nop);
    }

    if word == AARCH64_BRK_1 {
        return Ok(Instruction::Brk(Brk {
            imm16: bits(word, 5, 16) as u16,
        }));
    }

    if bits(word, 24, 5) == 0b10000 {
        return Ok(Instruction::PcRelAddress(PcRelAddress {
            page: bit(word, 31),
            imm21: sign_extend(bits(word, 29, 2) | (bits(word, 5, 19) << 2), 21),
            rd: bits(word, 0, 5) as u8,
        }));
    }

    if bits(word, 24, 5) == 0b01011 && !bit(word, 21) {
        return decode_add_sub_shifted_reg(word);
    }

    if bits(word, 24, 5) == 0b01010 {
        return decode_logical_shifted_reg(word);
    }

    if bits(word, 23, 6) == 0b100100 {
        return decode_logical_imm(word);
    }

    if bits(word, 23, 6) == 0b100010 {
        return Ok(Instruction::AddSubImm(AddSubImm {
            sf: bits(word, 31, 1) as u8,
            op: bits(word, 30, 1) as u8,
            set_flags: bit(word, 29),
            shift12: bit(word, 22),
            imm12: bits(word, 10, 12) as u16,
            rn: bits(word, 5, 5) as u8,
            rd: bits(word, 0, 5) as u8,
        }));
    }

    if bits(word, 21, 8) == 0b11010000 && bits(word, 10, 6) == 0 {
        return decode_add_sub_carry(word);
    }

    if bits(word, 23, 6) == 0b100101 {
        return decode_move_wide(word);
    }

    if bits(word, 23, 6) == 0b100110 {
        return decode_bitfield_move(word);
    }

    if bits(word, 24, 8) == 0b01010100 {
        return decode_cond_branch(word);
    }

    if bits(word, 26, 5) == 0b00101 {
        return Ok(Instruction::UncondBranch(UncondBranch {
            link: bit(word, 31),
            imm26: bits(word, 0, 26),
        }));
    }

    if bits(word, 25, 7) == 0b1101011
        && bits(word, 16, 5) == 0b11111
        && bits(word, 10, 6) == 0
        && bits(word, 0, 5) == 0
    {
        return decode_branch_reg(word);
    }

    if bits(word, 25, 6) == 0b011010 {
        return Ok(Instruction::CompareBranch(CompareBranch {
            sf: bits(word, 31, 1) as u8,
            nonzero: bit(word, 24),
            imm19: bits(word, 5, 19),
            rt: bits(word, 0, 5) as u8,
        }));
    }

    if bits(word, 25, 6) == 0b011011 {
        return Ok(Instruction::TestBranch(TestBranch {
            nonzero: bit(word, 24),
            bit: (((bit(word, 31) as u8) << 5) | bits(word, 19, 5) as u8),
            imm14: bits(word, 5, 14) as u16,
            rt: bits(word, 0, 5) as u8,
        }));
    }

    if bits(word, 24, 6) == 0b011000 {
        return decode_load_literal(word);
    }

    if bits(word, 21, 10) == 0b00_11010110 {
        return decode_data_processing_2_source(word);
    }

    if bits(word, 24, 5) == 0b11011 && bits(word, 29, 2) == 0 {
        return decode_data_processing_3_source(word);
    }

    if bits(word, 21, 8) == 0b11010100 {
        return decode_conditional_select(word);
    }

    if bits(word, 24, 5) == 0b11110 && bits(word, 29, 2) == 0 && bit(word, 21) {
        return decode_fp_scalar(word);
    }

    if bits(word, 22, 10) == 0b1101010100 {
        return decode_system(word);
    }

    if !bit(word, 31) && bits(word, 24, 5) == 0b01110 && bit(word, 21) {
        return decode_neon_three_same(word);
    }

    if !bit(word, 31) && bits(word, 19, 10) == 0b0111100000 {
        return decode_neon_modified_immediate(word);
    }

    if !bit(word, 31) && bits(word, 21, 9) == 0b001110000 && bits(word, 10, 6) == 0b000001 {
        return decode_neon_dup_element(word);
    }

    if !bit(word, 31)
        && bits(word, 21, 9) == 0b001110000
        && matches!(bits(word, 10, 6), 0b000011 | 0b000111)
    {
        return decode_neon_dup_general(word);
    }

    if !bit(word, 31) && bits(word, 23, 7) == 0b0011001 {
        return decode_neon_ldst_single_post_imm(word);
    }

    if bits(word, 24, 6) == 0b001000 {
        return decode_load_store_acquire_release(word);
    }

    if bits(word, 24, 6) == 0b111000 && bit(word, 21) && bits(word, 10, 2) == 0 {
        return decode_lse_atomic_rmw(word);
    }

    if bits(word, 27, 3) == 0b111 && bits(word, 24, 2) == 0b01 {
        let size = bits(word, 30, 2) as u8;
        let vector = bit(word, 26);
        let opc = bits(word, 22, 2) as u8;
        validate_scalar_load_store(word, size, vector, opc, ScalarLoadStoreForm::NoWriteback)?;
        return Ok(Instruction::LoadStoreUnsignedImm(LoadStoreUnsignedImm {
            size,
            vector,
            opc,
            imm12: bits(word, 10, 12) as u16,
            rn: bits(word, 5, 5) as u8,
            rt: bits(word, 0, 5) as u8,
        }));
    }

    if bits(word, 27, 3) == 0b111
        && bits(word, 24, 2) == 0
        && bit(word, 21)
        && bits(word, 10, 2) == 0b10
    {
        return decode_load_store_register(word);
    }

    if bits(word, 27, 3) == 0b111 && bits(word, 24, 2) == 0 && !bit(word, 21) {
        let size = bits(word, 30, 2) as u8;
        let vector = bit(word, 26);
        let opc = bits(word, 22, 2) as u8;
        match bits(word, 10, 2) {
            0b00 => {
                validate_scalar_load_store(
                    word,
                    size,
                    vector,
                    opc,
                    ScalarLoadStoreForm::NoWriteback,
                )?;
                return Ok(Instruction::LoadStoreUnscaled(LoadStoreUnscaled {
                    size,
                    vector,
                    opc,
                    imm9: sign_extend(bits(word, 12, 9), 9) as i16,
                    rn: bits(word, 5, 5) as u8,
                    rt: bits(word, 0, 5) as u8,
                }));
            }
            0b01 | 0b11 => {
                let mode = if bits(word, 10, 2) == 0b01 {
                    LoadStoreIndexMode::PostIndex
                } else {
                    LoadStoreIndexMode::PreIndex
                };
                // Two INDEPENDENT rejections apply here, on different axes:
                // allocation — is this `(size, V, opc)` triple an instruction at
                // all — and operand aliasing, which rejects an allocated
                // encoding whose register choice is CONSTRAINED UNPREDICTABLE.
                // Neither subsumes the other, so both run.
                validate_scalar_load_store(
                    word,
                    size,
                    vector,
                    opc,
                    ScalarLoadStoreForm::Writeback,
                )?;
                let rn = bits(word, 5, 5) as u8;
                let rt = bits(word, 0, 5) as u8;
                // WBOVERLAP applies to the scalar GPR transfer forms. SIMD/FP
                // Rt lives in a different register file from the GPR base.
                if !vector && rn != 31 && rt == rn {
                    return Err(DecodeError::ConstrainedUnpredictable {
                        word,
                        reason: "pre/post-indexed transfer register aliases its writeback base",
                    });
                }
                return Ok(Instruction::LoadStoreIndexed(LoadStoreIndexed {
                    size,
                    vector,
                    opc,
                    imm9: sign_extend(bits(word, 12, 9), 9) as i16,
                    mode,
                    rn,
                    rt,
                }));
            }
            _ => {}
        }
    }

    if bits(word, 27, 3) == 0b101 && !bit(word, 25) {
        let mode = match bits(word, 23, 3) {
            0b001 => LoadStorePairAddressMode::PostIndex,
            0b010 => LoadStorePairAddressMode::SignedOffset,
            0b011 => LoadStorePairAddressMode::PreIndex,
            _ => return Err(DecodeError::Unsupported { word }),
        };

        let opc = bits(word, 30, 2) as u8;
        let vector = bit(word, 26);
        let load = bit(word, 22);
        // Allocation first. `validate_load_store_pair` subsumes the narrower
        // STGP-only rejection this arm used to carry inline — it refuses the
        // same `opc=0b01, V=0, L=0` word as `Unallocated` rather than
        // `Unsupported`, and additionally refuses `opc=0b11` (STTP/LDTP), which
        // the inline check let through onto the STP/LDP the interpreter knows.
        validate_load_store_pair(word, opc, vector, load)?;

        // Then operand aliasing, which is a separate axis: these words ARE
        // allocated, and are rejected only because the register choice makes
        // them CONSTRAINED UNPREDICTABLE.
        let rt2 = bits(word, 10, 5) as u8;
        let rn = bits(word, 5, 5) as u8;
        let rt = bits(word, 0, 5) as u8;
        if load && rt == rt2 {
            return Err(DecodeError::ConstrainedUnpredictable {
                word,
                reason: "load-pair transfer registers name the same destination",
            });
        }
        // SIMD/FP transfer registers do not alias the GPR writeback base.
        if !vector
            && !matches!(mode, LoadStorePairAddressMode::SignedOffset)
            && rn != 31
            && (rt == rn || rt2 == rn)
        {
            return Err(DecodeError::ConstrainedUnpredictable {
                word,
                reason: "pre/post-indexed pair transfer register aliases its writeback base",
            });
        }

        return Ok(Instruction::LoadStorePair(LoadStorePair {
            opc,
            vector,
            load,
            mode,
            imm7: bits(word, 15, 7) as u8,
            rt2,
            rn,
            rt,
        }));
    }

    Err(DecodeError::Unsupported { word })
}

/// Reject the `(opc, V, L)` combinations in the load/store-pair space that are
/// NOT `STP`/`LDP`/`LDPSW`.
///
/// This was the single largest hole in this decoder: 70,628 words in the sweep
/// were named `stp`/`ldp` while objdump named a DIFFERENT ALLOCATED
/// INSTRUCTION. The `opc` field was read into the struct and never checked, so
/// three distinct instructions were laundered onto the pair the interpreter
/// knows:
///
/// * `opc=0b11` (any V, any L) is `STTP`/`LDTP` (FEAT_THE) — a checked,
///   unprivileged pair access, not `STP`/`LDP`.
/// * `opc=0b01, V=0, L=0` is `STGP` (FEAT_MTE) — it stores an allocation TAG
///   alongside the pair AND scales `imm7` by 16 rather than 4. The interpreter
///   maps `opc=0b01, V=0` to `LDPSW` (scale 4, sign-extending), so an `STGP`
///   word was executed at the WRONG ADDRESS with the WRONG ACCESS WIDTH. That is
///   the "allocated resolved onto a different allocated" class, live.
///
/// `opc=0b01, V=0, L=1` really is `LDPSW`, and every `V=1` row for
/// `opc=0b00/0b01/0b10` really is the SIMD pair — those stay accepted.
fn validate_load_store_pair(
    word: u32,
    opc: u8,
    vector: bool,
    load: bool,
) -> Result<(), DecodeError> {
    if opc == 0b11 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "load/store pair opc 0b11 is STTP/LDTP, not STP/LDP",
        });
    }

    if opc == 0b01 && !vector && !load {
        return Err(DecodeError::Unallocated {
            word,
            reason: "load/store pair opc 0b01 with V=0, L=0 is STGP, not STP",
        });
    }

    Ok(())
}

fn decode_lse_atomic_rmw(word: u32) -> Result<Instruction, DecodeError> {
    let size = bits(word, 30, 2) as u8;
    let acquire = bit(word, 23);
    let release = bit(word, 22);
    let bit21 = bit(word, 21);
    let o3 = bit(word, 15);
    let opc = bits(word, 12, 3) as u8;
    let zero = bits(word, 10, 2);

    if !bit21 || zero != 0 {
        return Err(DecodeError::Unsupported { word });
    }

    // A (bit 23) and R (bit 22) select the memory ordering INDEPENDENTLY for
    // every op: plain (A=0,R=0 = Relaxed), A (A=1,R=0 = Acquire), L (A=0,R=1 =
    // Release), AL (A=1,R=1 = AcqRel). All four are architecturally valid for
    // every LSE atomic-RMW op, so the disassembler decodes them all regardless
    // of which orderings our own isel happens to emit — a disassembler must
    // read every VALID ISA encoding, not only the emit-symmetric subset.
    // All four access sizes are likewise allocated for every op × ordering:
    // byte (size=00, ..B forms), half (size=01, ..H forms), word (10), and
    // dword (11) — the emit side produces the narrow ..ab/..ah/..alb/..alh
    // forms for i8/i16 atomics, mirroring the CASB/CASH decode. The
    // `acquire`/`release` bits are recorded verbatim below; only genuinely
    // reserved encodings (bit21/zero mismatch above, or an o3=1 opcode other
    // than SWP) stay fail-closed.
    let op = match (o3, opc) {
        (false, 0b000) => LseAtomicRmwOp::Add,
        (false, 0b001) => LseAtomicRmwOp::Clr,
        (false, 0b010) => LseAtomicRmwOp::Eor,
        (false, 0b011) => LseAtomicRmwOp::Set,
        (false, 0b100) => LseAtomicRmwOp::Smax,
        (false, 0b101) => LseAtomicRmwOp::Smin,
        (false, 0b110) => LseAtomicRmwOp::Umax,
        (false, 0b111) => LseAtomicRmwOp::Umin,
        // o3=1 is allocated only for SWP (opc=0b000); every other o3=1 opcode
        // is architecturally reserved.
        (true, 0b000) => LseAtomicRmwOp::Swp,
        _ => return Err(DecodeError::Unsupported { word }),
    };

    Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
        size,
        acquire,
        release,
        op,
        rs: bits(word, 16, 5) as u8,
        rn: bits(word, 5, 5) as u8,
        rt: bits(word, 0, 5) as u8,
    }))
}

/// A 6-bit shift amount is only legal up to the operand width: with `sf=0` the
/// operand is 32 bits, so `imm6<5>` (bit 15) MUST be zero. The ARM pseudocode is
/// literally `if sf == '0' && imm6<5> == '1' then UNDEFINED` — an amount of
/// 32..63 on a 32-bit register is not a wide shift, it is not an instruction at
/// all. Accepting it silently produced 40,779 + 15,333 words that this decoder
/// named while objdump answered `<unknown>`.
fn validate_shifted_reg_amount(word: u32, sf: u8, imm6: u8) -> Result<(), DecodeError> {
    if sf == 0 && imm6 >= 32 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "32-bit shifted register shift amount must be in 0..32",
        });
    }
    Ok(())
}

fn decode_logical_shifted_reg(word: u32) -> Result<Instruction, DecodeError> {
    let sf = bits(word, 31, 1) as u8;
    let imm6 = bits(word, 10, 6) as u8;
    validate_shifted_reg_amount(word, sf, imm6)?;

    Ok(Instruction::LogicalShiftedReg(LogicalShiftedReg {
        sf,
        opc: bits(word, 29, 2) as u8,
        shift: bits(word, 22, 2) as u8,
        n: bit(word, 21),
        rm: bits(word, 16, 5) as u8,
        imm6,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_add_sub_shifted_reg(word: u32) -> Result<Instruction, DecodeError> {
    let shift = bits(word, 22, 2) as u8;
    if shift == 0b11 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "add/sub shifted register uses reserved shift field 0b11",
        });
    }

    let sf = bits(word, 31, 1) as u8;
    let imm6 = bits(word, 10, 6) as u8;
    validate_shifted_reg_amount(word, sf, imm6)?;

    Ok(Instruction::AddSubShiftedReg(AddSubShiftedReg {
        sf,
        op: bits(word, 30, 1) as u8,
        set_flags: bit(word, 29),
        shift,
        rm: bits(word, 16, 5) as u8,
        imm6,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_logical_imm(word: u32) -> Result<Instruction, DecodeError> {
    let sf = bits(word, 31, 1) as u8;
    let opc = bits(word, 29, 2) as u8;
    let n = bit(word, 22);
    let immr = bits(word, 16, 6) as u8;
    let imms = bits(word, 10, 6) as u8;

    // opc == 0b11 is ANDS (immediate) — the `tst Wn, #imm` idiom when Rd==31.
    // It decodes exactly like the other three logical-immediate forms; the
    // only difference is that it writes NZCV, which `LogicalImm` carries in
    // `opc` for the consumer to act on (the a64 interpreter already
    // implements it: sets N/Z, clears C/V, and treats Rd==31 as a discard).
    // It was rejected here while the executor was ready and waiting, which
    // left the select/cmov corpus sweep red on every `tst`-bearing program.

    if sf == 0 && n {
        return Err(DecodeError::Unallocated {
            word,
            reason: "32-bit logical immediate cannot set N",
        });
    }

    if !logical_immediate_bitmask_is_allocated(n, imms) {
        return Err(DecodeError::Unallocated {
            word,
            reason: "logical immediate bitmask encoding is unallocated",
        });
    }

    Ok(Instruction::LogicalImm(LogicalImm {
        sf,
        opc,
        n,
        immr,
        imms,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn logical_immediate_bitmask_is_allocated(n: bool, imms: u8) -> bool {
    let pattern = ((n as u8) << 6) | (!imms & 0x3f);
    if pattern == 0 {
        return false;
    }

    let len = 7 - pattern.leading_zeros() as u8;
    if len < 1 {
        return false;
    }

    let levels = (1u8 << len) - 1;
    imms & levels != levels
}

fn decode_add_sub_carry(word: u32) -> Result<Instruction, DecodeError> {
    let set_flags = bit(word, 29);
    if set_flags {
        return Err(DecodeError::Unsupported { word });
    }

    Ok(Instruction::AddSubCarry(AddSubCarry {
        sf: bits(word, 31, 1) as u8,
        op: bits(word, 30, 1) as u8,
        set_flags,
        rm: bits(word, 16, 5) as u8,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_move_wide(word: u32) -> Result<Instruction, DecodeError> {
    let opc = bits(word, 29, 2) as u8;
    if opc == 0b01 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "move-wide opc field 0b01 is unallocated",
        });
    }

    let sf = bits(word, 31, 1) as u8;
    let hw = bits(word, 21, 2) as u8;
    // `hw` selects a 16-bit lane of the destination: shift = hw * 16. With
    // `sf=0` the destination is 32 bits, so only lanes 0 and 1 exist and the ARM
    // pseudocode is `if sf == '0' && hw<1> == '1' then UNDEFINED`. This is not a
    // harmless out-of-range shift: an interpreter that computes `imm16 << 32`
    // and then truncates to 32 bits renders `MOVZ Wd, #imm, LSL #32` as
    // `MOVZ Wd, #0` — a silent wrong answer for a word that is not an
    // instruction. 14,277 such words were named by this decoder.
    if sf == 0 && hw >= 0b10 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "32-bit move-wide hw field selects a nonexistent halfword lane",
        });
    }

    Ok(Instruction::MoveWide(MoveWide {
        sf,
        opc,
        hw,
        imm16: bits(word, 5, 16) as u16,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_bitfield_move(word: u32) -> Result<Instruction, DecodeError> {
    let sf = bits(word, 31, 1) as u8;
    let opc = bits(word, 29, 2) as u8;
    if opc == 0b11 {
        return Err(DecodeError::Unsupported { word });
    }

    let n = bits(word, 22, 1) as u8;
    if n != sf {
        return Err(DecodeError::Unallocated {
            word,
            reason: "bitfield move N bit must match sf",
        });
    }

    let immr = bits(word, 16, 6) as u8;
    let imms = bits(word, 10, 6) as u8;
    if sf == 0 && (immr >= 32 || imms >= 32) {
        return Err(DecodeError::Unallocated {
            word,
            reason: "32-bit bitfield move immediates must be in 0..32",
        });
    }

    Ok(Instruction::BitfieldMove(BitfieldMove {
        sf,
        opc,
        immr,
        imms,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_cond_branch(word: u32) -> Result<Instruction, DecodeError> {
    if bit(word, 4) {
        return Err(DecodeError::Unallocated {
            word,
            reason: "conditional branch bit 4 must be zero",
        });
    }

    Ok(Instruction::CondBranch(CondBranch {
        imm19: bits(word, 5, 19),
        cond: bits(word, 0, 4) as u8,
    }))
}

fn decode_branch_reg(word: u32) -> Result<Instruction, DecodeError> {
    let opc = bits(word, 21, 4) as u8;
    if opc > 0b0010 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "branch-register opc only covers BR, BLR, and RET",
        });
    }

    Ok(Instruction::BranchReg(BranchReg {
        opc,
        rn: bits(word, 5, 5) as u8,
    }))
}

/// Addressing form of a scalar load/store. It changes which `(size, V, opc)`
/// triples the architecture allocates, so it is a decode input, not a label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScalarLoadStoreForm {
    /// Unsigned-offset, unscaled (`LDUR`-family) and register-offset forms.
    /// `size=0b11, V=0, opc=0b10` is `PRFM`/`PRFUM` here and IS allocated.
    NoWriteback,
    /// Pre-index and post-index forms. `PRFM` has no base-writeback form, so
    /// `size=0b11, V=0, opc=0b10` is UNALLOCATED here.
    Writeback,
}

/// Reject the `(size, V, opc)` triples the architecture does not allocate for a
/// scalar load/store.
///
/// The `opc` field is not free: together with `size` and `V` it names the access
/// width and direction, and half the 16-entry `(size, V, opc)` space is
/// unallocated. Decoding those anyway is what produced 37,692 + 10,826 + 4,882 +
/// 2,651 words that this decoder named while objdump answered `<unknown>`.
///
/// The table below was measured, not recalled: every `(size, V, opc)` triple was
/// assembled verbatim for all five addressing forms and read back with objdump.
fn validate_scalar_load_store(
    word: u32,
    size: u8,
    vector: bool,
    opc: u8,
    form: ScalarLoadStoreForm,
) -> Result<(), DecodeError> {
    if vector {
        // V=1: opc<1> selects the 128-bit (Q) access, which exists only in the
        // size=0b00 row. size=0b01/0b10/0b11 with opc>=0b10 is unallocated.
        if opc >= 0b10 && size != 0b00 {
            return Err(DecodeError::Unallocated {
                word,
                reason: "SIMD load/store (size, opc) pair is unallocated",
            });
        }
        return Ok(());
    }

    // V=0, opc=0b11 is the "sign-extend into a 32-bit register" load, which only
    // exists for the narrow sizes (LDRSB/LDRSH). size=0b10/0b11 has nothing
    // wider to sign-extend into.
    if opc == 0b11 && size >= 0b10 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "integer load/store (size, opc) pair is unallocated",
        });
    }

    // V=0, size=0b11, opc=0b10 is PRFM/PRFUM. Prefetch has no base-writeback
    // form, so it is unallocated in the pre/post-index encodings.
    if opc == 0b10 && size == 0b11 && form == ScalarLoadStoreForm::Writeback {
        return Err(DecodeError::Unallocated {
            word,
            reason: "PRFM has no pre/post-index (base writeback) form",
        });
    }

    Ok(())
}

fn decode_load_store_register(word: u32) -> Result<Instruction, DecodeError> {
    let option = bits(word, 13, 3) as u8;
    if option & 0b010 == 0 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "load/store register-offset option field is unallocated",
        });
    }

    let size = bits(word, 30, 2) as u8;
    let vector = bit(word, 26);
    let opc = bits(word, 22, 2) as u8;
    validate_scalar_load_store(word, size, vector, opc, ScalarLoadStoreForm::NoWriteback)?;

    let rt = bits(word, 0, 5) as u8;
    // In the register-offset PRFM space (size=0b11, V=0, opc=0b10) the `Rt`
    // field is not a register, it is the prefetch operation `<prfop>` =
    // type:target:policy. `type = 0b11` is not a prefetch type: that quarter of
    // the space is allocated to RPRFM (FEAT_RPRFM), a RANGE prefetch with a
    // different operand meaning entirely. Decoding it as PRFM renames one
    // allocated instruction onto another — 89 words in the sweep.
    if size == 0b11 && !vector && opc == 0b10 && (rt >> 3) == 0b11 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "register-offset prefetch with prfop type 0b11 is RPRFM, not PRFM",
        });
    }

    Ok(Instruction::LoadStoreRegister(LoadStoreRegister {
        size,
        vector,
        opc,
        rm: bits(word, 16, 5) as u8,
        option,
        shift: bit(word, 12),
        rn: bits(word, 5, 5) as u8,
        rt,
    }))
}

fn decode_load_literal(word: u32) -> Result<Instruction, DecodeError> {
    let opc = bits(word, 30, 2) as u8;
    let vector = bit(word, 26);
    if opc != 0b01 || vector {
        return Err(DecodeError::Unsupported { word });
    }

    Ok(Instruction::LoadLiteral(LoadLiteral {
        opc,
        vector,
        imm19: bits(word, 5, 19),
        rt: bits(word, 0, 5) as u8,
    }))
}

fn decode_load_store_acquire_release(word: u32) -> Result<Instruction, DecodeError> {
    let size = bits(word, 30, 2) as u8;
    let o2 = bit(word, 23);
    let bit22 = bit(word, 22);
    let o1 = bit(word, 21);
    let rs = bits(word, 16, 5) as u8;
    let o0 = bit(word, 15);
    let rt2 = bits(word, 10, 5) as u8;

    if o2 && !o1 && rs == 0b11111 && o0 && rt2 == 0b11111 {
        return Ok(Instruction::LoadStoreAcquireRelease(
            LoadStoreAcquireRelease {
                size,
                load: bit22,
                rn: bits(word, 5, 5) as u8,
                rt: bits(word, 0, 5) as u8,
            },
        ));
    }

    if o2 && o1 && rt2 == 0b11111 {
        // Compare-and-swap: CAS/CASA/CASAL/CASL (and their B/H forms via
        // size 00/01 — CASP lives in the o2=0 space, so no collision). A
        // (bit 22) and R (o0, bit 15) select the ordering INDEPENDENTLY:
        // plain (A=0,R=0), acquire (A=1,R=0), release-only (A=0,R=1 — the
        // CASL form the isel emits for a release-only compare-exchange),
        // and acquire+release (A=1,R=1). All four are architecturally valid
        // for every access size, so decode them all — decode/emit stays
        // symmetric with `encode_cas` (A bit 22, R bit 15, size 00..11).
        let acquire = bit22;
        let release = o0;
        return Ok(Instruction::CompareAndSwap(CompareAndSwap {
            size,
            acquire,
            release,
            rs,
            rn: bits(word, 5, 5) as u8,
            rt: bits(word, 0, 5) as u8,
        }));
    }

    if !o2 && !o1 && o0 && rt2 == 0b11111 && matches!(size, 0b10 | 0b11) {
        let is_ldaxr = bit22 && rs == 0b11111;
        let is_stlxr = !bit22;
        if is_ldaxr || is_stlxr {
            let rn = bits(word, 5, 5) as u8;
            let rt = bits(word, 0, 5) as u8;
            if is_stlxr && (rs == rt || (rs == rn && rn != 31)) {
                return Err(DecodeError::ConstrainedUnpredictable {
                    word,
                    reason: "store-exclusive status register aliases its data or address register",
                });
            }
            return Ok(Instruction::LoadStoreExclusiveAcquireRelease(
                LoadStoreExclusiveAcquireRelease {
                    size,
                    load: bit22,
                    rs,
                    rn,
                    rt,
                },
            ));
        }
    }

    Err(DecodeError::Unsupported { word })
}

fn decode_data_processing_2_source(word: u32) -> Result<Instruction, DecodeError> {
    let opcode = bits(word, 10, 6) as u8;
    match opcode {
        0b000010 | 0b000011 | 0b001000 | 0b001001 | 0b001010 => {
            Ok(Instruction::DataProcessing2Source(DataProcessing2Source {
                sf: bits(word, 31, 1) as u8,
                opcode,
                rm: bits(word, 16, 5) as u8,
                rn: bits(word, 5, 5) as u8,
                rd: bits(word, 0, 5) as u8,
            }))
        }
        _ => Err(DecodeError::Unsupported { word }),
    }
}

fn decode_data_processing_3_source(word: u32) -> Result<Instruction, DecodeError> {
    let sf = bits(word, 31, 1) as u8;
    let op31 = bits(word, 21, 3) as u8;
    let o0 = bit(word, 15);
    let ra = bits(word, 10, 5) as u8;

    match op31 {
        0b000 => {}
        0b001 | 0b101 => {
            if sf != 1 {
                return Err(DecodeError::Unallocated {
                    word,
                    reason: "data-processing 3-source long multiply requires sf=1",
                });
            }
            if o0 || ra != 31 {
                return Err(DecodeError::Unsupported { word });
            }
        }
        0b010 | 0b110 => {
            if sf != 1 {
                return Err(DecodeError::Unallocated {
                    word,
                    reason: "data-processing 3-source high multiply requires sf=1",
                });
            }
            if o0 || ra != 31 {
                return Err(DecodeError::Unallocated {
                    word,
                    reason: "data-processing 3-source high multiply requires o0=0 and ra=31",
                });
            }
        }
        _ => return Err(DecodeError::Unsupported { word }),
    }

    Ok(Instruction::DataProcessing3Source(DataProcessing3Source {
        sf,
        op31,
        o0,
        rm: bits(word, 16, 5) as u8,
        ra,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_conditional_select(word: u32) -> Result<Instruction, DecodeError> {
    if bit(word, 29) {
        return Err(DecodeError::Unallocated {
            word,
            reason: "conditional select S bit must be zero",
        });
    }

    if bit(word, 11) {
        return Err(DecodeError::Unallocated {
            word,
            reason: "conditional select bit 11 must be zero",
        });
    }

    Ok(Instruction::ConditionalSelect(ConditionalSelect {
        sf: bits(word, 31, 1) as u8,
        op: bit(word, 30),
        o2: bit(word, 10),
        rm: bits(word, 16, 5) as u8,
        cond: bits(word, 12, 4) as u8,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_fp_scalar(word: u32) -> Result<Instruction, DecodeError> {
    let ftype = bits(word, 22, 2) as u8;
    validate_fp_ftype(word, ftype)?;

    if bits(word, 10, 3) == 0b100 {
        return decode_fp_immediate(word, ftype);
    }

    if bits(word, 10, 6) == 0 {
        return decode_fp_int_conversion(word, ftype);
    }

    if bit(word, 31) {
        return Err(DecodeError::Unsupported { word });
    }

    if bits(word, 10, 2) == 0b10 {
        return decode_fp_arith(word, ftype);
    }

    if bits(word, 10, 6) == 0b001000 {
        return decode_fp_compare(word, ftype);
    }

    if bits(word, 10, 5) == 0b10000 {
        return match bits(word, 17, 4) {
            0b0000 => Ok(Instruction::FpUnary(FpUnary {
                ftype,
                opcode: bits(word, 15, 2) as u8,
                rn: bits(word, 5, 5) as u8,
                rd: bits(word, 0, 5) as u8,
            })),
            0b0001 => {
                let dst_ftype = bits(word, 15, 2) as u8;
                validate_fp_ftype(word, dst_ftype)?;
                // FCVT converts BETWEEN precisions; the same-type encodings are
                // unallocated, not an identity move. 27 such words were decoded
                // as a precision conversion that does nothing.
                if dst_ftype == ftype {
                    return Err(DecodeError::Unallocated {
                        word,
                        reason: "FCVT source and destination precision must differ",
                    });
                }
                Ok(Instruction::FpPrecisionConvert(FpPrecisionConvert {
                    src_ftype: ftype,
                    dst_ftype,
                    rn: bits(word, 5, 5) as u8,
                    rd: bits(word, 0, 5) as u8,
                }))
            }
            _ => Err(DecodeError::Unsupported { word }),
        };
    }

    Err(DecodeError::Unsupported { word })
}

fn decode_fp_arith(word: u32, ftype: u8) -> Result<Instruction, DecodeError> {
    let opcode = bits(word, 12, 4) as u8;
    if opcode > 0b0011 {
        return Err(DecodeError::Unsupported { word });
    }

    Ok(Instruction::FpArith(FpArith {
        ftype,
        opcode,
        rm: bits(word, 16, 5) as u8,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_fp_compare(word: u32, ftype: u8) -> Result<Instruction, DecodeError> {
    let opc = bits(word, 0, 5) as u8;
    match opc {
        0b00000 | 0b10000 => {}
        0b01000 | 0b11000 => {
            if bits(word, 16, 5) != 0 {
                return Err(DecodeError::Unallocated {
                    word,
                    reason: "FP compare zero form requires rm == 0",
                });
            }
        }
        _ => return Err(DecodeError::Unsupported { word }),
    }

    Ok(Instruction::FpCompare(FpCompare {
        ftype,
        rm: bits(word, 16, 5) as u8,
        rn: bits(word, 5, 5) as u8,
        opc,
    }))
}

fn decode_fp_int_conversion(word: u32, ftype: u8) -> Result<Instruction, DecodeError> {
    let rmode = bits(word, 19, 2) as u8;
    let opcode = bits(word, 16, 3) as u8;
    let sf64 = bit(word, 31);

    // `rmode=0b00, opcode=0b11x` is FMOV between a general register and an FP
    // register. FMOV is a BIT COPY, so the two registers must be the same width:
    // 32-bit <-> S (ftype=0b00), 64-bit <-> D (ftype=0b01). (Half-precision,
    // ftype=0b11, is allocated for both widths.) The mismatched pairs are not
    // "FMOV with a conversion", they are unallocated — 52 such words.
    if rmode == 0b00 && opcode >= 0b110 {
        let width_matches = match ftype {
            0b00 => !sf64,
            0b01 => sf64,
            0b11 => true,
            _ => false,
        };
        if !width_matches {
            return Err(DecodeError::Unallocated {
                word,
                reason: "FMOV general/FP register widths must match",
            });
        }
    }

    match (rmode, opcode) {
        (0b11, 0b000)
        | (0b11, 0b001)
        | (0b00, 0b010)
        | (0b00, 0b011)
        | (0b00, 0b110)
        | (0b00, 0b111) => Ok(Instruction::FpIntConversion(FpIntConversion {
            sf64,
            ftype,
            rmode,
            opcode,
            rn: bits(word, 5, 5) as u8,
            rd: bits(word, 0, 5) as u8,
        })),
        _ => Err(DecodeError::Unsupported { word }),
    }
}

fn decode_fp_immediate(word: u32, ftype: u8) -> Result<Instruction, DecodeError> {
    if bit(word, 31) {
        return Err(DecodeError::Unallocated {
            word,
            reason: "FP immediate bit 31 must be zero",
        });
    }

    if bits(word, 5, 5) != 0 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "FP immediate bits 9:5 must be zero",
        });
    }

    Ok(Instruction::FpImmediate(FpImmediate {
        ftype,
        imm8: bits(word, 13, 8) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_system(word: u32) -> Result<Instruction, DecodeError> {
    // Bit 21 is `L` (read vs write), NOT "this is a system-register access".
    // The instruction class is chosen by `op0` = bits[20:19]:
    //
    //   op0=0b00  hints / barriers / PSTATE / TSTART-TTEST  (L=0 for barriers)
    //   op0=0b01  SYS (L=0) / SYSL (L=1)
    //   op0=0b1x  MSR (L=0) / MRS (L=1)
    //
    // Treating every L=1 word as MRS renamed 611 `SYSL` words — a system
    // INSTRUCTION result read, not a system REGISTER read — plus a `TSTART`,
    // onto MRS. MRS requires op0=0b1x; anything narrower is refused.
    let l = bit(word, 21);
    let op0 = bits(word, 19, 2) as u8;

    if l {
        if op0 < 0b10 {
            return Err(DecodeError::Unallocated {
                word,
                reason: "system read with op0 < 0b10 is SYSL/TSTART, not MRS",
            });
        }
        return Ok(Instruction::SystemRegisterRead(SystemRegisterRead {
            sysreg: bits(word, 5, 16) as u16,
            rt: bits(word, 0, 5) as u8,
        }));
    }

    if op0 == 0
        && bits(word, 16, 3) == 0b011
        && bits(word, 12, 4) == 0b0011
        && bits(word, 0, 5) == 0b11111
    {
        let kind = match bits(word, 5, 3) {
            0b100 => SystemBarrierKind::Dsb,
            0b101 => SystemBarrierKind::Dmb,
            0b110 => SystemBarrierKind::Isb,
            _ => return Err(DecodeError::Unsupported { word }),
        };

        return Ok(Instruction::SystemBarrier(SystemBarrier {
            kind,
            crm: bits(word, 8, 4) as u8,
        }));
    }

    Err(DecodeError::Unsupported { word })
}

fn decode_neon_three_same(word: u32) -> Result<Instruction, DecodeError> {
    let q = bit(word, 30);
    let u = bit(word, 29);
    let size = bits(word, 22, 2) as u8;
    let opcode = bits(word, 11, 5) as u8;

    if u && size == 0
        && bits(word, 17, 5) == 0b10000
        && bits(word, 12, 5) == 0b00101
        && bits(word, 10, 2) == 0b10
    {
        return Ok(Instruction::NeonVecNot(NeonVecNot {
            q,
            rn: bits(word, 5, 5) as u8,
            rd: bits(word, 0, 5) as u8,
        }));
    }

    if q && u
        && size == 0b10
        && bits(word, 17, 5) == 0b11000
        && bits(word, 12, 5) == 0b01010
        && bits(word, 10, 2) == 0b10
    {
        return Ok(Instruction::NeonAcrossLanes(NeonAcrossLanes {
            q,
            u,
            size,
            opcode: bits(word, 12, 5) as u8,
            rn: bits(word, 5, 5) as u8,
            rd: bits(word, 0, 5) as u8,
        }));
    }

    // Bit 10 is the "three same" class bit and it is NOT part of `opcode`. With
    // bit10=0 the same [15:11] pattern is a DIFFERENT class — "Advanced SIMD
    // three DIFFERENT" (SMLAL/SMLAL2/UMLAL/UMLAL2/SSUBW/...) or two-register
    // misc (REV16) — operating on widened lanes with different operand
    // meanings. Reading `opcode` as bits[15:11] and never checking bit 10 named
    // 768 + 7 words after an unrelated allocated instruction (`smlal` → `add`,
    // `umlal` → `sub`, `ssubw` → `cmgt`, `rev16` → `and`) and produced a further
    // 802 + 325 words objdump calls undefined.
    //
    // The two-register-misc forms handled above (`NeonVecNot`, `NeonAcrossLanes`)
    // legitimately carry bits[11:10]=0b10 and have already returned.
    let three_same = bit(word, 10);

    match (u, opcode) {
        (false, 0b10000)
        | (true, 0b10000)
        | (false, 0b10011)
        | (true, 0b10001)
        | (false, 0b00110)
        | (false, 0b00111)
            if three_same =>
        {
            validate_neon_vector_arrangement(word, q, size)?;
            // MUL has no 64-bit-lane form: unlike ADD/SUB/CMxx there is no
            // `mul.2d`, so size=0b11 is unallocated even at q=1.
            if opcode == 0b10011 && size == 0b11 {
                return Err(DecodeError::Unallocated {
                    word,
                    reason: "NEON MUL has no 64-bit element arrangement",
                });
            }
            return Ok(Instruction::NeonIntVec3Same(NeonIntVec3Same {
                q,
                u,
                size,
                opcode,
                rm: bits(word, 16, 5) as u8,
                rn: bits(word, 5, 5) as u8,
                rd: bits(word, 0, 5) as u8,
            }));
        }
        _ => {}
    }

    if opcode == 0b00011 && three_same {
        match (u, size) {
            (false, 0b00) | (false, 0b01) | (false, 0b10) | (true, 0b00) => {
                return Ok(Instruction::NeonVecLogic(NeonVecLogic {
                    q,
                    u,
                    size,
                    rm: bits(word, 16, 5) as u8,
                    rn: bits(word, 5, 5) as u8,
                    rd: bits(word, 0, 5) as u8,
                }));
            }
            _ => return Err(DecodeError::Unsupported { word }),
        }
    }

    let bit23 = bit(word, 23);
    let sz = bits(word, 22, 1) as u8;
    let fp_opcode = bits(word, 10, 6) as u8;
    match (u, bit23, fp_opcode) {
        (false, false, 0b110101)
        | (false, true, 0b110101)
        | (true, false, 0b110111)
        | (true, false, 0b111111) => {
            validate_neon_fp_arrangement(word, q, sz)?;
            Ok(Instruction::NeonFpVec3Same(NeonFpVec3Same {
                q,
                u,
                bit23,
                sz,
                opcode: fp_opcode,
                rm: bits(word, 16, 5) as u8,
                rn: bits(word, 5, 5) as u8,
                rd: bits(word, 0, 5) as u8,
            }))
        }
        _ => Err(DecodeError::Unsupported { word }),
    }
}

fn decode_neon_modified_immediate(word: u32) -> Result<Instruction, DecodeError> {
    if !bit(word, 29) && bits(word, 12, 4) == 0b1110 && bits(word, 10, 2) == 0b01 {
        let imm8 = ((bits(word, 16, 3) << 5) | bits(word, 5, 5)) as u8;
        return Ok(Instruction::NeonMoviByte(NeonMoviByte {
            q: bit(word, 30),
            imm8,
            rd: bits(word, 0, 5) as u8,
        }));
    }

    Err(DecodeError::Unsupported { word })
}

fn decode_neon_dup_element(word: u32) -> Result<Instruction, DecodeError> {
    let q = bit(word, 30);
    let imm5 = bits(word, 16, 5) as u8;
    let (element_size, lane) = decode_neon_element_imm5(word, imm5)?;

    if !q && element_size == NeonElementSize::D {
        return Err(DecodeError::Unallocated {
            word,
            reason: "NEON DUP element D arrangement requires q=1",
        });
    }

    Ok(Instruction::NeonDupElement(NeonDupElement {
        q,
        element_size,
        lane,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_neon_dup_general(word: u32) -> Result<Instruction, DecodeError> {
    let q = bit(word, 30);
    let imm5 = bits(word, 16, 5) as u8;
    let opcode = bits(word, 11, 4);
    let (element_size, lane) = decode_neon_element_imm5(word, imm5)?;

    if opcode == 0b0011 {
        if !q {
            return Err(DecodeError::Unallocated {
                word,
                reason: "NEON INS general requires q=1",
            });
        }

        return Ok(Instruction::NeonInsGeneral(NeonInsGeneral {
            element_size,
            lane,
            rn: bits(word, 5, 5) as u8,
            rd: bits(word, 0, 5) as u8,
        }));
    }

    if opcode != 0b0001 {
        return Err(DecodeError::Unsupported { word });
    }

    if !q && element_size == NeonElementSize::D {
        return Err(DecodeError::Unallocated {
            word,
            reason: "NEON DUP general D arrangement requires q=1",
        });
    }

    Ok(Instruction::NeonDupGeneral(NeonDupGeneral {
        q,
        element_size,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_neon_ldst_single_post_imm(word: u32) -> Result<Instruction, DecodeError> {
    if bit(word, 21) || bits(word, 16, 5) != 0b11111 || bits(word, 12, 4) != 0b0111 {
        return Err(DecodeError::Unsupported { word });
    }

    let q = bit(word, 30);
    let size = bits(word, 10, 2) as u8;
    validate_neon_vector_arrangement(word, q, size)?;

    Ok(Instruction::NeonLdStSinglePostImm(NeonLdStSinglePostImm {
        q,
        load: bit(word, 22),
        size,
        rn: bits(word, 5, 5) as u8,
        rt: bits(word, 0, 5) as u8,
    }))
}

fn validate_fp_ftype(word: u32, ftype: u8) -> Result<(), DecodeError> {
    if ftype == 0b10 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "scalar FP ftype field 0b10 is unallocated",
        });
    }
    Ok(())
}

fn validate_neon_vector_arrangement(word: u32, q: bool, size: u8) -> Result<(), DecodeError> {
    if !q && size == 0b11 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "NEON vector q=0 size=0b11 arrangement is unallocated",
        });
    }
    Ok(())
}

fn validate_neon_fp_arrangement(word: u32, q: bool, sz: u8) -> Result<(), DecodeError> {
    if !q && sz == 1 {
        return Err(DecodeError::Unallocated {
            word,
            reason: "NEON FP vector q=0 sz=1 arrangement is unallocated",
        });
    }
    Ok(())
}

fn decode_neon_element_imm5(word: u32, imm5: u8) -> Result<(NeonElementSize, u8), DecodeError> {
    match imm5.trailing_zeros() {
        0 => Ok((NeonElementSize::B, imm5 >> 1)),
        1 => Ok((NeonElementSize::H, imm5 >> 2)),
        2 => Ok((NeonElementSize::S, imm5 >> 3)),
        3 => Ok((NeonElementSize::D, imm5 >> 4)),
        4 => Err(DecodeError::Unallocated {
            word,
            reason: "NEON copy imm5 field encodes unsupported 128-bit element",
        }),
        _ => Err(DecodeError::Unallocated {
            word,
            reason: "NEON copy imm5 field must not be zero",
        }),
    }
}

#[inline]
fn bit(word: u32, offset: u8) -> bool {
    ((word >> offset) & 1) != 0
}

#[inline]
fn bits(word: u32, offset: u8, width: u8) -> u32 {
    (word >> offset) & ((1u32 << width) - 1)
}

#[inline]
fn sign_extend(value: u32, width: u8) -> i32 {
    let shift = 32 - width;
    ((value << shift) as i32) >> shift
}
