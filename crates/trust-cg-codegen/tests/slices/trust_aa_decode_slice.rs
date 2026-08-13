// Trust-toolchain slice — the trust-cg AArch64 INSTRUCTION DECODER
// (trust-cg/crates/trust-cg-lift/src/disasm/aarch64.rs), transcribed VERBATIM.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 27, TRUST BATCH 14).
//
// `decode(word) -> Result<Instruction, DecodeError>` is the Phase-1 binary-lifting
// DECODER: it classifies a 32-bit AArch64 instruction word into its family and
// extracts the operand fields. It is the INVERSE of the R2-verified pure encoders
// in `aarch64/encoding.rs` — the decoded forms "mirror the low-level forward
// encoder fields so tests can assert `decode(encode(fields)) == fields`" (module
// doc). A wrong dispatch guard mis-classifies a word; a wrong field extraction
// reads the wrong operand — either is a lifting miscompile.
//
// MODELED BOUNDARIES (documented honestly):
//   1. ERROR-DIAGNOSTIC PAYLOAD: production returns
//      `Err(DecodeError::Unsupported { word })` and
//      `Err(DecodeError::Unallocated { word, reason: &'static str })` — the `word`
//      merely echoes the input and `reason` is a &'static str diagnostic. The slice
//      models `DecodeError` as the 3-variant FIELDLESS enum `DecErr {Unsupported,
//      Unallocated, ConstrainedUnpredictable}` (drops the echoed `word` + the
//      diagnostic `reason`). The
//      VERIFIED semantics is the family classification, the Unsupported/Unallocated
//      REJECT distinction, and the exact extracted operand fields; the diagnostic
//      string content is NOT verified. (Same discipline as the R1/R2 encoder slices
//      that modeled EncodeError as `Err(())`.)
//   2. The `#[unsafe(no_mangle)]` emit root `decode_root` is a test-harness ABI adapter
//      (NOT production code): it runs the verbatim `decode` and packs the resulting
//      `Instruction`/`DecErr` into a scalar POD (`tag` = the Instruction variant's
//      declaration index, or 0xE0 Unsupported / 0xE1 Unallocated; `a..h` = the
//      variant's fields in declaration order, bool→u32, sub-enum→discriminant,
//      i16/i32→two's-complement bits). The map is injective on outcomes, so
//      native==JIT through the adapter verifies the verbatim callee.
//   3. F3 shift-typing: the two `u32`-LHS literal left-shifts in the decoder body
//      are written `<< Nu32` (line ~562 `bits(..) << 2u32` in PcRelAddress; line
//      ~1364 `bits(..) << 5u32` in NeonMoviByte) so the emit-closure frontend types
//      the RHS to the u32 LHS — a `u32 << i32-literal` is otherwise a validate_module
//      BinOpTypeMismatch (the R21 [F3] gap: the frontend normalizes a const shift
//      amount to the LHS type for 64-bit shifts but not 32-bit). The shift AMOUNT's
//      type never affects the result value, so `x << 2` == `x << 2u32`. Confirmed
//      MINIMAL: the u8-LHS literal shifts (`(x as u8) << 5`, `(n as u8) << 6`,
//      `imm5 >> N`) and the variable u8 shifts in `bits`/`sign_extend` lower
//      byte-for-byte with NO typing.
//   4. F1 enum-const compare: `element_size == NeonElementSize::D` (a fieldless-enum
//      variant constant in `==`) is written `matches!(element_size, NeonElementSize::D)`
//      (the documented R20/R21 workaround — `==` on such a constant hits "constant
//      value not a single scalar"). Two sites (decode_neon_dup_element/_general);
//      semantically identical (both test the discriminant).
//   5b. `?`-operator leaf: the `?` on `Result<_, DecErr>` (7 sites — the fp/neon
//      validators + decode_neon_element_imm5) desugars to `Try::branch` /
//      `FromResidual::from_residual` trait calls that lower to UNRESOLVED extern
//      leaves at JIT link. Each `?` is rewritten to the explicit `match`/`if let`
//      it desugars to (`X?;` -> `if let Err(e) = X { return Err(e); }`;
//      `let v = X?;` -> `let v = match X { Ok(v)=>v, Err(e)=>return Err(e) };`) —
//      semantically identical. The bulk native==JIT sweep + the reject-direction
//      spot-checks exercise these rewritten error paths.
//   5. F4 (R21) intrinsic leaves: `pattern.leading_zeros()` (in the logical-imm
//      gate) and `imm5.trailing_zeros()` (in decode_neon_element_imm5) lower to
//      UNRESOLVED extern leaves at JIT link (`Jit(UnresolvedSymbol ...leading_zeros/
//      trailing_zeros)`) — the emit validates but the JIT cannot link the leaf. Both
//      are replaced by equivalent explicit bit-scans producing IDENTICAL values on
//      the relevant domain (documented at each site). The gate rewrite is
//      exhaustively cross-checked against an INDEPENDENT `DecodeBitMasks` spec oracle;
//      the neon-element rewrite is checked by NEON DUP ground-truth spot decodes.
//
// Everything else is byte-for-byte from disasm/aarch64.rs (compare against
// ~/trust-cg/crates/trust-cg-lift/src/disasm/aarch64.rs).
//
// ── STALE AS OF 2026-08-10: this transcribes the decoder BEFORE the allocation
//    fixes ──────────────────────────────────────────────────────────────────
//
// On 2026-08-10 `disasm/aarch64.rs` gained ~10 allocation-validation refusals
// (load/store-pair `opc` — STGP/STTP/LDTP were being decoded as STP/LDP; the
// scalar load/store `(size, V, opc)` table; `sf`-dependent shift amounts and
// move-wide `hw`; the NEON three-same bit-10 class bit; MRS `op0`; RPRFM; FMOV
// width pairing; same-type FCVT). The differential against Apple/LLVM 21 objdump
// went from GHOST 127,678 / MISMATCH 72,236 to 0 / 0 over 5,078,879 words.
//
// THIS SLICE DOES NOT MIRROR THOSE FIXES. It is therefore no longer "verbatim":
// it is a verbatim transcription of the PRE-FIX decoder, kept as-is because
// round 27's claim is unaffected by the drift.
//
// What round 27 does and does not establish, stated exactly:
//   * IT DOES establish native==JIT equivalence for THIS code — i.e. that the
//     Trust toolchain compiles this decoder body to something that agrees with
//     rustc's native build of the same body. That is a claim about the TOOLCHAIN.
//   * IT DOES NOT establish that this code agrees with the ARCHITECTURE. A word
//     mis-classified identically by both native and JIT is native==JIT and still
//     wrong. Architectural agreement is what the objdump differential measures,
//     and it is pinned by `trust-cg-lift/tests/aarch64_allocation.rs`.
// "TRUST-SELF ROUND 27 ... verifying trust-cg's AArch64 INSTRUCTION DECODER"
// must be read in the first sense only.
//
// Re-transcribing the slice onto the fixed decoder is a separate, mechanical
// task; until it happens, do not describe this file as current.

#![allow(dead_code)]

const AARCH64_NOP: u32 = 0xd503_201f;
const AARCH64_BRK_1: u32 = 0xd420_0020;

// ── MODELED (boundary #1): DecodeError -> DecErr fieldless 3-variant enum ──
#[derive(Clone, Copy)]
pub enum DecErr {
    Unsupported,
    Unallocated,
    ConstrainedUnpredictable,
}

// ── the decoded-instruction forms (VERBATIM structs/enums) ─────────────────
#[derive(Clone, Copy)]
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

#[derive(Clone, Copy)]
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

#[derive(Clone, Copy)]
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

#[derive(Clone, Copy)]
pub struct LogicalImm {
    pub sf: u8,
    pub opc: u8,
    pub n: bool,
    pub immr: u8,
    pub imms: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct AddSubImm {
    pub sf: u8,
    pub op: u8,
    pub set_flags: bool,
    pub shift12: bool,
    pub imm12: u16,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct AddSubCarry {
    pub sf: u8,
    pub op: u8,
    pub set_flags: bool,
    pub rm: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct MoveWide {
    pub sf: u8,
    pub opc: u8,
    pub hw: u8,
    pub imm16: u16,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct BitfieldMove {
    pub sf: u8,
    pub opc: u8,
    pub immr: u8,
    pub imms: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct PcRelAddress {
    pub page: bool,
    pub imm21: i32,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct CondBranch {
    pub imm19: u32,
    pub cond: u8,
}

#[derive(Clone, Copy)]
pub struct UncondBranch {
    pub link: bool,
    pub imm26: u32,
}

#[derive(Clone, Copy)]
pub struct BranchReg {
    pub opc: u8,
    pub rn: u8,
}

#[derive(Clone, Copy)]
pub struct TestBranch {
    pub nonzero: bool,
    pub bit: u8,
    pub imm14: u16,
    pub rt: u8,
}

#[derive(Clone, Copy)]
pub struct LoadStoreUnsignedImm {
    pub size: u8,
    pub vector: bool,
    pub opc: u8,
    pub imm12: u16,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Clone, Copy)]
pub struct LoadStoreUnscaled {
    pub size: u8,
    pub vector: bool,
    pub opc: u8,
    pub imm9: i16,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Clone, Copy)]
pub struct LoadStoreIndexed {
    pub size: u8,
    pub vector: bool,
    pub opc: u8,
    pub imm9: i16,
    pub mode: LoadStoreIndexMode,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LoadStoreIndexMode {
    PostIndex,
    PreIndex,
}

#[derive(Clone, Copy)]
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

#[derive(Clone, Copy)]
pub struct LoadLiteral {
    pub opc: u8,
    pub vector: bool,
    pub imm19: u32,
    pub rt: u8,
}

#[derive(Clone, Copy)]
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

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LoadStorePairAddressMode {
    SignedOffset,
    PostIndex,
    PreIndex,
}

#[derive(Clone, Copy)]
pub struct LoadStoreAcquireRelease {
    pub size: u8,
    pub load: bool,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Clone, Copy)]
pub struct LoadStoreExclusiveAcquireRelease {
    pub size: u8,
    pub load: bool,
    pub rs: u8,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Clone, Copy)]
pub struct CompareAndSwap {
    pub size: u8,
    pub acquire: bool,
    pub release: bool,
    pub rs: u8,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LseAtomicRmwOp {
    Add,
    Clr,
    Eor,
    Set,
    Swp,
    Smax,
    Smin,
    Umax,
    Umin,
}

#[derive(Clone, Copy)]
pub struct LseAtomicRmw {
    pub size: u8,
    pub acquire: bool,
    pub release: bool,
    pub op: LseAtomicRmwOp,
    pub rs: u8,
    pub rn: u8,
    pub rt: u8,
}

#[derive(Clone, Copy)]
pub struct CompareBranch {
    pub sf: u8,
    pub nonzero: bool,
    pub imm19: u32,
    pub rt: u8,
}

#[derive(Clone, Copy)]
pub struct DataProcessing2Source {
    pub sf: u8,
    pub opcode: u8,
    pub rm: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct DataProcessing3Source {
    pub sf: u8,
    pub op31: u8,
    pub o0: bool,
    pub rm: u8,
    pub ra: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct ConditionalSelect {
    pub sf: u8,
    pub op: bool,
    pub o2: bool,
    pub rm: u8,
    pub cond: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct FpArith {
    pub ftype: u8,
    pub opcode: u8,
    pub rm: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct FpCompare {
    pub ftype: u8,
    pub rm: u8,
    pub rn: u8,
    pub opc: u8,
}

#[derive(Clone, Copy)]
pub struct FpIntConversion {
    pub sf64: bool,
    pub ftype: u8,
    pub rmode: u8,
    pub opcode: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct FpUnary {
    pub ftype: u8,
    pub opcode: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct FpPrecisionConvert {
    pub src_ftype: u8,
    pub dst_ftype: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct FpImmediate {
    pub ftype: u8,
    pub imm8: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct Brk {
    pub imm16: u16,
}

#[derive(Clone, Copy)]
pub struct SystemBarrier {
    pub kind: SystemBarrierKind,
    pub crm: u8,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SystemBarrierKind {
    Dsb,
    Dmb,
    Isb,
}

#[derive(Clone, Copy)]
pub struct SystemRegisterRead {
    pub sysreg: u16,
    pub rt: u8,
}

#[derive(Clone, Copy)]
pub struct NeonIntVec3Same {
    pub q: bool,
    pub u: bool,
    pub size: u8,
    pub opcode: u8,
    pub rm: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct NeonVecLogic {
    pub q: bool,
    pub u: bool,
    pub size: u8,
    pub rm: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
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

#[derive(Clone, Copy)]
pub struct NeonVecNot {
    pub q: bool,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct NeonAcrossLanes {
    pub q: bool,
    pub u: bool,
    pub size: u8,
    pub opcode: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NeonElementSize {
    B,
    H,
    S,
    D,
}

#[derive(Clone, Copy)]
pub struct NeonDupElement {
    pub q: bool,
    pub element_size: NeonElementSize,
    pub lane: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct NeonDupGeneral {
    pub q: bool,
    pub element_size: NeonElementSize,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct NeonInsGeneral {
    pub element_size: NeonElementSize,
    pub lane: u8,
    pub rn: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct NeonMoviByte {
    pub q: bool,
    pub imm8: u8,
    pub rd: u8,
}

#[derive(Clone, Copy)]
pub struct NeonLdStSinglePostImm {
    pub q: bool,
    pub load: bool,
    pub size: u8,
    pub rn: u8,
    pub rt: u8,
}

/// Decode one 32-bit AArch64 instruction word. (VERBATIM; DecodeError -> DecErr)
pub fn decode(word: u32) -> Result<Instruction, DecErr> {
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
            imm21: sign_extend(bits(word, 29, 2) | (bits(word, 5, 19) << 2u32), 21),
            rd: bits(word, 0, 5) as u8,
        }));
    }

    if bits(word, 24, 5) == 0b01011 && !bit(word, 21) {
        return decode_add_sub_shifted_reg(word);
    }

    if bits(word, 24, 5) == 0b01010 {
        return Ok(Instruction::LogicalShiftedReg(LogicalShiftedReg {
            sf: bits(word, 31, 1) as u8,
            opc: bits(word, 29, 2) as u8,
            shift: bits(word, 22, 2) as u8,
            n: bit(word, 21),
            rm: bits(word, 16, 5) as u8,
            imm6: bits(word, 10, 6) as u8,
            rn: bits(word, 5, 5) as u8,
            rd: bits(word, 0, 5) as u8,
        }));
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
        return Ok(Instruction::LoadStoreUnsignedImm(LoadStoreUnsignedImm {
            size: bits(word, 30, 2) as u8,
            vector: bit(word, 26),
            opc: bits(word, 22, 2) as u8,
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
        match bits(word, 10, 2) {
            0b00 => {
                return Ok(Instruction::LoadStoreUnscaled(LoadStoreUnscaled {
                    size: bits(word, 30, 2) as u8,
                    vector: bit(word, 26),
                    opc: bits(word, 22, 2) as u8,
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
                let vector = bit(word, 26);
                let rn = bits(word, 5, 5) as u8;
                let rt = bits(word, 0, 5) as u8;
                if !vector && rn != 31 && rt == rn {
                    return Err(DecErr::ConstrainedUnpredictable);
                }
                return Ok(Instruction::LoadStoreIndexed(LoadStoreIndexed {
                    size: bits(word, 30, 2) as u8,
                    vector,
                    opc: bits(word, 22, 2) as u8,
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
            _ => return Err(DecErr::Unsupported),
        };

        let opc = bits(word, 30, 2) as u8;
        let vector = bit(word, 26);
        let load = bit(word, 22);
        if !vector && opc == 0b01 && !load {
            return Err(DecErr::Unsupported);
        }

        let rt2 = bits(word, 10, 5) as u8;
        let rn = bits(word, 5, 5) as u8;
        let rt = bits(word, 0, 5) as u8;
        if load && rt == rt2 {
            return Err(DecErr::ConstrainedUnpredictable);
        }
        if !vector
            && !matches!(mode, LoadStorePairAddressMode::SignedOffset)
            && rn != 31
            && (rt == rn || rt2 == rn)
        {
            return Err(DecErr::ConstrainedUnpredictable);
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

    Err(DecErr::Unsupported)
}

fn decode_lse_atomic_rmw(word: u32) -> Result<Instruction, DecErr> {
    let size = bits(word, 30, 2) as u8;
    let acquire = bit(word, 23);
    let release = bit(word, 22);
    let bit21 = bit(word, 21);
    let o3 = bit(word, 15);
    let opc = bits(word, 12, 3) as u8;
    let zero = bits(word, 10, 2);

    if !bit21 || zero != 0 {
        return Err(DecErr::Unsupported);
    }

    let op = match (o3, opc) {
        (false, 0b000) => LseAtomicRmwOp::Add,
        (false, 0b001) => LseAtomicRmwOp::Clr,
        (false, 0b010) => LseAtomicRmwOp::Eor,
        (false, 0b011) => LseAtomicRmwOp::Set,
        (false, 0b100) => LseAtomicRmwOp::Smax,
        (false, 0b101) => LseAtomicRmwOp::Smin,
        (false, 0b110) => LseAtomicRmwOp::Umax,
        (false, 0b111) => LseAtomicRmwOp::Umin,
        (true, 0b000) => LseAtomicRmwOp::Swp,
        _ => return Err(DecErr::Unsupported),
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

fn decode_add_sub_shifted_reg(word: u32) -> Result<Instruction, DecErr> {
    let shift = bits(word, 22, 2) as u8;
    if shift == 0b11 {
        return Err(DecErr::Unallocated);
    }

    Ok(Instruction::AddSubShiftedReg(AddSubShiftedReg {
        sf: bits(word, 31, 1) as u8,
        op: bits(word, 30, 1) as u8,
        set_flags: bit(word, 29),
        shift,
        rm: bits(word, 16, 5) as u8,
        imm6: bits(word, 10, 6) as u8,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_logical_imm(word: u32) -> Result<Instruction, DecErr> {
    let sf = bits(word, 31, 1) as u8;
    let opc = bits(word, 29, 2) as u8;
    let n = bit(word, 22);
    let immr = bits(word, 16, 6) as u8;
    let imms = bits(word, 10, 6) as u8;

    if sf == 0 && n {
        return Err(DecErr::Unallocated);
    }

    if !logical_immediate_bitmask_is_allocated(n, imms) {
        return Err(DecErr::Unallocated);
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

    // F4 boundary (see header #5): VERBATIM was
    // `let len = 7 - pattern.leading_zeros() as u8;` — `leading_zeros` is an
    // unresolved extern leaf at JIT link. `len` = index of the highest set bit of
    // `pattern` (== `7 - leading_zeros` for pattern in 1..=0x7f, pattern != 0 here).
    let mut len: u8 = 0;
    let mut probe: u8 = 6;
    while probe > 0 {
        if (pattern >> probe) & 1 != 0 {
            len = probe;
            break;
        }
        probe -= 1;
    }
    if len < 1 {
        return false;
    }

    let levels = (1u8 << len) - 1;
    imms & levels != levels
}

fn decode_add_sub_carry(word: u32) -> Result<Instruction, DecErr> {
    let set_flags = bit(word, 29);
    if set_flags {
        return Err(DecErr::Unsupported);
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

fn decode_move_wide(word: u32) -> Result<Instruction, DecErr> {
    let opc = bits(word, 29, 2) as u8;
    if opc == 0b01 {
        return Err(DecErr::Unallocated);
    }

    let sf = bits(word, 31, 1) as u8;
    let hw = bits(word, 21, 2) as u8;
    if sf == 0 && hw >= 0b10 {
        return Err(DecErr::Unallocated);
    }

    Ok(Instruction::MoveWide(MoveWide {
        sf,
        opc,
        hw,
        imm16: bits(word, 5, 16) as u16,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_bitfield_move(word: u32) -> Result<Instruction, DecErr> {
    let sf = bits(word, 31, 1) as u8;
    let opc = bits(word, 29, 2) as u8;
    if opc == 0b11 {
        return Err(DecErr::Unsupported);
    }

    let n = bits(word, 22, 1) as u8;
    if n != sf {
        return Err(DecErr::Unallocated);
    }

    let immr = bits(word, 16, 6) as u8;
    let imms = bits(word, 10, 6) as u8;
    if sf == 0 && (immr >= 32 || imms >= 32) {
        return Err(DecErr::Unallocated);
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

fn decode_cond_branch(word: u32) -> Result<Instruction, DecErr> {
    if bit(word, 4) {
        return Err(DecErr::Unallocated);
    }

    Ok(Instruction::CondBranch(CondBranch {
        imm19: bits(word, 5, 19),
        cond: bits(word, 0, 4) as u8,
    }))
}

fn decode_branch_reg(word: u32) -> Result<Instruction, DecErr> {
    let opc = bits(word, 21, 4) as u8;
    if opc > 0b0010 {
        return Err(DecErr::Unallocated);
    }

    Ok(Instruction::BranchReg(BranchReg {
        opc,
        rn: bits(word, 5, 5) as u8,
    }))
}

fn decode_load_store_register(word: u32) -> Result<Instruction, DecErr> {
    let option = bits(word, 13, 3) as u8;
    if option & 0b010 == 0 {
        return Err(DecErr::Unallocated);
    }

    Ok(Instruction::LoadStoreRegister(LoadStoreRegister {
        size: bits(word, 30, 2) as u8,
        vector: bit(word, 26),
        opc: bits(word, 22, 2) as u8,
        rm: bits(word, 16, 5) as u8,
        option,
        shift: bit(word, 12),
        rn: bits(word, 5, 5) as u8,
        rt: bits(word, 0, 5) as u8,
    }))
}

fn decode_load_literal(word: u32) -> Result<Instruction, DecErr> {
    let opc = bits(word, 30, 2) as u8;
    let vector = bit(word, 26);
    if opc != 0b01 || vector {
        return Err(DecErr::Unsupported);
    }

    Ok(Instruction::LoadLiteral(LoadLiteral {
        opc,
        vector,
        imm19: bits(word, 5, 19),
        rt: bits(word, 0, 5) as u8,
    }))
}

fn decode_load_store_acquire_release(word: u32) -> Result<Instruction, DecErr> {
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
                return Err(DecErr::ConstrainedUnpredictable);
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

    Err(DecErr::Unsupported)
}

fn decode_data_processing_2_source(word: u32) -> Result<Instruction, DecErr> {
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
        _ => Err(DecErr::Unsupported),
    }
}

fn decode_data_processing_3_source(word: u32) -> Result<Instruction, DecErr> {
    let sf = bits(word, 31, 1) as u8;
    let op31 = bits(word, 21, 3) as u8;
    let o0 = bit(word, 15);
    let ra = bits(word, 10, 5) as u8;

    match op31 {
        0b000 => {}
        0b001 | 0b101 => {
            if sf != 1 {
                return Err(DecErr::Unallocated);
            }
            if o0 || ra != 31 {
                return Err(DecErr::Unsupported);
            }
        }
        0b010 | 0b110 => {
            if sf != 1 {
                return Err(DecErr::Unallocated);
            }
            if o0 || ra != 31 {
                return Err(DecErr::Unallocated);
            }
        }
        _ => return Err(DecErr::Unsupported),
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

fn decode_conditional_select(word: u32) -> Result<Instruction, DecErr> {
    if bit(word, 29) {
        return Err(DecErr::Unallocated);
    }

    if bit(word, 11) {
        return Err(DecErr::Unallocated);
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

fn decode_fp_scalar(word: u32) -> Result<Instruction, DecErr> {
    let ftype = bits(word, 22, 2) as u8;
    if let Err(e) = validate_fp_ftype(word, ftype) {
        return Err(e);
    }

    if bits(word, 10, 3) == 0b100 {
        return decode_fp_immediate(word, ftype);
    }

    if bits(word, 10, 6) == 0 {
        return decode_fp_int_conversion(word, ftype);
    }

    if bit(word, 31) {
        return Err(DecErr::Unsupported);
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
                if let Err(e) = validate_fp_ftype(word, dst_ftype) {
                    return Err(e);
                }
                Ok(Instruction::FpPrecisionConvert(FpPrecisionConvert {
                    src_ftype: ftype,
                    dst_ftype,
                    rn: bits(word, 5, 5) as u8,
                    rd: bits(word, 0, 5) as u8,
                }))
            }
            _ => Err(DecErr::Unsupported),
        };
    }

    Err(DecErr::Unsupported)
}

fn decode_fp_arith(word: u32, ftype: u8) -> Result<Instruction, DecErr> {
    let opcode = bits(word, 12, 4) as u8;
    if opcode > 0b0011 {
        return Err(DecErr::Unsupported);
    }

    Ok(Instruction::FpArith(FpArith {
        ftype,
        opcode,
        rm: bits(word, 16, 5) as u8,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_fp_compare(word: u32, ftype: u8) -> Result<Instruction, DecErr> {
    let opc = bits(word, 0, 5) as u8;
    match opc {
        0b00000 | 0b10000 => {}
        0b01000 | 0b11000 => {
            if bits(word, 16, 5) != 0 {
                return Err(DecErr::Unallocated);
            }
        }
        _ => return Err(DecErr::Unsupported),
    }

    Ok(Instruction::FpCompare(FpCompare {
        ftype,
        rm: bits(word, 16, 5) as u8,
        rn: bits(word, 5, 5) as u8,
        opc,
    }))
}

fn decode_fp_int_conversion(word: u32, ftype: u8) -> Result<Instruction, DecErr> {
    let rmode = bits(word, 19, 2) as u8;
    let opcode = bits(word, 16, 3) as u8;
    match (rmode, opcode) {
        (0b11, 0b000)
        | (0b11, 0b001)
        | (0b00, 0b010)
        | (0b00, 0b011)
        | (0b00, 0b110)
        | (0b00, 0b111) => Ok(Instruction::FpIntConversion(FpIntConversion {
            sf64: bit(word, 31),
            ftype,
            rmode,
            opcode,
            rn: bits(word, 5, 5) as u8,
            rd: bits(word, 0, 5) as u8,
        })),
        _ => Err(DecErr::Unsupported),
    }
}

fn decode_fp_immediate(word: u32, ftype: u8) -> Result<Instruction, DecErr> {
    if bit(word, 31) {
        return Err(DecErr::Unallocated);
    }

    if bits(word, 5, 5) != 0 {
        return Err(DecErr::Unallocated);
    }

    Ok(Instruction::FpImmediate(FpImmediate {
        ftype,
        imm8: bits(word, 13, 8) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_system(word: u32) -> Result<Instruction, DecErr> {
    if bit(word, 21) {
        return Ok(Instruction::SystemRegisterRead(SystemRegisterRead {
            sysreg: bits(word, 5, 16) as u16,
            rt: bits(word, 0, 5) as u8,
        }));
    }

    if bits(word, 19, 2) == 0
        && bits(word, 16, 3) == 0b011
        && bits(word, 12, 4) == 0b0011
        && bits(word, 0, 5) == 0b11111
    {
        let kind = match bits(word, 5, 3) {
            0b100 => SystemBarrierKind::Dsb,
            0b101 => SystemBarrierKind::Dmb,
            0b110 => SystemBarrierKind::Isb,
            _ => return Err(DecErr::Unsupported),
        };

        return Ok(Instruction::SystemBarrier(SystemBarrier {
            kind,
            crm: bits(word, 8, 4) as u8,
        }));
    }

    Err(DecErr::Unsupported)
}

fn decode_neon_three_same(word: u32) -> Result<Instruction, DecErr> {
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

    match (u, opcode) {
        (false, 0b10000)
        | (true, 0b10000)
        | (false, 0b10011)
        | (true, 0b10001)
        | (false, 0b00110)
        | (false, 0b00111) => {
            if let Err(e) = validate_neon_vector_arrangement(word, q, size) {
                return Err(e);
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

    if opcode == 0b00011 {
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
            _ => return Err(DecErr::Unsupported),
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
            if let Err(e) = validate_neon_fp_arrangement(word, q, sz) {
                return Err(e);
            }
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
        _ => Err(DecErr::Unsupported),
    }
}

fn decode_neon_modified_immediate(word: u32) -> Result<Instruction, DecErr> {
    if !bit(word, 29) && bits(word, 12, 4) == 0b1110 && bits(word, 10, 2) == 0b01 {
        let imm8 = ((bits(word, 16, 3) << 5u32) | bits(word, 5, 5)) as u8;
        return Ok(Instruction::NeonMoviByte(NeonMoviByte {
            q: bit(word, 30),
            imm8,
            rd: bits(word, 0, 5) as u8,
        }));
    }

    Err(DecErr::Unsupported)
}

fn decode_neon_dup_element(word: u32) -> Result<Instruction, DecErr> {
    let q = bit(word, 30);
    let imm5 = bits(word, 16, 5) as u8;
    let (element_size, lane) = match decode_neon_element_imm5(word, imm5) {
        Ok(value) => value,
        Err(e) => return Err(e),
    };

    if !q && matches!(element_size, NeonElementSize::D) {
        return Err(DecErr::Unallocated);
    }

    Ok(Instruction::NeonDupElement(NeonDupElement {
        q,
        element_size,
        lane,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_neon_dup_general(word: u32) -> Result<Instruction, DecErr> {
    let q = bit(word, 30);
    let imm5 = bits(word, 16, 5) as u8;
    let opcode = bits(word, 11, 4);
    let (element_size, lane) = match decode_neon_element_imm5(word, imm5) {
        Ok(value) => value,
        Err(e) => return Err(e),
    };

    if opcode == 0b0011 {
        if !q {
            return Err(DecErr::Unallocated);
        }

        return Ok(Instruction::NeonInsGeneral(NeonInsGeneral {
            element_size,
            lane,
            rn: bits(word, 5, 5) as u8,
            rd: bits(word, 0, 5) as u8,
        }));
    }

    if opcode != 0b0001 {
        return Err(DecErr::Unsupported);
    }

    if !q && matches!(element_size, NeonElementSize::D) {
        return Err(DecErr::Unallocated);
    }

    Ok(Instruction::NeonDupGeneral(NeonDupGeneral {
        q,
        element_size,
        rn: bits(word, 5, 5) as u8,
        rd: bits(word, 0, 5) as u8,
    }))
}

fn decode_neon_ldst_single_post_imm(word: u32) -> Result<Instruction, DecErr> {
    if bit(word, 21) || bits(word, 16, 5) != 0b11111 || bits(word, 12, 4) != 0b0111 {
        return Err(DecErr::Unsupported);
    }

    let q = bit(word, 30);
    let size = bits(word, 10, 2) as u8;
    if let Err(e) = validate_neon_vector_arrangement(word, q, size) {
        return Err(e);
    }

    Ok(Instruction::NeonLdStSinglePostImm(NeonLdStSinglePostImm {
        q,
        load: bit(word, 22),
        size,
        rn: bits(word, 5, 5) as u8,
        rt: bits(word, 0, 5) as u8,
    }))
}

fn validate_fp_ftype(word: u32, ftype: u8) -> Result<(), DecErr> {
    let _ = word;
    if ftype == 0b10 {
        return Err(DecErr::Unallocated);
    }
    Ok(())
}

fn validate_neon_vector_arrangement(word: u32, q: bool, size: u8) -> Result<(), DecErr> {
    let _ = word;
    if !q && size == 0b11 {
        return Err(DecErr::Unallocated);
    }
    Ok(())
}

fn validate_neon_fp_arrangement(word: u32, q: bool, sz: u8) -> Result<(), DecErr> {
    let _ = word;
    if !q && sz == 1 {
        return Err(DecErr::Unallocated);
    }
    Ok(())
}

fn decode_neon_element_imm5(word: u32, imm5: u8) -> Result<(NeonElementSize, u8), DecErr> {
    let _ = word;
    // F4 boundary (see header #5): VERBATIM was `match imm5.trailing_zeros()` —
    // `trailing_zeros` is an unresolved extern leaf at JIT link. `tz` = number of
    // trailing zero bits (== `imm5.trailing_zeros()`; == 8 for imm5 == 0, matching
    // u8::trailing_zeros). imm5 is 5-bit so a nonzero value yields tz in 0..=4; the
    // `_` arm catches imm5 == 0 (tz == 8), exactly as production.
    let tz: u32 = if imm5 == 0 {
        8
    } else {
        let mut t: u32 = 0;
        let mut p: u8 = imm5;
        while p & 1 == 0 {
            t += 1;
            p >>= 1;
        }
        t
    };
    match tz {
        0 => Ok((NeonElementSize::B, imm5 >> 1)),
        1 => Ok((NeonElementSize::H, imm5 >> 2)),
        2 => Ok((NeonElementSize::S, imm5 >> 3)),
        3 => Ok((NeonElementSize::D, imm5 >> 4)),
        4 => Err(DecErr::Unallocated),
        _ => Err(DecErr::Unallocated),
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

// ── harness adapter root (boundary #2): run verbatim `decode`, pack to POD ──
#[repr(C)]
pub struct DecOut {
    pub tag: u32,
    pub a: u32,
    pub b: u32,
    pub c: u32,
    pub d: u32,
    pub e: u32,
    pub f: u32,
    pub g: u32,
    pub h: u32,
}

#[unsafe(no_mangle)]
pub extern "C" fn decode_root(word: u32, out: *mut DecOut) {
    let (tag, a, b, c, d, e, f, g, h): (u32, u32, u32, u32, u32, u32, u32, u32, u32) =
        match decode(word) {
            Ok(Instruction::AddSubShiftedReg(x)) => (
                0,
                x.sf as u32,
                x.op as u32,
                x.set_flags as u32,
                x.shift as u32,
                x.rm as u32,
                x.imm6 as u32,
                x.rn as u32,
                x.rd as u32,
            ),
            Ok(Instruction::LogicalShiftedReg(x)) => (
                1,
                x.sf as u32,
                x.opc as u32,
                x.shift as u32,
                x.n as u32,
                x.rm as u32,
                x.imm6 as u32,
                x.rn as u32,
                x.rd as u32,
            ),
            Ok(Instruction::LogicalImm(x)) => (
                2,
                x.sf as u32,
                x.opc as u32,
                x.n as u32,
                x.immr as u32,
                x.imms as u32,
                x.rn as u32,
                x.rd as u32,
                0,
            ),
            Ok(Instruction::AddSubImm(x)) => (
                3,
                x.sf as u32,
                x.op as u32,
                x.set_flags as u32,
                x.shift12 as u32,
                x.imm12 as u32,
                x.rn as u32,
                x.rd as u32,
                0,
            ),
            Ok(Instruction::AddSubCarry(x)) => (
                4,
                x.sf as u32,
                x.op as u32,
                x.set_flags as u32,
                x.rm as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
            ),
            Ok(Instruction::MoveWide(x)) => (
                5,
                x.sf as u32,
                x.opc as u32,
                x.hw as u32,
                x.imm16 as u32,
                x.rd as u32,
                0,
                0,
                0,
            ),
            Ok(Instruction::BitfieldMove(x)) => (
                6,
                x.sf as u32,
                x.opc as u32,
                x.immr as u32,
                x.imms as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
            ),
            Ok(Instruction::PcRelAddress(x)) => {
                (7, x.page as u32, x.imm21 as u32, x.rd as u32, 0, 0, 0, 0, 0)
            }
            Ok(Instruction::CondBranch(x)) => (8, x.imm19, x.cond as u32, 0, 0, 0, 0, 0, 0),
            Ok(Instruction::UncondBranch(x)) => (9, x.link as u32, x.imm26, 0, 0, 0, 0, 0, 0),
            Ok(Instruction::BranchReg(x)) => (10, x.opc as u32, x.rn as u32, 0, 0, 0, 0, 0, 0),
            Ok(Instruction::TestBranch(x)) => (
                11,
                x.nonzero as u32,
                x.bit as u32,
                x.imm14 as u32,
                x.rt as u32,
                0,
                0,
                0,
                0,
            ),
            Ok(Instruction::LoadStoreUnsignedImm(x)) => (
                12,
                x.size as u32,
                x.vector as u32,
                x.opc as u32,
                x.imm12 as u32,
                x.rn as u32,
                x.rt as u32,
                0,
                0,
            ),
            Ok(Instruction::LoadStoreUnscaled(x)) => (
                13,
                x.size as u32,
                x.vector as u32,
                x.opc as u32,
                x.imm9 as u32,
                x.rn as u32,
                x.rt as u32,
                0,
                0,
            ),
            Ok(Instruction::LoadStoreIndexed(x)) => (
                14,
                x.size as u32,
                x.vector as u32,
                x.opc as u32,
                x.imm9 as u32,
                x.mode as u32,
                x.rn as u32,
                x.rt as u32,
                0,
            ),
            Ok(Instruction::LoadStoreRegister(x)) => (
                15,
                x.size as u32,
                x.vector as u32,
                x.opc as u32,
                x.rm as u32,
                x.option as u32,
                x.shift as u32,
                x.rn as u32,
                x.rt as u32,
            ),
            Ok(Instruction::LoadLiteral(x)) => (
                16,
                x.opc as u32,
                x.vector as u32,
                x.imm19,
                x.rt as u32,
                0,
                0,
                0,
                0,
            ),
            Ok(Instruction::LoadStorePair(x)) => (
                17,
                x.opc as u32,
                x.vector as u32,
                x.load as u32,
                x.mode as u32,
                x.imm7 as u32,
                x.rt2 as u32,
                x.rn as u32,
                x.rt as u32,
            ),
            Ok(Instruction::LoadStoreAcquireRelease(x)) => (
                18,
                x.size as u32,
                x.load as u32,
                x.rn as u32,
                x.rt as u32,
                0,
                0,
                0,
                0,
            ),
            Ok(Instruction::LoadStoreExclusiveAcquireRelease(x)) => (
                19,
                x.size as u32,
                x.load as u32,
                x.rs as u32,
                x.rn as u32,
                x.rt as u32,
                0,
                0,
                0,
            ),
            Ok(Instruction::CompareAndSwap(x)) => (
                20,
                x.size as u32,
                x.acquire as u32,
                x.release as u32,
                x.rs as u32,
                x.rn as u32,
                x.rt as u32,
                0,
                0,
            ),
            Ok(Instruction::LseAtomicRmw(x)) => (
                21,
                x.size as u32,
                x.acquire as u32,
                x.release as u32,
                x.op as u32,
                x.rs as u32,
                x.rn as u32,
                x.rt as u32,
                0,
            ),
            Ok(Instruction::CompareBranch(x)) => (
                22,
                x.sf as u32,
                x.nonzero as u32,
                x.imm19,
                x.rt as u32,
                0,
                0,
                0,
                0,
            ),
            Ok(Instruction::DataProcessing2Source(x)) => (
                23,
                x.sf as u32,
                x.opcode as u32,
                x.rm as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
                0,
            ),
            Ok(Instruction::DataProcessing3Source(x)) => (
                24,
                x.sf as u32,
                x.op31 as u32,
                x.o0 as u32,
                x.rm as u32,
                x.ra as u32,
                x.rn as u32,
                x.rd as u32,
                0,
            ),
            Ok(Instruction::ConditionalSelect(x)) => (
                25,
                x.sf as u32,
                x.op as u32,
                x.o2 as u32,
                x.rm as u32,
                x.cond as u32,
                x.rn as u32,
                x.rd as u32,
                0,
            ),
            Ok(Instruction::FpArith(x)) => (
                26,
                x.ftype as u32,
                x.opcode as u32,
                x.rm as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
                0,
            ),
            Ok(Instruction::FpCompare(x)) => (
                27,
                x.ftype as u32,
                x.rm as u32,
                x.rn as u32,
                x.opc as u32,
                0,
                0,
                0,
                0,
            ),
            Ok(Instruction::FpIntConversion(x)) => (
                28,
                x.sf64 as u32,
                x.ftype as u32,
                x.rmode as u32,
                x.opcode as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
            ),
            Ok(Instruction::FpUnary(x)) => (
                29,
                x.ftype as u32,
                x.opcode as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
                0,
                0,
            ),
            Ok(Instruction::FpPrecisionConvert(x)) => (
                30,
                x.src_ftype as u32,
                x.dst_ftype as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
                0,
                0,
            ),
            Ok(Instruction::FpImmediate(x)) => (
                31,
                x.ftype as u32,
                x.imm8 as u32,
                x.rd as u32,
                0,
                0,
                0,
                0,
                0,
            ),
            Ok(Instruction::Nop) => (32, 0, 0, 0, 0, 0, 0, 0, 0),
            Ok(Instruction::Brk(x)) => (33, x.imm16 as u32, 0, 0, 0, 0, 0, 0, 0),
            Ok(Instruction::SystemBarrier(x)) => {
                (34, x.kind as u32, x.crm as u32, 0, 0, 0, 0, 0, 0)
            }
            Ok(Instruction::SystemRegisterRead(x)) => {
                (35, x.sysreg as u32, x.rt as u32, 0, 0, 0, 0, 0, 0)
            }
            Ok(Instruction::NeonIntVec3Same(x)) => (
                36,
                x.q as u32,
                x.u as u32,
                x.size as u32,
                x.opcode as u32,
                x.rm as u32,
                x.rn as u32,
                x.rd as u32,
                0,
            ),
            Ok(Instruction::NeonVecLogic(x)) => (
                37,
                x.q as u32,
                x.u as u32,
                x.size as u32,
                x.rm as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
            ),
            Ok(Instruction::NeonFpVec3Same(x)) => (
                38,
                x.q as u32,
                x.u as u32,
                x.bit23 as u32,
                x.sz as u32,
                x.opcode as u32,
                x.rm as u32,
                x.rn as u32,
                x.rd as u32,
            ),
            Ok(Instruction::NeonVecNot(x)) => {
                (39, x.q as u32, x.rn as u32, x.rd as u32, 0, 0, 0, 0, 0)
            }
            Ok(Instruction::NeonAcrossLanes(x)) => (
                40,
                x.q as u32,
                x.u as u32,
                x.size as u32,
                x.opcode as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
            ),
            Ok(Instruction::NeonDupElement(x)) => (
                41,
                x.q as u32,
                x.element_size as u32,
                x.lane as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
                0,
            ),
            Ok(Instruction::NeonDupGeneral(x)) => (
                42,
                x.q as u32,
                x.element_size as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
                0,
                0,
            ),
            Ok(Instruction::NeonInsGeneral(x)) => (
                43,
                x.element_size as u32,
                x.lane as u32,
                x.rn as u32,
                x.rd as u32,
                0,
                0,
                0,
                0,
            ),
            Ok(Instruction::NeonMoviByte(x)) => {
                (44, x.q as u32, x.imm8 as u32, x.rd as u32, 0, 0, 0, 0, 0)
            }
            Ok(Instruction::NeonLdStSinglePostImm(x)) => (
                45,
                x.q as u32,
                x.load as u32,
                x.size as u32,
                x.rn as u32,
                x.rt as u32,
                0,
                0,
                0,
            ),
            Err(DecErr::Unsupported) => (0xE0, 0, 0, 0, 0, 0, 0, 0, 0),
            Err(DecErr::Unallocated) => (0xE1, 0, 0, 0, 0, 0, 0, 0, 0),
            Err(DecErr::ConstrainedUnpredictable) => (0xE2, 0, 0, 0, 0, 0, 0, 0, 0),
        };

    unsafe {
        (*out).tag = tag;
        (*out).a = a;
        (*out).b = b;
        (*out).c = c;
        (*out).d = d;
        (*out).e = e;
        (*out).f = f;
        (*out).g = g;
        (*out).h = h;
    }
}

fn main() {
    let mut o = DecOut {
        tag: 0,
        a: 0,
        b: 0,
        c: 0,
        d: 0,
        e: 0,
        f: 0,
        g: 0,
        h: 0,
    };
    decode_root(0xd503_201f, &mut o);
    println!("{}", o.tag);
}
