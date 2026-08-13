// trust-cg-ir - x86-64 opcode definitions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: ~/llvm-project-ref/llvm/lib/Target/X86/X86InstrInfo.td
// Reference: Intel 64 and IA-32 Architectures Software Developer's Manual

//! x86-64 instruction opcode enum.
//!
//! Naming convention follows the AArch64 pattern: `<mnemonic><operand_kinds>`
//! where RR = register-register, RI = register-immediate, RM = register-memory,
//! MR = memory-register.

use crate::inst::InstFlags;

// ---------------------------------------------------------------------------
// X86Opcode
// ---------------------------------------------------------------------------

/// x86-64 instruction opcodes.
///
/// This covers the core integer, logical, move, compare, branch, SSE scalar,
/// and baseline SSE2 packed-integer instructions needed for trust_ir lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum X86Opcode {
    // =====================================================================
    // Arithmetic
    // =====================================================================
    /// ADD r64, r64
    AddRR,
    /// ADD r64, imm32 (sign-extended)
    AddRI,
    /// ADD r64, [mem]
    AddRM,
    /// SUB r64, r64
    SubRR,
    /// SUB r64, imm32 (sign-extended)
    SubRI,
    /// SUB r64, [mem]
    SubRM,
    /// IMUL r64, r64 (signed multiply, two-operand form)
    ImulRR,
    /// IMUL r64, r64, imm32 (signed multiply, three-operand form)
    ImulRRI,
    /// IMUL r64, [mem] (signed multiply, two-operand memory form)
    ImulRM,
    /// IDIV r64 (signed divide RDX:RAX by r64, quotient in RAX, remainder in RDX)
    Idiv,
    /// DIV r64 (unsigned divide RDX:RAX by r64, quotient in RAX, remainder in RDX)
    Div,
    /// NEG r64 (two's complement negate)
    Neg,
    /// INC r64
    Inc,
    /// DEC r64
    Dec,
    /// CDQ — sign-extend EAX into EDX:EAX (32-bit, opcode 99)
    Cdq,
    /// CQO — sign-extend RAX into RDX:RAX (64-bit, REX.W + 99)
    Cqo,

    // =====================================================================
    // Logical / bitwise
    // =====================================================================
    /// AND r64, r64
    AndRR,
    /// AND r64, imm32
    AndRI,
    /// OR r64, r64
    OrRR,
    /// OR r64, imm32
    OrRI,
    /// XOR r64, r64
    XorRR,
    /// XOR r64, imm32
    XorRI,
    /// NOT r64 (bitwise complement)
    Not,

    // =====================================================================
    // Shifts
    // =====================================================================
    /// SHL r64, CL (shift left by CL register)
    ShlRR,
    /// SHL r64, imm8
    ShlRI,
    /// SHR r64, CL (logical shift right by CL)
    ShrRR,
    /// SHR r64, imm8
    ShrRI,
    /// SAR r64, CL (arithmetic shift right by CL)
    SarRR,
    /// SAR r64, imm8
    SarRI,

    // =====================================================================
    // Move
    // =====================================================================
    /// MOV r64, r64
    MovRR,
    /// MOV r64, imm64 (movabs for 64-bit immediates)
    MovRI,
    /// MOV r8, [mem]
    MovRM8,
    /// MOV r16, [mem]
    MovRM16,
    /// MOV r32, [mem]
    MovRM32,
    /// MOV r64, [mem]
    MovRM,
    /// MOV [mem], r8
    MovMR8,
    /// MOV [mem], r16
    MovMR16,
    /// MOV [mem], r32
    MovMR32,
    /// MOV [mem], r64
    MovMR,
    /// MOVZX r64, r8 (zero-extend byte to qword, 0F B6)
    Movzx,
    /// MOVZX r64, r16 (zero-extend word to qword, 0F B7)
    MovzxW,
    /// MOVSX r64, r8 (sign-extend byte to qword, 0F BE)
    MovsxB,
    /// MOVSX r64, r16 (sign-extend word to qword, 0F BF)
    MovsxW,
    /// MOVSXD r64, r32 (sign-extend dword to qword, 63h)
    Movsx,
    /// LEA r64, [mem] (load effective address)
    Lea,
    /// LEA r64, [base + index*scale + disp] (SIB addressing form)
    LeaSib,

    // =====================================================================
    // Scaled-index memory addressing (SIB forms)
    // =====================================================================
    /// MOV r64, [base + index*scale + disp] (scaled-index load)
    MovRMSib,
    /// MOV [base + index*scale + disp], r64 (scaled-index store)
    MovMRSib,
    /// LEA r64, [RIP + disp32] (RIP-relative, for PIC code)
    LeaRip,

    // =====================================================================
    // Compare / test
    // =====================================================================
    /// CMP r64, r64 (sets RFLAGS)
    CmpRR,
    /// CMP r64, imm32 (sets RFLAGS)
    CmpRI,
    /// CMP r/m64, imm8 (sign-extended, sets RFLAGS) — short immediate form
    CmpRI8,
    /// CMP r64, [mem] (sets RFLAGS)
    CmpRM,
    /// TEST r64, r64 (AND without storing result, sets RFLAGS)
    TestRR,
    /// TEST r64, imm32
    TestRI,
    /// TEST r64, [mem] (AND without storing result, sets RFLAGS)
    TestRM,

    // =====================================================================
    // Branch / control flow
    // =====================================================================
    /// JMP rel32 (unconditional near jump)
    Jmp,
    /// Jcc rel32 (conditional near jump based on RFLAGS)
    Jcc,
    /// CALL rel32 (near call)
    Call,
    /// CALL r64 (indirect call)
    CallR,
    /// CALL [mem] (indirect call through memory)
    CallM,
    /// RET (near return)
    Ret,

    // =====================================================================
    // SSE scalar double-precision
    // =====================================================================
    /// ADDSD xmm, xmm (scalar double add)
    Addsd,
    /// SUBSD xmm, xmm (scalar double subtract)
    Subsd,
    /// MULSD xmm, xmm (scalar double multiply)
    Mulsd,
    /// DIVSD xmm, xmm (scalar double divide)
    Divsd,
    /// SQRTSD xmm, xmm (scalar double square root)
    Sqrtsd,
    /// ANDPD xmm, xmm (packed double bitwise and)
    Andpd,
    /// MOVSD xmm, xmm (scalar double move)
    MovsdRR,
    /// MOVSD xmm, [mem] (scalar double load)
    MovsdRM,
    /// MOVSD [mem], xmm (scalar double store)
    MovsdMR,
    /// UCOMISD xmm, xmm (unordered compare scalar double, sets RFLAGS)
    Ucomisd,
    /// MOVDQU xmm, [mem] (unaligned 128-bit XMM load)
    MovdquRM,
    /// MOVDQU [mem], xmm (unaligned 128-bit XMM store)
    MovdquMR,

    // =====================================================================
    // SSE scalar single-precision
    // =====================================================================
    /// ADDSS xmm, xmm (scalar single add)
    Addss,
    /// SUBSS xmm, xmm (scalar single subtract)
    Subss,
    /// MULSS xmm, xmm (scalar single multiply)
    Mulss,
    /// DIVSS xmm, xmm (scalar single divide)
    Divss,
    /// SQRTSS xmm, xmm (scalar single square root)
    Sqrtss,
    /// ANDPS xmm, xmm (packed single bitwise and)
    Andps,
    /// MOVSS xmm, xmm (scalar single move)
    MovssRR,
    /// MOVSS xmm, [mem] (scalar single load)
    MovssRM,
    /// MOVSS [mem], xmm (scalar single store)
    MovssMR,
    /// UCOMISS xmm, xmm (unordered compare scalar single, sets RFLAGS)
    Ucomiss,

    // =====================================================================
    // SSE4.1 scalar round-to-integral
    // =====================================================================
    /// ROUNDSD xmm, xmm, imm8 (round scalar double to integral value). The
    /// imm8 selects the rounding mode: 0 = nearest, 1 = floor (toward -inf),
    /// 2 = ceil (toward +inf), 3 = trunc (toward zero). Encoding:
    /// `66 0F 3A 0B /r ib`.
    Roundsd,
    /// ROUNDSS xmm, xmm, imm8 (round scalar single to integral value). Same
    /// imm8 mode selector as ROUNDSD. Encoding: `66 0F 3A 0A /r ib`.
    Roundss,

    // =====================================================================
    // SSE scalar min/max + compare (for Rust f{32,64}::min/max NaN-away
    // lowering: MINSD/MAXSD + a CMPUNORD-driven NaN-fixup blend)
    // =====================================================================
    /// MINSD xmm, xmm (scalar double minimum). HARDWARE semantics (NOT IEEE
    /// minNum): `dst = (dst < src) ? dst : src` — returns the SECOND operand
    /// (src) when the operands are unordered (either is NaN) OR equal (incl.
    /// ±0). Encoding: `F2 0F 5D /r`.
    Minsd,
    /// MAXSD xmm, xmm (scalar double maximum). HARDWARE semantics: `dst =
    /// (dst > src) ? dst : src` — returns src when unordered or equal.
    /// Encoding: `F2 0F 5F /r`.
    Maxsd,
    /// MINSS xmm, xmm (scalar single minimum). Same hardware semantics as
    /// MINSD. Encoding: `F3 0F 5D /r`.
    Minss,
    /// MAXSS xmm, xmm (scalar single maximum). Same hardware semantics as
    /// MAXSD. Encoding: `F3 0F 5F /r`.
    Maxss,
    /// CMPSD xmm, xmm, imm8 (scalar double compare to mask). With imm8 = 3
    /// (UNORD): `dst = (dst unordered src) ? all-ones-64 : 0` in the low lane.
    /// Used as a self-compare (`CMPSD t, t, 3`) to build an isNaN(t) mask.
    /// Encoding: `F2 0F C2 /r ib`.
    Cmpsd,
    /// CMPSS xmm, xmm, imm8 (scalar single compare to mask). With imm8 = 3
    /// (UNORD): `dst = (dst unordered src) ? all-ones-32 : 0` in the low lane.
    /// Encoding: `F3 0F C2 /r ib`.
    Cmpss,

    // =====================================================================
    // SSE RIP-relative constant pool loads
    // =====================================================================
    /// MOVSS xmm, [RIP+disp32] (load single from constant pool)
    MovssRipRel,
    /// MOVSD xmm, [RIP+disp32] (load double from constant pool)
    MovsdRipRel,

    // =====================================================================
    // Conditional move / set
    // =====================================================================
    /// CMOVcc r64, r64 (conditional move based on RFLAGS)
    Cmovcc,
    /// SETcc r8 (set byte based on RFLAGS condition)
    Setcc,

    // =====================================================================
    // SSE type conversion
    // =====================================================================
    /// CVTSI2SD xmm, r64 (convert signed int64 to scalar double)
    Cvtsi2sd,
    /// CVTSD2SI r64, xmm (convert scalar double to signed int64 using MXCSR rounding)
    Cvtsd2si,
    /// CVTSI2SS xmm, r64 (convert signed int64 to scalar single)
    Cvtsi2ss,
    /// CVTSS2SI r64, xmm (convert scalar single to signed int64 using MXCSR rounding)
    Cvtss2si,
    /// CVTSD2SS xmm, xmm (convert scalar double to scalar single)
    Cvtsd2ss,
    /// CVTSS2SD xmm, xmm (convert scalar single to scalar double)
    Cvtss2sd,

    // =====================================================================
    // Bit manipulation
    // =====================================================================
    /// BSF r64, r64 (bit scan forward — find lowest set bit)
    Bsf,
    /// BSR r64, r64 (bit scan reverse — find highest set bit)
    Bsr,
    /// TZCNT r64, r64 (trailing zero count — BMI1)
    Tzcnt,
    /// LZCNT r64, r64 (leading zero count — ABM/LZCNT)
    Lzcnt,
    /// POPCNT r64, r64 (population count — POPCNT)
    Popcnt,
    /// BT r/m64, imm8 (bit test — sets CF, 0F BA /4 ib)
    BtRI,
    /// BSWAP r64 (byte swap for endianness conversion, 0F C8+rd)
    Bswap,

    // =====================================================================
    // Atomic / exchange
    // =====================================================================
    /// XCHG r64, r64 (swap register contents, 87 /r)
    Xchg,
    /// LOCK CMPXCHG r/m64, r64 (atomic compare and exchange, F0 0F B1 /r)
    Cmpxchg,
    /// MFENCE (serializing load/store memory fence, 0F AE F0)
    Mfence,

    // =====================================================================
    // GPR ↔ XMM transfers
    // =====================================================================
    /// MOVD xmm, r/m32 (move 32-bit GPR to low 32 bits of XMM, 66 0F 6E /r)
    MovdToXmm,
    /// MOVD r/m32, xmm (move low 32 bits of XMM to GPR, 66 0F 7E /r)
    MovdFromXmm,
    /// MOVQ xmm, r/m64 (move 64-bit GPR to XMM, 66 REX.W 0F 6E /r)
    MovqToXmm,
    /// MOVQ r/m64, xmm (move XMM to 64-bit GPR, 66 REX.W 0F 7E /r)
    MovqFromXmm,

    // =====================================================================
    // Stack
    // =====================================================================
    /// PUSH r64
    Push,
    /// POP r64
    Pop,

    // =====================================================================
    // Pseudo-instructions (no hardware encoding)
    // =====================================================================
    /// PHI node (SSA merge point).
    Phi,
    /// Stack allocation pseudo (allocates local stack space).
    StackAlloc,
    /// No-op.
    Nop,

    // =====================================================================
    // Hardware NOP (real encoding)
    // =====================================================================
    /// Multi-byte NOP (0F 1F /0) — for alignment padding (2-9 bytes).
    NopMulti,
    /// MOV r32, r32.
    ///
    /// Kept in its historical slot so existing implicit discriminants remain
    /// stable for code that carries opcodes as `u16`.
    MovRR32,
    /// MOV r64, [RIP+disp32] (load pointer-sized data through a RIP-relative slot).
    ///
    /// Appended after MovRR32 to preserve older opcode discriminants.
    MovRipRel,
    /// CMOVcc r32, r32 (conditional move based on RFLAGS).
    ///
    /// Appended after MovRipRel to preserve older opcode discriminants.
    Cmovcc32,
    /// MUL r/m32|r/m64 (unsigned multiply EDX:EAX/RDX:RAX by operand).
    ///
    /// Appended after Cmovcc32 to preserve older opcode discriminants.
    Mul,
    /// UD2 (undefined instruction trap).
    ///
    /// Appended after Mul to preserve older opcode discriminants.
    Ud2,
    /// CVTTSD2SI r64, xmm (convert scalar double to signed int64 with truncation).
    ///
    /// Appended after Ud2 to preserve older opcode discriminants.
    Cvttsd2si,
    /// CVTTSS2SI r64, xmm (convert scalar single to signed int64 with truncation).
    ///
    /// Appended after Cvttsd2si to preserve older opcode discriminants.
    Cvttss2si,
    /// Pseudo: atomic RMW via a locked CMPXCHG retry loop.
    ///
    /// Operands carry [dst, value, mem, op-kind]. Appended after Cvttss2si to
    /// preserve older opcode discriminants.
    AtomicRmwCasLoop,
    /// Pseudo: 8-bit atomic RMW via a locked CMPXCHG retry loop.
    ///
    /// Operands carry [dst_gpr32, value_gpr32, mem, op-kind]. The encoder uses
    /// AL/R10B internally and zero-extends the old byte value into dst_gpr32.
    AtomicRmwCasLoop8,
    /// Pseudo: 16-bit atomic RMW via a locked CMPXCHG retry loop.
    ///
    /// Operands carry [dst_gpr32, value_gpr32, mem, op-kind]. The encoder uses
    /// AX/R10W internally and zero-extends the old word value into dst_gpr32.
    AtomicRmwCasLoop16,

    // =====================================================================
    // SSE2 packed integer
    // =====================================================================
    /// PAND xmm, xmm/m128 (packed bitwise and, 66 0F DB /r).
    Pand,
    /// PANDN xmm, xmm/m128 (packed bitwise and-not, 66 0F DF /r).
    Pandn,
    /// POR xmm, xmm/m128 (packed bitwise or, 66 0F EB /r).
    Por,
    /// PXOR xmm, xmm/m128 (packed bitwise xor, 66 0F EF /r).
    Pxor,
    /// PCMPEQD xmm, xmm/m128 (packed dword equality compare, 66 0F 76 /r).
    Pcmpeqd,
    /// PSHUFD xmm, xmm/m128, imm8 (packed dword shuffle, 66 0F 70 /r ib).
    Pshufd,
    /// PMOVMSKB r32, xmm (extract packed byte sign bits, 66 0F D7 /r).
    Pmovmskb,
    /// MOVDQA xmm, xmm (aligned 128-bit XMM register copy, 66 0F 6F /r).
    MovdqaRR,
    /// PCMPGTD xmm, xmm/m128 (packed signed dword greater-than compare, 66 0F 66 /r).
    ///
    /// Appended after MovdqaRR to preserve older implicit opcode discriminants.
    Pcmpgtd,
    /// MOVDQA xmm, [mem] (aligned 128-bit XMM load, 66 0F 6F /r).
    ///
    /// Appended after Pcmpgtd to preserve older implicit opcode discriminants.
    MovdqaRM,
    /// MOVDQA [mem], xmm (aligned 128-bit XMM store, 66 0F 7F /r).
    ///
    /// Appended after MovdqaRM to preserve older implicit opcode discriminants.
    MovdqaMR,
    /// PADDD xmm, xmm/m128 (packed dword add, 66 0F FE /r).
    ///
    /// Appended after MovdqaMR to preserve older implicit opcode discriminants.
    Paddd,
    /// PSUBD xmm, xmm/m128 (packed dword subtract, 66 0F FA /r).
    ///
    /// Appended after Paddd to preserve older implicit opcode discriminants.
    Psubd,
    /// PUNPCKLDQ xmm, xmm/m128 (unpack/interleave low dwords, 66 0F 62 /r).
    ///
    /// Appended after Psubd to preserve older implicit opcode discriminants.
    Punpckldq,
    /// PUNPCKLQDQ xmm, xmm/m128 (unpack/interleave low qwords, 66 0F 6C /r).
    ///
    /// Appended after Punpckldq to preserve older implicit opcode discriminants.
    Punpcklqdq,
    /// PADDQ xmm, xmm/m128 (packed qword add, 66 0F D4 /r).
    ///
    /// Appended after Punpcklqdq to preserve older implicit opcode discriminants.
    Paddq,
    /// PSUBQ xmm, xmm/m128 (packed qword subtract, 66 0F FB /r).
    ///
    /// Appended after Paddq to preserve older implicit opcode discriminants.
    Psubq,
    /// PADDB xmm, xmm/m128 (packed byte add, 66 0F FC /r).
    ///
    /// Appended after Psubq to preserve older implicit opcode discriminants.
    Paddb,
    /// PADDW xmm, xmm/m128 (packed word add, 66 0F FD /r).
    ///
    /// Appended after Paddb to preserve older implicit opcode discriminants.
    Paddw,
    /// PSUBB xmm, xmm/m128 (packed byte subtract, 66 0F F8 /r).
    ///
    /// Appended after Paddw to preserve older implicit opcode discriminants.
    Psubb,
    /// PSUBW xmm, xmm/m128 (packed word subtract, 66 0F F9 /r).
    ///
    /// Appended after Psubb to preserve older implicit opcode discriminants.
    Psubw,
    // =====================================================================
    // SSE4.1 packed lane insert/extract
    // =====================================================================
    /// PINSRD xmm, r32, imm8 (insert GPR dword into XMM lane, 66 0F 3A 22 /r ib).
    Pinsrd,
    /// PEXTRD r32, xmm, imm8 (extract XMM dword lane into GPR, 66 0F 3A 16 /r ib).
    Pextrd,
    /// Pseudo: extract a `<4 x i32>` all-ones/zero vector mask into GPR32 lane bits.
    ///
    /// Operands carry `[dst_gpr32, src_xmm]`. The x86-64 pipeline expands this
    /// to `PMOVMSKB` plus scalar normalization, producing bits 0..3 from lanes
    /// 0..3. Direct encoder use intentionally fails closed.
    ///
    /// Appended after Pextrd to preserve older implicit opcode discriminants.
    V4I32MaskExtract,
    /// PMULLD xmm, xmm (packed signed/unsigned dword low multiply, 66 0F 38 40 /r).
    ///
    /// Appended after V4I32MaskExtract to preserve older implicit opcode discriminants.
    Pmulld,
    /// PCMPEQQ xmm, xmm (packed qword equality compare, 66 0F 38 29 /r).
    ///
    /// Appended after Pmulld to preserve older implicit opcode discriminants.
    Pcmpeqq,
    /// PCMPGTQ xmm, xmm (packed signed qword greater-than compare, 66 0F 38 37 /r).
    ///
    /// Appended after Pcmpeqq to preserve older implicit opcode discriminants.
    Pcmpgtq,
    /// PTEST xmm, xmm/m128 (packed bit test, 66 0F 38 17 /r; sets RFLAGS).
    ///
    /// Appended after Pcmpgtq to preserve older implicit opcode discriminants.
    Ptest,
    /// PINSRQ xmm, r64, imm8 (insert GPR qword into XMM lane, 66 REX.W 0F 3A 22 /r ib).
    ///
    /// Appended after Ptest to preserve older implicit opcode discriminants.
    Pinsrq,
    /// PEXTRQ r64, xmm, imm8 (extract XMM qword lane into GPR, 66 REX.W 0F 3A 16 /r ib).
    ///
    /// Appended after Pinsrq to preserve older implicit opcode discriminants.
    Pextrq,
    /// Pseudo: extract a `<2 x i64>` all-ones/zero vector mask into scalar lane bits.
    ///
    /// Operands carry `[dst_gpr32, src_xmm]`. The x86-64 pipeline expands this
    /// to `PMOVMSKB` plus scalar normalization, producing bits 0..1 from lanes
    /// 0..1. Direct encoder use intentionally fails closed.
    ///
    /// Appended after Pextrq to preserve older implicit opcode discriminants.
    V2I64MaskExtract,
    /// PBLENDVB xmm, xmm (SSE4.1 byte select, implicit mask in XMM0).
    ///
    /// Appended after V2I64MaskExtract to preserve older implicit opcode
    /// discriminants.
    Pblendvb,
    /// Pseudo: select bytes from two V128 values with a canonical boolean mask.
    ///
    /// Operands carry `[dst_xmm, mask_xmm, true_xmm, false_xmm]`. The x86-64
    /// pipeline expands this to `PBLENDVB` when SSE4.1 is available, otherwise
    /// to the SSE2 `PAND/PANDN/POR` bitselect sequence. Direct encoder use
    /// intentionally fails closed.
    ///
    /// Appended after Pblendvb to preserve older implicit opcode discriminants.
    V128BoolSelect,
    /// PMULUDQ xmm, xmm/m128 (packed unsigned dword multiply to qword products, 66 0F F4 /r).
    ///
    /// Appended after V128BoolSelect to preserve older implicit opcode discriminants.
    Pmuludq,
    /// PMULLW xmm, xmm/m128 (packed signed word multiply low, 66 0F D5 /r).
    ///
    /// Appended after Pmuludq to preserve older implicit opcode discriminants.
    Pmullw,
    /// PCMPEQB xmm, xmm/m128 (packed byte equality compare, 66 0F 74 /r).
    ///
    /// Appended after Pmullw to preserve older implicit opcode discriminants.
    Pcmpeqb,
    /// PCMPEQW xmm, xmm/m128 (packed word equality compare, 66 0F 75 /r).
    ///
    /// Appended after Pcmpeqb to preserve older implicit opcode discriminants.
    Pcmpeqw,
    /// PCMPGTB xmm, xmm/m128 (packed signed byte greater-than compare, 66 0F 64 /r).
    ///
    /// Appended after Pcmpeqw to preserve older implicit opcode discriminants.
    Pcmpgtb,
    /// PCMPGTW xmm, xmm/m128 (packed signed word greater-than compare, 66 0F 65 /r).
    ///
    /// Appended after Pcmpgtb to preserve older implicit opcode discriminants.
    Pcmpgtw,
    /// Pseudo: extract a `<16 x i8>` all-ones/zero vector mask into GPR32 lane bits.
    ///
    /// Operands carry `[dst_gpr32, src_xmm]`. The x86-64 pipeline expands this
    /// to `PMOVMSKB` plus scalar upper-bit hygiene, producing bits 0..15 from
    /// lanes 0..15. Direct encoder use intentionally fails closed.
    ///
    /// Appended after Pcmpgtw to preserve older implicit opcode discriminants.
    V16I8MaskExtract,
    /// Pseudo: extract a `<8 x i16>` all-ones/zero vector mask into GPR32 lane bits.
    ///
    /// Operands carry `[dst_gpr32, src_xmm]`. The x86-64 pipeline expands this
    /// to `PMOVMSKB` plus scalar bit-pair compression, producing bits 0..7
    /// from lanes 0..7. Direct encoder use intentionally fails closed.
    ///
    /// Appended after V16I8MaskExtract to preserve older implicit opcode
    /// discriminants.
    V8I16MaskExtract,
    /// PSLLD xmm, imm8 (packed dword logical shift left, 66 0F 72 /6 ib).
    ///
    /// Appended after V8I16MaskExtract to preserve older implicit opcode
    /// discriminants.
    Pslld,
    /// PSRLD xmm, imm8 (packed dword logical shift right, 66 0F 72 /2 ib).
    ///
    /// Appended after Pslld to preserve older implicit opcode discriminants.
    Psrld,
    /// PSRAD xmm, imm8 (packed dword arithmetic shift right, 66 0F 72 /4 ib).
    ///
    /// Appended after Psrld to preserve older implicit opcode discriminants.
    Psrad,

    // =====================================================================
    // Add/subtract with carry/borrow (i128 multi-register arithmetic)
    // =====================================================================
    /// ADC r64, r64 (add-with-carry: dst = dst + src + CF, 11 /r form).
    ///
    /// Reads the carry flag set by a prior ADD/ADC and updates it. Used as the
    /// high-half of an i128 addition where the low-half ADD set CF. Mirrors the
    /// AArch64 `Adc` opcode.
    ///
    /// Appended after Psrad to preserve older implicit opcode discriminants.
    AdcRR,
    /// SBB r64, r64 (subtract-with-borrow: dst = dst - src - CF, 19 /r form).
    ///
    /// Reads the carry (borrow) flag set by a prior SUB/SBB and updates it.
    /// Used as the high-half of an i128 subtraction where the low-half SUB set
    /// CF. Mirrors the AArch64 `Sbc` opcode.
    ///
    /// Appended after AdcRR to preserve older implicit opcode discriminants.
    SbbRR,

    // =====================================================================
    // SSE packed single-precision floating-point arithmetic (`<4 x f32>`)
    // =====================================================================
    /// ADDPS xmm, xmm (packed single-precision add, 0F 58 /r).
    ///
    /// Four parallel binary32 IEEE adds, one per 32-bit lane, under the
    /// default MXCSR rounding mode (round-to-nearest-even). No 66 prefix.
    ///
    /// Appended after SbbRR to preserve older implicit opcode discriminants.
    Addps,
    /// SUBPS xmm, xmm (packed single-precision subtract, 0F 5C /r).
    ///
    /// Appended after Addps to preserve older implicit opcode discriminants.
    Subps,
    /// MULPS xmm, xmm (packed single-precision multiply, 0F 59 /r).
    ///
    /// Appended after Subps to preserve older implicit opcode discriminants.
    Mulps,
    /// DIVPS xmm, xmm (packed single-precision divide, 0F 5E /r).
    ///
    /// Appended after Mulps to preserve older implicit opcode discriminants.
    Divps,

    // =====================================================================
    // SSE2 packed double-precision floating-point arithmetic (`<2 x f64>`)
    // =====================================================================
    /// ADDPD xmm, xmm (packed double-precision add, 66 0F 58 /r).
    ///
    /// Two parallel binary64 IEEE adds, one per 64-bit lane, under the
    /// default MXCSR rounding mode (round-to-nearest-even). Mandatory 66
    /// prefix distinguishes it from ADDPS.
    ///
    /// Appended after Divps to preserve older implicit opcode discriminants.
    Addpd,
    /// SUBPD xmm, xmm (packed double-precision subtract, 66 0F 5C /r).
    ///
    /// Appended after Addpd to preserve older implicit opcode discriminants.
    Subpd,
    /// MULPD xmm, xmm (packed double-precision multiply, 66 0F 59 /r).
    ///
    /// Appended after Subpd to preserve older implicit opcode discriminants.
    Mulpd,
    /// DIVPD xmm, xmm (packed double-precision divide, 66 0F 5E /r).
    ///
    /// Appended after Mulpd to preserve older implicit opcode discriminants.
    Divpd,

    // =====================================================================
    // SSE2 byte/word pack and interleave (vector narrowing/unpack helpers)
    // =====================================================================
    /// PUNPCKLBW xmm, xmm/m128 (unpack/interleave low bytes, 66 0F 60 /r).
    ///
    /// Appended after Divpd to preserve older implicit opcode discriminants.
    Punpcklbw,
    /// PUNPCKHBW xmm, xmm/m128 (unpack/interleave high bytes, 66 0F 68 /r).
    ///
    /// Appended after Punpcklbw to preserve older implicit opcode discriminants.
    Punpckhbw,
    /// PACKUSWB xmm, xmm/m128 (pack signed words to unsigned saturated bytes, 66 0F 67 /r).
    ///
    /// Appended after Punpckhbw to preserve older implicit opcode discriminants.
    Packuswb,

    // =====================================================================
    // Proof-only guard carrier (Sentinel S5)
    // =====================================================================
    /// Pseudo: proof-only exact bounds-check carrier `[base, index, Imm(bound)]`.
    ///
    /// This is the x86-64 analogue of AArch64's `TrapBoundsCheckExact`. The
    /// x86 instruction selector emits it ONLY for a `getelementptr inbounds`
    /// access whose exact element count is statically known (i.e. a genuinely
    /// `InBounds`-proven access), recording the discharged-obligation binding by
    /// the operand fingerprint the Certified-Elimination Kernel computes.
    ///
    /// It carries the exact source identity (`base`, `index`, and the immediate
    /// `bound`) so the shared kernel can bind a proof obligation to it. If the
    /// kernel-gated proof pass authorizes elimination the carrier is deleted;
    /// otherwise the x86-64 codegen pipeline EXPANDS it to a real unsigned
    /// `CMP index, bound` + `Jcc AE -> UD2` runtime check
    /// (`expand_x86_bounds_check_carriers`). Direct encoder use intentionally
    /// fails closed (`X86EncodeError::UnsupportedOpcode`) so an un-expanded
    /// carrier can never reach object emission as a silent NOP.
    ///
    /// Appended after Packuswb to preserve older implicit opcode discriminants.
    TrapBoundsCheckExact,

    /// Pseudo: proof-only null-check carrier `[ptr]`.
    ///
    /// This is the x86-64 analogue of AArch64's `TrapNullIfZero`. The x86
    /// instruction selector emits it for a memory access whose pointer is
    /// genuinely `NotNull`-proven (i.e. the source memory node carries
    /// `ProofAnnotation::NotNull`), recording the discharged-obligation binding by
    /// the operand fingerprint the Certified-Elimination Kernel computes.
    ///
    /// It carries the exact source identity (`ptr`) so the shared kernel can bind a
    /// proof obligation to it. If the kernel-gated proof pass authorizes
    /// elimination the carrier is deleted; otherwise the x86-64 codegen pipeline
    /// EXPANDS it to a real `TEST ptr, ptr` + `Jcc E -> UD2` runtime null check
    /// (`expand_x86_null_check_carriers`) — byte-identical to the eager check the
    /// x86 ISel used to emit directly. Direct encoder use intentionally fails
    /// closed (`X86EncodeError::UnsupportedOpcode`) so an un-expanded carrier can
    /// never reach object emission as a silent NOP that would drop the null check.
    ///
    /// Appended after TrapBoundsCheckExact to preserve older implicit opcode
    /// discriminants.
    TrapNullIfZeroExact,

    /// Pseudo: proof-only div-by-zero-check carrier `[divisor]`.
    ///
    /// This is the x86-64 analogue of AArch64's `TrapDivZeroIfZero` (and the exact
    /// structural mirror of `TrapNullIfZeroExact`: a div-by-zero guard is "trap if
    /// divisor == 0", identical to null's "trap if ptr == 0"). The x86 instruction
    /// selector emits it for an integer division/remainder whose divisor is
    /// genuinely `DivNonZero`-proven (i.e. the source node carries
    /// `ProofAnnotation::DivNonZero`), recording the discharged-obligation binding
    /// by the operand fingerprint the Certified-Elimination Kernel computes.
    ///
    /// It carries the exact source identity (`divisor`) so the shared kernel can
    /// bind a proof obligation to it. If the kernel-gated proof pass authorizes
    /// elimination the carrier is deleted; otherwise the x86-64 codegen pipeline
    /// EXPANDS it to a real `TEST divisor, divisor` + `Jcc E -> UD2` runtime
    /// div-by-zero check (`expand_x86_div_zero_check_carriers`) — byte-identical to
    /// the eager check the x86 ISel used to emit directly. Direct encoder use
    /// intentionally fails closed (`X86EncodeError::UnsupportedOpcode`) so an
    /// un-expanded carrier can never reach object emission as a silent NOP that
    /// would drop the div-by-zero check.
    ///
    /// Appended after TrapNullIfZeroExact to preserve older implicit opcode
    /// discriminants.
    TrapDivZeroExact,

    /// Pseudo: proof-only shift-range-check carrier `[amount, Imm(bitwidth)]`.
    ///
    /// This is the x86-64 analogue of AArch64's `TrapShiftRangeIfOOB` (and the
    /// exact structural mirror of `TrapBoundsCheckExact`: a shift-range guard is
    /// "trap if amount >= bitwidth" (unsigned), structurally a `value < bound`
    /// range check identical to bounds' "trap if index >= bound"). The x86
    /// instruction selector emits it for a shift whose amount is genuinely
    /// `ShiftInRange`-proven (i.e. the source node carries
    /// `ProofAnnotation::ShiftInRange`), recording the discharged-obligation
    /// binding by the operand fingerprint the Certified-Elimination Kernel
    /// computes.
    ///
    /// It carries the exact source identity (`amount`) AND the shift width as an
    /// immediate operand, so the shared kernel fingerprints `[amount,
    /// Imm(bitwidth)]` — a 32-bit (width 32) proof can therefore never discharge a
    /// 64-bit (width 64) shift guard, because the fingerprints differ. If the
    /// kernel-gated proof pass authorizes elimination the carrier is deleted;
    /// otherwise the x86-64 codegen pipeline EXPANDS it to a real `CMP amount,
    /// #bitwidth` + `Jcc AE -> UD2` runtime shift-range check
    /// (`expand_x86_shift_range_check_carriers`) — byte-identical to the eager
    /// check the x86 ISel used to emit directly. Direct encoder use intentionally
    /// fails closed (`X86EncodeError::UnsupportedOpcode`) so an un-expanded
    /// carrier can never reach object emission as a silent NOP that would drop the
    /// shift-range check.
    ///
    /// Appended after TrapDivZeroExact to preserve older implicit opcode
    /// discriminants.
    TrapShiftRangeExact,

    /// PSLLQ xmm, imm8 (packed qword logical shift left, 66 0F 73 /6 ib).
    ///
    /// The i64x2 sibling of `Pslld`: both 64-bit lanes shift left by the same
    /// immediate count (counts > 63 zero each lane). Emitted by the x86 SSE2
    /// vectorizer's packed 64-bit multiply compose (PMULUDQ cross-term `<< 32`).
    ///
    /// Appended after TrapShiftRangeExact to preserve older implicit opcode
    /// discriminants.
    Psllq,
    /// PSRLQ xmm, imm8 (packed qword logical shift right, 66 0F 73 /2 ib).
    ///
    /// The i64x2 sibling of `Psrld`: both 64-bit lanes shift right (zero fill)
    /// by the same immediate count (counts > 63 zero each lane). Emitted by the
    /// x86 SSE2 vectorizer's packed 64-bit multiply compose (high-dword extract).
    ///
    /// Appended after Psllq to preserve older implicit opcode discriminants.
    Psrlq,
    /// JMP r64 — indirect near jump through a register (`FF /4`).
    ///
    /// Unconditional indirect branch: `RIP := reg`. Emitted ONLY as the final
    /// dispatch of an x86 jump-table lowering (`select_switch` dense path); the
    /// target register is computed by a preceding `LeaRip`(table base) +
    /// `MovsxdRMSib`(signed 4-byte entry) + `AddRR`, so the transfer target is a
    /// verified `base + table[idx]`. A terminator whose successors are recorded
    /// on the CFG (all case targets ∪ default) so TV-5 sees them. Mirrors the
    /// AArch64 `Br` used by its jump table and x86 `CallR` (both `FF /r` reg-indirect).
    ///
    /// Appended after Psrlq to preserve older implicit opcode discriminants.
    JmpR,
    /// MOVSXD r64, m32 — sign-extend a 32-bit memory dword to 64 bits, with a
    /// scaled-index (SIB) address (`REX.W 63 /r` + SIB).
    ///
    /// `dst_r64 := sext32→64( mem32[ base + index*scale + disp ] )`. The
    /// memory-source sibling of the existing reg-reg `Movsx` (MOVSXD r64,r32).
    /// Emitted ONLY to load a signed 4-byte jump-table entry (`scale=4, disp=0`)
    /// — the exact x86 analogue of AArch64 `LdrswRO [base, index, LSL #2]`.
    ///
    /// Appended after JmpR to preserve older implicit opcode discriminants.
    MovsxdRMSib,
    /// MOV r64, [RIP + disp32] carrying a Mach-O `@TLVP` thread-local
    /// descriptor reference (`REX.W 8B /r`, byte-identical encoding to
    /// `MovRipRel` — only the RELOCATION kind differs).
    ///
    /// `dst := &tlv_descriptor(symbol)` — loads the ADDRESS of the symbol's
    /// thread-local-variable descriptor (`__DATA,__thread_vars` entry). Object
    /// emission records an `X86_64_RELOC_TLV` (pcrel, 4-byte) against the
    /// symbol for the disp32, exactly as clang emits for
    /// `movq _var@TLVP(%rip), %rdi`. The x86-64 Darwin TLS access sequence is
    /// completed by the instruction selector: the descriptor address is passed
    /// in RDI and the descriptor's first word (the dyld-installed
    /// `tlv_get_addr` thunk) is called, returning the variable address in RAX
    /// (`TlsRef { model: Tlv }` lowering, the x86 mirror of AArch64's
    /// Adrp+LdrTlvp+Blr sequence).
    ///
    /// Appended after MovsxdRMSib to preserve older implicit opcode
    /// discriminants.
    MovRipRelTlv,
    /// LOCK CMPXCHG [mem], r8 (`F0 REX 0F B0 /r`) — byte compare-exchange.
    ///
    /// 8-bit sibling of `Cmpxchg` (which handles the 32/64-bit widths via its
    /// register class): compares AL with `[base+disp]`; if equal stores the
    /// low byte of the source register, else loads the memory byte into AL.
    /// The accumulator contract is IDENTICAL to `Cmpxchg` (RAX implicitly
    /// used + defined); the source register is encoded via its byte alias
    /// (REX-extended so SIL/DIL/SPL/BPL encode correctly). Backs
    /// `CmpXchg { ty: I8 }` — `AtomicU8/AtomicBool::compare_exchange` monos
    /// (first surfaced by the wp10-x86 catch_unwind corpus).
    ///
    /// Appended after MovRipRelTlv to preserve older implicit opcode
    /// discriminants.
    Cmpxchg8,
    /// LOCK CMPXCHG [mem], r16 (`F0 66 REX 0F B1 /r`) — word compare-exchange.
    ///
    /// 16-bit sibling of `Cmpxchg8` (operand-size-prefixed `0F B1` form):
    /// compares AX with `[base+disp]`; if equal stores the low word of the
    /// source register, else loads the memory word into AX. Same implicit
    /// RAX accumulator contract. Backs `CmpXchg { ty: I16 }`.
    ///
    /// Appended after Cmpxchg8 to preserve older implicit opcode
    /// discriminants.
    Cmpxchg16,
    /// PSADBW xmm1, xmm2/m128 (`66 0F F6 /r`) — packed sum-of-absolute-differences
    /// of unsigned bytes. For each 8-byte half, computes `Σ |xmm1[i] - xmm2[i]|`
    /// and writes it as a u64 into the corresponding 64-bit lane (bits 63:0 from
    /// bytes 0..7, bits 127:64 from bytes 8..15; the intervening bits are zeroed).
    ///
    /// Used against a zeroed operand as a horizontal BYTE-SUM primitive
    /// (`PSADBW b, 0` = the two byte-sum halves, since `|x - 0| = x` for u8) — the
    /// vectorized lowering of a `count += arr[k] as u64` u8→u64 widening reduction
    /// (b02_sieve; see docs/psadbw-bytesum-vectorizer-design-2026-07-17.md). A pure
    /// V128→V128 producer (no memory, no flags); falls to the `EMPTY` default-flags
    /// arm.
    ///
    /// Appended after Cmpxchg16 to preserve older implicit opcode discriminants.
    Psadbw,
    /// IMUL r64, [base+index*scale+disp] (`REX.W 0F AF /r` + SIB) — the
    /// scaled-index sibling of `ImulRM`, mirroring how `MovRMSib` extends
    /// `MovRM`. Two-address TIED form: `dst := dst * load64(ea)`; reads
    /// memory, writes RFLAGS (CF/OF defined, SF/ZF/AF/PF undefined — the
    /// same partial-overwrite contract as `ImulRR`).
    ///
    /// Producer: the RM-fusion peephole (`MovRMSib t, [sib]; ImulRR d, a, t`
    /// with `t` locally dead → `MovRR d, a; ImulRMSib d, [sib]`), collapsing
    /// the fully-unrolled matmul k-step's separate b-load into the multiply
    /// (X9 slice 3).
    ///
    /// Appended after Psadbw to preserve older implicit opcode discriminants.
    ImulRMSib,
    /// MOV r32, [base+index*scale+disp] (`8B /r` + SIB, no REX.W) — the
    /// 32-bit sibling of `MovRMSib`. Zero-extends into the full register
    /// exactly like `MovRM32`. Producer: the SIB address fold on 32-bit
    /// element arrays (`u32`/`i32` indexing — the b06/b18 class).
    ///
    /// Appended after ImulRMSib to preserve older implicit opcode
    /// discriminants.
    MovRM32Sib,
    /// MOV [base+index*scale+disp], r32 (`89 /r` + SIB, no REX.W) — the
    /// 32-bit sibling of `MovMRSib`, store form of `MovRM32Sib`.
    ///
    /// Appended after MovRM32Sib to preserve older implicit opcode
    /// discriminants.
    MovMR32Sib,

    // -- Volatile memory (MMIO / signal visibility) --
    // Encode BYTE-IDENTICALLY to the corresponding MovRM*/MovMR* scalar,
    // FP, and SIMD forms, but are DISTINCT opcodes classified as observable
    // memory barriers so the optimizer never elides/CSEs/forwards/hoists/
    // reorders them. Appended after MovMR32Sib to preserve every older
    // implicit discriminant.
    /// Volatile MOV r8,  [mem] (same encoding as MovRM8).
    VolatileMovRM8,
    /// Volatile MOV r16, [mem] (same encoding as MovRM16).
    VolatileMovRM16,
    /// Volatile MOV r32, [mem] (same encoding as MovRM32).
    VolatileMovRM32,
    /// Volatile MOV r64, [mem] (same encoding as MovRM).
    VolatileMovRM,
    /// Volatile MOV [mem], r8  (same encoding as MovMR8).
    VolatileMovMR8,
    /// Volatile MOV [mem], r16 (same encoding as MovMR16).
    VolatileMovMR16,
    /// Volatile MOV [mem], r32 (same encoding as MovMR32).
    VolatileMovMR32,
    /// Volatile MOV [mem], r64 (same encoding as MovMR).
    VolatileMovMR,
    /// Volatile MOVSS xmm, [mem] (same encoding as MovssRM).
    VolatileMovssRM,
    /// Volatile MOVSS [mem], xmm (same encoding as MovssMR).
    VolatileMovssMR,
    /// Volatile MOVSD xmm, [mem] (same encoding as MovsdRM).
    VolatileMovsdRM,
    /// Volatile MOVSD [mem], xmm (same encoding as MovsdMR).
    VolatileMovsdMR,
    /// Volatile MOVDQU xmm, [mem] (same encoding as MovdquRM).
    VolatileMovdquRM,
    /// Volatile MOVDQU [mem], xmm (same encoding as MovdquMR).
    VolatileMovdquMR,
    /// Volatile MOVDQA xmm, [mem] (same encoding as MovdqaRM).
    VolatileMovdqaRM,
    /// Volatile MOVDQA [mem], xmm (same encoding as MovdqaMR).
    VolatileMovdqaMR,

    /// MOVSD xmm, [base+index*scale+disp] (`F2 0F 10 /r` + SIB) — the
    /// scaled-index sibling of `MovsdRM`, mirroring how `MovRMSib` extends
    /// `MovRM`. Pure 8-byte FP load; no flags.
    ///
    /// Producer: the SIB address fold on f64 element arrays. Without it every
    /// `a[k]` in a float loop pays three instructions to form the address
    /// (`imulq $8,k / movq base / addq`) AND forces a scratch GPR reload,
    /// because the address math clobbers the register holding the induction
    /// variable — measured as 8 of the 22 instructions in b11_float_dot's inner
    /// loop.
    ///
    /// Appended after VolatileMovdqaMR to preserve older implicit opcode
    /// discriminants.
    MovsdRMSib,
    /// MOVSS xmm, [base+index*scale+disp] (`F3 0F 10 /r` + SIB) — the 4-byte
    /// sibling of `MovsdRMSib`, standing to `MovssRM` as `MovRM32Sib` stands
    /// to `MovRM32`.
    ///
    /// Appended after MovsdRMSib to preserve older implicit opcode
    /// discriminants.
    MovssRMSib,
    /// ROL r/m{32,64}, imm8 (`REX.W? C1 /0 ib`) — rotate left by a constant.
    ///
    /// `dst = (dst << k) | (dst >>u (width - k))` for `k` in `[1, width)`; the
    /// two-address `[dst, src, imm]` shift-by-immediate form, exactly like
    /// `ShlRI` (`/4`) / `ShrRI` (`/5`) / `SarRI` (`/7`).
    ///
    /// Closes a cross-arch parity gap: AArch64 has `RorRI`, x86 had NO rotate
    /// at all, so `rotate_left` lowered to a six-instruction shift/shift/or
    /// sequence — and on a dependency chain the latency cost exceeds even that.
    ///
    /// ⚑ FLAGS DIFFER FROM THE OTHER SHIFTS. ROL writes only CF and OF and
    /// leaves SF/ZF/AF/PF UNAFFECTED — it is NOT the SHL/SHR mask. Anything
    /// reasoning about flag deadness must model that separately or it will
    /// conclude a live flag is dead.
    ///
    /// Appended after MovssRMSib to preserve older implicit opcode
    /// discriminants.
    RolRI,
    /// `MOV r8, [base + index*scale + disp]` — `8A /r` + SIB (scaled-index
    /// 8-bit LOAD). The 8-bit sibling of `MovRMSib` / `MovRM32Sib`.
    ///
    /// Closes a gap that excluded an entire class of Rust code from indexed
    /// addressing: the SIB opcode set was 64-bit, 32-bit and float ONLY, so a
    /// `&[u8]` / `Vec<u8>` / `[u8; N]` access could never fold its address and
    /// paid a base-`Lea` plus an `Add` on every single access.
    ///
    /// ⚑ 8-BIT REGISTER ENCODING TRAP. With no REX prefix, ModRM reg values
    /// 4..=7 name `AH/CH/DH/BH`, not `SPL/BPL/SIL/DIL`. Any 8-bit register
    /// operand in that range must FORCE a REX byte — `low_byte_reg_needs_rex`
    /// plus `emit_rex_forced` is the existing mechanism, shared with `MovRM8`.
    ///
    /// Appended after RolRI to preserve older implicit opcode discriminants.
    MovRM8Sib,
    /// `MOV [base + index*scale + disp], r8` — `88 /r` + SIB (scaled-index
    /// 8-bit STORE). The 8-bit sibling of `MovMRSib` / `MovMR32Sib`; see
    /// `MovRM8Sib` for why this class was missing and for the REX trap.
    ///
    /// Appended after MovRM8Sib to preserve older implicit opcode
    /// discriminants.
    MovMR8Sib,
}

impl X86Opcode {
    /// Returns the default instruction flags for this opcode.
    pub fn default_flags(self) -> InstFlags {
        use X86Opcode::*;
        match self {
            // Unconditional branch
            Jmp => InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            // Indirect near jump through a register (jump-table dispatch). A
            // terminator like `Jmp`; its successors live on the CFG edges.
            JmpR => InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            // Conditional branch
            Jcc => InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),

            // Calls
            Call => InstFlags::IS_CALL.union(InstFlags::HAS_SIDE_EFFECTS),
            CallR => InstFlags::IS_CALL.union(InstFlags::HAS_SIDE_EFFECTS),
            CallM => InstFlags::IS_CALL
                .union(InstFlags::HAS_SIDE_EFFECTS)
                .union(InstFlags::READS_MEMORY),

            // Return
            Ret => InstFlags::IS_RETURN.union(InstFlags::IS_TERMINATOR),

            // Memory loads
            MovRM8 | MovRM16 | MovRM32 | MovRM | MovsdRM | MovssRM | MovdquRM | MovdqaRM
            | AddRM | SubRM | CmpRM | MovRMSib | MovsxdRMSib | MovRM32Sib | ImulRM | ImulRMSib
            | MovsdRMSib | MovssRMSib | MovRM8Sib | MovRipRel | MovssRipRel | MovsdRipRel
            | MovRipRelTlv => InstFlags::READS_MEMORY,

            // Volatile loads: observable reads — mark HAS_SIDE_EFFECTS in
            // addition to READS_MEMORY so DCE never elides them even when the
            // loaded value is dead (an MMIO read must happen).
            VolatileMovRM8 | VolatileMovRM16 | VolatileMovRM32 | VolatileMovRM
            | VolatileMovssRM | VolatileMovsdRM | VolatileMovdquRM | VolatileMovdqaRM => {
                InstFlags::READS_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS)
            }

            // Memory stores
            MovMR8 | MovMR16 | MovMR32 | MovMR | MovsdMR | MovssMR | MovdquMR | MovdqaMR
            | MovMRSib | MovMR32Sib | MovMR8Sib => {
                InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS)
            }

            // Volatile stores: same flags as plain stores (writes memory +
            // side-effecting) — the barrier effect prevents reordering/CSE.
            VolatileMovMR8 | VolatileMovMR16 | VolatileMovMR32 | VolatileMovMR
            | VolatileMovssMR | VolatileMovsdMR | VolatileMovdquMR | VolatileMovdqaMR => {
                InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS)
            }

            // Compare/test (set RFLAGS = side effect)
            CmpRR | CmpRI | CmpRI8 | TestRR | TestRI | Ucomisd | Ucomiss | BtRI => {
                InstFlags::HAS_SIDE_EFFECTS
            }

            // Atomic / exchange forms conservatively model memory effects.
            Xchg | Cmpxchg | Cmpxchg8 | Cmpxchg16 | AtomicRmwCasLoop | AtomicRmwCasLoop8
            | AtomicRmwCasLoop16 => InstFlags::HAS_SIDE_EFFECTS
                .union(InstFlags::READS_MEMORY)
                .union(InstFlags::WRITES_MEMORY),

            // Full memory fence. Model as touching memory so schedulers and
            // effect-aware passes keep loads/stores ordered around it.
            Mfence => InstFlags::HAS_SIDE_EFFECTS
                .union(InstFlags::READS_MEMORY)
                .union(InstFlags::WRITES_MEMORY),

            // Compare/test with memory operand (side effect + memory read)
            TestRM => InstFlags::HAS_SIDE_EFFECTS.union(InstFlags::READS_MEMORY),

            // PTEST supports xmm,xmm and xmm,m128 under one opcode. Opcode-only
            // metadata is conservative; ISel/effects helpers refine proven
            // register-register instances.
            Ptest => InstFlags::HAS_SIDE_EFFECTS.union(InstFlags::READS_MEMORY),

            // SETcc sets RFLAGS-dependent byte (reads RFLAGS)
            Cmovcc32 | Setcc => InstFlags::EMPTY,

            // IDIV/DIV/MUL have implicit operands (RDX:RAX / EDX:EAX).
            Idiv | Div | Mul => InstFlags::HAS_SIDE_EFFECTS,

            // ADC/SBB read the implicit carry flag set by a prior ADD/SUB and
            // also update it. The carry input is NOT visible in the operand
            // list, so they must be ordered after their flag-setter and never
            // CSE'd/DCE'd as pure functions of their explicit operands. Mirror
            // the AArch64 `Adc`/`Sbc` modeling.
            AdcRR | SbbRR => InstFlags::HAS_SIDE_EFFECTS,

            // UD2 is a real target trap instruction.
            Ud2 => InstFlags::HAS_SIDE_EFFECTS.union(InstFlags::IS_TERMINATOR),

            // Proof-only exact bounds-check carrier (Sentinel S5). A pseudo with
            // no hardware encoding that sits INLINE before the proven access (it
            // is NOT a terminator on x86: the access falls through it). It must
            // model side effects so DCE/CSE/copy-prop never silently drop or
            // reorder it before the kernel-gated proof pass decides; the codegen
            // pipeline either deletes it (kernel-authorized) or expands it to a
            // real CMP+Jcc(AE)+UD2 runtime check before encoding.
            TrapBoundsCheckExact => InstFlags::IS_PSEUDO.union(InstFlags::HAS_SIDE_EFFECTS),

            // Proof-only null-check carrier (Sentinel S5). A pseudo with no
            // hardware encoding that sits INLINE before the proven access (it is
            // NOT a terminator on x86: the access falls through it). It must model
            // side effects so DCE/CSE/copy-prop never silently drop or reorder it
            // before the kernel-gated proof pass decides; the codegen pipeline
            // either deletes it (kernel-authorized) or expands it to a real
            // TEST+Jcc(E)+UD2 runtime null check before encoding.
            TrapNullIfZeroExact => InstFlags::IS_PSEUDO.union(InstFlags::HAS_SIDE_EFFECTS),

            // Proof-only div-by-zero-check carrier (Sentinel S5). A pseudo with no
            // hardware encoding that sits INLINE before the proven divide (it is
            // NOT a terminator on x86: the divide falls through it). It must model
            // side effects so DCE/CSE/copy-prop never silently drop or reorder it
            // before the kernel-gated proof pass decides; the codegen pipeline
            // either deletes it (kernel-authorized) or expands it to a real
            // TEST+Jcc(E)+UD2 runtime div-by-zero check before encoding.
            TrapDivZeroExact => InstFlags::IS_PSEUDO.union(InstFlags::HAS_SIDE_EFFECTS),

            // Proof-only shift-range-check carrier (Sentinel S5). A pseudo with no
            // hardware encoding that sits INLINE before the proven shift (it is
            // NOT a terminator on x86: the shift falls through it). It must model
            // side effects so DCE/CSE/copy-prop never silently drop or reorder it
            // before the kernel-gated proof pass decides; the codegen pipeline
            // either deletes it (kernel-authorized) or expands it to a real
            // CMP+Jcc(AE)+UD2 runtime shift-range check before encoding.
            TrapShiftRangeExact => InstFlags::IS_PSEUDO.union(InstFlags::HAS_SIDE_EFFECTS),

            // CDQ/CQO write implicit RDX register
            Cdq | Cqo => InstFlags::HAS_SIDE_EFFECTS,

            // Stack manipulation (modifies RSP)
            Push => InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS),
            Pop => InstFlags::READS_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS),

            // Pseudo-instructions
            Phi => InstFlags::IS_PSEUDO,
            V4I32MaskExtract | V16I8MaskExtract | V8I16MaskExtract | V2I64MaskExtract
            | V128BoolSelect => InstFlags::IS_PSEUDO,
            StackAlloc => InstFlags::IS_PSEUDO.union(InstFlags::HAS_SIDE_EFFECTS),
            Nop => InstFlags::IS_PSEUDO,

            // Everything else: pure computation
            _ => InstFlags::EMPTY,
        }
    }

    /// Returns true if this is a pseudo-instruction with no hardware encoding.
    pub fn is_pseudo(self) -> bool {
        matches!(
            self,
            Self::Phi
                | Self::StackAlloc
                | Self::Nop
                | Self::V4I32MaskExtract
                | Self::V16I8MaskExtract
                | Self::V8I16MaskExtract
                | Self::V2I64MaskExtract
                | Self::V128BoolSelect
                | Self::TrapBoundsCheckExact
                | Self::TrapNullIfZeroExact
                | Self::TrapDivZeroExact
                | Self::TrapShiftRangeExact
        )
    }

    /// Returns true if this is a phi instruction.
    pub fn is_phi(self) -> bool {
        matches!(self, Self::Phi)
    }
}

// ---------------------------------------------------------------------------
// SSE2 packed integer opcode surface
// ---------------------------------------------------------------------------

/// Standalone SSE2 packed integer opcodes.
///
/// This compatibility surface is retained for direct encoder/fuzz users. The
/// pipeline-coupled surface lives in [`X86Opcode`], and each variant maps
/// one-for-one via [`X86Sse2PackedOpcode::to_x86_opcode`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum X86Sse2PackedOpcode {
    /// PAND xmm, xmm/m128 (packed bitwise and, 66 0F DB /r)
    Pand,
    /// PANDN xmm, xmm/m128 (packed bitwise and-not, 66 0F DF /r)
    Pandn,
    /// POR xmm, xmm/m128 (packed bitwise or, 66 0F EB /r)
    Por,
    /// PXOR xmm, xmm/m128 (packed bitwise xor, 66 0F EF /r)
    Pxor,
    /// PCMPEQD xmm, xmm/m128 (packed dword equality compare, 66 0F 76 /r)
    Pcmpeqd,
    /// PSHUFD xmm, xmm/m128, imm8 (packed dword shuffle, 66 0F 70 /r ib)
    Pshufd,
    /// PMOVMSKB r32, xmm (extract packed byte sign bits, 66 0F D7 /r)
    Pmovmskb,
    /// MOVDQA xmm, xmm (aligned 128-bit XMM register copy, 66 0F 6F /r)
    MovdqaRR,
    /// PCMPGTD xmm, xmm/m128 (packed signed dword greater-than compare, 66 0F 66 /r)
    Pcmpgtd,
    /// PADDD xmm, xmm/m128 (packed dword add, 66 0F FE /r)
    Paddd,
    /// PSUBD xmm, xmm/m128 (packed dword subtract, 66 0F FA /r)
    Psubd,
    /// PCMPEQQ xmm, xmm (packed qword equality compare, 66 0F 38 29 /r)
    Pcmpeqq,
    /// PCMPGTQ xmm, xmm (packed signed qword greater-than compare, 66 0F 38 37 /r)
    Pcmpgtq,
    /// PUNPCKLDQ xmm, xmm/m128 (unpack/interleave low dwords, 66 0F 62 /r)
    Punpckldq,
    /// PUNPCKLQDQ xmm, xmm/m128 (unpack/interleave low qwords, 66 0F 6C /r)
    Punpcklqdq,
    /// PADDQ xmm, xmm/m128 (packed qword add, 66 0F D4 /r)
    Paddq,
    /// PSUBQ xmm, xmm/m128 (packed qword subtract, 66 0F FB /r)
    Psubq,
    /// PADDB xmm, xmm/m128 (packed byte add, 66 0F FC /r)
    Paddb,
    /// PADDW xmm, xmm/m128 (packed word add, 66 0F FD /r)
    Paddw,
    /// PSUBB xmm, xmm/m128 (packed byte subtract, 66 0F F8 /r)
    Psubb,
    /// PSUBW xmm, xmm/m128 (packed word subtract, 66 0F F9 /r)
    Psubw,
    /// PMULUDQ xmm, xmm/m128 (packed unsigned dword multiply to qword products, 66 0F F4 /r)
    Pmuludq,
    /// PCMPEQB xmm, xmm/m128 (packed byte equality compare, 66 0F 74 /r)
    Pcmpeqb,
    /// PCMPEQW xmm, xmm/m128 (packed word equality compare, 66 0F 75 /r)
    Pcmpeqw,
    /// PCMPGTB xmm, xmm/m128 (packed signed byte greater-than compare, 66 0F 64 /r)
    Pcmpgtb,
    /// PCMPGTW xmm, xmm/m128 (packed signed word greater-than compare, 66 0F 65 /r)
    Pcmpgtw,
    /// PSLLD xmm, imm8 (packed dword logical shift left, 66 0F 72 /6 ib)
    Pslld,
    /// PSRLD xmm, imm8 (packed dword logical shift right, 66 0F 72 /2 ib)
    Psrld,
    /// PSRAD xmm, imm8 (packed dword arithmetic shift right, 66 0F 72 /4 ib)
    Psrad,
    /// PUNPCKLBW xmm, xmm/m128 (unpack/interleave low bytes, 66 0F 60 /r)
    Punpcklbw,
    /// PUNPCKHBW xmm, xmm/m128 (unpack/interleave high bytes, 66 0F 68 /r)
    Punpckhbw,
    /// PACKUSWB xmm, xmm/m128 (pack signed words to unsigned saturated bytes, 66 0F 67 /r)
    Packuswb,
    /// PMULLW xmm, xmm/m128 (packed signed word multiply low, 66 0F D5 /r)
    Pmullw,
    /// PSLLQ xmm, imm8 (packed qword logical shift left, 66 0F 73 /6 ib)
    Psllq,
    /// PSRLQ xmm, imm8 (packed qword logical shift right, 66 0F 73 /2 ib)
    Psrlq,
}

impl X86Sse2PackedOpcode {
    /// Return the pipeline-coupled x86 opcode for this packed SSE2 helper.
    pub const fn to_x86_opcode(self) -> X86Opcode {
        match self {
            Self::Pand => X86Opcode::Pand,
            Self::Pandn => X86Opcode::Pandn,
            Self::Por => X86Opcode::Por,
            Self::Pxor => X86Opcode::Pxor,
            Self::Pcmpeqd => X86Opcode::Pcmpeqd,
            Self::Pshufd => X86Opcode::Pshufd,
            Self::Pmovmskb => X86Opcode::Pmovmskb,
            Self::MovdqaRR => X86Opcode::MovdqaRR,
            Self::Pcmpgtd => X86Opcode::Pcmpgtd,
            Self::Paddd => X86Opcode::Paddd,
            Self::Psubd => X86Opcode::Psubd,
            Self::Pcmpeqq => X86Opcode::Pcmpeqq,
            Self::Pcmpgtq => X86Opcode::Pcmpgtq,
            Self::Punpckldq => X86Opcode::Punpckldq,
            Self::Punpcklqdq => X86Opcode::Punpcklqdq,
            Self::Paddq => X86Opcode::Paddq,
            Self::Psubq => X86Opcode::Psubq,
            Self::Paddb => X86Opcode::Paddb,
            Self::Paddw => X86Opcode::Paddw,
            Self::Psubb => X86Opcode::Psubb,
            Self::Psubw => X86Opcode::Psubw,
            Self::Pmullw => X86Opcode::Pmullw,
            Self::Pmuludq => X86Opcode::Pmuludq,
            Self::Pcmpeqb => X86Opcode::Pcmpeqb,
            Self::Pcmpeqw => X86Opcode::Pcmpeqw,
            Self::Pcmpgtb => X86Opcode::Pcmpgtb,
            Self::Pcmpgtw => X86Opcode::Pcmpgtw,
            Self::Pslld => X86Opcode::Pslld,
            Self::Psrld => X86Opcode::Psrld,
            Self::Psrad => X86Opcode::Psrad,
            Self::Psllq => X86Opcode::Psllq,
            Self::Psrlq => X86Opcode::Psrlq,
            Self::Punpcklbw => X86Opcode::Punpcklbw,
            Self::Punpckhbw => X86Opcode::Punpckhbw,
            Self::Packuswb => X86Opcode::Packuswb,
        }
    }

    /// Returns the default instruction flags for this opcode.
    pub fn default_flags(self) -> InstFlags {
        InstFlags::EMPTY
    }

    /// Returns true if the opcode's register-register operation is
    /// mathematically commutative.
    pub fn is_commutative(self) -> bool {
        matches!(
            self,
            Self::Pand
                | Self::Por
                | Self::Pxor
                | Self::Pcmpeqb
                | Self::Pcmpeqw
                | Self::Pcmpeqd
                | Self::Paddb
                | Self::Paddw
                | Self::Paddd
                | Self::Pcmpeqq
                | Self::Paddq
                | Self::Pmullw
                | Self::Pmuludq
        )
    }

    /// Returns true when the opcode produces a destination value.
    pub fn produces_value(self) -> bool {
        true
    }
}

impl From<X86Sse2PackedOpcode> for X86Opcode {
    fn from(opcode: X86Sse2PackedOpcode) -> Self {
        opcode.to_x86_opcode()
    }
}

// ---------------------------------------------------------------------------
// x86-64 Condition Codes (for Jcc, SETcc, CMOVcc)
// ---------------------------------------------------------------------------
// Reference: Intel SDM Vol 2A, Appendix B (Jcc encoding)

/// x86-64 condition code for conditional jumps, sets, and moves.
///
/// The 4-bit encoding matches the hardware encoding used in Jcc/SETcc/CMOVcc
/// opcode bytes (0F 80+cc through 0F 8F+cc).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum X86CondCode {
    /// Overflow (OF=1)
    O = 0x0,
    /// No overflow (OF=0)
    NO = 0x1,
    /// Below / carry (CF=1) — unsigned less than
    B = 0x2,
    /// Above or equal / no carry (CF=0) — unsigned greater or equal
    AE = 0x3,
    /// Equal / zero (ZF=1)
    E = 0x4,
    /// Not equal / not zero (ZF=0)
    NE = 0x5,
    /// Below or equal (CF=1 or ZF=1) — unsigned less or equal
    BE = 0x6,
    /// Above (CF=0 and ZF=0) — unsigned greater
    A = 0x7,
    /// Sign / negative (SF=1)
    S = 0x8,
    /// No sign / positive (SF=0)
    NS = 0x9,
    /// Parity even (PF=1)
    P = 0xA,
    /// Parity odd (PF=0)
    NP = 0xB,
    /// Less than (SF!=OF) — signed less than
    L = 0xC,
    /// Greater or equal (SF=OF) — signed greater or equal
    GE = 0xD,
    /// Less or equal (ZF=1 or SF!=OF) — signed less or equal
    LE = 0xE,
    /// Greater (ZF=0 and SF=OF) — signed greater than
    G = 0xF,
}

impl X86CondCode {
    /// Return the 4-bit hardware encoding.
    #[inline]
    pub const fn encoding(self) -> u8 {
        self as u8
    }

    /// Invert the condition (logical negation).
    ///
    /// Flipping bit 0 of the encoding inverts the condition.
    #[inline]
    pub const fn invert(self) -> Self {
        let inv = (self as u8) ^ 1;
        // SAFETY: all 16 values 0x0..=0xF are valid X86CondCode variants.
        unsafe { core::mem::transmute::<u8, X86CondCode>(inv) }
    }

    /// Return the assembly mnemonic suffix.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::O => "o",
            Self::NO => "no",
            Self::B => "b",
            Self::AE => "ae",
            Self::E => "e",
            Self::NE => "ne",
            Self::BE => "be",
            Self::A => "a",
            Self::S => "s",
            Self::NS => "ns",
            Self::P => "p",
            Self::NP => "np",
            Self::L => "l",
            Self::GE => "ge",
            Self::LE => "le",
            Self::G => "g",
        }
    }

    /// Return `true` if this is a signed comparison condition.
    #[inline]
    pub const fn is_signed(self) -> bool {
        matches!(self, Self::L | Self::GE | Self::LE | Self::G)
    }

    /// Return `true` if this is an unsigned comparison condition.
    #[inline]
    pub const fn is_unsigned(self) -> bool {
        matches!(self, Self::B | Self::AE | Self::BE | Self::A)
    }
}

impl core::fmt::Display for X86CondCode {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.as_str())
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn volatile_opcodes_are_appended_after_the_preexisting_surface() {
        assert_eq!(
            X86Opcode::VolatileMovRM8 as usize,
            X86Opcode::MovMR32Sib as usize + 1
        );
        assert_eq!(
            X86Opcode::VolatileMovdqaMR as usize,
            X86Opcode::VolatileMovRM8 as usize + 15
        );
    }

    #[test]
    fn branch_opcodes_have_branch_and_terminator_flags() {
        let flags = X86Opcode::Jmp.default_flags();
        assert!(flags.contains(InstFlags::IS_BRANCH));
        assert!(flags.contains(InstFlags::IS_TERMINATOR));

        let flags = X86Opcode::Jcc.default_flags();
        assert!(flags.contains(InstFlags::IS_BRANCH));
        assert!(flags.contains(InstFlags::IS_TERMINATOR));
    }

    #[test]
    fn call_opcodes_have_call_and_side_effect_flags() {
        for op in &[X86Opcode::Call, X86Opcode::CallR, X86Opcode::CallM] {
            let flags = op.default_flags();
            assert!(flags.contains(InstFlags::IS_CALL), "{:?}", op);
            assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS), "{:?}", op);
        }
        // CallM also reads memory
        let flags = X86Opcode::CallM.default_flags();
        assert!(flags.contains(InstFlags::READS_MEMORY));
    }

    #[test]
    fn ret_has_return_and_terminator() {
        let flags = X86Opcode::Ret.default_flags();
        assert!(flags.contains(InstFlags::IS_RETURN));
        assert!(flags.contains(InstFlags::IS_TERMINATOR));
    }

    #[test]
    fn vector_pseudos_are_pipeline_only() {
        for opcode in [
            X86Opcode::V4I32MaskExtract,
            X86Opcode::V16I8MaskExtract,
            X86Opcode::V8I16MaskExtract,
            X86Opcode::V2I64MaskExtract,
            X86Opcode::V128BoolSelect,
        ] {
            let flags = opcode.default_flags();
            assert!(flags.contains(InstFlags::IS_PSEUDO));
            assert!(opcode.is_pseudo());
        }
    }

    #[test]
    fn memory_load_opcodes() {
        for op in &[
            X86Opcode::MovRM8,
            X86Opcode::MovRM16,
            X86Opcode::MovRM32,
            X86Opcode::MovRM,
            X86Opcode::MovsdRM,
            X86Opcode::MovssRM,
            X86Opcode::MovdquRM,
            X86Opcode::MovdqaRM,
            X86Opcode::MovRMSib,
            X86Opcode::ImulRM,
            X86Opcode::ImulRMSib,
            X86Opcode::MovsdRMSib,
            X86Opcode::MovssRMSib,
            X86Opcode::MovRipRel,
            X86Opcode::MovssRipRel,
            X86Opcode::MovsdRipRel,
        ] {
            let flags = op.default_flags();
            assert!(flags.contains(InstFlags::READS_MEMORY), "{:?}", op);
            assert!(!flags.contains(InstFlags::WRITES_MEMORY), "{:?}", op);
        }
    }

    #[test]
    fn memory_store_opcodes() {
        for op in &[
            X86Opcode::MovMR8,
            X86Opcode::MovMR16,
            X86Opcode::MovMR32,
            X86Opcode::MovMR,
            X86Opcode::MovsdMR,
            X86Opcode::MovssMR,
            X86Opcode::MovdquMR,
            X86Opcode::MovdqaMR,
            X86Opcode::MovMRSib,
        ] {
            let flags = op.default_flags();
            assert!(flags.contains(InstFlags::WRITES_MEMORY), "{:?}", op);
            assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS), "{:?}", op);
        }
    }

    #[test]
    fn compare_opcodes_have_side_effects() {
        for op in &[
            X86Opcode::CmpRR,
            X86Opcode::CmpRI,
            X86Opcode::CmpRI8,
            X86Opcode::TestRR,
            X86Opcode::TestRI,
            X86Opcode::TestRM,
            X86Opcode::Ucomisd,
            X86Opcode::Ucomiss,
            X86Opcode::Ptest,
        ] {
            let flags = op.default_flags();
            assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS), "{:?}", op);
        }
        // TestRM also reads memory
        let flags = X86Opcode::TestRM.default_flags();
        assert!(flags.contains(InstFlags::READS_MEMORY));
        let flags = X86Opcode::Ptest.default_flags();
        assert!(flags.contains(InstFlags::READS_MEMORY));
    }

    #[test]
    fn atomic_exchange_opcodes_have_memory_effects() {
        for op in &[
            X86Opcode::Xchg,
            X86Opcode::Cmpxchg,
            X86Opcode::AtomicRmwCasLoop,
        ] {
            let flags = op.default_flags();
            assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS), "{:?}", op);
            assert!(flags.contains(InstFlags::READS_MEMORY), "{:?}", op);
            assert!(flags.contains(InstFlags::WRITES_MEMORY), "{:?}", op);
        }
    }

    #[test]
    fn mfence_has_memory_barrier_flags() {
        let flags = X86Opcode::Mfence.default_flags();
        assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS));
        assert!(flags.contains(InstFlags::READS_MEMORY));
        assert!(flags.contains(InstFlags::WRITES_MEMORY));
        assert!(!X86Opcode::Mfence.is_pseudo());
    }

    #[test]
    fn pure_arithmetic_has_empty_flags() {
        let pure_ops = [
            X86Opcode::AddRR,
            X86Opcode::AddRI,
            X86Opcode::SubRR,
            X86Opcode::SubRI,
            X86Opcode::ImulRR,
            X86Opcode::ImulRRI,
            X86Opcode::Neg,
            X86Opcode::Inc,
            X86Opcode::Dec,
            X86Opcode::AndRR,
            X86Opcode::AndRI,
            X86Opcode::OrRR,
            X86Opcode::OrRI,
            X86Opcode::XorRR,
            X86Opcode::XorRI,
            X86Opcode::Not,
            X86Opcode::ShlRR,
            X86Opcode::ShlRI,
            X86Opcode::ShrRR,
            X86Opcode::ShrRI,
            X86Opcode::SarRR,
            X86Opcode::SarRI,
            X86Opcode::MovRR,
            X86Opcode::MovRR32,
            X86Opcode::MovRI,
            X86Opcode::Movzx,
            X86Opcode::MovzxW,
            X86Opcode::MovsxB,
            X86Opcode::MovsxW,
            X86Opcode::Movsx,
            X86Opcode::Lea,
            X86Opcode::LeaSib,
            X86Opcode::LeaRip,
            X86Opcode::Addsd,
            X86Opcode::Subsd,
            X86Opcode::Mulsd,
            X86Opcode::Divsd,
            X86Opcode::Sqrtsd,
            X86Opcode::Andpd,
            X86Opcode::MovsdRR,
            // SSE single-precision
            X86Opcode::Addss,
            X86Opcode::Subss,
            X86Opcode::Mulss,
            X86Opcode::Divss,
            X86Opcode::Sqrtss,
            X86Opcode::Andps,
            X86Opcode::MovssRR,
            // SSE type conversion
            X86Opcode::Cvtsi2sd,
            X86Opcode::Cvtsd2si,
            X86Opcode::Cvttsd2si,
            X86Opcode::Cvtsi2ss,
            X86Opcode::Cvtss2si,
            X86Opcode::Cvttss2si,
            X86Opcode::Cvtsd2ss,
            X86Opcode::Cvtss2sd,
            // Conditional move, SETcc, bit manipulation
            X86Opcode::Cmovcc,
            X86Opcode::Cmovcc32,
            X86Opcode::Setcc,
            X86Opcode::Bsf,
            X86Opcode::Bsr,
            X86Opcode::Tzcnt,
            X86Opcode::Lzcnt,
            X86Opcode::Popcnt,
            X86Opcode::Bswap,
            // GPR ↔ XMM transfers
            X86Opcode::MovdToXmm,
            X86Opcode::MovdFromXmm,
            X86Opcode::MovqToXmm,
            X86Opcode::MovqFromXmm,
            // SSE2 packed integer
            X86Opcode::Pand,
            X86Opcode::Pandn,
            X86Opcode::Por,
            X86Opcode::Pxor,
            X86Opcode::Pcmpeqd,
            X86Opcode::Pshufd,
            X86Opcode::Pmovmskb,
            X86Opcode::MovdqaRR,
            X86Opcode::Pcmpgtd,
            X86Opcode::Paddb,
            X86Opcode::Paddw,
            X86Opcode::Paddd,
            X86Opcode::Psubb,
            X86Opcode::Psubw,
            X86Opcode::Psubd,
            X86Opcode::Pmullw,
            X86Opcode::Punpckldq,
            X86Opcode::Punpcklqdq,
            X86Opcode::Paddq,
            X86Opcode::Psubq,
            X86Opcode::Pmuludq,
            X86Opcode::Pcmpeqb,
            X86Opcode::Pcmpeqw,
            X86Opcode::Pcmpgtb,
            X86Opcode::Pcmpgtw,
            X86Opcode::Pcmpeqq,
            X86Opcode::Pcmpgtq,
            X86Opcode::Pblendvb,
            X86Opcode::Pslld,
            X86Opcode::Psrld,
            X86Opcode::Psrad,
            X86Opcode::Psllq,
            X86Opcode::Psrlq,
            X86Opcode::Punpcklbw,
            X86Opcode::Punpckhbw,
            X86Opcode::Packuswb,
            // SSE4.1 packed lane insert/extract
            X86Opcode::Pinsrd,
            X86Opcode::Pextrd,
            X86Opcode::Pinsrq,
            X86Opcode::Pextrq,
            // Hardware NOP
            X86Opcode::NopMulti,
        ];
        for op in &pure_ops {
            assert!(
                op.default_flags().is_empty(),
                "{:?} should have EMPTY flags",
                op
            );
        }
    }

    #[test]
    fn cdq_cqo_have_side_effects() {
        let flags = X86Opcode::Cdq.default_flags();
        assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS));
        let flags = X86Opcode::Cqo.default_flags();
        assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS));
    }

    #[test]
    fn fixed_register_arithmetic_has_side_effects() {
        for op in &[X86Opcode::Idiv, X86Opcode::Div, X86Opcode::Mul] {
            let flags = op.default_flags();
            assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS), "{:?}", op);
            assert!(!op.is_pseudo(), "{:?}", op);
        }
    }

    #[test]
    fn sse2_packed_compat_opcodes_map_to_pipeline_opcodes() {
        for (packed, pipeline) in [
            (X86Sse2PackedOpcode::Pand, X86Opcode::Pand),
            (X86Sse2PackedOpcode::Pandn, X86Opcode::Pandn),
            (X86Sse2PackedOpcode::Por, X86Opcode::Por),
            (X86Sse2PackedOpcode::Pxor, X86Opcode::Pxor),
            (X86Sse2PackedOpcode::Pcmpeqb, X86Opcode::Pcmpeqb),
            (X86Sse2PackedOpcode::Pcmpeqw, X86Opcode::Pcmpeqw),
            (X86Sse2PackedOpcode::Pcmpgtb, X86Opcode::Pcmpgtb),
            (X86Sse2PackedOpcode::Pcmpgtw, X86Opcode::Pcmpgtw),
            (X86Sse2PackedOpcode::Pcmpeqd, X86Opcode::Pcmpeqd),
            (X86Sse2PackedOpcode::Pshufd, X86Opcode::Pshufd),
            (X86Sse2PackedOpcode::Pmovmskb, X86Opcode::Pmovmskb),
            (X86Sse2PackedOpcode::MovdqaRR, X86Opcode::MovdqaRR),
            (X86Sse2PackedOpcode::Pcmpgtd, X86Opcode::Pcmpgtd),
            (X86Sse2PackedOpcode::Paddb, X86Opcode::Paddb),
            (X86Sse2PackedOpcode::Paddw, X86Opcode::Paddw),
            (X86Sse2PackedOpcode::Paddd, X86Opcode::Paddd),
            (X86Sse2PackedOpcode::Psubb, X86Opcode::Psubb),
            (X86Sse2PackedOpcode::Psubw, X86Opcode::Psubw),
            (X86Sse2PackedOpcode::Psubd, X86Opcode::Psubd),
            (X86Sse2PackedOpcode::Pmullw, X86Opcode::Pmullw),
            (X86Sse2PackedOpcode::Pcmpeqq, X86Opcode::Pcmpeqq),
            (X86Sse2PackedOpcode::Pcmpgtq, X86Opcode::Pcmpgtq),
            (X86Sse2PackedOpcode::Punpcklbw, X86Opcode::Punpcklbw),
            (X86Sse2PackedOpcode::Punpckldq, X86Opcode::Punpckldq),
            (X86Sse2PackedOpcode::Packuswb, X86Opcode::Packuswb),
            (X86Sse2PackedOpcode::Punpckhbw, X86Opcode::Punpckhbw),
            (X86Sse2PackedOpcode::Punpcklqdq, X86Opcode::Punpcklqdq),
            (X86Sse2PackedOpcode::Paddq, X86Opcode::Paddq),
            (X86Sse2PackedOpcode::Psubq, X86Opcode::Psubq),
            (X86Sse2PackedOpcode::Pmuludq, X86Opcode::Pmuludq),
            (X86Sse2PackedOpcode::Pslld, X86Opcode::Pslld),
            (X86Sse2PackedOpcode::Psrld, X86Opcode::Psrld),
            (X86Sse2PackedOpcode::Psrad, X86Opcode::Psrad),
            (X86Sse2PackedOpcode::Psllq, X86Opcode::Psllq),
            (X86Sse2PackedOpcode::Psrlq, X86Opcode::Psrlq),
        ] {
            assert_eq!(packed.to_x86_opcode(), pipeline);
            assert_eq!(X86Opcode::from(packed), pipeline);
        }
    }

    #[test]
    fn ud2_has_trap_flags_and_is_real_instruction() {
        let flags = X86Opcode::Ud2.default_flags();
        assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS));
        assert!(flags.contains(InstFlags::IS_TERMINATOR));
        assert!(!X86Opcode::Ud2.is_pseudo());
    }

    #[test]
    fn nopmulti_has_empty_flags() {
        let flags = X86Opcode::NopMulti.default_flags();
        assert!(flags.is_empty());
        // NopMulti is NOT pseudo (it has a real hardware encoding)
        assert!(!X86Opcode::NopMulti.is_pseudo());
    }

    #[test]
    fn pseudo_opcodes() {
        assert!(X86Opcode::Phi.is_pseudo());
        assert!(X86Opcode::StackAlloc.is_pseudo());
        assert!(X86Opcode::Nop.is_pseudo());
        assert!(!X86Opcode::AddRR.is_pseudo());
        assert!(!X86Opcode::NopMulti.is_pseudo());
    }

    #[test]
    fn is_phi_method() {
        assert!(X86Opcode::Phi.is_phi());
        assert!(!X86Opcode::Nop.is_phi());
    }

    // ---- X86CondCode tests ----

    #[test]
    fn cond_code_encoding() {
        assert_eq!(X86CondCode::O.encoding(), 0x0);
        assert_eq!(X86CondCode::NO.encoding(), 0x1);
        assert_eq!(X86CondCode::B.encoding(), 0x2);
        assert_eq!(X86CondCode::AE.encoding(), 0x3);
        assert_eq!(X86CondCode::E.encoding(), 0x4);
        assert_eq!(X86CondCode::NE.encoding(), 0x5);
        assert_eq!(X86CondCode::BE.encoding(), 0x6);
        assert_eq!(X86CondCode::A.encoding(), 0x7);
        assert_eq!(X86CondCode::S.encoding(), 0x8);
        assert_eq!(X86CondCode::NS.encoding(), 0x9);
        assert_eq!(X86CondCode::P.encoding(), 0xA);
        assert_eq!(X86CondCode::NP.encoding(), 0xB);
        assert_eq!(X86CondCode::L.encoding(), 0xC);
        assert_eq!(X86CondCode::GE.encoding(), 0xD);
        assert_eq!(X86CondCode::LE.encoding(), 0xE);
        assert_eq!(X86CondCode::G.encoding(), 0xF);
    }

    #[test]
    fn cond_code_invert() {
        assert_eq!(X86CondCode::O.invert(), X86CondCode::NO);
        assert_eq!(X86CondCode::NO.invert(), X86CondCode::O);
        assert_eq!(X86CondCode::B.invert(), X86CondCode::AE);
        assert_eq!(X86CondCode::AE.invert(), X86CondCode::B);
        assert_eq!(X86CondCode::E.invert(), X86CondCode::NE);
        assert_eq!(X86CondCode::NE.invert(), X86CondCode::E);
        assert_eq!(X86CondCode::L.invert(), X86CondCode::GE);
        assert_eq!(X86CondCode::GE.invert(), X86CondCode::L);
        assert_eq!(X86CondCode::LE.invert(), X86CondCode::G);
        assert_eq!(X86CondCode::G.invert(), X86CondCode::LE);
    }

    #[test]
    fn cond_code_double_invert_is_identity() {
        let all = [
            X86CondCode::O,
            X86CondCode::NO,
            X86CondCode::B,
            X86CondCode::AE,
            X86CondCode::E,
            X86CondCode::NE,
            X86CondCode::BE,
            X86CondCode::A,
            X86CondCode::S,
            X86CondCode::NS,
            X86CondCode::P,
            X86CondCode::NP,
            X86CondCode::L,
            X86CondCode::GE,
            X86CondCode::LE,
            X86CondCode::G,
        ];
        for cc in &all {
            assert_eq!(
                cc.invert().invert(),
                *cc,
                "double invert identity for {:?}",
                cc
            );
        }
    }

    #[test]
    fn cond_code_signed_unsigned() {
        assert!(X86CondCode::L.is_signed());
        assert!(X86CondCode::GE.is_signed());
        assert!(X86CondCode::LE.is_signed());
        assert!(X86CondCode::G.is_signed());
        assert!(!X86CondCode::E.is_signed());
        assert!(!X86CondCode::B.is_signed());

        assert!(X86CondCode::B.is_unsigned());
        assert!(X86CondCode::AE.is_unsigned());
        assert!(X86CondCode::BE.is_unsigned());
        assert!(X86CondCode::A.is_unsigned());
        assert!(!X86CondCode::L.is_unsigned());
        assert!(!X86CondCode::E.is_unsigned());
    }

    #[test]
    fn cond_code_display() {
        assert_eq!(format!("{}", X86CondCode::E), "e");
        assert_eq!(format!("{}", X86CondCode::NE), "ne");
        assert_eq!(format!("{}", X86CondCode::G), "g");
    }
}
