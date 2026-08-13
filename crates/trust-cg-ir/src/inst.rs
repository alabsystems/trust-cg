// trust-cg-ir - Shared machine IR model
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Machine instruction types: AArch64Opcode, InstFlags, MachInst.

use crate::operand::MachOperand;
use crate::regs::PReg;

// ---------------------------------------------------------------------------
// AArch64Opcode
// ---------------------------------------------------------------------------

/// AArch64 instruction opcodes.
///
/// Naming convention: `<mnemonic><operand_kinds>` where RR = register-register,
/// RI = register-immediate. Pseudo-instructions have no hardware encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AArch64Opcode {
    // -- Arithmetic --
    AddRR,
    AddRI,
    /// ADD (immediate, shift by 12) — `Xd = Xn + (imm12 << 12)`.
    /// Operands: `[PReg(Rd), PReg(Rn), Imm(imm12)]`.
    /// Used by the TLS local-exec sequence for the hi12 offset.
    AddRIShift12,
    SubRR,
    SubRI,
    MulRR,
    /// MSUB Rd, Rn, Rm, Ra — multiply-subtract: Rd = Ra - Rn * Rm.
    /// When Ra=XZR, this is MNEG Rd, Rn, Rm.
    Msub,
    /// SMULL Xd, Wn, Wm — signed multiply long: Xd = sext(Wn) * sext(Wm).
    Smull,
    /// UMULL Xd, Wn, Wm — unsigned multiply long: Xd = zext(Wn) * zext(Wm).
    Umull,
    SDiv,
    UDiv,
    Neg,

    // -- Logical --
    AndRR,
    AndRI,
    OrrRR,
    OrrRI,
    EorRR,
    EorRI,
    /// EOR Rd, Rn, Rm, ROR #amount — exclusive-OR with a ROTATE-RIGHT-shifted
    /// second source (the logical shifted-register form, `shift`=ROR=0b11).
    ///
    /// Semantics: `Rd = Rn ^ ror(Rm, amount)`. The SHIFTED operand is `Rm`
    /// (the ARM `Rm, ROR #amount`); `Rn` is the un-shifted operand. Because the
    /// shift applies to only one source, this is NOT commutative (unlike
    /// [`Self::EorRR`]).
    ///
    /// MINIMAL, HONEST SURFACE: only the ROR shift kind is modeled (the one the
    /// rotate-fusion peephole produces), at both the W (32-bit) and X (64-bit)
    /// register forms. LSL/LSR/ASR shifted logical forms are deliberately NOT
    /// added — nothing emits them, and a per-shift-kind opcode explosion would be
    /// unproven surface. The shift kind is therefore implicit in the opcode
    /// rather than an operand.
    ///
    /// Emitted by the EOR-rotate fusion peephole (`trust_cg_opt::eor_rotate_fuse`)
    /// which collapses `t = RorRI(s, k); d = EorRR(x, t)` (single-use `t`) into a
    /// single `d = EorRRShift(x, s, k)` — the unfinished half of the 8c9e922
    /// rotate arc (salsa20's ARX `x[b] ^= ROTL(x[c]+x[d], r)`).
    ///
    /// Operands: `[dst, Rn (un-shifted), Rm (rotated source), Imm(ror_amount)]`,
    /// `ror_amount` in `[1, width)`.
    EorRRShift,
    /// ADD Rd, Rn, Rm, LSL #k — add with a LOGICAL-SHIFT-LEFT-shifted second
    /// source (the arithmetic shifted-register form, `shift`=LSL=0b00).
    ///
    /// Semantics: `Rd = Rn + (Rm << k)` (wrapping). The SHIFTED operand is `Rm`
    /// (the ARM `Rm, LSL #k`); `Rn` is the un-shifted base. Because the shift
    /// applies to only one source, this is the sibling of [`Self::EorRRShift`]
    /// (LSL here, ROR there). ADD is commutative in intent, but the shift binds
    /// to `Rm` only, so the fusion producer must place the shifted source in the
    /// `Rm` slot.
    ///
    /// MINIMAL, HONEST SURFACE: only the LSL shift kind is modeled (the one the
    /// shift-add fusion peephole produces), at both the W (32-bit) and X (64-bit)
    /// register forms. The shift kind is implicit in the opcode rather than an
    /// operand (no per-shift-kind opcode explosion), mirroring `EorRRShift`.
    ///
    /// Emitted by the shift-ALU fusion peephole (`trust_cg_opt::shift_alu_fuse`)
    /// which collapses `t = LslRI(s, k); d = AddRR(x, t)` (single-use `t`) into a
    /// single `d = AddRRShift(x, s, k)` — the missing shifted-register ADD the
    /// `mul_shift_reduce` strength-reduction (LslRI + AddRR) and any explicit
    /// `y + (x << k)` want.
    ///
    /// Operands: `[dst, Rn (un-shifted base), Rm (shifted source), Imm(k)]`,
    /// `k` in `[1, width)`.
    AddRRShift,
    /// SUB Rd, Rn, Rm, LSL #k — subtract a LOGICAL-SHIFT-LEFT-shifted second
    /// source (the arithmetic shifted-register form, `shift`=LSL=0b00).
    ///
    /// Semantics: `Rd = Rn - (Rm << k)` (wrapping). The SHIFTED operand is `Rm`
    /// (the ARM `Rm, LSL #k`, the subtrahend); `Rn` is the un-shifted minuend.
    /// SUB is NOT commutative — `SUB Rd, Rn, Rm, LSL #k` = `Rn - (Rm << k)`, so
    /// the shift can ONLY sit on the subtrahend. The fusion producer therefore
    /// fuses a shifted temp ONLY when it feeds the subtrahend (`Rm`) position,
    /// never the minuend.
    ///
    /// MINIMAL, HONEST SURFACE: only the LSL shift kind is modeled, at both W and
    /// X forms; the shift kind is implicit in the opcode (see [`Self::AddRRShift`]).
    ///
    /// Emitted by the shift-ALU fusion peephole (`trust_cg_opt::shift_alu_fuse`)
    /// which collapses `t = LslRI(s, k); d = SubRR(x, t)` (single-use `t`, `t` in
    /// the subtrahend slot) into a single `d = SubRRShift(x, s, k)`.
    ///
    /// Operands: `[dst, Rn (minuend), Rm (shifted subtrahend), Imm(k)]`, `k` in
    /// `[1, width)`.
    SubRRShift,
    /// EOR Rd, Rn, Rm, LSL #k — exclusive-or with a LOGICAL-SHIFT-LEFT-shifted
    /// second source (`shift`=LSL=0b00).
    ///
    /// Semantics: `Rd = Rn ^ (Rm << k)`. The SHIFTED operand is `Rm`; `Rn` is the
    /// un-shifted source. EOR is commutative in intent, but the shift binds to
    /// `Rm` only, so the fusion producer must place the shifted source in `Rm`.
    ///
    /// The LOGICAL sibling of [`Self::AddRRShift`] (ADD+LSL) and the LSL
    /// counterpart of [`Self::EorRRShift`] (EOR+ROR). Together with
    /// [`Self::EorRRLsr`] this closes the xorshift / bit-manipulation shape
    /// `x ^= x << k` / `x ^= x >> k`, which AArch64 encodes as ONE
    /// shifted-register EOR but which the backend otherwise emits as a separate
    /// `LslRI`/`LsrRI` plus `EorRR` — roughly doubling the hot loop of
    /// xorshift-class kernels (measured 1.99x vs LLVM on `p1_xorshift`).
    ///
    /// Credited via `MachineSideProvenance::Reconstructed`: the verifier rebuilds
    /// `Rn ^ (Rm << k)` from the REAL emitted opcode and operand positions, so a
    /// wrong shift kind, a wrong amount, or swapped `Rn`/`Rm` REFUTES.
    ///
    /// Operands: `[dst, Rn (un-shifted), Rm (shifted source), Imm(k)]`, `k` in
    /// `[1, width)`.
    EorRRLsl,
    /// EOR Rd, Rn, Rm, LSR #k — exclusive-or with a LOGICAL-SHIFT-RIGHT-shifted
    /// second source (`shift`=LSR=0b01).
    ///
    /// Semantics: `Rd = Rn ^ (Rm >>u k)` — LOGICAL (zero-filling) shift right.
    /// ASR is a DISTINCT shift kind and is deliberately not modeled here.
    /// Operand roles, provenance, and minimal-surface policy are exactly
    /// [`Self::EorRRLsl`]'s.
    ///
    /// Operands: `[dst, Rn (un-shifted), Rm (shifted source), Imm(k)]`, `k` in
    /// `[1, width)`.
    EorRRLsr,
    /// ADD Rd, Rn, Rm, LSR #k — add with a LOGICAL-SHIFT-RIGHT-shifted second
    /// source (the arithmetic shifted-register form, `shift`=LSR=0b01).
    ///
    /// Semantics: `Rd = Rn + (Rm >>u k)` (wrapping add, zero-fill right shift).
    /// The SHIFTED operand is `Rm` (the ARM `Rm, LSR #k`); `Rn` is the
    /// un-shifted base. Because the shift applies to only one source, the fusion
    /// producer must place the shifted source in the `Rm` slot (ADD commutes in
    /// value, so either add operand may be fused there).
    ///
    /// MINIMAL, HONEST SURFACE: only the ADD+LSR combination is modeled (the one
    /// the shift-ALU fusion peephole produces), at both the W (32-bit) and X
    /// (64-bit) register forms. The shift kind is implicit in the opcode rather
    /// than an operand (no per-shift-kind opcode explosion), mirroring
    /// [`Self::AddRRShift`] (LSL) and [`Self::EorRRShift`] (ROR). No SUB+LSR
    /// sibling is added — nothing emits it.
    ///
    /// Emitted by the shift-ALU fusion peephole (`trust_cg_opt::shift_alu_fuse`)
    /// which collapses `t = LsrRI(s, k); d = AddRR(x, t)` (single-use `t`) into a
    /// single `d = AddRRShiftLsr(x, s, k)` — the one-instruction sign-bit
    /// correction of the srem/sdiv-by-constant magic sequence
    /// (`add w8, w8, w9, lsr #31`) and the udiv magic add-back
    /// (`add w8, w9, w8, lsr #1`), exactly what clang emits at those sites.
    ///
    /// Operands: `[dst, Rn (un-shifted base), Rm (shifted source), Imm(k)]`,
    /// `k` in `[1, width)`.
    AddRRShiftLsr,
    /// ORN Rd, Rn, Rm — bitwise OR-NOT.
    /// When Rn=XZR, this is MVN (bitwise NOT).
    OrnRR,
    /// BIC Rd, Rn, Rm — bitwise AND-NOT (bit clear).
    BicRR,

    // -- Shifts --
    LslRR,
    LsrRR,
    AsrRR,
    LslRI,
    LsrRI,
    AsrRI,
    /// ROR Rd, Rn, #shift — rotate right by immediate.
    /// Encoded as the AArch64 EXTR alias with both sources equal.
    /// Operands: `[dst, src, Imm(shift)]`.
    RorRI,
    /// RBIT Rd, Rn — reverse bits in a 32-bit or 64-bit GPR.
    /// Operands: `[dst, src]`.
    Rbit,

    // -- Compare / conditional select --
    CmpRR,
    CmpRI,
    Tst,
    /// CSEL Xd, Xn, Xm, cond — conditional select.
    /// Operands: [dst, true_src, false_src, Imm(cond_code_encoding)].
    Csel,
    /// CSINC Xd, Xn, Xm, cond — conditional select increment.
    /// Semantically: Xd = cond ? Xn : (Xm + 1).
    Csinc,
    /// CSINV Xd, Xn, Xm, cond — conditional select invert.
    /// Semantically: Xd = cond ? Xn : ~Xm.
    Csinv,
    /// CSNEG Xd, Xn, Xm, cond — conditional select negate.
    /// Semantically: Xd = cond ? Xn : -Xm.
    Csneg,
    /// FCSEL Sd/Dd, Sn/Dn, Sm/Dm, cond — scalar floating-point conditional
    /// select. Operands: `[dst, true_src, false_src, Imm(cond_code_encoding)]`.
    ///
    /// Semantics: `Rd = cond ? Rn : Rm`, copied BIT-FOR-BIT. This is a
    /// FPR-domain mux — all three registers are scalar FPRs (S for f32, D for
    /// f64). The select is BIT-PRESERVING: the chosen source is written verbatim
    /// with NO floating-point arithmetic, so NaN payloads, signaling NaNs,
    /// signed zeros and denormals pass through untouched (there is no
    /// canonicalization).
    ///
    /// The `ftype` (S vs D) is implicit in the destination register class (the
    /// encoder derives it, S=ftype 00 / D=ftype 01); only the F32 and F64 forms
    /// are modeled. The f16 form (ftype 11, FEAT_FP16) is deliberately EXCLUDED
    /// — the enum's `Fpr16` selects still lower through the GPR CSEL fallback.
    ///
    /// Emitted by the AArch64 ISel FP-`Select` path (`select_csel`), replacing
    /// the old FMOV(FPR->GPR)x2 + CMP + integer CSEL + FMOV(GPR->FPR) cross-bank
    /// sequence with a single FPR-domain `CMP cond,#0` + `FCSEL dst,t,f,cc`. The
    /// GPR Csel encoder has NO bank check, so an FPR `Csel` would silently encode
    /// as a CSEL on the collided GPRs (the audit-era P0 the FP route fail-closed
    /// around); this opcode has a dedicated fail-closed FPR encoder instead.
    FcselRR,

    // -- Move --
    MovR,
    MovI,
    Movz,
    /// MOVN: move wide with NOT (for small negative constants).
    Movn,
    Movk,
    /// FMOV immediate to FPR (e.g., FMOV Sd, #imm8 or FMOV Dd, #imm8).
    FmovImm,

    // -- Memory (immediate offset) --
    LdrRI,
    StrRI,
    /// LDR with pre-index writeback: LDR Xt, [Xn|SP, #imm]!
    /// The base register is updated before the load.
    /// Operands: [PReg(Rt), PReg(Rn)|Special(SP), Imm(offset)]
    LdrPreIndex,
    /// STR with pre-index writeback: STR Xt, [Xn|SP, #imm]!
    /// The base register is updated before the store.
    /// Operands: [PReg(Rt), PReg(Rn)|Special(SP), Imm(offset)]
    StrPreIndex,
    /// LDR with post-index writeback: LDR Xt, [Xn|SP], #imm
    /// The base register is updated after the load.
    /// Operands: [PReg(Rt), PReg(Rn)|Special(SP), Imm(offset)]
    LdrPostIndex,
    /// STR with post-index writeback: STR Xt, [Xn|SP], #imm
    /// The base register is updated after the store.
    /// Operands: [PReg(Rt), PReg(Rn)|Special(SP), Imm(offset)]
    StrPostIndex,
    /// LDRB (unsigned offset): load byte, zero-extend to 32-bit.
    /// Operands: [PReg(Rt), PReg(Rn)|Special(SP), Imm(offset)]
    LdrbRI,
    /// LDRH (unsigned offset): load halfword, zero-extend to 32-bit.
    /// Operands: [PReg(Rt), PReg(Rn)|Special(SP), Imm(offset)]
    LdrhRI,
    /// LDRSB (unsigned offset): load byte, sign-extend to 32-bit.
    /// Operands: [PReg(Rt), PReg(Rn)|Special(SP), Imm(offset)]
    LdrsbRI,
    /// LDRSH (unsigned offset): load halfword, sign-extend to 32-bit.
    /// Operands: [PReg(Rt), PReg(Rn)|Special(SP), Imm(offset)]
    LdrshRI,
    /// STRB (unsigned offset): store byte (truncating).
    /// Operands: [PReg(Rt), PReg(Rn)|Special(SP), Imm(offset)]
    StrbRI,
    /// STRH (unsigned offset): store halfword (truncating).
    /// Operands: [PReg(Rt), PReg(Rn)|Special(SP), Imm(offset)]
    StrhRI,
    LdrLiteral,
    LdpRI,
    StpRI,
    /// STP with pre-index writeback: STP Rt, Rt2, [Rn, #imm]!
    /// The base register is updated before the store.
    /// Operands: [PReg(Rt), PReg(Rt2), Special(SP)|PReg(Rn), Imm(offset)]
    StpPreIndex,
    /// LDP with post-index writeback: LDP Rt, Rt2, [Rn], #imm
    /// The base register is updated after the load.
    /// Operands: [PReg(Rt), PReg(Rt2), Special(SP)|PReg(Rn), Imm(offset)]
    LdpPostIndex,

    // -- Memory (register offset) --
    /// LDR Wt, [Xn, Xm] — load 32-bit, base + register offset.
    LdrRO,
    /// STR Wt, [Xn, Xm] — store 32-bit/64-bit, base + register offset.
    StrRO,
    /// LDRB Wt, [Xn, Xm{, extend}] — load byte (zero-extend to 32), base +
    /// register offset. Narrow sibling of `LdrRO`; the transfer register is a
    /// W register but the access width is 1 byte, taken from the OPCODE (not
    /// the transfer class). Byte accesses use no shift (S=0) since log2(1)=0.
    /// Operands: [Wt, Xn, Xm, Imm((option<<1)|S)].
    LdrbRO,
    /// LDRH Wt, [Xn, Xm{, extend}] — load halfword (zero-extend to 32), base +
    /// register offset. Narrow sibling of `LdrRO`; the access width is 2 bytes,
    /// taken from the OPCODE. S=1 shifts the index by log2(2)=1.
    /// Operands: [Wt, Xn, Xm, Imm((option<<1)|S)].
    LdrhRO,

    // -- Memory (GOT / TLV) --
    /// LDR Xd, [Xn, #got_pageoff] — load from GOT slot.
    LdrGot,
    /// LDR Xd, [Xn, #tlvp_pageoff] — load from TLV descriptor.
    LdrTlvp,

    // -- Branch --
    B,
    BCond,
    Cbz,
    Cbnz,
    Tbz,
    Tbnz,
    Br,
    Bl,
    Blr,
    Ret,

    // -- Conditional --
    /// CSET Xd/Wd, cond — conditional set (materialize condition as 0/1).
    /// Encoded as CSINC Xd, XZR, XZR, invert(cond) per ARM ARM C6.2.70.
    /// Operands: [dst, Imm(cond_code_encoding)].
    /// Semantically: Xd = (cond) ? 1 : 0.
    CSet,

    // -- Extension --
    Sxtw,
    Uxtw,
    Sxtb,
    Sxth,
    /// UXTB Wd, Wn — zero-extend byte to 32-bit (alias: AND Wd, Wn, #0xFF).
    /// Encoded as UBFM Wd, Wn, #0, #7.
    Uxtb,
    /// UXTH Wd, Wn — zero-extend halfword to 32-bit (alias: AND Wd, Wn, #0xFFFF).
    /// Encoded as UBFM Wd, Wn, #0, #15.
    Uxth,

    // -- Bitfield operations --
    /// UBFM Rd, Rn, #immr, #imms — unsigned bitfield move.
    /// Aliases: LSL/LSR (imm), UBFX, UXTB, UXTH.
    Ubfm,
    /// SBFM Rd, Rn, #immr, #imms — signed bitfield move.
    /// Aliases: ASR (imm), SBFX, SXTB, SXTH, SXTW.
    Sbfm,
    /// BFM Rd, Rn, #immr, #imms — bitfield move (insert).
    /// Aliases: BFI, BFXIL.
    Bfm,

    // -- Floating-point --
    FaddRR,
    FsubRR,
    FmulRR,
    FdivRR,
    /// FMADD Sd/Dd, Sn, Sm, Sa — scalar FUSED multiply-add: `Fd = Fa + Fn*Fm`
    /// with a SINGLE rounding of the exact product-plus-addend (NOT round twice).
    /// Encoded in the FP data-processing 3-source family (o1=0, o0=0). This is
    /// the initial lowering of both strict `llvm.fma.f{32,64}` and
    /// fusion-licensed `llvm.fmuladd.f{32,64}`. The
    /// [`InstFlags::FMULADD_MAY_UNFUSE`] semantic bit distinguishes the latter;
    /// an unmarked instruction must retain fused single-rounding semantics.
    /// Operands: [Rd, Rn, Rm, Ra] — 4 FP registers (fp width from the Rd class).
    FmaddRR,
    /// FMINNM Dd, Dn, Dm — IEEE minNum scalar FP min (Rust `f{32,64}::min`).
    FminnmRR,
    /// FMAXNM Dd, Dn, Dm — IEEE maxNum scalar FP max (Rust `f{32,64}::max`).
    FmaxnmRR,
    /// FNEG Dd, Dn — floating-point negate.
    FnegRR,
    /// FABS Dd, Dn — floating-point absolute value.
    FabsRR,
    /// FSQRT Dd, Dn — floating-point square root.
    FsqrtRR,
    /// FRINTM Dd, Dn — round to integral toward -inf (floor).
    FrintmRR,
    /// FRINTP Dd, Dn — round to integral toward +inf (ceil).
    FrintpRR,
    /// FRINTZ Dd, Dn — round to integral toward zero (trunc).
    FrintzRR,
    Fcmp,
    FcvtzsRR,
    /// FCVTZU: float-to-unsigned-integer conversion (round toward zero).
    FcvtzuRR,
    ScvtfRR,
    /// UCVTF: unsigned-integer-to-float conversion.
    UcvtfRR,
    /// FCVT Dd, Sn: float precision widen (f32 -> f64).
    FcvtSD,
    /// FCVT Ss, Dn: float precision narrow (f64 -> f32).
    FcvtDS,
    /// FCVT Sd, Hn: float precision widen (f16 -> f32).
    FcvtHS,
    /// FCVT Dd, Hn: float precision widen (f16 -> f64).
    FcvtHD,
    /// FCVT Hd, Sn: float precision narrow (f32 -> f16).
    FcvtSH,
    /// FCVT Hd, Dn: float precision narrow (f64 -> f16).
    FcvtDH,
    /// FMOV between GPR and FPR (e.g., FMOV Sd, Wn or FMOV Dd, Xn).
    FmovGprFpr,
    /// FMOV between FPR and GPR (e.g., FMOV Wn, Sd or FMOV Xn, Dd).
    FmovFprGpr,
    /// FMOV between FPR registers (e.g., FMOV Dd, Dn or FMOV Ss, Sn).
    /// Encoded as FP data-processing 1-source with opcode=00 (FmovReg).
    /// Operands: [Rd, Rn] where both are FPR.
    FmovFprFpr,

    // -- NEON SIMD (vector) --
    /// ADD Vd.T, Vn.T, Vm.T — integer vector add.
    /// Operands: [Vd, Vn, Vm, Imm(arrangement)]
    NeonAddV,
    /// SUB Vd.T, Vn.T, Vm.T — integer vector subtract.
    NeonSubV,
    /// MUL Vd.T, Vn.T, Vm.T — integer vector multiply.
    NeonMulV,
    /// SMAX Vd.T, Vn.T, Vm.T — signed integer vector maximum (per lane).
    /// Operands: [Vd, Vn, Vm, Imm(arrangement)]. Distinct from the across-lane
    /// horizontal reduce `NeonUmaxv` (note the lowercase-`v`): this is the
    /// three-register-same per-lane op.
    NeonSmaxV,
    /// SMIN Vd.T, Vn.T, Vm.T — signed integer vector minimum (per lane).
    /// Operands: [Vd, Vn, Vm, Imm(arrangement)].
    NeonSminV,
    /// UMAX Vd.T, Vn.T, Vm.T — unsigned integer vector maximum (per lane).
    /// Operands: [Vd, Vn, Vm, Imm(arrangement)].
    NeonUmaxV,
    /// UMIN Vd.T, Vn.T, Vm.T — unsigned integer vector minimum (per lane).
    /// Operands: [Vd, Vn, Vm, Imm(arrangement)].
    NeonUminV,
    /// FADD Vd.T, Vn.T, Vm.T — FP vector add.
    NeonFaddV,
    /// FSUB Vd.T, Vn.T, Vm.T — FP vector subtract.
    NeonFsubV,
    /// FMUL Vd.T, Vn.T, Vm.T — FP vector multiply.
    NeonFmulV,
    /// FDIV Vd.T, Vn.T, Vm.T — FP vector divide.
    NeonFdivV,
    /// FCMGT Vd.T, Vn.T, Vm.T — FP vector compare greater-than (ordered):
    /// per lane all-ones iff `Vn[i] > Vm[i]`, else zero (a NaN operand => 0,
    /// matching the scalar `FCMP; CSET GT` idiom's unordered behavior).
    /// Operands: [Vd, Vn, Vm, Imm(fp-arrangement 0=2S, 1=4S, 2=2D)].
    NeonFcmgtV,
    /// AND Vd.T, Vn.T, Vm.T — vector bitwise AND.
    NeonAndV,
    /// ORR Vd.T, Vn.T, Vm.T — vector bitwise OR.
    NeonOrrV,
    /// EOR Vd.T, Vn.T, Vm.T — vector bitwise XOR.
    NeonEorV,
    /// BIC Vd.T, Vn.T, Vm.T — vector bitwise AND-NOT.
    NeonBicV,
    /// NOT Vd.T, Vn.T — vector bitwise NOT.
    NeonNotV,
    /// RBIT Vd.{8B,16B}, Vn.{8B,16B} — reverse bits in each byte lane.
    /// Operands: [Vd, Vn, Imm(arrangement)] where arrangement is 8B or 16B.
    NeonRbitV,
    /// REV32 Vd.{8B,16B}, Vn.{8B,16B} — reverse bytes within each 32-bit lane.
    /// Operands: [Vd, Vn, Imm(arrangement)] where arrangement is 8B or 16B.
    NeonRev32V,
    /// REV64 Vd.{8B,16B}, Vn.{8B,16B} — reverse bytes within each 64-bit lane.
    /// Operands: [Vd, Vn, Imm(arrangement)] where arrangement is 8B or 16B.
    NeonRev64V,
    /// CMEQ Vd.T, Vn.T, Vm.T — vector compare equal.
    NeonCmeqV,
    /// CMGT Vd.T, Vn.T, Vm.T — vector compare greater than (signed).
    NeonCmgtV,
    /// CMGE Vd.T, Vn.T, Vm.T — vector compare greater or equal (signed).
    NeonCmgeV,
    /// CMHI Vd.T, Vn.T, Vm.T — vector compare greater than (unsigned).
    NeonCmhiV,
    /// CMHS Vd.T, Vn.T, Vm.T — vector compare greater or same (unsigned).
    NeonCmhsV,
    /// UMAXV Sd, Vn.4S — unsigned horizontal max across four i32 lanes.
    /// Used as horizontal-any over `CMEQ.4S` masks.
    /// Operands: [Sd, Vn, Imm(arrangement)] where arrangement must be 4S.
    NeonUmaxv,
    /// ADDP Dd, Vn.2D — pairwise add across two i64 lanes into a scalar D reg.
    /// Used to bridge vector i64 lanes into scalar subtract reductions.
    /// Operands: [Dd, Vn, Imm(arrangement)] where arrangement must be 2D.
    NeonAddpScalar,
    /// DUP Vd.T, Vn.Ts[lane] — duplicate element to all lanes.
    /// Operands: [Vd, Vn, Imm(lane), Imm(element_size)]
    NeonDupElem,
    /// DUP Vd.T, Xn/Wn — duplicate GPR to all vector lanes.
    /// Operands: [Vd, Rn, Imm(element_size)]
    NeonDupGen,
    /// INS Vd.Ts[lane], Xn/Wn — insert GPR into vector lane.
    /// Operands: [Vd, Rn, Imm(lane), Imm(element_size)]
    NeonInsGen,
    /// UMOV Wd/Xd, Vn.S/D[lane] — extract vector lane into a GPR.
    /// Operands: [Wd/Xd, Vn, Imm(lane), Imm(element_size)] where element_size is S or D.
    NeonUmovGen,
    /// MOVI Vd.T, #imm8 — move immediate to vector (byte form).
    /// Operands: [Vd, Imm(imm8)]
    NeonMovi,
    /// LD1 {Vt.T}, [Xn], #imm — SIMD load 1 register, post-index.
    /// Operands: [Vt, Xn, Imm(arrangement)]
    NeonLd1Post,
    /// LDP Qt1, Qt2, [Xn], #imm — SIMD&FP load PAIR of 128-bit Q registers,
    /// post-index (one instruction, 32 bytes: `Qt1 = [Xn]`, `Qt2 = [Xn+16]`,
    /// then `Xn += imm`). Bit-identical (little-endian) to two consecutive
    /// `LD1 {V.4S}, [Xn], #16` from the same running pointer; emitted by the
    /// NEON reduction/map vectorizers so the hot vector loops load 32 bytes
    /// per instruction like clang's `ldp q, q` loops. The encoder emits the
    /// SIMD&FP form (V=1, opc=0b10) and REJECTS non-Fpr128 data operands —
    /// never the GPR form.
    /// Operands: [Vt1, Vt2, Xn, Imm(post-index byte offset, multiple of 16)]
    NeonLdpQPost,
    /// ST1 {Vt.T}, [Xn], #imm — SIMD store 1 register, post-index.
    /// Operands: [Vt, Xn, Imm(arrangement)]
    NeonSt1Post,
    /// STP Qt1, Qt2, [Xn], #imm — SIMD&FP store PAIR of 128-bit Q registers,
    /// post-index (one instruction, 32 bytes: `[Xn] = Qt1`, `[Xn+16] = Qt2`,
    /// then `Xn += imm`). Bit-identical (little-endian) to two consecutive
    /// `ST1 {V.4S}, [Xn], #16` of the same running pointer; emitted by the NEON
    /// map/stencil/fmap vectorizers so the hot vector loops store 32 bytes per
    /// instruction like clang's `stp q, q` loops (the STORE sibling of
    /// [`Self::NeonLdpQPost`]). The encoder emits the SIMD&FP form (V=1,
    /// opc=0b10) and REJECTS non-Fpr128 data operands — never the GPR form.
    /// Operands: [Vt1, Vt2, Xn, Imm(post-index byte offset, multiple of 16)]
    NeonStpQPost,
    /// CNT Vd.T, Vn.T — per-byte population count: each output byte lane holds the
    /// number of set bits in the corresponding input byte.
    /// Operands: [Vd, Vn, Imm(arrangement)] where arrangement is 8B or 16B.
    NeonCntV,
    /// UADDLP Vd.Ta, Vn.Tb — unsigned add long pairwise: each output lane is the
    /// sum of two adjacent zero-extended input lanes (`Ta` is the widened,
    /// half-lane-count arrangement of the input `Tb`). Paired with `NeonCntV` to
    /// fold per-byte popcounts up into per-i32-lane popcounts (`.16B→.8H` then
    /// `.8H→.4S`).
    /// Operands: [Vd, Vn, Imm(input_arrangement)] where input is 16B or 8H.
    NeonUaddlpV,
    /// SADDLP Vd.Ta, Vn.Tb — signed add long pairwise: each output lane is the
    /// sum of two adjacent SIGN-extended input lanes (`Ta` is the widened,
    /// half-lane-count arrangement of the input `Tb`). The signed sibling of
    /// [`Self::NeonUaddlpV`]; emitted by the widening `sext(i8/i16) → i32`
    /// array-reduction lowering (`.16B→.8H` then `.8H→.4S` for i8; `.8H→.4S`
    /// alone for i16).
    /// Operands: [Vd, Vn, Imm(input_arrangement)] where input is 16B or 8H.
    NeonSaddlpV,
    /// ABS Vd.T, Vn.T — per-lane signed absolute value: each output lane holds the
    /// two's-complement absolute value of the corresponding input lane
    /// (`Vd[i] = if Vn[i] <s 0 then 0 - Vn[i] else Vn[i]`, so `abs(INT_MIN) == INT_MIN`
    /// by two's-complement wraparound — matching clang and the negating SUB + SMAX
    /// path it replaces). Emitted by the abs-sum reduction lowering (`.4S`).
    /// Operands: [Vd, Vn, Imm(arrangement)] where arrangement is `.4S`.
    NeonAbsV,
    /// BIT Vd.16B, Vn.16B, Vm.16B — bitwise insert if true: for every BIT
    /// position, `Vd = Vd ^ ((Vd ^ Vn) & Vm)` — i.e. insert `Vn`'s bit where
    /// the mask `Vm` is 1, keep `Vd`'s bit where it is 0. With a per-lane
    /// all-ones/all-zeros compare mask this is exactly a per-lane select —
    /// the i64 (`.2D`) min/max reduction pairs it with `CMGT/CMHI.2D`
    /// (`SMAX/SMIN/UMAX/UMIN` have no `.2D` form).
    ///
    /// Vd is BOTH source and destination (a read-modify-write insert), so
    /// operand 0 is a tied def-use — see `has_tied_def_use` in
    /// trust-cg-opt/effects.rs.
    /// Operands: [Vd (tied def-use), Vn, Vm] (whole-register `.16B`).
    NeonBitV,
    /// UDOT Vd.4S, Vn.16B, Vm.16B — unsigned dot-product ACCUMULATE
    /// (FEAT_DotProd): for each 32-bit lane `i` in 0..3,
    /// `Vd[i] = Vd[i] + sum_{j=0..3}(zext32(Vn.byte[4i+j]) * zext32(Vm.byte[4i+j]))`.
    ///
    /// Vd is BOTH source and destination (a read-modify-write accumulate), so
    /// operand 0 is a tied def-use — see `has_tied_def_use` in
    /// trust-cg-opt/effects.rs. Emitted by the ctpop-reduction lowering as
    /// `UDOT(acc, CNT.16B(x), ones.16B)`: with an all-ones Vm each i32 lane
    /// accumulates the sum of its 4 per-byte popcounts, i.e. `acc += popcount(x)`
    /// per lane, replacing the UADDLP+UADDLP+ADD fold in one instruction.
    ///
    /// FEAT_DotProd (ARMv8.2 dot product) is assumed present: every Apple
    /// M-series chip has it, matching the backend's existing Apple-M target
    /// assumption (same precedent as the ARMv8.1 LSE atomics).
    /// Operands: [Vd (accumulator, def+use), Vn, Vm, Imm(input arrangement 16B)].
    NeonUdotV,
    /// EXT Vd.16B, Vn.16B, Vm.16B, #imm — byte-wise extract/concatenate: the
    /// result is bytes `imm .. imm+15` of the 32-byte concatenation `Vm:Vn`
    /// (`Vn` supplies the LOW bytes, `Vm` the HIGH bytes), i.e.
    /// `Vd.byte[j] = if j+imm < 16 then Vn.byte[j+imm] else Vm.byte[j+imm-16]`.
    ///
    /// Emitted by the NEON stencil vectorizer to form a shifted window
    /// in-register: with two consecutive 16-byte blocks `Vn = a[i..i+4)` and
    /// `Vm = a[i+4..i+8)` (i32 lanes), `EXT(Vn, Vm, #4*d)` yields
    /// `a[i+d..i+d+4)` — the middle stencil stream without its own load
    /// stream. Only byte shifts `#4 / #8 / #12` (whole-i32-lane shifts) are
    /// emitted and proven; the encoder REJECTS every other immediate
    /// (fail-closed: no proof credit exists for them). Operand ORDER matters
    /// (swapping `Vn`/`Vm` selects the complementary window) — pinned by the
    /// exact-byte encoding tests AND the swapped-operand refute control.
    /// Operands: [Vd, Vn, Vm, Imm(byte shift: 4, 8, or 12)].
    NeonExtV,
    /// SMLAL Vd.2D, Vn.2S, Vm.2S — SIGNED widening multiply-ACCUMULATE-LONG
    /// (LOW half): each of the two i64 output lanes accumulates the EXACT
    /// (no-truncation) product of a pair of i32->i64 SIGN-extended source lanes
    /// from the LOW `.4S` half `{0,1}`:
    /// `Vd.d[j] = Vd.d[j] + sext64(Vn.4S[j]) * sext64(Vm.4S[j])`, `j ∈ {0,1}`.
    ///
    /// Emitted by the NEON array-reduction vectorizer (neon_array) for the i32
    /// widening dot `s(i64) += (a_i32[i] as i64) * (b_i32[i] as i64)`, paired with
    /// [`Self::NeonSmlal2V`] (the HIGH `.4S` half `{2,3}`) so one Q-pair of i32
    /// loads feeds both. Input arrangement is FIXED `.4S -> .2D` (the ISA has no
    /// other size for this widening dot); the encoder fail-closes on anything
    /// else. Low vs high are SEPARATE opcodes (the FCVTL/FCVTL2 precedent), so the
    /// `.4S` lane-selection is baked into the opcode, not an operand.
    ///
    /// Vd is BOTH source and destination (a read-modify-write accumulate), so
    /// operand 0 is a tied def-use — see `has_tied_def_use` in
    /// trust-cg-opt/effects.rs (same class as UDOT/FMLA).
    /// Operands: [Vd (accumulator, def+use), Vn, Vm, Imm(input arrangement .4S)].
    NeonSmlalV,
    /// SMLAL2 Vd.2D, Vn.4S, Vm.4S — SIGNED widening multiply-ACCUMULATE-LONG
    /// (HIGH half): the HIGH-`.4S`-half sibling of [`Self::NeonSmlalV`], consuming
    /// source lanes `{2,3}`:
    /// `Vd.d[j] = Vd.d[j] + sext64(Vn.4S[2+j]) * sext64(Vm.4S[2+j])`, `j ∈ {0,1}`.
    /// Operand 0 is a tied def-use.
    /// Operands: [Vd (accumulator, def+use), Vn, Vm, Imm(input arrangement .4S)].
    NeonSmlal2V,
    /// UMLAL Vd.2D, Vn.2S, Vm.2S — UNSIGNED widening multiply-ACCUMULATE-LONG
    /// (LOW half): the ZERO-extending (unsigned) sibling of [`Self::NeonSmlalV`]:
    /// `Vd.d[j] = Vd.d[j] + zext64(Vn.4S[j]) * zext64(Vm.4S[j])`, `j ∈ {0,1}`.
    /// Emitted for the UNSIGNED widening dot `s(u64) += (a_u32[i] as u64) *
    /// (b_u32[i] as u64)`. Operand 0 is a tied def-use.
    /// Operands: [Vd (accumulator, def+use), Vn, Vm, Imm(input arrangement .4S)].
    NeonUmlalV,
    /// UMLAL2 Vd.2D, Vn.4S, Vm.4S — UNSIGNED widening multiply-ACCUMULATE-LONG
    /// (HIGH half): the HIGH-`.4S`-half sibling of [`Self::NeonUmlalV`], consuming
    /// source lanes `{2,3}`:
    /// `Vd.d[j] = Vd.d[j] + zext64(Vn.4S[2+j]) * zext64(Vm.4S[2+j])`, `j ∈ {0,1}`.
    /// Operand 0 is a tied def-use.
    /// Operands: [Vd (accumulator, def+use), Vn, Vm, Imm(input arrangement .4S)].
    NeonUmlal2V,
    /// UADDW Vd.2D, Vn.2D, Vm.2S — UNSIGNED widening add-WIDE (LOW half): each
    /// of the two i64 output lanes is the i64 addend lane of `Vn` plus a
    /// u32->u64 ZERO-extended source lane from the LOW `.4S` half `{0,1}` of
    /// `Vm`: `Vd.d[j] = Vn.d[j] + zext64(Vm.4S[j])`, `j ∈ {0,1}`.
    ///
    /// Emitted by the NEON widening abs-sum vectorizer (neon_array TRACK D) for
    /// `s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))`, paired with
    /// [`Self::NeonUaddw2V`] (the HIGH `.4S` half `{2,3}`) so one abs'd i32 Q
    /// feeds both — structurally MATCHING LLVM's `abs.4s + uaddw.2d + uaddw2.2d`
    /// codegen and replacing the UMLAL-by-ones MAC (per lane
    /// `acc_j + zext64(u_j)` == `acc_j + zext64(u_j) * 1`, same zero-extension,
    /// minus the ones splat and the multiply latency). Input arrangement is
    /// FIXED `.4S -> .2D` (the only form the vectorizer emits and the proof
    /// covers); the encoder fail-closes on anything else. Low vs high are
    /// SEPARATE opcodes (the SMLAL/FCVTL2 precedent), so the `.4S`
    /// lane-selection is baked into the opcode, not an operand.
    ///
    /// UNLIKE the xMLAL accumulators, this is the ISA's plain THREE-OPERAND
    /// form: `Vd` is a pure def and the i64 addend `Vn` is a SEPARATE source
    /// operand (operand 1) — NOT a tied def-use (`has_tied_def_use` is false;
    /// the vectorizer passes the same register for Vd and Vn to accumulate in
    /// place, which regalloc honors because both operands are the same vreg).
    /// Operands: [Vd (def), Vn (i64 addend), Vm (.4S source), Imm(input
    /// arrangement .4S)].
    NeonUaddwV,
    /// UADDW2 Vd.2D, Vn.2D, Vm.4S — UNSIGNED widening add-WIDE (HIGH half): the
    /// HIGH-`.4S`-half sibling of [`Self::NeonUaddwV`], consuming source lanes
    /// `{2,3}` of `Vm`:
    /// `Vd.d[j] = Vn.d[j] + zext64(Vm.4S[2+j])`, `j ∈ {0,1}`.
    /// Plain three-operand form (operand 0 pure def, NOT tied).
    /// Operands: [Vd (def), Vn (i64 addend), Vm (.4S source), Imm(input
    /// arrangement .4S)].
    NeonUaddw2V,
    /// SADDW Vd.2D, Vn.2D, Vm.4S — SIGNED widening add-WIDE (LOW half): each
    /// of the two i64 output lanes is the i64 addend lane of `Vn` plus an
    /// i32->i64 SIGN-extended source lane from the LOW `.4S` half `{0,1}` of
    /// `Vm`: `Vd.d[j] = Vn.d[j] + sext64(Vm.4S[j])`, `j ∈ {0,1}`.
    ///
    /// The SIGNED sibling of [`Self::NeonUaddwV`] (U-bit 0 vs 1 — a DIFFERENT
    /// program on every lane with bit 31 set; each has its own faithful proof
    /// and a sign-confusion refute control against the other). Emitted by the
    /// NEON predicated-sum vectorizer (neon_predsum) for the WIDENING
    /// i64-accumulator condsum `s(i64) += (a_i32[iv] as i64) [if pred]`:
    /// `acc.2d[j] += sext64(masked_half[j])`, paired with
    /// [`Self::NeonSaddw2V`] (the HIGH `.4S` half `{2,3}`) so one masked i32 Q
    /// feeds both — structurally MATCHING LLVM's `cmgt.4s + and.16b +
    /// saddw.2d + saddw2.2d` codegen and replacing the SMLAL-by-ones MAC (per
    /// lane `acc_j + sext64(x_j)` == `acc_j + sext64(x_j) * sext64(1)`, same
    /// sign-extension, minus the ones splat and the multiply latency). Input
    /// arrangement is FIXED `.4S -> .2D` (the only form the vectorizer emits
    /// and the proof covers); the encoder fail-closes on anything else. Low vs
    /// high are SEPARATE opcodes (the SMLAL/UADDW precedent), so the `.4S`
    /// lane-selection is baked into the opcode, not an operand.
    ///
    /// Like UADDW (and UNLIKE the xMLAL accumulators), this is the ISA's plain
    /// THREE-OPERAND form: `Vd` is a pure def and the i64 addend `Vn` is a
    /// SEPARATE source operand (operand 1) — NOT a tied def-use
    /// (`has_tied_def_use` is false; the vectorizer passes the same register
    /// for Vd and Vn to accumulate in place, which regalloc honors because
    /// both operands are the same vreg).
    /// Operands: [Vd (def), Vn (i64 addend), Vm (.4S source), Imm(input
    /// arrangement .4S)].
    NeonSaddwV,
    /// SADDW2 Vd.2D, Vn.2D, Vm.4S — SIGNED widening add-WIDE (HIGH half): the
    /// HIGH-`.4S`-half sibling of [`Self::NeonSaddwV`], consuming source lanes
    /// `{2,3}` of `Vm`:
    /// `Vd.d[j] = Vn.d[j] + sext64(Vm.4S[2+j])`, `j ∈ {0,1}`.
    /// Plain three-operand form (operand 0 pure def, NOT tied).
    /// Operands: [Vd (def), Vn (i64 addend), Vm (.4S source), Imm(input
    /// arrangement .4S)].
    NeonSaddw2V,
    /// MLA Vd.4S, Vn.4S, Vm.4S — vector integer multiply-ACCUMULATE: per lane
    /// `Vd[i] = Vd[i] + Vn[i]*Vm[i]` (all mod 2^32; the low 32 bits of the
    /// product — the same-width truncating multiply, exactly `MUL.4S` fed into
    /// an add). `Vd` is BOTH source and destination (the accumulate READS the
    /// prior value as an explicit addend), so operand 0 is a TIED def-use like
    /// UDOT/SMLAL/FMLA — see `has_tied_def_use` in trust-cg-opt/effects.rs
    /// (contrast the three-operand UADDW/SADDW family, whose addend is a
    /// separate source operand).
    ///
    /// Emitted by the NEON predicated-sum vectorizer (neon_predsum) as the
    /// MLA-BY-MASK accumulate of the `Gpr32` (`.4S`) masked-add condsum
    /// `s(i32) += a_i32[iv] [if pred]`: the compare mask lane is exactly `-1`
    /// (all-ones) where the predicate holds and `0` otherwise, so
    /// `MLA(acc, a, mask)` contributes `a * (-1) == -a mod 2^32` on TRUE lanes
    /// and `0` on FALSE lanes — the accumulators hold the NEGATED predicated
    /// sum (folded at the drain by one wrapping `SubRR`), and the masking AND
    /// plus the accumulate ADD collapse into ONE op (2 vector ops per Q-block
    /// instead of 3). Exact for ALL i32 values including `i32::MIN`
    /// (`(-1) * a mod 2^32 == -a mod 2^32` unconditionally; the scalar acc is
    /// a wrapping i32, i.e. the same mod-2^32 group).
    ///
    /// Only the `.4S` arrangement is emitted (and proven); the encoder
    /// fail-closes on anything else.
    /// Operands: [Vd (accumulator, def+use), Vn, Vm, Imm(arrangement .4S)].
    NeonMlaV,
    /// UADALP Vd.2D, Vn.4S — UNSIGNED pairwise widening ACCUMULATE (Add and
    /// Accumulate Long Pairwise): each of the two i64 output lanes accumulates
    /// the sum of a ZERO-extended adjacent source-lane PAIR:
    /// `Vd.d[j] = Vd.d[j] + zext64(Vn.4S[2j]) + zext64(Vn.4S[2j+1])`,
    /// `j ∈ {0,1}` (all mod 2^64). The accumulating sibling of
    /// [`Self::NeonUaddlpV`] (which widens WITHOUT reading `Vd`): `Vd` is BOTH
    /// source and destination, so operand 0 is a TIED def-use like UDOT/SMLAL
    /// — see `has_tied_def_use` in trust-cg-opt/effects.rs.
    ///
    /// Emitted by the NEON widening abs-sum vectorizer (neon_array TRACK D)
    /// for `s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))`, replacing the
    /// UADDW/UADDW2 pair (2 ops) with ONE op per Q: both forms add the SAME
    /// four `zext64(u_j)` terms into the accumulator's two `.2D` lanes —
    /// UADDW/UADDW2 groups lanes {0,2} / {1,3}, UADALP groups the adjacent
    /// pairs {0,1} / {2,3} — and the drain sums BOTH `.2D` lanes into one
    /// scalar i64, so the different per-lane grouping is a pure REASSOCIATION
    /// of modular (mod-2^64) addition: the folded total is identical for every
    /// input. The extension is UNSIGNED (the abs output lanes are the exact
    /// u32 `unsigned_abs` bit patterns, zero-extended by the scalar `Uxtw`
    /// root); the signed SADALP is a different function on lanes `>= 2^31`
    /// (exactly the `i32::MIN` lanes) and is never emitted.
    ///
    /// Input arrangement is FIXED `.4S -> .2D` (the only form the vectorizer
    /// emits and the proof covers); the encoder fail-closes on anything else.
    /// Operands: [Vd (accumulator, def+use), Vn (.4S source), Imm(input
    /// arrangement .4S)].
    NeonUadalpV,
    /// FMLA Vd.T, Vn.T, Vm.T — FP vector FUSED multiply-ACCUMULATE: per lane
    /// `Vd[i] = Vd[i] + Vn[i]*Vm[i]` with a SINGLE rounding of the exact
    /// product-plus-addend (fused, NOT round-twice) — the vector sibling of the
    /// scalar [`Self::FmaddRR`]/`llvm.fmuladd`. `Vd` is BOTH source and
    /// destination (a read-modify-write accumulate), so operand 0 is a tied
    /// def-use (see `has_tied_def_use` in trust-cg-opt/effects.rs). Emitted by
    /// the IV-synthesized FP-reduction vectorizer ([`crate`] neon_fpred) to
    /// carry a scalar `FmaddRR(d, n, m, a)` into per-lane form as
    /// `MOV Vd, broadcast(a); FMLA Vd, Vn, Vm` — preserving the SAME single
    /// rounding the scalar loop performs, so the lane result is bit-identical.
    /// Operands: [Vd (tied def-use), Vn, Vm, Imm(fp-arrangement 0=2S,1=4S,2=2D)].
    NeonFmlaV,
    /// FMLS Vd.T, Vn.T, Vm.T — FP vector FUSED multiply-SUBTRACT: per lane
    /// `Vd[i] = Vd[i] - Vn[i]*Vm[i]` (single rounding). The subtract sibling of
    /// [`Self::NeonFmlaV`]; carries a scalar `FmsubRR(d, n, m, a)` (`d = a - n*m`)
    /// per lane. Operand 0 is a tied def-use.
    /// Operands: [Vd (tied def-use), Vn, Vm, Imm(fp-arrangement)].
    NeonFmlsV,
    /// UCVTF Vd.T, Vn.T — per-lane UNSIGNED integer-to-FP conversion (round to
    /// nearest-even under FPCR): each lane converts an unsigned integer to the
    /// same-width float, IDENTICAL to the scalar [`Self::UcvtfRR`] per lane.
    /// Emitted by the IV-synthesized FP-reduction vectorizer to convert the
    /// `.2D` integer induction-index vector `[i, i+1]` to `[（double)i,(double)(i+1)]`.
    /// Operands: [Vd, Vn, Imm(fp-arrangement 1=4S i32→f32, 2=2D i64→f64)].
    NeonUcvtfV,
    /// SCVTF Vd.T, Vn.T — per-lane SIGNED integer-to-FP conversion (RNE); the
    /// signed sibling of [`Self::NeonUcvtfV`], matching scalar [`Self::ScvtfRR`].
    /// Operands: [Vd, Vn, Imm(fp-arrangement)].
    NeonScvtfV,
    /// FCVTL Vd.2D, Vn.2S — FP convert to HIGHER precision (LONG), LOW half: the
    /// two `f32` lanes in the LOW 64 bits of `Vn` are each widened to `f64`, filling
    /// `Vd.2D`. Widening `f32→f64` is EXACT (every finite/inf/NaN `f32` is
    /// representable as `f64`, no rounding), so the per-lane semantics are a pure
    /// `fpext`. Emitted by the FP array-reduction vectorizer (`neon_farray`) to
    /// widen `f32` array elements for the `sum += (double)a[i]*(double)b[i]` kernel
    /// (halving the convert throughput vs two scalar `FCVT`s per pair). The high 64
    /// bits of `Vn` are IGNORED (contrast `NeonFcvtl2V`, which reads them).
    /// Operands: [Vd (Fpr128), Vn (Fpr128)].
    NeonFcvtlV,
    /// FCVTL2 Vd.2D, Vn.4S — FP convert to HIGHER precision (LONG), HIGH half: the
    /// two `f32` lanes in the HIGH 64 bits of `Vn` (lanes 2,3 of `Vn.4S`) are each
    /// widened to `f64`, filling `Vd.2D`. The `2` suffix is the ARM Q-bit selector
    /// that reads the upper half — the ONLY difference from [`Self::NeonFcvtlV`];
    /// per-lane semantics are the same exact `fpext`. Paired with `NeonFcvtlV` to
    /// convert all four `f32` lanes of a loaded `Vn.4S` into two `.2D` (4 x f64)
    /// vectors. Operands: [Vd (Fpr128), Vn (Fpr128)].
    NeonFcvtl2V,
    /// DUP Dd, Vn.D[lane] — extract one 64-bit FP lane of a `.2D` vector into a
    /// SCALAR `Dd` register (the assembler `MOV Dd, Vn.D[lane]`), a pure 64-bit
    /// copy with NO rounding. Emitted by the IV-synthesized FP-reduction
    /// vectorizer's ORDERED DRAIN: `mov d, vterm.d[0]; fadd acc, acc, d;
    /// mov d, vterm.d[1]; fadd acc, acc, d; …` folds the per-lane term results
    /// into the scalar accumulator in EXACTLY the scalar iteration order, so no
    /// FP reassociation occurs and the sum is bit-identical to the scalar loop.
    /// Operand 0 is an `Fpr64` def; operand 1 is the `Fpr128` source (they alias
    /// the same V register file — see `regs_overlap`). lane ∈ {0, 1}.
    /// Operands: [Dd (Fpr64), Vn (Fpr128), Imm(lane)].
    NeonDupScalarD,

    // -- Atomic memory operations (ARMv8.1-a LSE + legacy LL/SC) --
    /// LDAR Xt, [Xn] — load-acquire (sequential consistency load).
    /// size: 32-bit (Wt) or 64-bit (Xt) from register class.
    /// Operands: [Rt, Rn]
    Ldar,
    /// LDARB Wt, [Xn] — load-acquire byte.
    /// Operands: [Rt, Rn]
    Ldarb,
    /// LDARH Wt, [Xn] — load-acquire halfword.
    /// Operands: [Rt, Rn]
    Ldarh,
    /// STLR Xt, [Xn] — store-release (sequential consistency store).
    /// size: 32-bit (Wt) or 64-bit (Xt) from register class.
    /// Operands: [Rt, Rn]
    Stlr,
    /// STLRB Wt, [Xn] — store-release byte.
    /// Operands: [Rt, Rn]
    Stlrb,
    /// STLRH Wt, [Xn] — store-release halfword.
    /// Operands: [Rt, Rn]
    Stlrh,

    /// LDADD Xs, Xt, [Xn] — atomic add (ARMv8.1-a LSE).
    /// Atomically: Xt = *Xn; *Xn = Xt + Xs.
    /// Operands: [Rs (addend), Rt (old value dest), Rn (address)]
    Ldadd,
    /// LDADDA — load-acquire variant.
    Ldadda,
    /// LDADDAL — load-acquire + store-release (full barrier).
    Ldaddal,
    /// LDADDL — store-release-only variant (A=0, R=1). Used by
    /// `AtomicRmw { ordering: Release }` (e.g. `Arc::drop`'s `fetch_sub(1, Release)`).
    Ldaddl,

    /// LDCLR Xs, Xt, [Xn] — atomic bit clear (AND NOT) (ARMv8.1-a LSE).
    /// Atomically: Xt = *Xn; *Xn = Xt AND NOT Xs.
    /// Operands: [Rs, Rt, Rn]
    Ldclr,
    /// LDCLRA — load-acquire-only variant (A=1, R=0). Selected for
    /// `AtomicRmw { op: And, ordering: Acquire }` — the exact acquire form,
    /// not the strictly-stronger AL strengthening.
    Ldclra,
    /// LDCLRAL — full barrier variant.
    Ldclral,
    /// LDCLRL — store-release-only variant (A=0, R=1).
    Ldclrl,

    /// LDEOR Xs, Xt, [Xn] — atomic exclusive OR (ARMv8.1-a LSE).
    /// Atomically: Xt = *Xn; *Xn = Xt XOR Xs.
    /// Operands: [Rs, Rt, Rn]
    Ldeor,
    /// LDEORA — load-acquire-only variant (A=1, R=0).
    Ldeora,
    /// LDEORAL — full barrier variant.
    Ldeoral,
    /// LDEORL — store-release-only variant (A=0, R=1).
    Ldeorl,

    /// LDSET Xs, Xt, [Xn] — atomic bit set (OR) (ARMv8.1-a LSE).
    /// Atomically: Xt = *Xn; *Xn = Xt OR Xs.
    /// Operands: [Rs, Rt, Rn]
    Ldset,
    /// LDSETA — load-acquire-only variant (A=1, R=0).
    Ldseta,
    /// LDSETAL — full barrier variant.
    Ldsetal,
    /// LDSETL — store-release-only variant (A=0, R=1).
    Ldsetl,

    /// LDSMAX Xs, Xt, [Xn] — atomic signed maximum (ARMv8.1-a LSE).
    /// Atomically: Xt = *Xn; *Xn = signed_max(Xt, Xs).
    /// Operands: [Rs, Rt, Rn]
    Ldsmax,
    /// LDSMAXA — load-acquire-only variant (A=1, R=0).
    Ldsmaxa,
    /// LDSMAXAL — full barrier variant.
    Ldsmaxal,
    /// LDSMAXL — store-release-only variant (A=0, R=1).
    Ldsmaxl,

    /// LDSMIN Xs, Xt, [Xn] — atomic signed minimum (ARMv8.1-a LSE).
    /// Atomically: Xt = *Xn; *Xn = signed_min(Xt, Xs).
    /// Operands: [Rs, Rt, Rn]
    Ldsmin,
    /// LDSMINA — load-acquire-only variant (A=1, R=0).
    Ldsmina,
    /// LDSMINAL — full barrier variant.
    Ldsminal,
    /// LDSMINL — store-release-only variant (A=0, R=1).
    Ldsminl,

    /// LDUMAX Xs, Xt, [Xn] — atomic unsigned maximum (ARMv8.1-a LSE).
    /// Atomically: Xt = *Xn; *Xn = unsigned_max(Xt, Xs).
    /// Operands: [Rs, Rt, Rn]
    Ldumax,
    /// LDUMAXA — load-acquire-only variant (A=1, R=0).
    Ldumaxa,
    /// LDUMAXAL — full barrier variant.
    Ldumaxal,
    /// LDUMAXL — store-release-only variant (A=0, R=1).
    Ldumaxl,

    /// LDUMIN Xs, Xt, [Xn] — atomic unsigned minimum (ARMv8.1-a LSE).
    /// Atomically: Xt = *Xn; *Xn = unsigned_min(Xt, Xs).
    /// Operands: [Rs, Rt, Rn]
    Ldumin,
    /// LDUMINA — load-acquire-only variant (A=1, R=0).
    Ldumina,
    /// LDUMINAL — full barrier variant.
    Lduminal,
    /// LDUMINL — store-release-only variant (A=0, R=1).
    Lduminl,

    /// SWP Xs, Xt, [Xn] — atomic swap (ARMv8.1-a LSE).
    /// Atomically: Xt = *Xn; *Xn = Xs.
    /// Operands: [Rs, Rt, Rn]
    Swp,
    /// SWPA — load-acquire-only variant (A=1, R=0). Selected for
    /// `AtomicRmw { op: Xchg, ordering: Acquire }` (the darwin thread
    /// Parker's `state.swap(EMPTY, Acquire)`).
    Swpa,
    /// SWPAL — full barrier variant.
    Swpal,
    /// SWPL — store-release-only variant (A=0, R=1).
    Swpl,

    /// CAS Xs, Xt, [Xn] — compare and swap (ARMv8.1-a LSE).
    /// Atomically: if *Xn == Xs then *Xn = Xt; Xs = old *Xn.
    /// Operands: [Rs (expected/result), Rt (desired), Rn (address)]
    Cas,
    /// CASA — load-acquire variant.
    Casa,
    /// CASAL — full barrier (acquire + release).
    Casal,
    /// CASL — store-release-only variant (A=0, o0/R=1). Selected for a
    /// release-only compare-exchange (`compare_exchange_weak(.., Release,
    /// Relaxed)` — the rwlock `read_unlock` fast path). Narrow (byte/half)
    /// accesses use the same opcode with the explicit access-size immediate,
    /// yielding the CASLB/CASLH encodings.
    Casl,

    /// LDAXR Xt, [Xn] — load-acquire exclusive register (LL/SC legacy path).
    /// Operands: [Rt, Rn]
    Ldaxr,
    /// STLXR Ws, Xt, [Xn] — store-release exclusive register (LL/SC legacy path).
    /// Ws receives 0 on success, 1 on failure.
    /// Operands: [Ws (status), Rt (value), Rn (address)]
    Stlxr,

    /// DMB — data memory barrier.
    /// Operands: [Imm(option)] where option is CRm field (e.g., 0xF = SY, 0xB = ISH).
    Dmb,
    /// DSB — data synchronization barrier.
    /// Operands: [Imm(option)]
    Dsb,
    /// ISB — instruction synchronization barrier.
    /// Operands: [Imm(option)] (typically 0xF = SY).
    Isb,

    // -- Address --
    Adrp,
    /// ADR Xd, label — form PC-relative address (used for jump table base).
    /// Operands (at ISel level): [Xd, JumpTable{...}]
    /// Operands (at codegen level): [Xd, Imm(offset)]
    Adr,
    AddPCRel,
    /// ADD Xd, Xn, #:tprel_hi12:sym, LSL #12 — ELF local-exec TLS: add bits
    /// [23:12] of the symbol's TP-relative offset (imm12 placeholder 0,
    /// patched by the linker via `R_AARCH64_TLSLE_ADD_TPREL_HI12`).
    /// Operands: [Xd, Xn, Symbol(name)]. Emitted only by the AOT ELF
    /// `TlsRef { model: LocalExec, local_exec_offset: None }` lowering;
    /// Mach-O object emission fails closed on its fixup.
    AddTprelHi12,
    /// ADD Xd, Xn, #:tprel_lo12_nc:sym — ELF local-exec TLS: add bits [11:0]
    /// of the symbol's TP-relative offset (imm12 placeholder 0, patched via
    /// `R_AARCH64_TLSLE_ADD_TPREL_LO12_NC`). Pairs after `AddTprelHi12`.
    /// Operands: [Xd, Xn, Symbol(name)].
    AddTprelLo12,

    // -- Jump table support --
    /// LDRSW Xt, [Xn, Xm, LSL #2] — load signed word with register offset.
    /// Used to load 32-bit relative offsets from jump tables.
    /// Operands: [Xt (dst), Xn (base), Xm (index)]
    LdrswRO,

    // -- Checked arithmetic (set flags for overflow detection) --
    /// ADDS: add and set flags (used for overflow-checked addition).
    AddsRR,
    /// ADDS immediate: add immediate and set flags.
    AddsRI,
    /// SUBS: subtract and set flags (used for overflow-checked subtraction).
    SubsRR,
    /// SUBS immediate: subtract immediate and set flags.
    SubsRI,

    // -- i128 multi-register arithmetic --
    /// ADC Xd, Xn, Xm — add with carry (for i128 high-half addition).
    /// Reads carry flag from previous ADDS. Always 64-bit.
    Adc,
    /// SBC Xd, Xn, Xm — subtract with carry/borrow (for i128 high-half subtraction).
    /// Reads carry/borrow flag from previous SUBS. Always 64-bit.
    Sbc,
    /// UMULH Xd, Xn, Xm — unsigned multiply high (upper 64 bits of 64x64->128 product).
    /// Always 64-bit (no 32-bit variant).
    Umulh,
    /// SMULH Xd, Xn, Xm — signed multiply high (upper 64 bits of signed 64x64->128 product).
    /// Always 64-bit (no 32-bit variant). Used for the aarch64 overflow-safe
    /// signed-mul idiom: `MUL lo; SMULH hi; CMP hi, lo, ASR #63; B.NE overflow`.
    Smulh,
    /// MADD Xd, Xn, Xm, Xa — multiply-add: Xd = Xa + Xn * Xm.
    /// Used for i128 multiplication middle-term accumulation.
    Madd,

    // -- Trap / panic instructions and pseudo-guards --
    /// BRK #1 — real synchronous breakpoint/trap instruction.
    Brk,
    /// Trap on overflow: conditional branch to trap block after ADDS/SUBS.
    /// Operands: [condition_code_imm, Block(trap_target)].
    TrapOverflow,
    /// Trap on bounds check failure: branch to panic if index >= length.
    /// Operands: [Block(panic_target)].
    TrapBoundsCheck,
    /// Proof-only exact bounds guard pseudo: trap if index >= bound.
    /// Operands: [base, index, imm_bound]. Base is identity metadata for
    /// exact proof binding; the runtime check compares index against bound.
    /// Removed by InBounds proof opts or expanded before final encoding.
    TrapBoundsCheckExact,
    /// Trap on null pointer.
    /// Operands: [Block(panic_target)].
    TrapNull,
    /// Trap if the pointer operand is zero.
    /// Operands: [ptr]. Expanded before encoding to `CBNZ ptr, +2; BRK #1`.
    TrapNullIfZero,
    /// Trap on division by zero: branch to trap block if divisor is zero.
    /// Operands: [Block(panic_target)].
    TrapDivZero,
    /// Proof-only divide-by-zero guard: trap if the divisor operand is zero.
    /// Operands: [divisor]. Self-contained carrier (the exact DivZero mirror of
    /// [`Self::TrapNullIfZero`]): the divisor whose non-zeroness was proven is the
    /// carrier's own operand, so the Certified-Elimination Kernel can fingerprint
    /// [divisor] and re-check it. Removed by NonZeroDivisor proof opts or expanded
    /// before encoding to `CBNZ divisor, +2; BRK #1`.
    TrapDivZeroIfZero,
    /// Trap on out-of-range shift amount: branch to trap block if shift >= bitwidth.
    /// Operands: [Block(panic_target)].
    TrapShiftRange,
    /// Proof-only shift-range guard: trap if `amount >= bitwidth` (unsigned).
    /// Operands: [amount, imm_bitwidth]. Self-contained carrier (the ShiftRange
    /// mirror of [`Self::TrapBoundsCheckExact`]): the shift amount and its width
    /// are the carrier's own operands, so the Certified-Elimination Kernel can
    /// fingerprint [amount, Imm(bitwidth)] and re-check it. Removed by ValidShift
    /// proof opts or expanded before encoding to
    /// `CMP amount, #bitwidth; B.LO +2; BRK #1`.
    TrapShiftRangeIfOOB,

    // -- Reference counting pseudo-instructions --
    /// Retain (increment reference count). Operands: [ptr].
    Retain,
    /// Release (decrement reference count). Operands: [ptr].
    Release,

    // -- LLVM-style typed aliases (used by trust-cg-lower isel) --
    /// MOV Wd, Wn — 32-bit register move.
    MOVWrr,
    /// MOV Xd, Xn — 64-bit register move.
    MOVXrr,
    /// STR Wt, [Xn, #imm] — store 32-bit integer, unsigned immediate offset.
    STRWui,
    /// STR Xt, [Xn, #imm] — store 64-bit integer, unsigned immediate offset.
    STRXui,
    /// STR St, [Xn, #imm] — store 32-bit FP, unsigned immediate offset.
    STRSui,
    /// STR Dt, [Xn, #imm] — store 64-bit FP, unsigned immediate offset.
    STRDui,
    /// BL label — branch with link (LLVM-style alias for Bl).
    BL,
    /// BLR Xn — branch with link to register (LLVM-style alias for Blr).
    BLR,
    /// CMP Wn, Wm — 32-bit compare register.
    CMPWrr,
    /// CMP Xn, Xm — 64-bit compare register.
    CMPXrr,
    /// CMP Wn, #imm — 32-bit compare immediate.
    CMPWri,
    /// CMP Xn, #imm — 64-bit compare immediate.
    CMPXri,
    /// MOVZ Wd, #imm — 32-bit move zero immediate.
    MOVZWi,
    /// MOVZ Xd, #imm — 64-bit move zero immediate.
    MOVZXi,
    /// B.cond label — conditional branch (LLVM-style alias for BCond).
    Bcc,

    // -- System register access --
    /// MRS Xd, (sysreg) — move from system register.
    ///
    /// Reads an AArch64 system register into a GPR. Used by the thread-local
    /// storage local-exec sequence (MRS Xd, TPIDR_EL0) and other system-level
    /// accesses. The destination is always 64-bit.
    ///
    /// Operands: `[PReg(Xd), Imm(sysreg_encoding)]`
    ///
    /// `sysreg_encoding` packs op0/op1/CRn/CRm/op2 into the 16-bit
    /// "systemreg" field used by the A64 instruction encoding (bits[20:5]):
    ///   bits [15:14] = op0  (always 0b11 for EL0/EL1 sysregs MRS/MSR can access)
    ///   bits [13:11] = op1
    ///   bits [10:7]  = CRn
    ///   bits [6:3]   = CRm
    ///   bits [2:0]   = op2
    /// For TPIDR_EL0 (op0=11, op1=011, CRn=1101, CRm=0000, op2=010) the
    /// packed value is `0xDE82`, and the full instruction word is
    /// `0xD53BD040 | Rd`.
    ///
    /// See the MRS encoder in `aarch64/encode.rs`, ARM ARM C6.2.169, and
    /// LLVM `AArch64SystemOperands.td` `class SysReg`.
    Mrs,

    // -- Pseudo-instructions (no hardware encoding) --
    Phi,
    StackAlloc,
    /// COPY: register-to-register copy pseudo (resolved by regalloc).
    Copy,
    Nop,

    // -- NEON SIMD shift by immediate (appended at the end of the enum to
    //    preserve the implicit discriminants of every variant above) --
    /// SHL Vd.T, Vn.T, #shift — vector left shift by immediate.
    /// Operands: `[Vd, Vn, Imm(shift), Imm(arrangement)]`.
    NeonShlVImm,
    /// USHR Vd.T, Vn.T, #shift — vector unsigned (logical) right shift by immediate.
    /// Operands: `[Vd, Vn, Imm(shift), Imm(arrangement)]`.
    NeonUshrVImm,
    /// SSHR Vd.T, Vn.T, #shift — vector signed (arithmetic) right shift by immediate.
    /// Operands: `[Vd, Vn, Imm(shift), Imm(arrangement)]`.
    NeonSshrVImm,

    /// Proof-only overflow guard with self-contained operand identity.
    ///
    /// Operands: `[lhs, rhs, Imm(op_tag)]`, where `op_tag` packs the arithmetic
    /// op-kind (signed/unsigned × add/sub) and the operand width into a single
    /// immediate (see [`crate::overflow_tag`]). This is the OVERFLOW analogue of
    /// [`Self::TrapBoundsCheckExact`] / [`Self::TrapShiftRangeIfOOB`], but it is a
    /// *bigger* soundness obligation: rather than re-checking a single operand, a
    /// KEPT carrier RE-DERIVES the overflow condition from `lhs` and `rhs` by a
    /// flag-only `ADDS/SUBS XZR, lhs, rhs` followed by the matching conditional
    /// skip-branch + `BRK #1`. The value-producing op is a SEPARATE plain `ADD/SUB`
    /// (the carrier carries no result), so this carrier DECOUPLES the value from the
    /// overflow check — unlike the legacy `apply_no_overflow` path, where the same
    /// `ADDS/SUBS` did double duty (value + NZCV).
    ///
    /// The `op_tag` is part of the carrier's operand identity, so the Certified-
    /// Elimination Kernel fingerprints `[lhs, rhs, Imm(op_tag)]`: a wrong-op or
    /// wrong-width overflow proof fingerprints differently and CANNOT discharge it.
    /// Removed by NoOverflow/NoSignedOverflow/NoUnsignedOverflow proof opts under
    /// the kernel gate, or expanded before encoding to a flag-recompute + skip +
    /// trap so an ACTUAL overflow still traps. Appended after the earlier opcode
    /// surface to preserve every preceding implicit discriminant.
    TrapOverflowExact,

    /// Authenticated direct tail call.
    ///
    /// This has the hardware encoding of `B`, but remains structurally distinct
    /// in MachIR so register allocation and the final call-argument verifier
    /// retain the originating call's implicit argument uses and clobbers. A
    /// plain `B` is never an argument-consuming call boundary.
    ///
    /// Operands: `[Symbol|Block|Imm(target)]`. Appended to preserve all earlier
    /// opcode discriminants.
    TailCall,

    /// LDR Xd, [Xn, #:gottprel_lo12:sym] — load a thread-local's TPREL offset
    /// from its GOT slot (ELF initial-exec TLS, paired with an
    /// `ADRP Xn, :gottprel:sym`).
    ///
    /// Same hardware encoding as [`Self::LdrGot`] (64-bit unsigned-offset
    /// load); structurally distinct so encode-time ADRP pairing selects the
    /// `R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21` / `_LD64_GOTTPREL_LO12_NC`
    /// relocation pair instead of the data-GOT pair (exactly as `LdrTlvp` is
    /// the TLV-flavored `LdrGot`). Operands: `[Xd, Xn, Symbol]`. Appended to
    /// preserve all earlier opcode discriminants.
    LdrGottprel,

    /// FMLA Vd.T, Vn.T, Vm.Ts[lane] — FP vector fused multiply-accumulate BY
    /// ELEMENT: per lane `Vd[i] = Vd[i] + Vn[i]*Vm[lane]` — the SAME fused
    /// SINGLE-rounding accumulate as [`Self::NeonFmlaV`], except the multiplier
    /// is ONE broadcast lane `Vm[lane]` of the second source rather than the
    /// matching lane `Vm[i]`. This is the shape clang emits for `y[i] += da*x[i]`
    /// (a scalar invariant `da` kept in a vector lane, no `DUP` broadcast): the
    /// vectorizer ([`crate`] neon_fmap) keeps the invariant in lane 0 of an FPR
    /// and emits `FMLA Vd, Vx, Vda.s[0]`, eliminating the hoisted broadcast.
    /// `Vd` is BOTH source and destination (tied def-use, operand 0), exactly
    /// like `NeonFmlaV`. Only the `.4S` (single, `sz=10`, lane 0..3 via H:L) and
    /// `.2D` (double, `sz=11`, lane 0..1 via H) forms are emitted and proven; the
    /// encoder REJECTS any other arrangement/lane (fail-closed). `Vm` may be any
    /// V0-V31 (the register's high bit is the encoding `M` bit).
    /// Operands: [Vd (tied def-use), Vn, Vm, Imm(lane), Imm(fp-arrangement 1=4S,2=2D)].
    /// Appended to preserve all earlier opcode discriminants.
    NeonFmlaLaneV,

    // -- Volatile memory (immediate offset) --
    // Encode BYTE-IDENTICALLY to the corresponding LdrRI/LdrbRI/LdrhRI /
    // StrRI/StrbRI/StrhRI, but are DISTINCT opcodes so the optimizer treats
    // them as memory barriers (MemoryEffect::Call): a volatile access (MMIO /
    // signal visibility) must never be elided, CSE'd, forwarded, hoisted, or
    // reordered. The opcode-hardcoded memory passes (gvn/mem_pair/
    // recurrence_store_forward) match the plain opcodes and so conservatively
    // ignore these; the effect-gated passes see the Call barrier. Appended
    // after NeonFmlaLaneV to preserve every older implicit discriminant.
    /// Volatile LDR (word/dword/FP), same encoding as `LdrRI`.
    VolatileLdrRI,
    /// Volatile LDRB, same encoding as `LdrbRI`.
    VolatileLdrbRI,
    /// Volatile LDRH, same encoding as `LdrhRI`.
    VolatileLdrhRI,
    /// Volatile STR (word/dword/FP), same encoding as `StrRI`.
    VolatileStrRI,
    /// Volatile STRB, same encoding as `StrbRI`.
    VolatileStrbRI,
    /// Volatile STRH, same encoding as `StrhRI`.
    VolatileStrhRI,

    /// Emission-time alignment padding NOP (`HINT #0`, word `0xD503201F`).
    ///
    /// Unlike [`Self::Nop`] (an `IS_PSEUDO` that every encoder walk SKIPS),
    /// `AlignNop` is a REAL 4-byte instruction: it occupies one instruction
    /// slot in every offset derivation (branch resolution, encoding, EH
    /// re-derivation, CFG reconstruction from resolved immediates) and encodes
    /// to the architectural NOP. That self-describing property is the whole
    /// point: alignment padding must shift every downstream byte offset by
    /// exactly its own size in every consumer, or branch targets/LSDA ranges
    /// drift.
    ///
    /// Created ONLY by the loop-head alignment pass
    /// (`trust_cg_codegen::loop_align`), which inserts runs of at most 3 at
    /// the very END of the layout-predecessor of a 32-byte-aligned innermost
    /// loop header, immediately before branch resolution. Semantics: the
    /// architectural NOP is a no-op; padding at a block seam either executes
    /// on the fallthrough path (harmless) or sits after a hard terminator
    /// (dead bytes). No branch ever targets padding: branch targets are block
    /// starts, which lie after any padding by construction.
    ///
    /// Operands: none. Appended to preserve all earlier opcode discriminants.
    AlignNop,
}

impl AArch64Opcode {
    /// Returns the default instruction flags for this opcode.
    pub fn default_flags(self) -> InstFlags {
        use AArch64Opcode::*;
        match self {
            // Branches
            B => InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            TailCall => InstFlags::IS_CALL
                .union(InstFlags::IS_BRANCH)
                .union(InstFlags::IS_TERMINATOR)
                .union(InstFlags::HAS_SIDE_EFFECTS)
                .union(InstFlags::READS_MEMORY)
                .union(InstFlags::WRITES_MEMORY),
            BCond => InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            Cbz => InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            Cbnz => InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            Tbz => InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            Tbnz => InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            Br => InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),

            // Conditional branch aliases
            Bcc => InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),

            // Calls are conservative memory barriers: an arbitrary callee may
            // read or write through pointer arguments or global state.
            Bl | BL => InstFlags::IS_CALL
                .union(InstFlags::HAS_SIDE_EFFECTS)
                .union(InstFlags::READS_MEMORY)
                .union(InstFlags::WRITES_MEMORY),
            Blr | BLR => InstFlags::IS_CALL
                .union(InstFlags::HAS_SIDE_EFFECTS)
                .union(InstFlags::READS_MEMORY)
                .union(InstFlags::WRITES_MEMORY),

            // Return
            Ret => InstFlags::IS_RETURN.union(InstFlags::IS_TERMINATOR),

            // Memory loads
            LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | LdrRO | LdrbRO | LdrhRO | LdrswRO => {
                InstFlags::READS_MEMORY
            }
            LdrPreIndex | LdrPostIndex => {
                InstFlags::READS_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS)
            }
            LdrLiteral | LdrGot | LdrTlvp | LdrGottprel => InstFlags::READS_MEMORY,
            LdpRI | LdpPostIndex => InstFlags::READS_MEMORY,
            NeonLd1Post => InstFlags::READS_MEMORY,
            NeonLdpQPost => InstFlags::READS_MEMORY,

            // Volatile loads are observable accesses (MMIO / signal-visible
            // memory). READS_MEMORY alone is insufficient: a dead-result pass
            // may otherwise replace the instruction with Nop. Keep the
            // side-effect bit even though the hardware encoding is identical
            // to the corresponding plain load.
            VolatileLdrRI | VolatileLdrbRI | VolatileLdrhRI => {
                InstFlags::READS_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS)
            }

            // Memory stores
            StrRI | StrbRI | StrhRI | StrRO => {
                InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS)
            }
            StrPreIndex | StrPostIndex => {
                InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS)
            }
            STRWui | STRXui | STRSui | STRDui => {
                InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS)
            }
            StpRI | StpPreIndex => InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS),
            NeonSt1Post => InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS),
            NeonStpQPost => InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS),

            // Volatile stores are observable writes. They use distinct
            // opcodes so effect-aware passes cannot treat them as ordinary
            // memory traffic even though their encodings are byte-identical.
            VolatileStrRI | VolatileStrbRI | VolatileStrhRI => {
                InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS)
            }

            // Atomic loads (load-acquire): read memory with ordering side effect
            Ldar | Ldarb | Ldarh => InstFlags::READS_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS),

            // Atomic stores (store-release): write memory with ordering side effect
            Stlr | Stlrb | Stlrh => InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS),

            // Atomic read-modify-write (LSE): read AND write memory, always side-effecting
            Ldadd | Ldadda | Ldaddal | Ldaddl | Ldclr | Ldclra | Ldclral | Ldclrl | Ldeor
            | Ldeora | Ldeoral | Ldeorl | Ldset | Ldseta | Ldsetal | Ldsetl | Ldsmax | Ldsmaxa
            | Ldsmaxal | Ldsmaxl | Ldsmin | Ldsmina | Ldsminal | Ldsminl | Ldumax | Ldumaxa
            | Ldumaxal | Ldumaxl | Ldumin | Ldumina | Lduminal | Lduminl | Swp | Swpa | Swpal
            | Swpl => InstFlags::READS_MEMORY
                .union(InstFlags::WRITES_MEMORY)
                .union(InstFlags::HAS_SIDE_EFFECTS),

            // Compare-and-swap (LSE): read AND write memory, always side-effecting
            Cas | Casa | Casal | Casl => InstFlags::READS_MEMORY
                .union(InstFlags::WRITES_MEMORY)
                .union(InstFlags::HAS_SIDE_EFFECTS),

            // Exclusive load/store (LL/SC legacy path)
            Ldaxr => InstFlags::READS_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS),
            Stlxr => InstFlags::WRITES_MEMORY.union(InstFlags::HAS_SIDE_EFFECTS),

            // Memory barriers: pure side effects (enforce ordering)
            Dmb | Dsb | Isb => InstFlags::HAS_SIDE_EFFECTS,

            // System register read: treat as side-effecting so optimization
            // passes never reorder it across memory ops or speculate it. The
            // opcode covers all sysregs; only some (e.g. TPIDR_EL0) are
            // thread-stable, and the optimizer has no way to know which.
            Mrs => InstFlags::HAS_SIDE_EFFECTS,

            // Synchronous trap.
            Brk => InstFlags::HAS_SIDE_EFFECTS,

            // Shifted immediate arithmetic: same default semantics as AddRI.
            AddRIShift12 => InstFlags::EMPTY,

            // Pseudo-instructions
            Phi => InstFlags::IS_PSEUDO,
            StackAlloc => InstFlags::IS_PSEUDO.union(InstFlags::HAS_SIDE_EFFECTS),
            Copy => InstFlags::IS_PSEUDO,
            Nop => InstFlags::IS_PSEUDO,

            // Emission-time alignment padding: a REAL encoded NOP (not pseudo,
            // so every offset walk counts it). HAS_SIDE_EFFECTS keeps any late
            // pass from deleting or reordering the padding it did not create.
            AlignNop => InstFlags::HAS_SIDE_EFFECTS,

            // Compare/test (set condition flags = side effect)
            CmpRR | CmpRI | CMPWrr | CMPXrr | CMPWri | CMPXri | Tst | Fcmp => {
                InstFlags::HAS_SIDE_EFFECTS
            }

            // Checked arithmetic: produce a result AND set flags (side effect)
            AddsRR | AddsRI | SubsRR | SubsRI => InstFlags::HAS_SIDE_EFFECTS,

            // i128 multi-register: ADC/SBC read NZCV flags from preceding ADDS/SUBS
            Adc | Sbc => InstFlags::HAS_SIDE_EFFECTS,

            // Trap/guard pseudo-instructions: control-flowing side effects
            // until proof opts remove them or lowering/encoding materializes a trap.
            TrapOverflow => InstFlags::IS_BRANCH
                .union(InstFlags::IS_TERMINATOR)
                .union(InstFlags::HAS_SIDE_EFFECTS),
            TrapBoundsCheck => InstFlags::IS_BRANCH
                .union(InstFlags::IS_TERMINATOR)
                .union(InstFlags::HAS_SIDE_EFFECTS),
            TrapBoundsCheckExact => InstFlags::IS_BRANCH
                .union(InstFlags::IS_TERMINATOR)
                .union(InstFlags::HAS_SIDE_EFFECTS),
            TrapNull => InstFlags::IS_BRANCH
                .union(InstFlags::IS_TERMINATOR)
                .union(InstFlags::HAS_SIDE_EFFECTS),
            TrapNullIfZero => InstFlags::IS_BRANCH
                .union(InstFlags::IS_TERMINATOR)
                .union(InstFlags::HAS_SIDE_EFFECTS),
            TrapDivZero => InstFlags::IS_BRANCH
                .union(InstFlags::IS_TERMINATOR)
                .union(InstFlags::HAS_SIDE_EFFECTS),
            TrapDivZeroIfZero => InstFlags::IS_BRANCH
                .union(InstFlags::IS_TERMINATOR)
                .union(InstFlags::HAS_SIDE_EFFECTS),
            TrapShiftRange => InstFlags::IS_BRANCH
                .union(InstFlags::IS_TERMINATOR)
                .union(InstFlags::HAS_SIDE_EFFECTS),
            TrapShiftRangeIfOOB => InstFlags::IS_BRANCH
                .union(InstFlags::IS_TERMINATOR)
                .union(InstFlags::HAS_SIDE_EFFECTS),
            TrapOverflowExact => InstFlags::IS_BRANCH
                .union(InstFlags::IS_TERMINATOR)
                .union(InstFlags::HAS_SIDE_EFFECTS),

            // Reference counting: side effects (modify refcount in memory)
            Retain => InstFlags::HAS_SIDE_EFFECTS
                .union(InstFlags::READS_MEMORY)
                .union(InstFlags::WRITES_MEMORY),
            Release => InstFlags::HAS_SIDE_EFFECTS
                .union(InstFlags::READS_MEMORY)
                .union(InstFlags::WRITES_MEMORY),

            // Everything else: pure computation, no flags
            _ => InstFlags::EMPTY,
        }
    }

    /// Returns true if this is a pseudo-instruction with no hardware encoding.
    pub fn is_pseudo(self) -> bool {
        matches!(
            self,
            Self::Phi
                | Self::StackAlloc
                | Self::Copy
                | Self::Nop
                | Self::TrapOverflow
                | Self::TrapBoundsCheck
                | Self::TrapBoundsCheckExact
                | Self::TrapNull
                | Self::TrapNullIfZero
                | Self::TrapDivZero
                | Self::TrapDivZeroIfZero
                | Self::TrapShiftRange
                | Self::TrapShiftRangeIfOOB
                | Self::TrapOverflowExact
                | Self::Retain
                | Self::Release
        )
    }

    /// Returns true if this is a phi instruction.
    pub fn is_phi(self) -> bool {
        matches!(self, Self::Phi)
    }

    // -- Generic instruction property queries --
    //
    // These enable optimization passes to operate on generic instruction
    // properties rather than matching target-specific opcode variants.
    // This is the foundation for multi-target optimization support.

    /// Returns true if this is a no-op instruction (can be deleted without
    /// affecting program semantics).
    pub fn is_nop(self) -> bool {
        matches!(self, Self::Nop)
    }

    /// Returns true if this is a register-to-register move (copy).
    ///
    /// Move instructions transfer a value from one register to another
    /// without modifying it. Includes both generic pseudo-moves and
    /// target-specific move variants.
    pub fn is_move(self) -> bool {
        matches!(
            self,
            Self::MovR | Self::Copy | Self::MOVWrr | Self::MOVXrr | Self::FmovFprFpr
        )
    }

    /// Returns true if this is a move-immediate instruction (loads a
    /// constant value into a register).
    pub fn is_move_imm(self) -> bool {
        matches!(
            self,
            Self::MovI | Self::Movz | Self::Movn | Self::MOVZWi | Self::MOVZXi
        )
    }

    /// Returns true if this is an unconditional branch (always transfers
    /// control, no fallthrough).
    pub fn is_unconditional_branch(self) -> bool {
        matches!(self, Self::B | Self::TailCall | Self::Br)
    }

    /// Returns true if this is a conditional branch (may or may not transfer
    /// control; has a fallthrough path).
    pub fn is_conditional_branch(self) -> bool {
        matches!(
            self,
            Self::BCond | Self::Bcc | Self::Cbz | Self::Cbnz | Self::Tbz | Self::Tbnz
        )
    }

    /// Returns true if this is a compare-and-branch-if-zero instruction.
    pub fn is_cbz(self) -> bool {
        matches!(self, Self::Cbz)
    }

    /// Returns true if this is a compare-and-branch-if-not-zero instruction.
    pub fn is_cbnz(self) -> bool {
        matches!(self, Self::Cbnz)
    }

    /// Returns true if this is a commutative operation (operand order does
    /// not affect the result).
    pub fn is_commutative(self) -> bool {
        matches!(
            self,
            Self::AddRR
                | Self::MulRR
                | Self::AndRR
                | Self::OrrRR
                | Self::EorRR
                | Self::FaddRR
                | Self::FmulRR
                | Self::FminnmRR
                | Self::FmaxnmRR
                | Self::NeonAddV
                | Self::NeonMulV
                | Self::NeonFaddV
                | Self::NeonFmulV
                | Self::NeonAndV
                | Self::NeonOrrV
                | Self::NeonEorV
                | Self::NeonSmaxV
                | Self::NeonSminV
                | Self::NeonUmaxV
                | Self::NeonUminV
        )
    }

    /// Returns true if this opcode produces a value (operand[0] is a def).
    ///
    /// Instructions that don't produce values: CMP, TST, STR, STP, branches,
    /// returns, NOP, calls, traps, and reference counting ops.
    pub fn produces_value(self) -> bool {
        use AArch64Opcode::*;
        match self {
            // Compare/test: set flags, no register def
            CmpRR | CmpRI | Tst | Fcmp | CMPWrr | CMPXrr | CMPWri | CMPXri => false,
            // Stores: write to memory, no register def
            StrRI | StrbRI | StrhRI | StrPreIndex | StrPostIndex | StpRI | StpPreIndex | StrRO
            | STRWui | STRXui | STRSui | STRDui | NeonSt1Post | NeonStpQPost => false,
            // Volatile stores produce no value (mirror the plain stores above);
            // the `_ => true` default would otherwise mark the stored-value
            // operand as a dead def and let a pass eliminate the store.
            VolatileStrRI | VolatileStrbRI | VolatileStrhRI => false,
            // Branches and returns: control flow, no register def
            B | TailCall | BCond | Bcc | Cbz | Cbnz | Tbz | Tbnz | Br | Ret => false,
            // Trap instructions and trap/guard pseudos: control flow, no register def
            Brk | TrapOverflow | TrapBoundsCheck | TrapBoundsCheckExact | TrapNull
            | TrapNullIfZero | TrapDivZero | TrapDivZeroIfZero | TrapShiftRange
            | TrapShiftRangeIfOOB | TrapOverflowExact => false,
            // Reference counting: side effects, no register def
            Retain | Release => false,
            // Architectural and emission-time padding NOPs: no def.
            Nop | AlignNop => false,
            // Calls: produce result via implicit defs; for simple model, not a value producer
            Bl | Blr | BL | BLR => false,
            // Memory barriers: no register def
            Dmb | Dsb | Isb => false,
            // Atomic stores: no register def for the store itself
            Stlr | Stlrb | Stlrh | Stlxr => false,
            // Everything else produces a value in operand[0]
            _ => true,
        }
    }
}

// ---------------------------------------------------------------------------
// InstFlags (manual bitflags, no external crate)
// ---------------------------------------------------------------------------

/// Instruction property flags, packed as a u16 bitfield.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstFlags(u16);

impl InstFlags {
    pub const EMPTY: Self = Self(0);
    pub const IS_CALL: Self = Self(0x01);
    pub const IS_BRANCH: Self = Self(0x02);
    pub const IS_RETURN: Self = Self(0x04);
    pub const IS_TERMINATOR: Self = Self(0x08);
    pub const HAS_SIDE_EFFECTS: Self = Self(0x10);
    pub const IS_PSEUDO: Self = Self(0x20);
    pub const READS_MEMORY: Self = Self(0x40);
    pub const WRITES_MEMORY: Self = Self(0x80);
    pub const IS_PHI: Self = Self(0x100);
    /// Proof-guided: this memory instruction has been proven safe to reorder
    /// past other memory operations. Set by the ValidBorrow proof optimization.
    pub const PROOF_REORDERABLE: Self = Self(0x200);
    /// Semantic provenance: this instruction participates in the logical
    /// parallel assignment that establishes physical ABI argument registers
    /// for the immediately following call.
    ///
    /// This is deliberately metadata, not an encoding property.  Late
    /// AArch64 call-argument repair uses it to distinguish the logical
    /// parallel assignment emitted by call lowering from sequential spill and
    /// frame-materialization moves that happen to be adjacent to a call.
    pub const IS_CALL_ARG_SETUP: Self = Self(0x400);
    /// Metadata (NOT an encoding property): this direct call targets a function
    /// the module-level purity fixpoint proved side-effect-free and independent
    /// of mutable global state (see `trust-cg-lower`'s
    /// `compute_structural_pure_func_ids`). It is set only when the frontend
    /// purity analysis is enabled (`TCG_PURE_FN_ANALYSIS`) and is read ONLY by
    /// the x86 LICM pure-call cluster-hoist tier (gated behind
    /// `TCG_PURE_CALL_HOIST`). No other pass consumes it, so a call carrying this
    /// flag is otherwise treated exactly like any other call (its
    /// `HAS_SIDE_EFFECTS`/barrier flags are deliberately left intact — this flag
    /// enables ONLY the explicit, gated hoist, never implicit DCE/reordering).
    pub const PURE_CALL_HOISTABLE: Self = Self(0x800);
    /// Semantic provenance: this `FmaddRR` came from LLVM's fusion-licensed
    /// `llvm.fmuladd` carrier, whose contract permits either fused or separate
    /// multiply/add rounding. `UnfuseSerialFma` requires this bit before it may
    /// replace `FmaddRR` with `FmulRR` + `FaddRR`.
    ///
    /// Strict IEEE `llvm.fma` instructions never carry this bit. This is
    /// metadata, not an encoding property; it must be removed if the opcode is
    /// rewritten to anything other than `FmaddRR`.
    pub const FMULADD_MAY_UNFUSE: Self = Self(0x1000);
    /// Metadata (NOT an encoding property): this direct `Bl` targets a libm
    /// entry point that the LLVM importer proved side-effect-free at THIS call
    /// site's origin: the call was lowered from a `llvm.<fn>.f64/.f32` math
    /// intrinsic whose declaration carries `speculatable willreturn nounwind
    /// memory(none)`, and the module contains no other (plain, unlicensed)
    /// reference to the same libm symbol. Licensed per-module by the importer
    /// (see `trust-cg-llvm-import` libm purity licensing) and stamped by
    /// AArch64 ISel from `LirFunction::libm_pure_callees`.
    ///
    /// Read ONLY by the aarch64 `loop-dead-pure-sink` pass (gated behind
    /// `TCG_NO_LOOP_DEAD_SINK`). The call's conservative
    /// `HAS_SIDE_EFFECTS`/`READS_MEMORY`/`WRITES_MEMORY` flags are deliberately
    /// left intact — this bit enables ONLY that explicit, gated transform,
    /// never implicit DCE/reordering (mirrors `PURE_CALL_HOISTABLE`).
    pub const LIBM_PURE_CALL: Self = Self(0x2000);

    /// Returns true if all bits in `other` are set in `self`.
    #[inline]
    pub const fn contains(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }

    /// Set all bits in `other`.
    #[inline]
    pub fn insert(&mut self, other: Self) {
        self.0 |= other.0;
    }

    /// Clear all bits in `other`.
    #[inline]
    pub fn remove(&mut self, other: Self) {
        self.0 &= !other.0;
    }

    /// Union of two flag sets.
    #[inline]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Intersection of two flag sets.
    #[inline]
    pub const fn intersection(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    /// Returns true if no flags are set.
    #[inline]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Raw bits.
    #[inline]
    pub const fn bits(self) -> u16 {
        self.0
    }

    /// Create from raw bits (e.g., `InstFlags::from_bits(IS_CALL | IS_BRANCH)`).
    ///
    /// Used by crates that construct InstFlags from u16 constants
    /// (e.g., regalloc test helpers, pipeline adapters).
    #[inline]
    pub const fn from_bits(bits: u16) -> Self {
        Self(bits)
    }

    // -- Convenience query methods --
    //
    // These duplicate the methods on MachInst but operate on InstFlags directly.
    // Used by the register allocator which stores InstFlags separately from
    // opcode/operands and needs to query flags without a MachInst wrapper.

    #[inline]
    pub const fn is_call(self) -> bool {
        self.contains(Self::IS_CALL)
    }

    #[inline]
    pub const fn is_branch(self) -> bool {
        self.contains(Self::IS_BRANCH)
    }

    #[inline]
    pub const fn is_return(self) -> bool {
        self.contains(Self::IS_RETURN)
    }

    #[inline]
    pub const fn is_terminator(self) -> bool {
        self.contains(Self::IS_TERMINATOR)
    }

    #[inline]
    pub const fn has_side_effects(self) -> bool {
        self.contains(Self::HAS_SIDE_EFFECTS)
    }

    #[inline]
    pub const fn is_pseudo(self) -> bool {
        self.contains(Self::IS_PSEUDO)
    }

    #[inline]
    pub const fn reads_memory(self) -> bool {
        self.contains(Self::READS_MEMORY)
    }

    #[inline]
    pub const fn writes_memory(self) -> bool {
        self.contains(Self::WRITES_MEMORY)
    }

    #[inline]
    pub const fn is_phi(self) -> bool {
        self.contains(Self::IS_PHI)
    }

    #[inline]
    pub const fn is_call_arg_setup(self) -> bool {
        self.contains(Self::IS_CALL_ARG_SETUP)
    }

    /// Whether an `FmaddRR` is licensed to become separate multiply/add ops.
    #[inline]
    pub const fn fmuladd_may_unfuse(self) -> bool {
        self.contains(Self::FMULADD_MAY_UNFUSE)
    }
}

impl Default for InstFlags {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl core::ops::BitOr for InstFlags {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl core::ops::BitAnd for InstFlags {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self {
        Self(self.0 & rhs.0)
    }
}

impl core::ops::BitOrAssign for InstFlags {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl core::fmt::Debug for InstFlags {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut first = true;
        let flags = [
            (Self::IS_CALL, "IS_CALL"),
            (Self::IS_BRANCH, "IS_BRANCH"),
            (Self::IS_RETURN, "IS_RETURN"),
            (Self::IS_TERMINATOR, "IS_TERMINATOR"),
            (Self::HAS_SIDE_EFFECTS, "HAS_SIDE_EFFECTS"),
            (Self::IS_PSEUDO, "IS_PSEUDO"),
            (Self::READS_MEMORY, "READS_MEMORY"),
            (Self::WRITES_MEMORY, "WRITES_MEMORY"),
            (Self::IS_PHI, "IS_PHI"),
            (Self::PROOF_REORDERABLE, "PROOF_REORDERABLE"),
            (Self::IS_CALL_ARG_SETUP, "IS_CALL_ARG_SETUP"),
            (Self::PURE_CALL_HOISTABLE, "PURE_CALL_HOISTABLE"),
            (Self::FMULADD_MAY_UNFUSE, "FMULADD_MAY_UNFUSE"),
            (Self::LIBM_PURE_CALL, "LIBM_PURE_CALL"),
        ];
        write!(f, "InstFlags(")?;
        for (flag, name) in &flags {
            if self.contains(*flag) {
                if !first {
                    write!(f, " | ")?;
                }
                write!(f, "{}", name)?;
                first = false;
            }
        }
        if first {
            write!(f, "EMPTY")?;
        }
        write!(f, ")")
    }
}

// ---------------------------------------------------------------------------
// ProofAnnotation
// ---------------------------------------------------------------------------

/// Proof annotations from trust_ir that enable optimizations no other compiler can do.
///
/// These annotations represent formally verified preconditions that the trust_ir
/// frontend has proven about program values. The Trust Codegen backend consumes these
/// proofs only through exact proof-guard carriers; generic, already-lowered
/// compare/branch idioms are not proof consumers.
///
/// Each annotation corresponds to a specific optimization opportunity:
/// - `NoOverflow`/`NoSignedOverflow` → eliminate signed overflow checks
/// - `NoUnsignedOverflow` → eliminate unsigned no-wrap checks
/// - `InBounds` → eliminate exact bounds proof guards
/// - `NotNull` → eliminate null pointer checks
/// - `ValidBorrow` → enable load/store reordering (refined alias analysis)
/// - `PositiveRefCount` → eliminate redundant retain/release pairs
/// - `NonZeroDivisor` → eliminate exact division-by-zero proof guards
/// - `ValidShift` → eliminate shift-amount range checks
/// - `Pure` → aggressive CSE/LICM of proven-pure memory operations
/// - `Associative` → parallel reduction trees, operation reordering
/// - `Commutative` → operand canonicalization, parallel reduction
/// - `Idempotent` → redundant application elimination
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProofAnnotation {
    /// Legacy trust_ir has proven this arithmetic operation cannot overflow.
    /// Signed-compatible: consumes the same machine carriers as
    /// [`ProofAnnotation::NoSignedOverflow`].
    NoOverflow,

    /// trust_ir has proven this arithmetic operation cannot signed-overflow.
    /// Enables: ADDS/SUBS → ADD/SUB, remove TrapOverflow or B.VS guards.
    NoSignedOverflow,

    /// trust_ir has proven this arithmetic operation cannot unsigned-overflow
    /// or unsigned-underflow.
    /// Enables: ADDS+B.HS and SUBS+B.LO → ADD/SUB, remove the B.cond guard.
    /// Does not consume TrapOverflow, which is signed-compatible.
    NoUnsignedOverflow,

    /// trust_ir has proven this array access index is within bounds.
    /// Enables: remove exact ExactInBounds/TrapBoundsCheckExact bounds guard.
    /// Legacy CMP+B.HS/TrapBoundsCheck shapes are not InBounds consumers.
    InBounds,

    /// trust_ir has proven this pointer is not null.
    /// Enables: remove exact TrapNullIfZero pointer guard.
    NotNull,

    /// trust_ir has proven this borrow/reference is valid (no aliasing violations).
    /// Enables: load/store reordering past other memory operations.
    ValidBorrow,

    /// trust_ir has proven the reference count is positive (object is live).
    /// Enables: eliminate redundant retain/release pairs.
    PositiveRefCount,

    /// trust_ir has proven the divisor is non-zero.
    /// Enables: remove exact CmpRI[NonZeroDivisor] + TrapDivZero guard
    /// before UDIV/SDIV.
    /// Legacy CBZ divisor shapes are not NonZeroDivisor consumers.
    NonZeroDivisor,

    /// trust_ir has proven the shift amount is in [0, bitwidth).
    /// Enables: remove CMP+B.GE range check before LSL/LSR/ASR.
    ValidShift,

    /// trust_ir has proven this operation is pure (no observable side effects).
    /// Enables: aggressive CSE of loads, LICM of memory operations.
    /// A load with Pure proof can be treated as a pure computation for
    /// CSE purposes: if two loads from the same address exist and the
    /// address is proven pure (immutable), the second load is redundant.
    Pure,

    /// trust_ir has proven this operation is associative: (a op b) op c = a op (b op c).
    /// Enables: parallel reduction trees, operation reordering for vectorization.
    Associative,

    /// trust_ir has proven this operation is commutative: a op b = b op a.
    /// Enables: operand canonicalization, parallel reduction, vectorization.
    Commutative,

    /// trust_ir has proven this operation is idempotent: f(f(x)) = f(x).
    /// Enables: redundant application elimination.
    Idempotent,
}

// ---------------------------------------------------------------------------
// ProofFact
// ---------------------------------------------------------------------------

/// Multi-fact proof vocabulary for ay/TY facts that need payloads or can
/// coexist with the legacy single-value [`ProofAnnotation`] field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProofFact {
    /// Pointer arithmetic or memory address is proven in-bounds for its allocation.
    InBounds,
    /// Pointer/value is known not to alias other in-scope pointers.
    NoAlias,
    /// Pointer/value is aligned to the given byte boundary.
    Aligned(u64),
    /// Value evolves monotonically.
    Monotonic,
    /// Function/instruction cannot panic.
    NoPanic,
    /// Value is neither undef nor poison.
    NoUndef,
    /// Operation is deterministic.
    Deterministic,
    /// Function/instruction is known to terminate.
    Terminates,
    /// Operation is data-race-free.
    DataRaceFree,
    /// Deallocation is valid for the referenced allocation.
    ValidDealloc,
    /// Immutable lookup table memory-role proof.
    ReadonlyTable,
    /// Append-only buffer memory-role proof.
    AppendOnlyBuffer,
    /// Threadgroup-local atomic set insertion proof.
    AtomicSetInsert,
    /// Loop iterations are independent and parallelizable.
    ParallelMap,
    /// Loop iteration count is statically bounded by this maximum.
    BoundedLoop(u64),
    /// GPU thread-divergence classification.
    DivergenceClass(ProofDivergence),
}

/// ay/TY thread-divergence proof payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProofDivergence {
    /// All lanes execute the same control-flow path.
    Uniform,
    /// Minor bounded divergence that lane masking can tolerate.
    Low,
    /// High/unpredictable divergence; consumers should fall back conservatively.
    High,
}

impl ProofFact {
    /// Stable fact name for diagnostics and golden tests.
    pub fn stable_name(&self) -> &'static str {
        match self {
            ProofFact::InBounds => "InBounds",
            ProofFact::NoAlias => "NoAlias",
            ProofFact::Aligned(_) => "Aligned",
            ProofFact::Monotonic => "Monotonic",
            ProofFact::NoPanic => "NoPanic",
            ProofFact::NoUndef => "NoUndef",
            ProofFact::Deterministic => "Deterministic",
            ProofFact::Terminates => "Terminates",
            ProofFact::DataRaceFree => "DataRaceFree",
            ProofFact::ValidDealloc => "ValidDealloc",
            ProofFact::ReadonlyTable => "ReadonlyTable",
            ProofFact::AppendOnlyBuffer => "AppendOnlyBuffer",
            ProofFact::AtomicSetInsert => "AtomicSetInsert",
            ProofFact::ParallelMap => "ParallelMap",
            ProofFact::BoundedLoop(_) => "BoundedLoop",
            ProofFact::DivergenceClass(_) => "DivergenceClass",
        }
    }

    /// Return the bounded-loop maximum trip count from a fact list, if present.
    pub fn bounded_loop_bound(facts: &[ProofFact]) -> Option<u64> {
        facts.iter().find_map(|fact| match fact {
            ProofFact::BoundedLoop(bound) => Some(*bound),
            _ => None,
        })
    }

    /// Return the thread-divergence proof from a fact list, if present.
    pub fn divergence(facts: &[ProofFact]) -> Option<ProofDivergence> {
        facts.iter().find_map(|fact| match fact {
            ProofFact::DivergenceClass(divergence) => Some(*divergence),
            _ => None,
        })
    }
}

impl ProofAnnotation {
    /// Conservatively merge two optional proof annotations.
    ///
    /// Used by optimization passes to combine proof annotations when
    /// instructions are replaced or eliminated:
    /// - If both are `None`, returns `None`.
    /// - If one is `Some` and the other is `None`, returns the `Some`.
    /// - If both are `Some` and equal, returns that annotation.
    /// - If both are `Some` but different, returns `None` (conservative:
    ///   we cannot combine proofs of different properties).
    pub fn merge(
        a: Option<ProofAnnotation>,
        b: Option<ProofAnnotation>,
    ) -> Option<ProofAnnotation> {
        match (a, b) {
            (None, None) => None,
            (Some(proof), None) | (None, Some(proof)) => Some(proof),
            (Some(x), Some(y)) if x == y => Some(x),
            (Some(_), Some(_)) => None,
        }
    }
}

// ---------------------------------------------------------------------------
// SourceLoc — source location for debug info
// ---------------------------------------------------------------------------

/// Source location for DWARF debug info.
///
/// Tracks the original source file, line, and column for a machine instruction.
/// Populated from trust_ir `SourceSpan` during instruction selection and preserved
/// through optimization/regalloc for DWARF line number program emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SourceLoc {
    /// Source file index (0-based, matches trust_ir SourceSpan.file).
    pub file: u32,
    /// Source line number (1-based).
    pub line: u32,
    /// Source column number (0 = unknown).
    pub col: u32,
}

// ---------------------------------------------------------------------------
// MachInst
// ---------------------------------------------------------------------------

/// A single machine instruction.
///
/// Operands are stored inline in a Vec. Implicit defs/uses are static slices
/// (e.g., call instructions implicitly clobber caller-saved registers).
///
/// The `proof` field carries optional trust_ir proof annotations that enable
/// proof-consuming optimizations unique to Trust Codegen.
#[derive(Debug, Clone)]
pub struct MachInst {
    pub opcode: AArch64Opcode,
    pub operands: Vec<MachOperand>,
    pub implicit_defs: &'static [PReg],
    pub implicit_uses: &'static [PReg],
    pub flags: InstFlags,
    /// Optional proof annotation from trust_ir. When present, indicates that
    /// the trust_ir frontend has formally verified a property about this
    /// instruction's operands, enabling proof-consuming optimizations.
    pub proof: Option<ProofAnnotation>,
    /// Optional source location from trust_ir for DWARF debug info.
    /// Populated from trust_ir `SourceSpan` during ISel, preserved through
    /// optimization and register allocation for line number program emission.
    pub source_loc: Option<SourceLoc>,
}

impl MachInst {
    /// Create a new instruction with default flags for the opcode.
    pub fn new(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> Self {
        Self {
            flags: opcode.default_flags(),
            opcode,
            operands,
            implicit_defs: &[],
            implicit_uses: &[],
            proof: None,
            source_loc: None,
        }
    }

    /// Create a new instruction with explicit flags.
    pub fn with_flags(opcode: AArch64Opcode, operands: Vec<MachOperand>, flags: InstFlags) -> Self {
        Self {
            opcode,
            operands,
            implicit_defs: &[],
            implicit_uses: &[],
            flags,
            proof: None,
            source_loc: None,
        }
    }

    /// Attach a proof annotation to this instruction.
    pub fn with_proof(mut self, proof: ProofAnnotation) -> Self {
        self.proof = Some(proof);
        self
    }

    /// Attach a source location for DWARF debug info.
    pub fn with_source_loc(mut self, loc: SourceLoc) -> Self {
        self.source_loc = Some(loc);
        self
    }

    /// Set implicit register definitions (clobbers).
    pub fn with_implicit_defs(mut self, defs: &'static [PReg]) -> Self {
        self.implicit_defs = defs;
        self
    }

    /// Set implicit register uses.
    pub fn with_implicit_uses(mut self, uses: &'static [PReg]) -> Self {
        self.implicit_uses = uses;
        self
    }

    // -- Flag query convenience methods --

    #[inline]
    pub fn is_call(&self) -> bool {
        self.flags.contains(InstFlags::IS_CALL)
    }

    #[inline]
    pub fn is_branch(&self) -> bool {
        self.flags.contains(InstFlags::IS_BRANCH)
    }

    #[inline]
    pub fn is_return(&self) -> bool {
        self.flags.contains(InstFlags::IS_RETURN)
    }

    #[inline]
    pub fn is_terminator(&self) -> bool {
        self.flags.contains(InstFlags::IS_TERMINATOR)
    }

    #[inline]
    pub fn has_side_effects(&self) -> bool {
        self.flags.contains(InstFlags::HAS_SIDE_EFFECTS)
    }

    #[inline]
    pub fn is_pseudo(&self) -> bool {
        self.flags.contains(InstFlags::IS_PSEUDO)
    }

    #[inline]
    pub fn reads_memory(&self) -> bool {
        self.flags.contains(InstFlags::READS_MEMORY)
    }

    #[inline]
    pub fn writes_memory(&self) -> bool {
        self.flags.contains(InstFlags::WRITES_MEMORY)
    }

    // -- Generic instruction property queries (delegates to opcode) --

    /// Returns true if this is a no-op instruction.
    #[inline]
    pub fn is_nop(&self) -> bool {
        self.opcode.is_nop()
    }

    /// Returns true if this is a register-to-register move/copy.
    #[inline]
    pub fn is_move(&self) -> bool {
        self.opcode.is_move()
    }

    /// Returns true if this is a move-immediate instruction.
    #[inline]
    pub fn is_move_imm(&self) -> bool {
        self.opcode.is_move_imm()
    }

    /// Returns true if this is an unconditional branch.
    #[inline]
    pub fn is_unconditional_branch(&self) -> bool {
        self.opcode.is_unconditional_branch()
    }

    /// Returns true if this is a conditional branch.
    #[inline]
    pub fn is_conditional_branch(&self) -> bool {
        self.opcode.is_conditional_branch()
    }

    /// Returns true if this is a commutative operation.
    #[inline]
    pub fn is_commutative(&self) -> bool {
        self.opcode.is_commutative()
    }

    /// Returns true if this instruction produces a value (operand[0] is a def).
    #[inline]
    pub fn produces_value(&self) -> bool {
        self.opcode.produces_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::operand::MachOperand;
    use crate::regs::{PReg, RegClass, VReg, X0, X1, X30};
    use crate::types::BlockId;

    // ---- AArch64Opcode flag tests ----

    #[test]
    fn no_op_instructions_do_not_claim_a_destination() {
        assert!(!AArch64Opcode::Nop.produces_value());
        assert!(!AArch64Opcode::AlignNop.produces_value());
    }

    #[test]
    fn volatile_opcodes_are_appended_after_the_preexisting_surface() {
        assert_eq!(
            AArch64Opcode::VolatileLdrRI as usize,
            AArch64Opcode::NeonFmlaLaneV as usize + 1
        );
        assert_eq!(
            AArch64Opcode::VolatileStrhRI as usize,
            AArch64Opcode::VolatileLdrRI as usize + 5
        );
    }

    #[test]
    fn branch_opcodes_have_branch_and_terminator_flags() {
        let branch_ops = [
            AArch64Opcode::B,
            AArch64Opcode::BCond,
            AArch64Opcode::Cbz,
            AArch64Opcode::Cbnz,
            AArch64Opcode::Tbz,
            AArch64Opcode::Tbnz,
            AArch64Opcode::Br,
        ];
        for op in &branch_ops {
            let flags = op.default_flags();
            assert!(
                flags.contains(InstFlags::IS_BRANCH),
                "{:?} should have IS_BRANCH",
                op
            );
            assert!(
                flags.contains(InstFlags::IS_TERMINATOR),
                "{:?} should have IS_TERMINATOR",
                op
            );
        }
    }

    #[test]
    fn call_opcodes_have_call_and_side_effect_flags() {
        let call_ops = [AArch64Opcode::Bl, AArch64Opcode::Blr];
        for op in &call_ops {
            let flags = op.default_flags();
            assert!(
                flags.contains(InstFlags::IS_CALL),
                "{:?} should have IS_CALL",
                op
            );
            assert!(
                flags.contains(InstFlags::HAS_SIDE_EFFECTS),
                "{:?} should have HAS_SIDE_EFFECTS",
                op
            );
            assert!(
                !flags.contains(InstFlags::IS_BRANCH),
                "{:?} should NOT have IS_BRANCH",
                op
            );
        }
    }

    #[test]
    fn ret_opcode_has_return_and_terminator_flags() {
        let flags = AArch64Opcode::Ret.default_flags();
        assert!(flags.contains(InstFlags::IS_RETURN));
        assert!(flags.contains(InstFlags::IS_TERMINATOR));
        assert!(!flags.contains(InstFlags::IS_CALL));
        assert!(!flags.contains(InstFlags::IS_BRANCH));
    }

    #[test]
    fn load_opcodes_have_reads_memory() {
        let load_ops = [
            AArch64Opcode::LdrRI,
            AArch64Opcode::LdrPreIndex,
            AArch64Opcode::LdrPostIndex,
            AArch64Opcode::LdrLiteral,
            AArch64Opcode::LdpRI,
            AArch64Opcode::LdpPostIndex,
        ];
        for op in &load_ops {
            let flags = op.default_flags();
            assert!(
                flags.contains(InstFlags::READS_MEMORY),
                "{:?} should have READS_MEMORY",
                op
            );
            assert!(
                !flags.contains(InstFlags::WRITES_MEMORY),
                "{:?} should NOT have WRITES_MEMORY",
                op
            );
            if matches!(op, AArch64Opcode::LdrPreIndex | AArch64Opcode::LdrPostIndex) {
                assert!(
                    flags.contains(InstFlags::HAS_SIDE_EFFECTS),
                    "{:?} should have HAS_SIDE_EFFECTS for base writeback",
                    op
                );
            }
        }
    }

    #[test]
    fn volatile_memory_opcodes_are_observable_side_effects() {
        for op in [
            AArch64Opcode::VolatileLdrRI,
            AArch64Opcode::VolatileLdrbRI,
            AArch64Opcode::VolatileLdrhRI,
        ] {
            let flags = op.default_flags();
            assert!(flags.contains(InstFlags::READS_MEMORY), "{op:?}");
            assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS), "{op:?}");
            assert!(!flags.contains(InstFlags::WRITES_MEMORY), "{op:?}");
        }

        for op in [
            AArch64Opcode::VolatileStrRI,
            AArch64Opcode::VolatileStrbRI,
            AArch64Opcode::VolatileStrhRI,
        ] {
            let flags = op.default_flags();
            assert!(flags.contains(InstFlags::WRITES_MEMORY), "{op:?}");
            assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS), "{op:?}");
            assert!(!flags.contains(InstFlags::READS_MEMORY), "{op:?}");
        }
    }

    #[test]
    fn store_opcodes_have_writes_memory_and_side_effects() {
        let store_ops = [
            AArch64Opcode::StrRI,
            AArch64Opcode::StrPreIndex,
            AArch64Opcode::StrPostIndex,
            AArch64Opcode::StpRI,
            AArch64Opcode::StpPreIndex,
        ];
        for op in &store_ops {
            let flags = op.default_flags();
            assert!(
                flags.contains(InstFlags::WRITES_MEMORY),
                "{:?} should have WRITES_MEMORY",
                op
            );
            assert!(
                flags.contains(InstFlags::HAS_SIDE_EFFECTS),
                "{:?} should have HAS_SIDE_EFFECTS",
                op
            );
        }
    }

    #[test]
    fn pseudo_opcodes_have_pseudo_flag() {
        let pseudo_ops = [
            AArch64Opcode::Phi,
            AArch64Opcode::StackAlloc,
            AArch64Opcode::Nop,
        ];
        for op in &pseudo_ops {
            let flags = op.default_flags();
            assert!(
                flags.contains(InstFlags::IS_PSEUDO),
                "{:?} should have IS_PSEUDO",
                op
            );
        }
    }

    #[test]
    fn is_pseudo_method() {
        assert!(AArch64Opcode::Phi.is_pseudo());
        assert!(AArch64Opcode::StackAlloc.is_pseudo());
        assert!(AArch64Opcode::Nop.is_pseudo());
        assert!(!AArch64Opcode::AddRR.is_pseudo());
        assert!(!AArch64Opcode::B.is_pseudo());
        assert!(!AArch64Opcode::Ret.is_pseudo());
    }

    #[test]
    fn is_phi_method() {
        assert!(AArch64Opcode::Phi.is_phi());
        assert!(!AArch64Opcode::Nop.is_phi());
        assert!(!AArch64Opcode::AddRR.is_phi());
    }

    #[test]
    fn pure_arithmetic_has_empty_flags() {
        let pure_ops = [
            AArch64Opcode::AddRR,
            AArch64Opcode::AddRI,
            AArch64Opcode::AddRIShift12,
            AArch64Opcode::SubRR,
            AArch64Opcode::SubRI,
            AArch64Opcode::MulRR,
            AArch64Opcode::SDiv,
            AArch64Opcode::UDiv,
            AArch64Opcode::Neg,
            AArch64Opcode::AndRR,
            AArch64Opcode::OrrRR,
            AArch64Opcode::EorRR,
            AArch64Opcode::OrnRR,
            AArch64Opcode::RorRI,
            AArch64Opcode::Rbit,
            AArch64Opcode::FnegRR,
            AArch64Opcode::MovR,
            AArch64Opcode::MovI,
        ];
        for op in &pure_ops {
            let flags = op.default_flags();
            assert!(
                flags.is_empty(),
                "{:?} should have EMPTY flags but has {:?}",
                op,
                flags
            );
        }
    }

    #[test]
    fn compare_opcodes_have_side_effects() {
        let cmp_ops = [
            AArch64Opcode::CmpRR,
            AArch64Opcode::CmpRI,
            AArch64Opcode::Tst,
            AArch64Opcode::Fcmp,
        ];
        for op in &cmp_ops {
            let flags = op.default_flags();
            assert!(
                flags.contains(InstFlags::HAS_SIDE_EFFECTS),
                "{:?} should have HAS_SIDE_EFFECTS",
                op
            );
        }
    }

    #[test]
    fn trap_null_if_zero_is_control_barrier() {
        let flags = AArch64Opcode::TrapNullIfZero.default_flags();
        assert!(flags.contains(InstFlags::IS_BRANCH));
        assert!(flags.contains(InstFlags::IS_TERMINATOR));
        assert!(flags.contains(InstFlags::HAS_SIDE_EFFECTS));
    }

    // ---- InstFlags bitwise operation tests ----

    #[test]
    fn instflags_empty() {
        let f = InstFlags::EMPTY;
        assert!(f.is_empty());
        assert_eq!(f.bits(), 0);
    }

    #[test]
    fn instflags_single_flag() {
        let f = InstFlags::IS_CALL;
        assert!(!f.is_empty());
        assert!(f.contains(InstFlags::IS_CALL));
        assert!(!f.contains(InstFlags::IS_BRANCH));
    }

    #[test]
    fn instflags_union() {
        let f = InstFlags::IS_CALL.union(InstFlags::HAS_SIDE_EFFECTS);
        assert!(f.contains(InstFlags::IS_CALL));
        assert!(f.contains(InstFlags::HAS_SIDE_EFFECTS));
        assert!(!f.contains(InstFlags::IS_BRANCH));
    }

    #[test]
    fn instflags_intersection() {
        let a = InstFlags::IS_CALL.union(InstFlags::HAS_SIDE_EFFECTS);
        let b = InstFlags::IS_CALL.union(InstFlags::IS_BRANCH);
        let c = a.intersection(b);
        assert!(c.contains(InstFlags::IS_CALL));
        assert!(!c.contains(InstFlags::HAS_SIDE_EFFECTS));
        assert!(!c.contains(InstFlags::IS_BRANCH));
    }

    #[test]
    fn instflags_insert() {
        let mut f = InstFlags::EMPTY;
        assert!(f.is_empty());
        f.insert(InstFlags::IS_CALL);
        assert!(f.contains(InstFlags::IS_CALL));
        f.insert(InstFlags::IS_BRANCH);
        assert!(f.contains(InstFlags::IS_CALL));
        assert!(f.contains(InstFlags::IS_BRANCH));
    }

    #[test]
    fn instflags_remove() {
        let mut f = InstFlags::IS_CALL.union(InstFlags::IS_BRANCH);
        f.remove(InstFlags::IS_CALL);
        assert!(!f.contains(InstFlags::IS_CALL));
        assert!(f.contains(InstFlags::IS_BRANCH));
    }

    #[test]
    fn instflags_bitor_operator() {
        let f = InstFlags::IS_CALL | InstFlags::IS_BRANCH;
        assert!(f.contains(InstFlags::IS_CALL));
        assert!(f.contains(InstFlags::IS_BRANCH));
    }

    #[test]
    fn instflags_bitand_operator() {
        let a = InstFlags::IS_CALL | InstFlags::IS_BRANCH;
        let b = InstFlags::IS_CALL | InstFlags::IS_RETURN;
        let c = a & b;
        assert!(c.contains(InstFlags::IS_CALL));
        assert!(!c.contains(InstFlags::IS_BRANCH));
        assert!(!c.contains(InstFlags::IS_RETURN));
    }

    #[test]
    fn instflags_bitor_assign() {
        let mut f = InstFlags::IS_CALL;
        f |= InstFlags::IS_BRANCH;
        assert!(f.contains(InstFlags::IS_CALL));
        assert!(f.contains(InstFlags::IS_BRANCH));
    }

    #[test]
    fn instflags_default_is_empty() {
        let f = InstFlags::default();
        assert!(f.is_empty());
        assert_eq!(f, InstFlags::EMPTY);
    }

    #[test]
    fn instflags_contains_self() {
        let flags = [
            InstFlags::IS_CALL,
            InstFlags::IS_BRANCH,
            InstFlags::IS_RETURN,
            InstFlags::IS_TERMINATOR,
            InstFlags::HAS_SIDE_EFFECTS,
            InstFlags::IS_PSEUDO,
            InstFlags::READS_MEMORY,
            InstFlags::WRITES_MEMORY,
            InstFlags::IS_PHI,
        ];
        for f in &flags {
            assert!(f.contains(*f), "{:?} should contain itself", f);
        }
    }

    #[test]
    fn instflags_empty_contains_nothing() {
        let flags = [
            InstFlags::IS_CALL,
            InstFlags::IS_BRANCH,
            InstFlags::IS_RETURN,
            InstFlags::IS_TERMINATOR,
            InstFlags::HAS_SIDE_EFFECTS,
            InstFlags::IS_PSEUDO,
            InstFlags::READS_MEMORY,
            InstFlags::WRITES_MEMORY,
            InstFlags::IS_PHI,
        ];
        for f in &flags {
            assert!(!InstFlags::EMPTY.contains(*f));
        }
    }

    #[test]
    fn instflags_bit_values_are_distinct() {
        let flags = [
            InstFlags::IS_CALL,
            InstFlags::IS_BRANCH,
            InstFlags::IS_RETURN,
            InstFlags::IS_TERMINATOR,
            InstFlags::HAS_SIDE_EFFECTS,
            InstFlags::IS_PSEUDO,
            InstFlags::READS_MEMORY,
            InstFlags::WRITES_MEMORY,
            InstFlags::IS_PHI,
        ];
        for i in 0..flags.len() {
            for j in (i + 1)..flags.len() {
                assert_ne!(
                    flags[i].bits(),
                    flags[j].bits(),
                    "flags {:?} and {:?} have same bits",
                    flags[i],
                    flags[j]
                );
            }
        }
    }

    #[test]
    fn instflags_debug_empty() {
        let f = InstFlags::EMPTY;
        let s = format!("{:?}", f);
        assert!(s.contains("EMPTY"));
    }

    #[test]
    fn instflags_debug_single() {
        let f = InstFlags::IS_CALL;
        let s = format!("{:?}", f);
        assert!(s.contains("IS_CALL"));
        assert!(!s.contains("IS_BRANCH"));
    }

    #[test]
    fn instflags_debug_multiple() {
        let f = InstFlags::IS_CALL | InstFlags::HAS_SIDE_EFFECTS;
        let s = format!("{:?}", f);
        assert!(s.contains("IS_CALL"));
        assert!(s.contains("HAS_SIDE_EFFECTS"));
    }

    // ---- MachInst construction tests ----

    #[test]
    fn machinst_new_uses_default_flags() {
        let inst = MachInst::new(AArch64Opcode::AddRR, vec![]);
        assert_eq!(inst.opcode, AArch64Opcode::AddRR);
        assert!(inst.flags.is_empty()); // AddRR has empty default flags
        assert!(inst.operands.is_empty());
        assert!(inst.implicit_defs.is_empty());
        assert!(inst.implicit_uses.is_empty());
    }

    #[test]
    fn machinst_new_branch_has_correct_flags() {
        let inst = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(1))]);
        assert!(inst.is_branch());
        assert!(inst.is_terminator());
        assert!(!inst.is_call());
        assert!(!inst.is_return());
    }

    #[test]
    fn machinst_new_ret_has_correct_flags() {
        let inst = MachInst::new(AArch64Opcode::Ret, vec![]);
        assert!(inst.is_return());
        assert!(inst.is_terminator());
        assert!(!inst.is_branch());
        assert!(!inst.is_call());
    }

    #[test]
    fn machinst_with_flags_overrides_defaults() {
        let inst = MachInst::with_flags(AArch64Opcode::AddRR, vec![], InstFlags::HAS_SIDE_EFFECTS);
        assert!(inst.has_side_effects());
        assert!(!inst.is_call());
    }

    #[test]
    fn machinst_with_implicit_defs() {
        static DEFS: &[PReg] = &[X0, X1];
        let inst = MachInst::new(AArch64Opcode::Bl, vec![]).with_implicit_defs(DEFS);
        assert_eq!(inst.implicit_defs, DEFS);
        assert!(inst.implicit_uses.is_empty());
    }

    #[test]
    fn machinst_with_implicit_uses() {
        static USES: &[PReg] = &[X0];
        let inst = MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(USES);
        assert_eq!(inst.implicit_uses, USES);
        assert!(inst.implicit_defs.is_empty());
    }

    #[test]
    fn machinst_builder_chain() {
        static DEFS: &[PReg] = &[X0, X1];
        static USES: &[PReg] = &[X30];
        let inst = MachInst::new(AArch64Opcode::Blr, vec![MachOperand::PReg(X30)])
            .with_implicit_defs(DEFS)
            .with_implicit_uses(USES);
        assert!(inst.is_call());
        assert!(inst.has_side_effects());
        assert_eq!(inst.implicit_defs.len(), 2);
        assert_eq!(inst.implicit_uses.len(), 1);
        assert_eq!(inst.operands.len(), 1);
    }

    #[test]
    fn machinst_with_operands() {
        let v0 = VReg::new(0, RegClass::Gpr64);
        let v1 = VReg::new(1, RegClass::Gpr64);
        let inst = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(v0),
                MachOperand::VReg(v1),
                MachOperand::VReg(v0),
            ],
        );
        assert_eq!(inst.operands.len(), 3);
        assert_eq!(inst.operands[0].as_vreg(), Some(v0));
        assert_eq!(inst.operands[1].as_vreg(), Some(v1));
    }

    // ---- MachInst flag query convenience methods ----

    #[test]
    fn machinst_flag_queries_match_flags() {
        let inst_call = MachInst::new(AArch64Opcode::Bl, vec![]);
        assert!(inst_call.is_call());
        assert!(inst_call.has_side_effects());
        assert!(!inst_call.is_branch());
        assert!(!inst_call.is_return());
        assert!(!inst_call.is_terminator());
        assert!(!inst_call.is_pseudo());
        assert!(inst_call.reads_memory());
        assert!(inst_call.writes_memory());

        let inst_load = MachInst::new(AArch64Opcode::LdrRI, vec![]);
        assert!(inst_load.reads_memory());
        assert!(!inst_load.writes_memory());

        let inst_store = MachInst::new(AArch64Opcode::StrRI, vec![]);
        assert!(inst_store.writes_memory());
        assert!(inst_store.has_side_effects());
        assert!(!inst_store.reads_memory());

        let inst_phi = MachInst::new(AArch64Opcode::Phi, vec![]);
        assert!(inst_phi.is_pseudo());
    }

    #[test]
    fn machinst_clone() {
        let inst = MachInst::new(AArch64Opcode::AddRR, vec![MachOperand::Imm(42)]);
        let inst2 = inst.clone();
        assert_eq!(inst2.opcode, inst.opcode);
        assert_eq!(inst2.operands.len(), inst.operands.len());
        assert_eq!(inst2.flags, inst.flags);
    }

    // ---- ProofAnnotation::merge tests ----

    #[test]
    fn proof_merge_none_none() {
        assert_eq!(ProofAnnotation::merge(None, None), None);
    }

    #[test]
    fn proof_merge_some_and_none() {
        assert_eq!(
            ProofAnnotation::merge(Some(ProofAnnotation::NoOverflow), None),
            Some(ProofAnnotation::NoOverflow),
        );
        assert_eq!(
            ProofAnnotation::merge(None, Some(ProofAnnotation::InBounds)),
            Some(ProofAnnotation::InBounds),
        );
    }

    #[test]
    fn proof_merge_equal() {
        assert_eq!(
            ProofAnnotation::merge(
                Some(ProofAnnotation::NotNull),
                Some(ProofAnnotation::NotNull),
            ),
            Some(ProofAnnotation::NotNull),
        );
    }

    #[test]
    fn proof_merge_different_returns_none() {
        assert_eq!(
            ProofAnnotation::merge(
                Some(ProofAnnotation::ValidBorrow),
                Some(ProofAnnotation::PositiveRefCount),
            ),
            None,
        );
    }

    #[test]
    fn proof_merge_all_variants_with_self() {
        let variants = [
            ProofAnnotation::NoOverflow,
            ProofAnnotation::NoSignedOverflow,
            ProofAnnotation::NoUnsignedOverflow,
            ProofAnnotation::InBounds,
            ProofAnnotation::NotNull,
            ProofAnnotation::ValidBorrow,
            ProofAnnotation::PositiveRefCount,
            ProofAnnotation::NonZeroDivisor,
            ProofAnnotation::ValidShift,
            ProofAnnotation::Pure,
            ProofAnnotation::Associative,
            ProofAnnotation::Commutative,
            ProofAnnotation::Idempotent,
        ];
        for v in &variants {
            assert_eq!(
                ProofAnnotation::merge(Some(*v), Some(*v)),
                Some(*v),
                "{:?} merged with itself should be Some({:?})",
                v,
                v,
            );
        }
    }

    #[test]
    fn proof_fact_payload_helpers_read_sidecar_facts() {
        let facts = [
            ProofFact::Aligned(16),
            ProofFact::BoundedLoop(1024),
            ProofFact::DivergenceClass(ProofDivergence::Uniform),
        ];

        assert_eq!(ProofFact::bounded_loop_bound(&facts), Some(1024));
        assert_eq!(
            ProofFact::divergence(&facts),
            Some(ProofDivergence::Uniform)
        );
    }

    #[test]
    fn proof_fact_stable_names_hide_payloads() {
        assert_eq!(ProofFact::InBounds.stable_name(), "InBounds");
        assert_eq!(ProofFact::NoAlias.stable_name(), "NoAlias");
        assert_eq!(ProofFact::Aligned(64).stable_name(), "Aligned");
        assert_eq!(ProofFact::BoundedLoop(7).stable_name(), "BoundedLoop");
        assert_eq!(
            ProofFact::DivergenceClass(ProofDivergence::High).stable_name(),
            "DivergenceClass"
        );
    }

    // --- SourceLoc tests ---

    #[test]
    fn test_source_loc_on_mach_inst() {
        let inst = MachInst::new(AArch64Opcode::AddRR, vec![]).with_source_loc(SourceLoc {
            file: 0,
            line: 42,
            col: 5,
        });
        assert!(inst.source_loc.is_some());
        let loc = inst.source_loc.unwrap();
        assert_eq!(loc.file, 0);
        assert_eq!(loc.line, 42);
        assert_eq!(loc.col, 5);
    }

    #[test]
    fn test_source_loc_default_none() {
        let inst = MachInst::new(AArch64Opcode::Ret, vec![]);
        assert!(inst.source_loc.is_none());
    }

    #[test]
    fn test_source_loc_preserved_through_clone() {
        let inst = MachInst::new(AArch64Opcode::SubRR, vec![]).with_source_loc(SourceLoc {
            file: 1,
            line: 100,
            col: 0,
        });
        let cloned = inst.clone();
        assert_eq!(
            cloned.source_loc,
            Some(SourceLoc {
                file: 1,
                line: 100,
                col: 0
            })
        );
    }
}
