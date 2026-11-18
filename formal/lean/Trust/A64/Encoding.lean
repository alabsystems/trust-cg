/-
  A64.Encoding — an A64 (AArch64) instruction-word model: forms, field ranges, a 32-bit
  encoder, a decoder, and kernel-checked round-trip theorems (ledger X-LEAN-P3).

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHAT THIS IS.  `Instr` is one constructor per A64 encoding CLASS that trust-cg's AArch64
  emitter (`crates/trust-cg-codegen/src/aarch64/encode.rs`) writes for integer code, with every
  variable bit-field of that class as a `Fin (2^width)` argument named after the Arm ARM
  (DDI 0487 / DDI 0602, section C4.1) encoding diagram: `sf`, `op`, `S`, `shift`, `imm6`, `Rm`,
  `Rn`, `Rd`, and so on.  A constructor's FIXED bits are not arguments; `encodeNat` writes them.

    * `encodeNat : Instr → Nat` places each field at its diagram position;
      `encode : Instr → UInt32` is that word.
    * `decodeNat : Nat → Option Instr` follows a decision tree over fixed bits only, extracts
      every field with `bits`, and returns the instruction only when it is `valid` (the
      class-specific reserved/unallocated field values below are refused).
    * `decode_encode`: `decode (encode i) = some i` for every `valid` instruction.
    * `encode_decode`: `decode w = some i → encode i = w`, and the decoded `i` is `valid`.

  Aliases (CMP, CMN, TST, MOV, MUL, NEG, CSET, LSL/LSR/ASR #imm, SXT*/UXT*, SMULL, UMULL, ROR
  #imm, ...) are NOT constructors: the Arm ARM defines an alias as a preferred disassembly of
  another encoding, so an alias is the canonical class instruction it names (`Trust.A64.Spec` in
  `Corpus.lean` builds each alias the emitter uses).  The round-trip theorems therefore cover
  every alias too.

  `valid` refuses exactly the field values the Arm ARM makes UNDEFINED or unallocated for the
  class (for example `shift = 11` in add/subtract shifted register, `imm6<5> = 1` for a 32-bit
  shifted-register form, an unallocated logical-immediate bitmask, `opc = 01` in move wide, or
  a load/store `size:opc` combination that is a prefetch or unallocated).  Fields the Arm ARM
  marks "should be one" (SMULH/UMULH `Ra`) are required to hold that value.  Encodings that are
  allocated but CONSTRAINED UNPREDICTABLE for some register combination (for example a
  write-back load whose base is also its destination) remain decodable here: this module is
  about bit layout, not about behaviour.

  EVIDENCE.  Every theorem is checked by the Lean kernel with ordinary `omega` and `simp`
  reasoning; no `sorry`, no `axiom`, no `native_decide` or `bv_decide` (so no
  `Lean.ofReduceBool`).  `#print axioms decode_encode` shows only Lean's standard axioms.  The
  correspondence with the Rust emitter is NOT a theorem: `Trust/A64/EncoderGolden.lean` pins a
  generated corpus that `crates/trust-cg-codegen/tests/lean_a64_encode_golden_binding.rs`
  compares with the live encoder word for word.
  ─────────────────────────────────────────────────────────────────────────────────────────────
-/

import Trust.A64.AddSubImmBits
import Trust.A64.LogicalImmBits
import Trust.A64.MoveWideBits

namespace Trust
namespace A64

/-! ## Bit fields -/

/-- The `n`-bit field of `w` whose least significant bit is bit `lo` (Arm ARM `w<lo+n-1:lo>`). -/
def bits (w lo n : Nat) : Nat := w / 2 ^ lo % 2 ^ n

theorem bits_lt (w lo n : Nat) : bits w lo n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)

/-- A field extracted from `w`, typed by its width. -/
def fld (w lo n : Nat) : Fin (2 ^ n) := ⟨bits w lo n, bits_lt w lo n⟩

@[simp] theorem fld_val (w lo n : Nat) : (fld w lo n).val = bits w lo n := rfl

/-- A 5-bit register field.  Number 31 names SP or the zero register depending on the form;
    the encoding model does not interpret it. -/
abbrev Reg := Fin 32

/-! ## Instruction forms -/

/-- One constructor per modelled A64 encoding class; arguments are the class's variable fields,
    most significant first, named as in the Arm ARM encoding diagram. -/
inductive Instr where
  /-- PC-rel. addressing: `op immlo 10000 immhi Rd` (ADR `op=0`, ADRP `op=1`). -/
  | pcRel (op : Fin 2) (immlo : Fin 4) (immhi : Fin 524288) (rd : Reg)
  /-- Add/subtract (immediate): `sf op S 100010 sh imm12 Rn Rd`. -/
  | addSubImm (sf op s sh : Fin 2) (imm12 : Fin 4096) (rn rd : Reg)
  /-- Logical (immediate): `sf opc 100100 N immr imms Rn Rd` (AND, ORR, EOR, ANDS). -/
  | logicalImm (sf : Fin 2) (opc : Fin 4) (n : Fin 2) (immr imms : Fin 64) (rn rd : Reg)
  /-- Move wide (immediate): `sf opc 100101 hw imm16 Rd` (MOVN `00`, MOVZ `10`, MOVK `11`). -/
  | moveWide (sf : Fin 2) (opc : Fin 4) (hw : Fin 4) (imm16 : Fin 65536) (rd : Reg)
  /-- Bitfield: `sf opc 100110 N immr imms Rn Rd` (SBFM `00`, BFM `01`, UBFM `10`). -/
  | bitfield (sf : Fin 2) (opc : Fin 4) (n : Fin 2) (immr imms : Fin 64) (rn rd : Reg)
  /-- Extract: `sf 00 100111 N 0 Rm imms Rn Rd` (EXTR). -/
  | extract (sf n : Fin 2) (rm : Reg) (imms : Fin 64) (rn rd : Reg)
  /-- Unconditional branch (immediate): `op 00101 imm26` (B `0`, BL `1`). -/
  | branchImm (op : Fin 2) (imm26 : Fin 67108864)
  /-- Compare and branch (immediate): `sf 011010 op imm19 Rt` (CBZ `0`, CBNZ `1`). -/
  | compareBranch (sf op : Fin 2) (imm19 : Fin 524288) (rt : Reg)
  /-- Test and branch (immediate): `b5 011011 op b40 imm14 Rt` (TBZ `0`, TBNZ `1`). -/
  | testBranch (b5 op : Fin 2) (b40 : Fin 32) (imm14 : Fin 16384) (rt : Reg)
  /-- Conditional branch (immediate): `0101010 0 imm19 0 cond` (B.cond). -/
  | condBranch (imm19 : Fin 524288) (cond : Fin 16)
  /-- Unconditional branch (register): `1101011 opc 11111 000000 Rn 00000`
      (BR `0000`, BLR `0001`, RET `0010`). -/
  | branchReg (opc : Fin 16) (rn : Reg)
  /-- Exception generation, BRK: `11010100 001 imm16 000 00`. -/
  | brk (imm16 : Fin 65536)
  /-- Hint NOP: the fixed word `0xD503201F`. -/
  | nop
  /-- Barriers: `1101010100 0 00 011 0011 CRm op2 11111` (DSB `100`, DMB `101`, ISB `110`). -/
  | barrier (crm : Fin 16) (op2 : Fin 8)
  /-- Load register (literal): `opc 011 V 00 imm19 Rt`. -/
  | loadLiteral (opc : Fin 4) (v : Fin 2) (imm19 : Fin 524288) (rt : Reg)
  /-- Load/store register pair: `opc 101 V 0 mode L imm7 Rt2 Rn Rt`
      (mode `00` no-allocate, `01` post-index, `10` signed offset, `11` pre-index). -/
  | loadStorePair (opc : Fin 4) (v : Fin 2) (mode : Fin 4) (l : Fin 2) (imm7 : Fin 128)
      (rt2 rn rt : Reg)
  /-- Load/store register, 9-bit signed immediate: `size 111 V 00 opc 0 imm9 idx Rn Rt`
      (idx `00` unscaled LDUR/STUR, `01` post-index, `11` pre-index). -/
  | loadStoreImm9 (size : Fin 4) (v : Fin 2) (opc : Fin 4) (imm9 : Fin 512) (idx : Fin 4)
      (rn rt : Reg)
  /-- Load/store register (register offset): `size 111 V 00 opc 1 Rm option S 10 Rn Rt`. -/
  | loadStoreRegOff (size : Fin 4) (v : Fin 2) (opc : Fin 4) (rm : Reg) (option : Fin 8)
      (s : Fin 2) (rn rt : Reg)
  /-- Load/store register (unsigned immediate): `size 111 V 01 opc imm12 Rn Rt`. -/
  | loadStoreUImm (size : Fin 4) (v : Fin 2) (opc : Fin 4) (imm12 : Fin 4096) (rn rt : Reg)
  /-- Logical (shifted register): `sf opc 01010 shift N Rm imm6 Rn Rd`
      (AND/BIC, ORR/ORN, EOR/EON, ANDS/BICS). -/
  | logicalShifted (sf : Fin 2) (opc shift : Fin 4) (n : Fin 2) (rm : Reg) (imm6 : Fin 64)
      (rn rd : Reg)
  /-- Add/subtract (shifted register): `sf op S 01011 shift 0 Rm imm6 Rn Rd`. -/
  | addSubShifted (sf op s : Fin 2) (shift : Fin 4) (rm : Reg) (imm6 : Fin 64) (rn rd : Reg)
  /-- Add/subtract (extended register): `sf op S 01011 00 1 Rm option imm3 Rn Rd`. -/
  | addSubExt (sf op s : Fin 2) (rm : Reg) (option imm3 : Fin 8) (rn rd : Reg)
  /-- Add/subtract (with carry): `sf op S 11010000 Rm 000000 Rn Rd` (ADC, ADCS, SBC, SBCS). -/
  | addSubCarry (sf op s : Fin 2) (rm rn rd : Reg)
  /-- Conditional select: `sf op 0 11010100 Rm cond 0 o2 Rn Rd`
      (CSEL `op=0,o2=0`, CSINC `0,1`, CSINV `1,0`, CSNEG `1,1`). -/
  | condSelect (sf op : Fin 2) (rm : Reg) (cond : Fin 16) (o2 : Fin 2) (rn rd : Reg)
  /-- Data-processing (2 source): `sf 0 0 11010110 Rm opcode Rn Rd`
      (UDIV `000010`, SDIV `000011`, LSLV `001000`, LSRV `001001`, ASRV `001010`,
      RORV `001011`, CRC32/CRC32C `010 C sz`). -/
  | dataProc2 (sf : Fin 2) (rm : Reg) (opcode : Fin 64) (rn rd : Reg)
  /-- Data-processing (1 source): `sf 1 0 11010110 00000 opcode Rn Rd`
      (RBIT `000000`, REV16 `000001`, REV32/REV `000010`, REV `000011`, CLZ `000100`,
      CLS `000101`). -/
  | dataProc1 (sf : Fin 2) (opcode : Fin 64) (rn rd : Reg)
  /-- Data-processing (3 source): `sf 00 11011 op31 Rm o0 Ra Rn Rd`
      (MADD/MSUB `000`, SMADDL/SMSUBL `001`, SMULH `010`, UMADDL/UMSUBL `101`, UMULH `110`). -/
  | dataProc3 (sf : Fin 2) (op31 : Fin 8) (rm : Reg) (o0 : Fin 2) (ra rn rd : Reg)
  deriving DecidableEq, Repr

/-! ## Reserved and unallocated field values -/

/-- The logical-immediate `N:immr:imms` field is allocated: `DecodeBitMasks` (Arm ARM J1) finds
    `len = HighestSetBit(N:NOT(imms)) ≥ 1` and the run length `S = imms<len-1:0>` is not all
    ones.  (`immr` never makes an encoding UNDEFINED.) -/
def bitmaskValid (n imms : Nat) : Bool :=
  let combined := n * 64 + (63 - imms)
  let len :=
    if combined ≥ 64 then 6 else if combined ≥ 32 then 5 else if combined ≥ 16 then 4
    else if combined ≥ 8 then 3 else if combined ≥ 4 then 2 else if combined ≥ 2 then 1 else 0
  len ≥ 1 && imms % 2 ^ len != 2 ^ len - 1

/-- The general-purpose (`V=0`) and SIMD&FP (`V=1`) `size:opc` combinations of the single
    register load/store classes that are loads or stores (prefetches and unallocated
    combinations are refused). -/
def ldstSizeOpcValid (size v opc : Nat) : Bool :=
  if v = 0 then opc ≤ 1 || (opc = 2 && size ≤ 2) || (opc = 3 && size ≤ 1)
  else opc ≤ 1 || size = 0

/-- The field-level validity of an instruction (see the module header). -/
def Instr.valid : Instr → Bool
  | .pcRel .. => true
  | .addSubImm .. => true
  | .logicalImm sf _ n _ imms _ _ => (sf.val = 1 || n.val = 0) && bitmaskValid n.val imms.val
  | .moveWide sf opc hw _ _ => opc.val != 1 && (sf.val = 1 || hw.val < 2)
  | .bitfield sf opc n immr imms _ _ =>
      opc.val != 3 && n.val == sf.val && (sf.val = 1 || (immr.val < 32 && imms.val < 32))
  | .extract sf n _ imms _ _ => n.val == sf.val && (sf.val = 1 || imms.val < 32)
  | .branchImm .. => true
  | .compareBranch .. => true
  | .testBranch .. => true
  | .condBranch .. => true
  | .branchReg opc _ => opc.val ≤ 2
  | .brk .. => true
  | .nop => true
  | .barrier _ op2 => 4 ≤ op2.val && op2.val ≤ 6
  | .loadLiteral opc _ _ _ => opc.val ≤ 2
  | .loadStorePair opc v mode l _ _ _ _ =>
      if v.val = 0 then opc.val = 0 || opc.val = 2 || (opc.val = 1 && l.val = 1 && mode.val != 0)
      else opc.val ≤ 2
  | .loadStoreImm9 size v opc _ idx _ _ => idx.val != 2 && ldstSizeOpcValid size.val v.val opc.val
  | .loadStoreRegOff size v opc _ option _ _ _ =>
      option.val / 2 % 2 == 1 && ldstSizeOpcValid size.val v.val opc.val
  | .loadStoreUImm size v opc _ _ _ => ldstSizeOpcValid size.val v.val opc.val
  | .logicalShifted sf _ _ _ _ imm6 _ _ => sf.val = 1 || imm6.val < 32
  | .addSubShifted sf _ _ shift _ imm6 _ _ => shift.val != 3 && (sf.val = 1 || imm6.val < 32)
  | .addSubExt _ _ _ _ _ imm3 _ _ => imm3.val ≤ 4
  | .addSubCarry .. => true
  | .condSelect .. => true
  | .dataProc2 sf _ opcode _ _ =>
      opcode.val = 2 || opcode.val = 3 || (8 ≤ opcode.val && opcode.val ≤ 11) ||
      -- CRC32{B,H,W,X} / CRC32C{B,H,W,X} (FEAT_CRC32): `010 C sz`, `sf = 1` exactly for `sz = 11`.
      (16 ≤ opcode.val && opcode.val ≤ 23 && (opcode.val % 4 == 3) == (sf.val == 1))
  | .dataProc1 sf opcode _ _ =>
      opcode.val ≤ 2 || opcode.val = 4 || opcode.val = 5 || (opcode.val = 3 && sf.val = 1)
  | .dataProc3 sf op31 _ o0 ra _ _ =>
      op31.val = 0 ||
      (sf.val = 1 && (op31.val = 1 || op31.val = 5 ||
        ((op31.val = 2 || op31.val = 6) && o0.val = 0 && ra.val = 31)))

/-! ## Encoder -/

/-- The instruction word as a natural number: each field at its Arm ARM diagram position plus
    the class's fixed bits. -/
def encodeNat : Instr → Nat
  | .pcRel op immlo immhi rd =>
      op.val * 2^31 + immlo.val * 2^29 + 0b10000 * 2^24 + immhi.val * 2^5 + rd.val
  | .addSubImm sf op s sh imm12 rn rd =>
      sf.val * 2^31 + op.val * 2^30 + s.val * 2^29 + 0b100010 * 2^23 + sh.val * 2^22
      + imm12.val * 2^10 + rn.val * 2^5 + rd.val
  | .logicalImm sf opc n immr imms rn rd =>
      sf.val * 2^31 + opc.val * 2^29 + 0b100100 * 2^23 + n.val * 2^22 + immr.val * 2^16
      + imms.val * 2^10 + rn.val * 2^5 + rd.val
  | .moveWide sf opc hw imm16 rd =>
      sf.val * 2^31 + opc.val * 2^29 + 0b100101 * 2^23 + hw.val * 2^21 + imm16.val * 2^5
      + rd.val
  | .bitfield sf opc n immr imms rn rd =>
      sf.val * 2^31 + opc.val * 2^29 + 0b100110 * 2^23 + n.val * 2^22 + immr.val * 2^16
      + imms.val * 2^10 + rn.val * 2^5 + rd.val
  | .extract sf n rm imms rn rd =>
      sf.val * 2^31 + 0b100111 * 2^23 + n.val * 2^22 + rm.val * 2^16 + imms.val * 2^10
      + rn.val * 2^5 + rd.val
  | .branchImm op imm26 => op.val * 2^31 + 0b00101 * 2^26 + imm26.val
  | .compareBranch sf op imm19 rt =>
      sf.val * 2^31 + 0b011010 * 2^25 + op.val * 2^24 + imm19.val * 2^5 + rt.val
  | .testBranch b5 op b40 imm14 rt =>
      b5.val * 2^31 + 0b011011 * 2^25 + op.val * 2^24 + b40.val * 2^19 + imm14.val * 2^5
      + rt.val
  | .condBranch imm19 cond => 0b01010100 * 2^24 + imm19.val * 2^5 + cond.val
  | .branchReg opc rn => 0b1101011 * 2^25 + opc.val * 2^21 + 0b11111 * 2^16 + rn.val * 2^5
  | .brk imm16 => 0b11010100001 * 2^21 + imm16.val * 2^5
  | .nop => 0xD503201F
  | .barrier crm op2 => 0xD5033 * 2^12 + crm.val * 2^8 + op2.val * 2^5 + 0b11111
  | .loadLiteral opc v imm19 rt =>
      opc.val * 2^30 + 0b011 * 2^27 + v.val * 2^26 + imm19.val * 2^5 + rt.val
  | .loadStorePair opc v mode l imm7 rt2 rn rt =>
      opc.val * 2^30 + 0b101 * 2^27 + v.val * 2^26 + mode.val * 2^23 + l.val * 2^22
      + imm7.val * 2^15 + rt2.val * 2^10 + rn.val * 2^5 + rt.val
  | .loadStoreImm9 size v opc imm9 idx rn rt =>
      size.val * 2^30 + 0b111 * 2^27 + v.val * 2^26 + opc.val * 2^22 + imm9.val * 2^12
      + idx.val * 2^10 + rn.val * 2^5 + rt.val
  | .loadStoreRegOff size v opc rm option s rn rt =>
      size.val * 2^30 + 0b111 * 2^27 + v.val * 2^26 + opc.val * 2^22 + 2^21 + rm.val * 2^16
      + option.val * 2^13 + s.val * 2^12 + 0b10 * 2^10 + rn.val * 2^5 + rt.val
  | .loadStoreUImm size v opc imm12 rn rt =>
      size.val * 2^30 + 0b111 * 2^27 + v.val * 2^26 + 0b01 * 2^24 + opc.val * 2^22
      + imm12.val * 2^10 + rn.val * 2^5 + rt.val
  | .logicalShifted sf opc shift n rm imm6 rn rd =>
      sf.val * 2^31 + opc.val * 2^29 + 0b01010 * 2^24 + shift.val * 2^22 + n.val * 2^21
      + rm.val * 2^16 + imm6.val * 2^10 + rn.val * 2^5 + rd.val
  | .addSubShifted sf op s shift rm imm6 rn rd =>
      sf.val * 2^31 + op.val * 2^30 + s.val * 2^29 + 0b01011 * 2^24 + shift.val * 2^22
      + rm.val * 2^16 + imm6.val * 2^10 + rn.val * 2^5 + rd.val
  | .addSubExt sf op s rm option imm3 rn rd =>
      sf.val * 2^31 + op.val * 2^30 + s.val * 2^29 + 0b01011 * 2^24 + 2^21 + rm.val * 2^16
      + option.val * 2^13 + imm3.val * 2^10 + rn.val * 2^5 + rd.val
  | .addSubCarry sf op s rm rn rd =>
      sf.val * 2^31 + op.val * 2^30 + s.val * 2^29 + 0b11010000 * 2^21 + rm.val * 2^16
      + rn.val * 2^5 + rd.val
  | .condSelect sf op rm cond o2 rn rd =>
      sf.val * 2^31 + op.val * 2^30 + 0b11010100 * 2^21 + rm.val * 2^16 + cond.val * 2^12
      + o2.val * 2^10 + rn.val * 2^5 + rd.val
  | .dataProc2 sf rm opcode rn rd =>
      sf.val * 2^31 + 0b11010110 * 2^21 + rm.val * 2^16 + opcode.val * 2^10 + rn.val * 2^5
      + rd.val
  | .dataProc1 sf opcode rn rd =>
      sf.val * 2^31 + 2^30 + 0b11010110 * 2^21 + opcode.val * 2^10 + rn.val * 2^5 + rd.val
  | .dataProc3 sf op31 rm o0 ra rn rd =>
      sf.val * 2^31 + 0b11011 * 2^24 + op31.val * 2^21 + rm.val * 2^16 + o0.val * 2^15
      + ra.val * 2^10 + rn.val * 2^5 + rd.val

theorem encodeNat_lt (i : Instr) : encodeNat i < 2 ^ 32 := by
  cases i <;> simp only [encodeNat] <;> omega

/-- The 32-bit instruction word (little-endian in memory). -/
def encode : Instr → UInt32
  | .addSubImm sf op s sh imm12 rn rd =>
      trust_cg_a64_add_sub_imm_word (UInt32.ofNat (sf.val * 4 + op.val * 2 + s.val))
        (UInt32.ofNat sh.val) (UInt32.ofNat imm12.val) (UInt32.ofNat rn.val) (UInt32.ofNat rd.val)
  | .logicalImm sf opc n immr imms rn rd =>
      trust_cg_a64_logical_imm_word (UInt32.ofNat sf.val) (UInt32.ofNat opc.val)
        (UInt32.ofNat n.val) (UInt32.ofNat immr.val) (UInt32.ofNat imms.val)
        (UInt32.ofNat rn.val) (UInt32.ofNat rd.val)
  | .moveWide sf opc hw imm16 rd =>
      trust_cg_a64_move_wide_word (UInt32.ofNat (sf.val * 4 + opc.val))
        (UInt32.ofNat hw.val) (UInt32.ofNat imm16.val) (UInt32.ofNat rd.val)
  | i => UInt32.ofNat (encodeNat i)

/-- The Trust-compiled ADD/SUB immediate word equals the architectural field layout. -/
theorem encode_addSubImm_toNat
    (sf op s sh : Fin 2) (imm12 : Fin 4096) (rn rd : Reg) :
    (encode (.addSubImm sf op s sh imm12 rn rd)).toNat =
      encodeNat (.addSubImm sf op s sh imm12 rn rd) := by
  have fields :
      0x11000000 + (sf.val * 4 + op.val * 2 + s.val) * 0x20000000
        + sh.val * 0x00400000 + imm12.val * 1024 + rn.val * 32 + rd.val =
      encodeNat (.addSubImm sf op s sh imm12 rn rd) := by
    simp only [encodeNat, Nat.add_mul, Nat.mul_assoc, Nat.reducePow, Nat.reduceMul]
    ac_rfl
  simp only [encode, trust_cg_a64_add_sub_imm_word, UInt32.toNat_add, UInt32.toNat_mul,
    UInt32.toNat_ofNat, UInt32.toNat_ofNat', Nat.mod_add_mod, Nat.add_mod_mod,
    Nat.mod_mul_mod, Nat.mul_mod_mod]
  rw [fields, Nat.mod_eq_of_lt (encodeNat_lt _)]

/-- The Trust-compiled logical-immediate word equals the architectural field layout. -/
theorem encode_logicalImm_toNat
    (sf n : Fin 2) (opc : Fin 4) (immr imms : Fin 64) (rn rd : Reg) :
    (encode (.logicalImm sf opc n immr imms rn rd)).toNat =
      encodeNat (.logicalImm sf opc n immr imms rn rd) := by
  simp only [encode, trust_cg_a64_logical_imm_word, UInt32.toNat_add, UInt32.toNat_mul,
    UInt32.toNat_ofNat, UInt32.toNat_ofNat', Nat.mod_add_mod, Nat.add_mod_mod,
    Nat.mod_mul_mod, Nat.mul_mod_mod]
  rw [← Nat.mod_eq_of_lt (encodeNat_lt (.logicalImm sf opc n immr imms rn rd))]
  congr 1
  simp only [encodeNat, Nat.reducePow, Nat.reduceMul]
  ac_rfl

/-- The Trust-compiled move-wide word equals the architectural field layout. -/
theorem encode_moveWide_toNat (sf : Fin 2) (opc hw : Fin 4) (imm16 : Fin 65536) (rd : Reg) :
    (encode (.moveWide sf opc hw imm16 rd)).toNat = encodeNat (.moveWide sf opc hw imm16 rd) := by
  have fields :
      0x12800000 + (sf.val * 4 + opc.val) * 0x20000000 + hw.val * 0x00200000
          + imm16.val * 32 + rd.val = encodeNat (.moveWide sf opc hw imm16 rd) := by
    simp only [encodeNat, Nat.add_mul, Nat.mul_assoc, Nat.reducePow, Nat.reduceMul]
    ac_rfl
  simp only [encode, trust_cg_a64_move_wide_word, UInt32.toNat_add, UInt32.toNat_mul,
    UInt32.toNat_ofNat, UInt32.toNat_ofNat', Nat.mod_add_mod, Nat.add_mod_mod,
    Nat.mod_mul_mod, Nat.mul_mod_mod]
  rw [fields, Nat.mod_eq_of_lt (encodeNat_lt _)]

theorem encode_toNat (i : Instr) : (encode i).toNat = encodeNat i := by
  cases i
  case addSubImm => exact encode_addSubImm_toNat _ _ _ _ _ _ _
  case logicalImm => exact encode_logicalImm_toNat _ _ _ _ _ _ _
  case moveWide => exact encode_moveWide_toNat _ _ _ _ _
  all_goals
    simp only [encode, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (encodeNat_lt _)

/-! ## Decoder

    A decision tree over the fixed bits, following the Arm ARM top-level and group decode
    tables (C4.1).  Two rules make the tree easy to audit and to prove:

    * every test on the path to a class reads only bits that are FIXED in that class, so the
      path a word takes depends only on its class, never on its operand fields;
    * the tests on one path read disjoint bit slices (a slice tested twice is tested whole),
      and together they cover every fixed bit of the class, so a word that reaches a leaf is
      exactly the class's fixed bits plus its extracted fields.

    `checked` then keeps the candidate only when it is `valid`. -/

/-- Keep a candidate instruction only when its fields are allocated. -/
def checked (i : Instr) : Option Instr := if i.valid then some i else none

/-- Data processing (immediate): bits 28:26 = `100`. -/
def decodeDpImm (w : Nat) : Option Instr :=
  if bits w 24 2 = 0b00 then
    checked (.pcRel (fld w 31 1) (fld w 29 2) (fld w 5 19) (fld w 0 5))
  else if bits w 24 2 = 0b01 then
    if bits w 23 1 = 0 then
      checked (.addSubImm (fld w 31 1) (fld w 30 1) (fld w 29 1) (fld w 22 1) (fld w 10 12)
        (fld w 5 5) (fld w 0 5))
    else none
  else if bits w 24 2 = 0b10 then
    if bits w 23 1 = 0 then
      checked (.logicalImm (fld w 31 1) (fld w 29 2) (fld w 22 1) (fld w 16 6) (fld w 10 6)
        (fld w 5 5) (fld w 0 5))
    else
      checked (.moveWide (fld w 31 1) (fld w 29 2) (fld w 21 2) (fld w 5 16) (fld w 0 5))
  else if bits w 23 1 = 0 then
    checked (.bitfield (fld w 31 1) (fld w 29 2) (fld w 22 1) (fld w 16 6) (fld w 10 6)
      (fld w 5 5) (fld w 0 5))
  else if bits w 29 2 = 0b00 ∧ bits w 21 1 = 0 then
    checked (.extract (fld w 31 1) (fld w 22 1) (fld w 16 5) (fld w 10 6) (fld w 5 5)
      (fld w 0 5))
  else none

/-- Branches, exception generation and system instructions: bits 28:26 = `101`. -/
def decodeBranch (w : Nat) : Option Instr :=
  if bits w 29 2 = 0b00 then
    checked (.branchImm (fld w 31 1) (fld w 0 26))
  else if bits w 29 2 = 0b01 then
    if bits w 25 1 = 0 then
      checked (.compareBranch (fld w 31 1) (fld w 24 1) (fld w 5 19) (fld w 0 5))
    else
      checked (.testBranch (fld w 31 1) (fld w 24 1) (fld w 19 5) (fld w 5 14) (fld w 0 5))
  else if bits w 29 2 = 0b10 then
    if bits w 31 1 = 0 then
      if bits w 24 2 = 0b00 ∧ bits w 4 1 = 0 then
        checked (.condBranch (fld w 5 19) (fld w 0 4))
      else none
    else if bits w 25 1 = 1 then
      if bits w 16 5 = 0b11111 ∧ bits w 10 6 = 0 ∧ bits w 0 5 = 0 then
        checked (.branchReg (fld w 21 4) (fld w 5 5))
      else none
    else if bits w 24 1 = 0 then
      if bits w 21 3 = 0b001 ∧ bits w 0 5 = 0 then checked (.brk (fld w 5 16)) else none
    else if bits w 12 12 = 0x033 ∧ bits w 0 5 = 0b11111 then
      checked (.barrier (fld w 8 4) (fld w 5 3))
    else if bits w 0 24 = 0x03201F then checked .nop
    else none
  else none

/-- Loads and stores: bit 27 = 1, bit 25 = 0. -/
def decodeLoadStore (w : Nat) : Option Instr :=
  if bits w 28 2 = 0b01 then
    if bits w 24 1 = 0 then
      checked (.loadLiteral (fld w 30 2) (fld w 26 1) (fld w 5 19) (fld w 0 5))
    else none
  else if bits w 28 2 = 0b10 then
    checked (.loadStorePair (fld w 30 2) (fld w 26 1) (fld w 23 2) (fld w 22 1) (fld w 15 7)
      (fld w 10 5) (fld w 5 5) (fld w 0 5))
  else if bits w 28 2 = 0b11 then
    if bits w 24 1 = 1 then
      checked (.loadStoreUImm (fld w 30 2) (fld w 26 1) (fld w 22 2) (fld w 10 12) (fld w 5 5)
        (fld w 0 5))
    else if bits w 21 1 = 0 then
      checked (.loadStoreImm9 (fld w 30 2) (fld w 26 1) (fld w 22 2) (fld w 12 9) (fld w 10 2)
        (fld w 5 5) (fld w 0 5))
    else if bits w 10 2 = 0b10 then
      checked (.loadStoreRegOff (fld w 30 2) (fld w 26 1) (fld w 22 2) (fld w 16 5)
        (fld w 13 3) (fld w 12 1) (fld w 5 5) (fld w 0 5))
    else none
  else none

/-- Data processing (register): bits 27:25 = `101`. -/
def decodeDpReg (w : Nat) : Option Instr :=
  if bits w 28 1 = 0 then
    if bits w 24 1 = 0 then
      checked (.logicalShifted (fld w 31 1) (fld w 29 2) (fld w 22 2) (fld w 21 1) (fld w 16 5)
        (fld w 10 6) (fld w 5 5) (fld w 0 5))
    else if bits w 21 1 = 0 then
      checked (.addSubShifted (fld w 31 1) (fld w 30 1) (fld w 29 1) (fld w 22 2) (fld w 16 5)
        (fld w 10 6) (fld w 5 5) (fld w 0 5))
    else if bits w 22 2 = 0b00 then
      checked (.addSubExt (fld w 31 1) (fld w 30 1) (fld w 29 1) (fld w 16 5) (fld w 13 3)
        (fld w 10 3) (fld w 5 5) (fld w 0 5))
    else none
  else if bits w 24 1 = 1 then
    if bits w 29 2 = 0b00 then
      checked (.dataProc3 (fld w 31 1) (fld w 21 3) (fld w 16 5) (fld w 15 1) (fld w 10 5)
        (fld w 5 5) (fld w 0 5))
    else none
  else if bits w 21 3 = 0b000 then
    if bits w 10 6 = 0 then
      checked (.addSubCarry (fld w 31 1) (fld w 30 1) (fld w 29 1) (fld w 16 5) (fld w 5 5)
        (fld w 0 5))
    else none
  else if bits w 21 3 = 0b100 then
    if bits w 29 1 = 0 ∧ bits w 11 1 = 0 then
      checked (.condSelect (fld w 31 1) (fld w 30 1) (fld w 16 5) (fld w 12 4) (fld w 10 1)
        (fld w 5 5) (fld w 0 5))
    else none
  else if bits w 21 3 = 0b110 then
    if bits w 29 2 = 0b00 then
      checked (.dataProc2 (fld w 31 1) (fld w 16 5) (fld w 10 6) (fld w 5 5) (fld w 0 5))
    else if bits w 29 2 = 0b10 ∧ bits w 16 5 = 0 then
      checked (.dataProc1 (fld w 31 1) (fld w 10 6) (fld w 5 5) (fld w 0 5))
    else none
  else none

/-- Decode a word given as a natural number (the A64 top-level table on bits 28:25). -/
def decodeNat (w : Nat) : Option Instr :=
  if bits w 27 1 = 0 then
    if bits w 28 1 = 1 then
      if bits w 26 1 = 0 then decodeDpImm w else decodeBranch w
    else none
  else if bits w 25 1 = 0 then decodeLoadStore w
  else if bits w 26 1 = 0 then decodeDpReg w
  else none

/-- Decode a 32-bit instruction word. -/
def decode (w : UInt32) : Option Instr := decodeNat w.toNat

/-! ## Round trip: decode ∘ encode -/

/-- A recogniser whose candidate is the valid `i` returns `i`. -/
theorem checked_eq_some {c i : Instr} (hc : c = i) (hv : i.valid = true) :
    checked c = some i := by
  subst hc; simp only [checked, hv, if_true]

/-- Close a branch of the decision tree whose test contradicts the encoded word's fixed bits
    (`hE` is the word as the sum of its fields and fixed bits). -/
macro "a64_refute" : tactic =>
  `(tactic| (rename_i hc; exfalso; simp only [bits] at hc; omega))

/-- Follow the decision tree down the encoded word's path (the word is generalised to `w`
    with `hE : <fields and fixed bits> = w`), then match the leaf's candidate against the
    instruction field by field. -/
macro "a64_fwd" : tactic =>
  `(tactic| (
      simp only [encodeNat] at *
      simp only [decodeNat]
      repeat (split <;> try a64_refute)
      simp only [decodeDpImm, decodeBranch, decodeLoadStore, decodeDpReg]
      repeat (split <;> try a64_refute)
      rw [checked_eq_some ?_ (by assumption)]
      (simp only [Instr.pcRel.injEq, Instr.addSubImm.injEq, Instr.logicalImm.injEq, Instr.moveWide.injEq, Instr.bitfield.injEq, Instr.extract.injEq, Instr.branchImm.injEq, Instr.compareBranch.injEq, Instr.testBranch.injEq, Instr.condBranch.injEq, Instr.branchReg.injEq, Instr.brk.injEq, Instr.barrier.injEq, Instr.loadLiteral.injEq, Instr.loadStorePair.injEq, Instr.loadStoreImm9.injEq, Instr.loadStoreRegOff.injEq, Instr.loadStoreUImm.injEq, Instr.logicalShifted.injEq, Instr.addSubShifted.injEq, Instr.addSubExt.injEq, Instr.addSubCarry.injEq, Instr.condSelect.injEq, Instr.dataProc2.injEq, Instr.dataProc1.injEq, Instr.dataProc3.injEq, Fin.ext_iff, fld_val, bits]) <;> omega))

set_option maxHeartbeats 4000000 in
/-- **Decode after encode.**  Every valid instruction decodes from its own word. -/
theorem decodeNat_encodeNat (i : Instr) (h : i.valid = true) :
    decodeNat (encodeNat i) = some i := by
  generalize hE : encodeNat i = w
  cases i <;> a64_fwd

theorem decode_encode (i : Instr) (h : i.valid = true) : decode (encode i) = some i := by
  rw [decode, encode_toNat]; exact decodeNat_encodeNat i h

/-! ## Round trip: encode ∘ decode -/

set_option maxHeartbeats 4000000 in
/-- **Encode after decode.**  A decoded word is the encoding of the decoded instruction, and
    that instruction is valid: every leaf's path facts and extracted fields reassemble `w`. -/
theorem encodeNat_decodeNat (w : Nat) (hw : w < 2 ^ 32) (i : Instr) (h : decodeNat w = some i) :
    encodeNat i = w ∧ i.valid = true := by
  simp only [decodeNat] at h
  repeat' (split at h)
  all_goals try (cases h; done)
  all_goals simp only [decodeDpImm, decodeBranch, decodeLoadStore, decodeDpReg] at h
  all_goals repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (simp only [checked] at h
       split at h
       · rename_i hv
         cases h
         refine ⟨?_, hv⟩
         simp only [encodeNat, fld_val, bits] at *
         omega
       · cases h)

theorem encode_decode (w : UInt32) (i : Instr) (h : decode w = some i) :
    encode i = w ∧ i.valid = true := by
  have ⟨he, hv⟩ := encodeNat_decodeNat w.toNat (UInt32.toNat_lt w) i h
  exact ⟨UInt32.toNat_inj.mp (by simpa only [encode_toNat] using he), hv⟩

/-- The decoder is the partial inverse of the encoder on valid instructions. -/
theorem decode_eq_some_iff (w : UInt32) (i : Instr) :
    decode w = some i ↔ i.valid = true ∧ encode i = w := by
  constructor
  · intro h
    have ⟨he, hv⟩ := encode_decode w i h
    exact ⟨hv, he⟩
  · rintro ⟨hv, rfl⟩
    exact decode_encode i hv

/-- Distinct valid instructions have distinct words. -/
theorem encode_injective (i j : Instr) (hi : i.valid = true) (hj : j.valid = true)
    (h : encode i = encode j) : i = j := by
  have h1 := decode_encode i hi
  have h2 := decode_encode j hj
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-! ## Refusal controls

    Words whose class fixed bits match but whose fields the Arm ARM makes UNDEFINED or
    unallocated decode to `none` (kernel evaluation), so `valid` is not vacuous. -/

/-- ADD (shifted register) with `shift = 11`. -/
theorem decode_refuses_reserved_shift : decode 0x8BC20020 = none := by decide +kernel
/-- 32-bit ADD (shifted register) with `imm6 = 32`. -/
theorem decode_refuses_w_shift_32 : decode 0x0B028020 = none := by decide +kernel
/-- 32-bit logical immediate with `N = 1`. -/
theorem decode_refuses_w_bitmask_n : decode 0x12400020 = none := by decide +kernel
/-- Logical immediate whose run is all ones (`N = 1`, `imms = 111111`). -/
theorem decode_refuses_all_ones_bitmask : decode 0x9240FC20 = none := by decide +kernel
/-- Move wide with `opc = 01`. -/
theorem decode_refuses_move_wide_opc01 : decode 0xB2800000 = none := by decide +kernel
/-- Data processing (2 source) with the unallocated `opcode = 000000`. -/
theorem decode_refuses_dp2_opcode0 : decode 0x9AC00000 = none := by decide +kernel
/-- PRFM (unsigned immediate), a prefetch rather than a load. -/
theorem decode_refuses_prfm : decode 0xF9800000 = none := by decide +kernel
/-- LDTR (unprivileged), outside the modelled 9-bit-immediate modes. -/
theorem decode_refuses_ldtr : decode 0xF8400800 = none := by decide +kernel
/-- SMULH with `Ra ≠ 11111`. -/
theorem decode_refuses_smulh_ra : decode 0x9B420020 = none := by decide +kernel
/-- CRC32X with `sf = 0`. -/
theorem decode_refuses_crc32x_w : decode 0x1AC24C20 = none := by decide +kernel

end A64
end Trust
