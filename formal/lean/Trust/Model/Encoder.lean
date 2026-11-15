/-
  Model.Encoder — the byte-level x86-64 instruction model: encoder, decoder, transfer function.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHAT THIS MODULE IS.  trust-cg's `EmittableNeedsProof` opcode set is the small family of x86-64
  instructions the backend is *allowed* to emit; every one of them must carry a per-instruction
  SMT cert or compilation FAILS CLOSED.  The Cert.* modules discharge the VALUE leg of those
  certs by `bv_decide`.  But a value cert about `execInstr` only matters end-to-end if the BYTES
  the backend actually writes DECODE to that very `execInstr`.  This module supplies the model
  side of that link:

      Instr               — the reified `EmittableNeedsProof` opcode set (mirrors `X86Opcode`).
      encode  : Instr → List UInt8     — REX / opcode / ModRM / disp / imm byte emission.
      decode  : List UInt8 → Option (Instr × List UInt8)  — the inverse byte parser.
      decode_encode_*      — left-inverse: every decodable emitted opcode byte-round-trips.
      execInstr            — the architectural effect of one decoded `Instr` on `MachState`.
      BytesAt              — the bytes resident at an address.

  HOW IT PLUGS INTO THE CONTRACT.  This module imports only `Model.Core`.  `Trust.Model` (the
  link step) DEFINES `x86Step` as fetch∘decode∘execInstr over these definitions, and
  `Model.EncoderStep` proves the keystone `x86Step_decode` (formerly an axiom) and the
  `LoweredStep` builders from that definition.  The byte round trips here are kernel-checked;
  what stays trusted, outside Lean, is that `decode`/`execInstr` are what an x86-64 processor
  does with the same bytes.  The golden matrix (`Model.EncoderGolden`) binds enumerated `encode`
  rows to the Rust emitter; `Model.MovabsGolden` extends that binding to full-width
  immediate loads. Nothing binds `execInstr` to hardware.

  TRUSTED BOUNDARY. No explicit axiom. The little-endian split/join and near-branch round-trips
  are proved from bit extensionality and finite case analysis. Their audited dependencies
  contain only standard logical axioms. Other existing proofs use `bv_decide`, whose
  native-evaluation dependencies must be counted through `#print axioms`.
  None of these model proofs establishes production Rust or hardware refinement.

  DECODER ADMISSION. Register ALU forms require both REX.W and ModRM mode 11.
  Memory-addressing ModRM bytes cannot be interpreted as register operands.
  Near Jcc/JMP forms consume exactly four displacement bytes and preserve the
  remaining input. Other memory/SSE/IDIV/XADD forms still return none, so the model
  machine takes no step on them.
  ─────────────────────────────────────────────────────────────────────────────────────────────
-/
import Std.Tactic.BVDecide
import Trust.Model.Core
import Trust.Model.RegisterBits       -- the state vocabulary (Val, Loc, MachState, Flags, Event …)

namespace Trust
namespace Model
namespace Encoder

open Trust

/-! ## 0.  Register ↔ 4-bit encoding. -/

def gprNum : GPR → BitVec 4
  | .rax => 0  | .rcx => 1  | .rdx => 2  | .rbx => 3
  | .rsp => 4  | .rbp => 5  | .rsi => 6  | .rdi => 7
  | .r8  => 8  | .r9  => 9  | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

def gprOfNum (n : BitVec 4) : GPR :=
  match n with
  | 0  => .rax | 1  => .rcx | 2  => .rdx | 3  => .rbx
  | 4  => .rsp | 5  => .rbp | 6  => .rsi | 7  => .rdi
  | 8  => .r8  | 9  => .r9  | 10 => .r10 | 11 => .r11
  | 12 => .r12 | 13 => .r13 | 14 => .r14 | _  => .r15

theorem gprOfNum_gprNum (r : GPR) : gprOfNum (gprNum r) = r := by
  cases r <;> decide

def gprLo3 (r : GPR) : BitVec 3 :=
  BitVec.ofNat 3 (trust_cg_x86_low3 (UInt8.ofNat (gprNum r).toNat)).toNat

/-- The shared Trust computation extracts exactly the model's three register bits. -/
@[simp] theorem gprLo3_bits (r : GPR) : gprLo3 r = (gprNum r).truncate 3 := by
  cases r <;> decide
def gprHiBit (r : GPR) : Bool := (gprNum r).getMsbD 0

theorem gprNum_split (r : GPR) :
    gprNum r = ((BitVec.ofBool (gprHiBit r)) ++ (gprLo3 r)).cast (by omega) := by
  cases r <;> (simp only [gprNum, gprLo3_bits, gprHiBit]; bv_decide)

/-! ## 1.  Condition codes (Jcc / SETcc / CMOVcc). -/

inductive Cond
  | o | no | b | ae | e | ne | be | a
  | s | ns | p | np | l | ge | le | g
  deriving DecidableEq, Repr

def condNum : Cond → BitVec 4
  | .o => 0  | .no => 1 | .b  => 2  | .ae => 3
  | .e => 4  | .ne => 5 | .be => 6  | .a  => 7
  | .s => 8  | .ns => 9 | .p  => 10 | .np => 11
  | .l => 12 | .ge => 13| .le => 14 | .g  => 15

def condOfNum (n : BitVec 4) : Cond :=
  match n with
  | 0  => .o | 1  => .no | 2  => .b  | 3  => .ae
  | 4  => .e | 5  => .ne | 6  => .be | 7  => .a
  | 8  => .s | 9  => .ns | 10 => .p  | 11 => .np
  | 12 => .l | 13 => .ge | 14 => .le | _  => .g

theorem condOfNum_condNum (c : Cond) : condOfNum (condNum c) = c := by
  cases c <;> decide

/-! ## 2.  `Instr` — the reified `EmittableNeedsProof` opcode set. -/

inductive OSize | b8 | b16 | b32 | b64
  deriving DecidableEq, Repr

abbrev Disp32 := BitVec 32

inductive Instr
  | movRR   (sz : OSize) (dst src : GPR)
  | movabsRI (dst : GPR) (imm : BitVec 64)
  | movRI   (sz : OSize) (dst : GPR) (imm : BitVec 32)
  | leaRM   (dst base : GPR) (disp : Disp32)
  | movLoadRM  (sz : OSize) (dst base : GPR) (disp : Disp32)
  | movStoreMR (sz : OSize) (base src : GPR) (disp : Disp32)
  | addRR   (sz : OSize) (dst src : GPR)
  | adcRR   (sz : OSize) (dst src : GPR)
  | subRR   (sz : OSize) (dst src : GPR)
  | sbbRR   (sz : OSize) (dst src : GPR)
  | imulRR  (sz : OSize) (dst src : GPR)
  | idivR   (sz : OSize) (divisor : GPR)
  | cmpRR   (sz : OSize) (a b : GPR)
  | testRR  (sz : OSize) (a b : GPR)
  | andRR   (sz : OSize) (dst src : GPR)
  | orRR    (sz : OSize) (dst src : GPR)
  | xorRR   (sz : OSize) (dst src : GPR)
  | notR    (sz : OSize) (dst : GPR)
  | negR    (sz : OSize) (dst : GPR)
  | shlRI   (sz : OSize) (dst : GPR) (amt : BitVec 8)
  | shrRI   (sz : OSize) (dst : GPR) (amt : BitVec 8)
  | sarRI   (sz : OSize) (dst : GPR) (amt : BitVec 8)
  | setcc   (cc : Cond) (dst : GPR)
  | cmovcc  (sz : OSize) (cc : Cond) (dst src : GPR)
  | jcc     (cc : Cond) (rel : BitVec 32)
  | jmp     (rel : BitVec 32)
  | lockXaddMR (sz : OSize) (base src : GPR) (disp : Disp32)
  | movsdRR (dst src : XMM)
  | movssRR (dst src : XMM)
  deriving Repr

/-! ## 3.  REX / ModRM byte helpers. -/

@[inline] def b8 (x : BitVec 8) : UInt8 := UInt8.ofNat x.toNat

def rexByte (w r x b : Bool) : BitVec 8 :=
  (0x40 : BitVec 8)
    ||| (if w then 0x08 else 0) ||| (if r then 0x04 else 0)
    ||| (if x then 0x02 else 0) ||| (if b then 0x01 else 0)

def rexRR (sz : OSize) (reg rm : GPR) : BitVec 8 :=
  rexByte (sz = OSize.b64) (gprHiBit reg) false (gprHiBit rm)

def modrmByte (mode : BitVec 2) (reg rm : BitVec 3) : BitVec 8 :=
  (((mode.setWidth 8) <<< (6 : BitVec 8))
    ||| ((reg.setWidth 8) <<< (3 : BitVec 8))
    ||| (rm.setWidth 8))

def modrmRR (reg rm : GPR) : BitVec 8 := modrmByte 0b11 (gprLo3 reg) (gprLo3 rm)
def modrmExtR (ext : BitVec 3) (rm : GPR) : BitVec 8 := modrmByte 0b11 ext (gprLo3 rm)
def modrmMemDisp32 (reg base : GPR) : BitVec 8 := modrmByte 0b10 (gprLo3 reg) (gprLo3 base)

theorem modrmRR_fields (reg rm : GPR) :
    ((modrmRR reg rm) >>> (6 : BitVec 8)).truncate 2 = 0b11 ∧
    (((modrmRR reg rm) >>> (3 : BitVec 8)).truncate 3) = gprLo3 reg ∧
    ((modrmRR reg rm).truncate 3) = gprLo3 rm := by
  simp only [modrmRR, modrmByte, gprLo3_bits]
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

/-! ## 4.  Little-endian immediate / displacement splitting. -/

def le32 (x : BitVec 32) : List UInt8 :=
  [ b8 (x.truncate 8)
  , b8 ((x >>> (8  : BitVec 32)).truncate 8)
  , b8 ((x >>> (16 : BitVec 32)).truncate 8)
  , b8 ((x >>> (24 : BitVec 32)).truncate 8) ]

def ofLe32 : List UInt8 → Option (BitVec 32 × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: rest =>
      let v : BitVec 32 :=
        (BitVec.ofNat 32 b0.toNat)
          ||| ((BitVec.ofNat 32 b1.toNat) <<< (8  : BitVec 32))
          ||| ((BitVec.ofNat 32 b2.toNat) <<< (16 : BitVec 32))
          ||| ((BitVec.ofNat 32 b3.toNat) <<< (24 : BitVec 32))
      some (v, rest)
  | _ => none

def le8 (x : BitVec 8) : List UInt8 := [b8 x]

theorem toNat_b8 (y : BitVec 8) : (b8 y).toNat = y.toNat := by
  simp only [b8]; exact Nat.mod_eq_of_lt (by have := y.isLt; omega)

theorem ofNat_toNat_bv8 (y : BitVec 8) : BitVec.ofNat 32 y.toNat = y.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := y.isLt; omega : y.toNat < 2^32)]

private theorem split_join32 (x : BitVec 32) :
    (x.setWidth 8).setWidth 32 |||
      (((x >>> (8 : Nat)).setWidth 8).setWidth 32 <<< (8 : Nat)) |||
      (((x >>> (16 : Nat)).setWidth 8).setWidth 32 <<< (16 : Nat)) |||
      (((x >>> (24 : Nat)).setWidth 8).setWidth 32 <<< (24 : Nat)) = x := by
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h8 : i < 8
  · simp [h8, show i < 16 by omega, show i < 24 by omega, BitVec.getLsbD_eq_getElem, hi]
  · by_cases h16 : i < 16
    · simp [h8, h16, show i < 24 by omega, show i - 8 < 8 by omega,
        show 8 + (i - 8) = i by omega, BitVec.getLsbD_eq_getElem, hi]
    · by_cases h24 : i < 24
      · simp [h8, h16, h24, show ¬ i - 8 < 8 by omega, show i - 16 < 8 by omega,
          show 16 + (i - 16) = i by omega, BitVec.getLsbD_eq_getElem, hi]
      · simp [h8, h16, h24, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
          show i - 24 < 8 by omega, show 24 + (i - 24) = i by omega,
          BitVec.getLsbD_eq_getElem, hi]

/-- LE32 split then join is the identity (and the tail is preserved).  FULLY PROVEN (no `sorry`):
    the four bytes coerce back through `toNat_b8`/`ofNat_toNat_bv8`, and the OR-of-shifted-bytes
    reconstructs `x` by bit extensionality and arithmetic on bit indices. -/
theorem ofLe32_le32 (x : BitVec 32) (rest : List UInt8) :
    ofLe32 (le32 x ++ rest) = some (x, rest) := by
  simp only [le32, ofLe32, List.cons_append, List.nil_append]
  rw [toNat_b8, toNat_b8, toNat_b8, toNat_b8,
      ofNat_toNat_bv8, ofNat_toNat_bv8, ofNat_toNat_bv8, ofNat_toNat_bv8]
  refine congrArg some (Prod.ext ?_ rfl)
  simpa [BitVec.truncate, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq'] using split_join32 x

/-- Full-width immediate bytes, distinct from the C7 sign-extended imm32 form. -/
def le64 (x : BitVec 64) : List UInt8 :=
  le32 (x.setWidth 32) ++ le32 ((x >>> (32 : Nat)).setWidth 32)

def ofLe64 (bytes : List UInt8) : Option (BitVec 64 × List UInt8) := do
  let (lo, tail) ← ofLe32 bytes
  let (hi, rest) ← ofLe32 tail
  return (hi ++ lo, rest)

theorem ofLe64_le64 (x : BitVec 64) (rest : List UInt8) :
    ofLe64 (le64 x ++ rest) = some (x, rest) := by
  unfold le64
  rw [List.append_assoc]
  unfold ofLe64
  rw [ofLe32_le32]
  simp only [bind, Option.bind]
  rw [ofLe32_le32]
  simp only [pure]
  congr 2
  rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.setWidth_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_append_extractLsb'

/-! ## 5.  `encode : Instr → List UInt8`. -/

def osPrefix (sz : OSize) : List UInt8 := if sz = OSize.b16 then [b8 0x66] else []

def xmmNum : XMM → BitVec 4
  | .x0 => 0  | .x1 => 1  | .x2 => 2  | .x3 => 3
  | .x4 => 4  | .x5 => 5  | .x6 => 6  | .x7 => 7
  | .x8 => 8  | .x9 => 9  | .x10 => 10| .x11 => 11
  | .x12 => 12| .x13 => 13| .x14 => 14| .x15 => 15

def encInstr : Instr → List UInt8
  | .movabsRI dst imm =>
      [b8 (rexRR .b64 .rax dst), b8 (0xB8 + (gprLo3 dst).setWidth 8)] ++ le64 imm
  | .movRR sz dst src =>
      osPrefix sz ++ [b8 (rexRR sz src dst), b8 0x89, b8 (modrmRR src dst)]
  | .movRI sz dst imm =>
      osPrefix sz ++ [b8 (rexRR sz .rax dst), b8 0xC7, b8 (modrmExtR 0 dst)] ++ le32 imm
  | .leaRM dst base disp =>
      [b8 (rexRR OSize.b64 dst base), b8 0x8D, b8 (modrmMemDisp32 dst base)] ++ le32 disp
  | .movLoadRM sz dst base disp =>
      osPrefix sz ++ [b8 (rexRR sz dst base), b8 0x8B, b8 (modrmMemDisp32 dst base)] ++ le32 disp
  | .movStoreMR sz base src disp =>
      osPrefix sz ++ [b8 (rexRR sz src base), b8 0x89, b8 (modrmMemDisp32 src base)] ++ le32 disp
  | .addRR sz dst src =>
      osPrefix sz ++ [b8 (rexRR sz src dst), b8 0x01, b8 (modrmRR src dst)]
  | .adcRR sz dst src =>
      osPrefix sz ++ [b8 (rexRR sz src dst), b8 0x11, b8 (modrmRR src dst)]
  | .subRR sz dst src =>
      osPrefix sz ++ [b8 (rexRR sz src dst), b8 0x29, b8 (modrmRR src dst)]
  | .sbbRR sz dst src =>
      osPrefix sz ++ [b8 (rexRR sz src dst), b8 0x19, b8 (modrmRR src dst)]
  | .imulRR sz dst src =>
      osPrefix sz ++ [b8 (rexRR sz dst src), b8 0x0F, b8 0xAF, b8 (modrmRR dst src)]
  | .idivR sz divisor =>
      osPrefix sz ++ [b8 (rexRR sz .rax divisor), b8 0xF7, b8 (modrmExtR 7 divisor)]
  | .cmpRR sz a b =>
      osPrefix sz ++ [b8 (rexRR sz b a), b8 0x39, b8 (modrmRR b a)]
  | .testRR sz a b =>
      osPrefix sz ++ [b8 (rexRR sz b a), b8 0x85, b8 (modrmRR b a)]
  | .andRR sz dst src =>
      osPrefix sz ++ [b8 (rexRR sz src dst), b8 0x21, b8 (modrmRR src dst)]
  | .orRR sz dst src =>
      osPrefix sz ++ [b8 (rexRR sz src dst), b8 0x09, b8 (modrmRR src dst)]
  | .xorRR sz dst src =>
      osPrefix sz ++ [b8 (rexRR sz src dst), b8 0x31, b8 (modrmRR src dst)]
  | .notR sz dst =>
      osPrefix sz ++ [b8 (rexRR sz .rax dst), b8 0xF7, b8 (modrmExtR 2 dst)]
  | .negR sz dst =>
      osPrefix sz ++ [b8 (rexRR sz .rax dst), b8 0xF7, b8 (modrmExtR 3 dst)]
  | .shlRI sz dst amt =>
      osPrefix sz ++ [b8 (rexRR sz .rax dst), b8 0xC1, b8 (modrmExtR 4 dst)] ++ le8 amt
  | .shrRI sz dst amt =>
      osPrefix sz ++ [b8 (rexRR sz .rax dst), b8 0xC1, b8 (modrmExtR 5 dst)] ++ le8 amt
  | .sarRI sz dst amt =>
      osPrefix sz ++ [b8 (rexRR sz .rax dst), b8 0xC1, b8 (modrmExtR 7 dst)] ++ le8 amt
  | .setcc cc dst =>
      [b8 (rexRR OSize.b8 .rax dst), b8 0x0F, b8 (0x90 + (condNum cc).setWidth 8), b8 (modrmExtR 0 dst)]
  | .cmovcc sz cc dst src =>
      osPrefix sz ++ [b8 (rexRR sz dst src), b8 0x0F, b8 (0x40 + (condNum cc).setWidth 8), b8 (modrmRR dst src)]
  | .jcc cc rel =>
      [b8 0x0F, b8 (0x80 + (condNum cc).setWidth 8)] ++ le32 rel
  | .jmp rel =>
      [b8 0xE9] ++ le32 rel
  | .lockXaddMR sz base src disp =>
      [b8 0xF0] ++ osPrefix sz ++
        [b8 (rexRR sz src base), b8 0x0F, b8 0xC1, b8 (modrmMemDisp32 src base)] ++ le32 disp
  | .movsdRR dst src =>
      [b8 0xF2, b8 0x0F, b8 0x10, b8 (modrmByte 0b11 ((xmmNum dst).truncate 3) ((xmmNum src).truncate 3))]
  | .movssRR dst src =>
      [b8 0xF3, b8 0x0F, b8 0x10, b8 (modrmByte 0b11 ((xmmNum dst).truncate 3) ((xmmNum src).truncate 3))]

def encode (i : Instr) : List UInt8 := encInstr i

/-! ## 6.  `decode : List UInt8 → Option (Instr × List UInt8)`. -/

def decodeRR (rex modrm : BitVec 8) : GPR × GPR :=
  let rBit  := rex.getLsbD 2
  let bBit  := rex.getLsbD 0
  let regLo := ((modrm >>> (3 : BitVec 8)) &&& 0b111).truncate 3
  let rmLo  := (modrm &&& 0b111).truncate 3
  let reg := gprOfNum (((BitVec.ofBool rBit) ++ regLo).cast (by omega))
  let rm  := gprOfNum (((BitVec.ofBool bBit) ++ rmLo ).cast (by omega))
  (reg, rm)

def osizeOf (has66 wbit : Bool) : OSize :=
  if has66 then OSize.b16 else if wbit then OSize.b64 else OSize.b32

@[inline] def u8ToBv (b : UInt8) : BitVec 8 := BitVec.ofNat 8 b.toNat

theorem u8ToBv_b8 (x : BitVec 8) : u8ToBv (b8 x) = x := by
  unfold u8ToBv b8
  simp [BitVec.ofNat_toNat]

/-- Total decoder for REX.W register ALU forms, full-width immediate moves,
    SHR imm8, and near Jcc/JMP branches.
    Register forms require ModRM mode 11; unsupported opcodes and incomplete
    displacements return none. The b64 gate keeps register effects faithful. -/
def decode : List UInt8 → Option (Instr × List UInt8)
  | rexB :: opB :: modrmB :: rest =>
      let rex   := u8ToBv rexB
      let op    := u8ToBv opB
      let modrm := u8ToBv modrmB
      if (rex >>> (4 : BitVec 8) == (0x4 : BitVec 8)) then
        let wbit := rex.getLsbD 3
        let (f0, f1) := decodeRR rex modrm
        let sz := osizeOf false wbit
        -- SOUNDNESS GATE (b64-only): `execInstr` models the WIDE (64-bit) integer effect.  A real
        -- 32-bit ALU op ZERO-EXTENDS bits 32..63, which `execInstr`'s full-64 result does NOT match,
        -- so the fetch/decode/execute `x86Step` would be UNFAITHFUL for b32.  We therefore only admit the
        -- REX.W (b64) forms here; a non-W byte (b32) decodes to `none` and can never reach
        -- the keystone with the wide-effect `execInstr`.
        if !wbit then none else
        if op >>> (3 : BitVec 8) == 0x17 then
          (ofLe64 (modrmB :: rest)).map fun (imm, tail) =>
            (.movabsRI (gprOfNum ((BitVec.ofBool (rex.getLsbD 0)) ++ op.truncate 3)) imm, tail)
        else
        if ((modrm >>> (6 : BitVec 8)).truncate 2 != (0b11 : BitVec 2)) then none else
        if op == 0xC1 && ((modrm >>> (3 : BitVec 8)) &&& 7) == 5 then
          match rest with
          | imm :: tail => some (.shrRI .b64 f1 (u8ToBv imm), tail)
          | [] => none
        else if      op == 0x89 then some (.movRR sz f1 f0, rest)
        else if op == 0x01 then some (.addRR sz f1 f0, rest)
        else if op == 0x11 then some (.adcRR sz f1 f0, rest)
        else if op == 0x29 then some (.subRR sz f1 f0, rest)
        else if op == 0x19 then some (.sbbRR sz f1 f0, rest)
        else if op == 0x39 then some (.cmpRR sz f1 f0, rest)
        else if op == 0x85 then some (.testRR sz f1 f0, rest)
        else if op == 0x21 then some (.andRR sz f1 f0, rest)
        else if op == 0x09 then some (.orRR sz f1 f0, rest)
        else if op == 0x31 then some (.xorRR sz f1 f0, rest)
        else none
      else if rex == 0x0F then
        if (op >>> (4 : BitVec 8)) == 0x8 then
          (ofLe32 (modrmB :: rest)).map fun (rel, tail) =>
            (.jcc (condOfNum (op.truncate 4)) rel, tail)
        else none
      else if rex == 0xE9 then
        (ofLe32 (opB :: modrmB :: rest)).map fun (rel, tail) => (.jmp rel, tail)
      else none
  | _ => none

/-- All immediate bits and arbitrary following bytes survive decode. -/
theorem decode_encode_movabsRI (dst : GPR) (imm : BitVec 64) (tail : List UInt8) :
    decode (encode (.movabsRI dst imm) ++ tail) = some (.movabsRI dst imm, tail) := by
  have hread := ofLe64_le64 imm tail
  simp only [le64, le32, List.cons_append, List.nil_append] at hread
  simp only [BitVec.truncate, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)] at hread
  cases dst <;>
    simp [encode, encInstr, le64, le32, decode, u8ToBv_b8,
      rexRR, rexByte, gprHiBit, gprLo3_bits, gprNum, gprOfNum] <;> exact hread

/-- The entire imm8 domain shares the anchored three-byte prefix. -/
theorem encode_shrRI_immediate (dst : GPR) (amt : BitVec 8) :
    encode (.shrRI .b64 dst amt) = (encode (.shrRI .b64 dst 0)).take 3 ++ [b8 amt] := by
  rfl

/-- Register SHR decodes every raw imm8, preserving an arbitrary suffix. -/
theorem decode_encode_shrRI (dst : GPR) (amt : BitVec 8) (tail : List UInt8) :
    decode (encode (.shrRI .b64 dst amt) ++ tail) = some (.shrRI .b64 dst amt, tail) := by
  cases dst <;>
    simp [encode, encInstr, osPrefix, le8, decode, u8ToBv_b8, rexRR,
      rexByte, modrmExtR, modrmByte, gprHiBit, gprLo3_bits, gprNum, decodeRR, gprOfNum]

/-! ## 7.  `decode_encode` — the byte round-trip (left inverse). -/

theorem decodeRR_roundtrip (reg rm : GPR) :
    decodeRR (rexRR OSize.b64 reg rm) (modrmRR reg rm) = (reg, rm) := by
  simp only [decodeRR, rexRR, rexByte, modrmRR, modrmByte, gprLo3_bits, gprHiBit]
  have hreg : gprOfNum (gprNum reg) = reg := gprOfNum_gprNum reg
  have hrm  : gprOfNum (gprNum rm)  = rm  := gprOfNum_gprNum rm
  cases reg <;> cases rm <;>
    (simp only [gprNum] <;> first | rfl | (simp_all; bv_decide))

theorem rexRR_b64_guard (reg rm : GPR) :
    ((rexRR OSize.b64 reg rm) >>> (4 : BitVec 8) == (0x4 : BitVec 8)) = true ∧
    (rexRR OSize.b64 reg rm).getLsbD 3 = true := by
  cases reg <;> cases rm <;> (simp only [rexRR, rexByte, gprHiBit, gprNum]; bv_decide)

/-- The emitted register mode is checked independently of the opcode. -/
theorem modrmRR_register_mode (reg rm : GPR) :
    ((modrmRR reg rm) >>> (6 : BitVec 8)).truncate 2 = (0b11 : BitVec 2) := by
  cases reg <;> cases rm <;> decide

/-- `decode_encode` for the ADD reg/reg b64 form.  Fully proven from the round-trip helpers. -/
theorem decode_encode_addRR (dst src : GPR) :
    decode (encode (.addRR OSize.b64 dst src)) = some (.addRR OSize.b64 dst src, []) := by
  have hg := (rexRR_b64_guard src dst).1
  have hw := (rexRR_b64_guard src dst).2
  have hd := decodeRR_roundtrip src dst
  have hm := modrmRR_register_mode src dst
  simp only [encode, encInstr, osPrefix, if_neg (by decide : ¬ (OSize.b64 = OSize.b16)),
             List.nil_append, decode, u8ToBv_b8]
  rw [hg, hw, hd, hm]
  simp only [osizeOf, if_true, BEq.beq, Bool.not_true, Bool.false_eq_true, if_false, bne_self_eq_false]
  rfl

/-- The round-trip for EVERY reg/reg ALU b64 opcode.  FULLY PROVEN (no `sorry`):
    `rcases` over the finite opcode disjunction, then the shared `decode_encode_addRR` recipe. -/
theorem decode_encode_regreg
    (i : Instr)
    (hform : ∃ sz dst src,
        sz = OSize.b64 ∧
        (i = .movRR sz dst src ∨ i = .addRR sz dst src ∨ i = .adcRR sz dst src ∨
         i = .subRR sz dst src ∨ i = .sbbRR sz dst src ∨ i = .cmpRR sz dst src ∨
         i = .testRR sz dst src ∨ i = .andRR sz dst src ∨ i = .orRR sz dst src ∨
         i = .xorRR sz dst src)) :
    decode (encode i) = some (i, []) := by
  obtain ⟨sz, dst, src, rfl, hi⟩ := hform
  have hg := (rexRR_b64_guard src dst).1
  have hw := (rexRR_b64_guard src dst).2
  have hd := decodeRR_roundtrip src dst
  have hm := modrmRR_register_mode src dst
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [encode, encInstr, osPrefix, if_neg (by decide : ¬ (OSize.b64 = OSize.b16)),
                List.nil_append, decode, u8ToBv_b8] <;>
     rw [hg, hw, hd, hm] <;>
     simp only [osizeOf, if_true, BEq.beq, Bool.not_true, Bool.false_eq_true, if_false, bne_self_eq_false] <;>
     rfl)

/-- Near conditional branches preserve all four displacement bytes and the tail. -/
theorem decode_encode_jcc (cc : Cond) (rel : BitVec 32) (tail : List UInt8) :
    decode (encode (.jcc cc rel) ++ tail) = some (.jcc cc rel, tail) := by
  have hread := ofLe32_le32 rel tail
  simp only [le32, List.cons_append, List.nil_append, BitVec.truncate] at hread
  cases cc <;>
    simp [encode, encInstr, le32, decode, u8ToBv_b8, condNum, condOfNum] <;> exact hread

/-- Near unconditional branches preserve their displacement and following bytes. -/
theorem decode_encode_jmp (rel : BitVec 32) (tail : List UInt8) :
    decode (encode (.jmp rel) ++ tail) = some (.jmp rel, tail) := by
  have hread := ofLe32_le32 rel tail
  simp only [le32, List.cons_append, List.nil_append, BitVec.truncate] at hread
  simp [encode, encInstr, le32, decode, u8ToBv_b8]
  exact hread

/-- A memory-mode MOV must not decode as a register-to-register MOV. -/
theorem decode_memory_modrm_refused : decode [0x48, 0x89, 0x08] = none := by decide

/-- Truncated displacement and unsupported two-byte opcodes fail closed. -/
theorem decode_truncated_jcc_refused : decode [0x0F, 0x84, 0x12, 0x34, 0x56] = none := by decide

theorem decode_nonbranch_0f_refused : decode [0x0F, 0x74, 0xC0, 0, 0, 0] = none := by decide

/-! ## 8.  `execInstr` — the architectural transfer function.

    FAITHFULNESS of the keystone-reachable set.  Every opcode that can round-trip through `decode`
    (the b64 register ALU set and near Jcc/JMP branches) is modeled here,
    INCLUDING its flag effect.  Modeling the FULL 64-bit effect is sound precisely because `decode`
    admits ONLY the REX.W (b64) forms (b32 is rejected at the gate).  The remaining skeleton forms
    (mem/IDIV/LOCK-XADD/SSE) are NOT in `decode`'s table, so the model `x86Step` never executes
    them; their rip-only stub is unsupported-not-unsound. -/

def writeBytes (mem : BitVec 64 → BitVec 8) (a : BitVec 64) (v : BitVec 64) (n : Nat) :
    BitVec 64 → BitVec 8 :=
  fun addr =>
    (List.range n).foldl
      (fun acc k =>
        fun q => if q = a + BitVec.ofNat 64 k
                 then ((v >>> (BitVec.ofNat 64 (8*k))).truncate 8) else acc q)
      mem addr

/-- x86 PARITY flag: set iff the number of set bits in the LOW BYTE of the result is EVEN.
    (NOT `low8 % 2 == 0`, which is mere LSB parity — that was a faithfulness bug.) -/
def parityFlag (res : BitVec 64) : Bool :=
  !(res.getLsbD 0 ^^ res.getLsbD 1 ^^ res.getLsbD 2 ^^ res.getLsbD 3 ^^
    res.getLsbD 4 ^^ res.getLsbD 5 ^^ res.getLsbD 6 ^^ res.getLsbD 7)

def addFlags (a b res : BitVec 64) : Flags :=
  { cf := res < a
  , zf := res == 0
  , sf := res.getMsbD 0
  , of := (a.getMsbD 0 == b.getMsbD 0) && (a.getMsbD 0 != res.getMsbD 0)
  , pf := parityFlag res }

def subFlags (a b res : BitVec 64) : Flags :=
  { cf := a < b
  , zf := res == 0
  , sf := res.getMsbD 0
  , of := (a.getMsbD 0 != b.getMsbD 0) && (a.getMsbD 0 != res.getMsbD 0)
  , pf := parityFlag res }

/-- Status flags from a 64-bit bitwise op (AND/OR/XOR): x86 CLEARS CF and OF, sets SF/ZF/PF. -/
def logicFlags (res : BitVec 64) : Flags :=
  { cf := false
  , zf := res == 0
  , sf := res.getMsbD 0
  , of := false
  , pf := parityFlag res }

/-- Status flags from ADC (`a + b + cin`): CF is the true unsigned carry-out of the full 65-bit sum. -/
def adcFlags (a b : BitVec 64) (cin : Bool) (res : BitVec 64) : Flags :=
  let wide := (a.setWidth 65) + (b.setWidth 65) + (if cin then 1 else 0)
  { cf := wide.getMsbD 0
  , zf := res == 0
  , sf := res.getMsbD 0
  , of := (a.getMsbD 0 == b.getMsbD 0) && (a.getMsbD 0 != res.getMsbD 0)
  , pf := parityFlag res }

/-- Status flags from SBB (`a - b - bin`): CF is the true unsigned borrow. -/
def sbbFlags (a b : BitVec 64) (bin : Bool) (res : BitVec 64) : Flags :=
  { cf := (a < b) || (a == b && bin)
  , zf := res == 0
  , sf := res.getMsbD 0
  , of := (a.getMsbD 0 != b.getMsbD 0) && (a.getMsbD 0 != res.getMsbD 0)
  , pf := parityFlag res }

/-- REX.W shifts mask the immediate to six bits. -/
def shrCount64 (amt : BitVec 8) : Nat := amt.toNat % 64

theorem shrCount64_lt (amt : BitVec 8) : shrCount64 amt < 64 :=
  Nat.mod_lt _ (by decide)

/-- SHR's represented flags; OF is an explicit choice when the count exceeds one.
    AF is not represented in Flags. The zero-count case preserves every flag. -/
def shrFlags64 (old : Flags) (a : BitVec 64) (amt : BitVec 8)
    (undefinedOF : Bool) : Flags :=
  let count := shrCount64 amt
  let res := a >>> count
  if count = 0 then old else
    { cf := a.getLsbD (count - 1)
    , zf := res == 0
    , sf := res.getMsbD 0
    , of := if count = 1 then a.getMsbD 0 else undefinedOF
    , pf := parityFlag res }

def setReg (m : MachState) (r : GPR) (v : BitVec 64) : MachState :=
  { m with regs := fun q => if q = r then v else m.regs q }

def stepRip (m : MachState) (len : Nat) : BitVec 64 := m.rip + BitVec.ofNat 64 len

def condHolds (cc : Cond) (f : Flags) : Bool :=
  match cc with
  | .o  => f.of            | .no => !f.of
  | .b  => f.cf            | .ae => !f.cf
  | .e  => f.zf            | .ne => !f.zf
  | .be => f.cf || f.zf    | .a  => !f.cf && !f.zf
  | .s  => f.sf            | .ns => !f.sf
  | .p  => f.pf            | .np => !f.pf
  | .l  => f.sf != f.of    | .ge => f.sf == f.of
  | .le => (f.sf != f.of) || f.zf
  | .g  => (f.sf == f.of) && !f.zf

def execInstr (i : Instr) (m : MachState) : MachState :=
  let len := (encode i).length
  match i with
  | .movabsRI dst imm =>
      { (setReg m dst imm) with rip := stepRip m len }
  | .addRR _ dst src =>
      let res := m.regs dst + m.regs src
      { (setReg m dst res) with flags := addFlags (m.regs dst) (m.regs src) res, rip := stepRip m len }
  | .adcRR _ dst src =>
      let c : BitVec 64 := if m.flags.cf then 1 else 0
      let res := m.regs dst + m.regs src + c
      { (setReg m dst res) with
        flags := adcFlags (m.regs dst) (m.regs src) m.flags.cf res, rip := stepRip m len }
  | .subRR _ dst src =>
      let res := m.regs dst - m.regs src
      { (setReg m dst res) with flags := subFlags (m.regs dst) (m.regs src) res, rip := stepRip m len }
  | .sbbRR _ dst src =>
      let bbit : BitVec 64 := if m.flags.cf then 1 else 0
      let res := m.regs dst - m.regs src - bbit
      { (setReg m dst res) with
        flags := sbbFlags (m.regs dst) (m.regs src) m.flags.cf res, rip := stepRip m len }
  | .andRR _ dst src =>
      let res := m.regs dst &&& m.regs src
      { (setReg m dst res) with flags := logicFlags res, rip := stepRip m len }
  | .orRR _ dst src =>
      let res := m.regs dst ||| m.regs src
      { (setReg m dst res) with flags := logicFlags res, rip := stepRip m len }
  | .xorRR _ dst src =>
      let res := m.regs dst ^^^ m.regs src
      { (setReg m dst res) with flags := logicFlags res, rip := stepRip m len }
  | .notR _ dst =>
      { (setReg m dst (~~~ m.regs dst)) with rip := stepRip m len }
  | .negR _ dst =>
      { (setReg m dst (0 - m.regs dst)) with rip := stepRip m len }
  | .imulRR _ dst src =>
      { (setReg m dst (m.regs dst * m.regs src)) with rip := stepRip m len }
  | .movRR _ dst src =>
      { (setReg m dst (m.regs src)) with rip := stepRip m len }
  | .cmpRR _ a b =>
      { m with flags := subFlags (m.regs a) (m.regs b) (m.regs a - m.regs b), rip := stepRip m len }
  | .testRR _ a b =>
      { m with flags := logicFlags (m.regs a &&& m.regs b), rip := stepRip m len }
  | .shlRI _ dst amt =>
      { (setReg m dst (m.regs dst <<< (amt.setWidth 64))) with rip := stepRip m len }
  | .shrRI _ dst amt =>
      { (setReg m dst (m.regs dst >>> shrCount64 amt)) with
        flags := shrFlags64 m.flags (m.regs dst) amt false, rip := stepRip m len }
  | .sarRI _ dst amt =>
      { (setReg m dst ((m.regs dst).sshiftRight amt.toNat)) with rip := stepRip m len }
  | .jmp rel =>
      { m with rip := m.rip + BitVec.ofNat 64 len + rel.signExtend 64 }
  | .jcc cc rel =>
      let taken := condHolds cc m.flags
      { m with rip := if taken then m.rip + BitVec.ofNat 64 len + rel.signExtend 64
                              else stepRip m len }
  | .cmovcc _ cc dst src =>
      let v := if condHolds cc m.flags then m.regs src else m.regs dst
      { (setReg m dst v) with rip := stepRip m len }
  | .setcc cc dst =>
      let v : BitVec 64 := if condHolds cc m.flags then 1 else 0
      { (setReg m dst v) with rip := stepRip m len }
  | _ =>
      { m with rip := stepRip m len }

/-- All architectural choices for the represented undefined SHR overflow flag.
    `execInstr` remains the canonical false-OF representative. -/
def execInstrChoice (i : Instr) (m : MachState) (undefinedOF : Bool) : MachState :=
  match i with
  | .shrRI _ _ amt =>
      if 1 < shrCount64 amt then
        { execInstr i m with flags := { (execInstr i m).flags with of := undefinedOF } }
      else execInstr i m
  | _ => execInstr i m

theorem execInstrChoice_false (i : Instr) (m : MachState) :
    execInstrChoice i m false = execInstr i m := by
  cases i <;> try rfl
  rename_i sz dst amt
  simp only [execInstrChoice]
  split
  · rename_i h
    have h0 : shrCount64 amt ≠ 0 := by omega
    have h1 : shrCount64 amt ≠ 1 := by omega
    simp [execInstr, shrFlags64, h0, h1]
  · rfl

/-- Every OF choice has the same masked register effect. -/
@[simp] theorem execInstrChoice_shrRI_regs (dst q : GPR) (amt : BitVec 8)
    (m : MachState) (undefinedOF : Bool) :
    (execInstrChoice (.shrRI .b64 dst amt) m undefinedOF).regs q =
      if q = dst then m.regs dst >>> shrCount64 amt else m.regs q := by
  simp only [execInstrChoice]
  split <;> rfl

/-- All defined flags agree with the masked SHR equation for every choice. -/
theorem execInstrChoice_shrRI_flags (dst : GPR) (amt : BitVec 8)
    (m : MachState) (undefinedOF : Bool) :
    (execInstrChoice (.shrRI .b64 dst amt) m undefinedOF).flags =
      shrFlags64 m.flags (m.regs dst) amt undefinedOF := by
  simp only [execInstrChoice]
  split
  · rename_i h
    have h0 : shrCount64 amt ≠ 0 := by omega
    have h1 : shrCount64 amt ≠ 1 := by omega
    simp [execInstr, shrFlags64, h0, h1]
  · rename_i h
    have hn : shrCount64 amt = 0 ∨ shrCount64 amt = 1 := by omega
    rcases hn with hn | hn <;> simp [execInstr, shrFlags64, hn]

/-- Every architectural choice preserves memory/SIMD and advances four bytes. -/
theorem execInstrChoice_shrRI_frame (dst : GPR) (amt : BitVec 8)
    (m : MachState) (undefinedOF : Bool) :
    (execInstrChoice (.shrRI .b64 dst amt) m undefinedOF).mem = m.mem ∧
    (execInstrChoice (.shrRI .b64 dst amt) m undefinedOF).xmms = m.xmms ∧
    (execInstrChoice (.shrRI .b64 dst amt) m undefinedOF).rip = m.rip + 4 := by
  simp only [execInstrChoice]
  split <;> simp [execInstr, setReg, stepRip, encode, encInstr, osPrefix, le8]

def eventOf : Instr → Event
  | .lockXaddMR _ _ _ _ => .tau
  | _                   => .tau

/-! ## 9.  Resident bytes.

    `BytesAt m a bs`: the bytes `bs` are in `m.mem` from address `a` on. `Trust.Model` defines
    `x86Step` as: some `bs` resident at `rip` decodes completely to `i`, and the step is
    `execInstr i m` with event `eventOf i`. The keystone `x86Step_decode` and the `LoweredStep`
    builders over it are in `Model.EncoderStep`. -/

def BytesAt (m : MachState) (a : BitVec 64) : List UInt8 → Prop
  | []       => True
  | bb :: bs => m.mem a = (BitVec.ofNat 8 bb.toNat) ∧ BytesAt m (a + 1) bs

/-! ## 11.  execInstr value lemmas. -/

@[simp] theorem execInstr_addRR_dst (sz : OSize) (dst src : GPR) (m : MachState) :
    (execInstr (.addRR sz dst src) m).regs dst = m.regs dst + m.regs src := by
  simp only [execInstr, setReg]
  split <;> simp_all

@[simp] theorem execInstr_addRR_other (sz : OSize) (dst src : GPR) (m : MachState) (q : GPR)
    (hq : q ≠ dst) :
    (execInstr (.addRR sz dst src) m).regs q = m.regs q := by
  simp only [execInstr, setReg]
  split <;> simp_all

@[simp] theorem execInstr_subRR_dst (sz : OSize) (dst src : GPR) (m : MachState) :
    (execInstr (.subRR sz dst src) m).regs dst = m.regs dst - m.regs src := by
  simp only [execInstr, setReg]
  split <;> simp_all

@[simp] theorem execInstr_andRR_dst (sz : OSize) (dst src : GPR) (m : MachState) :
    (execInstr (.andRR sz dst src) m).regs dst = m.regs dst &&& m.regs src := by
  simp only [execInstr, setReg]
  split <;> simp_all

@[simp] theorem execInstr_cmpRR_regs (sz : OSize) (a b : GPR) (m : MachState) (q : GPR) :
    (execInstr (.cmpRR sz a b) m).regs q = m.regs q := by
  simp only [execInstr]

@[simp] theorem execInstr_cmpRR_flags (sz : OSize) (a b : GPR) (m : MachState) :
    (execInstr (.cmpRR sz a b) m).flags
      = subFlags (m.regs a) (m.regs b) (m.regs a - m.regs b) := by
  simp only [execInstr]

@[simp] theorem execInstr_setcc_dst (cc : Cond) (dst : GPR) (m : MachState) :
    (execInstr (.setcc cc dst) m).regs dst = (if condHolds cc m.flags then 1 else 0) := by
  simp only [execInstr, setReg]
  split <;> simp_all

@[simp] theorem execInstr_addRR_rip (sz : OSize) (dst src : GPR) (m : MachState) :
    (execInstr (.addRR sz dst src) m).rip = m.rip + BitVec.ofNat 64 (encode (.addRR sz dst src)).length := by
  simp only [execInstr, setReg, stepRip]

@[simp] theorem execInstr_jcc_rip (cc : Cond) (rel : BitVec 32) (m : MachState) :
    (execInstr (.jcc cc rel) m).rip
      = (if condHolds cc m.flags
         then m.rip + BitVec.ofNat 64 (encode (.jcc cc rel)).length + rel.signExtend 64
         else m.rip + BitVec.ofNat 64 (encode (.jcc cc rel)).length) := by
  simp only [execInstr, stepRip]

/-- Full-width immediates replace exactly the destination register. -/
@[simp] theorem execInstr_movabsRI_regs (dst q : GPR) (imm : BitVec 64) (m : MachState) :
    (execInstr (.movabsRI dst imm) m).regs q = if q = dst then imm else m.regs q := by
  rfl

/-- Immediate moves preserve flags, memory and all SIMD registers. -/
theorem execInstr_movabsRI_frame (dst : GPR) (imm : BitVec 64) (m : MachState) :
    (execInstr (.movabsRI dst imm) m).flags = m.flags ∧
    (execInstr (.movabsRI dst imm) m).mem = m.mem ∧
    (execInstr (.movabsRI dst imm) m).xmms = m.xmms := by
  exact ⟨rfl, rfl, rfl⟩

@[simp] theorem execInstr_movabsRI_rip (dst : GPR) (imm : BitVec 64) (m : MachState) :
    (execInstr (.movabsRI dst imm) m).rip = m.rip + 10 := by
  simp [execInstr, stepRip, encode, encInstr, le64, le32]

/-! ## 12.  Sanity facts. -/

theorem encode_addRR_len (dst src : GPR) :
    (encode (.addRR OSize.b64 dst src)).length = 3 := by
  simp only [encode, encInstr, osPrefix, if_neg (by decide : ¬ (OSize.b64 = OSize.b16))]
  rfl

end Encoder
end Model
end Trust
