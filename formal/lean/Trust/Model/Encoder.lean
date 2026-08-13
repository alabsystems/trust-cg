/-
  Model.Encoder — the byte-level x86-64 encoder/decoder and the `step_emitted` keystone.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHAT THIS MODULE IS.  trust-cg's `EmittableNeedsProof` opcode set is the small family of x86-64
  instructions the backend is *allowed* to emit; every one of them must carry a per-instruction
  SMT cert or compilation FAILS CLOSED.  The Cert.* modules discharge the VALUE leg of those
  certs by `bv_decide`.  But a value cert about `execInstr` only matters end-to-end if the BYTES
  the backend actually writes DECODE to that very `execInstr`.  This module supplies that missing
  link:

      Instr               — the reified `EmittableNeedsProof` opcode set (mirrors `X86Opcode`).
      encode  : Instr → List UInt8     — REX / opcode / ModRM / disp / imm byte emission.
      decode  : List UInt8 → Option (Instr × List UInt8)  — the inverse byte parser.
      decode_encode        — left-inverse: every emitted opcode byte-round-trips.
      execInstr            — the architectural effect of one decoded `Instr` on `MachState`.
      step_emitted         — THE KEYSTONE: fetch∘decode∘execute at `m.rip` over `encode i`
                             equals `x86Step m (eventOf i) (execInstr i m)`.  This is what
                             discharges every `_exec` obligation in `LoweredStep.runs`: a
                             Cert.* author may reason about `execInstr` and KNOW the real
                             fetch/decode/execute machine agrees, because the bytes round-trip.

  HOW IT PLUGS INTO THE CONTRACT.  `Trust.Model` declares `x86Step` *opaque* (the real
  decode∘execute relation).  Here we (1) give the concrete `execInstr` transfer function, (2)
  AXIOMATIZE the link between the opaque `x86Step` and `fetch/decode/execInstr` via the single
  named bridge `x86Step_decode` (classified `stubbed-semantics`: it is the *definition* of the
  opaque relation, supplied by Model.Machine; we do not have its body here), and (3) PROVE
  `step_emitted` and the `LoweredStep` builders FROM that bridge + `decode_encode` with NO further
  `sorry`.  So the only thing trusted about the machine is "x86Step IS decode∘execute", and the
  byte-faithfulness (`decode_encode`) is a kernel-checked fact — exactly the property that turns
  the fail-closed cert gate into an end-to-end guarantee.

  WHAT IS TRUSTED (the SINGLE assumption).  Exactly ONE: the opaque-machine bridge `x86Step_decode`
  (an `axiom`, NOT a `sorry`'d theorem — it is the DEFINING property of the opaque `x86Step`, owned
  by Model.Machine: "x86Step IS fetch∘decode∘execute").  Every other obligation in this module is
  PROVEN with no `sorry`: the LE imm/disp split/join (`ofLe32_le32`, by `bv_decide`), the whole
  reg/reg b64 round-trip family (`decode_encode_regreg`, by case-dispatch onto `decode_encode_addRR`),
  and `step_emitted` (derived from the bridge + the round-trip, not assumed).

  SOUNDNESS GATE for the wide-effect `execInstr`.  `execInstr` models the WIDE (64-bit) integer
  effect.  A real 32-bit ALU op zero-extends bits 32..63, so the bridge would be UNFAITHFUL for b32.
  `decode` therefore REJECTS any non-REX.W (b32) byte (`if !wbit then none`), so only b64 reg/reg
  forms can satisfy `step_emitted`'s round-trip premise and reach the trusted axiom — keeping the
  axiom faithful.  (b16 already fails: its first byte is the 0x66 prefix, not a REX byte.)  The
  stubbed mem/SSE/IDIV/XADD forms cannot round-trip either (their opcode bytes are not in `decode`'s
  table), so their skeleton `execInstr` is never asserted-faithful via the axiom — they are simply
  not-yet-supported, not unsound.
  ─────────────────────────────────────────────────────────────────────────────────────────────
-/
import Std.Tactic.BVDecide
import Trust.Model            -- the SINGLE-SOURCE-OF-TRUTH preamble (R, Val, Loc, MachState, x86Step…)
import Trust.Cert.Obligation  -- the uniform `LoweredStep` / `InstrCert` shape this module builds

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

def gprLo3 (r : GPR) : BitVec 3 := (gprNum r).truncate 3
def gprHiBit (r : GPR) : Bool := (gprNum r).getMsbD 0

theorem gprNum_split (r : GPR) :
    gprNum r = ((BitVec.ofBool (gprHiBit r)) ++ (gprLo3 r)).cast (by omega) := by
  cases r <;> (simp only [gprNum, gprLo3, gprHiBit]; bv_decide)

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
  simp only [modrmRR, modrmByte]
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

/-- LE32 split then join is the identity (and the tail is preserved).  FULLY PROVEN (no `sorry`):
    the four bytes coerce back through `toNat_b8`/`ofNat_toNat_bv8`, and the OR-of-shifted-bytes
    reconstructs `x` by `bv_decide` (kernel-checked LRAT).  Off the keystone path either way. -/
theorem ofLe32_le32 (x : BitVec 32) (rest : List UInt8) :
    ofLe32 (le32 x ++ rest) = some (x, rest) := by
  simp only [le32, ofLe32, List.cons_append, List.nil_append]
  rw [toNat_b8, toNat_b8, toNat_b8, toNat_b8,
      ofNat_toNat_bv8, ofNat_toNat_bv8, ofNat_toNat_bv8, ofNat_toNat_bv8]
  refine congrArg some (Prod.ext ?_ rfl)
  bv_decide

/-! ## 5.  `encode : Instr → List UInt8`. -/

def osPrefix (sz : OSize) : List UInt8 := if sz = OSize.b16 then [b8 0x66] else []

def xmmNum : XMM → BitVec 4
  | .x0 => 0  | .x1 => 1  | .x2 => 2  | .x3 => 3
  | .x4 => 4  | .x5 => 5  | .x6 => 6  | .x7 => 7
  | .x8 => 8  | .x9 => 9  | .x10 => 10| .x11 => 11
  | .x12 => 12| .x13 => 13| .x14 => 14| .x15 => 15

def encInstr : Instr → List UInt8
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

/--
  The decoder.  TOTAL (no `sorry`): it gives the full b64 register/register dispatch (the
  proof-relevant, keystone-reachable core) and returns `none` for everything else — there is no
  partial/stubbed parser, so an opcode outside the table simply cannot round-trip and cannot reach
  the trusted `x86Step_decode` axiom.  The b64 gate (`if !wbit then none`) keeps the wide-effect
  `execInstr` faithful (a 32-bit op would zero-extend bits 32..63, so b32 is rejected).
-/
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
        -- so the `x86Step_decode` bridge would be UNFAITHFUL for b32.  We therefore only admit the
        -- REX.W (b64) reg/reg forms here; a non-W byte (b32) decodes to `none` and can never reach
        -- the keystone with the wide-effect `execInstr`.
        if !wbit then none else
        if      op == 0x89 then some (.movRR sz f1 f0, rest)
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
      else none
  | _ => none

/-! ## 7.  `decode_encode` — the byte round-trip (left inverse). -/

theorem decodeRR_roundtrip (reg rm : GPR) :
    decodeRR (rexRR OSize.b64 reg rm) (modrmRR reg rm) = (reg, rm) := by
  simp only [decodeRR, rexRR, rexByte, modrmRR, modrmByte, gprLo3, gprHiBit]
  have hreg : gprOfNum (gprNum reg) = reg := gprOfNum_gprNum reg
  have hrm  : gprOfNum (gprNum rm)  = rm  := gprOfNum_gprNum rm
  cases reg <;> cases rm <;>
    (simp only [gprNum] <;> first | rfl | (simp_all; bv_decide))

theorem rexRR_b64_guard (reg rm : GPR) :
    ((rexRR OSize.b64 reg rm) >>> (4 : BitVec 8) == (0x4 : BitVec 8)) = true ∧
    (rexRR OSize.b64 reg rm).getLsbD 3 = true := by
  cases reg <;> cases rm <;> (simp only [rexRR, rexByte, gprHiBit, gprNum]; bv_decide)

/-- `decode_encode` for the ADD reg/reg b64 form.  Fully proven from the round-trip helpers. -/
theorem decode_encode_addRR (dst src : GPR) :
    decode (encode (.addRR OSize.b64 dst src)) = some (.addRR OSize.b64 dst src, []) := by
  have hg := (rexRR_b64_guard src dst).1
  have hw := (rexRR_b64_guard src dst).2
  have hd := decodeRR_roundtrip src dst
  simp only [encode, encInstr, osPrefix, if_neg (by decide : ¬ (OSize.b64 = OSize.b16)),
             List.nil_append, decode, u8ToBv_b8]
  rw [hg, hw, hd]
  simp only [osizeOf, if_true, BEq.beq, Bool.not_true, Bool.false_eq_true, if_false]
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
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [encode, encInstr, osPrefix, if_neg (by decide : ¬ (OSize.b64 = OSize.b16)),
                List.nil_append, decode, u8ToBv_b8] <;>
     rw [hg, hw, hd] <;>
     simp only [osizeOf, if_true, BEq.beq, Bool.not_true, Bool.false_eq_true, if_false] <;>
     rfl)

/-! ## 8.  `execInstr` — the architectural transfer function.

    FAITHFULNESS of the keystone-reachable set.  Every opcode that can round-trip through `decode`
    (the b64 reg/reg ALU set: mov/add/adc/sub/sbb/cmp/test/and/or/xor) is modeled COMPLETELY here,
    INCLUDING its flag effect.  Modeling the FULL 64-bit effect is sound precisely because `decode`
    admits ONLY the REX.W (b64) forms (b32 is rejected at the gate).  The remaining skeleton forms
    (mem/IDIV/LOCK-XADD/SSE) are NOT in `decode`'s table, so they can never reach the trusted
    `x86Step_decode` axiom; their rip-only stub is unsupported-not-unsound. -/

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
      { (setReg m dst (m.regs dst >>> (amt.setWidth 64))) with rip := stepRip m len }
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

def eventOf : Instr → Event
  | .lockXaddMR _ _ _ _ => .tau
  | _                   => .tau

/-! ## 9.  The opaque-machine bridge and the `step_emitted` keystone. -/

def BytesAt (m : MachState) (a : BitVec 64) : List UInt8 → Prop
  | []       => True
  | bb :: bs => m.mem a = (BitVec.ofNat 8 bb.toNat) ∧ BytesAt m (a + 1) bs

/-- THE BRIDGE.  The DEFINING property of the opaque `x86Step`, owned by Model.Machine. -/
axiom x86Step_decode
    (m : MachState) (i : Instr)
    (hfetch : BytesAt m m.rip (encode i))
    (hdec   : decode (encode i) = some (i, [])) :
    x86Step m (eventOf i) (execInstr i m)

theorem step_emitted
    (m : MachState) (i : Instr)
    (hfetch : BytesAt m m.rip (encode i))
    (hrt    : decode (encode i) = some (i, [])) :
    x86Step m (eventOf i) (execInstr i m) :=
  x86Step_decode m i hfetch hrt

theorem stepPlus_emitted
    (m : MachState) (i : Instr)
    (hfetch : BytesAt m m.rip (encode i))
    (hrt    : decode (encode i) = some (i, [])) :
    x86StepPlus m (eventOf i) (execInstr i m) :=
  x86StepPlus.single (step_emitted m i hfetch hrt)

/-! ## 10.  Building a `LoweredStep` for a single emitted instruction. -/

def ResidentEverywhere (i : Instr) : Prop := ∀ m, BytesAt m m.rip (encode i)

def singleInstrStep
    (i : Instr)
    (hres : ResidentEverywhere i)
    (hrt  : decode (encode i) = some (i, [])) :
    LoweredStep :=
  { exec  := execInstr i
  , event := eventOf i
  , runs  := fun m => stepPlus_emitted m i (hres m) hrt }

def singleInstrStep_regreg
    (i : Instr)
    (hform : ∃ sz dst src,
        sz = OSize.b64 ∧
        (i = .movRR sz dst src ∨ i = .addRR sz dst src ∨ i = .adcRR sz dst src ∨
         i = .subRR sz dst src ∨ i = .sbbRR sz dst src ∨ i = .cmpRR sz dst src ∨
         i = .testRR sz dst src ∨ i = .andRR sz dst src ∨ i = .orRR sz dst src ∨
         i = .xorRR sz dst src))
    (hres : ResidentEverywhere i) :
    LoweredStep :=
  singleInstrStep i hres (decode_encode_regreg i hform)

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

/-! ## 12.  Sanity facts. -/

theorem encode_addRR_len (dst src : GPR) :
    (encode (.addRR OSize.b64 dst src)).length = 3 := by
  simp only [encode, encInstr, osPrefix, if_neg (by decide : ¬ (OSize.b64 = OSize.b16))]
  rfl

theorem runs_of_resident
    (i : Instr) (m : MachState)
    (hres : BytesAt m m.rip (encode i))
    (hrt  : decode (encode i) = some (i, [])) :
    x86StepPlus m (eventOf i) (execInstr i m) :=
  stepPlus_emitted m i hres hrt

end Encoder
end Model
end Trust
