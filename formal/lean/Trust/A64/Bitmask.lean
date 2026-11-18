/-
  A64.Bitmask — the Arm ARM `DecodeBitMasks` function over natural numbers.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  `DecodeBitMasks(immN, imms, immr, immediate, M)` (Arm ARM, shared pseudocode J1) turns the
  `N:immr:imms` fields of a logical-immediate or bitfield instruction into the pair
  `(wmask, tmask)`.  The logical-immediate value is `wmask`; the bitfield instructions use both.
  This module transcribes the pseudocode step for step over `Nat` (bit vectors are their
  unsigned values) and proves that, for the logical-immediate encoding, it is defined exactly
  when `Trust.A64.bitmaskValid` accepts the fields — the validity the instruction-word decoder
  enforces.  No `sorry`, no `axiom`.
-/
import Trust.A64.Encoding
import Trust.A64.LogicalImmBits

namespace Trust
namespace A64

/-- `HighestSetBit` of a 7-bit value, `none` for zero (Arm ARM `HighestSetBit` returns -1). -/
def highestSetBit7 (v : Nat) : Option Nat :=
  if v ≥ 64 then some 6 else if v ≥ 32 then some 5 else if v ≥ 16 then some 4
  else if v ≥ 8 then some 3 else if v ≥ 4 then some 2 else if v ≥ 2 then some 1
  else if v ≥ 1 then some 0 else none

/-- `Ones(k)`: the value whose low `k` bits are set. -/
def ones (k : Nat) : Nat := 2 ^ k - 1

/-- `ROR(x, r)` of an `e`-bit value. -/
def rorBits (e x r : Nat) : Nat :=
  let r := r % e
  (x / 2 ^ r) + (x % 2 ^ r) * 2 ^ (e - r)

/-- `Replicate(x)` of an `e`-bit element to `count` copies (low copy first). -/
def replicateBits (e x : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => x + replicateBits e x count * 2 ^ e

/-- Arm ARM `DecodeBitMasks(immN, imms, immr, immediate, M)`, `none` where the pseudocode is
    UNDEFINED (or its `M >= esize` assertion fails).  Returns `(wmask, tmask)`. -/
def decodeBitMasks (immN imms immr : Nat) (immediate : Bool) (m : Nat) : Option (Nat × Nat) :=
  match highestSetBit7 (immN * 64 + (63 - imms % 64)) with
  | none => none
  | some len =>
    if len < 1 then none else
    let levels := ones len
    if immediate && imms % 2 ^ len == levels then none else
    let esize := 2 ^ len
    if m < esize then none else
    let s := imms % 2 ^ len
    let r := immr % 2 ^ len
    let d := (s + esize - r) % esize
    let welem := ones (s + 1)
    let telem := ones (d + 1)
    some (replicateBits esize (rorBits esize welem r) (m / esize),
          replicateBits esize telem (m / esize))

/-- The value of a logical immediate `N:immr:imms` at register width `m` (`wmask`). -/
def logicalImmValue (immN immr imms m : Nat) : Option Nat :=
  (decodeBitMasks immN imms immr true m).map Prod.fst

/-- The logical-immediate fields the decoder accepts are exactly the ones `DecodeBitMasks`
    defines at 64 bits (checked by kernel evaluation over every `N`, `imms` and `immr`). -/
theorem bitmaskValid_iff_decodeBitMasks :
    ∀ n, n < 2 → ∀ imms, imms < 64 → ∀ immr, immr < 64 →
      bitmaskValid n imms = (decodeBitMasks n imms immr true 64).isSome := by
  decide +kernel

/-! ## Compiled logical-immediate encoding -/

/-- The source of the power table used by the encoder. -/
def logicalImmPower (i : UInt64) : UInt64 :=
  trust_cg_a64_logical_imm_mul
    (trust_cg_a64_logical_imm_pow_lo (trust_cg_a64_logical_imm_pow_index i))
    (trust_cg_a64_logical_imm_pow_hi (trust_cg_a64_logical_imm_pow_group i))

theorem logicalImmPower_eq : ∀ i : Fin 65,
    logicalImmPower (UInt64.ofNat i.val) = UInt64.ofNat (2 ^ i.val) := by
  decide +kernel

theorem logicalImmMask_toNat : ∀ e : Fin 65,
    (trust_cg_a64_logical_imm_mask (logicalImmPower (UInt64.ofNat e.val))).toNat = ones e.val := by
  decide +kernel

theorem logicalImmExtract_toNat (e : Fin 65) (value : UInt64) :
    (trust_cg_a64_logical_imm_extract value
      (trust_cg_a64_logical_imm_mask (logicalImmPower (UInt64.ofNat e.val)))).toNat =
      value.toNat % 2 ^ e.val := by
  simp only [trust_cg_a64_logical_imm_extract, UInt64.toNat_and, logicalImmMask_toNat,
    ones, Nat.and_two_pow_sub_one_eq_mod]

/-- Rotate a run of ones by splitting off the part that wraps to the high end. -/
def logicalImmRotatedElement (elementWidth onesLen rotation : UInt64) : UInt64 :=
  let wrap := trust_cg_a64_logical_imm_wrap_count onesLen rotation
  trust_cg_a64_logical_imm_rotate (logicalImmPower (onesLen - wrap)) (logicalImmPower wrap)
    (logicalImmPower (elementWidth - rotation))

theorem rorOnes_eq (e l r : Nat) (hr : r < e) :
    rorBits e (ones l) r = ones (l - min l r) + ones (min l r) * 2 ^ (e - r) := by
  unfold rorBits
  rw [Nat.mod_eq_of_lt hr]
  by_cases h : l ≤ r
  · have hpow : 2 ^ l ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) h
    have hlt : 2 ^ l - 1 < 2 ^ r := by
      have := Nat.two_pow_pos l
      omega
    simp [Nat.min_eq_left h, ones, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
  · have hrl : r ≤ l := by omega
    have hpow : 2 ^ l = 2 ^ (l - r) * 2 ^ r := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hrl]
    have hprod : 2 ^ r ≤ 2 ^ (l - r) * 2 ^ r := by
      have hp : 1 ≤ 2 ^ (l - r) := Nat.two_pow_pos _
      simpa using Nat.mul_le_mul_right (2 ^ r) hp
    have partition : 2 ^ l - 1 = 2 ^ r * (2 ^ (l - r) - 1) + (2 ^ r - 1) := by
      rw [hpow, Nat.mul_sub, Nat.mul_one, Nat.mul_comm (2 ^ r) (2 ^ (l - r))]
      have := Nat.two_pow_pos r
      omega
    have hlt : 2 ^ r - 1 < 2 ^ r := by
      have := Nat.two_pow_pos r
      omega
    simp [Nat.min_eq_right hrl, ones, partition, Nat.mul_add_div (Nat.two_pow_pos r),
      Nat.div_eq_of_lt hlt]

theorem replicateBits_eq_mul (e x count : Nat) :
    replicateBits e x count = x * replicateBits e 1 count := by
  induction count with
  | zero => simp [replicateBits]
  | succ k ih =>
    simp only [replicateBits, ih, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]

theorem replicateBits_low (e x count : Nat) (hx : x < 2 ^ e) :
    replicateBits e x (count + 1) % 2 ^ e = x := by
  simp [replicateBits, Nat.add_mod, Nat.mod_eq_of_lt hx]

/-- Check repetition once per width and match individual candidates against the low element. -/
theorem replicateBits_match_iff (e x count raw : Nat) (hx : x < 2 ^ e) :
    replicateBits e x (count + 1) = raw ↔
      replicateBits e (raw % 2 ^ e) (count + 1) = raw ∧ x = raw % 2 ^ e := by
  constructor
  · intro h
    have hx' : x = raw % 2 ^ e := by rw [← h, replicateBits_low e x count hx]
    refine ⟨?_, hx'⟩
    rwa [← hx']
  · rintro ⟨h, hx'⟩
    rwa [hx']

theorem replicateBits_lt (e x count : Nat) (hx : x < 2 ^ e) :
    replicateBits e x count < (2 ^ e) ^ count := by
  induction count with
  | zero => simp [replicateBits]
  | succ count ih =>
    rw [replicateBits, Nat.pow_succ]
    have h := Nat.mul_le_mul_right (2 ^ e) (Nat.succ_le_of_lt ih)
    rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at h
    omega

theorem logicalImmRepeatFactor_toNat : ∀ width e : Fin 65,
    (width.val = 32 ∧ e.val ∈ [2, 4, 8, 16, 32] ∨
      width.val = 64 ∧ e.val ∈ [2, 4, 8, 16, 32, 64]) →
    (trust_cg_a64_logical_imm_repeat_factor (UInt64.ofNat width.val) (UInt64.ofNat e.val)).toNat =
      replicateBits e.val 1 (width.val / e.val) := by
  decide +kernel

theorem logicalImmReplicate_toNat (width e : Fin 65) (element : UInt64)
    (domain : width.val = 32 ∧ e.val ∈ [2, 4, 8, 16, 32] ∨
      width.val = 64 ∧ e.val ∈ [2, 4, 8, 16, 32, 64])
    (helem : element.toNat < 2 ^ e.val) :
    (trust_cg_a64_logical_imm_mul element
      (trust_cg_a64_logical_imm_repeat_factor (UInt64.ofNat width.val) (UInt64.ofNat e.val))).toNat =
      replicateBits e.val element.toNat (width.val / e.val) := by
  rw [trust_cg_a64_logical_imm_mul, UInt64.toNat_mul,
    logicalImmRepeatFactor_toNat width e domain, ← replicateBits_eq_mul]
  apply Nat.mod_eq_of_lt
  have hb := replicateBits_lt e.val element.toNat (width.val / e.val) helem
  rw [← Nat.pow_mul] at hb
  have he := Nat.mul_div_le width.val e.val
  have hwidth : width.val ≤ 64 := by omega
  exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (Nat.le_trans he hwidth))

/-- Canonical N and imms agree bit for bit with the size prefix and run length. -/
theorem logicalImmFields_eq : ∀ e l : Fin 65, e.val ∈ [2, 4, 8, 16, 32, 64] →
    0 < l.val → l.val < e.val →
    let width := UInt32.ofNat e.val
    let onesLen := UInt32.ofNat l.val
    let n := trust_cg_a64_logical_imm_n width
    n = (if e.val = 64 then 1 else 0) ∧
      trust_cg_a64_logical_imm_imms width n onesLen =
        ((~~~((width <<< 1) - 1)) &&& 63) ||| (onesLen - 1) := by
  decide +kernel

/-- The source of the encoder's canonical fields, related to the original architectural decoder. -/
def canonicalLogicalImmMatchesDecode (e width : Nat) : Prop :=
  ∀ l r : Fin e, l.val > 0 →
    let elementWidth := UInt64.ofNat e
    let element := logicalImmRotatedElement elementWidth (UInt64.ofNat l.val) (UInt64.ofNat r.val)
    let factor := trust_cg_a64_logical_imm_repeat_factor (UInt64.ofNat width) elementWidth
    let n := trust_cg_a64_logical_imm_n (UInt32.ofNat e)
    let s := trust_cg_a64_logical_imm_imms (UInt32.ofNat e) n (UInt32.ofNat l.val)
    logicalImmValue n.toNat r.val s.toNat width =
      some (trust_cg_a64_logical_imm_mul element factor).toNat

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem canonicalLogicalImm32_decode :
    canonicalLogicalImmMatchesDecode 2 32 ∧ canonicalLogicalImmMatchesDecode 4 32 ∧
    canonicalLogicalImmMatchesDecode 8 32 ∧ canonicalLogicalImmMatchesDecode 16 32 ∧
    canonicalLogicalImmMatchesDecode 32 32 := by
  unfold canonicalLogicalImmMatchesDecode
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem canonicalLogicalImm64_decode :
    canonicalLogicalImmMatchesDecode 2 64 ∧ canonicalLogicalImmMatchesDecode 4 64 ∧
    canonicalLogicalImmMatchesDecode 8 64 ∧ canonicalLogicalImmMatchesDecode 16 64 ∧
    canonicalLogicalImmMatchesDecode 32 64 ∧ canonicalLogicalImmMatchesDecode 64 64 := by
  unfold canonicalLogicalImmMatchesDecode
  decide +kernel

private theorem cpop_setWidth (x : BitVec w) (hle : w ≤ v) :
    (x.setWidth v).cpop.toNat = x.cpop.toNat := by
  rw [BitVec.setWidth_eq_append hle, BitVec.cpop_cast, BitVec.toNat_cast, BitVec.toNat_cpop_append]
  simp

private theorem cpop_ones (w n : Nat) (hle : n ≤ w) :
    (BitVec.ofNat w (ones n)).cpop.toNat = n := by
  have h : BitVec.ofNat w (ones n) = (BitVec.allOnes n).setWidth w := by
    apply BitVec.eq_of_toNat_eq
    simp [ones]
  rw [h, cpop_setWidth _ hle]
  simp [Nat.mod_eq_of_lt Nat.lt_two_pow_self]

private theorem ones_lt_pow (n w : Nat) (hle : n ≤ w) : ones n < 2 ^ w := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) hle
  have hp := Nat.two_pow_pos n
  unfold ones
  omega

private theorem cpop_ror_ones (e l r : Nat) (hr : r < e) (hl : l ≤ e) (he : e ≤ 64) :
    (BitVec.ofNat 64 (rorBits e (ones l) r)).cpop.toNat = l := by
  let a := BitVec.ofNat r (ones (min l r))
  let b := BitVec.ofNat (e - r) (ones (l - min l r))
  have hla : min l r ≤ r := Nat.min_le_right _ _
  have hlb : l - min l r ≤ e - r := by omega
  have ha : a.toNat = ones (min l r) := Nat.mod_eq_of_lt (ones_lt_pow _ _ hla)
  have hb : b.toNat = ones (l - min l r) := Nat.mod_eq_of_lt (ones_lt_pow _ _ hlb)
  have heq : BitVec.ofNat 64 (rorBits e (ones l) r) = (a ++ b).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_append, ha, hb,
      rorOnes_eq _ _ _ hr]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (ones_lt_pow _ _ hlb), Nat.shiftLeft_eq, Nat.add_comm]
  rw [heq, cpop_setWidth _ (by omega), BitVec.toNat_cpop_append]
  change (BitVec.ofNat r (ones (min l r))).cpop.toNat +
    (BitVec.ofNat (e - r) (ones (l - min l r))).cpop.toNat = l
  rw [cpop_ones _ _ hla, cpop_ones _ _ hlb]
  omega

private def logicalImmStarts (e : Nat) (element : UInt64) : UInt64 :=
  element &&& ~~~((element <<< 1) ||| (element >>> (UInt64.ofNat e - 1)))

private def logicalImmStartBit (e r : Nat) : UInt64 :=
  logicalImmPower (UInt64.ofNat ((e - r) % e))

private def logicalImmStartMatches (e r : Nat) (starts : UInt64) : Bool :=
  let start := starts.toBitVec.ctz.toNat
  starts != 0 && (starts &&& (starts - 1)) == 0 && decide (start < e) &&
    ((UInt64.ofNat e - UInt64.ofNat start) &&& (UInt64.ofNat e - 1)).toNat == r

private def logicalImmCandidateGeometry (e : Nat) : Prop :=
  ∀ l r : Fin e, l.val > 0 →
    let element := logicalImmRotatedElement (UInt64.ofNat e) (UInt64.ofNat l.val) (UInt64.ofNat r.val)
    element = UInt64.ofNat (rorBits e (ones l.val) r.val) ∧
      logicalImmStarts e element = logicalImmStartBit e r.val

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
private theorem logicalImmCandidateGeometry_all :
    logicalImmCandidateGeometry 2 ∧ logicalImmCandidateGeometry 4 ∧ logicalImmCandidateGeometry 8 ∧
    logicalImmCandidateGeometry 16 ∧ logicalImmCandidateGeometry 32 ∧ logicalImmCandidateGeometry 64 := by
  unfold logicalImmCandidateGeometry
  decide +kernel

private def logicalImmStartInverts (e : Nat) : Prop :=
  ∀ r : Fin e, logicalImmStartMatches e r.val (logicalImmStartBit e r.val) = true

private theorem logicalImmStartInverts_all :
    logicalImmStartInverts 2 ∧ logicalImmStartInverts 4 ∧ logicalImmStartInverts 8 ∧
    logicalImmStartInverts 16 ∧ logicalImmStartInverts 32 ∧ logicalImmStartInverts 64 := by
  unfold logicalImmStartInverts
  decide +kernel

/-- The candidate probe recovers each canonical rotation from the circular run's start and length. -/
def logicalImmCandidateInverts (e : Nat) : Prop :=
  ∀ l r : Fin e, l.val > 0 →
    let element := logicalImmRotatedElement (UInt64.ofNat e) (UInt64.ofNat l.val) (UInt64.ofNat r.val)
    element = UInt64.ofNat (rorBits e (ones l.val) r.val) ∧
      logicalImmStartMatches e r.val (logicalImmStarts e element) = true ∧
      element.toBitVec.cpop.toNat = l.val

private theorem logicalImmCandidateInverts_of_geometry (e : Nat) (he : e ≤ 64)
    (geometry : logicalImmCandidateGeometry e) (starts : logicalImmStartInverts e) :
    logicalImmCandidateInverts e := by
  intro l r hl
  have ⟨hrotation, hstart⟩ := geometry l r hl
  dsimp only
  refine ⟨hrotation, ?_, ?_⟩
  · rw [hstart]
    exact starts r
  · rw [hrotation]
    exact cpop_ror_ones e l.val r.val r.isLt (Nat.le_of_lt l.isLt) he

theorem logicalImmCandidate_matches_rotate :
    logicalImmCandidateInverts 2 ∧ logicalImmCandidateInverts 4 ∧
    logicalImmCandidateInverts 8 ∧ logicalImmCandidateInverts 16 ∧
    logicalImmCandidateInverts 32 ∧ logicalImmCandidateInverts 64 := by
  obtain ⟨g2, g4, g8, g16, g32, g64⟩ := logicalImmCandidateGeometry_all
  obtain ⟨s2, s4, s8, s16, s32, s64⟩ := logicalImmStartInverts_all
  exact ⟨logicalImmCandidateInverts_of_geometry 2 (by decide) g2 s2,
    logicalImmCandidateInverts_of_geometry 4 (by decide) g4 s4,
    logicalImmCandidateInverts_of_geometry 8 (by decide) g8 s8,
    logicalImmCandidateInverts_of_geometry 16 (by decide) g16 s16,
    logicalImmCandidateInverts_of_geometry 32 (by decide) g32 s32,
    logicalImmCandidateInverts_of_geometry 64 (by decide) g64 s64⟩

end A64
end Trust
