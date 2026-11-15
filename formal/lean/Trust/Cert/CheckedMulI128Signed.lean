/-
  Exact signed division-free i128 flag arithmetic. This theorem does not
  register a production verdict or replace original SMT/CIC correspondence.
-/
import Trust.Cert.CheckedMulI128Unsigned

set_option autoImplicit false
namespace Trust.Cert.CheckedMulI128Signed
open Trust.Cert.CheckedMulI128Unsigned

def low64BV (x : BitVec 128) : BitVec 64 := x.truncate 64

def signNegative (x : BitVec 128) : Bool := decide (x.extractLsb' 127 1 = 1)

def signMask (x : BitVec 64) : BitVec 64 := x.sshiftRight 63

def boolMask (negative : Bool) : BitVec 64 := if negative then BitVec.allOnes 64 else 0

def maskedLow (lo mask : BitVec 64) : BitVec 64 := (lo ^^^ mask) - mask

def maskedHigh (lo hi mask : BitVec 64) : BitVec 64 :=
  (hi ^^^ mask) - mask - (((lo ||| (0 - lo)) >>> (63 : Nat)) &&& mask)

def magnitude (x : BitVec 128) : BitVec 128 := if signNegative x then -x else x

def resultNegative (a b : BitVec 128) : Bool := !(signNegative a == signNegative b)

def unsignedCore (al ah bl bh p1 : BitVec 64) : Prop :=
  let t := (limbProductBV ah bl).truncate 64 + (limbProductBV al bh).truncate 64
  high64BV (limbProductBV ah bl) ≠ 0 ∨
    high64BV (limbProductBV al bh) ≠ 0 ∨ p1 < t ∨ (ah ≠ 0 ∧ bh ≠ 0)

instance (al ah bl bh p1 : BitVec 64) : Decidable (unsignedCore al ah bl bh p1) := by
  unfold unsignedCore
  infer_instance

def originalSourceSignedFlag (al ah bl bh : BitVec 64) : Prop :=
  let a := join128BV al ah
  let b := join128BV bl bh
  let ua := magnitude a
  let ub := magnitude b
  let high := originalSourceBV (low64BV ua) (high64BV ua) (low64BV ub) (high64BV ub)
  let low := ua * ub
  let limit : BitVec 128 := if resultNegative a b then
    170141183460469231731687303715884105728 else 170141183460469231731687303715884105727
  high ≠ 0 ∨ limit < low

def machineMagnitudeCore (a b : BitVec 128) : Prop :=
  let r := a * b
  let ma := signMask (high64BV a)
  let mb := signMask (high64BV b)
  let mn := ma ^^^ mb
  unsignedCore
    (maskedLow (low64BV a) ma) (maskedHigh (low64BV a) (high64BV a) ma)
    (maskedLow (low64BV b) mb) (maskedHigh (low64BV b) (high64BV b) mb)
    (maskedHigh (low64BV r) (high64BV r) mn)

def machineSignBad (a b : BitVec 128) : Prop :=
  let r := a * b
  let mn := signMask (high64BV a) ^^^ signMask (high64BV b)
  signMask (high64BV r) ^^^ mn ≠ 0 ∧
    low64BV r ||| high64BV r ≠ 0

def originalMachineSignedFlag (al ah bl bh : BitVec 64) : Prop :=
  let a := join128BV al ah
  let b := join128BV bl bh
  machineMagnitudeCore a b ∨ machineSignBad a b

instance (al ah bl bh : BitVec 64) : Decidable (originalSourceSignedFlag al ah bl bh) := by
  unfold originalSourceSignedFlag
  infer_instance

instance (al ah bl bh : BitVec 64) : Decidable (originalMachineSignedFlag al ah bl bh) := by
  unfold originalMachineSignedFlag machineMagnitudeCore machineSignBad
  infer_instance

theorem boolMask_bit (negative : Bool) (i : Nat) (hi : i < 64) :
    (boolMask negative)[i] = negative := by
  cases negative
  · change (0 : BitVec 64)[i] = false
    simp
  · change (BitVec.allOnes 64)[i] = true
    exact BitVec.getElem_allOnes i hi

theorem signMask_word (x : BitVec 64) : signMask x = boolMask x.msb := by
  ext i hi
  rw [boolMask_bit]
  simp only [signMask, BitVec.getElem_sshiftRight]
  split
  · have iz : i = 0 := by omega
    subst i
    exact (BitVec.msb_eq_getLsbD_last x).symm
  · rfl

theorem signNegative_msb (x : BitVec 128) : signNegative x = x.msb := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_extractLsb']
  apply Bool.eq_iff_iff.mpr
  simp [signNegative]

theorem high64_msb (x : BitVec 128) : (high64BV x).msb = x.msb := by
  simp [high64BV, BitVec.truncate, BitVec.msb_eq_getLsbD_last]

theorem signMask_actual (x : BitVec 128) :
    signMask (high64BV x) = boolMask (signNegative x) := by
  rw [signMask_word, high64_msb, signNegative_msb]

theorem low64_toNat (x : BitVec 128) : (low64BV x).toNat = x.toNat % limbBase := rfl

theorem top_bit_word (x : BitVec 64) :
    x >>> (63 : Nat) = if x.msb then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  have bound := x.isLt
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  split <;> simp_all <;> omega

theorem or_neg_msb (x : BitVec 64) : (x ||| -x).msb = decide (x ≠ 0) := by
  by_cases hx : x = 0
  · subst x
    decide
  · have positive : (0 : BitVec 64) < x := by bv_omega
    have bound := x.isLt
    rw [BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide,
      BitVec.toNat_neg_of_pos positive]
    rw [show decide (x ≠ 0) = true by apply decide_eq_true; bv_omega]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega

theorem borrow_nonzero (x : BitVec 64) :
    (x ||| (0 - x)) >>> (63 : Nat) = if x = 0 then 0 else 1 := by
  change (x ||| -x) >>> (63 : Nat) = if x = 0 then 0 else 1
  rw [top_bit_word, or_neg_msb]
  by_cases hx : x = 0 <;> simp [hx]

theorem maskedLow_transport (x : BitVec 128) (negative : Bool) :
    maskedLow (low64BV x) (boolMask negative) =
      low64BV (if negative then -x else x) := by
  cases negative
  · simp [maskedLow, boolMask]
  · apply BitVec.eq_of_toNat_eq
    have bound := x.isLt
    simp only [boolMask, if_true, maskedLow, BitVec.xor_allOnes,
      BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes, low64_toNat,
      BitVec.toNat_neg]
    simp only [limbBase] at *
    omega

theorem maskedHigh_transport (x : BitVec 128) (negative : Bool) :
    maskedHigh (low64BV x) (high64BV x) (boolMask negative) =
      high64BV (if negative then -x else x) := by
  cases negative
  · simp [maskedHigh, boolMask]
  · simp only [maskedHigh, boolMask, if_true, BitVec.xor_allOnes,
      borrow_nonzero, BitVec.and_allOnes]
    split
    next hx =>
      apply BitVec.eq_of_toNat_eq
      have bound := x.isLt
      have low_zero : x.toNat % limbBase = 0 := by
        have zero : (low64BV x).toNat = 0 := by bv_omega
        simpa only [low64_toNat] using zero
      simp [BitVec.toNat_sub, BitVec.toNat_not, high64BV_toNat,
        BitVec.toNat_neg, limbBase] at *
      omega
    next hx =>
      apply BitVec.eq_of_toNat_eq
      have bound := x.isLt
      have low_nonzero : (low64BV x).toNat ≠ 0 := by bv_omega
      simp [BitVec.toNat_sub, BitVec.toNat_not,
        high64BV_toNat, BitVec.toNat_neg, low64_toNat, limbBase] at *
      omega

theorem xor_sign_masks (a b : BitVec 128) :
    signMask (high64BV a) ^^^ signMask (high64BV b) = boolMask (resultNegative a b) := by
  rw [signMask_actual, signMask_actual]
  unfold resultNegative boolMask
  cases signNegative a <;> cases signNegative b <;> decide

theorem join_actual_limbs (x : BitVec 128) : join128BV (low64BV x) (high64BV x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [join128BV_toNat, low64_toNat, high64BV_toNat]
  exact Nat.mod_add_div x.toNat limbBase

/-- This is a ring identity at the actual width, not a nonlinear solver premise. -/
theorem magnitude_product (a b : BitVec 128) :
    (if resultNegative a b then -(a * b) else a * b) = magnitude a * magnitude b := by
  unfold resultNegative magnitude
  cases signNegative a <;> cases signNegative b <;> simp

theorem mask_xor_nonzero (a b : Bool) :
    boolMask a ^^^ boolMask b ≠ 0 ↔ a ≠ b := by
  cases a <;> cases b <;> decide

theorem limbs_nonzero (x : BitVec 128) :
    low64BV x ||| high64BV x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst x
    simp [low64BV, high64BV] at h
  · intro hx hz
    have both := BitVec.or_eq_zero_iff.mp hz
    apply hx
    rw [← join_actual_limbs x, both.1, both.2]
    rfl

theorem signNegative_toNat (x : BitVec 128) :
    signNegative x = decide (170141183460469231731687303715884105728 ≤ x.toNat) := by
  rw [signNegative_msb, BitVec.msb_eq_decide]

/-- Exact sign/zero reduction for an unrestricted full 128-bit product residue. -/
theorem signed_limit_reduction (p : BitVec 128) (negative : Bool) :
    ((if negative then (170141183460469231731687303715884105728 : BitVec 128)
      else 170141183460469231731687303715884105727) < p) ↔
      (signMask (high64BV (if negative then -p else p)) ^^^ boolMask negative ≠ 0 ∧
        low64BV (if negative then -p else p) |||
          high64BV (if negative then -p else p) ≠ 0) := by
  rw [signMask_actual, mask_xor_nonzero, limbs_nonzero]
  cases negative
  · simp [signNegative_toNat]
    bv_omega
  · simp [signNegative_toNat]
    bv_omega

theorem magnitude_low (a : BitVec 128) :
    maskedLow (low64BV a) (signMask (high64BV a)) = low64BV (magnitude a) := by
  rw [signMask_actual, maskedLow_transport]
  rfl

theorem magnitude_high (a : BitVec 128) :
    maskedHigh (low64BV a) (high64BV a) (signMask (high64BV a)) =
      high64BV (magnitude a) := by
  rw [signMask_actual, maskedHigh_transport]
  rfl

theorem product_magnitude_high (a b : BitVec 128) :
    maskedHigh (low64BV (a * b)) (high64BV (a * b))
      (signMask (high64BV a) ^^^ signMask (high64BV b)) =
        high64BV (magnitude a * magnitude b) := by
  rw [xor_sign_masks, maskedHigh_transport, magnitude_product]

/-- The machine's original masked limbs and masked raw-product high limb
    are transported to the actual unsigned instance; no product is free. -/
theorem machine_core_unsigned (a b : BitVec 128) :
    machineMagnitudeCore a b ↔
      originalMachineBV (low64BV (magnitude a)) (high64BV (magnitude a))
        (low64BV (magnitude b)) (high64BV (magnitude b)) := by
  dsimp only [machineMagnitudeCore]
  rw [magnitude_low, magnitude_high, magnitude_low, magnitude_high, product_magnitude_high]
  unfold originalMachineBV
  rw [join_actual_limbs, join_actual_limbs]
  rfl

theorem machine_core_correct (a b : BitVec 128) :
    machineMagnitudeCore a b ↔
      originalSourceBV (low64BV (magnitude a)) (high64BV (magnitude a))
        (low64BV (magnitude b)) (high64BV (magnitude b)) ≠ 0 := by
  rw [machine_core_unsigned]
  exact (original_unsigned_limb_check_bv _ _ _ _).symm

theorem raw_product_transport (a b : BitVec 128) :
    a * b = if resultNegative a b then -(magnitude a * magnitude b)
      else magnitude a * magnitude b := by
  rw [← magnitude_product]
  cases resultNegative a b <;> simp

theorem machine_sign_correct (a b : BitVec 128) :
    machineSignBad a b ↔
      ((if resultNegative a b then
          (170141183460469231731687303715884105728 : BitVec 128)
        else 170141183460469231731687303715884105727) < magnitude a * magnitude b) := by
  dsimp only [machineSignBad]
  rw [xor_sign_masks, raw_product_transport]
  exact (signed_limit_reduction _ _).symm

/-- Exact original signed overflow correspondence over four unrestricted
    64-bit limbs. The magnitudes, raw product, XOR sign, zero guard and both
    original source limbs all remain in the independently checked equation. -/
theorem original_signed_limb_check (al ah bl bh : BitVec 64) :
    originalSourceSignedFlag al ah bl bh ↔ originalMachineSignedFlag al ah bl bh := by
  dsimp only [originalSourceSignedFlag, originalMachineSignedFlag]
  exact or_congr (machine_core_correct _ _).symm (machine_sign_correct _ _).symm

theorem original_signed_limb_check_flag (al ah bl bh : BitVec 64) :
    (if originalSourceSignedFlag al ah bl bh then (1 : BitVec 1) else 0) =
      (if originalMachineSignedFlag al ah bl bh then (1 : BitVec 1) else 0) := by
  simp only [original_signed_limb_check]

end Trust.Cert.CheckedMulI128Signed
