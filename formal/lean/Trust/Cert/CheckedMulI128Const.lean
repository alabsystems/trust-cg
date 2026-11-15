/-
  The arithmetic boundary for the checked-u128 constant-operand lowering.
  This module proves full-word mathematics only. It does not confer a CG
  verdict: binding and replay against the original SMT obligation is separate.
-/
import Lean.Elab.Tactic.Omega
import Init.Data.BitVec.Lemmas
import Trust.Cert.CheckedMulI128Unsigned

namespace Trust.Cert.CheckedMulI128Const

def guardedLimit (modulus divisor : Nat) : Nat :=
  if divisor = 0 then modulus - 1 else (modulus - 1) / divisor

theorem overflow_iff_limit (modulus a b : Nat)
    (positive : 0 < modulus) (inRange : a < modulus) :
    modulus ≤ a * b ↔ guardedLimit modulus b < a := by
  by_cases zero : b = 0
  · simp only [guardedLimit, zero, ↓reduceIte, Nat.mul_zero]
    omega
  · simp only [guardedLimit, zero, ↓reduceIte]
    rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero zero)]
    omega

def wordMax (width : Nat) : BitVec width :=
  BitVec.ofNat width (2 ^ width - 1)

theorem wordMax_toNat (width : Nat) :
    (wordMax width).toNat = 2 ^ width - 1 := by
  simp only [wordMax, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have positive : 0 < 2 ^ width := Nat.two_pow_pos width
  omega

-- SMT-LIB bvudiv returns all ones at zero, unlike Lean's Nat-backed /.
-- Keep this primitive faithful even though the outer actual machine guard
-- makes the division-by-zero branch unreachable.
def smtUdiv (width : Nat) (a b : BitVec width) : BitVec width :=
  if b = 0 then wordMax width else a / b

def wordLimit (width : Nat) (b : BitVec width) : BitVec width :=
  if b = 0 then wordMax width else smtUdiv width (wordMax width) b

theorem wordLimit_toNat (width : Nat) (b : BitVec width) :
    (wordLimit width b).toNat = guardedLimit (2 ^ width) b.toNat := by
  by_cases zero : b = 0
  · simp [wordLimit, zero, wordMax_toNat, guardedLimit]
  · have notZero : b.toNat ≠ 0 := by
      intro h
      apply zero
      apply BitVec.eq_of_toNat_eq
      simpa using h
    simp only [wordLimit, smtUdiv, zero, ↓reduceIte, BitVec.toNat_udiv,
      wordMax_toNat, guardedLimit, notZero]

theorem word_overflow_iff_limit (width : Nat) (a b : BitVec width) :
    2 ^ width ≤ a.toNat * b.toNat ↔ wordLimit width b < a := by
  rw [BitVec.lt_def, wordLimit_toNat]
  exact overflow_iff_limit (2 ^ width) a.toNat b.toNat
    (Nat.two_pow_pos width) a.isLt

def overflowFlag (width : Nat) (a b : BitVec width) : BitVec 1 :=
  if 2 ^ width ≤ a.toNat * b.toNat then 1 else 0

def limitFlag (width : Nat) (a b : BitVec width) : BitVec 1 :=
  if wordLimit width b < a then 1 else 0

theorem constant_limit_flag_correct (width : Nat) (a b : BitVec width) :
    overflowFlag width a b = limitFlag width a b := by
  simp only [overflowFlag, limitFlag, ← word_overflow_iff_limit]

def join128 (lo hi : BitVec 64) : BitVec 128 := (hi ++ lo).cast (by omega)

theorem constant_limit_four_limb_correct
    (aLo aHi bLo bHi : BitVec 64) :
    overflowFlag 128 (join128 aLo aHi) (join128 bLo bHi) =
    limitFlag 128 (join128 aLo aHi) (join128 bLo bHi) :=
  constant_limit_flag_correct 128 _ _

open Trust.Cert.CheckedMulI128Unsigned

/-- The source is the original wrapped limb-expression, not a replacement
    product predicate. Its reduction to the mathematical overflow predicate
    is checked through the exact source-high theorem. -/
theorem original_source_overflow (al ah bl bh : BitVec 64) :
    originalSourceBV al ah bl bh ≠ 0 ↔
      2 ^ 128 ≤ (join128BV al ah).toNat * (join128BV bl bh).toNat := by
  have source : originalSourceBV al ah bl bh ≠ 0 ↔
      originalSourceHigh al.toNat ah.toNat bl.toNat bh.toNat ≠ 0 := by
    simp only [ne_eq, ← BitVec.toNat_inj]
    change (¬ (originalSourceBV al ah bl bh).toNat = 0) ↔ _
    rw [originalSourceBV_toNat]
  rw [original_source_exact al.toNat ah.toNat bl.toNat bh.toNat
    al.isLt ah.isLt bl.isLt bh.isLt] at source
  have arithmetic :
      (al.toNat + limbBase * ah.toNat) * (bl.toNat + limbBase * bh.toNat) /
        (limbBase * limbBase) ≠ 0 ↔
      2 ^ 128 ≤ (join128BV al ah).toNat * (join128BV bl bh).toNat := by
    rw [join128BV_toNat, join128BV_toNat]
    simp only [limbBase]
    omega
  exact source.trans arithmetic

/-- Complete original constant-limit one-bit correspondence on all four
    unrestricted 64-bit inputs. Division keeps SMT-LIB's zero semantics. -/
theorem original_constant_limit_flag (al ah bl bh : BitVec 64) :
    (if originalSourceBV al ah bl bh ≠ 0 then (1 : BitVec 1) else 0) =
      (if wordLimit 128 (join128BV bl bh) < join128BV al ah
        then (1 : BitVec 1) else 0) := by
  have conditions := (original_source_overflow al ah bl bh).trans
    (word_overflow_iff_limit 128 (join128BV al ah) (join128BV bl bh))
  simp only [conditions]

-- Kernel-checkable boundary controls, not a substitute for the theorem.
example : smtUdiv 128 0 0 = wordMax 128 := by decide
example : smtUdiv 128 (wordMax 128) 0 = wordMax 128 := by decide
example : guardedLimit (2 ^ 128) 0 = 2 ^ 128 - 1 := by decide
example : ¬ (2 ^ 128 ≤ (2 ^ 128 - 1) * 1) := by decide
example : ¬ (guardedLimit (2 ^ 128) 1 < 2 ^ 128 - 1) := by decide
example : 2 ^ 128 ≤ 2 ^ 64 * 2 ^ 64 := by decide
example : guardedLimit (2 ^ 128) (2 ^ 64) < 2 ^ 64 := by decide

-- The wrong >= boundary claims overflow at MAX * 1.
example : guardedLimit (2 ^ 128) 1 ≤ 2 ^ 128 - 1 ∧
    ¬ (2 ^ 128 ≤ (2 ^ 128 - 1) * 1) := by decide
-- Dropping the zero-divisor guard uses Nat.div-by-zero=0 and is wrong.
example : (2 ^ 128 - 1) / 0 < 1 ∧ ¬ (2 ^ 128 ≤ 1 * 0) := by decide

#print axioms overflow_iff_limit
#print axioms constant_limit_flag_correct
#print axioms constant_limit_four_limb_correct
#print axioms original_source_overflow
#print axioms original_constant_limit_flag

end Trust.Cert.CheckedMulI128Const
