/-
  Concrete counterexamples for deleting any original unsigned overflow arm.
  These are theorem-statement controls, not a production proof authority.
-/
import Trust.Cert.CheckedMulI128Unsigned

set_option autoImplicit false
namespace Trust.Cert.CheckedMulI128Unsigned.Controls

def omittedArm (omitted : Nat) (al ah bl bh : BitVec 64) : Prop :=
  let p1 := high64BV (join128BV al ah * join128BV bl bh)
  let t := (limbProductBV ah bl).truncate 64 + (limbProductBV al bh).truncate 64
  (omitted ≠ 0 ∧ high64BV (limbProductBV ah bl) ≠ 0) ∨
    (omitted ≠ 1 ∧ high64BV (limbProductBV al bh) ≠ 0) ∨
    (omitted ≠ 2 ∧ p1 < t) ∨ (omitted ≠ 3 ∧ ah ≠ 0 ∧ bh ≠ 0)

instance (omitted : Nat) (al ah bl bh : BitVec 64) :
    Decidable (omittedArm omitted al ah bl bh) := by
  unfold omittedArm
  infer_instance

theorem deleted_o1_counterexample :
    originalSourceBV 0 2 9223372036854775808 0 ≠ 0 ∧
      ¬ omittedArm 0 0 2 9223372036854775808 0 := by decide

theorem deleted_o2_counterexample :
    originalSourceBV 9223372036854775808 0 0 2 ≠ 0 ∧
      ¬ omittedArm 1 9223372036854775808 0 0 2 := by decide

theorem deleted_carry_counterexample :
    originalSourceBV 18446744073709551615 0 18446744073709551615 1 ≠ 0 ∧
      ¬ omittedArm 2 18446744073709551615 0 18446744073709551615 1 := by decide

theorem deleted_both_high_counterexample :
    originalSourceBV 0 1 0 1 ≠ 0 ∧ ¬ omittedArm 3 0 1 0 1 := by decide

#print axioms original_source_exact
#print axioms original_unsigned_limb_check
#print axioms originalSourceBV_toNat
#print axioms originalMachineBV_iff
#print axioms original_unsigned_limb_check_flag
#print axioms deleted_o1_counterexample
#print axioms deleted_o2_counterexample
#print axioms deleted_carry_counterexample
#print axioms deleted_both_high_counterexample

end Trust.Cert.CheckedMulI128Unsigned.Controls
