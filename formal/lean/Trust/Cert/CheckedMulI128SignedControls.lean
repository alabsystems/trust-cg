/- Exact finite statement controls; no compiler/proof-gate authority. -/
import Trust.Cert.CheckedMulI128Signed

set_option autoImplicit false
namespace Trust.Cert.CheckedMulI128Signed.Controls
open Trust.Cert.CheckedMulI128Unsigned

inductive Mutation
  | noZeroGuard | noSignCheck | noMagnitudeCore | orSign | rawHigh | rawCore | unsignedDispatch
  deriving DecidableEq

/-- The seven existing Rust signed controls, preserving the same raw formulas
    except for the named mutation. This is not a production mode switch. -/
def mutantFlag (mode : Mutation) (al ah bl bh : BitVec 64) : Prop :=
  if mode = .unsignedDispatch then originalMachineBV al ah bl bh else
  let a := join128BV al ah
  let b := join128BV bl bh
  let r := a * b
  let ma := signMask (high64BV a)
  let mb := signMask (high64BV b)
  let ua0 := if mode = .rawCore then low64BV a else maskedLow (low64BV a) ma
  let ua1 := if mode = .rawCore then high64BV a else maskedHigh (low64BV a) (high64BV a) ma
  let ub0 := if mode = .rawCore then low64BV b else maskedLow (low64BV b) mb
  let ub1 := if mode = .rawCore then high64BV b else maskedHigh (low64BV b) (high64BV b) mb
  let mn := if mode = .orSign then ma ||| mb else ma ^^^ mb
  let pu1 := if mode = .rawCore ∨ mode = .rawHigh then high64BV r else
    maskedHigh (low64BV r) (high64BV r) mn
  let ou := unsignedCore ua0 ua1 ub0 ub1 pu1
  let sign := signMask (high64BV r) ^^^ mn ≠ 0
  let bad := if mode = .noZeroGuard then sign else
    sign ∧ low64BV r ||| high64BV r ≠ 0
  if mode = .noSignCheck then ou else if mode = .noMagnitudeCore then bad else ou ∨ bad

instance (mode : Mutation) (al ah bl bh : BitVec 64) :
    Decidable (mutantFlag mode al ah bl bh) := by
  unfold mutantFlag
  infer_instance

theorem zero_guard_indispensable :
    decide (originalSourceSignedFlag 0 9223372036854775808 0 0) ≠
      decide (mutantFlag .noZeroGuard 0 9223372036854775808 0 0) := by decide

theorem sign_check_indispensable :
    decide (originalSourceSignedFlag 18446744073709551615 18446744073709551615
      0 9223372036854775808) ≠
    decide (mutantFlag .noSignCheck 18446744073709551615 18446744073709551615
      0 9223372036854775808) := by decide

theorem magnitude_core_indispensable :
    decide (originalSourceSignedFlag 3 0 6148914691236517206 6148914691236517205) ≠
      decide (mutantFlag .noMagnitudeCore 3 0 6148914691236517206 6148914691236517205) := by decide

theorem xor_sign_indispensable :
    decide (originalSourceSignedFlag 0 9223372036854775808
      18446744073709551615 18446744073709551615) ≠
    decide (mutantFlag .orSign 0 9223372036854775808
      18446744073709551615 18446744073709551615) := by decide

theorem masked_product_high_indispensable :
    decide (originalSourceSignedFlag 14304268710930555488 18446744073709551615
      15199015601233879320 4) ≠
    decide (mutantFlag .rawHigh 14304268710930555488 18446744073709551615
      15199015601233879320 4) := by decide

theorem magnitude_conversion_indispensable :
    decide (originalSourceSignedFlag 2 0 0 13835058055282163712) ≠
      decide (mutantFlag .rawCore 2 0 0 13835058055282163712) := by decide

theorem signed_dispatch_indispensable :
    decide (originalSourceSignedFlag 18446744073709551615 18446744073709551615 2 0) ≠
      decide (mutantFlag .unsignedDispatch 18446744073709551615 18446744073709551615 2 0) := by decide

/-- Exact zero, MIN times negative/positive one, positive limit, sign and signed/unsigned
    boundary controls, evaluated on both unchanged original expressions. -/
theorem signed_edge_cases :
    (¬ originalSourceSignedFlag 0 9223372036854775808 0 0 ∧
     ¬ originalMachineSignedFlag 0 9223372036854775808 0 0) ∧
    (originalSourceSignedFlag 0 9223372036854775808 18446744073709551615 18446744073709551615 ∧
     originalMachineSignedFlag 0 9223372036854775808 18446744073709551615 18446744073709551615) ∧
    (¬ originalSourceSignedFlag 0 9223372036854775808 1 0 ∧
     ¬ originalMachineSignedFlag 0 9223372036854775808 1 0) ∧
    (¬ originalSourceSignedFlag 18446744073709551615 9223372036854775807 1 0 ∧
     ¬ originalMachineSignedFlag 18446744073709551615 9223372036854775807 1 0) ∧
    (originalSourceSignedFlag 18446744073709551615 9223372036854775807 2 0 ∧
     originalMachineSignedFlag 18446744073709551615 9223372036854775807 2 0) ∧
    (¬ originalSourceSignedFlag 18446744073709551615 18446744073709551615
      18446744073709551615 18446744073709551615 ∧
     ¬ originalMachineSignedFlag 18446744073709551615 18446744073709551615
      18446744073709551615 18446744073709551615) ∧
    (¬ originalSourceSignedFlag 18446744073709551615 18446744073709551615 2 0 ∧
     ¬ originalMachineSignedFlag 18446744073709551615 18446744073709551615 2 0) ∧
    (¬ originalSourceSignedFlag 2 0 0 13835058055282163712 ∧
     ¬ originalMachineSignedFlag 2 0 0 13835058055282163712) := by decide

#print axioms maskedLow_transport
#print axioms maskedHigh_transport
#print axioms magnitude_product
#print axioms machine_core_correct
#print axioms signed_limit_reduction
#print axioms original_signed_limb_check_flag
#print axioms zero_guard_indispensable
#print axioms sign_check_indispensable
#print axioms magnitude_core_indispensable
#print axioms xor_sign_indispensable
#print axioms masked_product_high_indispensable
#print axioms magnitude_conversion_indispensable
#print axioms signed_dispatch_indispensable
#print axioms signed_edge_cases

end Trust.Cert.CheckedMulI128Signed.Controls
