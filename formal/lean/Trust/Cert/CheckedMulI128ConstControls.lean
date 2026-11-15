/- Hostile mathematical boundary controls. No production verdict is granted. -/
import Trust.Cert.CheckedMulI128Const

namespace Trust.Cert.CheckedMulI128ConstControls
open Trust.Cert.CheckedMulI128Unsigned
open Trust.Cert.CheckedMulI128Const

abbrev max64 : BitVec 64 := 18446744073709551615
abbrev sign64 : BitVec 64 := 9223372036854775808

def sourceFlag (al ah bl bh : BitVec 64) : BitVec 1 :=
  if originalSourceBV al ah bl bh ≠ 0 then 1 else 0

def geFlag (al ah bl bh : BitVec 64) : BitVec 1 :=
  if wordLimit 128 (join128BV bl bh) ≤ join128BV al ah then 1 else 0

def plusOneFlag (al ah bl bh : BitVec 64) : BitVec 1 :=
  if wordLimit 128 (join128BV bl bh) + 1 < join128BV al ah then 1 else 0

def ignoredHighFlag (al ah bl bh : BitVec 64) : BitVec 1 :=
  if wordLimit 128 ((join128BV bl bh).truncate 64 |>.setWidth 128) <
      join128BV al ah then 1 else 0

def narrowFlag (al ah bl bh : BitVec 64) : BitVec 1 :=
  if wordLimit 64 ((join128BV bl bh).truncate 64) <
      (join128BV al ah).truncate 64 then 1 else 0

def signedFlag (al ah bl bh : BitVec 64) : BitVec 1 :=
  if (wordLimit 128 (join128BV bl bh)).toInt < (join128BV al ah).toInt then 1 else 0

-- This intentionally wrong primitive also drops the outer machine guard:
-- Lean / returns zero at zero, whereas SMT-LIB bvudiv returns all ones.
def wrongNatZeroFlag (al ah bl bh : BitVec 64) : BitVec 1 :=
  if wordMax 128 / join128BV bl bh < join128BV al ah then 1 else 0

def swappedDivisorFlag (al ah bl bh : BitVec 64) : BitVec 1 :=
  if wordLimit 128 (join128BV bh bl) < join128BV al ah then 1 else 0

theorem ge_counterexample : sourceFlag max64 max64 1 0 ≠ geFlag max64 max64 1 0 := by decide
theorem plusOne_counterexample : sourceFlag 0 1 0 1 ≠ plusOneFlag 0 1 0 1 := by decide
theorem ignoredHigh_counterexample : sourceFlag 0 1 0 1 ≠ ignoredHighFlag 0 1 0 1 := by decide
theorem narrow_counterexample : sourceFlag 0 1 0 1 ≠ narrowFlag 0 1 0 1 := by decide
theorem signed_counterexample : sourceFlag 0 sign64 2 0 ≠ signedFlag 0 sign64 2 0 := by decide
theorem wrongNatZero_counterexample : sourceFlag 1 0 0 0 ≠ wrongNatZeroFlag 1 0 0 0 := by decide
theorem swappedDivisor_counterexample : sourceFlag 0 1 1 0 ≠ swappedDivisorFlag 0 1 1 0 := by decide

#print axioms ge_counterexample
#print axioms plusOne_counterexample
#print axioms ignoredHigh_counterexample
#print axioms narrow_counterexample
#print axioms signed_counterexample
#print axioms wrongNatZero_counterexample
#print axioms swappedDivisor_counterexample
end Trust.Cert.CheckedMulI128ConstControls
