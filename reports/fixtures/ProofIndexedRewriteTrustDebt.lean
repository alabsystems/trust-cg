-- ProofIndexedRewriteTrustDebt.lean
-- A proof-indexed rewrite module that carries explicit trust debt.
--
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Copyright 2026 Andrew Yates | License: Apache-2.0
--
-- Replayed by the certified-pass checker in semantic mode as a NEGATIVE
-- fixture. The obligation below is closed with `sorry`, i.e. it is not
-- actually proven. A conforming Lean5 must report "declaration uses explicit
-- sorry" and exit non-zero, and the certified-pass checker must fail closed
-- rather than accept the rewrite. This file exists so that the fail-closed
-- path is exercised end to end; it must never be treated as a valid proof.

namespace ProofIndexedRewriteTrustDebt

def BV (w : Nat) : Type := Fin (2 ^ w)

def bvEq {w : Nat} (a b : BV w) : Prop := a = b

/-- An indexed rewrite step whose soundness obligation is left as trust debt. -/
structure RewriteStep (w : Nat) where
  step : Nat
  lhs : BV w
  rhs : BV w

/-- This obligation is NOT discharged: it relies on `sorry`. The certified
    pass checker must reject any module reaching this declaration. -/
theorem step_unsound_trust_debt {w : Nat} (s : RewriteStep w) :
    bvEq s.lhs s.rhs := by
  sorry

end ProofIndexedRewriteTrustDebt
