/-
  StrengthReduction — modular product recurrence across arbitrary edge traces.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  For every register width, initial value, stride, and finite sequence of
  incoming edges, advancing a product by that edge's step times the stride
  agrees with multiplying the source induction value. No no-overflow premise
  or common-step assumption is needed. This is a value theorem, not a theorem
  about Rust CFG construction, SSA dominance, allocation, or machine bytes.
-/
import Init.Data.BitVec.Lemmas

namespace Trust.Optimization.StrengthReduction

-- `stepFor` describes the admitted update on each original incoming edge.
-- These value theorems do not establish that machine CFG edges, register
-- definitions, initialization, or the emitted phi actually implement it.
def sourceAfter {w : Nat} {Edge : Type} (stepFor : Edge → BitVec w)
    (initial : BitVec w) (edges : List Edge) : BitVec w :=
  edges.foldl (fun iv edge => iv + stepFor edge) initial

def productAfter {w : Nat} {Edge : Type} (stepFor : Edge → BitVec w)
    (stride product : BitVec w) (edges : List Edge) : BitVec w :=
  edges.foldl (fun value edge => value + stepFor edge * stride) product

theorem edge_update {w : Nat} (iv step stride : BitVec w) :
    iv * stride + step * stride = (iv + step) * stride := by
  exact BitVec.add_mul.symm

theorem every_finite_edge_trace {w : Nat} {Edge : Type}
    (stepFor : Edge → BitVec w) (stride initial : BitVec w) (edges : List Edge) :
    productAfter stepFor stride (initial * stride) edges =
      sourceAfter stepFor initial edges * stride := by
  induction edges generalizing initial with
  | nil => rfl
  | cons edge edges ih =>
    simp only [productAfter, sourceAfter, List.foldl_cons]
    rw [edge_update]
    exact ih (initial + stepFor edge)

end Trust.Optimization.StrengthReduction
