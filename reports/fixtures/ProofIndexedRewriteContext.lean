-- ProofIndexedRewriteContext.lean
-- Context-sensitive proof-indexed rewrite obligations.
--
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Copyright 2026 Andrew Yates | License: Apache-2.0
--
-- Replayed by the certified-pass checker in semantic mode. These obligations
-- show that a proof-indexed rewrite remains sound when embedded in a larger
-- expression context (congruence), which is the property the trust-cg-opt
-- rewriter relies on when it applies a local rewrite inside a function body.

namespace ProofIndexedRewriteContext

def BV (w : Nat) : Type := Fin (2 ^ w)

def bvEq {w : Nat} (a b : BV w) : Prop := a = b

theorem bvEq_refl {w : Nat} (a : BV w) : bvEq a a := rfl

/-- A single-hole context over bitvector expressions. -/
structure Context (w : Nat) where
  apply : BV w → BV w
  congr : ∀ {a b : BV w}, bvEq a b → bvEq (apply a) (apply b)

/-- The empty context is just the hole. -/
def holeContext {w : Nat} : Context w :=
  { apply := id
    congr := fun h => h }

theorem hole_apply {w : Nat} (a : BV w) : holeContext.apply a = a := rfl

/-- A rewrite that is sound at the hole stays sound under any context. -/
theorem rewrite_under_context {w : Nat}
    (C : Context w) {a b : BV w} (h : bvEq a b) :
    bvEq (C.apply a) (C.apply b) := C.congr h

theorem rewrite_under_hole {w : Nat} {a b : BV w} (h : bvEq a b) :
    bvEq (holeContext.apply a) (holeContext.apply b) :=
  rewrite_under_context holeContext h

/-- Contexts compose, and congruence composes with them. -/
def composeContext {w : Nat} (C D : Context w) : Context w :=
  { apply := fun x => C.apply (D.apply x)
    congr := fun h => C.congr (D.congr h) }

theorem composeContext_apply {w : Nat} (C D : Context w) (a : BV w) :
    (composeContext C D).apply a = C.apply (D.apply a) := rfl

theorem rewrite_under_composed {w : Nat}
    (C D : Context w) {a b : BV w} (h : bvEq a b) :
    bvEq ((composeContext C D).apply a) ((composeContext C D).apply b) :=
  (composeContext C D).congr h

/-- A proof index records which context a rewrite was admitted under. -/
structure ContextIndex where
  pass : String
  depth : Nat
  deriving Repr, DecidableEq

theorem context_index_depth (idx : ContextIndex) : idx.depth = idx.depth := rfl

/-- Identity congruence: rewriting `a` to itself is sound under any context. -/
theorem refl_under_context {w : Nat} (C : Context w) (a : BV w) :
    bvEq (C.apply a) (C.apply a) := C.congr (bvEq_refl a)

theorem refl_under_composed {w : Nat} (C D : Context w) (a : BV w) :
    bvEq ((composeContext C D).apply a) ((composeContext C D).apply a) :=
  (composeContext C D).congr (bvEq_refl a)

/-- Associativity of context composition (definitional). -/
theorem composeContext_assoc {w : Nat} (C D E : Context w) (a : BV w) :
    (composeContext (composeContext C D) E).apply a
      = (composeContext C (composeContext D E)).apply a := rfl

theorem hole_left_id {w : Nat} (C : Context w) (a : BV w) :
    (composeContext holeContext C).apply a = C.apply a := rfl

theorem hole_right_id {w : Nat} (C : Context w) (a : BV w) :
    (composeContext C holeContext).apply a = C.apply a := rfl

end ProofIndexedRewriteContext
