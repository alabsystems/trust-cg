-- ProofIndexedRewriteSemantic.lean
-- Minimal proof-indexed rewrite module for the semantic-mode base fixture.
--
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Copyright 2026 Andrew Yates | License: Apache-2.0
--
-- Replayed by the certified-pass checker in semantic mode. This is the small
-- base fixture used by the generic semantic-mode tests (version probe, digest
-- mismatch, timeout, trust-debt override). It states two trivially-sound
-- proof-indexed rewrite obligations so that `lean5 check` reports two passing
-- declarations.

namespace ProofIndexedRewriteSemantic

def BV (w : Nat) : Type := Fin (2 ^ w)

def bvEq {w : Nat} (a b : BV w) : Prop := a = b

/-- A proof-indexed rewrite from `a` to itself is sound. -/
theorem refl_rewrite_sound {w : Nat} (a : BV w) : bvEq a a := rfl

/-- A proof-indexed rewrite is symmetric. -/
theorem rewrite_symm {w : Nat} {a b : BV w} (h : bvEq a b) : bvEq b a := h.symm

end ProofIndexedRewriteSemantic
