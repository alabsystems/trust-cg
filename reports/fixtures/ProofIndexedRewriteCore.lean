-- ProofIndexedRewriteCore.lean
-- Proof-indexed rewrite core obligations for trust-cg certified passes.
--
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Copyright 2026 Andrew Yates | License: Apache-2.0
--
-- This module is a Lean5 proof artifact replayed by the certified-pass
-- checker in semantic mode. It states the core proof-indexed rewrite
-- obligations: each rewrite step preserves bitvector semantics under the
-- proof index that the trust-cg-opt pass emitted. The certified-pass
-- checker only verifies the transport digest and that Lean5 accepts the
-- module fail-closed; the declarations below are the proof obligations
-- replayed by `lean5 check`.

namespace ProofIndexedRewriteCore

/-- Abstract bitvector value indexed by width. -/
def BV (w : Nat) : Type := Fin (2 ^ w)

/-- A proof index identifies one admitted rewrite step. -/
structure ProofIndex where
  pass : String
  step : Nat
  deriving Repr, DecidableEq

/-- Semantic equality of two bitvector values at a fixed width. -/
def bvEq {w : Nat} (a b : BV w) : Prop := a = b

theorem bvEq_refl {w : Nat} (a : BV w) : bvEq a a := rfl

theorem bvEq_symm {w : Nat} {a b : BV w} (h : bvEq a b) : bvEq b a := h.symm

theorem bvEq_trans {w : Nat} {a b c : BV w}
    (h₁ : bvEq a b) (h₂ : bvEq b c) : bvEq a c := h₁.trans h₂

/-- A core rewrite step carries the index it was admitted under. -/
structure RewriteStep (w : Nat) where
  index : ProofIndex
  lhs : BV w
  rhs : BV w
  sound : bvEq lhs rhs

theorem step_preserves {w : Nat} (s : RewriteStep w) : bvEq s.lhs s.rhs := s.sound

theorem step_preserves_symm {w : Nat} (s : RewriteStep w) : bvEq s.rhs s.lhs :=
  bvEq_symm s.sound

/-- The identity rewrite is always sound at any width. -/
def idStep {w : Nat} (a : BV w) (idx : ProofIndex) : RewriteStep w :=
  { index := idx, lhs := a, rhs := a, sound := bvEq_refl a }

theorem idStep_sound {w : Nat} (a : BV w) (idx : ProofIndex) :
    bvEq (idStep a idx).lhs (idStep a idx).rhs := (idStep a idx).sound

theorem idStep_lhs {w : Nat} (a : BV w) (idx : ProofIndex) :
    (idStep a idx).lhs = a := rfl

theorem idStep_rhs {w : Nat} (a : BV w) (idx : ProofIndex) :
    (idStep a idx).rhs = a := rfl

/-- Two steps with matching endpoints compose to a sound step. -/
def composeStep {w : Nat} (s t : RewriteStep w) (h : bvEq s.rhs t.lhs) :
    RewriteStep w :=
  { index := s.index
    lhs := s.lhs
    rhs := t.rhs
    sound := bvEq_trans s.sound (bvEq_trans h t.sound) }

theorem composeStep_sound {w : Nat} (s t : RewriteStep w) (h : bvEq s.rhs t.lhs) :
    bvEq (composeStep s t h).lhs (composeStep s t h).rhs :=
  (composeStep s t h).sound

theorem composeStep_lhs {w : Nat} (s t : RewriteStep w) (h : bvEq s.rhs t.lhs) :
    (composeStep s t h).lhs = s.lhs := rfl

theorem composeStep_rhs {w : Nat} (s t : RewriteStep w) (h : bvEq s.rhs t.lhs) :
    (composeStep s t h).rhs = t.rhs := rfl

theorem index_stable {w : Nat} (s t : RewriteStep w) (h : bvEq s.rhs t.lhs) :
    (composeStep s t h).index = s.index := rfl

end ProofIndexedRewriteCore
