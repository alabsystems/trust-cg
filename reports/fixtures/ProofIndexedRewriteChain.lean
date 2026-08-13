-- ProofIndexedRewriteChain.lean
-- Chained proof-indexed rewrite obligations.
--
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Copyright 2026 Andrew Yates | License: Apache-2.0
--
-- Replayed by the certified-pass checker in semantic mode. A certified pass
-- emits an ordered chain of rewrite steps; this module proves that folding a
-- chain of individually-sound, proof-indexed steps yields a single sound
-- rewrite from the chain's source to its target.

namespace ProofIndexedRewriteChain

def BV (w : Nat) : Type := Fin (2 ^ w)

def bvEq {w : Nat} (a b : BV w) : Prop := a = b

theorem bvEq_refl {w : Nat} (a : BV w) : bvEq a a := rfl
theorem bvEq_trans {w : Nat} {a b c : BV w}
    (h₁ : bvEq a b) (h₂ : bvEq b c) : bvEq a c := h₁.trans h₂

/-- One indexed rewrite step in a chain. -/
structure Link (w : Nat) where
  step : Nat
  lhs : BV w
  rhs : BV w
  sound : bvEq lhs rhs

/-- A chain is a list of links whose endpoints are tracked by the index. -/
inductive Chain (w : Nat) : BV w → BV w → Type where
  | nil (a : BV w) : Chain w a a
  | cons {a b c : BV w} (link : Link w)
      (hlhs : link.lhs = a) (hrhs : link.rhs = b)
      (rest : Chain w b c) : Chain w a c

/-- The semantic obligation discharged by replaying a whole chain. -/
def Chain.sound {w : Nat} : {a b : BV w} → Chain w a b → bvEq a b
  | _, _, .nil a => bvEq_refl a
  | _, _, .cons link hlhs hrhs rest =>
      bvEq_trans (hlhs ▸ hrhs ▸ link.sound) rest.sound

theorem nil_sound {w : Nat} (a : BV w) : bvEq a a := (Chain.nil a).sound

theorem single_sound {w : Nat} (link : Link w) :
    bvEq link.lhs link.rhs := link.sound

/-- Appending two chains preserves soundness. -/
def Chain.append {w : Nat} : {a b c : BV w} →
    Chain w a b → Chain w b c → Chain w a c
  | _, _, _, .nil _, ys => ys
  | _, _, _, .cons link hlhs hrhs rest, ys =>
      .cons link hlhs hrhs (rest.append ys)

theorem append_sound {w : Nat} {a b c : BV w}
    (xs : Chain w a b) (ys : Chain w b c) :
    bvEq a c := (xs.append ys).sound

theorem chain_step_count_nonneg {w : Nat} (link : Link w) :
    0 ≤ link.step := Nat.zero_le _

/-- A proof index for the chain records the pass and chain length. -/
structure ChainIndex where
  pass : String
  length : Nat
  deriving Repr, DecidableEq

theorem chain_index_length (idx : ChainIndex) : idx.length = idx.length := rfl

theorem chain_endpoints_equal {w : Nat} {a b : BV w} (c : Chain w a b) :
    bvEq a b := c.sound

theorem chain_refl_endpoints {w : Nat} (a : BV w) :
    bvEq a a := (Chain.nil a).sound

end ProofIndexedRewriteChain
