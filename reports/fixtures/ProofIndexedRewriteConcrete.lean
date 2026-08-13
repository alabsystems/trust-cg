-- ProofIndexedRewriteConcrete.lean
-- Concrete proof-indexed rewrite obligations over fixed-width bitvectors.
--
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Copyright 2026 Andrew Yates | License: Apache-2.0
--
-- Replayed by the certified-pass checker in semantic mode. These are the
-- concrete (fully evaluated) instances of the proof-indexed rewrites: every
-- obligation is discharged by `decide`/`rfl` on a concrete 8-bit bitvector
-- so the Lean5 kernel re-checks the arithmetic with no `sorry`.

namespace ProofIndexedRewriteConcrete

/-- 8-bit bitvector represented as a bounded natural. -/
abbrev BV8 := Fin 256

def add (a b : BV8) : BV8 := a + b
def mul (a b : BV8) : BV8 := a * b

theorem add_comm_concrete (a b : BV8) : add a b = add b a := by
  simp [add, Fin.add_comm]

theorem mul_comm_concrete (a b : BV8) : mul a b = mul b a := by
  simp [mul, Fin.mul_comm]

theorem add_zero_concrete (a : BV8) : add a 0 = a := by
  simp [add]

theorem mul_one_concrete (a : BV8) : mul a 1 = a := by
  simp [mul]

theorem mul_zero_concrete (a : BV8) : mul a 0 = 0 := by
  simp [mul]

-- Concrete witnesses re-checked by the kernel.
example : add 1 2 = 3 := by decide
example : add 200 100 = 44 := by decide
example : mul 16 16 = 0 := by decide
example : mul 15 15 = 225 := by decide
example : add 255 1 = 0 := by decide
example : add 128 128 = 0 := by decide
example : mul 3 5 = 15 := by decide
example : mul 0 200 = 0 := by decide
example : add 0 0 = 0 := by decide
example : add 100 100 = 200 := by decide
example : mul 1 1 = 1 := by decide
example : mul 2 128 = 0 := by decide
example : add 250 10 = 4 := by decide
example : add 7 8 = 15 := by decide
example : mul 4 64 = 0 := by decide
example : mul 5 5 = 25 := by decide
example : add 1 254 = 255 := by decide
example : add 99 1 = 100 := by decide
example : mul 17 15 = 255 := by decide
example : add 200 56 = 0 := by decide

/-- A concrete rewrite index pins the pass and a literal step counter. -/
structure ConcreteIndex where
  pass : String
  step : Nat
  deriving Repr, DecidableEq

theorem concrete_index_step (idx : ConcreteIndex) : idx.step = idx.step := rfl

end ProofIndexedRewriteConcrete
