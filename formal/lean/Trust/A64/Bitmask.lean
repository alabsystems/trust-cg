/-
  A64.Bitmask — the Arm ARM `DecodeBitMasks` function over natural numbers.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  `DecodeBitMasks(immN, imms, immr, immediate, M)` (Arm ARM, shared pseudocode J1) turns the
  `N:immr:imms` fields of a logical-immediate or bitfield instruction into the pair
  `(wmask, tmask)`.  The logical-immediate value is `wmask`; the bitfield instructions use both.
  This module transcribes the pseudocode step for step over `Nat` (bit vectors are their
  unsigned values) and proves that, for the logical-immediate encoding, it is defined exactly
  when `Trust.A64.bitmaskValid` accepts the fields — the validity the instruction-word decoder
  enforces.  No `sorry`, no `axiom`.
-/
import Trust.A64.Encoding

namespace Trust
namespace A64

/-- `HighestSetBit` of a 7-bit value, `none` for zero (Arm ARM `HighestSetBit` returns -1). -/
def highestSetBit7 (v : Nat) : Option Nat :=
  if v ≥ 64 then some 6 else if v ≥ 32 then some 5 else if v ≥ 16 then some 4
  else if v ≥ 8 then some 3 else if v ≥ 4 then some 2 else if v ≥ 2 then some 1
  else if v ≥ 1 then some 0 else none

/-- `Ones(k)`: the value whose low `k` bits are set. -/
def ones (k : Nat) : Nat := 2 ^ k - 1

/-- `ROR(x, r)` of an `e`-bit value. -/
def rorBits (e x r : Nat) : Nat :=
  let r := r % e
  (x / 2 ^ r) + (x % 2 ^ r) * 2 ^ (e - r)

/-- `Replicate(x)` of an `e`-bit element to `count` copies (low copy first). -/
def replicateBits (e x : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => x + replicateBits e x count * 2 ^ e

/-- Arm ARM `DecodeBitMasks(immN, imms, immr, immediate, M)`, `none` where the pseudocode is
    UNDEFINED (or its `M >= esize` assertion fails).  Returns `(wmask, tmask)`. -/
def decodeBitMasks (immN imms immr : Nat) (immediate : Bool) (m : Nat) : Option (Nat × Nat) :=
  match highestSetBit7 (immN * 64 + (63 - imms % 64)) with
  | none => none
  | some len =>
    if len < 1 then none else
    let levels := ones len
    if immediate && imms % 2 ^ len == levels then none else
    let esize := 2 ^ len
    if m < esize then none else
    let s := imms % 2 ^ len
    let r := immr % 2 ^ len
    let d := (s + esize - r) % esize
    let welem := ones (s + 1)
    let telem := ones (d + 1)
    some (replicateBits esize (rorBits esize welem r) (m / esize),
          replicateBits esize telem (m / esize))

/-- The value of a logical immediate `N:immr:imms` at register width `m` (`wmask`). -/
def logicalImmValue (immN immr imms m : Nat) : Option Nat :=
  (decodeBitMasks immN imms immr true m).map Prod.fst

/-- The logical-immediate fields the decoder accepts are exactly the ones `DecodeBitMasks`
    defines at 64 bits (checked by kernel evaluation over every `N`, `imms` and `immr`). -/
theorem bitmaskValid_iff_decodeBitMasks :
    ∀ n, n < 2 → ∀ imms, imms < 64 → ∀ immr, immr < 64 →
      bitmaskValid n imms = (decodeBitMasks n imms immr true 64).isSome := by
  decide +kernel

end A64
end Trust
