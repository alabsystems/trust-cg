/-
  Kernel-checked SWAR population-count value proofs.
  Copyright 2026 Andrew Yates. Apache 2.0.
-/
import Init.Data.BitVec
import Init.Omega

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-! The emitted 32/64-bit fold chains sum valid byte counts. Explicit
quotient and overflow bounds keep each arithmetic proof small. Unneeded
previous constraints are cleared before invoking `omega`. -/
namespace Trust.Cert.BitManip.Internal

def pack32 (a b c d : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (16777216 * a + 65536 * b + 256 * c + d)
def fold32 (x : BitVec 32) : BitVec 32 :=
  let y := x + (x >>> 8)
  let z := y + (y >>> 16)
  z &&& 0x3f

theorem fold32_correct (a b c d : Nat)
    (ha : a ≤ 8) (hb : b ≤ 8) (hc : c ≤ 8) (hd : d ≤ 8) :
    fold32 (pack32 a b c d) = BitVec.ofNat 32 (a + b + c + d) := by
  let X := 16777216 * a + 65536 * b + 256 * c + d
  let Y := 16777216 * a + 65536 * (a + b) + 256 * (b + c) + (c + d)
  let Z := 16777216 * a + 65536 * (a + b) + 256 * (a + b + c) + (a + b + c + d)
  have hX : X < 4294967296 := by dsimp only [X]; omega
  have hY : Y < 4294967296 := by dsimp only [Y]; omega
  have hZ : Z < 4294967296 := by dsimp only [Z]; omega
  have hDX : X / 256 = 65536 * a + 256 * b + c := by
    have shape : X = d + 256 * (65536 * a + 256 * b + c) := by dsimp only [X]; omega
    rw [shape, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (show d < 256 by omega), Nat.zero_add]
  have hDY : Y / 65536 = 256 * a + (a + b) := by
    have shape : Y = (256 * (b + c) + (c + d)) + 65536 * (256 * a + (a + b)) := by dsimp only [Y]; omega
    rw [shape, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (show 256 * (b + c) + (c + d) < 65536 by omega), Nat.zero_add]
  let x := pack32 a b c d
  let y := x + (x >>> 8)
  let z := y + (y >>> 16)
  have hx : x.toNat = X := by
    change X % 4294967296 = X
    exact Nat.mod_eq_of_lt hX
  have hy : y.toNat = Y := by
    dsimp only [y]
    rw [BitVec.toNat_add, hx, BitVec.toNat_ushiftRight, hx, Nat.shiftRight_eq_div_pow]
    change (X + X / 256) % 4294967296 = Y
    rw [hDX]
    have shape : X + (65536 * a + 256 * b + c) = Y := by dsimp only [X,Y]; omega
    rw [shape, Nat.mod_eq_of_lt hY]
  have hz : z.toNat = Z := by
    dsimp only [z]
    rw [BitVec.toNat_add, hy, BitVec.toNat_ushiftRight, hy, Nat.shiftRight_eq_div_pow]
    change (Y + Y / 65536) % 4294967296 = Z
    rw [hDY]
    have shape : Y + (256 * a + (a + b)) = Z := by dsimp only [Y,Z]; omega
    rw [shape, Nat.mod_eq_of_lt hZ]
  have final : Z % 64 = a + b + c + d := by
    have shape : Z = (a + b + c + d) + 64 * (262144 * a + 1024 * (a + b) + 4 * (a + b + c)) := by dsimp only [Z]; omega
    rw [shape, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  change (z &&& (63 : BitVec 32)).toNat = (BitVec.ofNat 32 (a + b + c + d)).toNat
  rw [BitVec.toNat_and, hz, BitVec.toNat_ofNat]
  change (Z &&& (2 ^ 6 - 1)) = (a + b + c + d) % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  change Z % 64 = (a + b + c + d) % 4294967296
  rw [final, Nat.mod_eq_of_lt (show a + b + c + d < 4294967296 by omega)]

def pack64 (a b c d e f g h : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (72057594037927936 * a + 281474976710656 * b + 1099511627776 * c + 4294967296 * d + 16777216 * e + 65536 * f + 256 * g + h)
def fold64 (x : BitVec 64) : BitVec 64 :=
  let y := x + (x >>> 8)
  let z := y + (y >>> 16)
  let t := z + (z >>> 32)
  t &&& 0x7f

theorem fold64_correct (a b c d e f g h : Nat)
    (ha : a ≤ 8) (hb : b ≤ 8) (hc : c ≤ 8) (hd : d ≤ 8) (he : e ≤ 8) (hf : f ≤ 8) (hg : g ≤ 8) (hh : h ≤ 8) :
    fold64 (pack64 a b c d e f g h) = BitVec.ofNat 64 (a + b + c + d + e + f + g + h) := by
  have hSum : a + b + c + d + e + f + g + h ≤ 64 := by omega
  let X := 72057594037927936 * a + 281474976710656 * b + 1099511627776 * c + 4294967296 * d + 16777216 * e + 65536 * f + 256 * g + h
  let Y := 72057594037927936 * a + 281474976710656 * (a + b) + 1099511627776 * (b + c) + 4294967296 * (c + d) + 16777216 * (d + e) + 65536 * (e + f) + 256 * (f + g) + (g + h)
  let Z := 72057594037927936 * a + 281474976710656 * (a + b) + 1099511627776 * (a + b + c) + 4294967296 * (a + b + c + d) + 16777216 * (b + c + d + e) + 65536 * (c + d + e + f) + 256 * (d + e + f + g) + (e + f + g + h)
  let T := 72057594037927936 * a + 281474976710656 * (a + b) + 1099511627776 * (a + b + c) + 4294967296 * (a + b + c + d) + 16777216 * (a + b + c + d + e) + 65536 * (a + b + c + d + e + f) + 256 * (a + b + c + d + e + f + g) + (a + b + c + d + e + f + g + h)
  have hX : X < 18446744073709551616 := by dsimp only [X]; omega
  have hY : Y < 18446744073709551616 := by clear hX; dsimp only [Y]; omega
  have hZ : Z < 18446744073709551616 := by clear hX hY; dsimp only [Z]; omega
  have hT : T < 18446744073709551616 := by clear hX hY hZ; dsimp only [T]; omega
  have hDX : X / 256 = 281474976710656 * a + 1099511627776 * b + 4294967296 * c + 16777216 * d + 65536 * e + 256 * f + g := by
    clear hX hY hZ hT
    have shape : X = (h) + 256 * (281474976710656 * a + 1099511627776 * b + 4294967296 * c + 16777216 * d + 65536 * e + 256 * f + g) := by dsimp only [X]; omega
    rw [shape, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (show h < 256 by omega), Nat.zero_add]
  have hDY : Y / 65536 = 1099511627776 * a + 4294967296 * (a + b) + 16777216 * (b + c) + 65536 * (c + d) + 256 * (d + e) + (e + f) := by
    clear hX hY hZ hT hDX
    have shape : Y = (256 * (f + g) + (g + h)) + 65536 * (1099511627776 * a + 4294967296 * (a + b) + 16777216 * (b + c) + 65536 * (c + d) + 256 * (d + e) + (e + f)) := by dsimp only [Y]; omega
    rw [shape, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (show 256 * (f + g) + (g + h) < 65536 by omega), Nat.zero_add]
  have hDZ : Z / 4294967296 = 16777216 * a + 65536 * (a + b) + 256 * (a + b + c) + (a + b + c + d) := by
    clear hX hY hZ hT hDX hDY
    have shape : Z = (16777216 * (b + c + d + e) + 65536 * (c + d + e + f) + 256 * (d + e + f + g) + (e + f + g + h)) + 4294967296 * (16777216 * a + 65536 * (a + b) + 256 * (a + b + c) + (a + b + c + d)) := by dsimp only [Z]; omega
    rw [shape, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (show 16777216 * (b + c + d + e) + 65536 * (c + d + e + f) + 256 * (d + e + f + g) + (e + f + g + h) < 4294967296 by omega), Nat.zero_add]
  let x := pack64 a b c d e f g h
  let y := x + (x >>> 8)
  let z := y + (y >>> 16)
  let t := z + (z >>> 32)
  have hx : x.toNat = X := by
    change X % 18446744073709551616 = X
    exact Nat.mod_eq_of_lt hX
  have hy : y.toNat = Y := by
    dsimp only [y]
    rw [BitVec.toNat_add, hx, BitVec.toNat_ushiftRight, hx, Nat.shiftRight_eq_div_pow]
    change (X + X / 256) % 18446744073709551616 = Y
    rw [hDX]
    have shape : X + (281474976710656 * a + 1099511627776 * b + 4294967296 * c + 16777216 * d + 65536 * e + 256 * f + g) = Y := by clear hX hY hZ hT hDX hDY hDZ hx; dsimp only [X,Y]; omega
    rw [shape, Nat.mod_eq_of_lt hY]
  have hz : z.toNat = Z := by
    dsimp only [z]
    rw [BitVec.toNat_add, hy, BitVec.toNat_ushiftRight, hy, Nat.shiftRight_eq_div_pow]
    change (Y + Y / 65536) % 18446744073709551616 = Z
    rw [hDY]
    have shape : Y + (1099511627776 * a + 4294967296 * (a + b) + 16777216 * (b + c) + 65536 * (c + d) + 256 * (d + e) + (e + f)) = Z := by clear hX hY hZ hT hDX hDY hDZ hx hy; dsimp only [Y,Z]; omega
    rw [shape, Nat.mod_eq_of_lt hZ]
  have ht : t.toNat = T := by
    dsimp only [t]
    rw [BitVec.toNat_add, hz, BitVec.toNat_ushiftRight, hz, Nat.shiftRight_eq_div_pow]
    change (Z + Z / 4294967296) % 18446744073709551616 = T
    rw [hDZ]
    have shape : Z + (16777216 * a + 65536 * (a + b) + 256 * (a + b + c) + (a + b + c + d)) = T := by clear hX hY hZ hT hDX hDY hDZ hx hy hz; dsimp only [Z,T]; omega
    rw [shape, Nat.mod_eq_of_lt hT]
  have final : T % 128 = a + b + c + d + e + f + g + h := by
    have shape : T = (a + b + c + d + e + f + g + h) + 128 * (562949953421312 * a + 2199023255552 * (a + b) + 8589934592 * (a + b + c) + 33554432 * (a + b + c + d) + 131072 * (a + b + c + d + e) + 512 * (a + b + c + d + e + f) + 2 * (a + b + c + d + e + f + g)) := by clear hX hY hZ hT hDX hDY hDZ hx hy hz ht; dsimp only [T]; omega
    rw [shape, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hSum (by decide))
  apply BitVec.eq_of_toNat_eq
  change (t &&& (127 : BitVec 64)).toNat = (BitVec.ofNat 64 (a + b + c + d + e + f + g + h)).toNat
  rw [BitVec.toNat_and, ht, BitVec.toNat_ofNat]
  change (T &&& (2 ^ 7 - 1)) = (a + b + c + d + e + f + g + h) % 18446744073709551616
  rw [Nat.and_two_pow_sub_one_eq_mod]
  change T % 128 = (a + b + c + d + e + f + g + h) % 18446744073709551616
  rw [final, Nat.mod_eq_of_lt (show a + b + c + d + e + f + g + h < 18446744073709551616 from Nat.lt_of_le_of_lt hSum (by decide))]


end Trust.Cert.BitManip.Internal
