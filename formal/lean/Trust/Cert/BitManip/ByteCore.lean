/-
  Kernel-checked SWAR population-count value proofs.
  Copyright 2026 Andrew Yates. Apache 2.0.
-/
import Init.Data.BitVec
import Init.Omega

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-! The first three SWAR stages count each byte independently. The proof
tracks the absent borrow/carry at byte boundaries and then inducts on a byte
representation that covers every bitvector. Only the finite eight-bit facts
use `decide`; there is no solver or native-evaluation proof. -/
namespace Trust.Cert.BitManip.Internal

theorem shiftedMask_append {n : Nat} (a ma : BitVec n) (b mb : BitVec 8) (s : Nat)
    (low : ∀ i : Fin 8, 8 ≤ s + i.val → mb.getLsbD i.val = false) :
    (((a ++ b) >>> s) &&& (ma ++ mb)) =
      (((a >>> s) &&& ma) ++ ((b >>> s) &&& mb)) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  by_cases h : i < 8
  · simp only [if_pos h]
    by_cases cross : s + i < 8
    · simp [cross]
    · have hz : mb.getLsbD i = false := low ⟨i,h⟩ (by change 8 ≤ s + i; omega)
      simp [cross, hz]
  · have hc : ¬ s + i < 8 := by omega
    simp only [if_neg h, if_neg hc]
    rw [show s + i - 8 = s + (i - 8) by omega]

 theorem mod_packed_byte (A C K : Nat) (hK : 0 < K) (hC : C < 256) :
    (256 * A + C) % (256 * K) = 256 * (A % K) + C := by
  have shape : 256 * A + C = (256 * (A % K) + C) + (256 * K) * (A/K) := by
    calc
      256 * A + C = 256 * (A % K + K * (A/K)) + C := by rw [Nat.mod_add_div]
      _ = (256 * (A % K) + C) + (256 * K) * (A/K) := by
        simp only [Nat.mul_add, Nat.mul_assoc]
        ac_rfl
  rw [shape, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt A hK
  clear shape
  omega

theorem append_toNat_byte {n : Nat} (a : BitVec n) (b : BitVec 8) :
    (a ++ b).toNat = 256 * a.toNat + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  change a.toNat * 256 + b.toNat=256 * a.toNat + b.toNat
  rw [Nat.mul_comm a.toNat]



theorem append_add_noCarry {n : Nat} (a b : BitVec n) (c d : BitVec 8)
    (low : c.toNat + d.toNat < 256) :
    (a ++ c) + (b ++ d) = (a + b) ++ (c + d) := by
  have width : 2 ^ (n + 8) = 256 * 2 ^ n := by rw [Nat.pow_add, Nat.mul_comm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, append_toNat_byte, width]
  have shape : (256 * a.toNat + c.toNat) + (256 * b.toNat + d.toNat) =
      256 * (a.toNat + b.toNat) + (c.toNat + d.toNat) := by omega
  rw [shape, mod_packed_byte _ _ _ (Nat.two_pow_pos n) low, Nat.mod_eq_of_lt low]

theorem append_sub_noBorrow {n : Nat} (a b : BitVec n) (c d : BitVec 8)
    (low : d.toNat ≤ c.toNat) :
    (a ++ c) - (b ++ d) = (a - b) ++ (c - d) := by
  have width : 2 ^ (n + 8) = 256 * 2 ^ n := by rw [Nat.pow_add, Nat.mul_comm]
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have small : c.toNat - d.toNat < 256 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, append_toNat_byte, width]
  have shape : (256 * 2 ^ n - (256 * b.toNat + d.toNat)) + (256 * a.toNat + c.toNat) =
      256 * (2 ^ n - b.toNat + a.toNat) + (c.toNat - d.toNat) := by omega
  have lo : (256 - d.toNat + c.toNat) % 256 = c.toNat - d.toNat := by omega
  rw [shape, mod_packed_byte _ _ _ (Nat.two_pow_pos n) small, lo]



theorem shift4_append {n : Nat} (a : BitVec n) (b : BitVec 8) :
    (a ++ b) >>> 4 = (a >>> 4) ++
      (BitVec.ofNat 8 (16 * (a.toNat % 16) + b.toNat/16)) := by
  have hb := b.isLt
  have hm := Nat.mod_lt a.toNat (show 0 < 16 by decide)
  have small : 16 * (a.toNat % 16) + b.toNat/16 < 256 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, append_toNat_byte, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  change (256 * a.toNat + b.toNat)/16 =
    256 * (a.toNat/16) + (16 * (a.toNat % 16) + b.toNat/16) % 256
  rw [Nat.mod_eq_of_lt small]
  have shape : 256 * a.toNat + b.toNat = b.toNat + 16 * (16 * a.toNat) := by omega
  rw [shape, Nat.add_mul_div_left _ _ (by decide)]
  have := Nat.mod_add_div a.toNat 16
  clear shape
  omega

theorem byteFold_append {n : Nat} (a ma : BitVec n) (b : BitVec 8)
    (highLow : a.toNat % 16 ≤ 4) (low : b.toNat ≤ 68) :
    (((a ++ b) + ((a ++ b) >>> 4)) &&& (ma ++ (15 : BitVec 8))) =
    (((a + (a >>> 4)) &&& ma) ++ ((b + (b >>> 4)) &&& (15 : BitVec 8))) := by
  let L := 16 * (a.toNat % 16) + b.toNat/16
  let l := BitVec.ofNat 8 L
  have hL : L < 256 := by dsimp only [L]; omega
  have hl : l.toNat = L := Nat.mod_eq_of_lt hL
  have sumLow : b.toNat + l.toNat < 256 := by rw [hl]; dsimp only [L]; omega
  have small : b.toNat + b.toNat/16 < 256 := by omega
  have byteEq : ((b + l) &&& (15 : BitVec 8)) = ((b + (b >>> 4)) &&& (15 : BitVec 8)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, hl]
    change ((b.toNat + L) % 256 &&& (2 ^ 4 - 1)) =
      ((b.toNat + b.toNat/16) % 256 &&& (2 ^ 4 - 1))
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    rw [Nat.mod_eq_of_lt (show b.toNat + L < 256 by simpa only [hl] using sumLow), Nat.mod_eq_of_lt small]
    have shape : b.toNat + L = (b.toNat + b.toNat/16) + 16 * (a.toNat % 16) := by dsimp only [L]; omega
    rw [shape, Nat.add_mul_mod_self_left]
  rw [shift4_append]
  change (((a ++ b) + ((a >>> 4) ++ l)) &&& (ma ++ (15 : BitVec 8))) = _
  rw [append_add_noCarry _ _ _ _ sumLow, BitVec.and_append, byteEq]



def pairCore {n : Nat} (x m1 : BitVec n) : BitVec n := x - ((x >>> 1) &&& m1)
def nibbleCore {n : Nat} (x m1 m2 : BitVec n) : BitVec n :=
  let a := pairCore x m1
  (a &&& m2) + ((a >>> 2) &&& m2)
def byteCore {n : Nat} (x m1 m2 m4 : BitVec n) : BitVec n :=
  let a := nibbleCore x m1 m2
  (a + (a >>> 4)) &&& m4

theorem byteFacts : ∀ x : BitVec 8,
    (((x >>> 1) &&& (85 : BitVec 8)).toNat ≤ x.toNat) ∧
    ((pairCore x 85 &&& (51 : BitVec 8)).toNat +
      (((pairCore x 85 >>> 2) &&& (51 : BitVec 8)).toNat) < 256) ∧
    (nibbleCore x 85 51).toNat ≤ 68 ∧
    (nibbleCore x 85 51).toNat % 16 ≤ 4 := by decide

theorem byteCount_correct : ∀ x : BitVec 8, byteCore x 85 51 15 = x.cpop := by decide

private theorem mask55 : ∀ i : Fin 8, 8 ≤ 1 + i.val → (85 : BitVec 8).getLsbD i.val = false := by decide
private theorem mask33 : ∀ i : Fin 8, 8 ≤ 2 + i.val → (51 : BitVec 8).getLsbD i.val = false := by decide

theorem pairCore_append {n : Nat} (a m1 : BitVec n) (b : BitVec 8) :
    pairCore (a ++ b) (m1 ++ (85 : BitVec 8)) = pairCore a m1 ++ pairCore b 85 := by
  simp only [pairCore]
  rw [shiftedMask_append a m1 b 85 1 mask55]
  exact append_sub_noBorrow _ _ _ _ (byteFacts b).1

theorem nibbleCore_append {n : Nat} (a m1 m2 : BitVec n) (b : BitVec 8) :
    nibbleCore (a ++ b) (m1 ++ (85 : BitVec 8)) (m2 ++ (51 : BitVec 8)) =
      nibbleCore a m1 m2 ++ nibbleCore b 85 51 := by
  simp only [nibbleCore, pairCore_append, BitVec.and_append,
    shiftedMask_append (pairCore a m1) m2 (pairCore b 85) 51 2 mask33]
  exact append_add_noCarry _ _ _ _ (byteFacts b).2.1

theorem nibbleCore_lowBound {n : Nat} (a m1 m2 : BitVec n) (b : BitVec 8) :
    (nibbleCore (a ++ b) (m1 ++ (85 : BitVec 8)) (m2 ++ (51 : BitVec 8))).toNat % 16 ≤ 4 := by
  rw [nibbleCore_append, append_toNat_byte]
  simpa [Nat.add_mod, Nat.mul_mod] using (byteFacts b).2.2.2

theorem byteCore_append {n : Nat} (a m1 m2 m4 : BitVec n) (b : BitVec 8)
    (low : (nibbleCore a m1 m2).toNat % 16 ≤ 4) :
    byteCore (a ++ b) (m1 ++ (85 : BitVec 8)) (m2 ++ (51 : BitVec 8)) (m4 ++ (15 : BitVec 8)) =
      byteCore a m1 m2 m4 ++ byteCore b 85 51 15 := by
  simp only [byteCore, nibbleCore_append]
  exact byteFold_append _ _ _ low (byteFacts b).2.2.1

abbrev byteWidth (n : Nat) : Nat := 8 * n
inductive ByteWord : Nat → Type where
  | nil : ByteWord 0
  | snoc {n : Nat} : ByteWord n → BitVec 8 → ByteWord (n + 1)
def wordValue {n : Nat} : ByteWord n → BitVec (byteWidth n)
  | .nil => 0
  | .snoc w b => wordValue w ++ b
def countBytes {n : Nat} : ByteWord n → ByteWord n
  | .nil => .nil
  | .snoc w b => .snoc (countBytes w) b.cpop
def repeatByte : (n : Nat) → BitVec 8 → BitVec (byteWidth n)
  | 0, _ => 0
  | n + 1, b => repeatByte n b ++ b

theorem wordNibble_lowBound {n : Nat} (w : ByteWord n) :
    (nibbleCore (wordValue w) (repeatByte n 85) (repeatByte n 51)).toNat % 16 ≤ 4 := by
  cases w with
  | nil => decide
  | @snoc n w b => exact nibbleCore_lowBound _ _ _ _

theorem wordCore_correct {n : Nat} (w : ByteWord n) :
    byteCore (wordValue w) (repeatByte n 85) (repeatByte n 51) (repeatByte n 15) =
      wordValue (countBytes w) := by
  induction w with
  | nil => decide
  | @snoc n w b ih =>
    change byteCore (wordValue w ++ b) (repeatByte n 85 ++ 85)
      (repeatByte n 51 ++ 51) (repeatByte n 15 ++ 15) = wordValue (countBytes w) ++ b.cpop
    rw [byteCore_append _ _ _ _ _ (wordNibble_lowBound w), ih, byteCount_correct]

def ofBitVec : (n : Nat) → BitVec (byteWidth n) → ByteWord n
  | 0, _ => .nil
  | n + 1, x => .snoc (ofBitVec n (x.extractLsb' 8 (byteWidth n))) (x.extractLsb' 0 8)

theorem wordValue_ofBitVec (n : Nat) (x : BitVec (byteWidth n)) : wordValue (ofBitVec n x) = x := by
  induction n with
  | zero => exact (BitVec.of_length_zero (x := x)).symm
  | succ n ih =>
    change wordValue (ofBitVec n (x.extractLsb' 8 (byteWidth n))) ++ x.extractLsb' 0 8 = x
    rw [ih]
    exact BitVec.extractLsb'_append_extractLsb'



end Trust.Cert.BitManip.Internal
