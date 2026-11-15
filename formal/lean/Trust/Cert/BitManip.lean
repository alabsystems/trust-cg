/-
  SWAR population-count VALUE equations for every 32- and 64-bit input.
  Copyright 2026 Andrew Yates. Apache 2.0.

  These definitions use the shipping shift/mask/add/subtract sequence. The
  proof factors byte counting from the wide folds; it introduces no native
  evaluation axiom, project axiom or sorry. This is a value proof, not an
  InstrCert: emitted-byte execution, clobbers, carrier/frame preservation and
  connection to a source transition are separate obligations. The runtime
  portable DRAT authority and its acceptance policy do not consume these lemmas.
-/
import Trust.Cert.BitManip.ByteCore
import Trust.Cert.BitManip.Folds

set_option maxRecDepth 4096
set_option maxHeartbeats 0

namespace Trust.Cert.BitManip
open Internal

/-- The emitted 32-bit shift/mask SWAR value expression. -/
def popcnt32Swar (x : BitVec 32) : BitVec 32 :=
  fold32 (byteCore x 0x55555555 0x33333333 0x0f0f0f0f)

/-- The emitted 64-bit shift/mask SWAR value expression. -/
def popcnt64Swar (x : BitVec 64) : BitVec 64 :=
  fold64 (byteCore x 0x5555555555555555 0x3333333333333333 0x0f0f0f0f0f0f0f0f)

private theorem countsPack32 (a b c d : BitVec 8) :
    wordValue (countBytes (ByteWord.snoc (ByteWord.snoc (ByteWord.snoc (ByteWord.snoc ByteWord.nil a) b) c) d)) = pack32 a.cpop.toNat b.cpop.toNat c.cpop.toNat d.cpop.toNat := by
  have ha := BitVec.toNat_cpop_le a
  have hb := BitVec.toNat_cpop_le b
  have hc := BitVec.toNat_cpop_le c
  have hd := BitVec.toNat_cpop_le d
  have bound : 16777216 * a.cpop.toNat + 65536 * b.cpop.toNat + 256 * c.cpop.toNat + d.cpop.toNat < 4294967296 := by omega
  apply BitVec.eq_of_toNat_eq
  have zero : (0 : BitVec 0).toNat = 0 := rfl
  simp only [wordValue, countBytes, append_toNat_byte, zero, Nat.mul_zero, Nat.zero_add, pack32, BitVec.toNat_ofNat]
  change 256 * (256 * (256 * a.cpop.toNat + b.cpop.toNat) + c.cpop.toNat) + d.cpop.toNat =
    (16777216 * a.cpop.toNat + 65536 * b.cpop.toNat + 256 * c.cpop.toNat + d.cpop.toNat) % 4294967296
  rw [Nat.mod_eq_of_lt bound]
  omega

private theorem popcnt32Swar_bytes (w : ByteWord 4) : popcnt32Swar (wordValue w) = (wordValue w).cpop := by
  have core : byteCore (wordValue w) (0x55555555 : BitVec 32) 0x33333333 0x0f0f0f0f = wordValue (countBytes w) := by
    change byteCore (wordValue w) (repeatByte 4 85) (repeatByte 4 51) (repeatByte 4 15) = _
    exact wordCore_correct w
  dsimp only [popcnt32Swar]
  rw [core]
  cases w with
  | snoc w d =>
    cases w with
    | snoc w c =>
      cases w with
      | snoc w b =>
        cases w with
        | snoc w a =>
          cases w
          rw [countsPack32, fold32_correct _ _ _ _ (BitVec.toNat_cpop_le a) (BitVec.toNat_cpop_le b) (BitVec.toNat_cpop_le c) (BitVec.toNat_cpop_le d)]
          apply BitVec.eq_of_toNat_eq
          have zero : ((0 : BitVec 0).cpop).toNat = 0 := rfl
          simp only [BitVec.toNat_ofNat, wordValue, BitVec.toNat_cpop_append, zero, Nat.zero_add]
          change (a.cpop.toNat + b.cpop.toNat + c.cpop.toNat + d.cpop.toNat) % 4294967296 = a.cpop.toNat + b.cpop.toNat + c.cpop.toNat + d.cpop.toNat
          exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (BitVec.toNat_cpop_le a) (BitVec.toNat_cpop_le b)) (BitVec.toNat_cpop_le c)) (BitVec.toNat_cpop_le d)) (by decide))

/-- Every 32-bit input has the same value as the reference bit count. -/
theorem popcnt32_swar_correct (x : BitVec 32) : popcnt32Swar x = x.cpop := by
  simpa only [wordValue_ofBitVec] using popcnt32Swar_bytes (ofBitVec 4 x)


private theorem countsPack64 (a b c d e f g h : BitVec 8) :
    wordValue (countBytes (ByteWord.snoc (ByteWord.snoc (ByteWord.snoc (ByteWord.snoc (ByteWord.snoc (ByteWord.snoc (ByteWord.snoc (ByteWord.snoc ByteWord.nil a) b) c) d) e) f) g) h)) = pack64 a.cpop.toNat b.cpop.toNat c.cpop.toNat d.cpop.toNat e.cpop.toNat f.cpop.toNat g.cpop.toNat h.cpop.toNat := by
  have ha := BitVec.toNat_cpop_le a
  have hb := BitVec.toNat_cpop_le b
  have hc := BitVec.toNat_cpop_le c
  have hd := BitVec.toNat_cpop_le d
  have he := BitVec.toNat_cpop_le e
  have hf := BitVec.toNat_cpop_le f
  have hg := BitVec.toNat_cpop_le g
  have hh := BitVec.toNat_cpop_le h
  have bound : 72057594037927936 * a.cpop.toNat + 281474976710656 * b.cpop.toNat + 1099511627776 * c.cpop.toNat + 4294967296 * d.cpop.toNat + 16777216 * e.cpop.toNat + 65536 * f.cpop.toNat + 256 * g.cpop.toNat + h.cpop.toNat < 18446744073709551616 := by omega
  apply BitVec.eq_of_toNat_eq
  have zero : (0 : BitVec 0).toNat = 0 := rfl
  simp only [wordValue, countBytes, append_toNat_byte, zero, Nat.mul_zero, Nat.zero_add, pack64, BitVec.toNat_ofNat]
  change (256 * (256 * (256 * (256 * (256 * (256 * (256 * a.cpop.toNat + b.cpop.toNat) + c.cpop.toNat) + d.cpop.toNat) + e.cpop.toNat) + f.cpop.toNat) + g.cpop.toNat) + h.cpop.toNat) = (72057594037927936 * a.cpop.toNat + 281474976710656 * b.cpop.toNat + 1099511627776 * c.cpop.toNat + 4294967296 * d.cpop.toNat + 16777216 * e.cpop.toNat + 65536 * f.cpop.toNat + 256 * g.cpop.toNat + h.cpop.toNat) % 18446744073709551616
  rw [Nat.mod_eq_of_lt bound]
  omega

private theorem popcnt64Swar_bytes (w : ByteWord 8) : popcnt64Swar (wordValue w) = (wordValue w).cpop := by
  have core : byteCore (wordValue w) (0x5555555555555555 : BitVec 64) 0x3333333333333333 0x0f0f0f0f0f0f0f0f = wordValue (countBytes w) := by
    change byteCore (wordValue w) (repeatByte 8 85) (repeatByte 8 51) (repeatByte 8 15) = _
    exact wordCore_correct w
  dsimp only [popcnt64Swar]
  rw [core]
  cases w with
  | snoc w h =>
    cases w with
    | snoc w g =>
      cases w with
      | snoc w f =>
        cases w with
        | snoc w e =>
          cases w with
          | snoc w d =>
            cases w with
            | snoc w c =>
              cases w with
              | snoc w b =>
                cases w with
                | snoc w a =>
                  cases w
                  rw [countsPack64, fold64_correct _ _ _ _ _ _ _ _ (BitVec.toNat_cpop_le a) (BitVec.toNat_cpop_le b) (BitVec.toNat_cpop_le c) (BitVec.toNat_cpop_le d) (BitVec.toNat_cpop_le e) (BitVec.toNat_cpop_le f) (BitVec.toNat_cpop_le g) (BitVec.toNat_cpop_le h)]
                  apply BitVec.eq_of_toNat_eq
                  have zero : ((0 : BitVec 0).cpop).toNat = 0 := rfl
                  simp only [BitVec.toNat_ofNat, wordValue, BitVec.toNat_cpop_append, zero, Nat.zero_add]
                  change (a.cpop.toNat + b.cpop.toNat + c.cpop.toNat + d.cpop.toNat + e.cpop.toNat + f.cpop.toNat + g.cpop.toNat + h.cpop.toNat) % 18446744073709551616 = a.cpop.toNat + b.cpop.toNat + c.cpop.toNat + d.cpop.toNat + e.cpop.toNat + f.cpop.toNat + g.cpop.toNat + h.cpop.toNat
                  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (BitVec.toNat_cpop_le a) (BitVec.toNat_cpop_le b)) (BitVec.toNat_cpop_le c)) (BitVec.toNat_cpop_le d)) (BitVec.toNat_cpop_le e)) (BitVec.toNat_cpop_le f)) (BitVec.toNat_cpop_le g)) (BitVec.toNat_cpop_le h)) (by decide))

/-- Every 64-bit input has the same value as the reference bit count. -/
theorem popcnt64_swar_correct (x : BitVec 64) : popcnt64Swar x = x.cpop := by
  simpa only [wordValue_ofBitVec] using popcnt64Swar_bytes (ofBitVec 8 x)

end Trust.Cert.BitManip
