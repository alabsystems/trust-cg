import Trust.Model
open BitVec

namespace Trust
namespace Bits

/-! ## Canonical zero/sign extensions (the carrier-hygiene normal forms) -/

/-- Zero-extend a width-`w` value to the full 64-bit physical register. -/
def zext (w : Nat) (x : BitVec w) : BitVec 64 := x.setWidth 64

/-- Sign-extend a width-`w` value to the full 64-bit physical register. -/
def sext (w : Nat) (x : BitVec w) : BitVec 64 := x.signExtend 64

/-- The low `w` bits read out of a 64-bit register (a `denoteLoc` `.reg`/`.int` read). -/
def lo (x : BitVec 64) (w : Nat) : BitVec w := x.truncate w

/-- The zero-extension normal form of `x`'s low `w` bits — the exact RHS that
    `WidthFaithful` requires a clean carrier to equal. -/
def canonZ (x : BitVec 64) (w : Nat) : BitVec 64 := (x.truncate w).setWidth 64

/-! ## General-width truncate / setWidth lemmas (symbolic `w`) -/

@[simp] theorem lo_zext (w : Nat) (h : w ≤ 64) (x : BitVec w) :
    (zext w x).truncate w = x := by
  unfold zext
  rw [truncate_eq_setWidth, setWidth_setWidth_of_le _ h, setWidth_eq]

theorem truncate_self (w : Nat) (x : BitVec w) : x.truncate w = x := by
  simp

theorem canonZ_idem (x : BitVec 64) (w : Nat) (h : w ≤ 64) :
    (canonZ x w).truncate w = x.truncate w := by
  unfold canonZ
  rw [truncate_eq_setWidth, truncate_eq_setWidth (v := w) (x := x),
      setWidth_setWidth_of_le _ h, setWidth_eq]

theorem canonZ_fixed (x : BitVec 64) (w : Nat) (h : w ≤ 64) :
    canonZ (canonZ x w) w = canonZ x w := by
  unfold canonZ
  rw [truncate_eq_setWidth (v := w) (x := setWidth 64 (setWidth w x)),
      setWidth_setWidth_of_le _ h, setWidth_eq]

/-! ## i128 register-pair ↔ `BitVec 128` denotation -/

def pairBits (lo hi : BitVec 64) : BitVec 128 := (hi ++ lo).cast (by omega)

def i128Lo (x : BitVec 128) : BitVec 64 := x.truncate 64

def i128Hi (x : BitVec 128) : BitVec 64 := x.extractLsb' 64 64

@[simp] theorem pairBits_lo (lo hi : BitVec 64) : i128Lo (pairBits lo hi) = lo := by
  unfold i128Lo pairBits
  bv_decide

@[simp] theorem pairBits_hi (lo hi : BitVec 64) : i128Hi (pairBits lo hi) = hi := by
  unfold i128Hi pairBits
  bv_decide

theorem pairBits_roundtrip (x : BitVec 128) :
    pairBits (i128Lo x) (i128Hi x) = x := by
  unfold pairBits i128Lo i128Hi
  bv_decide

/-! ## Fixed-width carrier facts (the `bv_decide` core) -/

theorem zext_low8  (x : BitVec 8)  : (zext 8  x).truncate 8  = x := by
  unfold zext; bv_decide

theorem zext_low16 (x : BitVec 16) : (zext 16 x).truncate 16 = x := by
  unfold zext; bv_decide

theorem zext_low32 (x : BitVec 32) : (zext 32 x).truncate 32 = x := by
  unfold zext; bv_decide

theorem canonZ_low8 (x : BitVec 64) : (canonZ x 8).truncate 8 = x.truncate 8 := by
  unfold canonZ; bv_decide

theorem canonZ_high_clear8 (x : BitVec 64) :
    (canonZ x 8) &&& (0xFFFFFFFFFFFFFF00#64) = 0#64 := by
  unfold canonZ; bv_decide

theorem sext_low8 (x : BitVec 8) : (sext 8 x).truncate 8 = x := by
  unfold sext; bv_decide

/-! ## `denoteLoc` reg/pair bridges (consumed by Cert.* and Sim.Match) -/

theorem denote_pair_i128 (m : MachState) (a b : GPR) :
    denoteLoc m (Loc.pair a b) ValKind.i128
      = Val.i128 (pairBits (m.regs a) (m.regs b)) := by
  rfl

theorem denote_reg_int (m : MachState) (r : GPR) (w : Nat) (h : w ≤ 64) :
    denoteLoc m (Loc.reg r) (ValKind.int w h)
      = Val.int w h ((m.regs r).truncate w) := by
  rfl

end Bits
end Trust
