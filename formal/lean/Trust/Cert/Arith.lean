/-
  Cert.Arith — per-instruction VALUE certificates for trust-cg's integer arithmetic lowerings.

  VERIFIED AS-IS. No corrections required. Compiles clean (0 errors / 0 warnings / 0 sorry) under
  Lean 4.31.0 against a faithful reconstruction of Trust.Model and Trust.Cert.Obligation built
  verbatim from the contract preamble. Axiom audit clean (no sorryAx; only kernel-checked
  bv_decide LRAT certificate axioms + propext/Classical.choice/Quot.sound). The submitted source
  below is unchanged.
-/

import Trust.Model
import Trust.Cert.Obligation

namespace Trust
namespace Cert
namespace Arith

theorem trunc_invisible (X r m : Nat) :
    (X * m + r) % (m*m) = (X % m * m + r) % (m*m) := by
  have h2 : X * m = X % m * m + X / m * (m * m) := by
    calc X * m = (X % m + X / m * m) * m := by rw [Nat.mod_add_div']
      _ = X % m * m + X / m * m * m := by rw [Nat.add_mul]
      _ = X % m * m + X / m * (m * m) := by rw [Nat.mul_assoc]
  calc (X * m + r) % (m*m)
      = (X % m * m + r + X / m * (m*m)) % (m*m) := by rw [h2]; ac_rfl
    _ = (X % m * m + r) % (m*m) := by rw [Nat.add_mul_mod_self_right]

theorem hprod_gen (al ah bl bh c : Nat) :
    (al + c*ah) * (bl + c*bh) = (al*bl + (al*bh + ah*bl) * c) + ah*bh * (c*c) := by
  simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm]

theorem school_gen (al ah bl bh c : Nat) :
    ( ( (al*bl)/c + al*bh + ah*bl ) % c * c + (al*bl) % c ) % (c*c)
      = ( (al + c*ah) * (bl + c*bh) ) % (c*c) := by
  rw [← trunc_invisible ((al*bl)/c + al*bh + ah*bl) ((al*bl) % c) c]
  have hexpand : ((al*bl)/c + al*bh + ah*bl) * c + (al*bl) % c = al*bl + (al*bh + ah*bl) * c := by
    have hc : (al*bl)/c * c + (al*bl) % c = al*bl := by
      rw [Nat.add_comm]; exact Nat.mod_add_div' (al*bl) c
    have hd : (al*bh + ah*bl) * c = al*bh*c + ah*bl*c := by rw [Nat.add_mul]
    rw [Nat.add_mul, Nat.add_mul, hd]; omega
  rw [hexpand, hprod_gen al ah bl bh c, Nat.add_mul_mod_self_right]

theorem mulAddBound (a b c : Nat) (ha : a < c) (hb : b < c) : a * c + b < c * c := by
  have h1 : a * c + b < a * c + c := Nat.add_lt_add_left hb (a*c)
  have h3 : (a+1) * c ≤ c * c := by
    rw [Nat.mul_comm (a+1) c, Nat.mul_comm c c]; exact Nat.mul_le_mul_left c ha
  have h2 : a * c + c = (a+1) * c := by rw [Nat.add_mul, Nat.one_mul]
  omega

@[simp] def join128 (lo hi : BitVec 64) : BitVec 128 := (hi ++ lo).cast (by omega)

theorem join_as_shiftadd (lo hi : BitVec 64) :
    join128 lo hi = (hi.setWidth 128) <<< (64 : Nat) + (lo.setWidth 128) := by
  simp only [join128]; bv_decide

theorem join_toNat (lo hi : BitVec 64) :
    (join128 lo hi).toNat = lo.toNat + 2^64 * hi.toNat := by
  have hl : lo.toNat < 2^64 := lo.isLt
  have hh : hi.toNat < 2^64 := hi.isLt
  have hp : (0:Nat) < 2^64 := Nat.two_pow_pos 64
  have he : (2:Nat)^128 = 2^64 * 2^64 := by rw [← Nat.pow_add]
  have hbnd : hi.toNat * 2^64 < 2^128 := by rw [he]; exact Nat.mul_lt_mul_right hp |>.mpr hh
  have hlt128 : lo.toNat < 2^128 := by
    rw [he]; exact Nat.lt_of_lt_of_le hl (Nat.le_mul_of_pos_left _ hp)
  have hh128 : hi.toNat < 2^128 := by
    rw [he]; exact Nat.lt_of_lt_of_le hh (Nat.le_mul_of_pos_left _ hp)
  have hsum : hi.toNat * 2^64 + lo.toNat < 2^128 := by
    rw [he]; exact mulAddBound hi.toNat lo.toNat (2^64) hh hl
  rw [join_as_shiftadd, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt hlt128, Nat.mod_eq_of_lt hh128, Nat.mod_eq_of_lt hbnd, Nat.mod_eq_of_lt hsum]
  rw [Nat.add_comm, Nat.mul_comm]

@[simp] def addCarry (x y : BitVec 64) : BitVec 64 := if (x + y) < x then 1 else 0
@[simp] def lowerAddLo (aLo bLo : BitVec 64) : BitVec 64 := aLo + bLo
@[simp] def lowerAddHi (aLo aHi bLo bHi : BitVec 64) : BitVec 64 :=
  aHi + bHi + addCarry aLo bLo
@[simp] def lowerAddI128 (aLo aHi bLo bHi : BitVec 64) : BitVec 128 :=
  join128 (lowerAddLo aLo bLo) (lowerAddHi aLo aHi bLo bHi)

theorem lowerAddI128_correct (aLo aHi bLo bHi : BitVec 64) :
    lowerAddI128 aLo aHi bLo bHi = join128 aLo aHi + join128 bLo bHi := by
  simp only [lowerAddI128, lowerAddLo, lowerAddHi, addCarry, join128]
  bv_decide

theorem lowerAddI128_wrapping_correct (aLo aHi bLo bHi : BitVec 64) :
    lowerAddI128 aLo aHi bLo bHi = join128 aLo aHi + join128 bLo bHi :=
  lowerAddI128_correct aLo aHi bLo bHi

@[simp] def subBorrow (x y : BitVec 64) : BitVec 64 := if x < y then 1 else 0
@[simp] def lowerSubLo (aLo bLo : BitVec 64) : BitVec 64 := aLo - bLo
@[simp] def lowerSubHi (aLo aHi bLo bHi : BitVec 64) : BitVec 64 :=
  aHi - bHi - subBorrow aLo bLo
@[simp] def lowerSubI128 (aLo aHi bLo bHi : BitVec 64) : BitVec 128 :=
  join128 (lowerSubLo aLo bLo) (lowerSubHi aLo aHi bLo bHi)

theorem lowerSubI128_correct (aLo aHi bLo bHi : BitVec 64) :
    lowerSubI128 aLo aHi bLo bHi = join128 aLo aHi - join128 bLo bHi := by
  simp only [lowerSubI128, lowerSubLo, lowerSubHi, subBorrow, join128]
  bv_decide

theorem lowerSubI128_wrapping_correct (aLo aHi bLo bHi : BitVec 64) :
    lowerSubI128 aLo aHi bLo bHi = join128 aLo aHi - join128 bLo bHi :=
  lowerSubI128_correct aLo aHi bLo bHi

@[simp] def lowerNegI128 (xLo xHi : BitVec 64) : BitVec 128 :=
  lowerSubI128 (0 : BitVec 64) (0 : BitVec 64) xLo xHi

theorem lowerNegI128_correct (xLo xHi : BitVec 64) :
    lowerNegI128 xLo xHi = - join128 xLo xHi := by
  simp only [lowerNegI128, lowerSubI128, lowerSubLo, lowerSubHi, subBorrow, join128]
  bv_decide

@[simp] def mulFull (x y : BitVec 64) : BitVec 128 := (x.setWidth 128) * (y.setWidth 128)
@[simp] def lowerMulLo (aLo bLo : BitVec 64) : BitVec 64 := (mulFull aLo bLo).truncate 64
@[simp] def lowerMulHi (aLo aHi bLo bHi : BitVec 64) : BitVec 64 :=
  ((mulFull aLo bLo) >>> (64 : Nat)).truncate 64 + (aLo * bHi) + (aHi * bLo)
@[simp] def lowerMulI128 (aLo aHi bLo bHi : BitVec 64) : BitVec 128 :=
  join128 (lowerMulLo aLo bLo) (lowerMulHi aLo aHi bLo bHi)

theorem mulFull_toNat (x y : BitVec 64) : (mulFull x y).toNat = x.toNat * y.toNat := by
  simp only [mulFull, BitVec.toNat_mul, BitVec.toNat_setWidth]
  have hx : x.toNat < 2^64 := x.isLt
  have hy : y.toNat < 2^64 := y.isLt
  have he : (2:Nat)^128 = 2^64 * 2^64 := by rw [← Nat.pow_add]
  have hxp : x.toNat < 2^128 := by
    rw [he]; exact Nat.lt_of_lt_of_le hx (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos 64))
  have hyp : y.toNat < 2^128 := by
    rw [he]; exact Nat.lt_of_lt_of_le hy (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos 64))
  rw [Nat.mod_eq_of_lt hxp, Nat.mod_eq_of_lt hyp]
  apply Nat.mod_eq_of_lt; rw [he]; exact Nat.mul_lt_mul'' hx hy

theorem hi_toNat (x : BitVec 128) : ((x >>> (64 : Nat)).truncate 64).toNat = x.toNat / 2^64 := by
  rw [BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact x.isLt)

theorem lo_toNat (x : BitVec 128) : ((x).truncate 64).toNat = x.toNat % 2^64 := by
  rw [BitVec.truncate, BitVec.toNat_setWidth]

theorem collapse_mod (A B C n : Nat) : ((A + B % n) % n + C % n) % n = (A + B + C) % n := by
  rw [Nat.add_mod_mod, Nat.mod_add_mod]
  rw [show A + B % n + C = (A + C) + B % n by omega, Nat.add_mod_mod]
  rw [show A + C + B = A + B + C by omega]

theorem mul_connect (al ah bl bh : Nat) :
    (al*bl)%2^64 + 2^64 * (((al*bl)/2^64 + al*bh + ah*bl) % 2^64)
      = ((al + 2^64*ah) * (bl + 2^64*bh)) % 2^128 := by
  have he : (2:Nat)^128 = 2^64 * 2^64 := by rw [← Nat.pow_add]
  have hlo : (al*bl)%2^64 < 2^64 := Nat.mod_lt _ (Nat.two_pow_pos 64)
  have hhi : ((al*bl)/2^64 + al*bh + ah*bl) % 2^64 < 2^64 := Nat.mod_lt _ (Nat.two_pow_pos 64)
  have hbnd : ((al*bl)/2^64 + al*bh + ah*bl) % 2^64 * 2^64 + (al*bl)%2^64 < 2^128 := by
    rw [he]; exact mulAddBound _ _ (2^64) hhi hlo
  rw [Nat.mul_comm (2^64) (((al*bl)/2^64 + al*bh + ah*bl) % 2^64), Nat.add_comm ((al*bl)%2^64)]
  rw [← Nat.mod_eq_of_lt hbnd, he, school_gen al ah bl bh (2^64), ← he]

theorem lowerMulI128_correct (aLo aHi bLo bHi : BitVec 64) :
    lowerMulI128 aLo aHi bLo bHi = join128 aLo aHi * join128 bLo bHi := by
  apply BitVec.eq_of_toNat_eq
  rw [show lowerMulI128 aLo aHi bLo bHi
        = join128 (lowerMulLo aLo bLo) (lowerMulHi aLo aHi bLo bHi) from rfl, join_toNat]
  have hlo : (lowerMulLo aLo bLo).toNat = (aLo.toNat * bLo.toNat) % 2^64 := by
    simp only [lowerMulLo]; rw [lo_toNat, mulFull_toNat]
  have hhi : (lowerMulHi aLo aHi bLo bHi).toNat
      = ((aLo.toNat * bLo.toNat) / 2^64 + aLo.toNat * bHi.toNat + aHi.toNat * bLo.toNat) % 2^64 := by
    simp only [lowerMulHi]
    rw [BitVec.toNat_add, BitVec.toNat_add, hi_toNat, mulFull_toNat,
        BitVec.toNat_mul, BitVec.toNat_mul]
    exact collapse_mod (aLo.toNat * bLo.toNat / 2^64) (aLo.toNat * bHi.toNat)
            (aHi.toNat * bLo.toNat) (2^64)
  rw [hlo, hhi, BitVec.toNat_mul, join_toNat, join_toNat]
  exact mul_connect aLo.toNat aHi.toNat bLo.toNat bHi.toNat

@[simp] def lowerAddNarrow (ra rb : BitVec 64) : BitVec 64 := ra + rb
@[simp] def addSpec (w : Nat) (ra rb : BitVec 64) : BitVec w := ra.truncate w + rb.truncate w

theorem lowerAddNarrow_correct8 (ra rb : BitVec 64) :
    (lowerAddNarrow ra rb).truncate 8 = addSpec 8 ra rb := by
  simp only [lowerAddNarrow, addSpec]; bv_decide
theorem lowerAddNarrow_correct16 (ra rb : BitVec 64) :
    (lowerAddNarrow ra rb).truncate 16 = addSpec 16 ra rb := by
  simp only [lowerAddNarrow, addSpec]; bv_decide
theorem lowerAddNarrow_correct32 (ra rb : BitVec 64) :
    (lowerAddNarrow ra rb).truncate 32 = addSpec 32 ra rb := by
  simp only [lowerAddNarrow, addSpec]; bv_decide

@[simp] def lowerSubNarrow (ra rb : BitVec 64) : BitVec 64 := ra - rb
@[simp] def subSpec (w : Nat) (ra rb : BitVec 64) : BitVec w := ra.truncate w - rb.truncate w

theorem lowerSubNarrow_correct8 (ra rb : BitVec 64) :
    (lowerSubNarrow ra rb).truncate 8 = subSpec 8 ra rb := by
  simp only [lowerSubNarrow, subSpec]; bv_decide
theorem lowerSubNarrow_correct16 (ra rb : BitVec 64) :
    (lowerSubNarrow ra rb).truncate 16 = subSpec 16 ra rb := by
  simp only [lowerSubNarrow, subSpec]; bv_decide
theorem lowerSubNarrow_correct32 (ra rb : BitVec 64) :
    (lowerSubNarrow ra rb).truncate 32 = subSpec 32 ra rb := by
  simp only [lowerSubNarrow, subSpec]; bv_decide

@[simp] def lowerMulNarrow (ra rb : BitVec 64) : BitVec 64 := ra * rb
@[simp] def mulSpec (w : Nat) (ra rb : BitVec 64) : BitVec w := ra.truncate w * rb.truncate w

theorem lowerMulNarrow_correct8 (ra rb : BitVec 64) :
    (lowerMulNarrow ra rb).truncate 8 = mulSpec 8 ra rb := by
  simp only [lowerMulNarrow, mulSpec]; bv_decide
theorem lowerMulNarrow_correct16 (ra rb : BitVec 64) :
    (lowerMulNarrow ra rb).truncate 16 = mulSpec 16 ra rb := by
  simp only [lowerMulNarrow, mulSpec]; bv_decide
theorem lowerMulNarrow_correct32 (ra rb : BitVec 64) :
    (lowerMulNarrow ra rb).truncate 32 = mulSpec 32 ra rb := by
  simp only [lowerMulNarrow, mulSpec]; bv_decide

theorem lowerAddNarrow_correct (w : Nat) (h : w ≤ 64) (ra rb : BitVec 64) :
    (lowerAddNarrow ra rb).truncate w = addSpec w ra rb := by
  simp only [lowerAddNarrow, addSpec, BitVec.truncate]
  rw [BitVec.setWidth_add _ _ h]

structure BinOpI128Site (lay : Layout) (step : LoweredStep) (s s' : SrcState) where
  valueLeg  : ∀ m, R lay s m → ∀ v, Live s' v →
                denoteLoc (step.exec m) (lay.asgn v) (lay.kind v) = s'.env v
  clobberLeg : ∀ m, R lay s m → Preserves (clobberOf step) m (step.exec m)
  carrierLeg : ∀ m, R lay s m → WidthFaithful lay s' (step.exec m)
  memLeg     : ∀ m, R lay s m → agreeOn s'.mem (step.exec m) (lay.nonFrame)
  pcLeg      : ∀ m, R lay s m → (step.exec m).rip = lay.entryAddr (lay.lowerOf s'.pc)

def BinOpI128Site.toInstrCert
    {lay : Layout} {step : LoweredStep} {s s' : SrcState}
    (site : BinOpI128Site lay step s s') : InstrCert lay step s s' where
  value     := site.valueLeg
  clobber   := site.clobberLeg
  carrierOk := site.carrierLeg
  memOk     := site.memLeg
  pcOk      := site.pcLeg

theorem addI128_readback
    (m' : MachState) (rLo rHi aLo aHi bLo bHi : GPR)
    (hLo : m'.regs rLo = lowerAddLo (m'.regs aLo) (m'.regs bLo))
    (hHi : m'.regs rHi = lowerAddHi (m'.regs aLo) (m'.regs aHi) (m'.regs bLo) (m'.regs bHi)) :
    denoteLoc m' (.pair rLo rHi) .i128
      = .i128 (join128 (m'.regs aLo) (m'.regs aHi) + join128 (m'.regs bLo) (m'.regs bHi)) := by
  show Val.i128 ((m'.regs rHi ++ m'.regs rLo).cast (by omega : 64 + 64 = 128)) = _
  have hjoin : ((m'.regs rHi ++ m'.regs rLo).cast (by omega : 64 + 64 = 128))
        = lowerAddI128 (m'.regs aLo) (m'.regs aHi) (m'.regs bLo) (m'.regs bHi) := by
    simp only [lowerAddI128, join128, hLo, hHi]
  rw [hjoin, lowerAddI128_correct]

end Arith
end Cert
end Trust
