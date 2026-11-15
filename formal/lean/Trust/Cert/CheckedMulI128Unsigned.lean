/-
  Constructive arithmetic for the exact unsigned division-free i128 flag.
  This module does not register a Rust proof verdict or change the AY query.
-/
import Std.Tactic

set_option autoImplicit false
namespace Trust.Cert.CheckedMulI128Unsigned

abbrev limbBase : Nat := 18446744073709551616

/-- The original Rust source expression's exact high-half calculation, with
    each explicit 128-bit intermediate reduced modulo `2^128`. -/
def originalSourceHigh (al ah bl bh : Nat) : Nat :=
  let mid1 := (al * bl / limbBase + al * bh) % (limbBase * limbBase)
  let mid2 := (mid1 + ah * bl) % (limbBase * limbBase)
  let carry := if mid2 < mid1 then 1 else 0
  (mid2 / limbBase + ah * bh + carry * limbBase) % (limbBase * limbBase)

/-- The original division-free machine flag. The wrapped 128-bit product in
    `p1` and every 64-bit addition are kept explicitly, rather than normalized
    to a different goal. -/
def originalMachineFlag (al ah bl bh : Nat) : Prop :=
  let p1 := (((al + limbBase * ah) * (bl + limbBase * bh)) %
    (limbBase * limbBase)) / limbBase
  let t := (ah * bl % limbBase + al * bh % limbBase) % limbBase
  ah * bl / limbBase ≠ 0 ∨ al * bh / limbBase ≠ 0 ∨ p1 < t ∨ (ah ≠ 0 ∧ bh ≠ 0)

theorem schoolbook (al ah bl bh : Nat) :
    (al + limbBase * ah) * (bl + limbBase * bh) =
      al * bl + limbBase * (al * bh + ah * bl) +
        (limbBase * limbBase) * (ah * bh) := by
  simp only [Nat.mul_add, Nat.add_mul]
  ac_rfl

/-- An exact two-limb product has no wrapped or fabricated high payload. -/
theorem limb_product_bound (x y : Nat) (hx : x < limbBase) (hy : y < limbBase) :
    x * y < limbBase * limbBase := by
  exact Nat.mul_lt_mul'' hx hy

/-- The zero-product premise used by the free-product attempt is proved, not assumed. -/
theorem limb_product_zero (x y : Nat) :
    x * y = 0 ↔ x = 0 ∨ y = 0 := Nat.mul_eq_zero

/-- Adding a proper limb to a two-limb value overflows one limb exactly when
    its high limb is nonzero or the wrapped low limb is less than the addend. -/
theorem cross_add_overflow (h p : Nat) (hh : h < limbBase) :
    limbBase ≤ h + p ↔
      p / limbBase ≠ 0 ∨ (h + p % limbBase) % limbBase < p % limbBase := by
  have hd := Nat.mod_add_div p limbBase
  have hm := Nat.mod_lt p (by decide : 0 < limbBase)
  have hs := Nat.mod_add_div (h + p % limbBase) limbBase
  have hsm := Nat.mod_lt (h + p % limbBase) (by decide : 0 < limbBase)
  simp only [limbBase] at *
  omega

/-- The four products in the source are actual independent-limb products.
    Their bounds prove that the original high-half expression is the exact
    high 128 bits of the full (untruncated) 256-bit product. -/
theorem original_source_exact (al ah bl bh : Nat)
    (hal : al < limbBase) (hah : ah < limbBase)
    (hbl : bl < limbBase) (hbh : bh < limbBase) :
    originalSourceHigh al ah bl bh =
      (al + limbBase * ah) * (bl + limbBase * bh) / (limbBase * limbBase) := by
  have p00 := limb_product_bound al bl hal hbl
  have p01 := limb_product_bound al bh hal hbh
  have p10 := limb_product_bound ah bl hah hbl
  have p11 := limb_product_bound ah bh hah hbh
  have max_product (x y : Nat) (hx : x < limbBase) (hy : y < limbBase) :
      x * y ≤ (limbBase - 1) * (limbBase - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have b00 := max_product al bl hal hbl
  have b01 := max_product al bh hal hbh
  have a128 : al + limbBase * ah < limbBase * limbBase := by
    simp only [limbBase] at *
    omega
  have b128 : bl + limbBase * bh < limbBase * limbBase := by
    simp only [limbBase] at *
    omega
  have full := Nat.mul_lt_mul'' a128 b128
  have split00 := Nat.mod_add_div (al * bl) limbBase
  have mod00 := Nat.mod_lt (al * bl) (by decide : 0 < limbBase)
  have split1 := Nat.mod_add_div (al * bl / limbBase + al * bh)
    (limbBase * limbBase)
  have mod1 := Nat.mod_lt (al * bl / limbBase + al * bh)
    (by decide : 0 < limbBase * limbBase)
  have split2 := Nat.mod_add_div
    (((al * bl / limbBase + al * bh) % (limbBase * limbBase)) + ah * bl)
    (limbBase * limbBase)
  have mod2 := Nat.mod_lt
    (((al * bl / limbBase + al * bh) % (limbBase * limbBase)) + ah * bl)
    (by decide : 0 < limbBase * limbBase)
  have splitmid := Nat.mod_add_div
    ((((al * bl / limbBase + al * bh) % (limbBase * limbBase)) + ah * bl) %
      (limbBase * limbBase)) limbBase
  have modmid := Nat.mod_lt
    ((((al * bl / limbBase + al * bh) % (limbBase * limbBase)) + ah * bl) %
      (limbBase * limbBase)) (by decide : 0 < limbBase)
  have full_split := Nat.mod_add_div
    ((al + limbBase * ah) * (bl + limbBase * bh)) (limbBase * limbBase)
  have full_mod := Nat.mod_lt
    ((al + limbBase * ah) * (bl + limbBase * bh))
    (by decide : 0 < limbBase * limbBase)
  have expand := schoolbook al ah bl bh
  dsimp only [originalSourceHigh]
  split <;> simp only [limbBase] at * <;> omega

theorem single_cross_overflow (p00 p01 : Nat) (hp00 : p00 < limbBase * limbBase) :
    (p00 + limbBase * p01) / (limbBase * limbBase) ≠ 0 ↔
      p01 / limbBase ≠ 0 ∨
        ((p00 + limbBase * p01) % (limbBase * limbBase)) / limbBase <
          p01 % limbBase := by
  have bound : p00 / limbBase < limbBase := by
    simp only [limbBase] at *
    omega
  have carry := cross_add_overflow (p00 / limbBase) p01 bound
  simp only [limbBase] at *
  omega

/-- The complete unsigned statement, with all four independently quantified
    64-bit limbs. There are no free product premises or restricted valuations.
    The LHS is the original source high-half calculation and the RHS retains
    the original wrapped 128-bit product and 64-bit carry comparison. -/
theorem original_unsigned_limb_check (al ah bl bh : Nat)
    (hal : al < limbBase) (hah : ah < limbBase)
    (hbl : bl < limbBase) (hbh : bh < limbBase) :
    originalSourceHigh al ah bl bh ≠ 0 ↔ originalMachineFlag al ah bl bh := by
  rw [original_source_exact al ah bl bh hal hah hbl hbh]
  have expand := schoolbook al ah bl bh
  have p00 := limb_product_bound al bl hal hbl
  by_cases ahz : ah = 0
  · subst ah
    have single := single_cross_overflow (al * bl) (al * bh) p00
    simpa [originalMachineFlag, Nat.mul_add, Nat.mul_left_comm] using single
  · by_cases bhz : bh = 0
    · subst bh
      have single := single_cross_overflow (al * bl) (ah * bl) p00
      simpa [originalMachineFlag, Nat.add_mul, Nat.mul_assoc,
        Nat.or_comm] using single
    · have lower_a : limbBase ≤ al + limbBase * ah := by
        simp only [limbBase] at *
        omega
      have lower_b : limbBase ≤ bl + limbBase * bh := by
        simp only [limbBase] at *
        omega
      have lower := Nat.mul_le_mul lower_a lower_b
      have overflow :
          (al + limbBase * ah) * (bl + limbBase * bh) / (limbBase * limbBase) ≠ 0 := by
        simp only [limbBase] at *
        omega
      simp [originalMachineFlag, ahz, bhz, overflow]

/-- Exact counterpart of the Rust `limb_product`, with no 64-bit product
    truncation before the widening. -/
def limbProductBV (x y : BitVec 64) : BitVec 128 :=
  x.setWidth 128 * y.setWidth 128

def high64BV (x : BitVec 128) : BitVec 64 := (x >>> (64 : Nat)).truncate 64

def join128BV (lo hi : BitVec 64) : BitVec 128 :=
  hi ++ lo

def originalSourceBV (al ah bl bh : BitVec 64) : BitVec 128 :=
  let mid1 := (high64BV (limbProductBV al bl)).setWidth 128 + limbProductBV al bh
  let mid2 := mid1 + limbProductBV ah bl
  let carry : BitVec 1 := if mid2 < mid1 then 1 else 0
  (high64BV mid2).setWidth 128 + limbProductBV ah bh +
    (carry.setWidth 128 <<< (64 : Nat))

def originalMachineBV (al ah bl bh : BitVec 64) : Prop :=
  let p1 := high64BV (join128BV al ah * join128BV bl bh)
  let t := (limbProductBV ah bl).truncate 64 + (limbProductBV al bh).truncate 64
  high64BV (limbProductBV ah bl) ≠ 0 ∨
    high64BV (limbProductBV al bh) ≠ 0 ∨ p1 < t ∨ (ah ≠ 0 ∧ bh ≠ 0)

instance originalMachineBVDecidable (al ah bl bh : BitVec 64) :
    Decidable (originalMachineBV al ah bl bh) := by
  unfold originalMachineBV
  infer_instance

theorem limbProductBV_toNat (x y : BitVec 64) :
    (limbProductBV x y).toNat = x.toNat * y.toNat := by
  unfold limbProductBV
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth_of_le (by decide),
    BitVec.toNat_setWidth_of_le (by decide)]
  apply Nat.mod_eq_of_lt
  exact limb_product_bound x.toNat y.toNat x.isLt y.isLt

theorem high64BV_toNat (x : BitVec 128) :
    (high64BV x).toNat = x.toNat / limbBase := by
  rw [high64BV, BitVec.truncate, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  have bound := x.isLt
  omega

theorem high64BV_extract (x : BitVec 128) :
    high64BV x = x.extractLsb' 64 64 :=
  BitVec.setWidth_ushiftRight_eq_extractLsb

theorem join128BV_toNat (lo hi : BitVec 64) :
    (join128BV lo hi).toNat = lo.toNat + limbBase * hi.toNat := by
  rw [join128BV, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
    Nat.shiftLeft_eq]
  simp only [limbBase]
  omega

theorem originalSourceBV_toNat (al ah bl bh : BitVec 64) :
    (originalSourceBV al ah bl bh).toNat =
      originalSourceHigh al.toNat ah.toNat bl.toNat bh.toNat := by
  dsimp only [originalSourceBV, originalSourceHigh]
  simp only [BitVec.toNat_add,
    BitVec.toNat_setWidth_of_le (w := 64) (w' := 128) (by decide),
    BitVec.toNat_setWidth_of_le (w := 1) (w' := 128) (by decide),
    limbProductBV_toNat, high64BV_toNat, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, BitVec.lt_def]
  split <;> simp_all [limbBase, Nat.mod_add_mod] <;> split <;> omega

theorem originalMachineBV_iff (al ah bl bh : BitVec 64) :
    originalMachineBV al ah bl bh ↔
      originalMachineFlag al.toNat ah.toNat bl.toNat bh.toNat := by
  simp only [originalMachineBV, originalMachineFlag, ne_eq, ← BitVec.toNat_inj,
    BitVec.lt_def, high64BV_toNat, BitVec.toNat_mul,
    join128BV_toNat, BitVec.toNat_add, BitVec.truncate,
    BitVec.toNat_setWidth, limbProductBV_toNat]
  rfl

/-- Complete original unsigned flag correspondence over the full 256-bit
    input domain. All narrowing/widening and wrapped intermediate operations
    above have checked `toNat` transport; no valuation is sampled or assumed. -/
theorem original_unsigned_limb_check_bv (al ah bl bh : BitVec 64) :
    originalSourceBV al ah bl bh ≠ 0 ↔ originalMachineBV al ah bl bh := by
  have source : originalSourceBV al ah bl bh ≠ 0 ↔
      originalSourceHigh al.toNat ah.toNat bl.toNat bh.toNat ≠ 0 := by
    simp only [ne_eq, ← BitVec.toNat_inj]
    change (¬ (originalSourceBV al ah bl bh).toNat = 0) ↔ _
    rw [originalSourceBV_toNat]
  exact source.trans ((original_unsigned_limb_check al.toNat ah.toNat bl.toNat bh.toNat
    al.isLt ah.isLt bl.isLt bh.isLt).trans (originalMachineBV_iff al ah bl bh).symm)

/-- The actual one-bit equality, matching Rust's `bv1` encoding of both flags. -/
theorem original_unsigned_limb_check_flag (al ah bl bh : BitVec 64) :
    (if originalSourceBV al ah bl bh ≠ 0 then (1 : BitVec 1) else 0) =
      (if originalMachineBV al ah bl bh then (1 : BitVec 1) else 0) := by
  simp only [original_unsigned_limb_check_bv]

end Trust.Cert.CheckedMulI128Unsigned
