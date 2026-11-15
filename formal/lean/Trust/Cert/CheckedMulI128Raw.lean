/- Exact primitive interpretation of original CG SMT nodes. Candidate theorem
   selection is untrusted; a fresh original-goal kernel check is still required. -/
import Trust.Cert.CheckedMulI128Unsigned
import Trust.Cert.CheckedMulI128Signed
import Trust.Cert.CheckedMulI128Const

set_option autoImplicit false
namespace Trust.Cert.CheckedMulI128Raw

def bvOfNat (w v : Nat) : BitVec w := BitVec.ofNat w v
def bvAdd (w : Nat) (a b : BitVec w) : BitVec w := a + b
def bvSub (w : Nat) (a b : BitVec w) : BitVec w := a - b
def bvMul (w : Nat) (a b : BitVec w) : BitVec w := a * b
def bvAnd (w : Nat) (a b : BitVec w) : BitVec w := a &&& b
def bvOr (w : Nat) (a b : BitVec w) : BitVec w := a ||| b
def bvXor (w : Nat) (a b : BitVec w) : BitVec w := a ^^^ b
def bvNeg (w : Nat) (a : BitVec w) : BitVec w := -a
-- SMT-LIB's all-ones unsigned zero-divisor result is explicit.
def bvUDiv (w : Nat) (a b : BitVec w) : BitVec w := Trust.Cert.CheckedMulI128Const.smtUdiv w a b
def bvShl (w : Nat) (a b : BitVec w) : BitVec w := a <<< b.toNat
def bvLshr (w : Nat) (a b : BitVec w) : BitVec w := a >>> b.toNat
def bvAshr (w : Nat) (a b : BitVec w) : BitVec w := a.sshiftRight b.toNat
def bvEq (w : Nat) (a b : BitVec w) : Bool := decide (a = b)
def bvUlt (w : Nat) (a b : BitVec w) : Bool := decide (a < b)
def bvUgt (w : Nat) (a b : BitVec w) : Bool := decide (b < a)
def bvUle (w : Nat) (a b : BitVec w) : Bool := decide (a ≤ b)
def bvUge (w : Nat) (a b : BitVec w) : Bool := decide (b ≤ a)
def bvSlt (w : Nat) (a b : BitVec w) : Bool := decide (a.toInt < b.toInt)
def bvSgt (w : Nat) (a b : BitVec w) : Bool := decide (b.toInt < a.toInt)
def bvSle (w : Nat) (a b : BitVec w) : Bool := decide (a.toInt ≤ b.toInt)
def bvSge (w : Nat) (a b : BitVec w) : Bool := decide (b.toInt ≤ a.toInt)
def boolNot (a : Bool) : Bool := !a
def boolAnd (a b : Bool) : Bool := a && b
def boolOr (a b : Bool) : Bool := a || b
def boolEq (a b : Bool) : Bool := a == b
def boolIte (c a b : Bool) : Bool := cond c a b
def bvIte (w : Nat) (c : Bool) (a b : BitVec w) : BitVec w := cond c a b
def bvExtract (w hi lo : Nat) (x : BitVec w) : BitVec (hi-lo+1) := x.extractLsb hi lo
def bvConcat (hw lw : Nat) (hi : BitVec hw) (lo : BitVec lw) : BitVec (hw+lw) := hi ++ lo
def bvZeroExtend (w extra : Nat) (x : BitVec w) : BitVec (w+extra) := x.setWidth (w+extra)
def bvSignExtend (w extra : Nat) (x : BitVec w) : BitVec (w+extra) := x.signExtend (w+extra)

-- Helpers reproduce Rust constructor spelling; they do not normalize its AST.
def oneBit (c : Bool) : BitVec 1 := bvIte 1 c (bvOfNat 1 1) (bvOfNat 1 0)
def zero128 : BitVec 128 := bvConcat 64 64 (bvOfNat 64 0) (bvOfNat 64 0)
def one128 : BitVec 128 := bvConcat 64 64 (bvOfNat 64 0) (bvOfNat 64 1)
def min128 : BitVec 128 := bvConcat 64 64 (bvOfNat 64 9223372036854775808) (bvOfNat 64 0)
def max128 : BitVec 128 := bvConcat 64 64 (bvOfNat 64 9223372036854775807) (bvOfNat 64 18446744073709551615)
def allOnes128 : BitVec 128 := bvConcat 64 64 (bvOfNat 64 18446744073709551615) (bvOfNat 64 18446744073709551615)
def shift64 : BitVec 128 := bvConcat 64 64 (bvOfNat 64 0) (bvOfNat 64 64)
def high64 (x : BitVec 128) : BitVec 64 := bvExtract 128 127 64 x
def low64 (x : BitVec 128) : BitVec 64 := bvExtract 128 63 0 x
def highLimb (x : BitVec 128) : BitVec 64 := bvExtract 128 63 0 (bvLshr 128 x shift64)
def join (lo hi : BitVec 64) : BitVec 128 := bvConcat 64 64 hi lo
def limbProduct (x y : BitVec 64) : BitVec 128 := bvMul 128 (bvZeroExtend 64 64 x) (bvZeroExtend 64 64 y)
def sourceHigh (al ah bl bh : BitVec 64) : BitVec 128 :=
  let p00 := limbProduct al bl
  let p01 := limbProduct al bh
  let p10 := limbProduct ah bl
  let p11 := limbProduct ah bh
  let mid1 := bvAdd 128 (bvZeroExtend 64 64 (high64 p00)) p01
  let mid2 := bvAdd 128 mid1 p10
  let carry := oneBit (bvUlt 128 mid2 mid1)
  let carryTerm := bvShl 128 (bvZeroExtend 1 127 carry) (bvZeroExtend 64 64 (bvOfNat 64 64))
  bvAdd 128 (bvAdd 128 (bvZeroExtend 64 64 (high64 mid2)) p11) carryTerm

def unsignedSource (al ah bl bh : BitVec 64) : BitVec 1 :=
  oneBit (boolNot (bvEq 128 (sourceHigh al ah bl bh) zero128))

def unsignedCore (x0 x1 y0 y1 p1 : BitVec 64) : Bool :=
  let p10 := limbProduct x1 y0
  let p01 := limbProduct x0 y1
  let o1 := boolNot (bvEq 64 (high64 p10) (bvOfNat 64 0))
  let o2 := boolNot (bvEq 64 (high64 p01) (bvOfNat 64 0))
  let t := bvAdd 64 (low64 p10) (low64 p01)
  let carry := bvUlt 64 p1 t
  let both := boolAnd (boolNot (bvEq 64 x1 (bvOfNat 64 0))) (boolNot (bvEq 64 y1 (bvOfNat 64 0)))
  boolOr (boolOr (boolOr o1 o2) carry) both

def unsignedMachine (al ah bl bh : BitVec 64) : BitVec 1 :=
  let a := join al ah
  let b := join bl bh
  oneBit (unsignedCore (low64 a) (highLimb a) (low64 b) (highLimb b) (highLimb (bvMul 128 a b)))

def maskedHigh (x0 x1 m : BitVec 64) : BitVec 64 :=
  let nonzero := bvLshr 64 (bvOr 64 x0 (bvSub 64 (bvOfNat 64 0) x0)) (bvOfNat 64 63)
  let borrow := bvAnd 64 nonzero m
  bvSub 64 (bvSub 64 (bvXor 64 x1 m) m) borrow

def magnitudeLow (x0 m : BitVec 64) : BitVec 64 := bvSub 64 (bvXor 64 x0 m) m

def signNegative (a : BitVec 128) : Bool := bvEq 1 (bvExtract 128 127 127 a) (bvOfNat 1 1)
def magnitude (a : BitVec 128) : BitVec 128 := bvIte 128 (signNegative a) (bvNeg 128 a) a
def resultNegative (a b : BitVec 128) : Bool := boolNot (boolEq (signNegative a) (signNegative b))
def signedLimit (a b : BitVec 128) : BitVec 128 := bvIte 128 (resultNegative a b) min128 max128

def signedSource (al ah bl bh : BitVec 64) : BitVec 1 :=
  let a := join al ah
  let b := join bl bh
  let ua := magnitude a
  let ub := magnitude b
  let high := sourceHigh (low64 ua) (high64 ua) (low64 ub) (high64 ub)
  let low := bvMul 128 ua ub
  oneBit (boolOr (boolNot (bvEq 128 high zero128)) (bvUgt 128 low (signedLimit a b)))

def signedMachine (al ah bl bh : BitVec 64) : BitVec 1 :=
  let a := join al ah
  let b := join bl bh
  let r := bvMul 128 a b
  let a0 := low64 a
  let a1 := highLimb a
  let b0 := low64 b
  let b1 := highLimb b
  let r0 := low64 r
  let r1 := highLimb r
  let ma := bvAshr 64 a1 (bvOfNat 64 63)
  let mb := bvAshr 64 b1 (bvOfNat 64 63)
  let ua0 := magnitudeLow a0 ma
  let ua1 := maskedHigh a0 a1 ma
  let ub0 := magnitudeLow b0 mb
  let ub1 := maskedHigh b0 b1 mb
  let mn := bvXor 64 ma mb
  let pu1 := maskedHigh r0 r1 mn
  let ou := unsignedCore ua0 ua1 ub0 ub1 pu1
  let sign := boolNot (bvEq 64 (bvXor 64 (bvAshr 64 r1 (bvOfNat 64 63)) mn) (bvOfNat 64 0))
  let rnz := boolNot (bvEq 64 (bvOr 64 r0 r1) (bvOfNat 64 0))
  oneBit (boolOr ou (boolAnd sign rnz))

def constMachine (al ah bl bh : BitVec 64) : BitVec 1 :=
  let a := join al ah
  let b := join bl bh
  let limit := bvIte 128 (bvEq 128 b zero128) allOnes128 (bvUDiv 128 allOnes128 b)
  oneBit (bvUgt 128 a limit)

theorem high64_eq (x : BitVec 128) : high64 x = Trust.Cert.CheckedMulI128Unsigned.high64BV x := (Trust.Cert.CheckedMulI128Unsigned.high64BV_extract x).symm
theorem highLimb_eq (x : BitVec 128) : highLimb x = Trust.Cert.CheckedMulI128Unsigned.high64BV x := rfl
theorem low64_eq (x : BitVec 128) : low64 x = Trust.Cert.CheckedMulI128Signed.low64BV x := rfl
theorem join_eq (lo hi : BitVec 64) : join lo hi = Trust.Cert.CheckedMulI128Unsigned.join128BV lo hi := rfl

theorem sourceHigh_eq (al ah bl bh : BitVec 64) : sourceHigh al ah bl bh = Trust.Cert.CheckedMulI128Unsigned.originalSourceBV al ah bl bh := by
  simp only [sourceHigh, high64_eq, limbProduct, bvMul, bvZeroExtend, bvAdd,
    bvShl, bvOfNat, oneBit, bvIte, bvUlt, Trust.Cert.CheckedMulI128Unsigned.originalSourceBV, Trust.Cert.CheckedMulI128Unsigned.limbProductBV]
  simp only [Bool.cond_decide]
  rfl

theorem low_join (al ah : BitVec 64) : low64 (join al ah) = al := by
  simp only [low64, join, bvExtract, bvConcat, BitVec.extractLsb]
  exact BitVec.extractLsb'_append_eq_right

theorem high_join (al ah : BitVec 64) : highLimb (join al ah) = ah := by
  rw [highLimb_eq, Trust.Cert.CheckedMulI128Unsigned.high64BV_extract]
  exact BitVec.extractLsb'_append_eq_left

theorem unsignedSource_eq (al ah bl bh : BitVec 64) :
    unsignedSource al ah bl bh =
      (if Trust.Cert.CheckedMulI128Unsigned.originalSourceBV al ah bl bh ≠ 0 then (1 : BitVec 1) else 0) := by
  simp only [unsignedSource, sourceHigh_eq, oneBit, bvIte, boolNot, bvEq, zero128, bvConcat, bvOfNat]
  rw [← decide_not]
  rw [Bool.cond_decide]
  rfl

theorem unsignedCore_iff (al ah bl bh p1 : BitVec 64) :
    unsignedCore al ah bl bh p1 = true ↔
      Trust.Cert.CheckedMulI128Signed.unsignedCore al ah bl bh p1 := by
  simp [unsignedCore, boolOr, boolAnd, boolNot, bvEq, bvUlt, high64_eq, low64_eq,
    limbProduct, bvMul, bvZeroExtend, bvAdd, bvOfNat,
    Trust.Cert.CheckedMulI128Signed.unsignedCore,
    Trust.Cert.CheckedMulI128Signed.low64BV,
    Trust.Cert.CheckedMulI128Unsigned.limbProductBV, or_assoc]

theorem unsignedMachine_eq (al ah bl bh : BitVec 64) :
    unsignedMachine al ah bl bh =
      (if Trust.Cert.CheckedMulI128Unsigned.originalMachineBV al ah bl bh then (1 : BitVec 1) else 0) := by
  simp only [unsignedMachine, low_join, high_join]
  simp only [highLimb_eq, bvMul, join_eq,
    oneBit, bvIte, bvOfNat, Bool.cond_eq_ite, unsignedCore_iff]
  rfl

theorem original_unsigned (al ah bl bh : BitVec 64) :
    unsignedSource al ah bl bh = unsignedMachine al ah bl bh := by
  rw [unsignedSource_eq, unsignedMachine_eq]
  exact Trust.Cert.CheckedMulI128Unsigned.original_unsigned_limb_check_flag al ah bl bh

theorem constMachine_eq (al ah bl bh : BitVec 64) :
    constMachine al ah bl bh =
      (if Trust.Cert.CheckedMulI128Const.wordLimit 128 (Trust.Cert.CheckedMulI128Unsigned.join128BV bl bh) <
          Trust.Cert.CheckedMulI128Unsigned.join128BV al ah then (1 : BitVec 1) else 0) := by
  simp only [constMachine, oneBit, bvIte, bvEq, bvUgt, bvUDiv, bvOfNat, join_eq,
    zero128, allOnes128, bvConcat, Trust.Cert.CheckedMulI128Const.wordLimit,
    Trust.Cert.CheckedMulI128Const.wordMax, Bool.cond_decide]
  rfl

theorem original_constant (al ah bl bh : BitVec 64) :
    unsignedSource al ah bl bh = constMachine al ah bl bh := by
  rw [unsignedSource_eq, constMachine_eq]
  exact Trust.Cert.CheckedMulI128Const.original_constant_limit_flag al ah bl bh

theorem signNegative_eq (a : BitVec 128) :
    signNegative a = Trust.Cert.CheckedMulI128Signed.signNegative a := rfl

theorem magnitude_eq (a : BitVec 128) :
    magnitude a = Trust.Cert.CheckedMulI128Signed.magnitude a := by
  simp only [magnitude, signNegative_eq, bvIte, bvNeg, Bool.cond_eq_ite,
    Trust.Cert.CheckedMulI128Signed.magnitude]

theorem resultNegative_eq (a b : BitVec 128) :
    resultNegative a b = Trust.Cert.CheckedMulI128Signed.resultNegative a b := rfl

theorem signedLimit_eq (a b : BitVec 128) :
    signedLimit a b = (if Trust.Cert.CheckedMulI128Signed.resultNegative a b then
      (170141183460469231731687303715884105728 : BitVec 128)
      else 170141183460469231731687303715884105727) := by
  simp only [signedLimit, resultNegative_eq, bvIte, Bool.cond_eq_ite]
  cases Trust.Cert.CheckedMulI128Signed.resultNegative a b <;> rfl

theorem boolNot_decide (p : Prop) [Decidable p] : boolNot (decide p) = decide (¬ p) := by
  simp only [boolNot, decide_not]

theorem boolAnd_decide (p q : Prop) [Decidable p] [Decidable q] :
    boolAnd (decide p) (decide q) = decide (p ∧ q) := by
  simp only [boolAnd, Bool.decide_and]

theorem boolOr_decide (p q : Prop) [Decidable p] [Decidable q] :
    boolOr (decide p) (decide q) = decide (p ∨ q) := by
  simp only [boolOr, Bool.decide_or]

theorem oneBit_decide (p : Prop) [Decidable p] :
    oneBit (decide p) = if p then (1 : BitVec 1) else 0 := by
  simp only [oneBit, bvIte, bvOfNat, Bool.cond_decide]
  rfl

theorem zero128_eq : zero128 = (0 : BitVec 128) := rfl

theorem mathLowJoin (al ah : BitVec 64) :
    Trust.Cert.CheckedMulI128Signed.low64BV (Trust.Cert.CheckedMulI128Unsigned.join128BV al ah) = al := by
  simpa only [Trust.Cert.CheckedMulI128Signed.low64BV,
    Trust.Cert.CheckedMulI128Unsigned.join128BV] using
      (BitVec.setWidth_append_eq_right (a := ah) (b := al))

theorem mathHighJoin (al ah : BitVec 64) :
    Trust.Cert.CheckedMulI128Unsigned.high64BV (Trust.Cert.CheckedMulI128Unsigned.join128BV al ah) = ah := by
  rw [Trust.Cert.CheckedMulI128Unsigned.high64BV_extract]
  exact BitVec.extractLsb'_append_eq_left

-- The whole-predicate decision parameter is explicit. This transports the
-- conditional without evaluating either large symbolic arithmetic subtree.
theorem signedFlagEncoding (hi low limit : BitVec 128)
    (d : Decidable (hi ≠ 0 ∨ limit < low)) :
    oneBit (boolOr (boolNot (bvEq 128 hi 0)) (bvUgt 128 low limit)) =
      @ite (BitVec 1) (hi ≠ 0 ∨ limit < low) d 1 0 := by
  simp only [bvEq, bvUgt, boolNot_decide, boolOr_decide, oneBit_decide]
  apply ite_cond_congr
  rfl

theorem signedSource_eq (al ah bl bh : BitVec 64) :
    signedSource al ah bl bh =
      (if Trust.Cert.CheckedMulI128Signed.originalSourceSignedFlag al ah bl bh then (1 : BitVec 1) else 0) := by
  simp only [signedSource, magnitude_eq, sourceHigh_eq, high64_eq, low64_eq, signedLimit_eq,
    join_eq, bvMul, zero128_eq]
  exact signedFlagEncoding _ _ _
    (inferInstance : Decidable (Trust.Cert.CheckedMulI128Signed.originalSourceSignedFlag al ah bl bh))

theorem maskedHigh_eq (lo hi m : BitVec 64) :
    maskedHigh lo hi m = Trust.Cert.CheckedMulI128Signed.maskedHigh lo hi m := rfl

theorem magnitudeLow_eq (lo m : BitVec 64) :
    magnitudeLow lo m = Trust.Cert.CheckedMulI128Signed.maskedLow lo m := rfl

theorem unsignedCore_eq_decide (al ah bl bh p1 : BitVec 64) :
    unsignedCore al ah bl bh p1 =
      decide (Trust.Cert.CheckedMulI128Signed.unsignedCore al ah bl bh p1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, unsignedCore_iff]

theorem signedMachine_eq (al ah bl bh : BitVec 64) :
    signedMachine al ah bl bh =
      (if Trust.Cert.CheckedMulI128Signed.originalMachineSignedFlag al ah bl bh then (1 : BitVec 1) else 0) := by
  simp only [signedMachine, low_join, high_join]
  simp only [unsignedCore_eq_decide, highLimb_eq, low64_eq, join_eq,
    maskedHigh_eq, magnitudeLow_eq, bvMul, bvAshr, bvXor, bvOr, bvEq, bvOfNat,
    boolNot_decide, boolAnd_decide, boolOr_decide, oneBit_decide]
  simp only [Trust.Cert.CheckedMulI128Signed.originalMachineSignedFlag,
    Trust.Cert.CheckedMulI128Signed.machineMagnitudeCore,
    Trust.Cert.CheckedMulI128Signed.machineSignBad,
    Trust.Cert.CheckedMulI128Signed.signMask, mathLowJoin, mathHighJoin]
  rfl

theorem original_signed (al ah bl bh : BitVec 64) :
    signedSource al ah bl bh = signedMachine al ah bl bh := by
  rw [signedSource_eq, signedMachine_eq]
  exact Trust.Cert.CheckedMulI128Signed.original_signed_limb_check_flag al ah bl bh

#print axioms original_unsigned
#print axioms original_signed
#print axioms original_constant

end Trust.Cert.CheckedMulI128Raw
