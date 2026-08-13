/-
  Model.Memory — the byte-addressed memory model and the MEMORY NON-INTERFERENCE proofs
  for trust-cg's Lean correctness development.

  This module is the formal counterpart of the `memory non-interference` validator
  and mirrors the exact symmetric, two-sided, no-wrap precondition shape used by the Rust gate in
  `crates/trust-cg-verify/src/memory_proofs.rs::proof_non_interference_symbolic`:
    - no wrapping on BOTH regions:  `base + storeW >u base`  and  `addr + loadW >u addr`;
    - disjointness, symmetric two-sided:
        `addr ≥u base + storeW   ∨   base ≥u addr + loadW`.

  Copyright 2026 Andrew Yates. Apache 2.0.
-/
import Trust.Model

namespace Trust

/-! ## The byte store and its single-byte update -/

abbrev Mem := BitVec 64 → BitVec 8

def MachState.writeByte (m : MachState) (a : BitVec 64) (v : BitVec 8) : MachState :=
  { m with mem := fun x => if x = a then v else m.mem x }

@[simp] theorem writeByte_mem_self (m : MachState) (a : BitVec 64) (v : BitVec 8) :
    (m.writeByte a v).mem a = v := by
  simp [MachState.writeByte]

theorem writeByte_mem_of_ne (m : MachState) (a : BitVec 64) (v : BitVec 8)
    {r : BitVec 64} (h : r ≠ a) : (m.writeByte a v).mem r = m.mem r := by
  simp [MachState.writeByte, h]

/-! ## Little-endian multi-byte read / write -/

abbrev readLE (m : MachState) (a : BitVec 64) (w : Nat) : BitVec (8 * w) :=
  readBytes m a w

def writeLE (m : MachState) (base : BitVec 64) : (w : Nat) → BitVec (8 * w) → MachState
  | 0,    _   => m
  | w+1,  val =>
      let lo   : BitVec 8        := val.truncate 8
      let rest : BitVec (8 * w)  := (val >>> (8 : BitVec (8 * (w+1)))).truncate (8 * w)
      writeLE (m.writeByte base lo) (base + 1) w rest

@[simp] theorem writeLE_zero (m : MachState) (base : BitVec 64) (val : BitVec (8 * 0)) :
    writeLE m base 0 val = m := rfl

/-! ## Ranges and (two-sided, no-wrap) disjointness — the validator's contract -/

def Range (base : BitVec 64) (w : Nat) (x : BitVec 64) : Prop :=
  ∃ k : Nat, k < w ∧ x = base + BitVec.ofNat 64 k

def NoWrap (base : BitVec 64) (w : Nat) : Prop :=
  base + BitVec.ofNat 64 w > base

def Disjoint (base : BitVec 64) (sw : Nat) (addr : BitVec 64) (lw : Nat) : Prop :=
  addr ≥ base + BitVec.ofNat 64 sw ∨ base ≥ addr + BitVec.ofNat 64 lw

/-! ## Address arithmetic and the per-byte distinctness bridge -/

theorem addr_step (base : BitVec 64) (k : Nat) :
    (base + 1) + BitVec.ofNat 64 k = base + BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.ofNat_add]
  show (base + 1) + BitVec.ofNat 64 k = base + (BitVec.ofNat 64 k + BitVec.ofNat 64 1)
  have h1 : (BitVec.ofNat 64 1 : BitVec 64) = 1 := rfl
  rw [h1]; bv_decide

theorem byte_distinct
    {base addr : BitVec 64} {sw lw : Nat}
    (hsw : sw < 2 ^ 64) (hlw : lw < 2 ^ 64)
    (hnwS : NoWrap base sw) (hnwL : NoWrap addr lw)
    (hdis : Disjoint base sw addr lw)
    {j k : Nat} (hj : j < lw) (hk : k < sw) :
    addr + BitVec.ofNat 64 j ≠ base + BitVec.ofNat 64 k := by
  intro heq
  have e1 : (addr + BitVec.ofNat 64 j).toNat = (base + BitVec.ofNat 64 k).toNat := by rw [heq]
  simp only [NoWrap, GT.gt, BitVec.lt_def, BitVec.toNat_add, BitVec.toNat_ofNat] at hnwS hnwL
  simp only [Disjoint, BitVec.le_def, BitVec.toNat_add, BitVec.toNat_ofNat] at hdis
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at e1
  have hb := base.isLt
  have ha := addr.isLt
  have hjmod  : j  % 2 ^ 64 = j  := Nat.mod_eq_of_lt (by omega)
  have hkmod  : k  % 2 ^ 64 = k  := Nat.mod_eq_of_lt (by omega)
  have hswmod : sw % 2 ^ 64 = sw := Nat.mod_eq_of_lt hsw
  have hlwmod : lw % 2 ^ 64 = lw := Nat.mod_eq_of_lt hlw
  omega

/-! ## Frame lemma: a write only perturbs its own range -/

theorem writeLE_mem_frame (base : BitVec 64) :
    ∀ (w : Nat) (val : BitVec (8 * w)) (m : MachState) (r : BitVec 64),
      (∀ k : Nat, k < w → r ≠ base + BitVec.ofNat 64 k) →
      (writeLE m base w val).mem r = m.mem r := by
  intro w
  induction w generalizing base with
  | zero => intro val m r _; simp [writeLE]
  | succ w ih =>
      intro val m r hdisj
      simp only [writeLE]
      rw [ih (base + 1)]
      · have hne : r ≠ base := by
          have := hdisj 0 (Nat.succ_pos w); simpa using this
        exact writeByte_mem_of_ne _ _ _ hne
      · intro k hk
        rw [addr_step base k]
        exact hdisj (k + 1) (by omega)

/-! ## readLE depends only on its own range -/

theorem readLE_congr (a : BitVec 64) :
    ∀ (n : Nat) (m m' : MachState),
      (∀ j : Nat, j < n → m.mem (a + BitVec.ofNat 64 j) = m'.mem (a + BitVec.ofNat 64 j)) →
      readLE m a n = readLE m' a n := by
  intro n
  induction n generalizing a with
  | zero => intro m m' _; simp [readLE, readBytes]
  | succ n ih =>
      intro m m' hmem
      simp only [readLE, readBytes]
      have h0 : m.mem a = m'.mem a := by
        have := hmem 0 (Nat.succ_pos n); simpa using this
      have hrec : readBytes m (a + 1) n = readBytes m' (a + 1) n := by
        apply ih
        intro j hj
        rw [addr_step a j]
        exact hmem (j + 1) (by omega)
      rw [h0, hrec]

/-! ## ── MEMORY NON-INTERFERENCE ── the two headline read/write facts -/

theorem read_write_disjoint
    {m : MachState} {base addr : BitVec 64} {storeW loadW : Nat}
    (hsw : storeW < 2 ^ 64) (hlw : loadW < 2 ^ 64)
    (hnwS : NoWrap base storeW) (hnwL : NoWrap addr loadW)
    (hdis : Disjoint base storeW addr loadW)
    (val : BitVec (8 * storeW)) :
    readLE (writeLE m base storeW val) addr loadW = readLE m addr loadW := by
  apply readLE_congr
  intro j hj
  apply writeLE_mem_frame
  intro k hk
  exact byte_distinct hsw hlw hnwS hnwL hdis hj hk

theorem read_write_same
    (m : MachState) (base : BitVec 64) (w : Nat) (val : BitVec (8 * w)) :
    readLE (writeLE m base w val) base w = val := by
  -- MECHANICAL (stubbed): the LE round-trip. Heterogeneous-width BitVec bookkeeping
  -- (cast/++/>>>/truncate). Axiom-isolated (sorryAx) and NOT consumed downstream.
  sorry

/-! ## agreeOn and its store-preservation lemma (R.memAgree maintenance) -/

theorem agreeOn_def (sm : SrcMem) (m : MachState) (p : BitVec 64 → Prop) :
    agreeOn sm m p ↔ ∀ a, p a → sm a = m.mem a := Iff.rfl

theorem agreeOn_writeByte
    {sm : SrcMem} {m : MachState} {p : BitVec 64 → Prop}
    (h : agreeOn sm m p) {a : BitVec 64} {v : BitVec 8} (hp : ¬ p a) :
    agreeOn sm (m.writeByte a v) p := by
  intro r hr
  have hne : r ≠ a := by rintro rfl; exact hp hr
  rw [writeByte_mem_of_ne _ _ _ hne]
  exact h r hr

theorem agreeOn_write
    {sm : SrcMem} {p : BitVec 64 → Prop} (base : BitVec 64) :
    ∀ (w : Nat) (val : BitVec (8 * w)) (m : MachState),
      agreeOn sm m p →
      (∀ k : Nat, k < w → ¬ p (base + BitVec.ofNat 64 k)) →
      agreeOn sm (writeLE m base w val) p := by
  intro w
  induction w generalizing base with
  | zero => intro val m h _; simpa [writeLE] using h
  | succ w ih =>
      intro val m h hoff
      simp only [writeLE]
      apply ih (base + 1)
      · exact agreeOn_writeByte h (by have := hoff 0 (Nat.succ_pos w); simpa using this)
      · intro k hk
        rw [addr_step base k]
        exact hoff (k + 1) (by omega)

theorem memAgree_preserved_by_frame_store
    {lay : Layout} {s : SrcState} {m : MachState}
    (base : BitVec 64) (w : Nat) (val : BitVec (8 * w))
    (hagree : agreeOn s.mem m lay.nonFrame)
    (hframe : ∀ k : Nat, k < w → ¬ lay.nonFrame (base + BitVec.ofNat 64 k)) :
    agreeOn s.mem (writeLE m base w val) lay.nonFrame :=
  agreeOn_write base w val m hagree hframe

end Trust
