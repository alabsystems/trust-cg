/- Copyright 2026 Andrew Yates | License: Apache-2.0 -/

import Trust.A64.EuclideanRemainder
import Trust.A64.Machine
import Trust.Semantics.Source

namespace Trust
namespace A64

private theorem registerPair_toNat (a b : Reg) :
    (32 * UInt32.ofNat a.val + UInt32.ofNat b.val).toNat = 32 * a.val + b.val := by
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat, UInt32.toNat_ofNat',
    Nat.mod_add_mod, Nat.add_mod_mod, Nat.mod_mul_mod, Nat.mul_mod_mod]
  apply Nat.mod_eq_of_lt
  have ha := a.isLt
  have hb := b.isLt
  omega

/-- A zero delta certifies both decoded move-source registers. -/
theorem euclideanRegisterUpdate_eq (b r nextASrc nextBSrc : Reg) :
    trust_cg_a64_euclidean_register_update
      (UInt32.ofNat b.val) (UInt32.ofNat r.val)
      (UInt32.ofNat nextASrc.val) (UInt32.ofNat nextBSrc.val) = 0 ↔
      nextASrc = b ∧ nextBSrc = r := by
  constructor
  · intro h
    have hz := congrArg UInt32.toBitVec h
    simp only [trust_cg_a64_euclidean_register_update, UInt32.toBitVec_sub] at hz
    have hp := BitVec.sub_add_cancel
      (32 * UInt32.ofNat b.val + UInt32.ofNat r.val).toBitVec
      (32 * UInt32.ofNat nextASrc.val + UInt32.ofNat nextBSrc.val).toBitVec
    rw [hz] at hp
    have hn := congrArg BitVec.toNat hp
    simp only [UInt32.toBitVec_ofNat, BitVec.zero_add, UInt32.toNat_toBitVec,
      registerPair_toNat] at hn
    have hr := r.isLt
    have hnextB := nextBSrc.isLt
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    simp [trust_cg_a64_euclidean_register_update]

theorem exec_udiv64 (q a b : Reg) (s : MachState) :
    exec (.dataProc2 1 b 2 a q) s =
      some (s.writeX q (s.readX a / s.readX b)).advance := by
  simp [exec, Instr.valid, execValid, datasize, BitVec.udiv_def]

theorem exec_msub64 (r q b a : Reg) (s : MachState) :
    exec (.dataProc3 1 0 b 1 a q r) s =
      some (s.writeX r (s.readX a - s.readX q * s.readX b)).advance := by
  simp [exec, Instr.valid, execValid, datasize] <;> rfl

theorem exec_mov64 (dst src : Reg) (s : MachState) :
    exec (.logicalShifted 1 1 0 0 src 0 31 dst) s =
      some (s.writeX dst (s.readX src)).advance := by
  simp [exec, Instr.valid, execValid, datasize, shiftReg, Exec.logicOp]
  change (s.writeX dst (0#64 ||| (s.readX src <<< (0 : Nat)))).advance =
    (s.writeX dst (s.readX src)).advance
  rw [BitVec.shiftLeft_zero, BitVec.zero_or]

theorem exec_cbz64 (offset : Fin 524288) (b : Reg) (s : MachState) :
    exec (.compareBranch 1 0 offset b) s =
      if s.readX b == 0#64 then
        some { s with pc := s.pc + BitVec.ofInt 64 (4 * sext 19 offset.val) }
      else some s.advance := by
  simp [exec, Instr.valid, execValid, datasize]
  change (if (s.readX b == 0#64) = true then
      some { s with pc := s.pc + BitVec.ofInt 64 (4 * sext 19 offset.val) }
    else some s.advance) = _
  simp only [beq_iff_eq]

private theorem read_advance_write_same (s : MachState) (r : Reg) (v : BitVec 64)
    (live : r.val < 31) :
    ((s.writeX r v).advance).readX r = v := by
  simp [MachState.readX, MachState.writeX, MachState.advance, live]

private theorem read_advance_write_other (s : MachState) (r dst : Reg) (v : BitVec 64)
    (distinct : r ≠ dst) :
    ((s.writeX dst v).advance).readX r = s.readX r := by
  by_cases hd : dst.val < 31
  · by_cases hr : r.val < 31
    · have h : (⟨r.val, hr⟩ : Fin 31) ≠ ⟨dst.val, hd⟩ := by
        intro he
        exact distinct (Fin.ext (congrArg (fun i : Fin 31 => i.val) he))
      simp [MachState.readX, MachState.writeX, MachState.advance, hd, hr, h]
    · simp [MachState.readX, hr]
  · simp [MachState.readX, MachState.writeX, MachState.advance, hd]

/-- The four allocated arithmetic and update words before the zero-test latch. -/
def euclideanLatch (a b q r nextASrc nextBSrc : Reg) (s : MachState) : Option MachState := do
  let s ← exec (.dataProc2 1 b 2 a q) s
  let s ← exec (.dataProc3 1 0 b 1 a q r) s
  let s ← exec (.logicalShifted 1 1 0 0 nextASrc 0 31 a) s
  exec (.logicalShifted 1 1 0 0 nextBSrc 0 31 b) s

/-- The checked routing gives the source remainder and the next Euclidean pair.
    The caller binds the decoded registers and the nonzero guard. -/
theorem exec_euclidean_latch (s : MachState) (a b q r nextASrc nextBSrc : Reg)
    (route : trust_cg_a64_euclidean_register_update
      (UInt32.ofNat b.val) (UInt32.ofNat r.val)
      (UInt32.ofNat nextASrc.val) (UInt32.ofNat nextBSrc.val) = 0)
    (quotientLive : q.val < 31) (remainderLive : r.val < 31)
    (dividendQuotient : a ≠ q) (divisorQuotient : b ≠ q)
    (divisorRemainder : b ≠ r) (remainderDividend : r ≠ a)
    (nonzero : s.readX b ≠ 0#64) :
    let quotient := s.readX a / s.readX b
    let remainder := s.readX a % s.readX b
    let divided := (s.writeX q quotient).advance
    let reduced := (divided.writeX r remainder).advance
    let shiftedA := (reduced.writeX a (s.readX b)).advance
    euclideanLatch a b q r nextASrc nextBSrc s =
      some (shiftedA.writeX b remainder).advance := by
  obtain ⟨nextA, nextB⟩ := (euclideanRegisterUpdate_eq b r nextASrc nextBSrc).mp route
  subst nextASrc
  subst nextBSrc
  have rem_eq :
      s.readX a - (s.readX a / s.readX b) * s.readX b = s.readX a % s.readX b :=
    Source.evalBin_urem_eq_umod 64 (s.readX a) (s.readX b) nonzero
  simp [euclideanLatch, exec_udiv64, exec_msub64, exec_mov64, read_advance_write_same,
    read_advance_write_other, quotientLive, remainderLive, dividendQuotient,
    divisorQuotient, divisorRemainder, remainderDividend, rem_eq]

/-- The checked latch stores the source Urem in the divisor register. Its CBZ
    takes the exit exactly when that value is zero. -/
theorem exec_euclidean_latch_cbz (s : MachState) (a b q r nextASrc nextBSrc : Reg)
    (offset : Fin 524288)
    (route : trust_cg_a64_euclidean_register_update
      (UInt32.ofNat b.val) (UInt32.ofNat r.val)
      (UInt32.ofNat nextASrc.val) (UInt32.ofNat nextBSrc.val) = 0)
    (divisorLive : b.val < 31) (quotientLive : q.val < 31) (remainderLive : r.val < 31)
    (dividendQuotient : a ≠ q) (divisorQuotient : b ≠ q)
    (divisorRemainder : b ≠ r) (remainderDividend : r ≠ a)
    (nonzero : s.readX b ≠ 0#64) :
    let sourceRemainder := Source.evalBin .urem 64 (s.readX a) (s.readX b)
    ∃ final, euclideanLatch a b q r nextASrc nextBSrc s = some final ∧
      final.readX b = sourceRemainder ∧
      exec (.compareBranch 1 0 offset b) final =
        if sourceRemainder == 0#64 then
          some { final with pc := final.pc + BitVec.ofInt 64 (4 * sext 19 offset.val) }
        else some final.advance := by
  let quotient := s.readX a / s.readX b
  let remainder := s.readX a % s.readX b
  let divided := (s.writeX q quotient).advance
  let reduced := (divided.writeX r remainder).advance
  let shiftedA := (reduced.writeX a (s.readX b)).advance
  let final := (shiftedA.writeX b remainder).advance
  have latch := exec_euclidean_latch s a b q r nextASrc nextBSrc route quotientLive remainderLive
    dividendQuotient divisorQuotient divisorRemainder remainderDividend nonzero
  have nextDivisor : final.readX b = Source.evalBin .urem 64 (s.readX a) (s.readX b) :=
    (read_advance_write_same shiftedA b remainder divisorLive).trans
      (Source.evalBin_urem_eq_umod 64 (s.readX a) (s.readX b) nonzero).symm
  refine ⟨final, latch, nextDivisor, ?_⟩
  rw [exec_cbz64, nextDivisor]

/-- The actual remainder in the next divisor register strictly decreases its unsigned rank. -/
theorem euclideanDivisor_decreases (a b : BitVec 64) (nonzero : b ≠ 0#64) :
    (a % b).toNat < b.toNat := by
  rw [BitVec.toNat_umod]
  exact Nat.mod_lt _ (BitVec.toNat_pos_of_ne_zero nonzero)

/-- Fuel counts only nonzero-divisor reductions. At zero, the phase has reached its exit. -/
def euclideanPhase : Nat → BitVec 64 → BitVec 64 → Option (BitVec 64)
  | 0, a, b => if b = 0 then some a else none
  | fuel + 1, a, b => if b = 0 then some a else euclideanPhase fuel b (a % b)

private theorem euclideanPhase_with_fuel (fuel : Nat) (a b : BitVec 64)
    (enough : b.toNat ≤ fuel) :
    ∃ result, euclideanPhase fuel a b = some result := by
  induction fuel generalizing a b with
  | zero =>
      have hb : b = 0#64 := BitVec.eq_of_toNat_eq (by simpa using enough)
      exact ⟨a, by simp [euclideanPhase, hb]⟩
  | succ fuel ih =>
      by_cases hb : b = 0#64
      · exact ⟨a, by simp [euclideanPhase, hb]⟩
      · have descent := euclideanDivisor_decreases a b hb
        obtain ⟨result, exits⟩ := ih b (a % b) (by omega)
        exact ⟨result, by simp [euclideanPhase, hb, exits]⟩

/-- Every finite-width Euclidean phase reaches the zero edge within its initial divisor rank.
    This supplies progress for a closed region whose steps match the checked latch. -/
theorem euclideanPhase_exits (a b : BitVec 64) :
    ∃ result, euclideanPhase b.toNat a b = some result :=
  euclideanPhase_with_fuel b.toNat a b (Nat.le_refl _)

end A64
end Trust
