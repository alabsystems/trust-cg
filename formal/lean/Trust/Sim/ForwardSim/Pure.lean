/-
  Sim.ForwardSim.Pure — the forward-simulation case for the PURE (register-only) opcodes.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHAT THIS MODULE IS.  `Sim.ForwardSim.*` proves one `forward_sim` case per source opcode
  class.  This file owns the PURE class: every lowered instruction that writes exactly ONE
  result GPR (plus EFLAGS) and touches NO memory — the ALU family (ADD/SUB/IMUL/AND/OR/XOR/
  NOT/NEG/shift-by-imm), the SETcc/CMOVcc comparison materializations, and the integer casts.

  SHAPE.  Mirrors `Sim.ForwardSim.Mem` exactly:
    * `PureTransition`  — the SOURCE-side shape of the transition (which name is defined, its
      width/assignment, the env/live bookkeeping, and the regalloc DISTINCTNESS facts: no other
      live value's register aliases the def register).  Machine-independent; owned by
      `Semantics.Source` + the regalloc validator.
    * `PureFrame`       — the MACHINE-side effect bounds of the lowered `step`: the def register
      holds a value whose low-w read-back denotes the source result (`dstDenotes` — discharged
      upstream by the `Cert.Arith`/`Cert.Compare` bv_decide value certs through the §4 read-back
      bridges below), the def carrier is CLEAN (`dstCarrier` — the producer zero-extends, e.g.
      MOVZX/SETcc), and the op writes no other GPR, no xmm, no memory byte (`execOtherReg`/
      `execXmms`/`execMem`), landing rip at the lowered successor (`pcAdvance`).
    * the four legs (`pure_value_leg`/`pure_carrier_leg`/`pure_mem_leg`/`pure_pc_leg`) are then
      assembled into the uniform `InstrCert` (`pureInstrCert`) and threaded through the ONE
      recombination bridge (`matchStep_exists` = `cert_reestablishes_R`) by `forward_sim_pure`.

  NO `sorry` anywhere in this module: the frame case-analysis is total over `Loc`/`ValKind`
  (the i128 register-pair arm is covered because `PureTransition` carries PAIR distinctness,
  the hypothesis the analogous `Mem` load arm was missing), and the worked value/carrier
  anchors in §4 are `bv_decide`/`lowerAddNarrow_correct`/`lowerCmp_correct` applications.
  ─────────────────────────────────────────────────────────────────────────────────────────────
-/
import Trust.Model
import Trust.Cert.Obligation
import Trust.Sim.Match
import Trust.Cert.Arith
import Trust.Cert.Compare

namespace Trust
namespace Sim
namespace ForwardSim

open Trust
open Trust.Sim

/-! ###########################################################################################
    ## 0.  Width round-trip + memory-congruence helpers.
    ######################################################################################### -/

/-- Zero-extend to the full 64-bit carrier, then read the low `w` bits back: the identity.
    This is the generic-width round-trip every clean-carrier producer (MOVZX, SETcc, zext-load)
    rests on; the concrete widths are `bv_decide`-anchored in `Sim.ForwardSim.Mem` §7. -/
theorem setWidth64_truncate_roundtrip (w : Nat) (hw : w ≤ 64) (b : BitVec w) :
    (BitVec.setWidth 64 b).truncate w = b := by
  simp only [BitVec.truncate_eq_setWidth]
  rw [BitVec.setWidth_setWidth_of_le _ hw, BitVec.setWidth_eq]

/-- `readBytes` reads the state only through `.mem`: two states with pointwise-equal memory
    read equal bytes.  PROVEN by induction (no `sorry`) — the engine that lets a spill-resident
    value's denotation ride across a memory-untouching pure op. -/
theorem readBytes_congr_of_mem_eq {m' m : MachState}
    (hmem : ∀ a, m'.mem a = m.mem a) :
    ∀ (n : Nat) (a : BitVec 64), readBytes m' a n = readBytes m a n := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ k ih =>
      intro a
      simp only [readBytes_succ, hmem, ih (a + 1)]

/-! ###########################################################################################
    ## 1.  The source-transition SHAPE and the machine-effect FRAME for a pure op.

    Exactly as in `Mem`: rather than `sorry` a projection of the abstract `srcStep`, the
    forward-sim case is GIVEN the transition's observable shape as a structured hypothesis
    (proved by `Semantics.Source` + the regalloc validator at the instantiation site).
    ######################################################################################### -/

/-- The shape of a pure source transition `s ⇒ s'`: one SSA name `vDst` is freshly defined
    into a width-`w` GPR carrier; every OTHER live value of `s'` is a live value of `s` with
    the same source value; and the regalloc validator's DISTINCTNESS facts — no other live
    value's `.reg`/`.pair` assignment aliases the def register `rDst`.  (Spill/xmm-resident
    values need no distinctness: a pure op touches neither memory nor xmm lanes.) -/
structure PureTransition (lay : Layout) (s s' : SrcState) where
  /-- the result SSA name defined by the op. -/
  vDst  : VName
  /-- result carrier width (bits); its assignment is the GPR `rDst`. -/
  w     : Nat
  hw    : w ≤ 64
  rDst  : GPR
  hkind : lay.kind vDst = ValKind.int w hw
  hasgn : lay.asgn vDst = Loc.reg rDst
  /-- `vDst` is live at `s'`. -/
  liveDst : Live s' vDst
  /-- every OTHER live value of `s'` is a pre-existing live value of `s`, same source value. -/
  envOther : ∀ v, Live s' v → v ≠ vDst → (Live s v ∧ s'.env v = s.env v)
  /-- regalloc distinctness: no other live value's assigned GPR is the def register. -/
  otherRegDistinct : ∀ v, Live s' v → v ≠ vDst → ∀ r, lay.asgn v = Loc.reg r → r ≠ rDst
  /-- regalloc distinctness for i128 register PAIRS: neither limb aliases the def register.
      (The hypothesis whose absence forced the `Mem` load pair-arm `sorry`; carried here so
      the pure case is total.) -/
  otherPairDistinct : ∀ v, Live s' v → v ≠ vDst → ∀ lo hi, lay.asgn v = Loc.pair lo hi →
                        lo ≠ rDst ∧ hi ≠ rDst

/-- The machine-side effect bounds of the lowered pure `step`, relative to a `PureTransition`.
    `dstDenotes`/`dstCarrier` are discharged by the per-opcode `Cert.*` bv_decide value/carrier
    certs (through the §4 read-back bridges); the `exec*` fields are the definitional frame of
    the emitted instruction (a register-only ALU op / SETcc / CMOV writes one GPR + EFLAGS);
    `pcAdvance` is the straight-line CFG fact (fall-through to the lowered successor). -/
structure PureFrame (lay : Layout) (step : LoweredStep) (s s' : SrcState)
    (tr : PureTransition lay s s') where
  /-- VALUE: the low-`w` read-back of the written def register denotes the source result. -/
  dstDenotes : ∀ m, R lay s m →
      Val.int tr.w tr.hw (((step.exec m).regs tr.rDst).truncate tr.w) = s'.env tr.vDst
  /-- CARRIER: the def register is width-faithful (canonically zero-extended low-`w` value). -/
  dstCarrier : ∀ m, R lay s m →
      (step.exec m).regs tr.rDst
        = (((step.exec m).regs tr.rDst).truncate tr.w).setWidth 64
  /-- a pure op writes NO other GPR. -/
  execOtherReg : ∀ m (r : GPR), r ≠ tr.rDst → (step.exec m).regs r = m.regs r
  /-- a pure op writes NO xmm lane. -/
  execXmms : ∀ m (x : XMM), (step.exec m).xmms x = m.xmms x
  /-- a pure op writes NO memory byte. -/
  execMem : ∀ m (a : BitVec 64), (step.exec m).mem a = m.mem a
  /-- straight-line fall-through: rip lands at the lowered successor block of `s'`. -/
  pcAdvance : ∀ m, R lay s m → (step.exec m).rip = lay.entryAddr (lay.lowerOf s'.pc)

/-! ###########################################################################################
    ## 2.  The four cert legs.
    ######################################################################################### -/

/-- PURE `value` leg: every value live at `s'` denotes its source value after the step.
    The def is `dstDenotes`; every OTHER value is framed — reg/pair via the regalloc
    distinctness + `execOtherReg`, xmm via `execXmms`, spill via the memory congruence.
    Total over `Loc`/`ValKind`; NO `sorry`. -/
theorem pure_value_leg
    {lay : Layout} {step : LoweredStep} {s s' : SrcState} {m : MachState}
    (tr : PureTransition lay s s') (fr : PureFrame lay step s s' tr)
    (hR : R lay s m) :
    ∀ v, Live s' v →
      denoteLoc (step.exec m) (lay.asgn v) (lay.kind v) = s'.env v := by
  intro v hv'
  by_cases hvd : v = tr.vDst
  · -- the freshly-defined result: read the low-w carrier back out of the def register.
    subst hvd
    rw [tr.hkind, tr.hasgn, denote_int_reg]
    exact fr.dstDenotes m hR
  · -- an untouched live value: its denotation transports from the incoming `R.realize`.
    obtain ⟨hvLive, hEnv⟩ := tr.envOther v hv' hvd
    rw [hEnv]
    have hold := hR.realize v hvLive
    have hread : ∀ (n : Nat) (a : BitVec 64),
        readBytes (step.exec m) a n = readBytes m a n :=
      readBytes_congr_of_mem_eq (fr.execMem m)
    cases hasgn : lay.asgn v with
    | reg r =>
        have hrne : r ≠ tr.rDst := tr.otherRegDistinct v hv' hvd r hasgn
        cases hkind : lay.kind v with
        | int w h => rw [hasgn, hkind] at hold; simpa only [denote_int_reg, fr.execOtherReg m r hrne] using hold
        | i128    => rw [hasgn, hkind] at hold; simpa only [denote_i128_reg, fr.execOtherReg m r hrne] using hold
        | f64     => rw [hasgn, hkind] at hold; simp only [denoteLoc, fr.execOtherReg m r hrne] at hold ⊢; exact hold
        | f32     => rw [hasgn, hkind] at hold; simp only [denoteLoc, fr.execOtherReg m r hrne] at hold ⊢; exact hold
    | pair lo hi =>
        obtain ⟨hlo, hhi⟩ := tr.otherPairDistinct v hv' hvd lo hi hasgn
        cases hkind : lay.kind v with
        | int w h => rw [hasgn, hkind] at hold; simpa only [denote_int_pair, fr.execOtherReg m lo hlo] using hold
        | i128    => rw [hasgn, hkind] at hold; simpa only [denote_i128_pair, fr.execOtherReg m lo hlo, fr.execOtherReg m hi hhi] using hold
        | f64     => rw [hasgn, hkind] at hold; simp only [denoteLoc, fr.execOtherReg m lo hlo] at hold ⊢; exact hold
        | f32     => rw [hasgn, hkind] at hold; simp only [denoteLoc, fr.execOtherReg m lo hlo] at hold ⊢; exact hold
    | xmm x =>
        cases hkind : lay.kind v with
        | int w h => rw [hasgn, hkind] at hold; simpa only [denote_int_xmm, fr.execXmms m x] using hold
        | i128    => rw [hasgn, hkind] at hold; simpa only [denote_i128_xmm, fr.execXmms m x] using hold
        | f64     => rw [hasgn, hkind] at hold; simpa only [denote_f64_xmm, fr.execXmms m x] using hold
        | f32     => rw [hasgn, hkind] at hold; simp only [denoteLoc, fr.execXmms m x] at hold ⊢; exact hold
    | spill sl =>
        cases hkind : lay.kind v with
        | int w h => rw [hasgn, hkind] at hold; simp only [denote_int_spill, hread]; exact hold
        | i128    => rw [hasgn, hkind] at hold; simp only [denote_i128_spill, hread]; exact hold
        | f64     => rw [hasgn, hkind] at hold; simp only [denoteLoc, hread]; exact hold
        | f32     => rw [hasgn, hkind] at hold; simp only [denoteLoc, hread]; exact hold

/-- PURE `carrierOk` leg: width-faithfulness re-established at `s'`.  The def register is
    faithful by `dstCarrier` (the producer zero-extends); every OTHER live narrow reg is
    bit-for-bit unchanged (`execOtherReg` under the regalloc distinctness) and transports
    from the incoming `carrier` conjunct. -/
theorem pure_carrier_leg
    {lay : Layout} {step : LoweredStep} {s s' : SrcState} {m : MachState}
    (tr : PureTransition lay s s') (fr : PureFrame lay step s s' tr)
    (hR : R lay s m) :
    WidthFaithful lay s' (step.exec m) := by
  intro v hv'
  by_cases hvd : v = tr.vDst
  · subst hvd
    simp only [tr.hkind, tr.hasgn]
    exact fr.dstCarrier m hR
  · obtain ⟨hvLive, _⟩ := tr.envOther v hv' hvd
    have hold := hR.carrier v hvLive
    cases hk : lay.kind v <;> cases ha : lay.asgn v <;>
      first
        | trivial
        | · rename_i w hw r
            have hrne : r ≠ tr.rDst := tr.otherRegDistinct v hv' hvd r ha
            simp only [hk, ha] at hold ⊢
            simpa only [fr.execOtherReg m r hrne] using hold

/-- PURE `memOk` leg: a pure op writes no memory byte and the source heap is unchanged
    (`hmemEq`), so off-frame agreement transports verbatim. -/
theorem pure_mem_leg
    {lay : Layout} {step : LoweredStep} {s s' : SrcState} {m : MachState}
    (tr : PureTransition lay s s') (fr : PureFrame lay step s s' tr)
    (hmemEq : ∀ a, s'.mem a = s.mem a) (hR : R lay s m) :
    agreeOn s'.mem (step.exec m) (lay.nonFrame) := by
  intro a ha
  rw [hmemEq a, fr.execMem m a]
  exact hR.memAgree a ha

/-- PURE `pcOk` leg: rip lands at the lowered successor — directly the `pcAdvance` CFG fact. -/
theorem pure_pc_leg
    {lay : Layout} {step : LoweredStep} {s s' : SrcState} {m : MachState}
    (tr : PureTransition lay s s') (fr : PureFrame lay step s s' tr)
    (hR : R lay s m) :
    (step.exec m).rip = lay.entryAddr (lay.lowerOf s'.pc) :=
  fr.pcAdvance m hR

/-! ###########################################################################################
    ## 3.  Assembly: the `InstrCert` and the forward-sim case.
    ######################################################################################### -/

/-- Assemble the PURE `InstrCert`.  Every leg is one of the proven lemmas above; the clobber
    leg is the regalloc-validator bound `clob`, supplied by the caller (it is the ONLY leg that
    speaks about `clobberOf`).  NO `sorry` — pure assembly. -/
def pureInstrCert
    {lay : Layout} {step : LoweredStep} {s s' : SrcState}
    (tr : PureTransition lay s s') (fr : PureFrame lay step s s' tr)
    (clob : ∀ m, R lay s m → Preserves (clobberOf step) m (step.exec m))
    (hmemEq : ∀ a, s'.mem a = s.mem a) :
    InstrCert lay step s s' where
  value     := fun _ hR => pure_value_leg tr fr hR
  clobber   := clob
  carrierOk := fun _ hR => pure_carrier_leg tr fr hR
  memOk     := fun _ hR => pure_mem_leg tr fr hmemEq hR
  pcOk      := fun _ hR => pure_pc_leg tr fr hR

/-- FORWARD-SIM, PURE case.  From a matching state, the lowered pure instruction's real
    `x86StepPlus` lands in a state re-matched at `s'` — via the ONE recombination bridge
    (`matchStep_exists` = `cert_reestablishes_R`).  This is the theorem
    `MetaTheorem.CompileRefines.forward_sim` dispatches to for `OpKind.pure`. -/
theorem forward_sim_pure
    {lay : Layout} {step : LoweredStep} {s s' : SrcState} {m : MachState}
    (tr : PureTransition lay s s') (fr : PureFrame lay step s s' tr)
    (clob : ∀ m, R lay s m → Preserves (clobberOf step) m (step.exec m))
    (hmemEq : ∀ a, s'.mem a = s.mem a)
    (hR : R lay s m) :
    ∃ m', x86StepPlus m step.event m' ∧ R lay s' m' :=
  matchStep_exists (pureInstrCert tr fr clob hmemEq) hR

/-! ###########################################################################################
    ## 4.  Worked read-back bridges + `bv_decide` anchors (the `dstDenotes` suppliers).

    The `Cert.Arith`/`Cert.Compare` value certs are pure-BitVec facts; these bridges restate
    them in the `denoteLoc` form `PureFrame.dstDenotes` consumes, and pin the concrete-width
    `bv_decide` obligations, so the wiring from a per-opcode cert into a `PureFrame` is
    exhibited rather than asserted.
    ######################################################################################### -/

/-- Narrow ADD at width 32 (the canonical worked ALU anchor): the full-64 ADD's low 32 bits
    equal the width-32 sum of the operands' low 32 bits.  `bv_decide`. -/
theorem addNarrow32_value (ra rb : BitVec 64) :
    (ra + rb).truncate 32 = ra.truncate 32 + rb.truncate 32 := by
  bv_decide

/-- READ-BACK bridge, ADD: if the def register holds the full-width ADD of the operand
    registers, its narrow read-back denotes the width-`w` `addSpec` — `Cert.Arith`'s
    generic-width value cert in `denoteLoc` form. -/
theorem add_resWritten_bridge
    (m' : MachState) (r ra rb : GPR) (w : Nat) (hw : w ≤ 64)
    (hres : m'.regs r = Cert.Arith.lowerAddNarrow (m'.regs ra) (m'.regs rb)) :
    denoteLoc m' (.reg r) (.int w hw)
      = .int w hw (Cert.Arith.addSpec w (m'.regs ra) (m'.regs rb)) := by
  rw [denote_int_reg, hres]
  congr 1
  exact Cert.Arith.lowerAddNarrow_correct w hw _ _

/-- The three-way-compare value cert (re-export of `Cert.Compare.lowerCmp_correct` under the
    ForwardSim namespace, the name the roadmap tracks): the differenced-SETcc lowering equals
    the `Ordering` spec at both signednesses. -/
theorem lowerCmp_correct (signed : Bool) (a b : BitVec 64) :
    Cert.Compare.lowerCmp signed a b = Cert.Compare.cmpSpec signed a b :=
  Cert.Compare.lowerCmp_correct signed a b

/-- READ-BACK bridge, CMP→Ordering: if the def register holds the (zero-extended) differenced
    SETcc byte, its i8 read-back denotes the `cmpSpec` ordering byte. -/
theorem cmp_resWritten_bridge
    (m' : MachState) (r ra rb : GPR) (signed : Bool)
    (hres : m'.regs r
      = BitVec.setWidth 64 (Cert.Compare.lowerCmp signed (m'.regs ra) (m'.regs rb))) :
    denoteLoc m' (.reg r) (.int 8 (by omega))
      = .int 8 (by omega) (Cert.Compare.cmpSpec signed (m'.regs ra) (m'.regs rb)) := by
  rw [denote_int_reg, hres, Cert.Compare.lowerCmp_correct]
  congr 1
  exact setWidth64_truncate_roundtrip 8 (by omega) _

/-- Integer cast anchor, zext 8→32 (MOVZX): the value leg — the zero-extended byte's low 32
    bits are the width-32 zero extension of the byte.  `bv_decide`. -/
theorem castZext8to32_value (x : BitVec 64) :
    (BitVec.setWidth 64 (x.truncate 8)).truncate 32
      = BitVec.setWidth 32 (x.truncate 8) := by
  bv_decide

/-- Integer cast anchor, zext 8→32: the carrier leg — the MOVZX-produced register is CLEAN
    (width-faithful at the 32-bit result width), so `PureFrame.dstCarrier` is dischargeable
    for the cast producer.  `bv_decide`. -/
theorem castZext8to32_carrier_clean (x : BitVec 64) :
    BitVec.setWidth 64 (x.truncate 8)
      = ((BitVec.setWidth 64 (x.truncate 8)).truncate 32).setWidth 64 := by
  bv_decide

end ForwardSim
end Sim
end Trust
