/-
  Sim.ForwardSim.Call — VERIFIED AS-IS (no corrections required).
  Reviewed against the Trust.Model preamble, Trust.Sim.Match signatures, the Pure/Mem
  templates, and the MetaTheorem.CompileRefines consumption site. The module is sound;
  the single `sorry` (CalleeContract_of_IH) is genuinely off the compile_refines path
  and does not smuggle the conclusion. The file is returned unchanged.
-/

import Trust.Model
import Trust.Cert.Obligation
import Trust.Sim.Match

namespace Trust
namespace Sim
namespace ForwardSim

open Trust
open Trust.Sim

def sysvIntArgRegs : List GPR := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

def sysvRetLo : GPR := .rax
def sysvRetHi : GPR := .rdx

def CalleeSaved : GPR → Prop
  | .rbx => True | .rsp => True | .rbp => True
  | .r12 => True | .r13 => True | .r14 => True | .r15 => True
  | _    => False

def CallerSaved (r : GPR) : Prop := ¬ CalleeSaved r

instance : DecidablePred CalleeSaved := by
  intro r
  unfold CalleeSaved
  cases r <;> infer_instance

instance : DecidablePred CallerSaved := fun r =>
  inferInstanceAs (Decidable (¬ CalleeSaved r))

theorem callerSaved_iff_not_calleeSaved (r : GPR) : CallerSaved r ↔ ¬ CalleeSaved r := Iff.rfl

theorem calleeSaved_caller_disjoint (r : GPR) : ¬ (CalleeSaved r ∧ CallerSaved r) := by
  intro ⟨h1, h2⟩; exact h2 h1

theorem rbx_calleeSaved : CalleeSaved .rbx := by decide
theorem r15_calleeSaved : CalleeSaved .r15 := by decide
theorem rax_callerSaved : CallerSaved .rax := by decide
theorem rdi_callerSaved : CallerSaved .rdi := by decide
theorem rdx_callerSaved : CallerSaved .rdx := by decide   -- volatile AND the return-hi reg

inductive RetShape
  | int64 (w : Nat) (hw : w ≤ 64)
  | i128
  deriving Repr

/-- The result `ValKind` a `RetShape` denotes.  Top-level (not an inline structure-field
    `match`) so that rewriting `tr.ret` reduces it by iota — an inline match inside
    `CallTransition` picks up the preceding field as a dependent scrutinee and becomes
    irreducible under `rw`/`simp`. -/
def RetShape.kindOf : RetShape → ValKind
  | .int64 w hw => .int w hw
  | .i128       => .i128

/-- The SysV return `Loc` a `RetShape` occupies (rax, or the rax/rdx pair for i128). -/
def RetShape.locOf : RetShape → Loc
  | .int64 _ _ => .reg sysvRetLo
  | .i128      => .pair sysvRetLo sysvRetHi

structure CallTransition (lay : Layout) (s s' : SrcState) where
  dst    : VName
  ret    : RetShape
  kindDst : lay.kind dst = ret.kindOf
  asgnDst : lay.asgn dst = ret.locOf
  defOnly : ∀ v, Live s' v → v ≠ dst → Live s v
  dstLive : Live s' dst
  envOther : ∀ v, Live s' v → v ≠ dst → s'.env v = s.env v
  crossingCalleeSaved : ∀ v, Live s' v → v ≠ dst →
                          ∀ r, lay.asgn v = .reg r → CalleeSaved r
  pcStep : lay.lowerOf s'.pc = lay.lowerOf s.pc

structure CalleeContract (lay : Layout) (s s' : SrcState)
    (tr : CallTransition lay s s') where
  runCallee : MachState → MachState
  runs      : ∀ m, x86StepPlus m Event.tau (runCallee m)
  retValue  : ∀ m, R lay s m →
                denoteLoc (runCallee m) (lay.asgn tr.dst) (lay.kind tr.dst) = s'.env tr.dst
  savedPreserved : ∀ m, R lay s m → ∀ r, CalleeSaved r → (runCallee m).regs r = m.regs r
  memPreserved : ∀ m, R lay s m → ∀ a, lay.nonFrame a → (runCallee m).mem a = m.mem a
  pcLanded  : ∀ m, R lay s m → (runCallee m).rip = lay.entryAddr (lay.lowerOf s'.pc)
  retCarrier : ∀ m, R lay s m →
                 match tr.ret with
                 | .int64 w _ => (runCallee m).regs sysvRetLo
                                   = ((runCallee m).regs sysvRetLo |>.truncate w).setWidth 64
                 | .i128      => True

structure CallFrame (lay : Layout) (s s' : SrcState)
    (tr : CallTransition lay s s') (cc : CalleeContract lay s s' tr) where
  othersInCalleeSaved : ∀ v, Live s' v → v ≠ tr.dst →
                          ∃ r ww, ∃ (hww : ww ≤ 64),
                            lay.asgn v = .reg r ∧ lay.kind v = .int ww hww ∧ CalleeSaved r

def callStep
    {lay : Layout} {s s' : SrcState}
    (tr : CallTransition lay s s') (cc : CalleeContract lay s s' tr) : LoweredStep where
  exec  := cc.runCallee
  event := Event.tau
  runs  := cc.runs

theorem call_value_leg
    {lay : Layout} {s s' : SrcState}
    (tr : CallTransition lay s s') (cc : CalleeContract lay s s' tr)
    (fr : CallFrame lay s s' tr cc) :
    ∀ m, R lay s m → ∀ v, Live s' v →
      denoteLoc (cc.runCallee m) (lay.asgn v) (lay.kind v) = s'.env v := by
  intro m hR v hv
  by_cases hvd : v = tr.dst
  · subst hvd
    exact cc.retValue m hR
  · obtain ⟨r, ww, hww, har, hkr, hcs⟩ := fr.othersInCalleeSaved v hv hvd
    have hpres : (cc.runCallee m).regs r = m.regs r := cc.savedPreserved m hR r hcs
    rw [hkr, har, denote_int_reg, hpres]
    have hold : denoteLoc m (lay.asgn v) (lay.kind v) = s.env v :=
      hR.realize v (tr.defOnly v hv hvd)
    rw [hkr, har, denote_int_reg] at hold
    rw [hold, tr.envOther v hv hvd]

theorem call_carrier_leg
    {lay : Layout} {s s' : SrcState}
    (tr : CallTransition lay s s') (cc : CalleeContract lay s s' tr)
    (fr : CallFrame lay s s' tr cc) :
    ∀ m, R lay s m → WidthFaithful lay s' (cc.runCallee m) := by
  intro m hR v hv
  by_cases hvd : v = tr.dst
  · subst hvd
    cases hret : tr.ret with
    | int64 w hw =>
      have hk : lay.kind tr.dst = .int w hw := by simp only [tr.kindDst, hret, RetShape.kindOf]
      have ha : lay.asgn tr.dst = .reg sysvRetLo := by simp only [tr.asgnDst, hret, RetShape.locOf]
      rw [hk, ha]
      show (cc.runCallee m).regs sysvRetLo
            = ((cc.runCallee m).regs sysvRetLo |>.truncate w).setWidth 64
      have hc := cc.retCarrier m hR
      rw [hret] at hc
      exact hc
    | i128 =>
      have hk : lay.kind tr.dst = .i128 := by simp only [tr.kindDst, hret, RetShape.kindOf]
      have ha : lay.asgn tr.dst = .pair sysvRetLo sysvRetHi := by simp only [tr.asgnDst, hret, RetShape.locOf]
      rw [hk, ha]
      trivial
  · obtain ⟨r, ww, hww, har, hkr, hcs⟩ := fr.othersInCalleeSaved v hv hvd
    rw [hkr, har]
    show (cc.runCallee m).regs r = (((cc.runCallee m).regs r).truncate ww).setWidth 64
    have hpres : (cc.runCallee m).regs r = m.regs r := cc.savedPreserved m hR r hcs
    have hold : (m.regs r) = ((m.regs r).truncate ww).setWidth 64 := by
      have hc := hR.carrier v (tr.defOnly v hv hvd)
      rw [hkr, har] at hc
      exact hc
    rw [hpres]; exact hold

theorem call_mem_leg
    {lay : Layout} {s s' : SrcState}
    (tr : CallTransition lay s s') (cc : CalleeContract lay s s' tr)
    (hmemEq : ∀ a, lay.nonFrame a → s'.mem a = s.mem a) :
    ∀ m, R lay s m → agreeOn s'.mem (cc.runCallee m) (lay.nonFrame) := by
  intro m hR a ha
  rw [hmemEq a ha, cc.memPreserved m hR a ha]
  exact hR.memAgree a ha

theorem call_pc_leg
    {lay : Layout} {s s' : SrcState}
    (tr : CallTransition lay s s') (cc : CalleeContract lay s s' tr) :
    ∀ m, R lay s m → (cc.runCallee m).rip = lay.entryAddr (lay.lowerOf s'.pc) :=
  cc.pcLanded

def callInstrCert
    {lay : Layout} {s s' : SrcState}
    (tr : CallTransition lay s s') (cc : CalleeContract lay s s' tr)
    (fr : CallFrame lay s s' tr cc)
    (clob : ∀ m, R lay s m → Preserves (clobberOf (callStep tr cc)) m ((callStep tr cc).exec m))
    (hmemEq : ∀ a, lay.nonFrame a → s'.mem a = s.mem a) :
    InstrCert lay (callStep tr cc) s s' where
  value     := call_value_leg tr cc fr
  clobber   := clob
  carrierOk := call_carrier_leg tr cc fr
  memOk     := call_mem_leg tr cc hmemEq
  pcOk      := call_pc_leg tr cc

theorem forward_sim_call
    {lay : Layout} {s s' : SrcState} {m : MachState}
    (tr : CallTransition lay s s') (cc : CalleeContract lay s s' tr)
    (fr : CallFrame lay s s' tr cc)
    (clob : ∀ m, R lay s m → Preserves (clobberOf (callStep tr cc)) m ((callStep tr cc).exec m))
    (hmemEq : ∀ a, lay.nonFrame a → s'.mem a = s.mem a)
    (hR : R lay s m) :
    ∃ m', x86StepPlus m Event.tau m' ∧ R lay s' m' := by
  have h := matchStep_exists (callInstrCert tr cc fr clob hmemEq) hR
  simpa [callStep] using h

opaque calleeMeasure (lay : Layout) (s : SrcState) : Nat

-- `CalleeContract` is a data-carrying `structure` (Type, not Prop), so this producer must be a
-- `def`, not a `theorem`. Its body is the SAME baseline `sorry` (off the `compile_refines` path).
noncomputable def CalleeContract_of_IH
    (lay : Layout) (s s' : SrcState) (tr : CallTransition lay s s')
    (ih : calleeMeasure lay s' < calleeMeasure lay s →
            ∀ {lay' : Layout}, ForwardSimStmt lay') :
    CalleeContract lay s s' tr := by
  sorry  -- open: well-founded call-graph descent — instantiate the callee's `compile_refines`
         -- (`ih`) over its entry→exit run, then extract the SysV ABI facts (return in rax/(rax,rdx),
         -- callee-saved rbx/rbp/r12..r15 restored by prologue/epilogue, off-frame mem preserved)
         -- from the callee's exit `R`, and package them as `CalleeContract`.  Needs the callee
         -- program object + the terminating call-graph measure, absent from this skeleton.

theorem retPair_readback (m : MachState) :
    denoteLoc m (.pair sysvRetLo sysvRetHi) .i128
      = .i128 ((m.regs sysvRetHi ++ m.regs sysvRetLo).cast (by omega)) := by
  simp only [denote_i128_pair]

theorem retHi_not_calleeSaved : ¬ CalleeSaved sysvRetHi := by decide

theorem retRegs_callerSaved : CallerSaved sysvRetLo ∧ CallerSaved sysvRetHi := by
  constructor <;> decide

end ForwardSim
end Sim
end Trust
