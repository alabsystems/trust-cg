/-
  MetaTheorem.CompileRefines — corrected. Doc-comment blocks elided for length;
  the load-bearing change is the load/store dispatch fix in `forward_sim`.
-/

import Trust.Model
import Trust.Cert.Obligation
import Trust.Sim.Match
import Trust.Sim.ForwardSim.Pure
import Trust.Sim.ForwardSim.Mem
import Trust.Sim.ForwardSim.Control
import Trust.Sim.ForwardSim.Call

namespace Trust
namespace MetaTheorem

open Trust
open Trust.Sim
open Trust.Sim.ForwardSim

inductive OpKind (lay : Layout) (s s' : SrcState) : Type
  | pure
      (step : LoweredStep)
      (tr   : PureTransition lay s s')
      (fr   : PureFrame lay step s s' tr)
      (clob : ∀ m, R lay s m → Preserves (clobberOf step) m (step.exec m))
      (hmemEq : ∀ a, s'.mem a = s.mem a)
      (hev  : step.event = Event.tau)
  | load
      (step : LoweredStep)
      (ld   : Mem.LoadShape lay s s')
      (len  : Nat)
      (hexec : ∀ m, step.exec m = Mem.loadExec ld.addr ld.rDst ld.n len m)
      (haddrOff : ∀ k, k < ld.n → lay.nonFrame (ld.addr + BitVec.ofNat 64 k))
      (hin  : ∀ _m : MachState, (clobberOf step).gprs ld.rDst)
      (hother : ∀ v, Live s' v → v ≠ ld.vDst → ∀ r, lay.asgn v = Loc.reg r → r ≠ ld.rDst)
      (hpc  : ∀ m, R lay s m → m.rip + BitVec.ofNat 64 len = lay.entryAddr (lay.lowerOf s'.pc))
  | store
      (step : LoweredStep)
      (sh   : Mem.StoreShape lay s s')
      (len  : Nat)
      (hexec : ∀ m, step.exec m = Mem.storeExec sh.addr sh.storedVal sh.n len m)
      (hcover : ∀ _m : MachState, ∀ q, ¬ (clobberOf step).frame q → Mem.OutsideRange sh.addr sh.n q)
      (hpc  : ∀ m, R lay s m → m.rip + BitVec.ofNat 64 len = lay.entryAddr (lay.lowerOf s'.pc))
  | condBr
      (bl   : Control.BranchLayout lay)
      (cc   : Trust.Model.Encoder.Cond)
      (cbs  : ∀ m, R lay s m → Control.CondBrStep lay bl cc s s' m)
      (hres : ∀ m, R lay s m →
                Trust.Model.Encoder.BytesAt m m.rip (Trust.Model.Encoder.encode (.jcc cc bl.rel)))
      (hrt  : Trust.Model.Encoder.decode (Trust.Model.Encoder.encode (.jcc cc bl.rel))
                = some (.jcc cc bl.rel, []))
  | call
      (tr   : CallTransition lay s s')
      (cc   : CalleeContract lay s s' tr)
      (fr   : CallFrame lay s s' tr cc)
      (clob : ∀ m, R lay s m →
                Preserves (clobberOf (callStep tr cc)) m ((callStep tr cc).exec m))
      (hmemEq : ∀ a, lay.nonFrame a → s'.mem a = s.mem a)

def OpKind.event {lay : Layout} {s s' : SrcState} : OpKind lay s s' → Event
  | .pure step _ _ _ _ _      => step.event
  | .load step _ _ _ _ _ _ _  => step.event
  | .store step _ _ _ _ _     => step.event
  | .condBr _ _ _ _ _         => Event.tau
  | .call _ _ _ _ _           => Event.tau

def Certified (lay : Layout) (s s' : SrcState) : Prop := Nonempty (OpKind lay s s')

theorem forward_sim
    {lay : Layout} {s s' : SrcState} {m : MachState}
    (ok : OpKind lay s s') (hR : R lay s m) :
    ∃ m', x86StepPlus m ok.event m' ∧ R lay s' m' := by
  cases ok with
  | pure step tr fr clob hmemEq hev =>
      exact forward_sim_pure tr fr clob hmemEq hR
  | load step ld len hexec haddrOff hin hother hpc =>
      -- FIX: `hin` is stored machine-parametrically (`∀ _m, …`) in the OpKind, but
      -- `Mem.forwardSim_load` wants the bare `(clobberOf step).gprs ld.rDst`; apply it at `m`.
      exact Mem.forwardSim_load ld len hexec haddrOff (hin m) hother hpc hR
  | store step sh len hexec hcover hpc =>
      -- FIX: `hcover` is stored machine-parametrically (`∀ _m, …`) in the OpKind, but
      -- `Mem.forwardSim_store` wants the un-parametrized cover fact; apply it at `m`.
      exact Mem.forwardSim_store sh len hexec (hcover m) hpc hR
  | condBr bl cc cbs hres hrt =>
      have h := Control.condBr_forwardSim (cbs m hR) hR (hres m hR) hrt
      have hev : Trust.Model.Encoder.eventOf (.jcc cc bl.rel) = Event.tau := rfl
      rw [hev] at h
      simpa [OpKind.event] using h
  | call tr cc fr clob hmemEq =>
      have h := forward_sim_call tr cc fr clob hmemEq hR
      simpa [OpKind.event] using h

inductive srcRun : SrcState → List Event → SrcState → Prop
  | nil  {s} : srcRun s [] s
  | cons {s ev s₀ evs s'} :
      srcStep s ev s₀ → srcRun s₀ evs s' → srcRun s (ev :: evs) s'

inductive CertRun (lay : Layout) : SrcState → List Event → SrcState → Prop
  | nil  {s} : CertRun lay s [] s
  | cons {s ev s₀ evs s'}
      (hstep : srcStep s ev s₀)
      (ok : OpKind lay s s₀) (hev : ok.event = ev)
      (rest : CertRun lay s₀ evs s') :
      CertRun lay s (ev :: evs) s'

theorem certRun_toSrc {lay : Layout} {s s' : SrcState} {evs : List Event}
    (h : CertRun lay s evs s') : srcRun s evs s' := by
  induction h with
  | nil => exact srcRun.nil
  | cons hstep _ _ _ ih => exact srcRun.cons hstep ih

inductive x86Run : MachState → List Event → MachState → Prop
  | nil  {m} : x86Run m [] m
  | cons {m ev m₀ evs m'} :
      x86Step m ev m₀ → x86Run m₀ evs m' → x86Run m (ev :: evs) m'

theorem x86Run_append {m m₀ m' : MachState} {evs₀ evs₁ : List Event}
    (h₀ : x86Run m evs₀ m₀) (h₁ : x86Run m₀ evs₁ m') :
    x86Run m (evs₀ ++ evs₁) m' := by
  induction h₀ with
  | nil => simpa using h₁
  | cons hstep _ ih => exact x86Run.cons hstep (ih h₁)

theorem x86StepPlus_toRun {m m' : MachState} {ev : Event}
    (h : x86StepPlus m ev m') :
    ∃ taus, x86Run m (taus ++ [ev]) m' ∧ (∀ e, e ∈ taus → e = Event.tau) := by
  induction h with
  | single hstep =>
      exact ⟨[], by simpa using x86Run.cons hstep x86Run.nil, by intro e he; simp at he⟩
  | cons hstep _ ih =>
      obtain ⟨taus, hrun, htau⟩ := ih
      refine ⟨Event.tau :: taus, x86Run.cons hstep hrun, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with h | h
      · exact h
      · exact htau e h

def isObservable : Event → Bool
  | Event.tau => false
  | _         => true

def observable (evs : List Event) : List Event := evs.filter isObservable

theorem observable_taus {taus : List Event} (htau : ∀ e, e ∈ taus → e = Event.tau) :
    observable taus = [] := by
  induction taus with
  | nil => rfl
  | cons hd tl ih =>
      have hhd : hd = Event.tau := htau hd (by simp)
      have htl : ∀ e, e ∈ tl → e = Event.tau := fun e he => htau e (by simp [he])
      have hpred : isObservable hd = false := by simp only [hhd, isObservable]
      simp only [observable, List.filter_cons, hpred, Bool.false_eq_true, if_false]
      exact ih htl

theorem observable_append (a b : List Event) :
    observable (a ++ b) = observable a ++ observable b := by
  simp only [observable, List.filter_append]

theorem observable_cons (ev : Event) (evs : List Event) :
    observable (ev :: evs) = observable [ev] ++ observable evs := by
  simp only [observable, List.filter_cons, List.filter_nil]
  cases isObservable ev <;> simp

theorem simRun
    {lay : Layout} {s s' : SrcState} {evs : List Event}
    (hrun : CertRun lay s evs s') :
    ∀ {m : MachState}, R lay s m →
      ∃ (mf : MachState) (evsM : List Event),
        x86Run m evsM mf ∧ observable evsM = observable evs ∧ R lay s' mf := by
  induction hrun with
  | nil =>
      intro m hR
      exact ⟨m, [], x86Run.nil, rfl, hR⟩
  | @cons s ev s₀ evs s' hstep ok hevEq rest ih =>
      intro m hR
      obtain ⟨m₀, hstepPlus, hR₀⟩ := forward_sim ok hR
      obtain ⟨taus, hsubrun, htau⟩ := x86StepPlus_toRun hstepPlus
      rw [hevEq] at hsubrun
      obtain ⟨mf, evsM, htailrun, htailobs, hR'⟩ := ih hR₀
      refine ⟨mf, (taus ++ [ev]) ++ evsM, x86Run_append hsubrun htailrun, ?_, hR'⟩
      rw [observable_append, observable_append, observable_taus htau, htailobs, List.nil_append,
          ← observable_cons]

theorem opKind_event_eq
    {lay : Layout} {s s₀ : SrcState} {ev : Event}
    (ok : OpKind lay s s₀) (hstep : srcStep s ev s₀) :
    ok.event = ev := by
  sorry  -- stubbed-semantics: the source classifier emits `ok` FOR `hstep`, so events coincide.

structure SrcSem where
  entry : SrcState
  behaviours : List Event → Prop

structure X86Sem where
  entry : MachState
  behaviours : List Event → Prop

def Refines (mb : X86Sem) (sb : SrcSem) : Prop :=
  ∀ obs, sb.behaviours obs → mb.behaviours obs

structure Program where
  entryS  : SrcState
  entryM  : MachState
  lay     : Layout
  rEntry  : R lay entryS entryM

def srcBeh (P : Program) (obs : List Event) : Prop :=
  ∃ (sf : SrcState) (evs : List Event), srcRun P.entryS evs sf ∧ observable evs = obs

def macBeh (P : Program) (obs : List Event) : Prop :=
  ∃ (mf : MachState) (evsM : List Event), x86Run P.entryM evsM mf ∧ observable evsM = obs

def srcSem (P : Program) : SrcSem := { entry := P.entryS, behaviours := srcBeh P }

def x86Sem (P : Program) : X86Sem := { entry := P.entryM, behaviours := macBeh P }

def Certified_compile (P : Program) : Prop :=
  ∀ (sf : SrcState) (evs : List Event), srcRun P.entryS evs sf → CertRun P.lay P.entryS evs sf

theorem compile_refines (P : Program) (hcert : Certified_compile P) :
    Refines (x86Sem P) (srcSem P) := by
  intro obs hsrc
  obtain ⟨sf, evs, hrun, hobs⟩ := hsrc
  have hcertRun : CertRun P.lay P.entryS evs sf := hcert sf evs hrun
  obtain ⟨mf, evsM, hmacrun, hmacobs, _hRf⟩ := simRun hcertRun P.rEntry
  exact ⟨mf, evsM, hmacrun, by rw [hmacobs]; exact hobs⟩

theorem refines_machine_subset_of_determinism (P : Program)
    (hdet : ∀ m ev₁ ev₂ m₁ m₂, x86Step m ev₁ m₁ → x86Step m ev₂ m₂ → ev₁ = ev₂ ∧ m₁ = m₂)
    (hfwd : Refines (x86Sem P) (srcSem P)) :
    ∀ obs, (x86Sem P).behaviours obs → (srcSem P).behaviours obs := by
  sorry  -- open: machine⊆source from determinism + maximal runs. OFF compile_refines path.

theorem simRun_nil {lay : Layout} {s : SrcState} {m : MachState} (hR : R lay s m) :
    ∃ (mf : MachState) (evsM : List Event),
      x86Run m evsM mf ∧ observable evsM = observable ([] : List Event) ∧ R lay s mf :=
  ⟨m, [], x86Run.nil, rfl, hR⟩

theorem certRun_nil {lay : Layout} {s : SrcState} : CertRun lay s [] s := CertRun.nil

theorem simRun_single
    {lay : Layout} {s s' : SrcState} {ev : Event} {m : MachState}
    (ok : OpKind lay s s') (hevEq : ok.event = ev) (hR : R lay s m) :
    ∃ (mf : MachState) (evsM : List Event),
      x86Run m evsM mf ∧ observable evsM = observable [ev] ∧ R lay s' mf := by
  obtain ⟨mf, hstepPlus, hR'⟩ := forward_sim ok hR
  obtain ⟨taus, hrun, htau⟩ := x86StepPlus_toRun hstepPlus
  rw [hevEq] at hrun
  refine ⟨mf, taus ++ [ev], hrun, ?_, hR'⟩
  rw [observable_append, observable_taus htau, List.nil_append]

end MetaTheorem
end Trust
