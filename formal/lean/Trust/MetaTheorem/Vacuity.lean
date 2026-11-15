/-
  MetaTheorem.Vacuity — what the linked definitions of `srcStep` and `x86Step` imply about the
  forward-simulation development, kernel-checked.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  The machine remains silent and partial; entry domains require real resident execution.
  The source is now indexed by an immutable program. A trap/return counterexample must
  fetch that operation and starts only in a running state; it cannot be attached to every
  program. ProgramWitness supplies a certified self-loop with a nonempty execution.

  The negative controls below retain the actual remaining defects: observable source
  operations have no machine counterpart, unrelated OpKinds need explicit event agreement,
  callee readiness cannot follow from an empty decrease premise, and unrestricted concurrent
  simulation fails for a thread whose program actually traps. The generic deterministic-run
  prefix theorem applies only with its explicit incompatible-trace hypotheses.

  Loader/layout binding, observable machine instructions and production compilation evidence
  remain open. These controls do not establish full compiler correctness.
-/
import Trust.Model
import Trust.Model.EncoderStep
import Trust.Cert.Obligation
import Trust.Sim.ForwardSim.Control
import Trust.Sim.ForwardSim.Call
import Trust.MetaTheorem.CompileRefines
import Trust.Concurrent.Atomics

namespace Trust
namespace MetaTheorem
namespace Vacuity

open Trust
open Trust.Model.Encoder
open Trust.Sim.ForwardSim

/-! ## 1.  The model machine is silent and partial. -/

/-- Every modelled instruction is silent. -/
theorem eventOf_tau (i : Instr) : eventOf i = Event.tau := by
  cases i <;> rfl

theorem x86Step_silent {m m' : MachState} {ev : Event} (h : x86Step m ev m') :
    ev = Event.tau := by
  obtain ⟨_, i, _, _, hev, _⟩ := h
  rw [hev, eventOf_tau]

theorem x86StepPlus_silent {m m' : MachState} {ev : Event} (h : x86StepPlus m ev m') :
    ev = Event.tau := by
  induction h with
  | single hs => exact x86Step_silent hs
  | cons _ _ ih => exact ih

theorem x86Run_silent {m m' : MachState} {evs : List Event} (h : x86Run m evs m') :
    ∀ e, e ∈ evs → e = Event.tau := by
  induction h with
  | nil => intro e he; simp at he
  | cons hs _ ih =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact x86Step_silent hs
      · exact ih e he

/-- Bytes whose first byte is zero never decode. -/
theorem decode_zero_head (b c : UInt8) (rest : List UInt8) :
    decode ((0 : UInt8) :: b :: c :: rest) = none := by
  simp [decode, u8ToBv]

/-- The model machine takes no step from a state whose memory is all zero bytes. -/
theorem x86Step_stuck_on_zero_memory {ev : Event} {m' : MachState} :
    ¬ x86Step (filledMachState 0) ev m' := by
  rintro ⟨bs, i, hbytes, hdec, _, _⟩
  match bs, hbytes, hdec with
  | [], _, h => simp [decode] at h
  | [_], _, h => simp [decode] at h
  | [_, _], _, h => simp [decode] at h
  | a :: b :: c :: rest, hb, h =>
      have h0 : (0 : BitVec 8) = BitVec.ofNat 8 a.toNat := hb.1
      have ha : a = 0 := by
        apply UInt8.toNat.inj
        have hlt : a.toNat < 2 ^ 8 := a.toNat_lt
        have := congrArg BitVec.toNat h0
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
        simpa using this.symm
      subst ha
      rw [decode_zero_head] at h
      cases h

/-- Even an inhabited guarded step must reject the all-zero, non-decoding memory. -/
theorem loweredStep_zero_memory_not_ready (step : LoweredStep) :
    ¬ step.entry (filledMachState 0) := by
  intro hentry
  cases step.runs (filledMachState 0) hentry with
  | single hs => exact x86Step_stuck_on_zero_memory hs
  | cons hs _ => exact x86Step_stuck_on_zero_memory hs

/-- A callee contract cannot admit the all-zero, non-decoding memory either. -/
theorem calleeContract_zero_memory_not_ready
    {lay : Layout} {s s' : SrcState} {tr : CallTransition lay s s'}
    (cc : CalleeContract lay s s' tr) : ¬ cc.entry (filledMachState 0) :=
  loweredStep_zero_memory_not_ready (callStep tr cc)

/-- An inhabited execution domain makes the still-silent instruction model's event concrete. -/
theorem loweredStep_event_tau (step : LoweredStep) : step.event = Event.tau := by
  obtain ⟨m, hm⟩ := step.entry_nonempty
  exact x86StepPlus_silent (step.runs m hm)

/-- Every current `OpKind` is silent. This no longer uses an empty step type. -/
theorem opKind_event_tau {lay : Layout} {s s' : SrcState} (ok : OpKind lay s s') :
    ok.event = Event.tau := by
  cases ok with
  | pure step _ _ _ _ _ => exact loweredStep_event_tau step
  | load step _ _ _ _ _ _ _ _ _ _ => exact loweredStep_event_tau step
  | store step _ _ _ _ _ _ => exact loweredStep_event_tau step
  | condBr _ _ _ _ _ => rfl
  | call _ _ _ _ _ => rfl

/-- Only the machine's empty observable trace is a behaviour of `x86Sem P`. -/
theorem macBeh_silent (P : Program) {obs : List Event} (h : (x86Sem P).behaviours obs) :
    obs = [] := by
  obtain ⟨_, evsM, hrun, hobs⟩ := h
  rw [← hobs]
  exact observable_taus (x86Run_silent hrun)

/-! ## 2. Fetched observable operations remain unsupported by the silent machine. -/

theorem srcStep_trap (code : Source.Program) (s : SrcState)
    (hrun : s.halted = false) (hfetch : code.code s.pc = some .trap) :
    srcStep code s Event.trap { s with halted := true } :=
  Source.trap_step hrun hfetch

theorem srcStep_ret (code : Source.Program) (s : SrcState)
    (hrun : s.halted = false) (hfetch : code.code s.pc = some (.term .ret)) :
    srcStep code s Event.ret { s with halted := true } :=
  Source.ret_step hrun hfetch

theorem srcBeh_trap (P : Program) (hrun : P.entryS.halted = false)
    (hfetch : P.sourceCode.code P.entryS.pc = some .trap) :
    (srcSem P).behaviours [Event.trap] :=
  ⟨{ P.entryS with halted := true }, [Event.trap],
    srcRun.cons (srcStep_trap P.sourceCode P.entryS hrun hfetch) srcRun.nil, rfl⟩

theorem srcBeh_ret (P : Program) (hrun : P.entryS.halted = false)
    (hfetch : P.sourceCode.code P.entryS.pc = some (.term .ret)) :
    (srcSem P).behaviours [Event.ret] :=
  ⟨{ P.entryS with halted := true }, [Event.ret],
    srcRun.cons (srcStep_ret P.sourceCode P.entryS hrun hfetch) srcRun.nil, rfl⟩

/-! ## 3. A program that actually traps cannot be certified by silent instructions. -/

theorem certified_compile_unsatisfiable (P : Program)
    (hrun : P.entryS.halted = false)
    (hfetch : P.sourceCode.code P.entryS.pc = some .trap) : ¬ Certified_compile P := by
  intro hcert
  have hs : srcRun P.sourceCode P.entryS [Event.trap] { P.entryS with halted := true } :=
    srcRun.cons (srcStep_trap P.sourceCode P.entryS hrun hfetch) srcRun.nil
  cases hcert _ [Event.trap] hs with
  | cons _ ok hev _ =>
      rw [opKind_event_tau ok] at hev
      cases hev

/-- This applies to a fetched trap, not to every source program. -/
theorem not_refines (P : Program) (hrun : P.entryS.halted = false)
    (hfetch : P.sourceCode.code P.entryS.pc = some .trap) :
    ¬ Refines (x86Sem P) (srcSem P) := by
  intro h
  have := macBeh_silent P (h _ (srcBeh_trap P hrun hfetch))
  cases this

/-! ## 4. Deterministic runs cannot have incompatible observable prefixes. -/

/-- Runs of an arbitrary machine step relation. -/
inductive RunOf (step : MachState → Event → MachState → Prop) :
    MachState → List Event → MachState → Prop
  | nil  {m} : RunOf step m [] m
  | cons {m ev m₀ evs m'} : step m ev m₀ → RunOf step m₀ evs m' → RunOf step m (ev :: evs) m'

/-- From one state, the event lists of two runs of a deterministic relation are prefix-related. -/
theorem runOf_prefix {step : MachState → Event → MachState → Prop}
    (hdet : ∀ m ev₁ ev₂ m₁ m₂, step m ev₁ m₁ → step m ev₂ m₂ → ev₁ = ev₂ ∧ m₁ = m₂)
    {m m₁ m₂ : MachState} {e₁ e₂ : List Event}
    (h₁ : RunOf step m e₁ m₁) (h₂ : RunOf step m e₂ m₂) :
    e₁ <+: e₂ ∨ e₂ <+: e₁ := by
  induction h₁ generalizing e₂ m₂ with
  | nil => exact Or.inl (List.nil_prefix)
  | @cons m ev m₀ evs m' hs _ ih =>
      cases h₂ with
      | nil => exact Or.inr (List.nil_prefix)
      | cons hs' rest' =>
          obtain ⟨hev, hm⟩ := hdet _ _ _ _ _ hs hs'
          subst hev; subst hm
          rcases ih rest' with hp | hp
          · exact Or.inl ((List.prefix_cons_inj _).mpr hp)
          · exact Or.inr ((List.prefix_cons_inj _).mpr hp)

theorem observable_prefix {a b : List Event} (h : a <+: b) : observable a <+: observable b := by
  obtain ⟨t, rfl⟩ := h
  rw [observable_append]
  exact List.prefix_append _ _

/-- Conditional trace exclusion: both incompatible behaviours must be supplied explicitly.
    The program-indexed source no longer grants them to every program. -/
theorem forward_refines_impossible_of_determinism (P : Program)
    (step : MachState → Event → MachState → Prop)
    (hdet : ∀ m ev₁ ev₂ m₁ m₂, step m ev₁ m₁ → step m ev₂ m₂ → ev₁ = ev₂ ∧ m₁ = m₂)
    (m₀ : MachState)
    (htrap : (srcSem P).behaviours [Event.trap])
    (hret : (srcSem P).behaviours [Event.ret]) :
    ¬ (∀ obs, (srcSem P).behaviours obs →
        ∃ (mf : MachState) (evs : List Event), RunOf step m₀ evs mf ∧ observable evs = obs) := by
  intro h
  obtain ⟨_, e₁, r₁, o₁⟩ := h _ htrap
  obtain ⟨_, e₂, r₂, o₂⟩ := h _ hret
  rcases runOf_prefix hdet r₁ r₂ with hp | hp
  · have := observable_prefix hp
    rw [o₁, o₂] at this
    have := this.eq_of_length (by simp)
    cases this
  · have := observable_prefix hp
    rw [o₁, o₂] at this
    have := this.eq_of_length (by simp)
    cases this

/-! ## 5.  The former `sorry` sites. -/

/-- A layout and a source state at which `R` never holds (the live name `0` has kind `f64` but an
    integer value), used to build `OpKind` witnesses whose machine obligations are vacuous. -/
def unmatchedLayout : Layout :=
  { asgn := fun _ => Loc.reg GPR.rax, kind := fun _ => ValKind.f64, lowerOf := id
  , entryAddr := fun _ => 0, nonFrame := fun _ => False }

def unmatchedState : SrcState :=
  { env := fun _ => Val.int 64 (by omega) 0, mem := fun _ => 0, pc := 0, live := fun _ => True }

theorem unmatched_no_R (m : MachState) : ¬ R unmatchedLayout unmatchedState m := by
  intro hR
  have h := hR.realize 0 trivial
  simp [unmatchedLayout, unmatchedState, denoteLoc] at h

def unmatchedBranch : Control.BranchLayout unmatchedLayout :=
  { branchPc := 0, takenPc := 0, fallPc := 0, branchRip := 0, jccLen := 0, rel := 0
  , takenResolved := by simp [unmatchedLayout]
  , fallResolved := by simp [unmatchedLayout] }

/-- A `condBr` `OpKind` from `unmatchedState` to itself. -/
def unmatchedCondBr :
    OpKind unmatchedLayout unmatchedState { unmatchedState with halted := true } :=
  OpKind.condBr unmatchedBranch Cond.e
    (fun m hR => absurd hR (unmatched_no_R m))
    (fun m hR => absurd hR (unmatched_no_R m))
    (by simpa using decode_encode_jcc Cond.e unmatchedBranch.rel [])

/-- The former `sorry` `opKind_event_eq` claimed every `OpKind` for `s ⇒ s₀` has the event of every
    source step `s ⇒ s₀`. False: `OpKind` is indexed by the two states, not by the step, and
    a fetched trap connects these two states. The agreement the capstone needs is the `hev` field
    `CertRun` carries; no theorem replaces it. -/
theorem opKind_event_eq_refuted :
    ¬ (∀ (code : Source.Program) (lay : Layout) (s s₀ : SrcState) (ev : Event)
        (ok : OpKind lay s s₀), srcStep code s ev s₀ → ok.event = ev) := by
  intro h
  have := h ⟨fun _ => some .trap⟩ _ _ _ _ unmatchedCondBr
    (srcStep_trap ⟨fun _ => some .trap⟩ unmatchedState rfl rfl)
  cases this

/-- A layout with one live 64-bit name `0` in `rax`, and a call transition from a state to itself. -/
def oneNameLayout : Layout :=
  { asgn := fun _ => Loc.reg GPR.rax, kind := fun _ => ValKind.int 64 (by omega), lowerOf := id
  , entryAddr := fun _ => 0, nonFrame := fun _ => False }

def oneNameState : SrcState :=
  { env := fun _ => Val.int 64 (by omega) 0, mem := fun _ => 0, pc := 0, live := fun v => v = 0 }

def selfCall : CallTransition oneNameLayout oneNameState oneNameState :=
  { dst := 0, ret := RetShape.int64 64 (by omega)
  , kindDst := rfl, asgnDst := rfl
  , defOnly := fun _ h _ => h
  , dstLive := rfl
  , envOther := fun _ _ _ => rfl
  , crossingCalleeSaved := fun v hv hne => absurd hv hne
  , pcStep := rfl }

/-- An induction hypothesis alone cannot justify the old unrestricted callee-entry rule.
    The self-transition makes the decrease hypothesis empty, but it still cannot admit
    non-decoding memory. Restricted, residency-guarded contracts are not ruled out. -/
theorem unguarded_calleeContract_of_IH_refuted (μ : Layout → SrcState → Nat) :
    ¬ (∀ (lay : Layout) (s s' : SrcState) (tr : CallTransition lay s s'),
        (μ lay s' < μ lay s → ∀ (code : Source.Program) {lay' : Layout}, ForwardSimStmt code lay') →
          ∃ cc : CalleeContract lay s s' tr, cc.entry (filledMachState 0)) := by
  intro h
  obtain ⟨cc, hentry⟩ := h _ _ _ selfCall (fun hlt => absurd hlt (Nat.lt_irrefl _))
  exact calleeContract_zero_memory_not_ready cc hentry

/-- The former `sorry` `atomic_forward_sim`. False: the acting thread's source step can trap, and
    no concurrent machine step is observable. -/
theorem concMachPlus_silent {t : Concurrent.Tid} {cm cm' : Concurrent.ConcMach} {ev : Event}
    (h : Concurrent.ConcMachPlus t cm ev cm') : ev = Event.tau := by
  induction h with
  | single hs => exact x86Step_silent hs.localStep
  | cons _ _ ih => exact ih

def idleConcSrc : Concurrent.ConcSrc :=
  { threads := fun _ => oneNameState, shared := fun _ => 0 }

def idleConcMach : Concurrent.ConcMach :=
  { threads := fun _ => filledMachState 0
  , shared := fun _ => 0, buf := fun _ => [] }

theorem atomic_forward_sim_refuted :
    ¬ (∀ code lay, Concurrent.AtomicForwardSimStmt code lay) := by
  intro h
  have hRC : Concurrent.RC oneNameLayout idleConcSrc idleConcMach 0 :=
    { local_R :=
        { realize := by
            intro v hv
            subst hv
            simp [oneNameLayout, idleConcSrc, idleConcMach, Concurrent.ConcSrc.localize,
              Concurrent.ConcMach.localizeView, oneNameState, filledMachState, denoteLoc]
          carrier := by
            intro v _
            simp [oneNameLayout, Concurrent.ConcMach.localizeView, idleConcMach, filledMachState]
          memAgree := fun _ hf => hf.elim
          pcSync := by
            simp [oneNameLayout, Concurrent.ConcMach.localizeView, idleConcMach,
              filledMachState] }
      tso := fun _ _ => rfl }
  let code : Concurrent.Tid → Source.Program := fun _ => ⟨fun _ => some .trap⟩
  let stopped : Concurrent.ConcSrc :=
    { threads := fun t => if t = 0 then { oneNameState with halted := true } else oneNameState
    , shared := fun _ => 0 }
  have hstep : Concurrent.ConcSrcStep code idleConcSrc 0 Event.trap stopped :=
    { localStep := by
        simpa [code, idleConcSrc, stopped, Concurrent.ConcSrc.localize, oneNameState] using
          srcStep_trap (code 0) oneNameState rfl rfl
      others := by intro u hu; simp [stopped, idleConcSrc, hu] }
  obtain ⟨_, hrun, _⟩ := h code oneNameLayout hRC hstep
  cases concMachPlus_silent hrun

/-- The silent model's empty observable trace is also the source's empty run. This remains
    a silence fact, not the backward compiler theorem (ROADMAP item 6). -/
theorem machine_subset_source_vacuous (P : Program) :
    ∀ obs, (x86Sem P).behaviours obs → (srcSem P).behaviours obs := by
  intro obs h
  rw [macBeh_silent P h]
  exact ⟨P.entryS, [], srcRun.nil, rfl⟩

end Vacuity
end MetaTheorem
end Trust
