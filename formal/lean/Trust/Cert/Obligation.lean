/-
  Cert.Obligation — the per-instruction contract every Cert.* lemma produces and every
  Sim.ForwardSim.* case consumes UNIFORMLY. Imports the Model preamble.
  This is what `forward_sim`'s PURE-op case needs: a VALUE cert PLUS a clobber/frame bound,
  plus a re-establishment of carrier-faithfulness.
  Copyright 2026 Andrew Yates. Apache 2.0.
-/
import Trust.Model        -- the SINGLE-SOURCE-OF-TRUTH model preamble (R, Val, Loc, MachState …)

namespace Trust

/-- The semantic effect of executing one lowered source instruction on the machine:
    a function MachState → MachState (the composed effect of its ≥1 x86 ops) together
    with the event it emits. Produced by the Encoder/step lemmas. -/
structure LoweredStep where
  exec  : MachState → MachState
  event : Event
  /-- States in which the emitted code and its execution prerequisites are present. -/
  entry : MachState → Prop
  /-- The execution domain must contain a concrete state, not be `False`. -/
  entry_nonempty : ∃ m, entry m
  /-- Real machine execution is required on that explicitly admitted domain. -/
  runs  : ∀ m, entry m → x86StepPlus m event (exec m)

/-- The set of physical registers / slots an instruction is permitted to clobber.
    Comes from regalloc_validator (distinct live values → distinct regs) + call_clobber. -/
structure ClobberSet where
  gprs   : GPR → Prop
  xmms   : XMM → Prop
  flags  : Bool          -- whether EFLAGS may be written
  frame  : BitVec 64 → Prop   -- frame bytes (spill region) it may write

/-- `ClobberSet` is nonempty (the everything-clobbered set). Required so the opaque
    `clobberOf` below is a well-formed declaration (`opaque` needs a `Nonempty` codomain);
    carries no semantic commitment — `clobberOf`'s real value is validator-supplied. -/
instance : Inhabited ClobberSet :=
  ⟨{ gprs := fun _ => True, xmms := fun _ => True, flags := true, frame := fun _ => True }⟩

/-- `Preserves cl st m m'` : the step touched only what `cl` allows. This is the
    clobber/frame bound consumed alongside the value cert. -/
def Preserves (cl : ClobberSet) (m m' : MachState) : Prop :=
  (∀ r, ¬ cl.gprs r → m'.regs r = m.regs r) ∧
  (∀ x, ¬ cl.xmms x → m'.xmms x = m.xmms x) ∧
  (¬ cl.flags → m'.flags = m.flags) ∧
  (∀ a, ¬ cl.frame a → m'.mem a = m.mem a)

/-- The clobber set a given lowered step is allowed (supplied by regalloc_validator
    output threaded through the Layout / per-block metadata). Opaque here; the
    validator-backed instance is provided in Sim.Match.
    (Declared BEFORE `InstrCert` because the `clobber` field references it.) -/
opaque clobberOf : LoweredStep → ClobberSet

/-!
  ## InstrCert — the uniform obligation typeclass/structure.

  Producers in this tree: `Cert.Arith.BinOpI128Site.toInstrCert`,
  `Cert.Compare.CmpSite.toInstrCert`, `Sim.ForwardSim.pureInstrCert` (ForwardSim/Pure.lean),
  `Sim.ForwardSim.Mem.load_instrCert` / `Sim.ForwardSim.Mem.store_instrCert`, and
  `Sim.ForwardSim.callInstrCert` (ForwardSim/Call.lean). `Cert.BitManip` supplies standalone
  SWAR value equations, while `Cert.Niche` is an empty placeholder; neither produces an
  `InstrCert`
  (docs/aarch64-completion-audit-2026-09-17.md, gap X-LEAN-P11).
  A forward_sim case that consumes an `InstrCert` for its lowered step gets, in one shot:
    (1) `value`     — the bv_decide-discharged VALUE correctness (post-state denotes the src result),
    (2) `clobber`   — the regalloc/frame bound (Preserves),
    (3) `carrierOk` — re-establishment of WidthFaithful for the (possibly narrow) result,
    (4) `memOk`     — memory non-interference preserved (trivial for pure ops; real for Mem),
  for the *specific* source transition (s ⇒ s') this instruction implements.
-/
structure InstrCert
    (lay : Layout) (step : LoweredStep)
    (s s' : SrcState)        -- the source transition this instruction realizes
    : Prop where
  /-- Establish the lowered code's execution prerequisites from the incoming relation. -/
  entryReady : ∀ m, R lay s m → step.entry m
  /-- VALUE cert (the bv_decide core): after `step.exec`, the relation's `realize`
      conjunct holds for s'. Discharged per-opcode via bv_decide on width-bounded BitVecs.
      Shapes reused: `lowerAdd_correct`, `lowerCmp_correct`. -/
  value     : ∀ m, R lay s m → ∀ v, Live s' v →
                denoteLoc (step.exec m) (lay.asgn v) (lay.kind v) = s'.env v
  /-- CLOBBER / FRAME bound: the step only writes registers/flags/frame the validator allows. -/
  clobber   : ∀ m, R lay s m → Preserves (clobberOf step) m (step.exec m)
  /-- CARRIER re-extension: WidthFaithful re-established at s'. Where the producer left a
      dirty narrow high carrier, this carries the obligation that a re-extend was emitted
      (the carrier_hygiene consumer site). -/
  carrierOk : ∀ m, R lay s m → WidthFaithful lay s' (step.exec m)
  /-- MEMORY non-interference: off-frame agreement preserved through the step. -/
  memOk     : ∀ m, R lay s m → agreeOn s'.mem (step.exec m) (lay.nonFrame)
  /-- PC advance: the machine rip lands at the lowered successor block of s'. -/
  pcOk      : ∀ m, R lay s m → (step.exec m).rip = lay.entryAddr (lay.lowerOf s'.pc)

/-!
  ## The bridge lemma every forward_sim case calls.

  Given an `InstrCert` for the transition AND a starting `R`, reassemble `R` at s'.
  This is the ONE place the four conjuncts are recombined, so each Cert.* author only
  proves the four component facts (value/clobber/carrier/mem) and never re-touches R.
  PROOF OBLIGATION (in Sim.Match): destruct R, apply the four cert fields, rebuild R.
  No `sorry` here — it must genuinely combine the components, not assume the goal. -/
theorem cert_reestablishes_R
    {lay : Layout} {step : LoweredStep} {s s' : SrcState} {m : MachState}
    (cert : InstrCert lay step s s') (hR : R lay s m) :
    x86StepPlus m step.event (step.exec m) ∧ R lay s' (step.exec m) :=
  ⟨ step.runs m (cert.entryReady m hR)
  , { realize  := cert.value  m hR
    , carrier  := cert.carrierOk m hR
    , memAgree := cert.memOk    m hR
    , pcSync   := cert.pcOk     m hR } ⟩

/-!
  ## CertProvider typeclass — the intended uniform dispatch from opcode to its InstrCert.

  No module in this tree registers a `CertProvider` instance, so nothing dispatches through
  this class. The producers listed above build each `InstrCert` directly: the `Cert.Compare`
  one is passed to `cert_reestablishes_R` directly, the ForwardSim Pure/Mem/Call ones through
  `Sim.matchStep_exists`, and `Cert.Arith.BinOpI128Site.toInstrCert` has no consumer here.
  `Cert.BitManip` supplies value equations but no provider; `Cert.Niche` remains an empty
  placeholder (X-LEAN-P11). The class is kept as the intended dispatch shape. -/
class CertProvider (OpTag : Type) where
  /-- given the static opcode tag and the source transition it implements, build the cert. -/
  cert : OpTag → (lay : Layout) → (step : LoweredStep) → (s s' : SrcState) →
         InstrCert lay step s s'

end Trust
