/-
  Model — the LINK STEP of trust-cg's Lean correctness development.

  `Model.Core` fixes the state vocabulary, `Semantics.Source` defines the source small-step
  relation `Source.SrcStep`, and `Model.Encoder` defines the x86-64 instruction set, its byte
  decoder and its transfer function `execInstr`. This module DEFINES the two step relations
  every simulation module programs against:

    * `srcStep code := Source.SrcStep code`, with a definitional link equation;
    * `x86Step` := fetch the bytes at `rip`, `decode` them to an `Instr`, run `execInstrChoice`, so
      `Model.Encoder.x86Step_decode` (in `Model.EncoderStep`) is a theorem.

  Both used to be `opaque` here, tied to their intended meanings by the explicit axioms
  `srcStep_spec` and `x86Step_decode`. Defining them removes those two axioms from the Lean
  trusted base; it does not remove the modelling assumption they carried. What is still
  trusted, and outside Lean, is that `Source.SrcStep` is the meaning of the trust-ir trust-cg
  compiles and that `decode`/`execInstr` are what an x86-64 processor does with those bytes.
  The encoder golden matrix (`Model.EncoderGolden`, `lean_encode_golden_binding`) binds the
  enumerated `encode` rows to the Rust emitter; nothing binds `execInstr` to x86-64 hardware.

  Consequences of the definitions are kernel-checked in `MetaTheorem.Vacuity`: the model machine
  never emits an observable event and is stuck wherever the bytes at `rip` do not decode, and the
  source fetches only from its immutable program. Programs that actually emit observables still
  cannot be matched by this silent machine. Read that module before citing any theorem that
  quantifies over `x86Step` or `srcStep`.
  Copyright 2026 Andrew Yates. Apache 2.0.
-/
import Trust.Model.Core
import Trust.Model.Encoder
import Trust.Semantics.Source

namespace Trust

/-! ## Small-step relations -/

/-- Execute the instruction selected by the immutable source program at `s.pc`. -/
def srcStep (code : Source.Program) : SrcState → Event → SrcState → Prop :=
  Source.SrcStep code

/-- Machine single small-step: `x86Step m ev m'` holds when some byte string `bs` is resident
    at `m.rip`, the model decoder reads it completely as `i`, and `m'` is one of
    `execInstrChoice i m` with the event `eventOf i`. SHR counts greater than one
    admit both undefined OF values. Bytes the decoder refuses take no step. -/
def x86Step (m : MachState) (ev : Event) (m' : MachState) : Prop :=
  ∃ (bs : List UInt8) (i : Model.Encoder.Instr),
    Model.Encoder.BytesAt m m.rip bs ∧ Model.Encoder.decode bs = some (i, []) ∧
      ev = Model.Encoder.eventOf i ∧
      ∃ undefinedOF, m' = Model.Encoder.execInstrChoice i m undefinedOF

/-- Transitive (one-or-more) machine step: a single source instruction lowers to ≥1 x86 ops. -/
inductive x86StepPlus : MachState → Event → MachState → Prop
  | single {m ev m'} : x86Step m ev m' → x86StepPlus m ev m'
  | cons   {m m₀ m'} : x86Step m .tau m₀ → x86StepPlus m₀ ev m' → x86StepPlus m ev m'

namespace Source

/-- The link-step equation that used to be the axiom `srcStep_spec`. It holds by definition. -/
theorem srcStep_spec (code : Program) : srcStep code = SrcStep code := rfl

end Source

/-! ## The top-level forward-simulation statement (proved in Sim.ForwardSim.* / MetaTheorem). -/

/-- forward_sim contract: from a matching state, any source step is matched by ≥1 machine
    steps landing in a re-matched state with the same observable event. -/
def ForwardSimStmt (code : Source.Program) (lay : Layout) : Prop :=
  ∀ {s m ev s'}, R lay s m → srcStep code s ev s' →
    ∃ m', x86StepPlus m ev m' ∧ R lay s' m'

end Trust
