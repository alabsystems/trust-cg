# Lean soundness boundary

The Lean development provides model-level evidence. It does not claim that it
proves the complete Rust compiler, all accepted trust-ir, all emitted bytes, or
real hardware execution end to end. Its forward capstone is conditional on
certificates for every run of a fixed source program. A resident self-loop now
inhabits that premise; observable source operations still have no counterpart
in the silent x86 oracle (see "What the linked definitions imply").

## Strength-reduction value recurrence

[`Trust/Optimization/StrengthReduction.lean`](Trust/Optimization/StrengthReduction.lean)
proves `edge_update` and `every_finite_edge_trace` for arbitrary bit widths,
initial values, strides, edge-specific steps and finite edge traces. Arithmetic
wraps modulo the register width. Zero, negative and differing steps need no
extra arithmetic premise. The theorem uses Lean's bitvector distributivity;
its checked axiom closure contains only `propext`.

The Rust pass must still derive every step from the original phi edge, emit
all incoming values, initialize the product, preserve dominance and register
widths, and survive allocation/encoding. These obligations are not premises
silently established by the arithmetic theorem. The multi-backedge phi and
32/64-bit arithmetic trace tests in `strength_reduce.rs` exercise the current
implementation; they are bounded regression evidence, not a proof that the
Rust implementation realizes this model. No end-to-end compiler or source
proof credit follows from this lemma alone.

## Trusted boundary

The current development trusts or assumes at least:

- the Lean kernel and the standard axioms `propext`, `Classical.choice` and
  `Quot.sound`;
- the native-evaluation axioms `bv_decide` generates: on 2026-10-15, 35 of
  them (`<theorem>._native.bv_decide.ax_*`), used by 42 declarations in
  `Cert/Arith`, `Cert/Compare`, `Sim/Match`, `Sim/ForwardSim/Pure`,
  `Sim/ForwardSim/Control`, `Model/Encoder`, `Model/Bits` and
  `Semantics/Source`. They trust Lean's compiled evaluator. None is in the
  closure of `compile_refines`;
- the faithfulness of the modeled source semantics, x86 semantics, encoder,
  loader/layout, and observables. Since the link step (below) these are
  definitions, not axioms: that `Source.SrcStep` is the meaning of the
  trust-ir trust-cg compiles, and that `x86Step` (fetch the bytes at `rip`,
  `decode` them, run `execInstr`) is what an x86-64 processor does with those
  bytes. The x86-64 encoder golden matrix (`Trust/Model/EncoderGolden.lean`,
  67 rows: 40 register/register ALU encodings and 27 near-branch encodings)
  binds `encode` on those rows to the Rust emitter
  (`lean_encode_golden_binding`). Nothing binds `decode` or `execInstr` to
  x86-64 hardware: there is no x86 silicon or emulator differential;
- the external correspondence between those models and the Rust backend,
  linker/runtime, and hardware.

There is no explicit project axiom and no `sorry`. The soundness gate checks
both from the Lean environment, not only from source lines:
[`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean) (run as
`lake env lean scripts/AxiomAudit.lean` after `lake build`) fails if any
declaration of a `Trust.*` module depends on `sorryAx` or on an axiom other
than the three standard ones and `bv_decide`'s native ones, or if
`compile_refines` depends on anything beyond the three standard axioms. An
inline `sorry` (`:= by exact sorry`) escapes the source-line count; it does not
escape the audit. On 2026-10-15 it audits 3,572 declarations.

## The link step (2026-10-15)

Until 2026-10-15 the contract in `Trust/Model.lean` declared `srcStep` and
`x86Step` opaque, and four explicit axioms tied them, and a second model, to
their intended meanings (ledger X-LEAN-P7):

| Former axiom | Resolution |
| --- | --- |
| `Machine.decode_encode` | Deleted with `Trust/Model/Machine.lean`, a second `Instr`/`execInstr` model over opaque byte codecs that only `Trust.lean` imported; no simulation, certificate, capstone or concurrency module used it. |
| `Machine.step_emitted` | Deleted with the same module. It asserted `x86Step m (eventOf i) (execInstr m i)` for every instruction regardless of the bytes at `rip`. |
| `Source.srcStep_spec` | A theorem (`rfl`): `Trust/Model.lean` now defines `srcStep code := Source.SrcStep code`. |
| `Model.Encoder.x86Step_decode` | A theorem (`Trust/Model/EncoderStep.lean`): `Trust/Model.lean` now defines `x86Step` as some byte string resident at `rip` that `decode` reads completely as `i`, stepping to `execInstr i m` with event `eventOf i`. |

`Trust/Model/Core.lean` holds the state vocabulary that `Semantics/Source` and
`Model/Encoder` build on, so `Trust/Model.lean` can import both and define the
two relations. A zero axiom count is therefore not a smaller trusted base about
hardware or the compiler. It means the two bridge claims are now definitions,
and their faithfulness is the modelling assumption listed above.

## What the linked definitions imply

Defining the relations lets Lean state, and the kernel check, what the opaque
relations hid ([`Trust/MetaTheorem/Vacuity.lean`](Trust/MetaTheorem/Vacuity.lean)):

- **The model machine is silent and partial.** `eventOf` is `.tau` for every
  `Instr`: the model has no CALL, RET, UD2 or MMIO instruction, so no
  `x86Step` emits an observable event (`x86Step_silent`). The machine takes no
  step where the bytes at `rip` do not decode (`x86Step_stuck_on_zero_memory`).
- **Execution domains are explicit and inhabited.** `LoweredStep` and
  `CalleeContract` now require real machine execution only under their `entry`
  predicate, and require a concrete witness that this domain is nonempty.
  `InstrCert.entryReady` must derive the guard from every incoming matching
  state; Pure, Mem, Compare, Arith, and Call producers retain that obligation.
  `EncoderStep.movSelfStep` supplies the resident bytes `48 89 c0`, proves an
  actual fetch/decode/execute step, advances PC by three bytes, and preserves
  memory. The all-zero negative controls still refuse execution
  (`loweredStep_zero_memory_not_ready`, `calleeContract_zero_memory_not_ready`).
  `not_residentEverywhere` still refutes unrestricted residency. Actual
  loader/layout evidence and callee implementations remain to be supplied.
- **The source relation is program-indexed.** `Source.Program.code` is an
  immutable input; `nextStep` fetches exactly `code[s.pc]`. Typed operands,
  casts and divisors are checked at that operation. Signed MIN / -1 faults
  for both division and remainder; shifts retain OD-57's masked refinement
  outside the TrustIR-defined range. Missing code and malformed
  operations fault there. Returns and faults set `halted`; halted states have
  no successor. `srcRun`, `CertRun`, the capstone's `Program.sourceCode` and
  concurrent per-thread steps retain the same program throughout execution.
- **The capstone premise is inhabited.** `ProgramWitness.certified` certifies
  every finite run of a source self-loop against resident x86 `JMP -5` bytes
  (`e9 fb ff ff ff`). `nonempty_certified_run` and `actual_machine_step`
  show real steps on both sides; `refinement` applies the unchanged conditional
  capstone. The all-runs certificate does not select only a convenient trace.
  This is a manually built model witness, not compiler output or a proof of
  the Rust-to-model binding. Its observable trace is empty because it loops.
- **Fetched observables remain unsupported.** `srcBeh_trap` and `srcBeh_ret`
  now require the running state and the fetched trap/return. `not_refines` and
  `certified_compile_unsatisfiable` apply to the explicit trap case, not every
  program. The deterministic-run exclusion theorem requires both incompatible
  traces as explicit hypotheses; no universal source impossibility remains.

The environment axiom audit still checks every imported declaration, including
these witnesses, without a `sorryAx` or project-axiom exemption. Full production
compiler correctness and an observable machine simulation remain open.

## The former `sorry` sites and the missing lemmas

The four classified `sorry` sites of ledger X-LEAN-P6 were not open proofs of
true statements. Under the linked relations three are false and the fourth
holds only vacuously; each is removed and replaced by the kernel-checked fact:

| Former `sorry` | What it claimed | Now |
| --- | --- | --- |
| `MetaTheorem.opKind_event_eq` (source-event correspondence) | every `OpKind` for `s ⇒ s₀` has the event of every source step `s ⇒ s₀` | false: `Vacuity.opKind_event_eq_refuted`. `OpKind` is indexed by the two states, not the step. `compile_refines` never used it: `CertRun` carries the agreement as its `hev` field. |
| `Sim.ForwardSim.CalleeContract_of_IH` (call-graph composition) | a `CalleeContract` from an induction hypothesis over the opaque `calleeMeasure` | the old unrestricted-entry rule remains false for every measure: `Vacuity.unguarded_calleeContract_of_IH_refuted` (a self-transition makes the decrease premise empty but cannot admit zero, non-decoding memory). Guarded callee contracts now require independent residency evidence. `calleeMeasure`, used only by the former rule, is removed. |
| `MetaTheorem.refines_machine_subset_of_determinism` (reverse refinement) | machine ⊆ source from a deterministic `x86Step` and forward refinement | the old universal impossibility argument is retired; explicit fetched traps still fail. The current conclusion holds only because the machine is silent: `Vacuity.machine_subset_source_vacuous`, which is not the backward theorem. |
| `Concurrent.atomic_forward_sim` (concurrent metatheorem) | `AtomicForwardSimStmt code lay` for every program and layout | false: `Vacuity.atomic_forward_sim_refuted` (the acting thread's source step can trap; no concurrent machine step is observable). |

What a meaningful replacement needs. Three prerequisites are shared:

- **P1, program-indexed model semantics: implemented.** Instructions are fetched
  from one fixed program, transitions are deterministic, terminal states do not
  step, and fault guards belong to the fetched operation. Positive arithmetic,
  return, fault, wrong-program and certified-loop witnesses build. The mapping
  from production TrustIR to this model and completeness for the real frontend
  remain obligations; model dispatch alone does not establish them.
- **P2, an event-bearing machine.** `Instr` cases for CALL, RET and UD2 (and
  for MMIO stores if they are observable), `eventOf` mapping them to `.call`,
  `.ret`, `.trap` (`.mmio`), decoder cases and golden rows for each, and the
  memory, IDIV, LOCK XADD and SSE forms admitted by `decode` (ledger
  X-LEAN-P5).
- **P3, residency-guarded step existence.** A code image in the layout and a
  conjunct of `R` (or a guard) saying the machine memory holds it, with
  `LoweredStep.runs : ∀ m, CodeResident lay m → x86StepPlus m event (exec m)`
  and the same guard on `CalleeContract.runs`, plus the frame lemma that
  execution does not write code bytes. The guarded interfaces, inhabited-domain
  witness and mandatory `InstrCert.entryReady` are now present; concrete
  loader/layout binding and code preservation remain open.

The four missing lemmas, stated over those prerequisites:

1. **Source-event correspondence.** Index `OpKind` by the event,
   `OpKind (lay) (s : SrcState) : Event → SrcState → Type`, with the `call`
   case at event `.call target` built from a machine CALL step (P2). Then
   `CertRun.cons (hstep : srcStep p s ev s₀) (ok : OpKind lay s ev s₀)` needs no
   `hev`, and the correspondence is definitional. Depends on P1, P2.
2. **Call-graph composition.**
   `calleeContract_of_compile (p) (lay) (μ : FnId → Nat) (hwf : ∀ f g, Calls p f g → μ g < μ f) (hcert : ∀ g, CertifiedFn p lay g) (tr : CallTransition lay s s') (hcall : CallsAt p s g) : CalleeContract lay s s' tr`,
   by well-founded induction on `μ g`: instantiate the callee's forward
   simulation over its entry-to-exit run and read the SysV facts (return in
   `rax` or `rax:rdx`, callee-saved registers restored, off-frame memory
   preserved) from its exit `R`. Depends on P1 (which callee a call reaches),
   P2 (CALL/RET), P3, and a recursion model (`μ`, or fuel). An AArch64 version
   needs the AAPCS64 partition, which exists only in Clean's subset
   (`proofs/abi_clobber_spec.lean`).
3. **Reverse (backward) refinement**, ROADMAP item 6 and
   DR-PROVEN-CORE-BOTH-DIRECTIONS-20261015:
   `compile_refines_backward (P) (hcert : Certified_compile P) : ∀ obs, (x86Sem P).behaviours obs → (srcSem P).behaviours obs`,
   with the resource disjunct the decision record names. The standard route:
   the forward simulation, determinism of `x86Step` (true of the current
   decoder, where the first byte fixes a complete decode's length, but not
   yet stated), and receptiveness of the source (a certified non-final state
   always has a step). Depends on P1, P2, P3.
4. **Concurrent forward simulation.**
   `atomic_forward_sim (p : ConcProg) (lay) (hcert : CertifiedConc p lay) : AtomicForwardSimStmt p lay`
   over per-thread program-indexed steps. Depends on P1 per thread, P2 (LOCK
   XADD and fences decodable and observable where they must be), P3, a
   `TSOConsistent` that constrains the machine (today it is a tautology, so
   `RC.tso` carries nothing), and the interleaving induction over the global
   schedule.

The byte-store outside-range and in-range independence facts, disjoint reads,
memory read congruence, source/machine read agreement, and atomic shared-store
agreement have kernel-checked proofs. The atomic-load value theorem also has a
proof and explicitly requires source memory to agree with the drained machine
memory; its former statement omitted that necessary relation. These seven
theorems depend only on `propext` and `Quot.sound`, not `sorryAx` or any
project axiom. This does not complete the concurrent simulation theorem or
the correspondence between these models and production Rust.

Load preservation now also requires disjoint destination registers for both
halves of live pairs and a byte-read width that fits its source carrier. These
premises flow through `load_instrCert`, `forwardSim_load`, and `OpKind.load`.
The associated proofs and two counterexample controls contain no `sorryAx`.
The conditional `forward_sim` theorem depends on `propext`, `Classical.choice`
and `Quot.sound` only; it still requires the complete `OpKind` evidence, and
its entry guard must now be established for every matching input. No
production load/call compilation is certified by the concrete MOV witness. The unsigned
quotient/remainder identity is proved for general bitvector widths using
natural-number arithmetic.

Both memory write/read round-trips are proved. The width-generic memory model
requires a byte count smaller than the 64-bit address space, ensuring distinct
addresses even when the base wraps. The encoder's 64-bit scalar store has a
separately checked equivalence to that model for byte counts zero through eight.
Their new explicit bounds replace the unsupported unbounded statements; these
round-trip proofs have no project axioms or sorry dependencies.

## AArch64 (A64) modules

`Trust/A64/` adds no `sorry` and no explicit axiom. `#print axioms` on `decode_encode`, `encode_decode`,
`encode_injective`, `cmp_condition_cert`, `cmp_v`, `exec_cset` and
`step_of_fetch` lists only `propext`, `Classical.choice` and `Quot.sound`;
`bitmaskValid_iff_decodeBitMasks` depends on no axiom and `condHolds_invert` on
`propext` alone. The finite facts (the bitmask equivalence, the 831 generated
golden rows, the 1,165 recorded hardware results, and their corruption controls) are closed by `decide +kernel`,
which is kernel reduction: no `native_decide`, no `bv_decide` and therefore no
`Lean.ofReduceBool`.

What these modules establish, by evidence strength:

- **Proved about the model:** the instruction-word encoder and decoder are
  mutually inverse on valid instructions (and the decoder accepts only valid
  ones); after `CMP a, b` each condition trust-cg selects for an integer
  predicate holds exactly when the predicate does, at every width; the CMP and
  CSET alias semantics; and that a step fetching the model's encoding of an
  instruction executes it.
- **Tested on enumerated rows, not proved:** that the Rust emitter, its
  field-level helpers and ENC-5 agree with the model on the generated corpus
  (`lean_a64_encode_golden_binding`); and that `decode` + `exec` reproduce the
  host CPU on 1,165 recorded executions (`Trust/A64/SiliconChecks.lean`).
- **Trusted:** that the Lean transcription of the Arm ARM pseudocode is
  faithful outside the recorded executions; the model's boundaries (a flat
  little-endian memory with no alignment faults or other observers, barriers
  as no-ops, no SIMD&FP, no exceptions); the Rust test's parser of the golden
  rows; and that the 140 emitter shapes' denotations in `Trust/A64/Corpus.lean`
  are the ones trust-cg intends. The generators are not trusted: the kernel
  re-checks everything they write.

None of this is an AArch64 forward simulation or compiler theorem; that remains
ledger gap X-LEAN-P1.

## How to interpret `compile_refines`

`compile_refines` states forward inclusion inside the Lean model when supplied
with `Certified_compile P` for the fixed `P.sourceCode`. The premise is now
inhabited by `ProgramWitness.program`, with nonempty resident execution, but it
is not constructed from a production compilation. The silent machine still
cannot implement fetched observable operations. In
particular:

- call correctness enters through a guarded callee contract; real compiled callee implementations remain unbound;
- unsupported state/operand/control-flow shapes do not gain coverage merely
  because the theorem exists;
- the reverse direction (excluding extra machine behavior) remains open;
- the production Rust emitter is only connected to a named encoder-golden
  matrix, not formally refined in full.

Before relying on a narrower claim, inspect the exact theorem, its
`#print axioms` output and `Trust/MetaTheorem/Vacuity.lean`. Do not infer a
repository-wide verified-compiler claim, or any compiler claim, from the
existence of the capstone declaration.

The authoritative automated checks are the `lake build`, the sorry/axiom
counts and the environment audit (`scripts/AxiomAudit.lean`), and the
encoder-golden bindings in the repository soundness gate.
