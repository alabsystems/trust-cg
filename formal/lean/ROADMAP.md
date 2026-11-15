# Lean proof-closure roadmap

The Lean development builds without `sorry` or explicit project axioms. Its
program-indexed capstone now has an inhabited all-runs premise and nonempty
resident execution (`ProgramWitness`); full compiler correctness remains open.
The x86 model stays frozen as an oracle (DR-PROVEN-CORE-20261015, decision 13).
The repair changes source dispatch and contracts, not the modeled machine.
The remaining proof requirements apply to a future model, including AArch64.

- **P1, modeled dispatch implemented.** `SrcStep code` fetches only the
  instruction at `s.pc` in a fixed program. Faults are operation-local, returns
  and faults terminate, and runs and per-thread steps retain the fixed code.
  Concrete controls and a certified looping program build. Production TrustIR
  binding and frontend coverage remain separate obligations.
- **P2.** Give the machine observable instructions: CALL, RET, UD2 (and MMIO
  stores if observable) with `eventOf` mapping them to their events, decoder
  cases and golden rows, and the memory, IDIV, LOCK XADD and SSE forms
  `decode` refuses today (X-LEAN-P5).
- **P3.** Guard step existence by code residency: a code image in the layout,
  `R` (or a guard) saying the machine memory holds it, and
  `LoweredStep.runs`/`CalleeContract.runs` quantified over resident states
  only. The interfaces now require explicit inhabited entry domains, every
  instruction certificate carries `entryReady`, and a concrete resident
  three-byte MOV witnesses a real step. Remaining: derive each site's guard
  from the actual loader/layout image and prove code-byte preservation.

Then, in roughly this order:

1. Discharge the remaining byte-memory and bitvector helper obligations, and
   index `OpKind` by the source event so the event correspondence is
   definitional (the refuted `opKind_event_eq`; SOUNDNESS.md, lemma 1).
2. Strengthen memory/load survivor interfaces so pair, vector, and spill cases
   can be framed without assumed side conditions.
3. Close or formally reject uncovered jump-table control flow.
4. Prove that callee contracts arise from a well-founded call-graph or explicit
   recursion model instead of entering as assumptions (the refuted
   `CalleeContract_of_IH`; SOUNDNESS.md, lemma 2).
5. Extend the Lean/Rust correspondence beyond the current encoder-golden
   matrix, including object layout and relocation behavior, and bind
   `decode`/`execInstr` to hardware or an emulator by recorded executions, as
   `Trust/A64/SiliconChecks.lean` does for A64.
6. Prove the reverse behavioral inclusion (machine ⊆ source). It is mandatory,
   not optional (DR-PROVEN-CORE-BOTH-DIRECTIONS-20261015), and needs P1 to P3
   and machine determinism (SOUNDNESS.md, lemma 3).
   `machine_subset_source_vacuous` is not it.
7. Treat the concurrent/atomic development as a separate proof track: a
   non-tautological `TSOConsistent` and the interleaving argument over
   per-thread program-indexed steps (the refuted `atomic_forward_sim`;
   SOUNDNESS.md, lemma 4) before presenting it as supported.
8. AArch64 (`Trust/A64/`, ledger X-LEAN-P1): state a forward simulation from a
   trust-cg source or LIR semantics to `Trust.A64.step` for the integer ALU,
   compare, select, shift and branch subset, then loads and stores; add an
   AArch64 capstone analogous to `compile_refines`, built on P1 to P3 from the
   start so it does not inherit the x86 development's vacuity; extend the
   semantics to SIMD&FP, atomics and the weak memory model; and widen the
   emitter corpus and decoder to every form the emitter writes (X-LEAN-P3
   binds the enumerated rows only).

For every step, inspect `#print axioms` on the affected load-bearing theorem,
run `lake env lean scripts/AxiomAudit.lean`, add a negative or mutation control
where practical (a theorem whose premise is unsatisfiable proves nothing; show
the premise is inhabited), and keep unsupported production paths fail-closed.
Merely moving a `sorry` behind a new axiom or strengthening a premise without
wiring it to the production gate is not proof closure.
