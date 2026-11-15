# trust-cg Lean development

This directory contains a Lean 4 model and a conditional forward-refinement
development for selected trust-cg paths. It is supporting research evidence,
not an end-to-end proof of the Rust compiler or every emitted binary.

## What the capstone says

`Trust/MetaTheorem/CompileRefines.lean` defines:

```lean
theorem compile_refines (P : Program) (hcert : Certified_compile P) :
    Refines (x86Sem P) (srcSem P)
```

In the Lean model, the theorem maps a source run covered by
`Certified_compile` to a matching modeled x86 run with the same filtered
observable trace, using one fixed `Program.sourceCode`. Source instructions
are fetched at the actual program counter; faults and returns terminate.
`ProgramWitness` supplies a certificate for every finite run of a resident
source/x86 self-loop, including a nonempty source and machine execution. The
premise is therefore no longer universally false.

This witness is manually constructed, not emitted by the Rust compiler. The
machine remains silent, so fetched source returns, traps, calls and MMIO still
need observable machine counterparts. Residency guards still need loader/layout
binding, and the Rust compiler/runtime do not establish `Certified_compile`.

The modeled surface is intentionally limited. The production source-model
binding, observable machine instructions, loader/layout evidence for the new residency guards,
cross-function composition, jump-table control flow, survivor framing, parts
of byte-level memory reasoning, and the concurrent extension remain missing
([`SOUNDNESS.md`](SOUNDNESS.md) states the missing lemmas).

## Target scope

### Forward simulation and capstone: x86-64 only

This is the repository's only Lean forward-simulation development, and it
models x86-64 alone:

- [`Trust/Model/Core.lean`](Trust/Model/Core.lean) fixes the register files
  (`GPR` rax..r15, `XMM` xmm0..xmm15), the EFLAGS subset, the `rip`-based
  machine state, the source state, the observable events and the refinement
  relation `R`;
- [`Trust/Model/Encoder.lean`](Trust/Model/Encoder.lean) is the x86-64
  instruction set (`Instr`), byte encoder/decoder and transfer function
  (`execInstr`), and
  [`Trust/Model/EncoderGolden.lean`](Trust/Model/EncoderGolden.lean) pins that
  encoder to golden vectors shared with the Rust x86-64 encoder;
- [`Trust/Model.lean`](Trust/Model.lean) is the link step that every other
  module builds on: it defines `srcStep` as the source semantics
  `Source.SrcStep` and `x86Step` as fetch the bytes at `rip`, `decode` them,
  run `execInstr`, so the former axioms `srcStep_spec` and `x86Step_decode`
  are theorems ([`Trust/Model/EncoderStep.lean`](Trust/Model/EncoderStep.lean)
  holds the latter and the `LoweredStep` builders);
- the forward-simulation cases under [`Trust/Sim/ForwardSim/`](Trust/Sim/ForwardSim)
  are stated over x86 steps (`x86StepPlus`), and the capstone in
  [`Trust/MetaTheorem/CompileRefines.lean`](Trust/MetaTheorem/CompileRefines.lean)
  refines `x86Sem`;
  [`Trust/MetaTheorem/Vacuity.lean`](Trust/MetaTheorem/Vacuity.lean) proves
  that capstone vacuous and refutes the four former `sorry` statements;
- [`Trust/Concurrent/Atomics.lean`](Trust/Concurrent/Atomics.lean) is an
  x86-TSO model.

No forward simulation, refinement target or capstone exists for AArch64, so no
theorem in this directory says that trust-cg compiles anything correctly for
AArch64. The AArch64 compilation evidence remains outside this development: the
value-level Clean B-definition checks and the Rust coverage, decode-check and
differential gates described in [`SOUNDNESS_CHECK.md`](../../SOUNDNESS_CHECK.md).

### AArch64: instruction-word model and integer semantics

[`Trust/A64/`](Trust/A64) is a separate AArch64 (A64) target model, the
instruction-word layer and the start of the machine layer that an AArch64
forward simulation needs (ledger X-LEAN-P3, and the start of X-LEAN-P1 in
`docs/aarch64-completion-audit-2026-09-17.md`):

- [`Trust/A64/Encoding.lean`](Trust/A64/Encoding.lean): an `Instr` inductive
  with one constructor per A64 encoding class trust-cg emits for integer code
  (27 classes: add/subtract shifted, extended, immediate and with carry; logical
  shifted and bitmask immediate; move wide; bitfield; extract; conditional
  select; data processing with 1, 2 (including CRC32/CRC32C) and 3 sources;
  B/BL, B.cond, CBZ/CBNZ, TBZ/TBNZ, BR/BLR/RET; ADR/ADRP; BRK, NOP and
  barriers; load literal, pairs, 9-bit-immediate, register-offset and
  unsigned-immediate loads and stores, general-purpose and SIMD&FP),
  each field a `Fin (2^width)` named as in the Arm ARM diagram; a field-level
  `valid` that refuses UNDEFINED and unallocated field values;
  `encode : Instr → UInt32`; a decision-tree `decode : UInt32 → Option Instr`
  over the fixed bits; and the proved round trips `decode_encode`
  (`decode (encode i) = some i` for every valid `i`), `encode_decode`
  (`decode w = some i → encode i = w ∧ i.valid`), `decode_eq_some_iff` and
  `encode_injective`; ten refusal controls show reserved field values (for
  example `shift = 11`, a 32-bit `N = 1` bitmask, PRFM, SMULH with `Ra ≠ 31`)
  decode to `none`. Aliases (CMP, TST, MOV, CSET, LSL #k, SXTW, SMULL, ...) are
  not constructors: they denote canonical class instructions, so the round trips
  cover them.
- [`Trust/A64/Bitmask.lean`](Trust/A64/Bitmask.lean): the Arm ARM
  `DecodeBitMasks`, and `bitmaskValid_iff_decodeBitMasks` (kernel evaluation
  over every `N`, `imms`, `immr`) showing the decoder's logical-immediate
  validity is exactly where `DecodeBitMasks` is defined.
- [`Trust/A64/Corpus.lean`](Trust/A64/Corpus.lean): for 140 emitter opcode
  shapes (`AArch64Opcode` variants with their `MachOperand` lists), the A64
  instruction the model says each denotes, and the enumerated corpus.
  [`scripts/GenA64Golden.lean`](scripts/GenA64Golden.lean) renders it as the
  generated [`Trust/A64/EncoderGolden.lean`](Trust/A64/EncoderGolden.lean)
  (831 rows), whose kernel-checked theorems require the rows to be exactly the
  corpus and every word to be `encode` of its instruction and to decode back.
  The Rust test
  [`lean_a64_encode_golden_binding`](../../crates/trust-cg-codegen/tests/lean_a64_encode_golden_binding.rs)
  requires the production `encode_instruction`, the field-level encoding
  helpers and the ENC-5 decode-check to agree with every row, ENC-5 to refuse
  every single-bit corruption of every golden word, and corrupted golden text
  to be refused by name. It runs on the Darwin and Linux AArch64 floors and in
  the soundness gate.
- [`Trust/A64/Machine.lean`](Trust/A64/Machine.lean): `MachState` (X0..X30,
  SP, PC, NZCV, byte memory; register 31 is the zero register except where the
  Arm ARM gives it to SP; 32-bit forms zero-extend), `exec` transcribing the
  Arm ARM operation pseudocode of every class above (`AddWithCarry`,
  `ConditionHolds`, `ShiftReg`, `ExtendReg`, `DecodeBitMasks`), and
  `step` = fetch, `decode`, `exec`. `exec` returns `none` outside the model:
  invalid instructions, SIMD&FP accesses, BRK, and CONSTRAINED UNPREDICTABLE
  write-back or LDP register overlaps. Proved: `cmp_c` (after `CMP a, b` the C
  flag is NOT-borrow, `C ↔ b ≤ a` unsigned, the opposite of x86's CF),
  `cmp_z`, `cmp_n`, `cmp_v`, `cmp_ge`, and `cmp_condition_cert`: for every
  integer predicate, the condition trust-cg's `AArch64CC::from_intcc` selects
  holds after `CMP a, b` exactly when the predicate does, at every width
  `w ≥ 1`; `condHolds_invert` (the CSET inversion); `tst_conditions` (after
  `TST a, b`, EQ/NE/MI read `a AND b` and C, V are clear) and `cmn_c`/`cmn_z`
  (CMN's carry and zero); `exec_cmp`, `exec_cmp_imm`, `exec_tst` and
  `exec_cset` (alias semantics); and `step_of_fetch` (a step whose fetched word
  is the model's encoding of `i` executes `i`).
- [`Trust/A64/SiliconChecks.lean`](Trust/A64/SiliconChecks.lean): generated by
  [`scripts/gen_a64_silicon_checks.py`](scripts/gen_a64_silicon_checks.py)
  from 1,165 instruction executions on the host CPU (Apple M4 Max): data
  processing, flags and CRC32, conditional, compare and test branches, and
  loads and stores against a 64-byte memory window. Its kernel-checked theorem
  requires `decode` and `exec` to reproduce every recorded register, NZCV,
  next PC and memory window, and a control theorem requires every corrupted
  record to fail. The differential found, and the model now fixes, a CLS
  transcription error.

The round trips and certificates are proofs about the Lean model. The binding
to the Rust emitter and the agreement with hardware are tests on enumerated
rows. Named next steps for X-LEAN-P1: a forward simulation from a trust-cg
source or LIR semantics to `step` for the ALU, compare, select, shift and
branch subset whose semantics now exist; an AArch64 capstone analogous to
`compile_refines`; SIMD&FP, atomics and the weak memory model; and widening
the corpus (and the Lean decoder's class list) to every form the emitter writes.

[`Trust/Cert/BitManip.lean`](Trust/Cert/BitManip.lean) proves the complete 32- and
64-bit SWAR population-count value equations for every input. Its byte-count
invariant and arithmetic folds are checked by the kernel; the transitive
assumptions are only `propext`, `Classical.choice` and `Quot.sound`. The focused
[`BitManipAudit.lean`](scripts/BitManipAudit.lean) rejects native-evaluation axioms
as well as project axioms and `sorryAx`. Run the proof build, definition bindings,
mutation controls and false-proof refusals with
`scripts/check_swar_value_proofs.py` from the repository root through build-slot.

These are standalone value equations. They produce no `InstrCert` or
`CertProvider`, and do not establish emitted-byte execution, clobber/frame
preservation or a source transition. Runtime DRAT acceptance is unchanged.
Other bit-manipulation value proofs and the machine/source connection remain
open in X-LEAN-P11. [`Trust/Cert/Niche.lean`](Trust/Cert/Niche.lean) remains empty;
there is still no niche or transmute value certificate here.

## Current proof boundary

The release gate pins the current tree-wide baseline at:

- 0 `sorry` lines under `Trust/`;
- 0 explicit axioms;
- a green `lake build`;
- the environment audit [`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean):
  no `Trust.*` declaration depends on `sorryAx` or on an axiom beyond
  `propext`, `Classical.choice`, `Quot.sound` and `bv_decide`'s native ones,
  and `compile_refines` on the first three only;
- a shared Lean/Rust encoder-golden test for its named x86-64 instruction matrix,
  and the generated A64 golden corpus test (`lean_a64_encode_golden_binding`).

The zero counts do not make the development a compiler proof. The four former
`sorry` sites were statements that are false or vacuous under the linked
relations and are replaced by their refutations; the four former axioms were
removed by deleting a dead parallel model and by defining the two step
relations, which leaves their content as modelling assumptions. The golden tests
bind only the enumerated encodings; they are not a proof of the full Rust
emitter. The `Trust/A64` modules add no `sorry` and no axiom.

Important trusted or incomplete boundaries include:

- that `Source.SrcStep` means trust-ir and that `decode`/`execInstr` mean
  x86-64 hardware (definitions now, not axioms; no x86 hardware differential);
- `bv_decide`'s native-evaluation axioms (35, used by 42 declarations);
- the correspondence between modeled instructions and the production emitter;
- a source semantics with no program, a silent machine, and step existence
  demanded from every machine state, which make the capstone vacuous;
- open call-graph, jump-table, reverse-refinement and concurrency cases.

See [`SOUNDNESS.md`](SOUNDNESS.md) for the inventory and
[`ROADMAP.md`](ROADMAP.md) for the closure order.

## Build and inspect

The package pins Lean in `lean-toolchain` and is built by `lakefile.lean`:

```sh
cd formal/lean
lake build
```

Regenerate the two generated A64 modules after changing the model or the
corpus (the second needs an AArch64 host with `clang` or `cc`):

```sh
lake build Trust.A64.Corpus
lake env lean --run scripts/GenA64Golden.lean > Trust/A64/EncoderGolden.lean
python3 scripts/gen_a64_silicon_checks.py --out Trust/A64/SiliconChecks.lean
```

Count `sorry` lines and explicit axioms, and run the environment audit, as the
release gate does:

```sh
grep -R -h -E '^[[:space:]]*sorry([[:space:]]|$)' --include='*.lean' Trust | wc -l
grep -R -h -E '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable|unsafe|partial)[[:space:]]+)*axiom[[:space:]]' --include='*.lean' Trust | wc -l
lake env lean scripts/AxiomAudit.lean
```

When reviewing a load-bearing declaration, use `#print axioms` in a small Lean
query to inspect its actual transitive assumptions. A successful `lake build`
alone is not evidence that a declaration is free of `sorryAx`; the audit
checks every declaration.

The cross-repository orchestration and exact ratchet implementation live in
[`scripts/soundness_check.sh`](../../scripts/soundness_check.sh) and
[`SOUNDNESS_CHECK.md`](../../SOUNDNESS_CHECK.md).


The x86 model also admits full-width `movabsRI` mask loads (REX.W + B8+r +
imm64), with an all-register/all-immediate round-trip theorem, exact destination
replacement, frame preservation and ten-byte PC advance. `Model.MovabsGolden`
binds 96 vectors to the production encoder through `lean_encode_golden_binding`.
Run `scripts/check_movabs_model.py` through build-slot for the focused model,
residency, axiom and backend checks. This does not add shift-immediate decoding
or prove complete SWAR instruction execution, and does not attest the compiler.
