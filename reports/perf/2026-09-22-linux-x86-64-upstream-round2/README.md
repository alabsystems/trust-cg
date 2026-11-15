# Linux x86-64: round 2 after `origin/main` moved again (2026-09-22)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`origin/main` moved two further commits — `4ded2b97c` (the first `core` refusal
census on the Darwin workstation) and `b943790f0` (`[TCG-PROOF-465]` 46 → 0
against the LIR source) — WHILE the first round of this merge was under review,
and the second of them rewrote the exact vacuity function the first round had
diverged on. Round 1's resolution was therefore not wrong so much as overtaken,
and it was re-argued against the newer measurement rather than re-asserted.

The round-2 merge is `35a3a6d9e`; everything below was produced from the merged
tree with a clean working tree, and every artifact it cites is retained beside
this file. Round 1 is retained separately at
[`2026-09-22-linux-x86-64-upstream-merge`](../2026-09-22-linux-x86-64-upstream-merge/README.md)
as the record of the tree at `9a276a0c1`.

Host: `x86_64-unknown-linux-gnu`, Ryzen 9 9900X3D, 24 cores, 61 GiB, GCC
15.2.0. Root workspace built with the pinned stock Rust 1.97.1
(`rust-toolchain.toml`; the project's own pin overrides this machine's Trust
default toolchain). Bridge built with the tree-built stage2 `trustc`
(`rustc 1.99.0-dev (3a3e781fe 2026-09-14)`) through
`targo --unverified build --release --locked`. Backend SHA-256 in
`census/backend.sha256` — the dylib the census below was actually run with.
Every build and test ran under a memory guard (`CARGO_BUILD_JOBS=3`, one of two
flock slots, `MemoryMax=22G`), and two other agents were building in other
worktrees throughout.

This is a regression and refusal measurement in the explicit unverified
frontend lane. It is not a proof claim, and it does not establish compiler
completion or release readiness.

## The decision that changed behaviour

`[TCG-PROOF-465]` had been attacked by three lanes, and the third arrived
after round 1 was cut.

| lane | host / evidence | rule it proposed |
| --- | --- | --- |
| upstream `3b80e9497` | Darwin, NO bridge dylib; drove source shapes through the pipeline | widen the anonymous empty-body escape by OPCODE SHAPE to `[Ud2]` / `[Push, MovRR, Ud2]`; explicitly decline `[Call, Ud2]` |
| this branch (round 1) | Linux, WITH the bridge; measured the census | a NAMED `call_only_body` certificate keyed on the verifier's per-row DISPOSITION; class 46 → 0 |
| upstream `b943790f0` | Darwin, WITH the bridge; **disassembled** the remaining 44 roots | admit the call-then-trap shape only against the LIR SOURCE, which must be exactly `Jump* ; Call (no args, no results) ; Trap`; class 270 → 226 with the class at 0 |

Round 1 had argued that upstream "declined `[Call, Ud2]` on that guess". That
argument is withdrawn: upstream has since measured, and its source fact is
strictly better evidence than a row-shape test can be. What it establishes —
that the message and the `#[track_caller]` location are gone AT THE SOURCE
LEVEL, so there is nothing to forward — is exactly what the emitted rows cannot
show.

**Resolved to one mechanism whose gate is the CONJUNCTION of the two facts.**
`x86_64_call_only_body_certificate` issues its named certificate only when

1. every report row carries the verifier's own by-design disposition — its trap
   SKIP, or its no-proof-mapping UNVERIFIED refusal for a control-transfer
   opcode (`x86_64_report_transfer_and_trap_rows`); AND
2. the LIR source, flattened in layout order, is a bare DIVERGING transfer:
   `Jump* ; Trap`, or upstream's `Jump* ; Call (direct, no args, no results) ;
   Trap` (`lir_is_transfer_only_diverging_body`, built on upstream's
   `lir_is_zero_arg_direct_call_then_trap`; the source is threaded through every
   `proof_certificates_from_x86_64_report` call site, upstream's plumbing kept
   verbatim).

Both halves are load-bearing, and the hole the review found was real:

| body | rows half | source half | before | now |
| --- | --- | --- | --- | --- |
| `unreachable` | pass | pass | promoted | promoted |
| `call abort; unreachable` (1 and 2 blocks) | pass | pass | promoted | promoted |
| **`call f; ret`** (forwarding shim, returns to its caller) | pass | **FAIL** | **promoted `verified: true`** | **refused** |
| `call f; call g; ud2` | pass | **FAIL** | promoted | refused |
| call with arguments already in place | pass | **FAIL** | promoted | refused |
| rows the verifier FAILED, with a diverging source | **FAIL** | pass | refused | refused |

The third row is the one that mattered: a `verified: true` certificate counts
as semantics-verified in `JitValidationProvenance` and promotes in the AOT
proof-required lane with zero discharged instruction theorems, and round 1's own
test asserted that behaviour. It now asserts the refusal instead, and names the
source half in the refusal text.

A jump that carries BLOCK ARGUMENTS needs no special case: it lowers to
phi-resolution `MOV` copies, which are value rows, so the rows half refuses it.

`x86_64_report_is_empty_body` stays at exactly `[Ret]`. Upstream's
`[Push, MovRR, Pop, Ret]` / `[Ud2]` / `[Push, MovRR, Ud2]` arms are still not
taken — a `MovRR` report row cannot be told from a value copy, and the frame
envelope is inserted by the encoder after instruction selection — and upstream's
new disassembly does not bear on that, because what it measured is the
call-then-trap SOURCE, which IS adopted. The evidence that this narrowing costs
nothing on either object format is
`x86_trap_only_body_certifies_and_argument_shims_are_not_vacuous`, which drives
the trap-only shim and upstream's two new call-then-trap shims through the whole
module-compile boundary on both `x86_64-apple-darwin` and
`x86_64-unknown-linux-gnu` and requires all three to promote under the NAMED
certificate.

The named certificate survives because it is auditable: `--emit-proofs` writes
it as an eval-only `.cert` and the lowering-sidecar builder skips it by name, so
a publication can be audited for exactly which functions promoted on the
exemption. Upstream's anonymous escape issues no certificate at all. Upstream's
improved vacuity DIAGNOSTICS are kept verbatim: a refusal now names its report
rows and either the source's own shape or the fact that no source was supplied.

## `library/core` refusal census, O0, certificates on

`scripts/trust_ir_cg_census.py` from the Trust checkout against the bridge
rebuilt from this tree. Retained in `census/` (`gap_table.md`,
`provenance.json`, `failed_roots.jsonl.gz`, `backend.sha256`).

| Measurement | Failed roots | Distinct reasons | Objects emitted | Backend |
| --- | ---: | ---: | ---: | --- |
| 2026-09-21 merged wave 1 | 183 | 27 | 3,249 | `2d6b86a3…` |
| 2026-09-22 round 1 (148 upstream commits) | 183 | 27 | 3,249 | `638c68a5…` |
| **2026-09-22 round 2 (this tree)** | **183** | **27** | **3,249** | **`baf97456…`** |

**The baseline held exactly, and not merely in the totals.** Compared symbol by
symbol against round 1's retained `failed_roots.jsonl.gz`: **0 roots added, 0
removed, 0 reasons changed on a shared root**, and the gap table is
line-identical below its provenance header (only `wall: 67s` vs `66s` differs).
`[TCG-PROOF-465]` stays at **0** under the stricter two-fact gate — the source
requirement costs nothing on real `core`, which is the measurement that says
the 46 roots really are the bare `call abort; ud2` shape upstream disassembled
and not something looser that the disposition half had been letting through.

Class order, unchanged: `[TCG-POINTEE-DYN-VALUE]` 30, `[TCG-PASSVAL-067]` 27,
`[TCG-POINTEE-LANES]` 21, fat-pointer union fields 21,
`[TCG-POINTEE-UNSIZED-TAIL]` 16, memory-backed slice `Rvalue::Cast` 11,
`[TCG-REGALLOC-063]` 8, `[TCG-RET-REGCLASS]` 6, `[TCG-ARG-ABI]` 2 (both
`Option<u128>`), then 18 reasons at five roots or fewer.

### The backend identity, and what it is and is not

The SHA-256 above is the dylib this census was ACTUALLY run with
(`census/backend.sha256`), read back from disk after the build and before the
run. Round 1's report cited a dylib REBUILT after its census; that citation is
corrected in `docs/linux-x86-64-completion.md` to the value its own
`census/backend.sha256` records.

**Measured here, because that discrepancy deserved an explanation rather than a
correction: the bridge dylib is NOT byte-reproducible.** Rebuilding it from the
same clean committed tree, same `trustc`, same `targo --unverified build
--release --locked`, produced
`5e2331d4e6de3f0b7f6515ad0a43a69afeb09e23bcf1435c0b8152bafc744e62` — a
different artifact from `baf97456…`. So a backend SHA-256 in this repository
IDENTIFIES the artifact a measurement used; it does not certify that the
artifact can be re-derived from a commit, and two reports of the same commit
will legitimately cite different hashes. That is what happened in round 1, and
it is a property of the build, not a bookkeeping error.

The census was therefore re-run on the SECOND dylib and is retained beside the
first in `census-rebuild/`: **183 failed roots over 27 reasons, 3,249 objects,
64 s**, with the failed-root symbol set identical to the first run (0 added, 0
removed, 0 reasons changed) and a line-identical gap table. The MEASUREMENT
reproduces even though the artifact does not, which is the property that
actually matters for a refusal census.

## Linux x86-64 regression floor

`python3 scripts/check_linux_x86_64.py --out … --jobs 4 --max-rss-gib 20
--require-clean --trust-driver <stage2>/bin/trustc`, run under the memory guard
on the clean committed tree (`report.json` provenance: `dirty: false` at
`source_sha 05dfdb16b`, `errors: []`). Retained in `floor/` with every
per-target log and its SHA-256.

**68 targets, 57 pass, 11 fail** — TARGET FOR TARGET IDENTICAL to round 1: no
target added, none removed, no status change on any of the 68.

The eleven are the same two open items:

* **XD-01** (proof promotion on a formal-capable host), 8:
  `jit_cert_cache_identity_x86_64`, `jit_sysv_x86_64_spill_replay`,
  `jit_validation_modes_x86_64`, `jit_x86_64_aggregate_abi_fail_closed`,
  `jit_x86_64_profile_modes`, `x86_64_constant_pool`, `x86_64_sysv_ay_abi`,
  `x86_64_target_features`;
* **X03** (ELF exception handling), 3: `e2e_x86_64_eh_catch`,
  `e2e_x86_64_eh_invoke_trust_ir_run`, `e2e_x86_64_eh_resume_trust_ir`.

`e2e_x86_64_swiftcc` is still printed as DECIDED ABSENT under XD-03, and the
bridge lane `m143_x86_vectorize_trace` and the TY kernel `ty_bfs_minimal` both
pass.

## Root workspace suites

Stock Rust 1.97.1, every invocation under the memory guard.

| Suite | Result |
| --- | --- |
| `trust-cg-lower --lib` | 1,882 passed / 0 failed |
| `trust-cg-codegen --lib` | 3,988 passed / **16 failed**, 1 ignored — the failure set is byte-identical to `codegen-lib-failures.txt` beside this file, to round 1's, and to the retained 2026-09-21 reconciled list (all three diffs empty). All sixteen are the XD-01 `ProofPromotionRejected` class (15 `compile_service` plus `test_aarch64_parallel_and_serial_multi_function_byte_identical`) |
| `trust-cg-opt --lib` | 3,550 passed / 0 failed, 2 ignored |
| `trust-cg-verify --lib post_ra_dataflow` | 74 passed / 0 failed |
| `trust-cg-verify --lib x86_64_lowering_proofs` | 176 passed / 0 failed |
| `coverage_gate_tests` | 49 passed / 0 failed |
| `meta_theorems` | 8 passed / 0 failed |
| `soundness_manifest` | 11 passed / 0 failed |
| `x86_addressing_gate` | 10 passed / 0 failed |
| `x86_volatile_trace_gate` | 8 passed / 0 failed |
| `e2e_x86_64_aggregate_abi` | 30 passed / 0 failed |
| `e2e_x86_64_aggregate_byval_arg` | 8 passed / 0 failed |
| `trust-cg-cli --bin trust-cg -- emit_proofs` | 14 passed / **1 failed** — `arithmetic_tests::exact_arithmetic_queries_survive_export_and_metadata_cannot_grant_authority`, a PRE-EXISTING toolchain-dependent red (see below) |
| `cargo test --workspace --no-run` | Finished, 0 errors, 634 test executables |

The vacuity family specifically (`-- vacuo call_only empty_body empty_function
trap_only`): 14 passed / 0 failed, including
`x86_call_only_bodies_certify_through_the_real_verifier`,
`x86_call_only_body_is_certified_on_verifier_dispositions_and_lir_source`,
`x86_trap_only_body_certifies_and_argument_shims_are_not_vacuous` and
`x86_empty_body_is_not_vacuous_but_one_unproved_instruction_is`.

Gates: `scripts/check_fmt.sh` OK; `check_documentation.py --write` then
`--check` current; `scripts/tests/test_linux_x86_64_gate.py` 6 OK;
`test_linux_aarch64_gate.py` 32 OK (1 skipped); `test_darwin_aarch64_gate.py`
28 OK.

## Pre-existing reds, found by measuring something round 1 did not

* **`trust-cg-cli`'s own tests were never run in round 1.** Running them here
  found `emit_proofs::arithmetic_tests::exact_arithmetic_queries_survive_export_and_metadata_cannot_grant_authority`
  failing with an AArch64 opcode-inventory refusal (`AArch64::StpPreIndex`,
  `AddRI`, `LdpPostIndex`, "source-bound frame needs independently replayed
  proof"). It is NOT a regression from either merge: the test file
  (`crates/trust-cg-cli/src/emit_proofs_alu_tests.rs`) has not changed since
  `eaf6097f0`, which is an ancestor of round 1's HEAD; upstream's 148 commits
  touch neither `crates/trust-cg-verify/src/source_bound_frame.rs` nor
  `crates/trust-cg-codegen/src/proof_evidence.rs`; and the retained
  2026-09-18 Darwin dev-build report
  already records this exact test as FAILED in three of its four AY/Clean
  toolchain columns and passing only with the coherent pair
  (AY `2657db47c` + Clean `ed21fee39`). It is a solver/checker-pairing red on
  this host, orthogonal to x86-64 vacuity, and it is recorded here as owed work
  rather than hidden.
* **`m141_x86_partial_eightbyte_aggregate_xback`** remains red on one
  combination (`O1 opt_ipv4`, trust-cg on both sides) at the LINK step. The
  pre-merge run is retained at
  `../2026-09-22-linux-x86-64-upstream-merge/bridge/m141-pre-merge-2026-09-21.log`,
  so the pre-existence is checkable from the tree. It was not re-run in round 2.

## ⚑ The race did not stop: `origin/main` moved again during round 2

Fetched at the end of this round, `origin/main` is `34bea0c85`, **13 commits
ahead of `b943790f0`**. They are not merged here. What matters for the next
round, measured rather than guessed:

* **The vacuity surface is UNTOUCHED by all 13.**
  `git diff b943790f0 origin/main -- crates/trust-cg-codegen/src/compiler.rs`
  contains no occurrence of `x86_64_report_is_empty_body`, `call_only`,
  `lir_is_zero_arg` or `proof_certificates_from_x86_64_report` (its only
  compiler.rs commit is `0b34081c3`, RISC-V ELF). The `[TCG-PROOF-465]`
  reconciliation settled here should survive the next merge intact.
* **`crates/trust-cg-lower/src/x86_64_isel.rs`, `crates/trust-cg-opt/src/x86_trap_block.rs`,
  `crates/trust-cg-opt/src/x86_vectorize.rs` and `scripts/check_linux_x86_64.py`
  are untouched by all 13.**
* **ONE head-on duplicate, and it is the branch's headline local work.**
  `e449ee87d bridge(x86-64): lower the two-value PassMode::Pair ARGUMENT lane —
  [TCG-ARG-ABI] 74 -> 2` implements XD-05 independently in the same file
  (`crates/rustc-codegen-trust-cg/src/lib.rs`, +587 lines), with
  `scalar_pair_param_plan` (singular) and `param_input_index_for_mir_arg`, and
  it does NOT contain this branch's `scalar_pair_param_plans` or
  `lower_call_arg_for_input` (grep on `origin/main`: 0 occurrences). Both lanes
  reach the same census number for the class. That reconciliation is the next
  round's main work and it should be decided the same way this one was: by
  measuring both against `core`, not by reading.
* Upstream also reports `[TCG-POINTEE-LANES]` 21 -> 11 (`92025e14b`) and a
  `core` census of 148 on its host, against the 183 here; those are different
  bridges on different hosts and the numbers do not compare directly.

## What this does not measure

No `alloc` or `std` census, no performance run, no Trust-verified compilation of
trust-cg itself, no bridge-corpus floor, no AArch64 or Darwin floor (this host
runs neither), and no full `trust-cg-verify --lib` run. Upstream's Darwin
census (`reports/perf/2026-09-22-darwin-x86-64-census/`) is upstream's
measurement on upstream's host and its dylib is not the one measured here.
