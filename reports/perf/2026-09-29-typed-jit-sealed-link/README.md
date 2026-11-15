# 2026-09-29 — the compiler's AArch64 JIT links sealed functions

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

Host: M5 Max, macOS 26 (Darwin 25.6.0), aarch64-apple-darwin. trust-cg built
with the managed Trust package (`targo 1.99.0-dev (321aaeda7 2026-09-17)`)
through `scripts/trust_cargo.sh`, the explicit `--unverified` lane (no proof
claim about the build). Instruction counts are the evidence; cycles were
recorded on a box shared with other sessions and are indicative only.

## What changed

`f873f13bd` (the compile-speed landing) sealed the **raw** AArch64 JIT: a
function prepared with `Pipeline::prepare_function_checked` carries the
final-stream check its preparation ran and passed, and
`JitCompiler::compile_raw_checked*` does not run that identical check again
at link. The compiler's **own** JIT — `Compiler::compile_module_to_jit`, the
typed lane every embedding runtime reaches through `Compiler` (ay's JIT
kernels in `ay-jit`, TY's typed-host lane) — still prepared bare
`MachFunction`s and its link re-ran every check.

Now each function is prepared sealed (`prepare_function_checked`, and the new
`prepare_function_checked_with_trust_ir_module` for the diagnostic source
form), the check is kept beside it by ordinal, and
`JitCompiler::compile_with_lir_globals_and_encoding_metrics` hands both to the
encoder (`Aarch64JitInputs::with_final_stream_checks`). The encoder skips a
check only when it EQUALS the one it would run (same integrity policy, same
net modes); any other — a verifying JIT's proof-grade policy, a diagnostic
mode changed since preparation, a function the encoder takes through its
exception-table branch — is run exactly as before. `prepared_funcs` is
immutable from preparation to the link, so a kept check describes exactly the
stream the encoder receives. **The emitted bytes are identical by
construction**; only a redundant verdict computation is skipped.
`TCG_NO_SEALED_JIT_LINK` restores the second run (same-binary A/B switch and
kill switch).

## Evidence

Every measurement was taken twice: on the lane before merging `origin/main`
(`f8783ac80`, against main `2e5d18664`; files at this directory's top level)
and on the merged landing tree (`313bca383`, against main `7e1cfe798`, which
had moved the TrustIR pin to `824174a`; files in [`merged/`](merged/)). The
numbers below are the merged tree's; the pre-merge ones agree to within 0.4%.

### 1. The new path, same binary, sealed vs `TCG_NO_SEALED_JIT_LINK=1`

`benchmarks/compile-corpus` gained an on-request lane, `jit-compiler`
(`Compiler::compile_module_to_jit` in `CompilerConfig::jit_fast` at each
module's own level, serial, against the corpus's fake externs; run only with
`--lane jit-compiler`, on every entry that lists `jit-raw`, so default runs
and every committed baseline are unchanged). One binary, 3 repetitions per
entry, steady state = cheapest of repetitions 2..3, `RAYON_NUM_THREADS=1`;
judged by [`analyze.py`](analyze.py) ([`merged/ab-table.md`](merged/ab-table.md),
`merged/sealed.json.gz`,
`merged/unsealed.json.gz`):

**Identity: PASS — 149 entries (146 compiled, 3 refused with the same error
text on both sides): the same verdicts, error texts and emitted code (code
SHA-256, symbol offsets, data-image manifest) on both sides and in every
repetition.** The unsealed side runs the frame net twice per function, the
sealed side once, except `trust-cg-fixture/large_aggregate_args--invoke`
(8 / 8: its functions take the encoder's exception-table branch, which keeps
checking on both sides).

| origin | sealed instr | unsealed instr | sealed / unsealed | per-entry median |
|---|--:|--:|--:|--:|
| ay-jit-matrix (5 kernels) | 431 M | 455 M | **0.946** | 0.951 |
| trust-cg-fixture | 942 M | 992 M | **0.950** | 0.951 |
| ty-prod | 3,908 M | 4,189 M | **0.933** | 0.939 |
| ty-semantic | 120,083 M | 127,469 M | **0.942** | 0.943 |
| all | 125,364 M | 133,105 M | **0.942** | 0.943 |

Pre-merge, the ay kernels one by one: `bcp-propagate` 0.943,
`bcp-propagate-with-decisions` 0.947, `bcp-watched-literal` 0.954,
`bcp-watched-literal-chunked` 0.947, `parent-loop` 0.956.

### 2. Every existing lane, `origin/main` vs this lane

The default corpus run (every manifest lane, 2 repetitions) of `main`'s
`compile_corpus` and of this lane's, `run.py compare`
([`merged/default-compare.md`](merged/default-compare.md); pre-merge
[`default-compare.md`](default-compare.md)): **Identity: PASS — 534 (entry,
lane) pairs, both times: same verdicts, error texts, emitted-code digests and
frame-net counters on both sides, every repetition.** Instructions are
unchanged, as they must be (the raw lanes and AOT do not reach the changed
code): `jit-raw` 1.0004, `jit-raw-checked` 1.0001, `aot-object` 0.9983,
`aot-proofs` 0.9991.

### 3. Tests

* `tests/aarch64_compiler_jit_sealed_link.rs` (new, one test: it counts the
  frame net's process-wide coverage counter): at O0, O1, O2 and O3 the sealed
  link runs the net exactly once less per function than the unsealed one,
  publishes the same `code_slice()` and the same complete
  `published_image_sha256()`, and both answer the fixture's value.
* Every integration test binary of `trust-cg-codegen` that calls
  `compile_module_to_jit` (108 binaries), pre-merge: **853 pass, 17 fail —
  the same 17, with the same panic messages, on main `2e5d18664`**:
  7 ELF-section tests need an `llvm-readelf`/GNU `readelf` this box lacks;
  2 x86-64 dispatcher, 4 `jit_fail_closed_proof_policy`, 2
  `jit_source_bound_arithmetic`, 1 `local_function_address_jit` and 1
  `jit_cert_cache_identity_aarch64` test need proof authority this box's
  toolchain does not admit (`ProofPromotionRejected`, the environmental class
  the compile-speed record names). Merged tree: the new test,
  `aarch64_checked_functions`, `jit_integration`, `e2e_aarch64_globals_darwin`,
  `jit_inline_only_bodies` and `jit_exception_handling` pass (89 tests).
* `scripts/check_fmt.sh`: OK. `targo tippy -p trust-cg-codegen --lib --tests
  --no-deps`: clean. `scripts/check_clippy.sh` over the workspace: red only
  on three findings in `trust-cg-verify/src/fp_bv_lowering.rs`, a file this
  change does not touch (present on main). `python3
  scripts/check_documentation.py --check`: current.

## Who benefits

Every consumer of `Compiler::compile_module_to_jit` on AArch64: **ay's JIT**
(`ay-jit` with its optional `trust-cg-backend` feature compiles its
substitution, LRA-region, CHC-batch, PB-cardinality and SAT whole-loop kernels
through it — `llvm2_substitute.rs:373`, `llvm2_lra_region.rs:395`,
`llvm2_chc_batch_bool.rs:373`, `pb_unit_cardinality.rs:186`,
`sat_whole_loop_guard.rs:142` at ay `HEAD`; the jit-matrix BCP kernels above
are the corpus's stand-in, x0.950), and any runtime that embeds the typed
JIT. TY does not gain from this commit on AArch64 — its native lane is
the raw one, which it moved onto the sealed API in TY
`pin/upstream-adopt-20260928` — but its typed-host lane gains on any host
that routes there.

## Not done

* The exception-table branch of the encoder keeps checking (the `invoke`
  fixture above); sealing it is a separate, small follow-up.
* `JitCompiler::compile_raw_with_globals` has no sealed variant; a raw-lane
  consumer that places globals (TY, if it adopts the JIT data image instead of
  its own address binding) would want `compile_raw_checked_with_globals`.
* The x86-64 JIT (`compile_x86_64_to_jit`) is a separate path with its own
  checks and is untouched.
* The soundness gate (`scripts/soundness_check.sh`) was not run: its
  `--pinned` mode and `proof_gate_strict` are red on this box for reasons that
  predate this change (the compile-speed record names them).
