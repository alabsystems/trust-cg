# 2026-09-28 — compile speed, byte for byte

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

Host: M5 Max, macOS 26 (Darwin 25.6.0), aarch64-apple-darwin. trust-cg built
with the repository's pinned stock 1.97.1 (`rust-toolchain.toml`). Instruction
counts are the evidence; cycles were recorded under a loaded box (load average
5 to 70 from other sessions' builds) and are indicative only.

## What was measured

`benchmarks/compile-corpus` (landed with this work): 247 TrustIR modules from
four frontends, compiled in process through the raw JIT lanes (`jit-raw`,
`jit-raw-checked`) and AOT (`aot-object`, `aot-proofs`), recording per module
the verdict or exact error text, the emitted-code digests (relocatable JIT
image, object file, function ranges) and the frame-net verifier's counters,
with per-phase instructions and cycles from `proc_pid_rusage`. 3 repetitions
per entry in one process, `RAYON_NUM_THREADS=1`, steady state = cheapest of
repetitions 2..3. `run.py compare` refuses to report a ratio unless every
repetition on both sides agrees on every identity column.

| file | what |
| --- | --- |
| `compare-main-final.md` | origin/main fa7d0ce12 (harness overlaid) vs this landing's code 8b5c80648 |
| `compare-main-theirs.md` | origin/main vs main + lane/cc-compile-debit's two frame-net commits (53b3b4146, 2a91a0f87), cherry-picked here |
| `../../../benchmarks/compile-corpus/baselines/fa7d0ce12-darwin-arm64.json.gz`, `8b5c80648-darwin-arm64.json.gz` | the two raw measurements |
| `ty-prep-ab.json.gz`, `ty-rows.md`, `measure_ty_prep.py` | TY's native preparation, A/T/B `[patch]` builds (below) |

## Result: the corpus

origin/main fa7d0ce12 → 8b5c80648: **Identity PASS on all 534 (entry, lane)
pairs** — same verdicts, error texts, emitted bytes and verifier counters.

| origin | lane | main instr | final instr | final/main | per-entry median | per-entry geomean |
|---|---|--:|--:|--:|--:|--:|
| rustc-bridge (98) | aot-object | 135,881 M | 44,196 M | 0.325 | 0.747 | 0.707 |
| rustc-bridge (98) | aot-proofs | 131,700 M | 41,491 M | 0.315 | 0.743 | 0.699 |
| ty-semantic (87) | jit-raw | 163,585 M | 124,605 M | 0.762 | 0.819 | 0.806 |
| ty-semantic (87) | jit-raw-checked | 163,585 M | 116,877 M | 0.715 | 0.761 | 0.745 |
| ty-prod (22) | jit-raw | 5,130 M | 3,917 M | 0.764 | 0.843 | 0.812 |
| ay-jit-matrix (5) | aot-object | 655 M | 414 M | 0.632 | 0.636 | 0.634 |
| ay-jit-matrix (5) | jit-raw | 571 M | 430 M | 0.753 | 0.773 | 0.769 |
| trust-cg-fixture (35) | aot-object | 1,445 M | 1,115 M | 0.772 | 0.790 | 0.794 |
| trust-cg-fixture (35) | jit-raw | 1,223 M | 1,079 M | 0.883 | 0.882 | 0.900 |

`jit-raw-checked` is the same compile through the sealed-function API
(`Pipeline::prepare_function_checked` + `JitCompiler::compile_raw_checked*`);
main has no such API, so its column compares against main's `jit-raw`. The
bridge total is dominated by three programs whose compile was super-linear:
`s04_matmul_i32` / `s05_matmul_i64` (38.2 G → 6.3 G, x0.164) and
`s67_method_chains` (19.5 G → 4.8 G, x0.244).

Phase split (all entries): raw JIT `prepare` x0.756, `link` x0.715 (x0.392
sealed), `adapter` x0.948; AOT `compile` x0.331.

Attribution: lane/cc-compile-debit's two frame-net commits alone give x0.989
(bridge aot-object) and x0.969 (TY semantic jit-raw) on the same corpus
(`compare-main-theirs.md`, Identity PASS on 385 pairs); everything else is
this lane.

## At landing: this lane alone, against main with the frame-net commits

main moved to e37412e55 while this was measured, and now carries
lane/cc-compile-debit's frame-net commits itself. Rebuilt both sides (main +
the same harness overlay; the landing merge e4ceba730, which adds the
return-sink summaries, the streamed lowering digest and the ENC-5 name table)
and measured again (`compare-main2-landing.md`, baselines
`e37412e55-darwin-arm64.json.gz` / `e4ceba730-darwin-arm64.json.gz`):
**Identity PASS on all 534 pairs**, so every ratio below is this lane's alone.

| origin | lane | main instr | landing instr | ratio | per-entry median | geomean |
|---|---|--:|--:|--:|--:|--:|
| rustc-bridge (98) | aot-object | 134,119 M | 43,891 M | 0.327 | 0.754 | 0.711 |
| rustc-bridge (98) | aot-proofs | 130,771 M | 41,181 M | 0.315 | 0.742 | 0.700 |
| ty-semantic (87) | jit-raw | 158,207 M | 121,902 M | 0.771 | 0.820 | 0.816 |
| ty-semantic (87) | jit-raw-checked | 158,207 M | 114,180 M | 0.722 | 0.764 | 0.753 |
| ty-prod (22) | jit-raw | 4,947 M | 3,846 M | 0.777 | 0.857 | 0.826 |
| ay-jit-matrix (5) | aot-object | 644 M | 410 M | 0.636 | 0.642 | 0.639 |
| ay-jit-matrix (5) | jit-raw | 551 M | 424 M | 0.770 | 0.788 | 0.782 |
| trust-cg-fixture (35) | aot-object | 1,423 M | 1,106 M | 0.777 | 0.803 | 0.801 |
| trust-cg-fixture (35) | jit-raw | 1,198 M | 1,075 M | 0.897 | 0.900 | 0.915 |

## Result: TY native preparation, 40 semantic-exact rows

TY main 3ef63f18e9 built three ways with `targo --unverified build --profile
release-perf -p tla-cli` through `scripts/with_build_lock.py`, trust-cg
overridden by command-line `[patch]` (never committed):

* **A** — TY's pin, trust-cg 318f896ed.
* **T** — 318f896ed + lane/cc-compile-debit's two frame-net commits,
  cherry-picked (d99a21b37, an ancestor of
  `origin/evidence/compile-speed-on-318f896ed`).
* **B** — T + this lane's commits, cherry-picked onto 318f896ed
  (`origin/evidence/compile-speed-on-318f896ed`, 92eb6fbb5): provenance,
  SROA facts + users index, frame-net sorted cells, ENC-5 routing, linear
  scan, scheduler DAG, FxHasher (three steps), operand-role memo. Not in B:
  the sealed API (TY does not call it yet), the compact dataflow identity (AOT
  only), the return-binding summaries.

Each observation: `ty <census argv> --source-compile-diagnostic --max-states 1`
with `TY_DISABLE_ARTIFACT_CACHE=1` and a fresh `TY_CACHE_DIR`, so every run
compiles the semantic image cold (checked: every run logs `native image
compiled (O2)`, none `from a cached artifact`), under `/usr/bin/time -l`,
3 repetitions, binaries interleaved in rotating order, the whole run holding
the measure side of `~/.ty/build.lock`. Rows: the 40 `exact_rows` of TY's
`reports/perf/2026-09-25-semantic-lane-standard-instance/census.json`, argv
from the same file.

**Identity:** on all 40 rows, every repetition of A, T and B produced the same
digest of the JSON result, the statistics (timings removed) and the
`source_compile_diagnostic` provenance; all exited 0 with the shadow status
`observed_prefix_matched`.

Whole-process instructions (median of 3 per row, summed):

| | A | T | B | T/A | B/A | B/T |
|---|--:|--:|--:|--:|--:|--:|
| instructions | 153,216 M | 149,746 M | 120,871 M | 0.977 | **0.789** | 0.807 |
| cycles (loaded box) | 49,949 M | 49,316 M | 41,627 M | 0.987 | 0.833 | 0.844 |

Per row B/A: median 0.810, geomean 0.816, range 0.706–0.923 (`ty-rows.md`).
These are whole-process counts — parsing, the interpreter prefix and output
are in both sides — so the native-preparation share fell by more than 21%.

## The changes, and how each was checked

Every change is an exact rewrite of the computation it replaces; none removes
or weakens a verification pass. Each has an oracle — the replaced code kept
verbatim in tests, or a randomized differential — and each was admitted only
with Identity PASS on the whole corpus.

| change | hotspot it removed | oracle |
| --- | --- | --- |
| provenance merges rewrite only the lists they change | quadratic resync per merge (matmul 38 G) | `ScanReference` over random merges |
| SROA dominators + positions once per run, on bit sets; vreg-users index | per-slot dominator recomputation (4.4% of TY); per-alias whole-function user scans | verbatim reference dominators/positions; `users_index_equals_the_per_vreg_scan` (2,000 random functions) |
| frame net: sorted cell vector, in-place join over differing middles | `post_ra_spill_slots::evaluate`, top frame of the raw JIT | `MapCells` reference, randomized joins |
| ENC-5 routing on borrowed names | per-bit string allocation in value-decode proofs | `reference_exact_routing` on random expressions |
| linear scan: range-side reserved search over a memoized union | per-candidate reserved scan | reference interference oracle |
| scheduler DAG edges in a bit matrix | hash-set edge dedup | `HashSetEdges` reference, random regions |
| FxHasher (shared `trust_cg_ir::fast_hash`) for the AArch64/shared passes, adapter, codegen spill/layout maps, CFG fingerprint | SipHash: 8.2% of TY, 6.4% of bridge samples | output order-independence is already required (std maps are per-instance randomly seeded); corpus identity |
| operand-role memo per opcode behind a per-count truncation check | `fill_operand_roles`, 3.3% of TY | memo vs direct classification, every special-cased opcode family |
| sealed prepared functions skip an identical link re-check | raw JIT link re-ran the final-stream check | `aarch64_checked_functions` (same bytes; check runs once; re-runs on a mode change) |
| compact LIR identity for the raw dataflow pairing digest | pretty-printed identity rendering | `verifier_identity_renderings` (canonical unchanged; compact separates exactly as canonical) |
| lowering-provenance digest streamed into FNV; ENC-5 register names from a table (landing table only) | a `format!` per selected instruction / per decoded operand | `compute_debug == compute(format!(..))`; `xvar_spells_the_formatted_name` |
| return-sink bindings on per-block summaries (landing table only; x0.989 on TY semantic) | per-pass per-instruction effect re-evaluation (2.6% of TY) | verbatim reference on 6,000 random CFGs |

## Tried and dropped

* Masking spill facts in the frame net: no measurable gain; reverted.
* Fusing the two post-RA checking passes into one walk: x0.998; reverted as not
  worth the coupling.
* A crate-wide FxHasher conversion of the x86-64 passes and `mach_view`: not
  landed — this host's corpus cannot check x86-64 output byte for byte.

## Gates

`scripts/check_fmt.sh` clean; `scripts/check_clippy.sh` clean (tippy);
`scripts/check_documentation.py --check` clean. Library tests of trust-cg-ir,
-regalloc, -opt, -lower (all targets) and trust-cg-jit-matrix pass. Failures
seen here are environmental and identical on origin/main fa7d0ce12 in the same
lane: 4 trust-cg-verify and 3 trust-cg-codegen library tests need an admitted
AY / the discovered verification authority (stock toolchain), and the
soundness gate's `proof_gate_strict` gets incomplete certificates from the
toolchain AY (0.26.0 build 9624) — reproduced on main with
`scripts/trust_ay_cargo.sh`. `--pinned` also fails on `soundness_revs.lock`
drift, which predates this work.
