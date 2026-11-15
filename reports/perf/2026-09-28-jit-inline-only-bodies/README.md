# 2026-09-28 — JIT-path LIR inlining and inline-only runtime bodies: evidence

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

Host: M5 Max, macOS 26 (Darwin 25.6.0), aarch64-apple-darwin, no Rosetta.
trust-cg built with the repository's pinned stock 1.97.1 (`rust-toolchain.toml`;
the Trust toolchain is not this repository's build lane). Instructions retired
are the evidence; cycles were recorded on a box shared with other sessions'
builds and measurements and are indicative only. Design, contract and plan:
`docs/jit-inline-only-bodies.md`.

What landed (each commit on `lane/jit-inline-only`, merged onto `origin/main`
`a9b618476`):

* the JIT runs the shared pre-ISel LIR step (`prepare_jit_lir_module`: OPT-4
  inlining, also through the JIT's exact module edges; the range pass over the
  functions inlining changed), and raw lanes call the same step;
* trust-ir `AvailableExternally` bodies are inline-only templates in the JIT
  step AND at the AOT seam (`Compiler::compile`, every target), admitted
  through one `admit_inline_only_bodies`; every spliced body is a disclosed
  one-definition premise (`inline_only_bodies` on `JitCompilationResult` and
  `CompilationResult`); a compile that makes a proof claim (`emit_proofs`, or
  a verifying JIT validation mode) withholds them all; a body preemptible
  under `pic` is withheld;
* a one-block inline-only body with memory operations (a field read) is a
  template through the CFG-splicing tier (module definitions unchanged);
* structural purity no longer reads a bodied `AvailableExternally` function;
* after this record's measurements, also on `main`: the CompileService
  payloads carry the disclosure; the LLVM importer imports `define
  available_externally` as trust-ir `AvailableExternally`; and AUTHENTICATED
  bodies — `Compiler::with_inline_only_dependencies`: an import row
  `verify_import` accepts, a dependency defining the symbol with the same
  translated LIR — are recorded as discharged premises and are the only
  bodies a proof-claiming compile splices (none of these changes a byte of
  any corpus module; their tests are in their commits);
* kill switches `TCG_NO_JIT_LIR_PREPARE` (the whole JIT step) and
  `TCG_NO_INLINE_ONLY_BODIES` (every inline-only body, both seams).

## Binaries

| name | what | sha256 (prefix) |
| --- | --- | --- |
| `cc-base` | `compile_corpus` at `origin/main` `a9b618476` | `204731204231` |
| `cc-lane` | `compile_corpus` at the lane `0bf34cb23` (= `a9b618476` + this work) | `f074a7078fa7` |
| `jit_inline_only_fast_path` | the JIT example at `0bf34cb23` | `1e04cd7810cc` |
| `aot_inline_only_fast_path` | the AOT example at `0bf34cb23` | `8e099155376d` |

## 1. Byte identity: the kill switch restores the pre-step bytes

`benchmarks/compile-corpus` (247 entries: TY semantic images and production
modules, rustc-bridge programs, the ay jit-matrix kernels, this repository's
fixtures; lanes `jit-raw`, `jit-raw-checked`, `aot-object`, `aot-proofs`;
3 reps, `RAYON_NUM_THREADS=1`). `cc-base` against `cc-lane` run with
`TCG_NO_JIT_LIR_PREPARE=1`:

**Identity: PASS — all 534 (entry, lane) pairs**: same verdicts, error texts,
emitted-code digests and frame-net counters on both sides, every repetition
([`compare-base-vs-lane-killed.md`](compare-base-vs-lane-killed.md);
measurements `base-a9b618476.json.gz`, `lane-killed.json.gz`). The AOT lanes
run the new AOT admission here too (no switch reaches it): no corpus module
carries a bodied `AvailableExternally` function, so it admits nothing and the
236 AOT pairs (138 `aot-object`, 98 `aot-proofs`) are identical. (The same comparison was PASS on 534 pairs against
the earlier bases `5828b4ce6` and `802aee4b4` before this lane last merged
`origin/main`.)

## 2. With the step on

Same base, `cc-lane` as shipped ([`compare-base-vs-lane-on.md`](compare-base-vs-lane-on.md),
`lane-on.json.gz`, per-module step statistics in
`lir-prepare-per-module.tsv`):

* **528 of 534 pairs byte-identical**: every AOT pair (rustc-bridge, ay and
  fixture objects, with and without proofs) and every JIT pair but three
  entries × two JIT lanes.
* The three are TY semantic images where the JIT now inlines module-local
  call sites through their exact edges: `DiningPhilosophers/0` (1 site),
  `Peterson/0` (1), `dijkstra-mutex_LSpec-model/0` (2). Their steady-state
  compile instructions (jit-raw): 3,974.6 → 3,987.1 M (×1.003), 4,069.1 →
  4,065.9 M (×0.999), 8,657.9 → 8,640.1 M (×0.998) — within the harness's
  run-to-run band.
* Over the 139 JIT modules the step ran on 127 (the rest are O0), spliced 4
  sites in total, spliced no inline-only body (no producer emits one yet) and
  the range pass folded nothing.
* **The step's own cost**: bracket `lir_prepare` 26.9 M instructions over the
  whole jit-raw lane (26.6 M jit-raw-checked) — 0.02% of the lane; lane totals
  ×1.0001. (The first cut ran the range pass over every function: 779.7 M,
  0.70% of every JIT compile, 97% of the step, for zero folds — hence the
  restriction to the functions inlining changed.)

## 3. The ay jit-matrix kernels and this repository's fixtures at O1, O2, O3

`measure --opt-level L` on base and lane (step on), 3 reps each
([`levels/`](levels/)): **Identity: PASS** at every level — the 5 ay BCP /
parent-loop kernels × {`jit-raw`, `jit-raw-checked`, `aot-object`} (15 pairs
per level) and the 35 fixture entries × the same three lanes (105 pairs per
level). None of them calls a module-local helper or carries an inline-only
body, so the step changes none of their bytes.

## 4. A non-TY program, JIT: a runtime fast path shipped as an inline-only body

`examples/jit_inline_only_fast_path.rs`: `sum(table, n) = Σ read(table, i & 7)`,
`read` a host helper (bounds check against `table[0]`, load, else the
out-of-line `read_slow`) whose fast path the module carries as an
`AvailableExternally` body. O2, same binary, arm `off` =
`TCG_NO_JIT_LIR_PREPARE=1`, `/usr/bin/time -l`, 3 reps
(`fastpath-jit.tsv`, made by [`fastpath.sh`](fastpath.sh)):

| n = 50,000,000 | instructions retired | cycles elapsed | host definition calls | slow calls | answer |
| --- | --- | --- | ---: | ---: | --- |
| on (spliced) | 818.5 – 820.4 M | 154.3 – 157.0 M | 0 | 18,750,000 | −17,925,000,000 |
| off (every read calls) | 1,173.4 – 1,174.3 M | 380.4 – 382.2 M | 50,000,000 | 18,750,000 | −17,925,000,000 |
| on / off | **−30.1%** | −59% | | | equal, = closed form |

The whole process at n = 0 costs 48–51 M instructions in both arms (one outlier
compile of 109 M in the first `on` repetition), so ≈ 7.1 instructions are saved
per read.

## 5. A non-TY program, AOT: the same fast path in an object file

`examples/aot_inline_only_fast_path.rs` compiles the same module with
`Compiler::compile` for `aarch64-apple-darwin` at O2, twice with ONE compiler
binary — as is, and with `TCG_NO_INLINE_ONLY_BODIES=1` — and each object is
linked (`cc -O2`) with the same C runtime that defines `tcg_read` /
`tcg_read_slow` and checks `sum` against the closed form
(`fastpath-aot.tsv`):

| n = 50,000,000 | instructions retired | cycles elapsed | definition calls | slow calls | answer = reference |
| --- | --- | --- | ---: | ---: | --- |
| on (spliced; object 661 B) | 692.61 – 692.63 M | 98.3 – 111.1 M | 0 | 18,750,000 | yes, every run |
| off (withheld; object 624 B) | 936.37 – 936.39 M | 211.0 – 212.3 M | 50,000,000 | 18,750,000 | yes, every run |
| on / off | **−26.0%** | −50% | | | |

## 6. x86-64: the AOT object executed under an emulator

No x86-64 executor on this host, so [`uc_inline_only.py`](uc_inline_only.py)
compiles the same module for `x86_64-apple-darwin` at O0-O3 in both arms,
links each object with the runtime (`cc -arch x86_64`, link only) and enters
`sum` under the Unicorn x86-64 emulator (unicorn 2.1.4) for n ∈ {0, 1, 5, 7,
8, 13, 1000}, reading the runtime's call counters from the image
(`x86-64-unicorn.tsv`): **56 runs, 0 failures** — every
answer equals the closed form; with the body spliced (O1-O3 `on`) the linked
definition is called 0 times, otherwise once per read; the remainder once per
out-of-range read in every arm. The x86-64 JIT (`compile_x86_64_to_jit`)
receives the same prepared LIR but cannot run here.

## 6b. x86-64 objects: byte identity over the whole corpus

`examples/x86_retarget_census` compiles every one of the corpus's 1,587
modules for `x86_64-apple-darwin` and `x86_64-unknown-linux-gnu` at O0-O3
(12,696 compiles per arm), base `a9b618476` against `main` `e1184cf14`
(all of this work), as collected and with `--externalize` (module-local
functions made `External`, so TY's JIT-shaped images reach the x86-64 object
path): **identical on every row in both modes** — 12,228 objects and 468
refusals as collected, 12,668 objects and 28 refusals externalized
(`x86-64-retarget-identity.txt`). No corpus
module carries an inline-only body, so the AOT admission changes no x86-64
byte, exactly as on AArch64.

## 7. Tests

`battery-summary.txt`: lane vs base `a9b618476`, same
host and toolchain. `trust-cg-opt --lib` 3,706 / 0 (base 3,694 / 0);
`trust-cg-lower --lib` 1,951 / 0 (1,950 / 0) and `tests/inline_only_bodies.rs`
7 / 0; `trust-cg-codegen --lib` 4,461 / 3 with the same 3 failures as the base
(host verification-authority tests); 39 codegen integration targets (the JIT
integration corpus, the proof-policy, cache-identity and ay JIT targets, the
must-refuse corpus, the ELF binding and ARC-ops objects, the new
`aot_inline_only_bodies.rs` and `jit_inline_only_bodies.rs`) with exactly the
base's 18 pre-existing failures after `7f00f6a76` updated the one test that
pinned the old "an `AvailableExternally` body is never spliced" behaviour
(`aarch64_elf_symbol_binding`, 46 / 0); `trust-cg-jit-matrix` 255 / 0 (the BCP
kernels); `trust-cg-cli` must-refuse corpus 1 / 0; `trust-cg-verify`
`soundness_manifest` 1 / 0 and `fsym_real_function_corpus` 12 / 0;
`trust-cg-ws2-import` 30 / 0. The one-block commit (`8208f64e3`) ran
`ir_inline` 37 / 0 and `jit_inline_only_bodies` 10 / 0. `scripts/check_fmt.sh`
OK; clippy reports nothing in any file this work touched (it reports
pre-existing findings in other `trust-cg-opt` and `trust-cg-llvm-import`
files, identical on the base).

## 8. Not done here

* **x86-64 JIT execution** (see §6), and **the soundness gate**
  (`scripts/soundness_check.sh`), whose x86-64 execution legs need Rosetta and
  fail closed without it; `trust-cg-verify` did not change.
* The remaining slices are the plan in the design doc: authenticated
  admission for proof-claiming compiles (the trust-ir half is a function-level
  structural equality across modules), the CompileService payloads, one-block
  memory MODULE definitions, the Core JIT plan, consumers (TY's fast paths;
  Clean's unpinned `ExternCalls` helpers; Clean's RC entry points need the
  authenticated route, since trust-ir's RC pin refuses a body for them), and
  the LLVM importer's `available_externally`.
