# compile-corpus — compile time, byte for byte

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

The regression guard for trust-cg's own compile time. It compiles a fixed
corpus of TrustIR modules from several frontends through the backend's real
compile lanes and records, for every module:

* the **verdict** (compiled, or the exact error text),
* the **output identity** (SHA-256 of the emitted machine code — the
  address-free relocatable JIT image, or the object file — plus every
  function's range),
* the **frame-net verifier's counters** for the compile (streams analyzed,
  declined by reason, spill reloads and exits checked, violations),
* the **cost**: instructions retired and cycles elapsed of each phase bracket,
  read in process from the kernel's counters (`proc_pid_rusage`,
  `RUSAGE_INFO_V4`; macOS only — elsewhere the columns are zero and
  `/usr/bin/time` is not a substitute for per-phase numbers).

A compile-speed change is acceptable only if `run.py compare` reports
**Identity: PASS** on the whole corpus: every module's verdict, error text and
emitted bytes, and every verifier counter, equal before and after. Only then do
its instruction columns mean anything.

```sh
targo --unverified build --release -p trust-cg-jit-matrix --bin compile_corpus
python3 run.py measure --bin ../../target/release/compile_corpus --out B.json --reps 3
python3 run.py compare baselines/<rev>.json.gz B.json --table compare.md
python3 run.py profile --bin ../../target/release/compile_corpus --out prof.txt \
    --filter ty-semantic/Barriers/0 --reps 3 --seconds 60
```

`measure` runs one process per entry, compiles each entry `--reps` times in it
and keeps every repetition; `compare` checks that every repetition agrees with
the others before comparing the two sides, and reports the steady-state
repetition (the cheapest of repetitions 2..N). `profile` runs `sample` and
attributes every working sample (idle pool threads excluded) to the innermost
compile phase on its stack — the split of a bracket into optimization, register
allocation, each verification pass, encoding and link.

### Pricing a JIT tier

`measure --opt-level <L>` compiles every module at `L` instead of its
producer's level (recorded as `opt_level_override` / `compiled_opt_level`), and
`tier-cost` compares such a run with a production-level run of the same binary:

```sh
python3 run.py measure --bin <compile_corpus> --lane jit-raw --opt-level O0 --out low.json
python3 run.py measure --bin <compile_corpus> --lane jit-raw --out top.json
python3 run.py tier-cost low.json top.json --table tier-cost.md
python3 run.py profile --bin <compile_corpus> --lane jit-raw --opt-level O0 --filter ty-semantic/ACP_NB_TLC/0 --out prof.txt
```

The bytes of the two runs differ by design, so `tier-cost` checks instead that
each run agrees with itself across repetitions and that both reach the same
verdict for every (entry, lane), then reports steady-state instructions per
origin and per entry: what the first tier of a JIT tier-up plan
(docs/jit-tier-up.md) costs against compiling
the top tier up front.

## The corpus (`corpus.json`)

| origin | what | how it was produced | lanes |
| --- | --- | --- | --- |
| `ty-semantic` | TY's semantic images (whole-spec native lowering) and their callout batches, 40 strict-exact TY rows | `collect_ty.py`, from TY replay artifacts of `--source-compile-diagnostic --max-states 1` | `jit-raw` |
| `ty-prod` | the modules TY's shipping configuration compiles (fused BFS levels, callout batches) | `collect_ty.py`, production default with `--max-states 1` | `jit-raw` |
| `rustc-bridge` | ordinary Rust programs as the rustc bridge hands them to trust-cg, one module per codegen unit, with the bridge's compile settings | `collect_bridge.py`: beat-llvm, fmt-selfhost and shape-coverage programs and the scale gate's 200-function program, compiled with `-Ztrust-ir-cg-args=dump-trust-ir=DIR` | `aot-object`, `aot-proofs` |
| `ay-jit-matrix` | the ay BCP propagation kernels and the parent-loop kernel the jit-matrix compiles | `collect_fixtures.py` (`compile_corpus dump-builtin`) | `jit-raw`, `aot-object` |
| `trust-cg-fixture` | this repository's TrustIR fixtures: the real-function fsym corpus, the aggregate/ABI corpora, the fuzz programs | `collect_fixtures.py` (`compile_corpus rebin`) | `jit-raw`, `aot-object` |

Lanes:

* `jit-raw` — the AArch64 raw JIT lane as an embedding runtime drives it:
  adapter → `Pipeline::prepare_function_with_metrics` (JIT-latency allocator
  profile) → `JitCompiler::compile_raw_relocatable`. Brackets: `adapter`,
  `prepare`, `link`.
* `aot-object` — `Compiler::compile` to an object file, serial, proof
  certificates off. Bracket: `compile`.
* `aot-proofs` — the same with proof certificates on, the rustc bridge's
  production setting. On aarch64-apple-darwin every module is refused at proof
  promotion ([`reports/perf/2026-09-28-darwin-aarch64-campaign`](../../reports/perf/2026-09-28-darwin-aarch64-campaign/README.md));
  the refusal text is part of the verdict and must not change.

Every module file is a committed copy: editing the program or fixture it came
from does not change the corpus a baseline was measured on. Re-collecting is a
deliberate, reviewed change of the corpus and of its baseline.

## Baselines (`baselines/`)

`<rev>-<host>.json.gz` is a `measure` run of the named trust-cg revision on the
named host, with the load average recorded at both ends. Instruction counts are
host- and toolchain-specific; the identity columns are not.

## What it does not measure

It is not the proof lane's cost (no certificate is minted in `jit-raw` or
`aot-object`), not rustc's frontend and not a runtime benchmark. A module whose
lane refuses still costs what it cost up to the refusal, and that is what its
row reports.
