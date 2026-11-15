# wasm32 round 7 (P1 + P2 + correctness) vs `3af946d8f`: two non-evidence harness runs

Date: 2026-10-01 (UTC 2026-10-02T03:19Z and 03:26Z) · Host: Apple M4 Pro,
14 CPUs, Darwin 25.6.0 arm64 · Harness: `benchmarks/wasm-vs-llvm/run.py`,
contract version 2, 144 programs, `-C opt-level=2`, `--jobs 4`, 5 timing
samples per lane and mode · Reference: rustc+LLVM (B1), no B2 lane (no
wasm-opt installed).

**Not evidence.** Both runs were recorded with `evidence-eligible: False` and
neither was appended to `ratchet/ledger.jsonl`. The reasons the harness
stamped, and `scripts/check_perf_ratchet.py` (without `--append`) recomputed
from the provenance:

- runaway processes from other work on the host (a node process at 93 CPU
  hours, a stale native probe binary at 78 CPU hours, a Python process at 19
  CPU hours), although the 1-minute load (3.15-4.66) stayed under the 7.0
  threshold;
- a source tree with tracked edits: `3af946d8f` plus the uncommitted round-7
  patches (`git_diff_sha256` `b8de95506b0ec824…` at run time; only
  documentation and `ratchet/perf_baseline.json` changed afterwards);
- for the before bridge only, a dylib older than its source `Cargo.toml`.

The raw results files are not committed (benchmarks/README.md). They are
identified here by name and SHA-256.

| Run | Bridge dylib SHA-256 | Results JSON (SHA-256) | Results Markdown (SHA-256) |
|---|---|---|---|
| before: bridge built from `3af946d8f` | `cc60b5c0765be115d87da590079cebdbcb075be8b749ee02585fa7586902f2d1` | `3af946d8f6da-dirty-20261002T032653Z.json` (`2285cae808932dd2830371ad241e979fb1f16217be09e9065a816250557430be`) | `…T032653Z.md` (`b3f40dfaf703242d0dd58754753f0fdf561d67f327242c9f910e406cc6be73b1`) |
| after: round-7 bridge | `32bc260b0dfbf30061410ad83dcd3b325e2b181a2cd54ff3696952454124ff6e` | `3af946d8f6da-dirty-20261002T033336Z.json` (`b39de43d2f23f45bdd265c7ec167785193874a9006fdbe0ca093a2ee8c0fba92`) | `…T033336Z.md` (`47adeaeaea29d0ea36e0a82c0cee45d0d44c6b07ee36058e136b0fee7e8f0d1c`) |

The after dylib is the one the bridge's `wasm32_differential` test target ran
(`target/release/deps`, linked by `targo --unverified test --release
--locked`) and the one the 2,283-row wasm32 regression sweep ran. A plain
`targo --unverified build --release --locked` of the same source links a
dylib of a different size (dev-dependency feature unification); that build
was not measured.

Shared identities (equal in both runs, so both share one ratchet toolchain
key): `measurement_sha256` `6c8c7619a84bdffc7d7fd2c03d8516a4500b1d980f6dd2350ed13324471a6809`,
corpus manifest `e180e5f6d251f90c…`, input grid `07d156ffc1ea7574…`, sysroot
`eb3d1911831b88b2…`, rustc 1.99.0-dev (Trust `321aaeda7`), LLD 22.1.2, node
v26.3.0 / V8 14.6.202.34-node.20, bridge knobs `no-proof-certs` only (the
lane's required one), empty `tcg_env`.

## Result

Both runs: 144/144 MATCH, 0 MISMATCH, 0 INCOMPLETE, 2 signed-zero
differences on the two manifest-listed `c7_minmax` exports.

| trust-cg / B1 | before | after | after / before |
|---|---|---|---|
| File bytes (geomean) | 2.769x | 2.589x | 0.935 |
| Code-section bytes (geomean) | 5.723x | 5.269x | 0.921 |
| Static instructions (geomean) | 6.372x | 5.847x | 0.918 |
| Declared locals (total) | 5.625x | 5.886x | 1.046 |
| Static memory operations (total) | 4.780x | 3.453x | 0.722 |
| Dynamic instructions (geomean) | 7.878x | 7.013x | 0.890 |
| Dynamic memory operations (total) | 5.354x | 3.459x | 0.646 |
| Dynamic calls (total) | 1.507x | 1.543x | 1.024 |
| Stack high-water (total) | 1.982x | 1.682x | 0.849 |
| Time, default tiering (geomean of min-of-5) | 2.200x | 2.016x | 0.916 |
| Time, TurboFan only | 2.043x | 1.860x | 0.910 |
| Time, Liftoff only | 3.568x | 3.502x | 0.982 |

57 programs get smaller and none larger, 54 execute fewer instructions and
none more, 6 use less stack and none more. Declared locals rise on 17
programs and fall on 28. The before run reproduces every deterministic
aggregate of the ledger's first wasm32 row (`docs/wasm32_perf_roadmap.md`
section 0). An earlier pair of runs, whose round-7 bridge differed only by the
reserved-helper-name refusal (which no corpus program reaches), produced the
same deterministic metrics for every program.

## Ratchet

Treating the before run as if it were evidence, `wasm_perf_ratchet.ratchet_check`
reports the after run RED on two deterministic metrics, whose floor is 0%:
declared locals (+4.65%) and dynamic calls (+2.40%). Both are the accepted
cost of P1 and P2 and are recorded as a reviewed entry in
`ratchet/perf_baseline.json` (`wasm32_notes`); the first wasm32 evidence row
must therefore be measured at or after the commit that lands round 7.
Section 0.1 of `docs/wasm32_perf_roadmap.md` attributes the moves by program.
