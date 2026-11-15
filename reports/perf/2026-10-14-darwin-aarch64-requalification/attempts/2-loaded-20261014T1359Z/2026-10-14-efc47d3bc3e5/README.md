# beat-llvm evidence — `efc47d3bc3e5` on Apple M4 Max (aarch64-apple-darwin)

Retained by `benchmarks/beat-llvm/run.py --retain-dir` at 2026-10-14T14:03:17+00:00 from revision
`efc47d3bc3e58412eae6c867769c394e65b45d60`. Host `Mac.localdomain`: Apple M4 Max (arm64, Mac16,5), Darwin 25.6.0 arm64.

**headline_eligible: NO — NOT EVIDENCE** (load LOADED, dirty=False, mismatches=0, provenance_complete=True, missing=[]; reasons: machine LOADED (1-min load 2.24->8.26 vs threshold 8.0))

Lanes: warm compile (median-of-3 after 1 unmeasured warmup compile); runtime (median-of-5 after 1 warmup run); linked binary size and emitted-code size (linker-map attribution); program and compiler peak RSS (median-of-5); true-cold compile (`--cold`).

CPU policy: `-C target-cpu` default, `-C target-feature` default, lane parity True (bridge adds ['-Zcodegen-backend=$HOME/trust-cg-w19/perf-requalification-L14-P1/crates/rustc-codegen-trust-cg/target-bridge/release/librustc_codegen_trust_cg.dylib']). Affinity: none on a host with heterogeneous cores=True (sysctl hw.nperflevels 2). RSS: getrusage(RUSAGE_CHILDREN).ru_maxrss read by a single-child Python wrapper (benchmarks/beat-llvm/peak_rss.py) after the child is reaped, normalised to bytes; the largest single process in the measured tree, not a sum; sampler cross-check agree=True (rusage 82411520 vs /usr/bin/time -l 82395136); sampler floor 1261568 bytes (readings at or below 2523136 bytes are upper bounds, not resolved values).

| metric | value |
|---|---|
| coverage (intent-to-treat) | 0.0% (0/18 MATCH, 18 INCOMPLETE, 0 MISMATCH) |
| runtime geomean vs LLVM -O3 | — (not measured) |
| scalar runtime geomean vs -O3 | — (not measured) |
| runtime worst vs -O3 | — (not measured) |
| compile warm geomean vs -O2 / -O3 | — / — |
| compile cold geomean vs -O2 | — (not measured) |
| emitted-code size geomean / worst vs -O3 | — / — |
| size (linked file bytes) geomean / worst vs -O3 | — / — |
| program peak-RSS geomean vs -O3 | — (not measured) |
| program peak-RSS floor-bound programs / R1 losses (null = unmeasured) | None / None |
| compiler peak-RSS geomean vs -O2 / -O3 | — / — |
| RSS samples per lane (fewest) / largest relative spread program / compiler | None / — / — |
| missing size/RSS readings | none |

## Files

- `efc47d3bc3e5-20261014T140910Z.json` — the complete results JSON: provenance, per-program outcomes, raw `times_s` samples, ratios, aggregates.
- `efc47d3bc3e5-20261014T140910Z.md` — the per-program table as printed by the harness.
- `outcomes.json` — per-input verdict/reason/label (intent-to-treat: INCOMPLETE and MISMATCH rows included).
- `raw_samples.json` — raw compile/run samples, sizes (linked and emitted, with the emitted-size attribution per section and object), every peak-RSS sample per program and lane with its sampler status, and the cold lane's per-compile cache population.
- `inventory.json` — byte size and SHA-256 of every file here.

This directory is the raw evidence behind one ledger row: append the row with
`python3 scripts/check_perf_ratchet.py --append <results dir>/efc47d3bc3e5-20261014T140910Z.json`; the row's
`retained_dir` names this directory. The numbers describe the recorded revision, host
and session only; they are not a measurement of the current checkout.
