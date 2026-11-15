# beat-llvm evidence — `f87c5959e2bc` on Apple M4 Max (aarch64-apple-darwin)

Retained by `benchmarks/beat-llvm/run.py --retain-dir` at 2026-09-29T16:27:28+00:00 from revision
`f87c5959e2bc9f73925c71ea23f0ca2a63da3cb0`. Host `m110-macbook-M4-Max-48GB-1TB.local`: Apple M4 Max (arm64, Mac16,5), Darwin 25.6.0 arm64.

**headline_eligible: NO — NOT EVIDENCE** (load LOADED, dirty=False, mismatches=0, provenance_complete=True, missing=[]; reasons: machine LOADED (1-min load 9.96->15.37 vs threshold 8.0); non-default backend knobs ['no-proof-certs'] (diagnostic lane))

Lanes: warm compile (median-of-3 after 1 unmeasured warmup compile); runtime (median-of-5 after 1 warmup run); linked binary size and emitted-code size (linker-map attribution); program and compiler peak RSS (median-of-5).

CPU policy: `-C target-cpu` default, `-C target-feature` default, lane parity False (bridge adds ['-Zcodegen-backend=$SCRATCH/l14p10/after.dylib', '-Ztrust-ir-cg-args=no-proof-certs']). Affinity: none on a host with heterogeneous cores=True (sysctl hw.nperflevels 2). RSS: getrusage(RUSAGE_CHILDREN).ru_maxrss read by a single-child Python wrapper (benchmarks/beat-llvm/peak_rss.py) after the child is reaped, normalised to bytes; the largest single process in the measured tree, not a sum; sampler cross-check agree=True (rusage 82411520 vs /usr/bin/time -l 82395136); sampler floor 1261568 bytes (readings at or below 2523136 bytes are upper bounds, not resolved values).

| metric | value |
|---|---|
| coverage (intent-to-treat) | 100.0% (18/18 MATCH, 0 INCOMPLETE, 0 MISMATCH) |
| runtime geomean vs LLVM -O3 | 0.961 |
| scalar runtime geomean vs -O3 | 1.009 |
| runtime worst vs -O3 | 1.062 |
| compile warm geomean vs -O2 / -O3 | 1.262 / 1.265 |
| compile cold geomean vs -O2 | — (not measured) |
| emitted-code size geomean / worst vs -O3 | 1.1474 / 2.0000 |
| size (linked file bytes) geomean / worst vs -O3 | 1.00060 / 1.00286 |
| program peak-RSS geomean vs -O3 | 0.999 |
| program peak-RSS floor-bound programs / R1 losses (null = unmeasured) | 15 / None |
| compiler peak-RSS geomean vs -O2 / -O3 | 1.109 / 1.108 |
| RSS samples per lane (fewest) / largest relative spread program / compiler | 5 / 0.0094 / 0.0426 |
| missing size/RSS readings | none |

## Files

- `f87c5959e2bc-20260929T163319Z.json` — the complete results JSON: provenance, per-program outcomes, raw `times_s` samples, ratios, aggregates.
- `f87c5959e2bc-20260929T163319Z.md` — the per-program table as printed by the harness.
- `outcomes.json` — per-input verdict/reason/label (intent-to-treat: INCOMPLETE and MISMATCH rows included).
- `raw_samples.json` — raw compile/run samples, sizes (linked and emitted, with the emitted-size attribution per section and object), every peak-RSS sample per program and lane with its sampler status, and the cold lane's per-compile cache population.
- `inventory.json` — byte size and SHA-256 of every file here.

This directory is the raw evidence behind one ledger row: append the row with
`python3 scripts/check_perf_ratchet.py --append <results dir>/f87c5959e2bc-20260929T163319Z.json`; the row's
`retained_dir` names this directory. The numbers describe the recorded revision, host
and session only; they are not a measurement of the current checkout.
