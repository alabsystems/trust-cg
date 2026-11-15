# beat-llvm evidence — `b30d99c81778` on Apple M4 Max (aarch64-apple-darwin)

> **Payloads out of tree**: the JSON files this record names were removed after
> commit `d4e3a331a` under the durable evidence policy; their SHA-256 are in
> [the record's README](../README.md); recover one with `git show d4e3a331a:<path>`.

Retained by `benchmarks/beat-llvm/run.py --retain-dir` at 2026-10-01T00:17:02+00:00 from revision
`b30d99c817784b2d6a46149a5438dfda67c14614`. Host `m110-macbook-M4-Max-48GB-1TB.local`: Apple M4 Max (arm64, Mac16,5), Darwin 25.6.0 arm64.

**headline_eligible: NO — NOT EVIDENCE** (load LOADED, dirty=False, mismatches=0, provenance_complete=True, missing=[]; reasons: machine LOADED (1-min load 29.42->10.69 vs threshold 8.0); non-default backend knobs ['no-proof-certs'] (diagnostic lane))

Lanes: warm compile (median-of-3 after 1 unmeasured warmup compile); runtime (median-of-5 after 1 warmup run); linked binary size and emitted-code size (linker-map attribution); program and compiler peak RSS (median-of-5).

CPU policy: `-C target-cpu` default, `-C target-feature` default, lane parity False (bridge adds ['-Zcodegen-backend=$SCRATCH/w13b4/after.dylib', '-Ztrust-ir-cg-args=no-proof-certs']). Affinity: none on a host with heterogeneous cores=True (sysctl hw.nperflevels 2). RSS: getrusage(RUSAGE_CHILDREN).ru_maxrss read by a single-child Python wrapper (benchmarks/beat-llvm/peak_rss.py) after the child is reaped, normalised to bytes; the largest single process in the measured tree, not a sum; sampler cross-check agree=True (rusage 82477056 vs /usr/bin/time -l 82296832); sampler floor 1277952 bytes (readings at or below 2555904 bytes are upper bounds, not resolved values).

| metric | value |
|---|---|
| coverage (intent-to-treat) | 100.0% (18/18 MATCH, 0 INCOMPLETE, 0 MISMATCH) |
| runtime geomean vs LLVM -O3 | 0.889 |
| scalar runtime geomean vs -O3 | 1.034 |
| runtime worst vs -O3 | 1.153 |
| compile warm geomean vs -O2 / -O3 | 1.438 / 1.391 |
| compile cold geomean vs -O2 | — (not measured) |
| emitted-code size geomean / worst vs -O3 | 0.9514 / 1.6016 |
| size (linked file bytes) geomean / worst vs -O3 | 1.00060 / 1.00286 |
| program peak-RSS geomean vs -O3 | 0.999 |
| program peak-RSS floor-bound programs / R1 losses (null = unmeasured) | 15 / None |
| compiler peak-RSS geomean vs -O2 / -O3 | 1.111 / 1.110 |
| RSS samples per lane (fewest) / largest relative spread program / compiler | 5 / 0.0377 / 0.0267 |
| missing size/RSS readings | none |

## Files

- `b30d99c81778-20261001T002319Z.json` — the complete results JSON: provenance, per-program outcomes, raw `times_s` samples, ratios, aggregates.
- `b30d99c81778-20261001T002319Z.md` — the per-program table as printed by the harness.
- `outcomes.json` — per-input verdict/reason/label (intent-to-treat: INCOMPLETE and MISMATCH rows included).
- `raw_samples.json` — raw compile/run samples, sizes (linked and emitted, with the emitted-size attribution per section and object), every peak-RSS sample per program and lane with its sampler status, and the cold lane's per-compile cache population.
- `inventory.json` — byte size and SHA-256 of every file here.

This directory is the raw evidence behind one ledger row: append the row with
`python3 scripts/check_perf_ratchet.py --append <results dir>/b30d99c81778-20261001T002319Z.json`; the row's
`retained_dir` names this directory. The numbers describe the recorded revision, host
and session only; they are not a measurement of the current checkout.
