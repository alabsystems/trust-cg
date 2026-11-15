# beat-llvm evidence — `80b0e03aa609` on Apple M4 Max (aarch64-apple-darwin)

Retained by `benchmarks/beat-llvm/run.py --retain-dir` at 2026-09-29T14:17:09+00:00 from revision
`80b0e03aa6091fdf517fb3e74940fb3cec799ca3` (DIRTY tree). Host `m110-macbook-M4-Max-48GB-1TB.local`: Apple M4 Max (arm64, Mac16,5), Darwin 25.6.0 arm64.

**headline_eligible: NO — NOT EVIDENCE** (load QUIET, dirty=True, mismatches=0, provenance_complete=True, missing=[]; reasons: source tree has tracked edits; non-default backend knobs ['no-proof-certs'] (diagnostic lane))

Lanes: warm compile (median-of-3 after 1 unmeasured warmup compile); runtime (median-of-5 after 1 warmup run); linked binary size; program and compiler peak RSS; true-cold compile (`--cold`).

CPU policy: `-C target-cpu` default, `-C target-feature` default, lane parity False (bridge adds ['-Zcodegen-backend=$HOME/trust-cg/.claude/worktrees/agent-workflow/crates/rustc-codegen-trust-cg/target-bridge/release/librustc_codegen_trust_cg.dylib', '-Ztrust-ir-cg-args=no-proof-certs']). Affinity: none on a host with heterogeneous cores=True (sysctl hw.nperflevels 2). RSS: getrusage(RUSAGE_CHILDREN).ru_maxrss read by a single-child Python wrapper (benchmarks/beat-llvm/peak_rss.py) after the child is reaped, normalised to bytes; the largest single process in the measured tree, not a sum; sampler cross-check agree=True (rusage 82427904 vs /usr/bin/time -l 82395136); sampler floor 1261568 bytes (readings at or below 2523136 bytes are upper bounds, not resolved values).

| metric | value |
|---|---|
| coverage (intent-to-treat) | 100.0% (18/18 MATCH, 0 INCOMPLETE, 0 MISMATCH) |
| runtime geomean vs LLVM -O3 | 0.950 |
| scalar runtime geomean vs -O3 | 1.003 |
| runtime worst vs -O3 | 1.113 |
| compile warm geomean vs -O2 / -O3 | 1.238 / 1.225 |
| compile cold geomean vs -O2 | 3.957 |
| size (linked file bytes) geomean / worst vs -O3 | 1.00060 / 1.00286 |
| program peak-RSS geomean vs -O3 | 0.999 |
| program peak-RSS floor-bound programs / R1 losses (null = unmeasured) | 15 / None |
| compiler peak-RSS geomean vs -O2 / -O3 | 1.197 / 1.196 |
| missing size/RSS readings | none |

## Files

- `80b0e03aa609-dirty-20260929T142117Z.json` — the complete results JSON: provenance, per-program outcomes, raw `times_s` samples, ratios, aggregates.
- `80b0e03aa609-dirty-20260929T142117Z.md` — the per-program table as printed by the harness.
- `outcomes.json` — per-input verdict/reason/label (intent-to-treat: INCOMPLETE and MISMATCH rows included).
- `raw_samples.json` — raw compile/run samples, sizes, peak RSS per program and lane with each RSS sample's sampler status, and the cold lane's per-compile cache population.
- `inventory.json` — byte size and SHA-256 of every file here.

This directory is the raw evidence behind one ledger row: append the row with
`python3 scripts/check_perf_ratchet.py --append <results dir>/80b0e03aa609-dirty-20260929T142117Z.json`; the row's
`retained_dir` names this directory. The numbers describe the recorded revision, host
and session only; they are not a measurement of the current checkout.
