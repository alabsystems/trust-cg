# trust-cg performance-evidence contract

Version: v0.1.0, 2026-07-22.

This contract defines the minimum evidence for a public trust-cg performance
claim. v0.1.0 itself makes no aggregate compiler or SAT-solver performance
claim.

## Eligibility

A number is eligible for publication only when all of the following hold:

- the measured source tree is clean and identified by a full Git revision;
- the exact compiler/backend binaries are identified by path and SHA-256;
- toolchain versions, host model, host/target triples, and relevant environment
  variables are recorded;
- both compared lanes run on the same host in the same measurement session;
- inputs, warmups, repetitions, timeouts, and resource limits are preserved;
- the machine is below a stated load threshold;
- every correctness oracle passes;
- unsupported or failed inputs remain in the reported corpus denominator;
- proof/evidence features used by the claimed configuration are enabled and
  recorded.

Scratch timings, dirty-tree runs, loaded-host runs, unstamped historical
numbers, and proof-disabled attribution runs are not headline evidence.

## Required provenance

Preserve at least:

| Field | Requirement |
| --- | --- |
| Source | Full revision, dirty status, diff digest, and untracked count. |
| Binaries | Path, SHA-256, modification time, and build command. |
| Toolchain | Rust/C/linker versions and absolute compiler paths. |
| Platform | Host architecture/model, CPU count, OS, and target triple. |
| Configuration | Optimization level and every `TCG_*` / `TRUST_CG_*` variable. |
| Cache | Cold/warm definition, cache path/fingerprint, and before/after entry counts. |
| Sampling | Warmup count, measured run count, raw samples, and aggregation method. |
| Load | Load samples before and after, threshold, and eligibility verdict. |
| Time | UTC timestamp and harness revision/path. |
| Corpus | Manifest digest, category, expected result, and status for every input. |

The checked-in benchmark harnesses may add stricter schema fields. Missing
required data never defaults to an eligible result.

## Correctness comes first

A mismatch, invalid proof/certificate, checker rejection, crash, or divergent
solver verdict voids the affected performance comparison. A fast wrong result
is not a datum.

For SAT experiments, preserve the SAT/UNSAT verdict, exit code, DRAT artifact
where applicable, and independent `drat-trim` result. For compiler programs,
prefer full stdout/stderr/output-state comparison; reduced exit-code checks
must disclose their collision risk.

Timeouts, solver `unknown`, and unsupported compiler paths are explicit
incomplete results. They must never be silently dropped or counted as proofs.

## Runtime

- Measure wall-clock time after at least one unmeasured warmup unless cold
  behavior is the subject of the claim.
- Preserve all raw samples and report the median plus spread.
- Compare binaries built for the same target and with stated optimization/CPU
  policies.
- Treat differences inside `max(5%, 2 × relative sample spread)` as parity
  within noise unless a stronger preregistered method is used.
- Publish the per-input table with any aggregate.

## Compile time

Define the timed region precisely: frontend-only, backend-only, source-to-object,
or source-to-linked-binary. Do not compare different regions.

Report cold and warm cache behavior separately. A cold run uses a fresh cache
and includes population cost; disabling writes is a `cold_proxy`, not a cold
run. A warm result records a stable cache fingerprint before measurement.

Solver and certificate work that is enabled in the claimed configuration stays
inside the timed region.

## Size and memory

State whether size means linked file bytes, stripped file bytes, executable
segments, or another precisely defined measure. Peak RSS must identify whether
it refers to the compiler or compiled program and how it was sampled.

## Coverage and aggregation

Use intent-to-treat reporting: every manifested program or fixture is a row.
Classify rows as matching, mismatching, unsupported/incomplete, timeout, error,
or invalid evidence.

Any geomean or summary must include:

- matching rows divided by total manifested rows;
- per-category coverage;
- the individual ratios used in the aggregate;
- excluded/non-evidence rows and their reasons;
- the host/target scope.

Never aggregate ratios across different hosts.

## Evidence labels

Performance does not strengthen correctness evidence. Every proof-related row
must retain its actual label, such as exhaustive, statistical, external-SMT
verified, independently replayed, pending, or unchecked. Statistical evidence
is never presented as a proof, and an unsigned artifact is never presented as
an independently certified result.

## Retractions and versioning

If a later correctness finding invalidates a number, retract it everywhere it
was cited and retain a short explanation in the relevant study. The historical
SAT `php-10-9` 6.1× end-to-end claim is withdrawn because it depended on an
unsound analyze-driver path; it is not evidence for v0.1.0.

Changes to a benchmark threshold, corpus, oracle, timeout, or aggregation rule
must be reviewed and versioned before the next eligible run, never adjusted in
response to the result being measured.
