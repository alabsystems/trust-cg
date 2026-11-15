# trust-cg performance-evidence contract

Applies to: the 0.x series. Maintained contract; historical measurements retain
the schema and threshold provenance recorded with their own run.

This contract defines the minimum evidence for a public trust-cg performance
claim. trust-cg itself makes no aggregate compiler or SAT-solver performance
claim.

The executable staged thresholds are in
[`benchmarks/beat-llvm/contract/gates.json`](benchmarks/beat-llvm/contract/gates.json),
with the declared corpus in
[`benchmarks/beat-llvm/progs/manifest.json`](benchmarks/beat-llvm/progs/manifest.json).
Older documents refer to numbered contract sections; use the named sections
below and those executable files. Historical section numbers are not a second
contract.

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
| Platform | Host architecture, CPU model (the processor, never a hostname or board name), CPU feature summary, CPU count, OS, and target triple. |
| Configuration | Optimization level, CPU policy (the `-C target-cpu` / `-C target-feature` values passed, or `default`), core-affinity policy (pinned core or none), and every `TCG_*` / `TRUST_CG_*` variable. |
| Cache | Cold/warm definition, cache path/fingerprint, and before/after entry counts. |
| Sampling | Warmup count, measured run count, raw samples, and aggregation method. |
| Load | Load samples before and after, threshold, and eligibility verdict. |
| Time | UTC timestamp and harness revision/path. |
| Corpus | Manifest digest, category, expected result, and status for every input. |

The checked-in benchmark harnesses may add stricter schema fields. Missing
required data never defaults to an eligible result.

Metric values used for ratios or geometric means must be finite and strictly
positive. A zero, negative, missing, boolean, NaN, or infinite value cannot
silently disappear from an aggregate or satisfy a threshold. Counters and
coverage percentages have their own nonnegative domains; report unavailable
measurements explicitly and preserve their rows in the corpus denominator.

## Correctness comes first

A mismatch, invalid proof/certificate, checker rejection, crash, or divergent
solver verdict voids the affected performance comparison. A fast wrong result
is not a datum. In the beat-LLVM corpus, a normal checksum exit is an integer
in `0..125` (checksum modulo 126). Signal termination, reserved exit statuses,
launch failure and timeout are incomplete runtime outcomes, even when both
lanes fail identically. Retain completed samples and the failure, without a
runtime median or ratio. The evidence reader independently rejects failed,
nondeterministic or disagreeing runtime outcomes stamped as `MATCH`.

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
it refers to the compiler or compiled program and how it was sampled, including
the unit it was normalized to and the sampler's floor: the smallest peak the
sampling path can report. A reading at or near the floor is an upper bound
rather than a resolved value; a comparison with a reading at or below twice the
measured floor resolves neither parity nor a win.

The Linux sampler uses a fresh native image built from
`benchmarks/beat-llvm/peak_rss_linux.c` before measurement. It reads the same
kernel counter after reaping its single command, with a smaller inherited
address space than the Python wrapper. Darwin keeps the Python path. Each run
still measures its own floor and allocation cross-check; native build, exec,
signal or timeout failures produce missing readings, never zero or a fallback
Linux measurement. Linux timeout cleanup kills the sampler's owned process
group and reaps its direct child. This adds no timing or RSS budget to the
measured compiler and changes no predicate, sample count or floor multiplier.

Versioned native RSS method IDs are compatibility keys in the performance
ledger; the unchanged Python path retains compatibility with older Darwin
rows through its description.
Changing that method is INCONCLUSIVE against old-method RSS baselines until
an eligible full-corpus row explicitly declares `--append --new-lineage
'<reason>'`. Runtime, compile time, size and coverage continue to be checked
against the prior baselines; the declaration cannot clear their regressions.
New-method RSS regressions use retained baselines of that method. The harness
also stamps the native source and executable hashes for provenance; those
hashes do not reset baseline compatibility within a method.

Version 2 of `benchmarks/beat-llvm/contract/gates.json` adds size predicates
and preregisters peak-RSS predicates. Its `revisions` entry records the
rationale. The size predicates are not preregistered in the strict sense: every
committed ledger row already recorded a linked-size geomean. The RSS predicates
are preregistered for `aarch64-unknown-linux-gnu`, where no row had a non-null
RSS value.

- Linked size is the linked executable's file bytes. That includes the shared
  standard library, so it does not resolve emitted-code size. S1 (geomean at
  most 1.10x LLVM `-O3`) and S2 (at most 1.00x) apply the July roadmap's
  parity-all and strictly-better size thresholds to that measure.
- R1 is per program and one-sided. The sampler reports the larger of its own
  inherited resident set and the program's peak. A comparison is resolved only
  when both readings are above twice the floor. A bridge reading above both
  the LLVM reading and the floor by more than the parity band is a loss
  wherever it sits. R1 fails on any loss, passes only when every matching
  program's comparison is resolved and none is a loss, and is otherwise
  unmeasured. It cannot show a win, so the program-RSS geomean is reported,
  not gated. On a host where most programs peak below the floor, R1 reads
  unmeasured.
- R2 requires a compiler peak-RSS geomean of at most 1.00x LLVM `-O2` and no
  compiler reading at or below the floor bound.

Version 3 (2026-09-29) defines emitted-code size and makes every peak-RSS
reading a median. Both were preregistered before any committed row measured
them.

- Emitted-code size is the bytes of the linked executable that the system
  linker places from object files the compile produced, counted in code
  sections and read-only data sections, after dead stripping. "Produced by the
  compile" means a relocatable object inside the compile's own fresh, private
  output directory: rustc's codegen units and the allocator shim, emitted by
  the backend under test, including the standard-library generics the crate
  instantiates. Sysroot `rlib` members, system startup objects, dylibs and
  linker-synthesized atoms are excluded. Code is `__TEXT,__text` or `.text*`.
  Read-only data is `__TEXT` constants and literals, `__DATA_CONST,__const`,
  `.rodata*` and `.data.rel.ro*`. The linker's own map (`ld -map` on Darwin,
  GNU `ld -Map` on Linux) states the attribution, so nothing is inferred from
  symbol names. Writable data, zero fill and unwind tables are recorded but not
  counted, because Darwin's compact unwind table is synthesized by the linker
  and cannot be attributed per object. The map comes from a second link of the
  same compile. The reading is refused unless that image's section bytes equal
  the timed binary's, ignoring only load commands, `__LINKEDIT` and the ELF
  build ID. An unsupported map format or a map that attributes no byte to the
  program is a missing reading, never zero. S3 (geomean at most 1.10x LLVM
  `-O3`) and S4 (at most 1.00x) apply the roadmap's size thresholds to this
  measure.
- Peak RSS, for the compiled program and for the compiler, is the exact median
  of N dedicated samples per lane, with N odd and at least 5 for evidence.
  Samples interleave the lanes, run outside the timed loops, and are all
  retained with their sampler status. A lane with any failed or invalid sample
  has no reading; the median of the surviving samples is never used. The
  checker recomputes every median from the retained samples and refuses a
  stamped reading that disagrees. R1's parity band for a program is
  `max(5%, 2 × relative spread)`, the Runtime rule, where the spread is
  `(max - min) / median` of the lane with the larger spread. A range is
  moved by one outlier sample that the median ignores, so a comparison whose
  spread exceeds 0.25 (the runtime lane's resolvability cap) is noisy: a
  bridge median beyond its band is still a loss, but a noisy comparison is
  never a measured parity, and R1 then reads unmeasured, never pass.
- Evidence requires N of at least 5 in provenance and in every retained lane
  of a matching row. A run with no matching row has no reading and is held to
  the provenance N only, as before version 3.

Size and RSS aggregates are fail-closed. One missing or invalid reading on a
matching row makes the aggregate null and names the reading, and the run is
not eligible. A sampler whose calibration fails, or whose `/usr/bin/time`
cross-check disagrees or is present but unusable, qualifies no RSS reading.

Version 4 (2026-10-02) nulls a floor-bound program peak-RSS ratio. The
program-RSS geomean is null unless the sampler is calibrated and no matching
program has a reading at or below twice the floor, and a ledger row keeps no
per-program RSS ratio for a floor-bound program. A ratio of upper bounds is
not a measurement. No predicate, threshold or eligibility rule changed.

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

Gates compare exact aggregates. Rounding is for display only: a value rounded
to a threshold would pass a comparison its exact value fails. The benchmark
checker recomputes every gated aggregate from the per-program table and
refuses a stamped value that disagrees by more than a relative 1e-12, the
allowance for another platform's floating-point library. A predicate whose input is null is
unmeasured, never a pass or a failure. Provenance is self-reported by the
harness and unsigned, including the backend options it records passing.

Eligibility decides only whether a row is evidence. It never exempts a row from
regression checks: a measured regression is a failure whether or not the row
is eligible. Regressions are judged like with like. A baseline measured the
same program set on the same host and target. A run of a subset of the
corpus, or with fewer samples than the contract requires, gets no regression
verdict: it is inconclusive, not a pass or a failure. Only a run of exactly
the declared corpus can be evidence or a baseline. When the declared corpus
changes, its runs are compared with the previous lineage on the programs both
measured where per-program values were kept. Anything further stays
inconclusive until a new lineage is declared explicitly, with a recorded
reason, by an eligible run, which becomes the new lineage's first baseline. A
change of corpus never silently starts a fresh baseline.

Regression baselines span versions of the gate file for metrics whose method
is unchanged: runtime, warm compile time, linked size and coverage. Version 2
changed aggregation from rounded to exact values, which moves a value by less
than 0.05%. Coverage is compared as recomputed from the outcome counts, so a
rounded legacy stamp is never read as a drop. Metrics a version introduces or
redefines have baselines only from rows of that version or later, which the
ratchet enforces: version 2 introduced peak RSS and the resolved-loss count,
and version 3 introduced emitted-code size and redefined both RSS metrics and
the resolved-loss count as medians. Ledger rows condensed under version 3
carry `ledger_row_schema` 2 and their peak-RSS sample count; older rows stay
readable, and a field they lack is unmeasured. A version that changes
a ratcheted metric's method must name the metrics whose baselines it resets.
Each ledger row records the version in force when it was condensed
(`gates_version`; absent means 1), and its stamped gate verdicts are never
re-evaluated under a later version.

An eligible row's source revision, target, and measurement timestamp limit its
scope. The newest committed row is historical evidence for that artifact;
regenerating the ledger view does not make it a current-HEAD result. Requalify
after compiler, dependency, toolchain, corpus, or evidence-policy changes before
using a previous result as a claim about the new configuration.

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
unsound analyze-driver path; it is not evidence for any 0.x release.

Changes to a benchmark threshold, corpus, oracle, timeout, or aggregation rule
must be reviewed and versioned before the next eligible run, never adjusted in
response to the result being measured.

The TY-versus-TLC comparison has its own versioned preregistration,
`benchmarks/ty-tlc/CONTRACT.md` in the development tree (it is not part of the
public snapshot). It defines the corpus, tool identities, oracles, measurement
methods and gate predicates for that comparison. Version 0.1.0 was approved on
2026-10-02, before any measurement. No harness implements it yet and no
measurement exists under it, so no TY/TLC result is eligible evidence until a
complete campaign is retained under that version.
