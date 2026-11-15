# real-corpus: the larger proofs-on denominator (ledger L14-P7)

The [beat-llvm](../beat-llvm/) contract corpus is 18 programs of tens of
lines. This suite measures a larger, versioned corpus with the production
backend configuration (proof certificates, solver and certificate store on, no
backend knob) and keeps every row, intent-to-treat: refusals, timeouts,
crashes, unavailable inputs and baseline failures stay in the denominator.

| file | what it is |
| --- | --- |
| [`manifest.json`](manifest.json) | The corpus, schema `trust-cg-real-corpus-manifest-v1`. Each row pins its source by digest. Its `selection_rules` and `revisions` say how rows were chosen and how versions change. |
| [`run.py`](run.py) | The harness entry point. `--check-manifest` re-derives every in-repo digest and compiles nothing; `--list` prints the rows. |

## Rows (version 1.0.1, 62 rows)

Version 1.0.1 changes only `selection_rules` and `revisions`; its rows are
1.0.0's, which the [2026-10-14 run](../../reports/perf/2026-10-14-darwin-aarch64-requalification/README.md#6-l14-p7-the-larger-corpus-proofs-on)
measured.

| kind | rows | source and identity |
| --- | ---: | --- |
| `real-program` | 13 | The bridge's shared real-program guests (`crates/rustc-codegen-trust-cg/tests/real_program_corpus/corpus_guests.rs`), `-O3`, run with an exit-status oracle. Identity: SHA-256 of each guest's text. |
| `real-crate` | 27 | crates.io library crates at the version the Trust compiler's own `Cargo.lock` names, with no build script and no required dependency (a hand-picked convenience sample, see below), compiled alone as one `rlib` object (`--emit=obj -Ccodegen-units=1 --cap-lints allow`) at `-O3` with their default features, or with the named dependency-free features where a default feature enables an optional dependency (`aho-corasick`, `hashbrown`). Identity: the `.crate` archive's SHA-256, which is the crates.io checksum. The harness reads the archive from the local Cargo registry cache and refuses it if the digest differs. |
| `trust-sysroot` | 2 | `library/core` at the installed Trust compiler's own revision (`321aaeda7`, the commit `trustc -vV` reports), `-O0` and `-O3`, `RUSTC_BOOTSTRAP=1`, timeout 3,600 s. Identity: the git tree of `library/` at that revision. It needs a Trust checkout (`--trust-checkout`) and is UNAVAILABLE when the driver's commit is not the pinned revision. |
| `scale-ladder` | 20 | `scale_gate.py`'s crates (small to xlarge, 355 to 33,605 lines, `-O3`) and `compile-scaling`'s four shapes at four sizes each (`-O2`, that harness's flags), run with an exit-status oracle. Identity: SHA-256 of the generated text. |

**How the 27 crates were chosen.** They are a convenience sample: hand-picked
from the crates that meet the rule above, before any proofs-on measurement of
them, by no further written criterion, so neither random nor exhaustive. On
the 2026-10-14 host 189 crates meet the rule (applied with this harness's own
`crate_plan` by
[`qualifying_crates.py`](../../reports/perf/2026-10-14-darwin-aarch64-requalification/commands/qualifying_crates.py);
the per-crate verdicts are in
[`qualifying-crates.tsv`](../../reports/perf/2026-10-14-darwin-aarch64-requalification/l14p7-real-corpus/qualifying-crates.tsv)),
and all 27 are among them. A crate-level completion rate or ratio describes
these 27 only; adding the other qualifying crates is a later version's change.

The default timeout is 900 s per compile. Every lane uses `-Cpanic=abort` and
the driver's explicit unverified frontend lane (`-Ztrust-verify=off`), as
every other harness here does.

## Lanes and outcomes

`llvm` is the Trust compiler's own LLVM backend at the row's opt level.
`bridge` is the production trust-cg configuration and decides completion:
one unmeasured warmup compile, a retry when it fails (beat-llvm's BENCH-8
rule: a refusal that compiles on retry is `NONDET-FAILCLOSED`, never a
completion), then N measured compiles. `--diagnostic-lane` adds the bridge
with `no-proof-certs`; it shows what the backend emits with the proof gate
off and is never evidence or completion.

Outcomes: `MATCH` (compiled, every run's exit status equals LLVM's),
`COMPILED` (compiled, every compile writing a readable object; a library has
no execution oracle), `MISMATCH` (P0, exit 1), `INCOMPLETE` (fail-closed twice
with a named `[TCG-...]` refusal), `NONDET-FAILCLOSED`, `TIMEOUT`, `ERROR` (a
compiler crash, a failure with no named refusal, a library compile that exits
0 without writing a readable object, or a harness fault on that row),
`BASELINE-FAILED` (the LLVM lane cannot compile or run the input, or writes no
library object), `UNAVAILABLE`, `INVALID-INPUT`.

Completion rate = (`MATCH` + `COMPILED`) / all manifested rows, overall and
per kind. A library row whose LLVM object holds 0 code bytes is **vacuous**
(`"vacuous": true`): it gives the proof gate nothing to judge. The aggregates
list the vacuous completions and also report the completions with code
(`completed_with_code`, over all manifested rows); a vacuous row has no
code-bytes ratio. Ratios against the LLVM lane (compile wall, CPU including children,
compiler instructions retired, peak RSS, runtime wall/cycles/instructions,
object code bytes for libraries) exist only for completed rows, and an
aggregate is null unless every completed row has the value. Refused rows
keep their named codes, their time to refusal and the LLVM compile time.

## Measurement and eligibility

Every compile and run is wrapped in `/usr/bin/time -l` (Darwin) or `-v`
(Linux). Peak RSS is the largest single process of the tree; CPU includes
every waited-for child; Darwin's instructions retired and cycles count the
compiler or program process itself (the bridge runs inside `trustc`; the AY
solver, Clean checker and linker are children and are not counted).

A run is evidence for this corpus only when: the tree has no tracked edits;
the manifest is the committed `benchmarks/real-corpus/manifest.json` at HEAD
(path and bytes); the backend is no older than its build inputs and loaded in
every bridge compile; no `TCG_*`/`TRUST_CG_*` variable is set; the 1-minute
load is at most ncpu/2 at the start and end of the run and of every row; no
runaway process; the whole manifest ran; N is at least 3 compiles and 5 runs;
every input is available and matches its digest; every row has a known
outcome; no `MISMATCH`; a runnable Clean checker and no DEGRADED bridge
compile. `ineligible_reasons` names each failed condition. An eligible run
feeds no ratchet: the ledger ratchet is defined over the 18-program contract
corpus.

```sh
python3 benchmarks/real-corpus/run.py --check-manifest
python3 benchmarks/real-corpus/run.py --diagnostic-lane \
    --trust-checkout <trust checkout> --out-dir <dir>
```

Path arguments are made absolute before anything runs (`trustc` runs inside
each lane's output directory, where a relative `--dylib` would not load). The
scratch directory (extracted crates, objects, binaries) is removed at the
end unless `--keep-work` is given. Unit tests:
`python3 -m unittest scripts.tests.test_real_corpus_harness`.
