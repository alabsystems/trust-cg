# Complete Linux required regression inventory — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The entire maintained 125-family Linux AArch64 regression inventory was executed
on clean source `884b1e4569f3096eba002aac292b215d52bb17a8`. Result: **PASS**; 125 families passed,
0 failed, and 679 Rust tests reported passing execution. The record
retains every target, including failures; its verdict uses the committed gate's
unchanged classification rules. Ignored, filtered or explicitly skipped execution
cannot count as a passing family.

The source contains the [Linux regression repairs](../2026-09-20-linux-floor-repairs/README.md)
and matches the production source in the [installed development package](../2026-09-20-floor-repair-install/README.md).
The [original full run](../2026-09-20-linux-required-floor/README.md) remains archived
as a failure. This separate run repeats every required family on the repaired source.
This is the required regression inventory, not the complete L01–L14 acceptance
corpus. It does not establish a verified frontend, self-host, general instruction
proof coverage, composed source-to-native correctness, performance qualification,
or a release. All fourteen completion requirements remain OPEN.

## Reproduction and evidence

`harnesses/qualify-cg-repaired-floor-20260920.py` loads the committed gate's
exact target list, classifier, dependency recorder and target environment policy.
It runs each entire integration target with locked, offline Cargo, two build
jobs and one test thread. Each command is independently supervised by the
retained anchored `_oom_guard.py` under a 16 GiB process-group RSS limit,
zero memory grace and a 1,200-second deadline. Output is redirected to retained
files so output-capture limits cannot truncate the test transcript. The external
supervisor substitutes only process execution; it does not replace the test
inventory or weaken the result classifier.

Source, pinned dependency checkout identities and tool hashes are compared
before and after the run. The package's AY/Clean tools are discovered on PATH;
no proof-policy overrides are injected. External LLVM readers are discovered on PATH from the
user-local LLVM installation qualified in the frame-effects record. No
`TRUST_CG_LLVM_BIN` override is supplied to sealed Core admission. Their exact
paths and hashes, stock compiler versions, commands, selected environment,
resource plans, guard receipts, transcripts and test executable identities are
retained. Test executables are hash identified, not copied. Original machine
paths identify the captured installation; reproducing elsewhere requires the
corresponding pinned inputs and LLVM readers.

```sh
python3 scripts/check_linux_aarch64.py --require-clean --require-offline-deps --jobs 2 --max-rss-gib 16 --timeout-seconds 1200 --out /path/outside/source
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-linux-required-floor-repaired
```

The first command is the maintained gate entry point; the retained harness uses
its same suites and verdict policy through the external supervisor described
above. A green result covers only those named regression families.
