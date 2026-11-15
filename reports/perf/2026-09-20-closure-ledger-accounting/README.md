# Closure ledger accounting — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The maintained documentation gate now cross-checks each gap index row against
its section, including the exact status/commit. Duplicate or missing rows,
sections and status fields fail. Headline and summary totals must match the
index, and unresolved means OPEN plus PARTIAL. An overall resolved declaration
cannot hide unresolved gaps. These are consistency checks, not certification
of closure evidence or an L01–L14 acceptance verdict.

The ledger editor now updates the separate summary and unresolved counts as
well as its headline. It also supports reopening a gap after its generated
ALL GAPS RESOLVED headline and refuses duplicate current summaries. Historical
ledgers without the later summary paragraph remain editable; the maintained
document checker still requires the complete current format.

On unchanged base `f509f7072657f9e48b74e40648dbd6e904cc711d`, the old gate
accepts all three mutated copies: zero reported unresolved gaps, zero headline
OPEN/PARTIAL counts, and a changed section commit. The repaired gate rejects
all three and accepts the unchanged ledger. The four exact inputs and both
outcomes are retained. No compiler or proof code changes.

All **55** focused tests pass, including the original ledger editor tests,
new accounting mutation controls, actual maintained-document integration,
acceptance-document checks and completion-plan tests. The documentation check
also passes. The live ledger remains 133 OPEN, 72 PARTIAL and 22 CLOSED out of
227: 205 unresolved; no gap or requirement closes from this repair.

```sh
python3 -m unittest scripts.tests.test_closure_ledger scripts.tests.test_closure_ledger_accounting scripts.tests.test_acceptance_documents scripts.tests.test_completion_plan_docs
python3 scripts/check_documentation.py --check
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-closure-ledger-accounting
```
