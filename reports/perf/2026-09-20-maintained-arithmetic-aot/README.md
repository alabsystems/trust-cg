# Maintained arithmetic AOT matrix — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The unchanged `scripts/check_aarch64_aot_arithmetic.py` passes its complete
Linux AArch64 denominator on clean source `c45c4d3f049ebd7f601c67b2a7df34e7e890e091`: **48/48 cases,
6,912 native calls, nine independently replayed original certificates accepted,
and all 27 corruption controls rejected**. This supplies the retained execution
missing from gap **L09-P12**; it does not close L09 or any L01–L14 row.

The matrix covers I32/U32/I64/U64 × ADD/SUB/doubling × O0–O3. Each case uses
the installed release CLI to export an object and proof sidecars, audits their
exact object/query/operand binding, links a retained C oracle and executes 144
wrapping-arithmetic calls. Every distinct exported query is independently
re-solved by AY and its Alethe proof checked by Clean. Each checker must refuse
the original runner's hole-rule, removed-empty-clause and opposite-premise
mutations. The runner's denominator, query count, classifier and controls are
unchanged; no skipped or missing case earns credit.

The installed CLI was built from clean `884b1e4569f3096eba002aac292b215d52bb17a8`. Its exact binary identity
and build receipt are in the [installation qualification](../2026-09-20-floor-repair-install/README.md).
Before running, the harness verifies the installed CLI/AY/Clean hashes and that
no workspace source, Cargo manifest, lockfile or build configuration differs between the build and this
qualification revision. The maintained runner independently checks source/tool
identities before and after. This adds a source-build receipt to the bounded
qualification; it does not prove the host compiler correct.

The run invokes the maintained entry point directly with `--require-clean`,
`--max-rss-gib 16` and the exact installed CLI path. Explicit AY/Clean paths
select the same recorded package. Ambient proof controls are stripped by the
runner. An additional anchored supervisor bounds the complete invocation at
16 GiB RSS with zero memory grace; the runner retains its per-command limits.
Full command logs, resource receipts, source/tool identities, objects, native
drivers/executables, sidecars, SMT queries, original proofs and corruption
controls are archived. Large installed tool binaries are hash identified.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-maintained-arithmetic-aot
python3 scripts/check_aarch64_aot_arithmetic.py --trust-cg /path/to/qualified/trust-cg --require-clean --max-rss-gib 16 --out /path/outside/source
```

This is bounded leaf-arithmetic evidence on Linux AArch64. Other instruction
families, linked-image proof binding, signed publication, Darwin qualification,
verified frontend/self-hosting and complete source-to-native composition remain
open. All fourteen platform completion rows remain OPEN.
