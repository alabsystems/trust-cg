# Integrated Linux gates before the fourth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `d5b5e5382ef2562cad34159c16df1457f0f2a27d`.
That commit is origin/main `be25d1ba6` plus three merged branches:

- trust-ir v45 function visibility and explicit function sections on AArch64
  ELF (L02-P1, L02-P3).
- The explicit BTI/PAC link refusal (C-01).
- The repair that stores the 2026-09-22 AOT archive's objects as `.o.gz`.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **145 required target families
and 839 Rust tests**. Source fingerprint
`70d2ee2986612134dc419d61b62532402da67064be709d8240e7614469c9724b` was
identical before and after. The run took 550 seconds of target wall time
(05:06:48Z to 05:16:04Z) with a highest sampled resident set of 234 MiB. All
four controls were on, and the AY/Clean identities were unchanged. The
changed targets passed: `aarch64_elf_symbol_binding` 19/19,
`e2e_aarch64_elf_sections` 19/19, `e2e_aarch64_elf_stack_zero_fill` 9/9 and
`link_options` 8/8.

## Library suites

On the same checkout, `cargo test -p trust-cg-codegen -p trust-cg-lower --lib`
passed: codegen 4,069 passed and 1 ignored (the pre-existing
`raw_machir_request_cache_real_exhaustive_campaign`), lower 1,879 passed.

## Bridge lane

`scripts/check_linux_aarch64_bridge.py` rebuilt the private backend from this
source with the sealed Trust `a62ae50d` package. The backend SHA-256 is
`06bde318751d700000d80e9ee1d78eac01d6b54528fda5c1f7c32ff713fae7b5`. The
changed adapter compiles into it. `tls_thread_local_linux` passes 2/2.
`aarch64_c_fnabi_aggregate_linux` still fails only at the known
`aliased_f32_read` O0 `[TCG-PROOF-465]` refusal (L06-P1). The lane verdict is
FAIL for that reason only.

## Archive integrity

Every Linux evidence archive in this tree from 2026-09-22 onward passes
`scripts/check_evidence_archive.py` on a clean `git archive` export of this
commit, not only in a working tree. That check found the AOT archive's
git-ignored objects, which this batch repairs.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
