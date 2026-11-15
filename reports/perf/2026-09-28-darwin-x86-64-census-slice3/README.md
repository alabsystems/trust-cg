# Darwin x86-64 `library/core` census — slice 3 (direct calls), 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

One proof row, same host and toolchains as the
[2026-09-27 census](../2026-09-27-darwin-x86-64-census/README.md): native
stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridge built on this host
against the stage-1 `stage0-sysroot` (`targo --unverified build --release
--locked`), `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU, proofs
required (the bridge default), `-Ztrust-ir-cg-args=x86-body-trace`. Nothing
here is a completion claim.

| Row | trust-cg | Mode | Failed roots | Distinct reasons |
| --- | --- | --- | --- | --- |
| `core-x86_64-darwin-O0-proof-slice3-c2a7639c0` | `c2a7639c0` | proofs required | 2887 | 2 |

## What was measured

- **Tree.** The bridge was built from the committed slice-3 tree
  `c2a7639c0` (branch `feat/x86-source-bound-body-slice3-calls`, clean
  worktree). The follow-up review commit changes tests, comments and
  documentation only, so this row also measures its production code.
  `backend.sha256` is the dylib's digest. The census tool's own
  `provenance.json` records `trust_cg_rev` = `de1f19099`: that is the
  `~/trust` superproject's pin, not the measured tree. The table above
  names the tree.
- **Replay tools.** The bridge build recorded the toolchain AY
  (`ay 0.27.0+build.10530`) of its build compiler's sysroot,
  `stage0-sysroot`. The census sets no checker override, so the bridge uses
  the default discovery: first the `clean` of the toolchain that owns the
  AY, then `store/clean/current`. `stage0-sysroot` ships no `clean`, so on
  this host the discovery resolves `store/clean/current` ->
  `~/clean-checker/bin/clean` (Clean `5f09e36c`, sha256 `949365b6…`), the
  checker the qualification test records. The census record itself does not
  log the resolved checker.
- **Memory.** No `[TCG-COMPILE-DRIVER]` resource-budget refusal occurred.

## Result

2887 failed roots: 2885 `[TCG-PROOF-465]` and 2 `[TCG-REGALLOC-063]`
(`atomic_load::<i128/u128>`). The baseline is the slice-2 row
`core-x86_64-darwin-O0-proof-slice2-d0278d3b9` on `main` (3078 roots, the
same two classes). Compared with it:

- **191** roots newly promote.
- **0** roots newly fail. Every failed root here has a byte-identical
  record in the baseline.

The body trace shows 494 functions whose theorem replayed `Valid` and 10
with `replay=none`. The 10 are shapes the admitted AY/Clean pair does not
certify: `i32::wrapping_mul` (a 32-bit multiply) and nine
`NonNull::add`/`offset` monomorphizations (scaled address arithmetic). No
`[TCG-SOURCE-BOUND-X86-MISMATCH]` occurred.

The trace refuses 55 functions as having no observable
(`X86BodyUnsupported::NoObservable`): the `#[track_caller]` panic helpers
(`panic_const_*`, `option::unwrap_failed`, `cell::panic_already_borrowed`,
...) and the `do_panic` bodies. Under `-Cpanic=abort` none of them returns a
value or passes an argument to its call (`abort()`). The helpers' incoming
`&Location` is only a dead copy, and that `MovRR` is the uncovered row that
keeps each one a failed root.

## Reproducibility

An earlier run of this census used a bridge built before the last edit to
`x86_source_bound_body.rs`. The dylib was built at 03:31 and the module was
last edited at 03:49. That run gave the same 2887-root set and 191 / 0.
The rebuild from the committed tree (incremental: trust-cg-verify, then
trust-cg-codegen, then the bridge, 11 min 46 s) reproduces it exactly.

The implementer's pos/neg/bool/lib corpora also give identical
`x86-body-trace` output and exit codes under both dylibs.

Wall time is not a measurement on this shared four-core host. The same
root set took 785 s and 911 s in the two runs, and two baseline-count runs
took 949 s and 842 s.

The row keeps `gap_table.md`, `provenance.json` (home directory shortened to
`~`, the session scratch directory to `<scratchpad>`),
`failed_roots.jsonl.gz` and the bridge's `backend.sha256`.
