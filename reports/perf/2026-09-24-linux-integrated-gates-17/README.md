# Integrated Linux gates before the seventeenth main push, final source — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `d244dab284bac80fd61bf68feedf34b99c637fbe`.
The source is the one recorded in
[gates-16](../2026-09-23-linux-integrated-gates-16/README.md) (`13e3d898c`)
with two merges added:

- **The owner's `0290f5153`, from origin/main:** fsym now checks
  `MemCopy`/`MemSet` as memory accesses.
- **The llvm-import Linux coverage branch.** It has four parts:
  - **Tests run natively.** Every trust-cg-llvm-import test now compiles
    for an explicit host triple, links with `cc` and runs on this host. The
    13 legs that used to return early, without running anything, now run,
    and `casttest3_e2e` builds on Linux. ELF checks replace the
    Mach-O-only `otool`/`nm` legs.
  - **Floor runner features.** The floor runners gained per-target Cargo
    features (`TARGET_FEATURES`). All 12 importer `driver` targets are
    required on the Linux floor, which grows from 154 to 166 targets, and
    on the Darwin floor, which grows from 201 to 213 rows.
  - **Refusal fixed (`77e6b62e8`).** AArch64 selection folds the stack-slot
    bit-reverse ladder into one `RBIT` and drops the slot's stores. Since
    the raw dataflow-integrity check (TV-3) was enforced on every compile,
    it had refused that fold.
  - **Latent wrong code fixed.** The fold never proved the slot private, so
    a second address of the slot could observe the dropped stores. The fold
    now happens only for a slot shown private over the whole function, and
    each folded store records a fusion link to the `RBIT`. An independent
    verifier found this sound: 14 adversarial LIR cases and 29 LLVM-IR
    variants ran correctly at O0-O3, and 12 of the 14 miscompile with the
    privacy proof disabled.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,003 Rust tests**. Among them are the 12 importer targets, which ran
39 tests built with `--features driver`. The source fingerprint
`edeb37c593a8df7c8bd8d0b7ad257dbb86868a67353da4dcf778f369fe123d6c` was the
same before and after the run. The run took 733 seconds of target wall time
(01:27:04Z to 01:39:32Z), and the highest sampled resident set was 327 MiB.
All four controls were on, and the AY/Clean and dependency identities did
not change.

## Library, CLI and extra suites

- **Library tests:** codegen passed 4,145 with 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`). Lower passed 1,894.
- **CLI:** the binary's tests passed 30, `link_options` 28, `output_paths` 8
  and `trust_ir_binary_container` 4.
- **trust-cg-llvm-import (`--features driver`):** `bitreverse_intrinsics`
  passed 6 and `intmm_arrays` 3.
- **trust-cg-codegen:** `e2e_aarch64_bit_intrinsics_bulk_memory` passed 2
  and `e2e_x86_64_dispatcher` 10.
- **Other targets:** the trust-cg-verify CEGIS and proof-suite targets and
  the race targets passed.

## Known and in progress

The verifier found that the AArch64 view of TV-3 checks only a fusion
edge's shape: a later instruction in the same block. It would therefore
also waive a dropped call or a dropped non-slot store if a selector
recorded such an edge. That is safe today, because only the bit-reverse
fold records edges. A fix that accepts only a store folded into the `RBIT`
root is in progress. The bridge lane was not run; these changes are in
tests, floor scripts, AArch64 selection for this fold, and the frame
decision for zero-byte slots.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
