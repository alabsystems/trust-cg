# Integrated Linux gates before the nineteenth main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `63ec0f1011249b7e39342576f5d07b00cb07332e`.
It is origin/main `da9871e5c` with two additions:

- **The `.eh_frame` refusals branch.** It was qualified in
  [2026-09-24-linux-eh-frame-wrap-alias](../2026-09-24-linux-eh-frame-wrap-alias/README.md)
  and
  [2026-09-24-linux-eh-frame-hidden-fde](../2026-09-24-linux-eh-frame-hidden-fde/README.md),
  and adds four changes:
  - A narrow pointer whose bits give another file-backed target is refused
    as unproven.
  - A live FDE that a lookup by start would miss is refused.
  - gold's and LLD's range messages are classified.
  - The `CALL26` veneer control links through three linkers.
- **A ledger note** recording the closure audit of L01-P7, L03-P2 and
  L02-P1. All three stay PARTIAL.

origin/main brought two of the owner's commits since
[gates-18](../2026-09-24-linux-integrated-gates-18/README.md):

- **`17fb76d4b`.** The x86-64 bridge's transparent wide-slice newtype
  boundary slot, which changes `crates/rustc-codegen-trust-cg`.
- **`da9871e5c`.** fsym closes four fail-open paths, in `trust-cg-verify`
  and the codegen pipeline's fsym scan.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,006 Rust tests**. The source fingerprint
`c150ec38f357c29e66cbd623f1a9f3c74153f9d4d489eaea9abbebf2942a95ee` was the
same before and after the run. The run took 769 seconds of target wall time
(03:40:37Z to 03:53:44Z). The highest sampled resident set was 293 MiB, in
`link_options`. All four controls were on, and the AY/Clean and dependency
identities did not change.

## Library, CLI and fsym suites

- **Library tests:** codegen passed 4,152 with 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`). Lower passed 1,894.
- **CLI, with `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`:** the binary's tests
  passed 30, `link_options` 30, `output_paths` 8 and
  `trust_ir_binary_container` 4.
- **The owner's fsym change:** `trust-cg-verify --lib fsym` passed 150,
  `fsym_false_positive_corpus` 1, `fsym_real_function_corpus` 1, and the
  CLI's `fsym_flag` 19.

## Bridge lane (`records/bridge25/`)

`scripts/check_linux_aarch64_bridge.py --require-proof-tools` ran on
`012a64ef9`, an earlier merge of this branch onto `17fb76d4b`, to check the
owner's bridge change.
- **TLS:** `tls_thread_local_linux` passed 2/2.
- **C aggregate:** `aarch64_c_fnabi_aggregate_linux` failed only at the
  known L06-P1 `[TCG-PROOF-465]` in `aliased_f32_read`: the unproven
  `StpPreIndex`/`StpRI`/`LdpRI`/`LdpPostIndex` pair opcodes. So the owner's
  bridge change added no new Linux bridge failure.
- **Changes since that run:** only the fsym scan in `pipeline.rs` and
  `trust-cg-verify`, the link driver, tests and docs. The bridge crate is
  the same.

## Known and in progress

A second independent verifier of the `.eh_frame` repair found five
problems, now being repaired:
- **Bypass (medium).** With `-z nosectionheader`, only the FDEs the table
  names are read, so an FDE LLD's table drops is never seen.
- **Pre-existing, not a regression.** gold `--static` C++ programs register
  no unwind information, so every throw aborts.
- **Wrong classification.** A no-table tie is refused as an observed
  failure, but it depends on sort order and should be unproven.
- **Wrong claim.** LLVM libunwind falls back to a linear scan, so a
  zero-range FDE hides nothing from it.
- **Wrong example.** The Qt function the documents name for the hidden FDE
  (`QProcess::setupChildProcess`) is the empty one. The hidden 0x20-byte FDE
  belongs to `QProcess::readData`, a leaf function.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
