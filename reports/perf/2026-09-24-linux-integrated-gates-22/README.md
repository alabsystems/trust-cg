# Integrated Linux gates before the twenty-first main push, with the owner's merge — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `53c0383c8e848e697223bfaa9f5bb7958acaf8c7`.
It is the [gates-21](../2026-09-24-linux-integrated-gates-21/README.md)
source (`24632e79d`: the third and fourth `.eh_frame` repairs) with
origin/main merged. origin/main had brought two of the owner's commits:

- **`fd1068399` fsym.** The pointer model is abstract: pointers are never
  compared, folded, cast or pruned on. Every UB class owes a verdict per
  site. A new differential oracle checks against trust-ir's reference
  interpreter (`fsym_interpreter_oracle`).
- **`8f87b9abb` x86-64 bridge.** Every Rust-ABI `PassMode::Pair` argument
  rides the two-value lane. This changes `crates/rustc-codegen-trust-cg`
  (`lib.rs`, `abi_reg_lanes.rs`).

## Linux regression floor (`records/run29/`)

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,011 Rust tests**. The source fingerprint
`2e3c9ef36926fb1b59be966a32c39eb1538d57bb5b69c5a018e1d635b204e580` was the
same before and after the run. The run took 768 seconds of target wall time
(06:04:34Z to 06:17:37Z). The highest sampled resident set was 341 MiB, in
`link_options`. All four controls were on.

## CLI and fsym suites

- **CLI, with `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`:** the binary's tests
  passed 30, `fsym_flag` 19, `link_options` 33, `output_paths` 8 and
  `trust_ir_binary_container` 4.
- **fsym:** `trust-cg-verify --lib fsym` passed 177. Of the integration
  targets, `fsym_false_positive_corpus` passed 1,
  `fsym_interpreter_oracle` 4, `fsym_real_function_corpus` 1 and
  `fsym_unknown_handling_corpus` 1.

The codegen and lower crates did not change from gates-21's source. Their
library tests (4,154 with 1 ignored, and 1,896) are recorded there.

## Bridge lane (`records/bridge29/`)

`scripts/check_linux_aarch64_bridge.py --require-proof-tools` ran against
backend `4dd79ac1…`, built from this source.
- **TLS:** `tls_thread_local_linux` passed 2/2.
- **C aggregate:** `aarch64_c_fnabi_aggregate_linux` failed only at the
  known L06-P1 `[TCG-PROOF-465]` in `aliased_f32_read` (the unproven
  `StpPreIndex`/`StpRI`/`LdpRI`/`LdpPostIndex` pair opcodes).

So the owner's bridge change added no Linux bridge failure.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
