# Integrated Linux gates before the tenth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `26adeddcee8ad45c166390903b34e5e90d0c5497`.
That source is origin/main `826fdc97a` plus seven merged branches. Each
branch went through a review repair or an independent verifier, or both.

- **The `.eh_frame_entry*` prefix repair.** BFD parses every input section
  whose name starts with `.eh_frame_entry` as compact unwind data, whatever
  the linker script says. The placement table now refuses the whole prefix
  (`[TCG-SECTION-RESERVED]`). A retained list of 21 BFD by-name rules backs
  the derivation test.
- **Six repairs from the first full integration-test sweep on this host.**
  The sweep covered 607 root-workspace test targets at `7cacebb13` and
  found 63 failures outside every gate. The repairs, in order:
  1. The x86-64 link/run probe was a false positive on AArch64 Linux, a
     regression from `f25be0dc4`. It now proves an x86-64 link and run by
     checking the header and running a marker program. On this host it
     skips explicitly, while the compile and object legs still run
     (48 failures).
  2. `e2e_aarch64_copy_coalesce` asserted Darwin red-zone leaves on an ELF
     host. Coalescing never regressed, and both leaf-frame policies are now
     pinned.
  3. `e2e_aarch64_swift_aggregate` built for the host. The swiftcall
     aggregates now compile for Darwin, and the AAPCS64 refusal is pinned
     by name.
  4. JIT tests hard-coded `aarch64-apple-darwin` and are now bound to the
     host spec.
  5. The round-8 x86 classifier fixture was stale, not wrong code. Bisecting
     it found a real compile refusal at O2/O3, which this branch fixes:
     `LateBooleanDiamondConvert` converted a switch header on its last
     compare only, and left an earlier `B.EQ` aimed at a deleted block.
     If-conversion now requires the selected branch to be the header's
     only exit.
  6. The TRUST_IR container fixtures are re-vendored from the trust-ir pin
     `7b9146ba`, and their version window now comes from the pinned reader.
     The rustc bridge now refuses `-Zcodegen-emit-retag` by name
     (`[TCG-EMIT-RETAG]`). Since the move to the Trust compiler it had been
     silently accepted without emitting retag calls.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **148 required target families
and 896 Rust tests**. Source fingerprint
`b0bae385dcc6341de6ceb7bc66019cdbab260f534a2cec72bfc25694933ebe02` was
identical before and after the run. The run took 659 seconds of target wall
time (11:38:38Z to 11:49:46Z), with a highest sampled resident set of
193 MiB. All four controls were on, and the AY/Clean and dependency
identities did not change. `e2e_aarch64_elf_sections` passed 26/26 and
`e2e_aarch64_switch` passed 2/2.

## Library and CLI suites

On the same checkout:

- `cargo test -p trust-cg-codegen -p trust-cg-lower --lib`: codegen 4,113
  passed and 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`); lower 1,879 passed.
- `cargo test -p trust-cg-cli`:
  - the binary's tests passed 29/29;
  - `--test link_options` passed 16/16;
  - `--test output_paths` passed 8/8;
  - `--test trust_ir_binary_container` passed 4/4. It failed 2/4 at the
    seventh push.

## Bridge lane

`scripts/check_linux_aarch64_bridge.py --require-proof-tools` rebuilt the
private backend from this source with the sealed Trust `a62ae50d` package.
The backend's SHA-256 is
`6713bb34b2d7e322af9ab800cb2281b2598193f336dc96d64fb8cbfa1574ebd5`.

- `tls_thread_local_linux` passes 2/2.
- `aarch64_c_fnabi_aggregate_linux` still fails only at the known
  `aliased_f32_read` O0 `[TCG-PROOF-465]` refusal (L06-P1).

The lane verdict is FAIL for that reason only. `records/bridge6/` holds the
report and logs. The backend is hash-identified here, not archived.

## Not included

- **The AArch64 CEGIS budget repair** (`debabccd9`). Its verifier found that
  the structural walk is now bounded only by its quadratic matchers, so a
  follow-up that makes them linear is in progress. Until it lands,
  `e2e_cegis_superopt` still fails 3/7 on this host.
- **The integration sweep.** It will be re-run on this source as its own
  record.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
