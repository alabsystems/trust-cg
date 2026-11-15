# Integrated Linux gates before the twelfth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `e72567e8e0dfb013af61a6ec883d3f07a2a85bb6`:
origin/main `306912d63` plus two increments, each reviewed adversarially.
L03-P2 was also repaired and then checked by an independent verifier.

- **L01-P7: f16 scalar and f16 HFA AAPCS64 boundaries run natively on
  Linux.** The new floor target is `e2e_aarch64_f16_abi_linux`. It runs 29
  shapes in both directions against GCC 13 `_Float16` at O0-O3, making
  11,136 calls and 100,608 bit-exact slot checks. The shapes are:
  - twelve `f16` arguments, four of them on the stack;
  - mixed register banks;
  - HFAs of one to four `f16` members, in registers and on the stack.

  Placement is checked against an independent AAPCS64 model. A profile
  without FP16 refuses `FADD H` by name.
- **L03-P2: CG-owned landing pads, cleanup and unwind run natively on
  Linux.** The new floor target is `e2e_aarch64_eh_linux`. It links ELF
  objects that own landing pads with libstdc++/libgcc_s and with Rust std,
  and checks exact payloads, stages and destructor counts at O0-O3.
  Forty mutated LSDA images (32 C++, 8 Rust) fail, and 20 unmutated
  reference runs pass.

  One product change comes with it (`62234066b`): AArch64 `Resume` now ends
  with `BRK #1` after `bl _Unwind_Resume`, as the x86-64 selector does with
  `UD2`. Without it, the final-layout CFG gave the block a fallthrough edge
  into the next block.
- **Integration follow-up (`2c4a5309f`).** It states the earlier `f16`
  natives' coverage exactly: at most two register arguments and an H0
  return, with C calling CG only.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **151 required target families
and 925 Rust tests**. The new targets passed `e2e_aarch64_eh_linux` 10/10
and `e2e_aarch64_f16_abi_linux` 9/9. The existing EH targets passed
`e2e_aarch64_eh_catch` 7/7, `_eh_invoke_trust_ir` 5/5 and
`_eh_resume_trust_ir` 5/5.

The source fingerprint
`365fd8f8c885b70c500808d3f6f2e0edefe60b85e286f18db25ecc153568ec01` was
identical before and after the run, which took 684 seconds of target wall
time (15:18:43Z to 15:30:17Z). The highest sampled resident set was
185 MiB. All four controls were on, and the AY/Clean and dependency
identities did not change.

## Library, CLI and extra suites

- **Library:** codegen passed 4,113 with 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`), and lower passed
  1,879.
- **CLI:** the binary's tests passed 29/29, `link_options` 16/16,
  `output_paths` 8/8 and `trust_ir_binary_container` 4/4.
- **trust-cg-verify:** the CEGIS and proof-suite targets passed.
- **Former race targets:** both passed at 16 threads.

## Bridge lane

`scripts/check_linux_aarch64_bridge.py --require-proof-tools` rebuilt the
private backend from this source. Its SHA-256 is
`1364e0e2a04f5e2e5ae0c2226961c5a5c713a3ca9cf5fdb5619c9d944c51dee7`, and it
includes the `Resume` change.

- `tls_thread_local_linux` passes 2/2.
- `aarch64_c_fnabi_aggregate_linux` still fails only at the known
  `aliased_f32_read` O0 `[TCG-PROOF-465]` refusal (L06-P1).

## Known findings recorded by these increments (not fixed here)

- **InsertField on an aggregate aliases its source (wrong code).** It lowers
  in place, so `swap(s)` built from two inserts returns `{2,2}` instead of
  `{2,1}` at O0 and O2. A fix is in progress.
- **Darwin stack HFA packing.** On Darwin, LLVM packs stack HFA members at
  their natural size, but the Darwin classifier rounds them to 8 bytes.
  This was not executed on a Mac.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
