# Zero-sized Drop receivers and cleanup edges — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bridge now executes supported user destructors for zero-sized whole locals.
An explicit reference, raw borrow, and the destructor of the same place share
one aligned address. Normal return edges from `Invoke` carry the ordinary SSA
arguments needed by loops; empty terminal cleanup blocks no longer request
unused local joins.

This is a native lowering repair on `41ac8d3b52bbbdf62d9419e8c4f847ee421b4e12`,
with the eight source hashes in the qualification receipt. It uses genuine
Trust `ae9c2c1da`, TrustIR `794227ad`, and backend SHA-256
`5ad1aa33d0dd0ad538e191118b041e91d9f7590a79a7cf1c95300cb23cf1d7b5`. Frontend verification and diagnostic codegen
certificates are explicitly disabled. No installed toolchain is promoted.

## Admission and behavior

The existing user-Drop gate still requires a supported struct whose fields are
Copy. A zero-sized whole local receives an entry-block address from the same
per-place map used by its references. Ordinary drop glue runs on both normal
and cleanup paths; the absence of payload bytes does not remove its effects.
Optimized MIR raw borrows use that address too, including a raw-only local
with no reference or destructor that would allocate it beforehand.

Alignment comes from rustc's layout and remains bounded by the frame's
16-byte guarantee. The repair retains the refusal for a 64-byte-aligned local.
Zero-sized array references keep their existing representation. Projected
Drop receivers and other previously unsupported shapes gain no admission.

`Invoke`'s normal destination receives the same explicit block arguments as
other ordinary edges. Unwind entry uses its existing landing-pad convention.
Join parameters are omitted only for blocks with no statements ending in
Unreachable, UnwindResume or UnwindTerminate: these blocks read no MIR locals
and have no successors. Resume still uses its stable exception slot.

## Validation

- Genuine Targo all-targets check and backend build pass. The maintained ABI
  target lists exactly 15 tests; both new regressions execute and pass.
- LLVM and TrustCG at O0–O3 pass 1,272 native checks across the original
  zero-sized try_fold panic reproducer and an expanded corpus. Checks cover
  destructor calls and order, the caught panic payload, address identity,
  alignment 8/16, by-value arguments, raw-only locals and loop counts 0–8.
- The original over-aligned program compiles with LLVM and is specifically
  refused by CG at all four optimization levels. An unrelated failure or a
  timeout cannot satisfy this negative control.
- Eleven unchanged native regressions pass another 4,918,140 checks. Together
  with the new corpus this records 4,919,412 checks, without proof credit.
- The unchanged Linux unwind suite passes both tests. Its execution marker
  records eight LLVM/CG lanes, three executions per lane, three MIR cleanup
  functions, missing-landing-pad controls and four unwind-disabled refusals.
- Root formatting passes. Private formatting adds no differences to the 59
  pre-existing library formatting blocks; new test/fixture sources pass in full.
- Full original core diagnostic: 23 failed roots;
  command exit 1. This is a complete
  census of the original input, not a clean core/self-host build. The 23 failed
  roots and their messages are identical to the preceding published repair.
- Unchanged proof-required C ABI test: exit 101,
  passed=false, TCG-PROOF-465=true.
  The diagnostic runtime passes do not satisfy that proof gate.

## Retained failures and limits

The first prototype repaired the original destructor receiver failure but the
expanded checked loop exposed missing normal-edge arguments and unused joins
on an empty terminal cleanup block. The second prototype passed O0 and then
refused raw-pointer borrows at O1. The final repair passes those same cases
through O3 and also covers raw-only const/mut borrows. These earlier failures
remain archived with their exact source, commands, output and backend hashes.

All product completion gates remain open. This repair does not supply missing
opcode proofs, finish the remaining core roots, widen the stack-alignment
contract or establish full general destructor/unwind support.

## Reproduction and records

The maintained regressions live in
`crates/rustc-codegen-trust-cg/tests/support/zero_sized_drop.rs`, selected as
`zero_sized_drop::` in `aarch64_c_fnabi_aggregate_linux`. The existing broader
cleanup suite is `unwind_cleanup_linux`. Archived scripts bind the compiler,
private sysroot, source, backend and test binaries, require exact test inventory
and native markers, and retain complete command output. `manifest.json`,
`assets.json`, `excluded.json` and `inventory.json` bind every compressed record
and asset. Rebuildable backend/runtime archives are excluded with their hashes;
sources, logs, objects and executables are retained.
