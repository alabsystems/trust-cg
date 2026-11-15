# Linux AArch64 128-bit atomic loads — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bridge admits signed and unsigned 128-bit atomic loads on Linux AArch64
through its existing paired load-exclusive/store-exclusive retry loop. Relaxed
uses LDXP/STXP, Acquire uses LDAXP/STXP, and SeqCst uses LDAXP/STLXP.
The successful store-back makes the observed pair indivisible. Natural result
signedness is preserved. Other targets and 128-bit store/RMW/CAS admission
retain their prior refusals. No selector or proof validator changes.

Qualification binds the combined atomic/iterator base `d14d5bcfa4cd750c5340abd55043a94894549fe4`, seven
source hashes and backend `03b96ecf1f7669075f00e1340ead827f68e5bbe8cc8a1fab15e3ca2c3b7e1f81`. The genuine Trust frontend
is explicitly unverified; native diagnostic codegen omits proof certificates.

- All-targets check and build pass; exactly 28 maintained tests are listed.
- New LLVM/CG O0–O3 value tests cover all six signedness/ordering combinations
  with 393,216 checks. Concurrent LLVM atomic writers and LLVM/CG readers add
  1,572,864 non-tearing observations, with writer progress required during each
  reader loop. Total new native checks: 1,966,080.
- The maintained corpus inspects 48 CG loops for pair registers, ordering bits,
  matching store-back values and status-controlled backward retry. Its inspector
  rejects 144 deliberately damaged instruction sequences. This structural and
  stress evidence is not an AArch64 memory-model proof.
- All six store/add/CAS refusal roots remain at O0–O3; LLVM accepts each input.
- Twenty-four unchanged regressions pass 5,881,740 native checks, including
  320 LLVM-only cases with corresponding expected CG refusals. Combined native
  total: 7,847,820.
- Full core exits 1 with
  9 failed roots and 44 objects.
  Only the i128/u128 atomic-load roots disappear from the previous 11 failures.
  No new or changed remaining failures occur.
- Mandatory proof ABI exits 101; TCG-PROOF-465
  is present: True. This gate remains unsatisfied.
- Root formatting passes. Private library formatting retains 59 preexisting
  differences and adds none; all changed tests pass formatting in full.

The prototype was built before integrating the separately published iterator
repair. Its full-core denominator fell from 12 to 10. The maintained combined
measurement above starts with that iterator repair and falls from 11 to 9.
Earlier loop inspection used GNU objdump despite an incorrect scope label;
the second receipt corrects the label and binds tool/object hashes. Both raw
receipts are preserved. No claimed execution is added for that label correction.

Full core, instruction proofs and conjunctive product completion remain open.
Archives contain exact source, commands, logs, objects, native executables and
receipts. Rebuildable library binaries are listed by hash in excluded.json.
