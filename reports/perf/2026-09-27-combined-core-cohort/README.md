# Three core lowering repairs on the incoming dependency cohort — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bridge now admits Linux AArch64 signed/unsigned 128-bit atomic loads,
computes full-width unsigned 128-bit carrying multiply-add, and reads nested
aggregate operands from their memory slots. These repairs are integrated with
remote main b23ecd365, TrustIR 524d8ded9549722a0fd1b10c5aa9736554513f67,
Clean 414913cced529d1367f45cde3d435a78218dfa47 and the incoming JIT changes.
No proof validator or instruction selector is weakened.

Qualification binds parent `1ab7d1cec25a2a02bf433a02edbc96517e20771d`, seventeen source/manifest/lock hashes
and rebuilt backend `9d6c7efcac3e89bfd760be9a5a5cc88715a90be5040cd22a18d861dd113f6d63`. The genuine Trust frontend is
explicitly unverified; native diagnostic codegen omits proof certificates.

- All-targets check and build pass; exactly 30 maintained tests are listed.
- Atomic LLVM/CG O0–O3 value and contention tests pass 1,966,080 checks.
  Relaxed/Acquire/SeqCst use the existing LDXP/STXP, LDAXP/STXP and LDAXP/STLXP
  retry loops respectively. The inspector checks 48 loops and rejects 144
  deliberately damaged sequences. All six store/add/CAS refusal roots remain.
  Structural inspection and stress observations are not a memory-model proof.
- Wide multiply-add passes 1,157,120 checks across 231,424 LLVM/CG O0–O3 cases.
  Four 64-bit partial products and bounded U128 carry accumulators produce the
  low/high 128-bit result. An independent 32-bit schoolbook oracle checks all
  four-argument combinations of twelve boundary values plus 8,192 deterministic
  wide cases per execution. Tuple, individual halves and guarded caller-memory
  outputs are covered, alongside unchanged u64 behavior.
- Iterator-wrapper construction passes 166,400 LLVM/CG O0–O3 cursor checks,
  including empty/nonempty slices, Some/None and front/back advancement before
  moving the iterator into a wrapper. Nested memory operands load their current
  fields at rustc layout offsets after exact flattened-leaf type/count checks.
- Twenty-four unchanged regressions pass 5,881,740 native checks, including
  320 LLVM-only cases whose CG inputs retain expected refusals. The combined
  native total is 9,171,340. No prior-cohort executions are added to this total.
- A fresh clean incoming-main backend and the repaired backend use the same
  compiler, frozen core source and new dependency cohort. The baseline has
  11 failed roots; the repaired run has
  7, with 44 objects.
  Only the two atomic-load roots, u128 carrying_mul_add and the Option.map
  iterator-wrapper root disappear. Remaining failures are byte-for-byte equal.
- Mandatory proof ABI exits 101, passed:
  False; TCG-PROOF-465 present: True.
  Diagnostic native results do not discharge an unsatisfied proof gate.
- Root formatting passes. Private library formatting preserves 59 existing
  differences and adds none; all changed tests pass formatting in full.

The [earlier atomic-only qualification](../2026-09-27-atomic128-loads/README.md)
used the preceding dependency cohort. It completed successfully, but the push
preflight found that remote main had advanced. That attempted publication and
its dependent queued steps stopped before publishing. Their failure receipts
are retained. The first source-fetch command incorrectly supplied the
compilation-only --unverified option to fetch; a plain authenticated Targo fetch
then populated the exact new pins. No pin, proof policy or authority changed to
make a gate pass. The repaired backend and all native regressions above were
rebuilt and rerun with the adopted pins.

Prototype arithmetic and iterator-wrapper baselines retain actual LLVM passes
and CG refusals, then repaired LLVM/CG success and isolated core measurements.
They establish the individual changes but are separate from the combined
maintained count. Full core, instruction proofs and conjunctive product
completion remain open. Archives retain exact sources, commands, logs, receipts,
objects and native executables. Rebuildable libraries are listed by hash in
excluded.json. Archive parts are bounded below the normal Git file-size limit.

Final integration incorporates main `b397eb9aa5f271c161780fd2848afa791b6c150d` at `2c0520e63c2e9fe7a6c446890945beda2fc28503`. Relative to
the qualified incoming main, only generated INVENTORY.md changes; all backend
inputs and all seventeen qualified input hashes remain byte-identical. The
inventory was regenerated after merging. This integration adds no claimed
executions; its command logs, preflight refusal and equivalence receipt are
archived.
