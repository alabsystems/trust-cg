# References to wide-pointer values — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

A local function returning a reference to a wide-pointer value now uses the
ordinary call path and preserves the address of that value. The scalar-reference
selector recognizes that a slice, string or trait pointer occupies two lanes
and declines its scalar promotion. The existing refusal for temporary borrowed
bindings remains: it cannot return the address of a discarded call temporary.
No metadata representation or proof validator changes.

Qualification binds base `b4edb3c28d1d8730fd772ca5ce25e5a8e08d0f1c`, seven maintained source hashes and
backend `1646342d2787338f16c995ae212b47555140dae0ab25bb1932d274ee5e0f4aba`. The tests use genuine Trust with the
unverified frontend and diagnostic code generation without proof certificates.

- Genuine all-targets check and build pass; exactly 26 maintained tests are
  listed. Original and expanded corpora run under LLVM and CG at O0–O3.
- The original local helper and iterator run 387,072 checks of element-slot
  addresses, trait data/vtable identity, formatting, advancement and exhaustion.
- Expanded local selectors run 73,728 checks of references to slices, strings,
  trait objects and corresponding raw pointers, including empty slices/strings,
  both branches and mutable-reference alias updates. Total new checks: 460,800.
- Twenty-three unchanged regressions run 5,420,940 native checks, including
  320 LLVM-only cases whose corresponding CG inputs retain expected refusals.
  The combined total is 5,881,740 native checks.
- Full core exits 1 with
  11 failed roots and 44 objects.
  Only `slice::Iter<&dyn Debug>::next` disappears from the previous 12 failures;
  no new or changed remaining failures occur.
- Mandatory proof ABI exit is 101; TCG-PROOF-465
  is present: True. Runtime checks do not discharge this gate.
- Root formatting passes. Private library formatting preserves 59 existing
  differences and introduces none; changed tests pass formatting in full.

Earlier wrappers that called external core helpers passed, so they did not
reproduce the failure. The archived full-core bridge-notes diagnostic identified
the local-call recognizer. A local reference-return helper then reproduced it
under CG while the same LLVM corpus passed; six expanded shared-selector roots
also refused before the change. The prototype passed both corpora before the
permanent regression was installed and requalified.

Full core, instruction proofs and conjunctive product completion remain open.
The archives retain receipts, source snapshots, commands, logs, objects and
native executables; rebuildable libraries are listed by hash in excluded.json.

The final merge incorporates main `7d4490c94c8cd5ac91d842e56ea2aa94ff0df273` at `dcc59fe26d4e1aff8d42b9fe0a7e32596fb2fa87`.
Incoming changes affect tests, gate scripts, reports and inventories; every
qualified bridge source and backend build input is unchanged. Root formatting
and documentation checks pass after integration. Native and core measurements
remain bound to the original base and source hashes above; this merge adds no
claimed executions. The integration receipt and commands are archived.
