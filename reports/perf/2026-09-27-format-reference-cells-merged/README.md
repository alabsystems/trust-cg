# Formatter repair after main integration — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The [formatter reference-cell repair](../2026-09-27-format-reference-cells/README.md)
was committed as `cb13212efd8511cd6532be0cff86c4783aa5d201`, then merged with
upstream `cef3960644444258c40a966df7ce9d2136ec68b2`.
Upstream changed code generation, x86 operand binding and proof admission,
including the bridge's discharged-evidence check. This report records a fresh
build and execution on clean merged commit `b4edb3c28d1d8730fd772ca5ce25e5a8e08d0f1c`.

- Genuine Trust all-targets check and backend build pass; exactly 25 maintained
  tests are listed. Backend SHA-256: `76cc20d4561f50c17fcfd6ff7fb8505edc5af61253da2509cf64529db5df4631`.
- The formatter tests pass all 77,824 LLVM/CG native checks at O0–O3. The 22
  unchanged controls pass 5,343,116 checks, including 320 LLVM-only checks
  whose corresponding CG inputs retain their expected refusals.
- Together these are 5,420,940 native checks. They use the unverified frontend
  and diagnostic code generation without proof certificates.
- Full core still fails with exactly the same 12 roots, with no new or changed
  failures: exit 1, 44 objects,
  34.27 seconds. The original formatter
  failure remains absent.
- Mandatory proof ABI exit is 101; TCG-PROOF-465
  is present: True. This gate remains open.
- Changed gate harness tests pass: AArch64 65 passed plus one existing
  platform skip; x86-64 16 passed. These are harness tests, not platform proof.
- Root formatting passes; private library formatting retains 59 existing
  differences and adds zero. Changed tests pass formatting in full.

The incoming raw evidence logs remain byte-for-byte intact. Merge whitespace
checking compares this contribution with upstream; it does not rewrite existing
upstream transcript whitespace. Generated source and diagnostic inventories
were regenerated when they conflicted. Earlier failed archive/integration
attempts remain recorded rather than overwritten.

Full core, instruction proof coverage and conjunctive product completion gates
remain unfinished. Records are split into bounded archives; source, commands,
logs, objects and native executables are retained, while rebuildable libraries
are listed by digest in excluded.json. No additional native checks are credited
for repeated archive validation or for source-equivalent merges.

A later merge of `9e9cb83b70bdf7ab564483a72a119d3dfffa1352` added only upstream tests, gate scripts
and generated inventory. Every qualified bridge source and backend build input
remained unchanged; the changed x86 gate module reran all 16 tests successfully
and root formatting passed. This integration is recorded at `a2c17df23e20d11afa5e6cedf2dab6da17a0ab78`.
The native and core measurements above remain bound to their original clean
commit; no additional executions are claimed for the source-equivalent merge.
