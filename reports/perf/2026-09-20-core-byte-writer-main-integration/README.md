# Writer proof integration with remote main — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Qualified on merge `cd26d7b0bf920394c206be70bb5eb53df0166d04` plus the retained
formatting/inventory patch. Its parents are writer-proof commit `cf1e947e`
and remote main `75f3c524`. The ordinary fast-forward pull and atomic push were
refused after main advanced by eight commits during proof qualification. A
normal merge preserved both histories without conflicts or force-pushing.

The imported changes cover x86 ABI/Swift/callee-save and Movsxd obligations,
shared adapter/compiler paths, and soundness harness repairs. Two incoming
files required rustfmt; their only integration edits are formatting. The source
inventory was refreshed. Dependency pins and the original writer fixture are
unchanged.

The integrated tree passes the maintained whole-writer gate: six test groups,
four accepted whole-world claims and 27 expected refusals. Two claims quantify
over all five independent canonical 64-bit words and all initial byte maps, at
two explicit caller addresses. Four positive DAGs and the rejected symbolic
candidates are retained again. Runtime: 442.65 seconds. This includes the
new combined-tree compilation; the report records the separate test runtime
and peak process-group RSS (11,474 MiB, including compilation) under the
16-GiB ceiling. All four proof hashes match the pre-merge qualification exactly.

The bridge Copy normalizer (3 tests) and signature/layout bridge (6 tests) also
pass on this combined tree. Root formatting, documentation inventory, file
links, diagnostic census and whitespace gates pass. The first integration
attempt stopped at the two formatting differences; it did not run Rust tests.
The second completed all required checks.

The actual Trust-pinned private backend also builds successfully in 289.89s
using the genuine sealed toolchain, under the same memory ceiling. This is
explicitly an unverified frontend development build; backend proof checks stay
on. The uninstrumented O1 native probe then reproduces the precise remaining
writer refusal: `TCG-PROOF-465`, uncovered `StpPreIndex` and `LdpPostIndex`, exit1,
no object. Its scalar control compiles with exit0 and emits the same 1,008-byte
ELF object as the previous capture, SHA-256
`5288b4e214c18166edc11f8274cb1d810a924ed1048cc0284523ba3b550bba8d`.
Compiler commands, source inputs, full logs and the scalar object are retained.
The backend binary is identified by hash in its build record; the large dylib
snapshot remains outside the repository. Neither object was executed here.

The [universal-word proof record](../2026-09-20-core-byte-writer-symbolic/README.md)
describes the theorem and its limits. This integration neither qualifies every
incoming x86 change nor changes native compiler admission. Arbitrary caller
memory placement, Rust frontend/reference adequacy and native stack/ABI proof
composition remain open. The actual writer's native frame check still refuses
it. **All L01–L14 remain OPEN.**

`inventory.json` records actual stored and decoded artifact hashes and sizes;
`scripts/check_evidence_archive.py` validates them.

A subsequent normal merge, `1246d3d0`, imports remote `f001a11e`. Its effective
delta is entirely `cfg(test)` x86 audit code; its two formatting edits match
those already retained here. The four incoming audit tests pass on that merge,
with logs under `followup/`. They confirm an existing limitation: 37 classified
memory-opcode reconstructions cannot refute changed addressing operands.
Passing these audit tests documents that gap; it does not repair it or qualify
those addresses. The writer proof model, dependencies and production backend
code are unchanged by this final test-only merge. Source inventory and docs
checks were refreshed.
