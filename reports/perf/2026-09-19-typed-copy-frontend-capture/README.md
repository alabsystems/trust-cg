# Actual frontend typed Copy capture — 2026-09-19

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The ordinary Rust `output_memory_writer` fixture was compiled at O0–O3 using
the genuine sealed Trust a62 compiler and the production change published as
`c5910147f897aec97a1cf6d4ee6b2413c7e7de67`. An isolated diagnostic build adds
only a JSON print immediately before the unchanged proof-enforcing object
compiler and its serde_json dependency. It does not change MIR lowering,
canonicalization, validation, selection or proof admission. Exact production
candidate and instrumentation patches are retained separately and together.

All four fresh modules contain the five expected explicit `PtrToPtr` casts,
each preserving `RefMut(Tuple[U64; 5])` as its source type and value 1 as its
operand. Each complete fresh module equals its historical fixture after
replacing exactly those five old pointer Copies. There are no other module
changes. O1–O3 share the annotation-free fixture; O0 still contains the five
discharged bounds obligations with no certificates. Every target_info is still
absent. `records/module-comparison.json` records this whole-module comparison.

All four required writer positives remain refused with `TCG-PROOF-465` and
produce no object. O1–O3 report two uncovered frame instructions:
`StpPreIndex` and `LdpPostIndex`. O0 reports twelve uncovered instructions
across those two opcodes and `CSet`. The complete diagnostics are retained.
This establishes that the actual frontend runs the repaired normalizer; it
does not establish memory/frame proof composition or native writer execution.
All L01–L14 remain OPEN.

The diagnostic backend built in 296.67 seconds; each capture took 1.98–2.33
seconds. The exclusive process-group envelope was 16 GiB with no grace, two
build jobs and per-command deadlines. No timeout or memory breach occurred.
The instrumented backend SHA-256 is
`e0b1de1d6f194f05645b115d4a07764ed7d1b8a51ba5d443aa87c9f21eb01cb5`
(93,460,488 bytes). Compiler/tool identities, source fingerprints, commands and
full output accompany the results. The explicit unverified Trust frontend
development lane was used; backend proof enforcement remained enabled.

After capture, both the temporary production patch and diagnostic changes were
verified byte-for-byte against their saved patches, restored through explicit
owned paths, and the isolated worktree was fast-forwarded cleanly to c5910147.
The restoration receipt is retained. The diagnostic binary was not installed;
the shared build cache must be rebuilt before ordinary backend use. The
separately frozen, uninstrumented backend and its qualification are in the
[Copy adoption record](../2026-09-19-core-byte-copy/README.md).

`inventory.json` covers exact stored and decoded hashes/sizes for every
artifact. Large binaries and transient tool caches are not committed; their
identities are retained. Captured proof-status labels supply no independent
certificate authority. The successful result here is source-capture validation,
with four explicit production-admission failures.
