# Trait-object struct tails — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bridge now carries pointers to unpacked struct chains ending in a trait
object as the whole struct address plus the terminal tail's vtable. Rustc's
field layouts determine prefix offsets; projections round unsized field offsets
to runtime alignment. Recursive `size_of_val` and `align_of_val` account for
both the static prefix and the dynamic tail. Concrete unsizing emits the
terminal payload's vtable while preserving the whole struct address, and
supertrait upcasts use rustc's secondary-vtable query.

The native corpus passes **272,448 checks** in eight LLVM/trust-cg executions
at O0–O3, using `panic=abort`. One shared LLVM types crate supplies the same
nominal trait definitions to both libraries and the driver. The checks cover
nested C layouts, default Rust and transparent layouts, static alignment up to
32, payload alignment up to 256, and an over-aligned zero-sized payload. They
compare actual field addresses, sizes and alignments against LLVM, and verify
prefix and payload mutation in the original caller's storage. The corpus also
checks stack-local construction, fat-pointer returns and stack arguments,
metadata extraction and reconstruction, secondary-supertrait dispatch, and
branches between differently aligned payloads.

The previous backend rejects all 26 roots of this same final fixture; LLVM
accepts it. The frozen full-core diagnostic drops from **two failing roots to
one**. `Request::fmt` now lowers. The remaining
`TwoWaySearcher::maximal_suffix` diagnostic is byte-for-byte unchanged: its
semantic loop check still needs a model for slice `get` and subsequent control
flow. Both core runs exit 1 and retain 44 partial objects. This is not a complete
core or self-host build.

Qualification on the final backend:

| Check | Result |
| --- | --- |
| New native regression | Passed, 272,448 checks at O0–O3 |
| Slice tails, trait upcasts, trait pointer values and trait leaves in memory | Passed |
| Caller locations, 128-bit loops and captured aggregates | Passed |
| Trait aggregate-cleanup refusal control | Passed |
| Mandatory ABI proof admission | Failed with `TCG-PROOF-465`: 14 uncovered instructions across 12 opcode kinds; first `StpPreIndex` |
| Bridge all-targets, formatting, diff and documentation checks | Passed |

The control invocation reports 8 passed and 1 failed, with no ignored tests.
This extension checks 64-bit, two-word pointer layouts and bounds traversal to
31 nested structs. Packed chains, extra dereferences inside a projection,
aggregate prefix loads/stores and projected unsize destinations remain outside
it. Concrete unsizing requires an existing stable data address and a principal
trait. This does not add dynamic-tail drop or cleanup lowering.

The backend SHA-256 is
`33d829e872d5c578e967cc6bf64b2f65c5afa455d9ec776c38fd7c30be3eca44`.
It was built with Trust-authored `trustc` 1.99.0-dev,
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, using LLVM 22.1.2 for this
development bootstrap. The base checkout is
`e0ac540a363e36c0f28bea7a4831aca10345c313` plus the archived changes.
The previous backend is identified in the
[128-bit loop report](../2026-09-27-wide-loop-threading/README.md).
All 721 frozen core files were rehashed and matched their manifest.

results.json records the final outcomes.
evidence.tar.gz contains source snapshots, patches, commands,
logs, all frozen core sources, the primary native executables and libraries,
and both censuses' partial core objects. The two installed rustc source files
consulted for dynamic layout and field projection are included. Large
rebuildable backend libraries and other control executables are recorded by
hash. assets.json hashes every tar member; each member was
independently rehashed after archiving. archive.json records the
stored archive identity and member count. inventory.json
includes stored and decoded archive identities.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-27-dyn-tail
```

Trust/Targo verification is disabled in this development lane, and native
codegen uses `no-proof-certs`. Native correctness does not establish complete
machine proofs. No qualifying performance comparison was made. Linux
completion, mandatory proof admission, and compile/runtime dominance over
LLVM and Clang remain open.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
