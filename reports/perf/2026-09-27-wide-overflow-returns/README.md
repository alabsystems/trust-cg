# Wide overflow tuple returns and sysroot census — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The Linux AArch64 compiler-builtins diagnostic census improves from **18 to
14 failing roots**, removing the signed and unsigned 128-bit `overflowing_add`
and `overflowing_sub` refusals without adding roots. The frozen core object
build still exits 0 with zero failing roots and 44 objects. A usable sysroot
remains unfinished: alloc has 147 diagnostic roots, and linking a consumer of
the generated core library exposes 40 unresolved helper symbols.

Checked integer arithmetic now shares one emitter between scalar and
memory-backed tuple destinations. The existing 128-bit add/sub/mul primitive
compositions return their wrapped value and overflow bit; memory destinations
store both at rustc's tuple field offsets. Narrow operations retain their
`Inst::Overflow` path and refinement checks. Memory destinations must be whole
locals with the matching `(operand_type, bool)` layout. No machine proof
requirement is disabled by this implementation change.

The maintained native regression checks returned tuples, direct compiler
intrinsics, a borrowed tuple modified by an LLVM-built callback, and scalar
consumption of the pair. It covers signed and unsigned 64/128-bit add/sub/mul,
all 256 pairs of 16 boundary values, and 4,096 generated pairs with full-width,
small, negative, zero, one, carry, power-of-two, and cancellation cases. LLVM
and trust-cg each execute at O0–O3 with `panic=abort`: **1,671,168 comparisons
pass**. The previous backend rejects 12 return/intrinsic functions in this
same source; LLVM accepts all of it.

| Check | Result |
| --- | --- |
| New wide overflow-return regression | 1 passed; 1,671,168 native comparisons |
| Overflow loops, wide loops, scalar-cell returns and maximal-suffix controls | Passed |
| Existing overflow and maximal-suffix refusal controls | Passed |
| Mandatory ABI proof admission | Still fails `TCG-PROOF-465`: 14 uncovered instructions across 12 opcode kinds, first `StpPreIndex` |
| Frozen core diagnostic object compile | Exit 0, zero roots, 44 objects |
| Compiler-builtins diagnostic compile | 18 → 14 roots; both attempts exit 1 |
| Initial alloc diagnostic compile | Exit 1, 147 roots; LLVM control exits 0 |
| Core consumer with LLVM-built core and matching builtins | 22,930 native character-count comparisons pass |
| Bridge all-targets, formatting, diff and documentation checks | Passed |

The selected control invocation reports 6 passed and 1 failed, with no ignored
tests. The sole failure is the mandatory ABI proof gate above.

The compiler-builtins build uses its real build script with the `arch`,
`compiler-builtins`, and `unmangled-names` features. Target configuration comes
from the baseline backend's `--print=cfg`, and the LLVM control receives the
same build-script configuration. The script's existing f16/f128 restrictions
follow that configuration. The before/after census uses the same source,
configuration, and baseline CG-built core dependency. All 460 installed
compiler-builtins/alloc source files were frozen and rehashed; all 721 frozen
core source files retain their previous identity.

The 14 remaining compiler-builtins roots are six inline-assembly functions,
four signed 128-bit-to-float conversions, two aggregate unary assignments,
one enum discriminant, and one aggregate pointee layout. The initial alloc
probe uses CG-built core and LLVM-built compiler-builtins; its 147 roots
include wide owning pointer ABIs, aggregate storage, drops and iterators.
These transitional dependencies do not constitute a CG-only sysroot.

Core `.rlib` and metadata generation succeeds, but native consumer linkage
fails with 40 unresolved core helper symbols, including pointer-address,
cast/provenance, metadata, no-op drop glue, and a formatting implementation.
The consumer is compiled independently by both LLVM and trust-cg and uses an
actual exported core character-counting body. Its C driver generates valid
UTF-8 independently. The link failure is recorded separately from diagnostic
codegen admission; no core-library execution success is claimed for the CG
archive. Both the baseline and final CG core archives reproduce these same
40 unresolved symbols. With LLVM-built core and matching LLVM-built builtins,
the exact consumer and C driver link and pass 11,465 character counts for each
consumer backend (22,930 total). The final CG core archive still cannot link.

The final backend SHA-256 is
`410c531c8d88b76a49986fcbd77e96bf44e8508292aa1f859bc088d610c0a58d`.
It was built using Trust-authored `trustc` 1.99.0-dev,
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, with LLVM 22.1.2 for the development
bootstrap. The source base is `e0ac540a363e36c0f28bea7a4831aca10345c313` plus
the archived changes. The prior baseline is the
[unconditional loop-path report](../2026-09-27-maximal-suffix/README.md).

results.json records the outcomes and remaining roots.
evidence.tar.gz contains source snapshots, patches, commands,
logs, frozen library sources and the primary native artifacts. Rebuildable
backend/dependency libraries and control executables are identified by hash.
assets.json hashes every archive member; each member was
independently rehashed. archive.json records the stored archive
identity. inventory.json records stored and decoded hashes.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-27-wide-overflow-returns
```

This is diagnostic development evidence. Trust verification and native
machine certificates are disabled in these runs; the mandatory proof control
still refuses. Linux completion, a usable sysroot, self-hosting, the complete
proof chain, and compile/runtime dominance over LLVM and Clang remain open.
No qualifying performance comparison was made.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
