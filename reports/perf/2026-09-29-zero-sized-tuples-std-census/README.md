# Zero-sized tuple optimized standard-library census

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The completed Linux AArch64 O2 diagnostic `std` census decreased from **233 to 231 failing roots**: two removed, zero added, zero changed. The removed failures are `ControlFlow::map_break` and its `FnOnce` constructor shim over `((),)`. Both runs completed with exit 1; neither timed out. This is still an incomplete `std` build using the recorded LLVM dependency artifacts.

This supplements the [published tuple report](../2026-09-29-zero-sized-tuples/README.md), whose census was still running when it was published. Its earlier evidence is unchanged.

The baseline backend is `e7c28938cf451256377e7a1b23d91be4f58ddd94222585619199345672b4a3b8`; the tuple backend is `1a6cc67befb08366c2523a3c09e71cd4ea73564fbe71ac10ca6432dc055f8e13`. The tuple backend predates the later sealed JIT merge. Both use Trust IR `824174a164de10dba2053e387dfc4b1140960885` and the same recorded LLVM dependency cohort; the intervening main merge also includes x86 jump-table changes. Source manifests, exact commands, complete diagnostics and the root delta are attached and hashed in `assets.json`.

The separate latest O0 census remains 197 failures. Whole-CG standard-library completion, self-hosting, complete machine proof, and strict compile-time/runtime superiority over LLVM and Clang remain open.
