# Virtual-unwind main alignment after the x86 increment optimization

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Remote main advanced to `f658c8a53` before the [virtual-unwind repair](../2026-09-29-virtual-unwind-filters/README.md) could be pushed. Merge `5e9bf7bbbc9de1015a91a346d1709df216c1ad87` preserves both histories. The incoming production change is an x86 peephole optimization and its tracked option wiring; it makes no speedup claim.

The frozen merged backend is SHA-256 `e02b0a80939f61beb2f3d065b462e5d6704fd9fc3f4b4a98677978e7cc932e5e`. All **236 x86 peephole tests** pass. The Linux AArch64 virtual-call matrix repeats across O0–O3 and both panic policies: 49,152 checks, 7,168 caught panics, 16 reason-checked SIGABRTs, eight forced-unwind executions, and four expected compile refusals with four LLVM controls. The existing frozen native harness and fixtures are identified in the preceding report.

Strict bridge checks retain 18/15 functions, 16/13 refinements, one memo hit each and zero skipped/unmodeled shapes at O0/O2. Machine-proof-required checks remain refused by `TCG-PROOF-465`. Documentation and diagnostic checks pass. The source identity, exact commands, executable/backend hashes and logs are attached and enumerated in `assets.json`.

The previous mixed-library and 223-root O2 std census evidence remains tied to its recorded premerge backend. This alignment does not claim a new std census, whole-CG std, self-hosting, complete machine proof, or performance superiority.
