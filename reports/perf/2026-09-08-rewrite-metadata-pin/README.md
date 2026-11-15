# TrustIR rewrite-metadata adoption — 2026-09-08

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Base: `648cd93f444ae65a0eaff0a405ca72ccee215e63`.
Adopted TrustIR: `eaed4319890b43c553e3a1c2a6bbc4a7960cde19`.

The root workspace, private rustc backend workspace, and unchecked artifact-cache
identity now select the same published TrustIR revision. Its generic dialect
rewriter refuses unmapped semantic metadata and invalidates original claims;
this pin does not turn existing code generation into a verified pipeline.

## Evidence

Stock Rust 1.97.1, aarch64-apple-darwin; explicit rustc wrapper/flag overrides
are cleared by `run-gates.sh`. Trust verification was not available or run.

| Gate | Result | Log |
| --- | --- | --- |
| trust-cg-lower, all features | 1,787 library + 410 integration tests passed | final-lower.log |
| local function addresses and TY callback clobbers | 6 native tests passed | final-native.log |
| artifact cache | 43 tests passed | final-cache.log |
| fuzz workspace, all features, all six bins | locked cargo check passed | final-fuzz.log |

Root, private-backend, and fuzz `cargo metadata --locked --all-features` each
resolve exactly three TrustIR packages at the new revision; see the corresponding
metadata logs. The private rustc backend was metadata-checked, not built with its
nightly rustc-private toolchain. Fuzz compilation is not a fuzz campaign.

## Pre-existing fuzz lock repair

Both the candidate and unchanged main failed locked fuzz metadata resolution.
The old fuzz lock still selected TrustIR 0.13.0 at
`f572adaf04f55edd6ae9e243586caebfcc3bc660`, despite the main workspace already
selecting 0.14.0. The baseline and initial failure logs retain that evidence.
Offline Cargo regeneration changed only the three TrustIR versions and git source
identities. Package roster, dependency lists, registry packages, Clean and AY pins
are unchanged. The repaired graph passes locked metadata and all-bin compilation.

This is a qualified dependency/cache-identity update and lock repair, not a broad
soundness reattestation, public release, proof certificate, TY closure feature, or
runtime speed/RSS benchmark. No lowering/codegen algorithm was changed here.
