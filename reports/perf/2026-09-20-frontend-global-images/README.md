# Canonical frontend allocation images — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The private Trust frontend now gives const-evaluated allocation images canonical
storage types. Byte-only allocations use U8 arrays and Bytes constants. Images
with relocations use declared packed structs containing byte-array runs and
pointer fields at the exact source offsets. Each global separately retains the
source allocation's alignment. Function-address cells use scalar SymbolAddr
initializers. Static, nested-static, TLS-definition and reader constant producers
share the checked image constructor; existing target/alignment/TLS restrictions
remain. The obsolete nested-static rounding to eight bytes is removed: allocation
extent stays exact, and the object writer aligns subsequent globals itself.

This fixes the three malformed global initializers in the fresh O0/O1 unwind
captures without changing their conditional failure edge or panic call. It does
not weaken canonical validation or supply a reference-validity/native proof.

## Qualification and remaining failures

Six maintained image tests pass, including exact sizes at forty size/alignment
combinations, unaligned relocations, negative addends, consecutive pointers,
self/cross-module references, sparse struct IDs, fixed type prefixes and
transactional malformed-input/ID-exhaustion refusals. They also check 22 fresh
modules from the genuine Trust frontend. All captured global storage validates;
16 entire modules validate. The six address-return captures retain eight exact
ConstTypeMismatch refusals from the separate legacy integer/reference address
producer (merged and individual attempts). Their 16-byte allocation alignment
and 32-byte extent are preserved; they are not credited as valid whole modules.
The first fresh-capture test exposed this defect and failed; its exact source and
log are retained alongside the corrected, explicit negative assertions.

Three existing native global-layout tests, eight native nested-byte tests,
68 module-merge tests and two historical bounds-capture tests also pass, with
zero ignored tests. These are focused checks, not the complete Linux floor.

The normal uninstrumented private backend builds. Both O0/O1 static-data
programs compile with backend proof enforcement enabled, producing fourteen
actual objects, byte-identical to their instrumented counterparts. Independent
ELF parsing checks sizes, alignment and all four pointer relocations per level:
reference data, the packed pointer at byte 1, a function pointer and a self-cycle.
The referenced anonymous images are exactly five bytes, without old tail padding.
Independent C executables link all seven objects at each level and check bytes,
packed layout, pointed-to contents, function invocation, cyclic address identity,
and mutable static writes. Both pass.

The two aligned-address and two unwind compilation cases still refuse frame
proof gaps (unwind O0 also CSet). These are remaining required-feature failures,
not passing positive cases. The genuine Rust frontend is explicitly unverified;
backend proof checks stay enabled. No installed package changes, self-host claim,
complete L01–L14 acceptance or full Rust/global/TLS support follows from this work.

## Reproduction and identities

The original commands, source fingerprints, diagnostic instrumentation, failed
attempt, complete logs, fresh modules, actual objects, C/ELF oracles, binary hashes
and resource records are retained below. Heavy commands ran serially under an
anchored 16 GiB process-group RSS limit, zero grace, two build jobs and one test
thread. Source and HEAD stayed fixed for each qualification. Temporary capture
edits were removed, and the final backend build is uninstrumented. Large compiler
and test executables are identified by hash rather than copied. Harnesses retain
their original machine-local paths.

Run the maintained image regression with the pinned stock toolchain:

```sh
cargo test --locked -p trust-cg-verify --test bridge_global_images -- --test-threads=1
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-frontend-global-images
```

The private frontend captures/native lane additionally require the exact sealed
Trust toolchain identified in the retained preflight records. Archived results
attest this candidate and host only.
