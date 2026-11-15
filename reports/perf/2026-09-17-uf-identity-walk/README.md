# UF declaration walk: 44 development controls pass

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Two fresh compilations and **all 44 selected controls pass** on this ARM64 Mac
at source `69c2fc347a14136e96b028592ee9e98995163d72`, tree
`40d8c9068490f0dbdef14c08899d6d450beb98a4`. Both captured real output-memory
query strings are byte-identical to the independent merged38 baseline.
This establishes the tested traversal-work bound and compatibility, **not a
measured speedup, lower peak RSS, or a new proof-admission capability**.

The candidate merges UF checkpoint `4bf9e190` with peer main `405f20a6`.
Its delta from that peer base is exactly `ay_bridge.rs`, the new
`ay_bridge_uf_walk_tests.rs`, and the regenerated inventory. Both Rust files
retain their exact checkpoint bytes. Peer arithmetic-export changes are
preserved; this selected campaign does not qualify all of their behavior.
Development main merge `d266e2ee954873e701308929be03603b6449c21d` subsequently
preserved these exact compiled source/configuration/inventory bytes alongside
peer stale-backend guards and proof-failure documentation. The execution
identity remains `69c2fc34`; the later tooling changes are not retroactively tested.

## Change and tradeoff

`collect_uf_declarations` now uses a call-local set of expression addresses to
avoid descending repeatedly into the same shared graph node. The immutable
borrowed root keeps these identities live for the walk; they are never persisted
as proof or cache keys. The implementation reuses the existing exhaustive child
visitor and preserves its order, UF declaration/signature behavior, traversal
of distinct same-name applications, and MemLoad handling. It neither substitutes
variables nor moves expressions across binders.

The added set costs **O(unique expression nodes) temporary memory**. Inputs with
little sharing can incur overhead. UF-name/signature work, other query passes,
recursive depth, and tree-shaped SMT formatting are unchanged. There is no
claim of lower overall query memory, linear complete-query generation, or
end-to-end compiler/model-checker speedup. Declaration-name membership still
uses a linear scan, and argument-sort work retains its prior cost; the entire
collector therefore has no new unconditional linear-time guarantee.

## Actual acceptance

The same freshly built library test image ran the unchanged 38
`source_bound_` controls and all six `ay_bridge::uf_walk_tests::` controls.
Both native listings and all result names matched exactly: no failures,
ignored tests, missing cases, or duplicate names. Six supervised phases exited
zero: two builds, two listings, and two serial test groups.

The six new tests cover shared-store unique-work bounds, constructed complete
query-byte compatibility, same-name UFs with distinct arguments, sharing across
shadowing binders, MemLoad/poison-symbol identity, and per-call pointer identity.
The structural scaling control checks 28 store/read combinations: unique visits
stay within its linear bound and the legacy tree walk exceeds twice that count.
These are deterministic work assertions, not elapsed-time or allocation measurements.

The output-memory controls additionally captured two instances of the **same
96,284-byte query**. Each has SHA-256
`e7cb7c86173f17dfd2445faeaab42604ebe64f31e674f6e49803a93395a0e6c7`;
the two-string JSON is `bc2036ad28ff4b5fb5a1f88fc31ee4d072c138edb56bbd26836701c0e654c8ce`.
Equality was checked against the retained
[merged38 result](../2026-09-17-output-memory-merged38/README.md), not merely
against a reconstructed expected query. This does not discharge that query:
the separate [Mac proof attempt](../2026-09-17-output-memory-mac-query/README.md)
remains UNKNOWN with no proof or Clean replay.

## Provenance and unchanged limits

The pinned September 10 Trust **`--unverified`** lane produced fresh ordinary
and library-test primaries for `trust-cg-verify`: default features, debug profile,
one job, locked dependencies, and checksum freshness. Independent audit checked
the actual compiler argv, generated environment, output identities, and locked
TrustIR/Clean linkage. This is not Trust-verified compilation of the Rust code.

Build limits remained 7200 seconds, listings 60 seconds, and each test group
300 seconds. The existing 12 GB scheduler reservation is not an RSS cap.
Compiler/tool/runtime-prefix identities, proof policy, configuration, and the
five-second passive final drain were unchanged. The last drain finished in
4.909 seconds without signals; all 377 prior/copy/phase process IDs and matching
source/cache processes were absent on independent audit.

The complete 15,216-file source, 43 tool records, 71 sysroot records, upstream,
environment, resource, ownership, and historical books matched before and after.
All 34 current primary/direct-extern/checker files matched their recorded bytes;
the native test image SHA-256 is
`18c24edcff2e5e75cb85aeae47a56663ca09f3a4afc5cf5a82bb5bba02374eae`.
The original xFHu, NX33, and merged38 caches remain unchanged. Only a new,
independently owned CoW target was used; no historical cache was cleared or
released for reuse.

## Retained evidence and boundary

`uf44-evidence.tar.gz` (removed from the tree) contains all 41 qualification
records, all 8 copy-admission records, the 3 activated/frozen controls, and the
3 selected source files: **55 regular files / 44,386,830 raw bytes**.
Archive SHA-256 is
`8d95e8b7e8ae3eeaa37121295cbcd8b802cb362c9bf9c2df724accde2223e2ed`
(7,011,004 bytes). The inventory records each original
path, size, mode, and hash. Every decoded member matched its original bytes and
mode; originals and all target outputs remained unchanged during archival.

The original result SHA-256 is
`8ac3039b024cc0b82f098c14ad0776209fecac589ba186d8e15e8c59566e20c6`.
No compiled executable payloads are included. Transitive helper/tool binaries,
full dependency sources, and retained baseline images remain separate inputs;
this is a complete campaign-record archive, not a standalone reproduction bundle.
The 34 new target outputs remain local and need independent retention before
any authorized reuse. **Archival grants no cache release.**

No solver replay, ordinary Rust writer compilation, source-bound native model
execution, production output-memory admission, verified TY implementation, or
TY/TLC performance comparison was performed by this campaign.
