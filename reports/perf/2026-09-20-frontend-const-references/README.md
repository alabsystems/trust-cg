# Canonical frontend references and declared tuple images — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The Trust bridge now represents supported immutable allocation references with
canonical SymbolAddr constants referring to the original allocation. It decodes
byte images into the shared requested scalar, scalar-array or flat-tuple storage
view, requiring canonical alignment and exact equality of the full emitted
global vector: bytes, extent, relocations, alignment, binding, mutability and
section/TLS properties. Bare zero-offset pointer constants use GlobalAddr.

All uses of each allocation are reconciled before publication. Conflicting
pointee views, interior or mutable references, external/weak/TLS/mutable storage,
other symbol-address users, duplicate identities and attached proof metadata
remain untouched. The conversion is transactional and idempotent. It creates no
new allocation and supplies no reference-validity or native theorem.

An adversarial reordered-tuple test exposed a separate object conversion bug:
the emitter ignored canonical tuple descriptors. It now validates and honors
stated field offsets, extent and alignment, including nested array elements,
and checks that recursively emitted children agree with their canonical shape.
The reference constructor decodes fields at those same declared offsets. Without
a descriptor the existing natural-C object compatibility path remains; this
change does not widen full Compiler tuple-descriptor admission beyond its
existing pointer-transport profile.

## Qualification and remaining failures

Eleven reference test groups pass. They cover all 22 previous frontend captures,
exact object-image and translated function-definition LIR preservation, signed
and unsigned 128-bit boundaries, booleans, Unicode, floats, scalar arrays, alias
identity, invalid storage/layout/proof/target metadata, module merging and fresh
original frontend output. A signaling f32 NaN that cannot round-trip through its
canonical Float representation is refused unchanged. Reordered and padded tuple
controls check correct field values; nonzero padding that cannot be represented
by an aggregate initializer is refused unchanged.

The fresh genuine Trust frontend run captures 38 modules across eight O0/O1
cases: unwind bounds, aligned literal references, seven scalar/array reference
functions and static images. Every captured module validates before lowering;
there are 34 canonical reference SymbolAddr constants and four bare GlobalAddr
instructions, with no legacy bare-pointer tagged integer constants. These
captures are maintained as regression fixtures. Original allocation identities,
source alignment and extents are retained.

Five native global-layout test groups pass, including a new direct object-layer
ELF/C reader for reversed tuple fields and nested array stride, plus eight
malformed/conflicting descriptor controls. Existing native struct/packed/array/
pointer checks run at O0 through O3. Twenty-one global-conversion unit tests, 68 module-merge
tests, six allocation-image tests and two historical bounds-capture tests also
pass with zero ignored tests: 113 distinct tests. This is focused qualification,
not a full floor run. The reference tests were rerun after refreshing the two
unwind capture fixtures whose source-path bytes changed.

The final normal uninstrumented private backend builds. Both O0/O1 static-data
programs compile with backend proof enforcement and produce fourteen objects
identical to the fresh instrumented counterparts. Independent ELF checks and
native C executables check exact extents, alignment, packed pointer relocations,
referenced bytes, function calls, self-cycles and mutable writes.

The other six compilation cases still refuse required native proof gaps: the
address-return functions retain stack-frame proof failures, and unwind O0 also
retains CSet. These are required-feature failures, not successful positive cases.
The frontend is explicitly unverified while backend proof enforcement remains
on. The installed package is unchanged. No L01–L14 closure, complete global/TLS
support, self-hosting or release claim follows from this repair.

Root formatting, private-helper formatting, documentation/link/inventory checks
and Git whitespace checks pass. The archive verifies stored and decoded hashes.

## Evidence and reproduction

Retained records include failed attempts and their exact test/helper sources,
all capture/build attempts, full command logs, original modules, actual objects,
C/ELF oracles, source and executable hashes and resource records. Heavy work ran
serially under an anchored 16 GiB process-group RSS limit with zero grace, two
build jobs and one test thread. Source and HEAD stayed fixed within each run.
The capture checkout was restored and the last backend build is uninstrumented.
Large compiler/test binaries are identified by hash. Harnesses retain their
original machine-local paths.

```sh
cargo test --locked -p trust-cg-verify --test bridge_const_references -- --test-threads=1
cargo test --locked -p trust-cg-codegen --test e2e_aarch64_global_layout -- --test-threads=1
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-frontend-const-references
```

The private frontend/native lane requires the exact sealed Trust toolchain in
the preflight records. Results apply to this qualified candidate and host only.
