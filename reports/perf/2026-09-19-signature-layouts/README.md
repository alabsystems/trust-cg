# Rustc signature layouts and pointer transport — 2026-09-19

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The Rust frontend now retains target facts from rustc and emits actual tuple
pointee layouts for a bounded C signature profile. It queries `FnAbi`, matches
direct argument/return types, sizes and alignments, and reads array/tuple/struct
field offsets from rustc's layout query. It does not infer physical offsets from
TrustIR tuple arity. Existing primitive type-table IDs are retained; each new
descriptor names its actual appended type-table ID.

The profile covers flat primitive pointees, entry parameters and their address
extraction. Structural tuples with conflicting Rust layouts, opaque ABI shells,
packed layouts that the descriptor cannot express, non-C signatures and
untracked tuple uses receive no invented descriptor or aggregate policy.
`NativeC` states the restricted by-value aggregate policy: these signatures
pass scalars/pointers and primitive/unit returns. It is not a proof of the
complete calling convention or Rust reference validity.

The lowerer validates descriptors and retains the original module through
pointer transport. It rejects tuple allocation, aggregate SSA/layout operations,
array/vector uses hiding an aggregate layout, malformed descriptors and unused
rows. Explicit scalar byte loads remain possible without invoking the legacy
tuple layout algorithm. The module merger declines descriptor-bearing modules
until its structural interner can preserve their layouts; ordinary separate
compilation remains available. Proof annotations and certificates are unchanged.

CG adopts TrustIR `25422eb43e61a04376db66ae3a9720e3bdfd69a1`, with Clean
`55a85e998d428606ec9745bf6ba65fd1888ea149` and AY
`849c19fa0382085174a6a4827739681f059b4615` unchanged. TrustIR's companion
[reference/layout qualification](https://github.com/alabsystems/trust-ir/blob/25422eb43e61a04376db66ae3a9720e3bdfd69a1/reports/2026-09-19-core-byte-reference-layouts/README.md)
contains 124 passing tests, including canonical whole-world pointer execution.
The official CG pin transaction and its compiled authority guard were used.

Final CG qualification covers 138 distinct Rust tests with no failed or ignored
tests: 6 signature/layout/reflection tests, 3 Copy tests, 68 merger tests,
8 pin-move floor tests, 19 contract-surface tests, 24 output-memory tests,
6 canonical Store/Return tests and 4 dependency-authority tests. The canonical
store gate retains its 12 accepted and 33 refused cases and ten proof DAGs.
Pin updater unit tests, formatting and documentation checks are retained
separately. Commands, input hashes, build/test binary identities, source patches
and all intermediate failures accompany the record.

The actual Trust frontend was captured at four writer optimization levels and
in eleven layout/ABI controls. All 15 final metadata checks passed. Every writer
module differs from the preceding typed-Copy capture only in target/type/layout
metadata: type ID 5, size 40, alignment 8 and offsets 0/8/16/24/32. The complete
O1 module now reflects into Core without erasing any instruction. Its actual
lowered instruction structure is unchanged. O0 retains all fifteen missing
certificate/site errors and remains outside the Core reflection profile.
All four native writer compilations still refuse with `TCG-PROOF-465` and emit
no object. This is not a checked execution claim for the writer.

Signature controls retain `[0,8]` for a C struct and `[8,0]` for a reordered Rust
struct, and deduplicate identical declarations. Conflicting declarations,
packed/nested shells and a Rust ABI signature remain unclassified. A legacy
`ExtractField` case remains outside the profile; a reordered field's explicit
scalar load retains its real descriptor. A scalar batch still compiles and
emits its CGU object, whose bytes and identity are retained; no CG-generated
code was executed in this capture check. An independent LLVM-backed program
checks `size_of`, `align_of` and `offset_of` for ordered, reordered, packed and
nested source types.

The first capture expectations incorrectly included aggregate extraction in
the transport profile. Further expectations incorrectly treated a merged
module as a single C signature and assumed all field access used the legacy
aggregate route. Final controls distinguish the actual paths; production code
was unchanged across these capture attempts. An extra raw-address probe exposes
an existing Ref-to-PtrConst `Copy` mismatch outside this change's profile.
Earlier development failures include a test's missing Option unwrap, omission
of the frontend's five existing primitive type-table entries, a HashMap debug
order comparison, and a sealed-rustc field-index API mismatch. Exact failed
inputs and diagnostics are retained; none receives qualification credit.

The diagnostic checkout was restored through its exact owned paths. The final
production backend was rebuilt and frozen after capture, so the shared sealed
backend target is uninstrumented again. Builds use genuine sealed Trust a62
with the explicit unverified frontend development lane; runtime backend proof
checks remain enabled. Jobs are serial, with two build workers, one test
thread, bounded deadlines and a 16-GiB process-group RSS ceiling without grace.
No compiler or backend was installed.

`inventory.json` records stored and decoded hashes and sizes. Large executables
remain outside the repository with their identities recorded. All L01–L14
remain OPEN: universal source adequacy, caller ownership, O0 proof transport,
whole-writer execution replay and native memory/frame composition are still
required. Layout metadata grants none of those authorities.
