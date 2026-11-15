# Original typed output source bound to LIR and reference instruction bytes

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`check_aarch64_trust_ir_output_bytes` independently interprets a selected,
module-owned TrustIR output writer, compares its entire ordered store trace
with the real adapter's LIR, checks its exact aggregate pointee metadata and
then checks the complete A64 instruction stream. Its private owner retains
immutable references to all original endpoints and the conditional query.
`OutputMemoryRequirements` records the original mutable-reference parameter,
declared byte extent and alignment. It does not discharge those requirements.

The bounded source domain has one mutable reference to a flat tuple/array of
one through 64 integer lanes, up to eight register parameters, a void C ABI
and at most 16 unconditional blocks / 256 instructions / 64 stores. Constants,
identity copies, bounded GEPs, 64-bit pointer/integer carrier conversions,
constant multiplication and address addition are interpreted independently.
Stores must stay within the declared extent. Raw/shared pointers, forged or
missing metadata, unsupported casts/effects, arbitrary integer-derived pointers,
loops, block arguments, malformed SSA and changed ordered effects refuse.
Pointer hints and proof annotations are not used as ownership evidence.
The LIR-only diagnostic still refuses every nonempty pointee sidecar.
No metadata is erased to gain acceptance.

Qualified source index tree: `1158ad30aae20d761a3ac029089748c1776ab691`, based on
`797e0ea59aa60f341bb0d6435141f0a8353d185e`. Stock Rust 1.97.1 Linux AArch64,
locked dependencies, two build jobs, serial tests and an exclusive resource
lease with zero-grace 16 GiB child RSS supervision. Frozen test executable
SHA256: `36fbf251c546f9a2d1b6929cc91444ff6e4b1d3e578de690a2c52e36c44ec5f6`.

All **56 selected tests pass**: 44 existing source-bound controls, six new
original-source controls and six UF traversal controls. Exact test listings
match executed names; no selected tests fail or are ignored. New controls
include 27 source/identity refusals, seven independent LIR mutations, all
288 single-bit mutations of the scalar stream, array-table mutation and a
source loop, plus positive nonfirst output parameters and literal values.
The existing byte suite again rejects its 512 changed original streams and
rechecks eight actual GNU assembler/objcopy reference programs.
Ordinary library compilation, repository formatting and documentation pass.

The genuine sealed Trust development frontend was rebuilt with a temporary,
three-line JSON capture immediately before the unchanged codegen pipeline,
plus the capture-only serde_json runtime dependency. Its source patch, command,
backend hash and complete logs are retained. O0–O3 all capture the actual
ordinary Rust output-buffer fixture; all four compilations still refuse at
the production proof gate, with zero object/native support credit. The
instrumented backend is **not installed** and its patch is not part of this
production source change. The frontend lane remains explicitly unverified.

The O1–O3 captured modules are byte-identical (SHA256
`6a1a2970534d992493f433d04a3d856706b32304e128f68bac9ba16be733fcd7`),
including mutable-reference metadata and explicit pointer/integer address
arithmetic. These original modules pass the new check through the real adapter
against both independent scalar and paired reference instruction streams.
Those reference words are not presented as compiler-emitted output from the
failed compilation. O0 contains bounds probes and remains a required positive
outside the new source domain; the retained O0 module must refuse. Its guards
are never deleted or reinterpreted as inert comparisons.

Both the authored and captured sources reproduce the exact original
96,284-byte query, SHA256
`e7cb7c86173f17dfd2445faeaab42604ebe64f31e674f6e49803a93395a0e6c7`.
Fresh strict AY produces its complete certificate; independent Clean accepts
it and rejects hole, missing-empty-clause and opposite-premise corruptions.
The four identical query exports are checked before deduplicated replay.

Failed preparation attempts are retained separately. The first generated
capture runner had a syntax error before any build. The first diagnostic build
then failed because serde_json was only a build dependency; the second build
adds the temporary runtime dependency and succeeds. The first verifier test
process returned zero but exceeded the 1 MiB capture limit, so that run receives
no qualified count. The successful runner splits the same unchanged test binary
into complete bounded-output groups and reruns every required test; it does
not increase or disable the capture limit.

This closes a bounded **original TrustIR → LIR → reference-word correspondence**
gap. It does not prove this Rust checker's implementation, Rust MIR refinement,
caller allocation/lifetime/permission, separation from the private stack frame,
object/link transport or production publication. The production frame constructor
still refuses the effectful writer. All full Linux L01–L14 requirements remain
open. The installed development compiler remains `ef2d7eaf` with the separately
qualified AY tree `43f133d3` and Clean tree `ed2a80d1`.

Every compressed and decoded artifact is audited against its size and SHA256.
Large binaries remain local and are identified by the retained receipts.
