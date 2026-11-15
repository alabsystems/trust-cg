# Linux AArch64 unsized slice arguments

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The alloc diagnostic census drops from **15 to 14 failed roots**. The by-value
`[&str]` implementation of `SpecExtendStr::spec_extend_into` now lowers. There
are no added failures or changed surviving failures. Full alloc/std, mandatory
machine proof, self-hosting, and faster compile-time/runtime performance remain
unfinished.

## Change

Rust passes a by-value unsized slice/str argument using the caller's storage
address and length metadata. The bridge now derives that convention from the
argument's exact rustc `FnAbi`: matching unsized type, Rust calling convention,
`PassMode::Indirect` with metadata, and no stack-by-value flag. Declaration,
entry block, direct and function-pointer calls, and the non-receiver arguments
of virtual calls share the same decision.

For the body, an internal MIR view changes the parameter local to a wide mutable
reference and prefixes every original place projection with a dereference.
The entry block receives two scalar ABI parameters and stores them in the
view's data/length slot. Normal slice lowering then accesses the caller's
payload, including ordinary borrows, raw borrows, indexing, and mutation.
Forwarded unsized operands transfer both lanes from the matching whole indirect
place. The LLVM IR probe independently confirms the same pointer/length
transfer, including its MIR Copy operand; it does not allocate or copy the
payload when forwarding.

Admission is limited to Linux AArch64 slice/str parameters whose payload does
not need destruction. An owned slice of elements with Drop is explicitly
refused under `TCG-UNSIZED-ARG`; the view must not erase payload destruction.
Other unsized shapes retain their existing refusal paths. The same body view
is used by the unreachable-body shortcut for a function with an uninhabited
argument; its signature and entry block must still agree.

## Native evidence

The matrix passes **912,384 checks** across LLVM and CG at O0, O1, O2, and O3:
114,048 checks per execution. An independently LLVM-built driver and shared type
crate exercise both LLVM-to-CG and CG-to-LLVM calls.

Each execution varies 128 seeds, lengths 0 through 32, and eight starting
offsets. Ten receiving and ten forwarding functions place zero through nine
scalar arguments before the unsized slice and two after it, including a data
pointer in the final argument register with its length on the stack. Each
checks the full mutated payload, original buffer address, metadata, and scalar
argument values through an independently calculated result.

Additional cases cover owned UTF-8 strings, 64-byte-aligned aggregate elements,
32-byte-aligned zero-sized elements, two distinct function-pointer callees, and
a virtual call. A counting allocator verifies that live allocation count returns
to its prior value after each group of owned buffers. The baseline LLVM fixture
compiles at all optimization levels; the baseline CG fixture refuses all four.
The Drop-payload negative control remains LLVM-positive and CG-refused at all
four optimization levels. A second admission fixture checks an unsized argument
combined with an uninhabited argument. The first candidate refused it; the final
LLVM and CG matrices both compile it at O0 through O3. The two admission fixtures
run 16 compiler invocations in the permanent harness.

## Validation

All eight regression tests pass **10,430,832 checks** across borrowed slices,
wide projections, aggregate stores, and value layouts. The three existing
negative controls retain their named refusals.

Fresh CG core builds with 44 AArch64 object members and 1,281 hidden private
function definitions. Isolated and matching compiler_builtins builds each
contain 11 AArch64 objects, with all six expected floating-point helper exports
present as weak definitions. Both LLVM and CG consumers linked against the
fresh CG core and matching builtins pass **81,097 checks each**. The inspected
core definitions are present in the linked executable.

The strict bridge probe reports five functions, zero unmodeled shapes, and two
discharged scalar op-selection obligations. Mandatory machine proof still
refuses the probe at the existing opcode inventory gap: its first reported
function has 13 uncovered instructions across seven distinct opcodes, starting
with `StpPreIndex`. The separate ABI proof control also retains its existing
refusal: 14 uncovered instructions across 12 distinct opcodes, first at
`aliased_f32_read[13]` (`StpPreIndex`). Neither result qualifies machine proof.

Diagnostic compilation uses `no-proof-certs` and compiler verification is
disabled for this investigation. Detailed results are recorded in
`results.json` and the archived logs.

The final all-target check, new-file formatting checks, differential formatting
check, generated documentation checks, diagnostics inventory check, and
`git diff --check` pass.

## Identities

- Backend: `770df5a7b457930114911308a99b0ed9326ab90b5bbb64bb2fc8eb11d4fd662f`
- Harness: `36e6d05d0b59c837370a79b8fd6ab3dad3f7fa4706ca085ffb1ece1586fbda43`
- Investigation: `target/unsized-argument-investigation`
- Baseline: `reports/perf/2026-09-28-borrowed-slices`

The evidence archive contains **3,162 files** and **115,033,785 compressed
bytes**, including the 261 sealed source files. Every archived member was
independently rehashed. Archive SHA-256:
`20a0a08472d4f48e638932396af8f203aeff01202674756dc8527335d2ff12e6`.
The standard durable-evidence validator and plan citation check pass.

- Results
- Evidence archive
- Member hashes
- Archive identity
- Top-level inventory

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
