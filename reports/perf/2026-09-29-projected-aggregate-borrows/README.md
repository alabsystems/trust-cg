# Linux AArch64 projected aggregate borrows

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

A borrowed aggregate field now gives its parent stable storage. The previous
storage scan asked whether the field needed a slot when borrowed as a whole
local. That missed flat aggregate fields: the borrowed-aggregate binding can
name a whole local, but cannot name an aggregate projection. An optimized
`Chars.iter` borrow in core exposed the gap.

The change admits nonzero, memory-eligible aggregate fields through fixed
Field/Downcast projections on Linux AArch64. It retains the existing closure
and Box<dyn> cases, checks that the parent has an admitted memory layout, and
leaves scalar, zero-sized and modeled collection boundaries in place. Mutations
through the reference and later whole-parent moves share the same Rust image.

## Results

The reduced cursor example refused at O0 and O2 before the change and compiles
at both levels afterward. The permanent native fixture checks mutable and
shared cursor borrows, nested fields at nonzero offsets, and a reordered struct
whose fields cover its complete storage. LLVM and trust-cg each pass O0–O3
under abort and unwind policies: **8,388,608 checks in 16 executions**.
A padded nested-copy variant retains its named partial-copy refusal at O0/O2.
The LLVM version of the original padded fixture ran successfully during the
exploratory test; this patch does not relax that separate copy restriction.

Seven existing regression tests also pass: projected aggregate values and
union/tuple images, their three refusal controls, borrowed aggregate captures,
closure wrappers, and zero-sized drops with four alignment refusals. Including
the new fixture, the counted total is **10,075,372 checks in 66 executions** and
**nine named refusals**. Counts come from the retained test logs.

O0 core builds successfully (165.48 seconds). The O2 census completes without a
timeout (364.01 seconds), reducing the failing function count from six to five.
`str::escape_debug` now compiles. `str::slice_error_fail_rt` gets past its iterator
borrow and reaches a raw-pointer conversion of a borrowed `Range<usize>`.
The four network formatting raw-reference failures remain. These timings are
census records, not controlled performance comparisons.

## Proof scope

Strict bridge probes accept O0/O2: 27/15 functions, 31/23 accepted scalar
refinement obligations, 10/6 memo hits, and no skipped obligations or unmodeled
shapes. Address-taking, layout and memory behavior are still reported TRUSTED;
there is no memory-refinement trace. Machine-proof-required probes both refuse
with `TCG-PROOF-465`, including missing frame and memory-instruction evidence.
Statistical sampling receives no proof credit.

Two initial core census attempts accidentally used the private proof cache,
changing the baseline solver policy. Long AY runs were explicitly terminated;
those incomplete attempts are not results. The qualified censuses use the
original recorded diagnostic environment. The separate strict/machine probes
use the private cache and the admitted AY identity.

## Provenance and availability

Production change: `61950566f`. Remote integration and synchronized checkpoint:
`e2a13fb50`. The merged bridge passes `check --lib`; generated inventories and
diagnostics checks pass. The frozen backend predates that remote integration:
`b8ecbdb0c73aa88fc6ba6f441210255138d93104ff7c5ea3ebb96ceb65feacf3`.
Its complete source hash manifest and patch name the exact build input. The
only subsequent formatting change before the production commit joins one line.
The native harness hash and proof/core receipts are in `results.json`.

These are thin evidence records. Full compiler logs, native binaries, core
artifacts and the frozen backend remain local under
`target/borrowed-iterator-investigation/`; independently published raw artifacts
remain open. No full std completion, complete machine proof, or compile/runtime
win over LLVM and Clang is claimed.
