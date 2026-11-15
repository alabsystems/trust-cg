# Linux AArch64: from-end indexing through slice-tail DST pointers

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Optimized MIR can now read, write or borrow the final elements of a slice-tail
DST through the original wrapper pointer, using its real length metadata.
This fixes the refusal for `(*r).tail[-k]` while preserving the generic
projection walker's refusal when it cannot recover a runtime length.

## Source and admitted shape

Source commit `0d5622b19` adds a checked path in `slice_tail::projection`, shared
by reads, writes and borrows. `is_slice_tail_dst_element_place` establishes
that a leading dereference and field chain reach exactly the pointer's slice
or string tail, at its rustc layout offset and with the matching element type.
The address is `data + tail_offset + (length - offset) * element_size`.
`min_length` remains only the pattern's minimum; it is never used as the
runtime length. Rust MIR's pattern/bounds control flow remains in place.

The path is limited to Linux AArch64 and a terminal from-end `ConstantIndex`.
Further projection into an indexed aggregate, unrelated prefix projections,
other metadata kinds and other hosts do not acquire this path. The retained
negative case reads a field of the final aggregate element; it still receives
the named from-end/runtime-length refusal at O2/O3. Whole-element addresses
are covered positively. Existing shared-reference store checks remain.

Remote `main` through `6364a2a54` was merged as `d2f7f0d97`. Its change makes
seven standalone x86 option fallbacks follow the existing tracked Boolean
policy. The IR cohort remains `7917c1721483b7b17136f4a6e1b8d8acef392c2f`.

## Native and proof qualification

| Frozen artifact | SHA-256 |
| --- | --- |
| Before backend, source `9b08de131` | `51c1361202aa32382cea2d68f917a6dd6571640a66b86b5c8522c83494e82881` |
| Fixed backend (`third`), `d6071b196` plus recorded patch | `a5af0a42e0fdd4f7d4e86669dc78555ef781dcabab13c8b9537013c085511bd7` |
| Merged backend, source `d2f7f0d97` | `75bd0f02fe966dab78885ed363420e3133ce7842060956536fd56962a6cef0d6` |
| Permanent native harness | `053126d865d52c1cb16819879d2fca2c7371e564df15e31ffb35f498a70e9cc0` |

The initial direct-slice and small wrapped baselines use the preceding
`8a7a6700...` backend, as their per-step records state. Expanded and std
baselines use the before artifact above.

Both fixed and merged artifacts pass **72 executions, 9,622,400 counted
checks, 9,216 caught panics and six named refusals per backend**:

- New O0–O3 LLVM/CG tests under abort and unwind: 16 executions and 391,424
  checks. They cover direct-slice controls, transparent wrappers, sized and
  nested prefixes, u8/u16/u64 element strides, offsets one and two from the
  end, empty and short slices, mutable and raw pointers, full backing-array
  preservation, returned reference/pointer identity and aggregate element
  addresses. Four O2/O3 projected-field refusals remain, with LLVM controls.
- Existing slice-tail tests: eight executions and 915,920 checks.
- Dynamic Fn argument tests: 32 executions, 67,696 checks, 9,216 caught panics
  and two closure-target ABI refusals.
- Borrowed-slice tests: eight executions and 7,974,912 checks.
- Dynamic-tail tests: eight executions and 272,448 checks.

The two backend runs total **144 executions and 19,244,800 counted checks**.
Support-runtime setup controls and exploratory runs are not added. Native
comparisons disable frontend Trust verification and codegen proof certificates;
they establish behavior for these cases, not a machine proof.

Strict bridge tests use the nine-function expanded corpus at O0/O2. Each
backend reports 10/9 functions, 14/14 refined obligations, nine/nine memo hits,
zero skips and zero unmodeled MIR shapes. The corresponding proof-required
runs remain named `TCG-PROOF-465` failures. No proof admission was waived.

The incoming x86 changes pass **467 selected unit tests**: Boolean parsing 1,
peephole 240, LICM 58, bounds elimination 24 and vectorization 144.

## Standard library

The complete paired O2 census falls **219 → 216 failing roots**, removing
`Path::trim_trailing_sep`, `PathBuf::push_trailing_sep` and `PathBuf::__push`.
There are **zero added roots and zero changed diagnostics** among the remaining
roots. Both runs exit normally with compiler failure, without timing out:
711.708s before and 719.527s after. These are diagnostic census durations,
not a controlled performance comparison.

Commands are identical after normalizing the backend and output directory;
working directory and recorded environment are identical. Both use the same
recorded LLVM-built dependencies. The fresh before census also reproduces all
219 diagnostics from the preceding milestone. The latest completed O0 census
remains 197 failing roots; O0 was not repeated for this change.

A fresh CG-core/alloc O2 + LLVM-remainder build passes. Consumers load the
exact recorded dynamic std: LLVM and CG UTF-8 consumers each pass 81,097 checks,
reference formatting passes 21,504 checks, and runtime tests catch 112 panics
with 112 drops. The library hashes, per-crate invocations, ELF inspection and
loader logs are retained. This is a mixed library build, using the fixed
pre-merge backend; it does not establish fully CG-built std.

## Investigation and evidence

Direct slice patterns already worked at both optimization levels. The small
wrapped reproduction succeeds at O0 but fails at O2 when MIR folds away the
temporary slice reference. All nine expanded wrapper functions fail in the
before O2 corpus; their O0 controls pass. The fixed and merged corpora pass.

An initial prototype (`first`) changed only generic memory entry points and
left the O2 refusal unchanged: the dedicated slice-tail module intercepts those
accesses earlier. It was removed. The second build failed because its let-chain
syntax was not accepted in the bridge's Rust 2021 edition; `third` uses the
compatible syntax. These failed investigation/build logs are preserved and are
not counted as qualification.

Source commits, patches, module snapshots and complete source/input hash
manifests bind the builds. Native, proof, std and mixed-library transcripts
are attached; `assets.json` binds every attachment. Full CG std, self-hosting,
complete machine proofs and speed superiority over LLVM/clang remain open.
