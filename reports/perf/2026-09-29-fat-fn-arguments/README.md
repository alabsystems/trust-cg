# Linux AArch64: length-pointer arguments through dynamic Fn calls

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`&dyn Fn(&str, ...)`, `&mut dyn FnMut(&mut [T], ...)`, and borrowed
`Box<dyn Fn/FnMut>` calls now spread supported length-metadata pointers using
rustc's checked argument ABI. The completed O2 std census falls from **223 to
219 failed roots**, removing four `CStr` helper instantiations, with no added
or changed remaining failures. Full std, self-hosting, complete machine proofs,
and compile-time/runtime superiority over LLVM and clang remain unfinished.

## Change and boundaries

`spread_fn_call_tuple_untupled` receives the resolved virtual method instance.
On Linux AArch64 it asks `scalar_pair_param_plan` for each reference/raw-pointer
argument with length metadata, checking the exact untupled `ArgAbi` and lane
placement. It loads the two carriers from rustc's tuple-field and pair-lane
offsets and declares them independently. This preserves a pair that straddles
x7 and the outgoing stack. Ignored zero-sized fields retain their FnAbi indices.
Whole constant tuples use the existing relocation-aware byte spill.

This admits strings, slices, `CStr` and references to slice-tail structs. It
does not generalize by-value aggregate, owned-pointer, trait-object or i128
tuple spreading. Concrete closure/vtable/export guards remain, as do unsupported
indirect-return, dynamic FnOnce and Box cleanup-edge restrictions. The native
closure-target negative control still refuses the same tuple convention
mismatch at O0 and O2; LLVM builds and executes its independent control.

Source commit: `8f76b96f7`. Remote `main` through `aa8f85633` was merged as
`4b350f74e`, bringing x86 writeback-shape and Boolean branch-layout policy fixes.
The IR cohort remains `7917c1721483b7b17136f4a6e1b8d8acef392c2f`.

## Frozen artifacts and qualification

| Artifact | SHA-256 |
| --- | --- |
| Before backend, source `5e9bf7bbb` | `e02b0a80939f61beb2f3d065b462e5d6704fd9fc3f4b4a98677978e7cc932e5e` |
| First backend, `b315e85cf` plus recorded patch | `50272ffec97086de65431329493d119c5385fc6259f3c67ab9546bb457c66be1` |
| Merged backend, source `4b350f74e` | `8a7a67008a22397120e1c0c67db00cd15243f44ceb8652d7e5871f28b7339b71` |
| Permanent native harness | `7983a61e14e0325da54697692773be7729b05ebbaa4dc445ed0719c7153520d5` |

The first artifact predates final comments and permanent fixtures; the merged
artifact includes those changes and the incoming x86 work. Build commands,
source hashes, patches, exact artifact hashes, and test inputs are retained.
The initial minimal baseline used the preceding `a7dc0c2d...` backend, as its
per-step records state. Expanded, constant, Box, closure-target and std
baselines use the before backend above.

Both first and merged backends pass the maintained LLVM/CG comparisons at
O0–O3: **66 executions, 153,668 counted checks, 16,384 caught panics, 16 expected
SIGABRT terminations and six named refusals per backend**. This comprises:

- New dynamic argument cases: 16 executions, 61,552 checks, 9,216 caught panics.
  Coverage includes empty/nonempty strings and slices, mutation and FnMut
  state, raw slice pointers, CStr, sized-prefix/slice-tail DSTs, ignored ZSTs,
  mixed floating/integer arguments, two fat arguments, the x7/stack split,
  constant relocation-bearing tuples, exact panic payloads, and drop order.
- New borrowed Box calls: 16 executions, 6,144 checks under both panic policies.
  These callbacks return normally; their cases do not establish Box cleanup
  support. Two closure-target ABI refusals are also checked.
- Existing virtual-call controls: 24 executions, 49,152 counted checks, 7,168
  caught panics, 16 expected SIGABRTs, four refusals, and forced-unwind checks.
- Existing closure-wrapper and mixed-object controls: ten executions and
  36,820 checks.

The two backend runs total **132 executions and 307,336 counted checks**.
Exploratory probes are retained separately and are not added to these totals.
Frontend Trust verification and codegen proof certificates are disabled for
native diagnostic execution; these are behavioral comparisons, not proofs.

Strict bridge refinement/coverage runs at O0/O2 pass on both frozen backends:
13 functions, four refined obligations, zero skips, zero memo hits and zero
unmodeled MIR shapes in each run. Machine-proof-required runs still fail by
name with `TCG-PROOF-465`, including the existing exception-table and opcode
coverage gaps. No proof admission was waived.

The merged workspace also passes **246 selected unit tests**: 240 x86 peephole
tests, the branch-layout Boolean-policy test (six isolated child cases), and
five LEA writeback tests. Child processes are not added to the test total.

## std census and mixed libraries

Both isolated std O2 runs completed (exit 1, no timeout), using identical
commands apart from the backend/output paths and the same recorded LLVM
library dependencies. Durations were 717.839595 seconds before and 725.766776
seconds after; these concurrent diagnostic builds are not performance evidence.
All four removed roots are `small_c_string::run_with_cstr_stack` or
`run_with_cstr_allocating`, instantiated for a raw DIR pointer or u32 result.
The remaining 219 diagnostics are unchanged. The latest O0 census remains
197 from the earlier milestone; this report does not rerun it. The paired
census uses the first backend, before the incoming x86 merge.

A fresh CG-core/alloc O2 + LLVM-remainder library build passes. Dynamic
consumers load that exact recorded `libstd.so`: LLVM and CG consumers each
pass 81,097 checks, reference formatting passes 21,504 checks, and runtime
controls catch 112 panics with 112 drops. Library hashes, compiler invocations,
ELF inspections and loader traces are recorded. This qualification uses the
first backend and is not a fully CG-built std.

The earlier `mixed-first-O2` invocation mistakenly selected CG globally,
including third-party dependencies, and failed on existing unsupported SIMD
and other MIR. Its logs and scope note are retained as a harness-invocation
error; it is not counted as a mixed-library success.

`assets.json` binds each attached evidence file. The source/test changes and
this report remain separate from the unresolved compiler completion goal.
