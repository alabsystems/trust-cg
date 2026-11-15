# Linux AArch64 scalar-union storage

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Address-taken scalar unions now keep their real storage when constructed or
assigned from an SSA scalar carrier. Calls returning those unions retain their
cleanup and ABI-termination edges. Optimized core improves from seven to six
unsupported functions, removing `core::hint::select_unpredictable::<usize>`;
none of the six remaining failures changes. O0 core still builds successfully.

## Implementation

A union destination that already has a memory slot uses its union storage
layout even when its by-value ABI is scalar. A whole-carrier assignment requires
identical normalized union types, agreement with the declared scalar ABI, and
an exact match between carrier width and storage size. A construct writes the
active field at offset zero; a zero-sized field leaves the storage untouched.
The Bool-to-Bool transmute is an identity and does not admit integer-to-Bool
reinterpretations.

Union-returning calls use the existing normal-continuation helper. Alias reloads
and the result store execute only after a successful return. Cleanup and
termination edges remain attached to the call, including when a Rust callee
panics inside a non-unwinding C entry point.

## Validation

The permanent storage fixture passes **3,407,872 checks in 16 executions**,
comparing LLVM and trust-cg at O0–O3 under abort and unwind policies. It covers
word, wide integer, pointer, Boolean, character, float bit patterns, reference,
function pointer, custom and partial union fields, write-before-read uninitialized
storage, reassignment, copying, and scalar selections matching core's generic
implementation.

The required aggregate pair-selection refusal remains at O0/O2. Both compiles
fail with the named unsupported intrinsic. LLVM compiles, links and runs the
same pair fixture. A refused compile may leave partial objects; if present,
they must fail to link because the required private callee is undefined. This
checks the actual failure boundary rather than treating every partial object
as a complete successful build.

The union-return cleanup fixture checks normal returns, live aliased mutation,
post-call actions and destructor execution after a caught panic. It passes
20,480 checks in eight executions. The expanded termination suite passes
90,112 checks in 16 executions and **88 required SIGABRT cases**, retaining four
named refusals. Related union-constant, associated-drop and wide-overflow
regressions also pass. The combined counted total is **5,721,056 checks in 80
executions**, with 13 named refusals and two additional LLVM link/run controls.

Core O0 succeeds; the O2 census finishes with six failures, without a timeout.
The remaining failures are two borrowed slice-iterator cases and four
network-address formatting reference cases. This is not a full std build or a
compiler performance win.

## Proof boundary and artifacts

Strict bridge-mode compilation accepts the fixture at O0/O2, covering 71/26
functions with zero unmodeled shapes. It generates **zero scalar refinement
obligations** and records no memory-refinement trace: these storage operations
remain trusted bridge behavior. This is admission/shape coverage, not a claim
that their correctness was formally proved. With machine certificates required,
both probes refuse with `TCG-PROOF-465`, including missing evidence for the emitted
frame and memory instructions. No refusal was converted into proof credit.

Backend SHA-256:
`671ddbff5a115d17657dfc497b16bbb86568d4eb1cbaf055fcb5911ad93f9d24`.
The exact build source hashes are in `merged-source-1.json`. Native executable
receipts identify the first harness used for the extended unwind controls and
the second harness used for the final storage/refusal test. Subsequent verifier
fixture-only edits and formatting do not change this backend's production
behavior. Builds and fixtures use the Trust-authored ae9c2c1d Linux AArch64
toolchain and diagnostic `no-proof-certs` code generation for runtime tests.

These logs and receipts are thin evidence. Binaries and full runtime artifacts
remain local under `target/scalar-union-storage-investigation/`; the core census
outputs are under `target/main-alignment-20260929/`. They are not independently
published here. Full Linux completion, machine-code proof and strict compile-time
and runtime wins over LLVM and Clang remain open.
