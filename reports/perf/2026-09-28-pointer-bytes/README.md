# Linux AArch64 pointer byte images

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Thin raw pointers can now be materialized as eight-byte arrays after MIR folds
`pointer.addr().to_ne_bytes()` into a transmute. Optimized core improves from
**12 to 11 failing functions** at O2 and O3, removing `TypeId::as_u128` with no
added or changed failures. **Full Linux completion and strict compile/runtime
wins over LLVM and Clang remain open.**

## Change and boundaries

The new array assignment path requires a genuine thin Rust raw pointer, a
`[u8; 8]` destination, exact cast/destination type agreement, and eight-byte source,
destination and target pointer sizes. It casts the pointer value to I64 and
stores its address bits into the array with alignment one. It does not read
through the pointer. The local pre-scan gives these destinations real storage,
even when their address is not otherwise observed. Metadata-bearing pointers,
reference sources and other element types do not enter this new path.

Taking a raw address of a thin raw-pointer variable now gives the variable a
scalar storage cell. Aliased writes and subsequent direct reads therefore use
the same storage. The new predicate requires an actual Rust raw pointer and
an admitted pointer-sized scalar leaf; reference chains and pointer-like
collection models retain their existing handling.

The tuple-pointer transport admission check now allows independent, flat arrays
of primitive elements. Their element IDs are resolved and checked before
admission. Such arrays cannot hide access to a declared tuple layout. Arrays
containing tuples or nested arrays remain rejected; descriptor validation,
tuple-use accounting and the requirement that every descriptor be used remain
intact. No tuple descriptor is stripped or reinterpreted.

## Validation

The permanent C oracle passes **43,909,120 checks in 16 native executions** with
CG and LLVM, O0–O3, and abort/unwind codegen policies. It tests plain and observed
pointer images, mutable pointers, replacement through an opaque raw-pointer
alias, byte-array returns and a two-pointer iteration matching TypeId's byte
assembly. Null, one-past and interior pointers are inspected without reading
their pointees. Related usize/u128 conversions run in both directions with high
bits, one-bit values, zero and all-ones values. Buffers use every offset 0–16;
byte checks cover the entire buffer, including canaries and unchanged inputs.
The executables link the selected compiler's real Rust runtime, with a separate
SIGABRT control. The pointer-byte fixture does not itself unwind.

All **24 tuple-layout contract tests** pass. New cases accept a primitive-array
allocation alongside an independently declared reordered tuple behind a pointer,
and reject direct and nested arrays containing that tuple on every native entry.
Twenty-one broader regressions pass **20,094,516 checks**, 104 explicit abort cases
and 14 expected refusals. They cover the existing storage, ownership, enum,
panic/unwind, linkage, relocation, pointer-image, TypeId and initialized-constant
paths. All-targets build, formatting, documentation, diagnostics and diff checks
pass.

Core builds at O0/O1 and has **11 failures** at O2/O3. The full CG graph attempts
19 crates: eight pass, eleven fail, with **103 failing functions** and no
compiler crashes. Isolated O0 std improves from **314 to 310 failing functions**, against
frozen LLVM dependencies, with no added or changed failures. The four removed
refusals are Unix aligned allocation, stack-guard/stack-start queries and the
home-directory fallback, all using raw addresses of borrowed pointer variables.
A separate C oracle for that borrow form passes 2,424,832 checks across LLVM/CG
O0–O3, observing the replacement and surrounding byte canaries. All censuses finish
without a timeout.

Two mixed graphs use CG core at O0/O1 and LLVM for the other std crates. Actual
std-dylib consumers pass **324,388 UTF-8 checks**, **224 caught panics and 224
destructor executions**. Loader traces and exported-symbol checks identify the
rebuilt libraries and exercised CG core objects. This is not full CG-built std.

Strict bridge probes on the permanent corpus pass at O0/O2 for **35/14 functions**,
with **18/7 scalar obligations**, **14/6 memory refinements**, zero unmodeled shapes
and zero skipped obligations. Mandatory machine proof still refuses with
`TCG-PROOF-465`. These probes do not establish complete semantic proof for the
new paths. Development compilation disables Trust frontend verification, and
concurrent build durations are not performance measurements.

## Evidence and continuation

The archive preserves baseline and first-candidate failures, the initial C-only
link failures from missing Rust panic symbols, and corrected runs linked to the
real runtime. The lower-test build setup and assertion-formatting failures are
also retained. Only the second backend and the final immutable native and tuple
contract test executables qualify this report.

`build-second.py`, `test-build-final.py`, `unit-retention.py`, `runtime-final.py`,
`qualify-final.py`, `post-graphs-final.py`, `check-dynamic-final.py` and
`compare-final.py` preserve commands and terminal results. The archive rehashes
all **304 current source files**, the prior **299-file snapshot**, two additional
tracked baseline files taken from the recorded Git revision, all **3,044 frozen
std sources**, compiler identities and registry inputs. It includes source
snapshots, MIR, native objects/executables, shared libraries and loader traces.
Large backend/test/library archives are identified with reproduction commands
instead of duplicated. This is development evidence; consolidated clean-source
acceptance, full std, proof closure, self-hosting and performance qualification
remain unfinished.

Read-only `next-select-body` probes reproduce the optimized-core scalar-union
construction refusal for usize, u128 and thin pointers. Direct scalar calls to
`core::hint::select_unpredictable` use an existing scalar-call lowering and pass;
the copied generic body exposes the failing construction after inlining. LLVM
O0/O2 and CG O0 native controls pass 106,496 comparisons, including the LLVM pair
controls; pair selection remains a separate unsupported-intrinsic boundary.
`next-union-storage` further isolates address-taken `MaybeUninit::new` storage,
with 110,592 passing native checks across LLVM O0/O2 and CG O0.
These probes do not alter the qualified backend.

Backend SHA-256:
`6b1b217037a223e7495487c92c1705ad32fc7f6bf379bd24369a11b2b717ecf1`.

Native test executable SHA-256:
`4ad93877935fac44cf65c4bdc77cb35d27e6ebfab757bad98f86099f00d79c7a`.

Archive SHA-256: `9bb6f793e647c8222606a9667702d00c7423b4b74a0047b20e8ce23feb5ea9d7` (23,786 files, 248,611,654 compressed bytes); every archived file independently rehashed.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
