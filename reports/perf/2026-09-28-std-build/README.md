# Linux AArch64 std build census and compiler crash repairs

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Two compiler crashes are repaired: foreign statics no longer enter Rust
initializer evaluation, and 128-bit float-cast refinement no longer overflows
while constructing integer bounds. The updated backend passes native regression
checks. **Full std support, mandatory machine proof, self-hosting, and strict
compile/runtime speed qualification against LLVM and Clang remain open.**

## Changes and validation

Foreign statics now declare external storage directly. Linux AArch64 weak
imports use an undefined weak symbol plus a hidden pointer cell containing its
address. The linker coalesces that cell across function objects, preserving
address identity for direct readers and pointers embedded in static initializers.
An absent weak symbol produces null. TLS and unsupported import linkages retain
explicit refusals.

The permanent LLVM/CG O0–O3 matrix passes **32 executions and 524,384 checks**.
It covers ordinary immutable and mutable imports, present/absent weak function
and data symbols, mutation through an imported pointer, saved static addresses,
and PIE/non-PIE links. ELF inspection checks weak undefined bindings. The valid
baseline fixture compiles and runs with LLVM but crashes with CG at all four
optimization levels. An earlier invalid linkage-bearing mutable-static probe
is retained as a rejected fixture and is excluded from that comparison.

Float-to-i128/u128 bounds and SMT constants now preserve both limbs. The concrete
SMT evaluator also returns 128-bit results for these conversions. The new unit
regression checks **33,076 cases** against Rust casts, including saturation
boundaries, NaNs, infinities, and random bit patterns. The broader 103 MIR and
38 floating-point unit tests pass. Separate native CG O0/O2 programs pass
**66,152 checks** against an LLVM-built Rust oracle; the baseline backend crashes
on both builds of that minimal reproducer.

Five existing regression tests pass, covering private function linkage and its
refusals, static alignment, optimized alloc, and native sysroot layouts. The three
matrices that print check totals contribute **4,287,752 checks**. The all-target
build check, formatting, documentation and diagnostic inventories also pass.

## Full std dependency graph

The installed compiler's library sources are copied unchanged except for the
workspace member list and its resulting lockfile pruning. The workspace selects
`std`; `backtrace` and `panic-unwind` are enabled, with normal dev unwind and
overflow-check settings. A missing path dependency, `trust-memchr`, is restored
from the exact compiler Git revision. Nine registry source packages are frozen.
The offline lock adjustment removes ten unused packages and adds or changes no
package versions. This covers the std graph, not the separate proc_macro, test,
or Trust bignum sysroot members.

LLVM builds all **20 target crates including std**. The fresh CG build attempts
19 dependencies: **6 pass and 13 fail with 182 named unsupported roots**.
Dependency failures prevent Cargo from attempting std. Previously gimli crashed
and the remaining failures reported 145 roots; it now completes diagnostics with
37 roots. The other dependencies retain exactly their previous failed-root lists.
These counts describe the unwind-enabled std graph. The earlier successful
core/alloc campaign used its recorded panic-abort configuration.

| Dependency | Failed roots |
| --- | ---: |
| core | 46 |
| gimli | 37 |
| object | 25 |
| compiler_builtins | 19 |
| rustc_demangle | 16 |
| addr2line | 9 |
| alloc | 7 |
| std_detect | 7 |
| libc | 5 |
| miniz_oxide | 5 |
| hashbrown | 4 |
| adler2 | 1 |
| panic_unwind | 1 |

An isolated std build using the successful LLVM dependency artifacts reaches a
complete **426-root O0 diagnostic result**. The baseline crashes while resolving
`pidfd_spawnp`; the first repair retry reaches a five-minute resource limit.
The final backend completes within the recorded 15-minute budget. This isolated
build diagnoses std itself; it is not a successful build of a CG sysroot.

The isolated O2 std run hits its **900-second resource limit** and is terminated
with SIGTERM. It does not reach the complete root inventory. Its partial
compiler diagnostics are retained; an empty `failed_roots` field in this timed
out record does not mean the build passed. O1/O3 std and the remaining sysroot
members still require qualification.

The remaining failures include unwind continuations and cleanup SSA transport,
terminate-pad activation, native collection/iterator layout handling in std's
third-party dependencies, SIMD intrinsics, and projected memory operations.
Exact named roots and compiler invocations are retained in the census records.

## Proof and measurement boundary

Strict bridge probes pass at O0/O2: 11/7 functions, 6/4 pushed refinement
obligations, zero unmodeled shapes and no skipped obligations. These probes cover
the bridge's modeled obligations; they do not establish complete linker or
machine semantics. Mandatory machine proof still rejects uncovered AArch64
instructions, including stack operations and relocatable addresses.

Every compiler and native run here is a diagnostic run with Trust frontend
verification disabled. Resource-limited or failed builds are retained as failures.
Concurrent diagnostic wall times are not performance comparisons. This report
makes no compile-time or runtime advantage claim.

## Reproduction and identities

The evidence archive contains exact commands, logs, source snapshots, patches,
native objects/executables and their identities. It freezes a 3,044-file snapshot of
the std and registry source inputs. The compiler, backend, test binaries,
and generated libraries are identified by hashes. Build the archived backend
sources in the recorded environment, run the std graph and isolated crate
probes, then the unit, native, regression and proof checks.

Backend SHA-256: `9942907452992f42ea368de0cd1e9e1690b34d85ccc77440f58200a7d7b48aa4`.

The archive contains 23814 independently rehashed files and 275 source files.
Archive SHA-256: `d2d822907f57bd6526b89b0c5ec586bc67e558421b66f6067fc49496367ea05c`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
