# Linux AArch64 relocation policy and shared std linkage

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

AArch64 Linux object generation now obeys rustc's default or explicit relocation
model. PIC objects link into shared libraries and preserve function/data address
identity under symbol interposition. Coherent builds with CG core at O0/O1 and
LLVM dependencies now produce a working `libstd.so`. **Full CG-built std,
optimized unwind core, mandatory machine proof, self-hosting, and strict compile/
runtime wins over LLVM and Clang remain open.**

## Cause and repair

The bridge copied architecture, optimization and panic policy into its object
compile environment but left `CompilerConfig::relocation_model` at Static. Even
an explicit `-Crelocation-model=pic` therefore emitted direct page references to
externally binding function definitions. GNU ld rejected those relocations when
linking a shared library. The session model now reaches the common AArch64 Linux
module compile path, including its existing GOT selection and TLS dialect.
Static, PIE and PIC remain distinct; DynamicNoPic, Ropi, Rwpi and RopiRwpi are
explicit refusals. Other target routes retain their previous fixed access models.
No symbol hiding or linker workaround is used to make the shared link succeed.

A function taking its own address exposed another missing case. The current
function is registered as `FuncId(0)` before lowering, but its completed body is
added to the module afterward. Reification now uses the exact signature saved
when that body is classified, including ABI-lowered hidden parameters. Rust's
separate `FnPtrToPtr` cast also now transports a reified address to a thin raw
pointer with explicit source/destination type guards. Existing provenance,
layout, signature and machine-proof checks remain active.

## Validation

The permanent matrix passes **344,928 checks in 48 native executions**, comparing
LLVM and CG at O0–O3 under the target default, PIC, PIE and Static models. Shared
objects run with and without executable symbol overrides. Tests check function
and data address identity, direct and indirect calls, self-addresses, aggregate
returns, private callbacks, and independent TLS state in four threads. Object
relocations distinguish GOT access in PIC from direct page addressing in
PIE/Static, and shared objects contain no TEXTREL. Four unsupported relocation
models fail with the expected named diagnostic.

Two coherent standard-library graphs rebuild core with CG at O0 and O1 and all
other libraries with LLVM. Both produce a std dylib. LLVM- and CG-generated
consumers then exercise it through shared libraries against an independent C
UTF-8 oracle: **324,388 checks**. LLVM-generated panic consumers additionally
exercise **224 caught panics and 224 destructor executions**, checking original
payloads across dynamically linked CG core frames. Loader traces confirm the
specific rebuilt `libstd.so` is loaded. Symbol checks trace character counting,
UTF-8 validation and panic entry points from the CG core objects into the actual
exported std dylib. This is a mixed-codegen integration result, not a complete
CG-built standard library.

Sixteen broader regression tests pass **16,301,012 checks**, 104 SIGABRT
cases and four expected refusals. These include the earlier assertion/pointer,
borrowed-storage, enum, panic, unwind, ownership and caller-location cases,
foreign statics, and cross-crate private function linkage in batched and legacy
compilation paths. The all-targets build, formatting, documentation and diagnostic
inventory checks pass.

Core builds at O0/O1; O2/O3 retain the same **23 failing functions** and diagnostics.
The full CG dependency graph attempts 19 crates, with eight passing, eleven
failing, the same **103 failing functions**, and no compiler crashes. The isolated
O0 std build, using frozen LLVM dependencies, improves from **317 to 314 failing
functions**, with no added or changed failures. `Backtrace::capture` and
`Backtrace::force_capture` clear the missing self-signature error;
`set_alloc_error_hook` clears the function-pointer cast error. Every final census
completes without a timeout.

Strict bridge probes pass at O0/O2 over **17/14 functions**, with **12 scalar
refinement obligations and one memory refinement** at each level, zero unmodeled
shapes and zero skipped obligations. Mandatory machine proof remains refused
(`TCG-PROOF-465`). Development builds disable Trust frontend verification, and
concurrent test timings are not performance measurements.

## Reproduction and identities

The final backend is built by `build-fourth.py`, with `build-fourth.log` and frozen
`fourth-lib.rs`. The permanent matrix and regressions use `test-build-first.log`
and immutable `first.test`. Records retain the original non-PIC shared-link
failure, missing self-signature failure, unsupported function-pointer cast,
intermediate candidates, final commands, MIR, objects, shared libraries, native
executables, loader traces, source snapshots and artifact identities.

The same frozen 3,044 standard-library source files and registry inputs are
revalidated. Large backend, test and library archives are identified by hashes
alongside their source inputs and build commands. This is development evidence,
not a consolidated acceptance report reproducible from an anonymous clone.

Backend SHA-256:
`95b40231047aab143f689757a4c30d143310346997b3e09a175918c7f30dbdb4`.

Native test executable SHA-256:
`8914673df6c957cfdb3b408a37ddb85045fe003073f2fd8af8c38e793f4f33f0`.

The evidence archive contains 21,934 files and is 216,005,371 compressed bytes.
Every member was independently rehashed against `assets.json`.
Archive SHA-256:
`d413d72c9045c8dda0d159767aff034b226c6f4485d6f2037ee1280c529d3307`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
