# rustc_codegen_trust_cg

`rustc_codegen_trust_cg` is the experimental rustc-private bridge for
[trust-cg](../../README.md). It lowers a bounded subset of monomorphized rustc
MIR into trust-ir and uses trust-cg to produce native code.

> **Status — 0.x research preview.** This bridge is an evaluation surface,
> not a general Rust codegen backend or a replacement for LLVM, Cranelift, or
> rustc's production backends. It accepts selected MIR, layout, ABI, runtime,
> and target shapes and deliberately rejects many others. Read the
> [trust-cg limitations](../../LIMITATIONS.md) before evaluating generated code.

## Why this is a standalone crate

This crate and the root trust-cg workspace pin the same toolchain: its
[`rust-toolchain.toml`](rust-toolchain.toml) and the root's
[`rust-toolchain.toml`](../../rust-toolchain.toml) both select the custom
`trust` channel (the root since 2026-09-28). It is still a workspace of its
own, because it:

- uses unstable `rustc_private` APIs, which only the Trust package's private
  compiler libraries provide;
- is built as a `dylib` for `trustc -Zcodegen-backend=<path>`, so the
  compiler that builds it must be the one that loads it; and
- has an empty `[workspace]` table in [`Cargo.toml`](Cargo.toml), so its
  compiler-private requirements do not affect the root workspace.

The rustc-internal API and dylib ABI are unstable. A toolchain-pin change must
be accompanied by a clean bridge rebuild and its focused regression tests.
Integration tests record the actual build compiler and use that exact driver for
backend loading and reference compilations. The current pin requires a coherent
installed Trust package, including matching `trustc`, `targo`, sysroot and
private compiler libraries. Historical stock-nightly results do not qualify
this compiler migration. Differential tests explicitly disable frontend
verification on both CG and LLVM sides; they do not establish a verified
backend build, verified-default authority, or self-hosting.

## Build

Install a matching Trust toolchain package and a native linker, with that
package's `trustc` and `targo` on PATH. From the repository root, the availability
probe checks their compiler/sysroot identity and private libraries, then
performs an explicitly unverified locked release build:

```bash
scripts/run_full_test_matrix.sh --check-rustc-backend-env
```

For the same diagnostic lane, after checking the matching package:

```bash
cd crates/rustc-codegen-trust-cg
RUSTC="$(command -v trustc)" targo --unverified build --release --locked
```

The resulting backend is
`target/release/librustc_codegen_trust_cg.dylib` on macOS or
`target/release/librustc_codegen_trust_cg.so` on Linux.

### Compiler capability probes

The build script checks the selected compiler's private API instead of treating
every compiler failure as an absent feature. Public throwaway probe functions
remain usable under `-Dwarnings`. Same-private-crate controls must compile.
An alternate API requires the exact missing-field/import or changed-shape
diagnostic at the authored source span. The alternate `MonoItem` import must
also compile.
The scalar-pair selector requires complete constructors and readers for the
selected tuple or explicit-offset structure. Both Scalars retain their validity
information; the modern declared offset is preserved rather than recomputed.
Unknown shapes and required-field/type changes abort.
The independent cast-padding selector requires a complete constructor/read and
all four CastTarget payload fields. The reader borrows the original target and
preserves every modern u8 padding count; the legacy boolean maps to zero/one.
Consumers retain named refusals for leading dummy arguments they cannot emit.
The independent indirect selector requires complete sized/unsized descriptors,
all argument attributes, address spaces and every modern indirect mode. Its
shared reader preserves metadata arity and original attribute borrows. Nonzero
address spaces, kernel-specific modes and invalid stack/metadata combinations
retain named refusals; consumer layout and target checks remain separate.
The independent float-format and register-kind selectors require complete enum
matches and the typed vector-hint constructor/reader. Format identity is checked
before using a width: bfloat16 and IBM double-double retain named refusals,
including the special two-f64-register IBM carrier. Equal byte widths cannot
alias supported IEEE carriers. Existing IEEE width and consumer limits remain;
this floor does not implement additional floating types.
The independent scalar-pointer selector requires the exact missing result method
and a working typed conversion/provenance reader. A shared conversion checks
scalar width before calling a direct-pointer API, preserving the legacy
fall-through for non-pointer constants. It forwards the complete pointer;
integer addresses retain no allocation provenance and consumer checks remain.
The independent synthetic-terminator selector requires a complete top-level
constructor and typed source/kind reader. Its factory forwards the original
span, scope and complete operation, using empty legacy global attributes only
where the existing synthetic Return/Drop callers already require that policy.
Existing operation metadata must be retained by cloning or retargeting the
original descriptor. Goto loop-hint emission remains a separate task.
The independent Goto selector requires complete construction and original-kind
borrowing. Read-only successor views retain the original operation; fresh
connectors start with empty hints. Moving an entry block retains its complete
metadata and retargets existing edges in place; the assembly connector receives
its own fresh block and the original source origin. Actual hint emission awaits
a qualified typed IR carrier. The current API port compiles, while complete
real hint emission remains a separate qualification frontier.
The independent SIMD lane-count selector requires the exact old `u64` method
absence and a complete typed reader for the selected representation. Its
borrowed reader returns the original fixed-vector count at full width. The
existing f16 pointee-shell consumer still requires four/eight lanes, exact
size and alignment; f16 values retain their existing refusal.
The independent function-item selector requires typed complete argument
reading and fresh construction for the selected FnDef shape. Its view retains
the original binder and reads values only when no bound variables escape.
Unused declarations and binders inside nested function-pointer types remain
valid. Fresh types built from Instance arguments use a new empty binder;
existing source descriptors stay in their original view.
Two independent clause-query selectors retain explicit supertraits and full
usage-site constraints. Their readers preserve the original early binder,
generic parent and clause/span slices; associated-type implications and
explicit-only constraints do not substitute for those query contracts.
The reconciled Linux qualification
builds both available API profiles and passes the complete process/installed
consumer checks. Current-API native execution is bounded to the linked scalar
and provenance fixtures; the complete modern graph remains unfinished.

An advertised `-Ztrust-ir-cg-args` option with a missing field aborts the build,
so accepted operator arguments cannot disappear into the legacy empty-list path.

The option listing and each compiler process have a 60-second execution/capture
budget and a 1 MiB limit per output stream. Tool, malformed-listing, flag,
verification, incomplete-output and ambiguous-diagnostic failures abort the
build. Where advertised, `-Ztrust-verify=off` is appended after ambient flags
**only for discarded type-check probes**; the actual backend's build flags and
verification requirements are unchanged. Compiler identity remains
compiler-reported, not a binary attestation. Cleanup targets only the direct
child and does not guarantee termination of escaped or OS-blocked processes.

The process-contract regression compiles this actual build script as a small
standalone binary with the installed Trust package and drives controlled
compiler fixtures:

```bash
# From the repository root; does not compile or qualify the Trust bridge dylib.
BRIDGE_PROBE_TARGO="$(python3 -B scripts/trust_toolchain.py --print targo)" \
BRIDGE_PROBE_TRUSTC="$(python3 -B scripts/trust_toolchain.py --print compiler)" \
  python3 scripts/tests/test_bridge_build_probe.py
targo --unverified test --locked --offline --manifest-path \
  scripts/tests/fixtures/bridge_build_probe/Cargo.toml -- --test-threads=1
```

The fixtures use real compiler lint/type diagnostics on ordinary-Rust
stand-ins and retain per-case arguments and outputs. They test classification
and process supervision, not actual Trust API compatibility or compiler proof.

## Minimal invocation

Still in the crate directory, compile the included smoke program with the
exact Trust compiler used to build the backend. This smoke invocation explicitly
turns frontend verification off, just as the differential tests do:

```bash
BACKEND="$(find target/release -maxdepth 1 -type f \
  \( -name 'librustc_codegen_trust_cg.dylib' \
     -o -name 'librustc_codegen_trust_cg.so' \) \
  -print -quit)"
test -n "$BACKEND"

trustc --edition=2021 -Ztrust-verify=off \
  -Copt-level=0 \
  -Zcodegen-backend="$BACKEND" \
  examples/hello.rs \
  -o target/trust-cg-hello
```

[`examples/hello.rs`](examples/hello.rs) intentionally loops forever. Producing
the executable exercises backend loading, MIR admission, object emission, and
linking; the integration test runs it under a bounded timeout.

This command uses the selected compiler's existing sysroot. It does not rebuild
`core`, `alloc`, or `std` with trust-cg and is not self-hosting evidence.

## Compile phases

`codegen_crate` lowers the crate's mono items to trust-ir while rustc's type
context exists. The object compile of the lowered modules, the batched per-CGU
compile and its per-function fallback, runs in `join_codegen` after rustc has
dropped the type context (`OngoingCodegen` in `src/lib.rs`). Every decision the
compile's failure handling needs from the type context is taken before
`codegen_crate` returns (`FailureRoute`, `CompileCtx`), so a compile error
takes the same fail-closed route, with the same diagnostic, as when the compile
ran inside `codegen_crate`; `tests/unsupported_program.rs`
(`no_mangle_roots_are_never_dropped_when_their_object_compile_fails`) pins that
a required root refused at object emission is a named failed root, never a
dropped record. Moving it changed no emitted byte and lowered the
compiler's peak RSS (L14-P10,
[report](../../reports/perf/2026-09-29-darwin-l14p10-size-memory/README.md)).

## Supported surface and fail-closed boundary

The current contract is the conservative
[`rustc-mir-coverage-inventory.md`](../../rustc-mir-coverage-inventory.md).
It classifies mono items, rustc ABI/layout facts, MIR statements, rvalues,
terminators, and intercepted `core`/`std` calls as supported, partial, or
fail-closed. The
[`trust-cg replacement-readiness ledger`](../../trust-cg-full-replacement-ledger.md)
records the broader blockers.

In particular:

- the bridge consumes actual rustc `FnAbi`/`PassMode::Cast` decisions for a
  bounded Linux AArch64 C homogeneous floating-point aggregate lane, not the
  complete Rust ABI or pass-mode model;
- MIR places, projections, aggregates, statics, TLS, trait objects, drops,
  unwinding, coroutines, assembly, runtime integration, and target ABIs are
  covered only on named, bounded paths;
- projected scalar-cell reads and statement writes use the actual cell only
  for layout-checked, zero-offset, full-cell primitive fields through
  single-field structs/tuples; unsupported layouts, projected references and
  genuine projected call results retain their fail-closed boundaries;
- references to supported aggregate locals stored in closures or other
  aggregates use stable rustc-layout storage, including reference copies and
  branch-selected referents; borrowed arrays retain that storage after MIR
  inlining removes the closure environment;
- scalar return places with stack-cell storage load their current value at
  return, including when MIR constructs the result before borrowing it;
- tracked function definitions and direct/virtual calls carry rustc's hidden
  caller-location pointer; the intrinsic and panic paths resolve inlining
  scopes with rustc's own location-boundary helper;
- pointers to unpacked struct chains ending in a trait object carry the whole
  struct address and the terminal tail's vtable; field projections and layout
  intrinsics account for runtime alignment at each level. Checked paths include
  concrete unsizing, supertrait upcasts, scalar prefix access, tail reborrows,
  metadata extraction and reconstruction; packed chains, extra dereferences
  inside a projection and projected unsize destinations remain outside this
  extension;
- loop back-edge validation models core's inherent overflowing integer calls,
  checked tuple fields, empty branch arms and conditional exits with one
  continuing path; unsigned division by a constant power of two has an exact,
  width-checked equality rule against the corresponding logical shift;
- modeled integer loops include i128/u128 arithmetic, full-width constants and
  complements; wide checked arithmetic uses exact carry, sign and guarded
  division identities, and wrapping add/sub/mul calls lower directly at O0;
- Linux AArch64 i128/u128 casts to f32/f64 preserve both integer halves and
  call the destination-specific compiler-runtime conversion. The
  [rounding and runtime regression](../../reports/perf/2026-09-28-wide-int-float/README.md)
  covers direct and indirect calls, live values across calls, and conversion
  routines compiled by trust-cg; machine and scalar-refinement proof gates
  remain open;
- projected integer fields in memory-backed aggregates support complement
  and negation through the scalar arithmetic and layout-based store paths;
  Linux AArch64 small indirect aggregate arguments follow rustc's pointer
  convention at definitions and ordinary direct, function-pointer and virtual
  calls. The [memory and argument regression](../../reports/perf/2026-09-28-memory-unary/README.md)
  covers nested fields, mutation through callbacks, stack arguments and checked
  negation overflow;
- borrowed fieldless enums retain their current tags in stable storage, and
  aggregate arrays reuse the validated whole-slot transmute and pointer layout;
  the [enum and array regression](../../reports/perf/2026-09-28-enum-discriminant/README.md)
  covers literal construction, unsigned 128-bit constant images, aliases, loops
  and partial forward/reverse array iteration;
- Linux AArch64 scalar `fmadd`, `fsqrt` and `frintn` assembly supports matching
  f32/f64 registers, one output and `pure, nomem, nostack`, including loop-carried
  outputs. The [hardware and compiler-builtins regression](../../reports/perf/2026-09-28-aarch64-fp-asm/README.md)
  qualifies these bounded forms and a complete diagnostic compiler-builtins
  archive; strict bridge refinement and machine certificates still refuse;
- sized values and bare slices/strings support `size_of_val` and `align_of_val`
  using rustc's layout and the pointer's current length metadata. The
  [value-layout regression](../../reports/perf/2026-09-28-value-layout/README.md)
  covers packed and padded elements, high alignment, projected and selected
  metadata, loops and zero-sized slices with large lengths;
- Linux AArch64 wide owning-pointer wrappers use a layout-checked two-word
  image for arguments, returns, construction and field storage. Rust pointer
  pairs split correctly between x7 and the stack when one argument register
  remains. The [owner transport regression](../../reports/perf/2026-09-28-wide-owner/README.md)
  covers Box, Rc, Arc, CString, nested wrappers and callbacks in both directions;
- explicit length-metadata pointer casts to thin raw pointers select the data
  address. Projected wide-field transmutes and checked carrier reads preserve
  both pointer words, including scalarized pair bindings. The
  [pointer-image regression](../../reports/perf/2026-09-28-pointer-image/README.md)
  checks CStr, slice-tail headers, NonNull, nested fields and borrowed owners;
- Linux AArch64 default-section statics, nested immutable allocations and
  pointer-free TLS templates preserve their allocation alignment above eight
  bytes. The [static-alignment regression](../../reports/perf/2026-09-28-static-alignment/README.md)
  checks 16–4096-byte alignment, ELF sections and relocations, zero-fill storage
  and independent thread-local values;
- monomorphized control flow follows rustc's own reachable-block traversal,
  removing constant-dead calls the item collector does not schedule; direct
  empty drop-glue shims branch to their successor, while live and indirect
  destructor calls retain their ordinary lowering;
- Linux and Darwin AArch64 function emission preserves rustc's CGU-local
  identities using distinct hidden symbols across split objects (ELF
  `STV_HIDDEN`; Mach-O `N_PEXT`, spelled `__trust_cg_private.<cgu>.<n>.<symbol>`
  so the item stays readable in the linked image); calls, callback statics and vtables share
  the same symbol plan. rustc's weak and link-once definitions (functions and
  statics) are weak symbols, a hidden `External` definition is hidden, and
  `available_externally` emits no definition; `common`, extern-weak
  definitions and weak thread-locals are refused as `[TCG-LINKAGE]`
  (`src/function_linkage.rs`, ledger L06-P7). Only Darwin AArch64 is
  measured: Linux weak statics share the path without a Linux run, and a
  `linkonce_odr` function is plain `weak external` where LLVM's is
  automatically hidden. Exported upstream statics
  retain their canonical storage, as established by rustc's export metadata.
  The
  [function linkage regression](../../reports/perf/2026-09-28-function-linkage/README.md)
  covers independent crates, multiple CGUs and both batch and legacy emission
  on Linux; `tests/linkage_macho_aarch64.rs` is the Darwin symbol-binding
  differential against LLVM's objects and the weak/strong resolution through
  ld64;
- checked integer results returned or borrowed as `(T, bool)` use layout-based
  field stores, including i128/u128 add/sub/mul. Memory and scalar results share
  the same arithmetic lowering; the 128-bit path composes existing primitives;
- a bounded fallback proves scalar threading when every source path and every
  emitted-IR path to a latch produces the same expressions over header scalars.
  Read values may remain unknown only when the final expressions are independent
  of them. No branch assumptions are added; path disagreement, address-taken
  source locals, unmodeled calls and traversal-budget exhaustion still refuse;
- the x86-64 and AArch64 evidence is asymmetric and host-dependent; and
- unsupported shapes are expected to stop compilation with a named diagnostic,
  including dedicated `TCG-*` guards, instead of receiving a guessed lowering.

Fail-closed checks are regression boundaries, not a proof that an alpha backend
contains no crashes, hangs, or wrong-code bugs. An unlisted Rust program must
not be assumed supported merely because it compiles.

### Bounded closure Pair transport

Eligible ARM64 non-Windows ordinary closure bodies use the same compiler-derived
two-scalar argument plan at declarations, body entry and hand-built iterator
calls. Preflight every argument before emitting loads, copies or fresh IDs;
preserve ignored-ZST source ordinals and receiver offsets. The closure environment
itself, closure shims/coroutines, slice/trait-object fat pointers and unsupported
return carriers do not become admitted by this rule. Single-result iterator
calls still refuse Pair/sret results. Linux eligibility is not new Linux
execution qualification.

Mapped two-leaf aggregate Vec collect/extension follows the actual reachable
standard-library body instead of a scalar modeled interception. Capture/type
walks are bounded and deduplicated; aggregate callback state still refuses the
scalar-only modeled fold/for_each routes. This is not a purity whitelist or a
replacement sorting algorithm.

With installed Trust9192, `targo --unverified` and native certificates off,
Darwin controls execute all16 LLVM/TrustCG rlib/bin combinations at O0–O3,
including argument-register exhaustion. Cached-key sorting now executes all4
levels with exactly4 callback invocations, rather than four named refusals or
the incorrect9-call uncached algorithm. Retained sort-order coverage remains
10 native matches/6 named refusals, and sub-slice loops16 native matches. The
older closure/register-exhaustion target also passes unchanged. Both new native
targets are required by the Darwin gate, with an exact test-owned summary and
an attributed native-run/certificates-off marker; refusal-only runs fail.

The broader bridge library remains **590 passed/20 failed**: the20 memory
refinement cases report incomplete or self-check-rejected AY certificates.
Warnings-denied all-target bridge Tippy remains red with355 diagnostics; their
primary source lines are unchanged from the predecessor, but that source audit
is not a predecessor lint rerun or a green whole lint gate. Preserve those
failures in `reports/2026-10-09-closure-body-*` receipts. This scoped native ABI
repair is neither verified Rust, native certificates, whole Rust coverage nor
a TY/TLC time or memory comparison.

### `StepBy` rule

The modeled `std::iter::StepBy` path is available only at
`-Copt-level=0` with the pinned compiler's default MIR-inlining settings. The
bridge rejects `StepBy` at O1, O2, and O3, and also rejects O0 sessions that
explicitly enable normal MIR inlining. Inlined standard-library methods can
observe internal iterator state that the bridge represents differently.

At default O0, modeled consumers and direct `next` use remain available.
Unmodeled state-observing methods such as `size_hint` still fail closed. The
dedicated optimization-level diagnostic is `TCG-STEPBY-OPT-LEVEL`; the
unmodeled-method diagnostic is `TCG-STEPBY-METHOD`.

The optimized-session guard searches monomorphized local type graphs for
`StepBy` nested inside aggregates and closure state. Its depth and unique-type
budgets also bound legal recursively expanding generic types. If either budget
is exhausted, codegen fails closed with `TCG-STEPBY-TYPE-SCAN`; consequently,
an optimized program that does not use `StepBy` can be conservatively rejected
when its type graph exceeds those limits.

## Codegen option matrix

`codegen_crate` decides every codegen option it reads before it lowers
anything (`src/codegen_options.rs`, ledger L06-P7): a refusal stops the
compile after all verdicts are printed, a warning or note is printed and the
compile continues. Each verdict is a `[TCG-OPT-*]` code in the
diagnostic census. The pure table has a
host-independent test (`tests/codegen_option_matrix.rs`, which no gate runs
yet), and the required bridge-gate target `tests/debuginfo_dwarf_aarch64.rs`
prints every refusal code and every note or warning natively on
aarch64-apple-darwin (not every condition that leads to one: debuginfo off
aarch64-apple-darwin is checked only by the pure test).

| Option | Verdict |
| --- | --- |
| `-C lto` unspecified, `off`, or rustc's implicit local ThinLTO | honoured: no cross-unit optimization runs |
| `-Z thinlto=yes` (local ThinLTO) | note `[TCG-OPT-THINLTO-LOCAL]`: a no-op |
| `-C lto=fat` / `thin` | refused `[TCG-OPT-LTO]` |
| `-C linker-plugin-lto` | refused `[TCG-OPT-LINKER-PLUGIN-LTO]` |
| `-C embed-bitcode=yes`, spelled | warning `[TCG-OPT-EMBED-BITCODE]`: no bitcode exists |
| `-C profile-generate`, `-C profile-use`, sample profiles (`-Z profile-sample-use` or `-C profile-sample-use`, per compiler API) | refused `[TCG-OPT-PGO]` |
| `-C instrument-coverage` | refused `[TCG-OPT-COVERAGE]` |
| `-C debuginfo=line-tables-only` on aarch64-apple-darwin, proofs off | honoured: DWARF 4 line table plus one subprogram DIE per function |
| `-C debuginfo=line-directives-only` / `limited`, same conditions | note `[TCG-OPT-DEBUGINFO-LINES]`: the line-table image |
| `-C debuginfo=full`; any level with proof certificates on, or off aarch64-apple-darwin | refused `[TCG-OPT-DEBUGINFO]` |
| `-C dwarf-version` other than 4, with debuginfo | refused `[TCG-OPT-DWARF-VERSION]` |
| `-C split-debuginfo` (Darwin) | honoured by rustc's Mach-O handling: `packed` runs dsymutil, `unpacked` keeps the objects, `off` keeps no debug info |
| `-C llvm-args`, `-C passes`, `-C remark`, `-C no-prepopulate-passes`, `-C no-vectorize-loops`, `-C no-vectorize-slp`, `-Z llvm-time-trace` | warning `[TCG-OPT-LLVM-ONLY]` |
| `-Z sanitizer` | refused `[TCG-OPT-SANITIZER]` |
| `-Z stack-protector` other than `none` | refused `[TCG-OPT-STACK-PROTECTOR]` |
| `-Z branch-protection` | refused `[TCG-OPT-BRANCH-PROTECTION]` |
| `-Z instrument-mcount`, `-Z instrument-xray`, `-Z patchable-function-entry` | refused `[TCG-OPT-PROFILING-HOOK]` |
| `-Z min-function-alignment` up to 4 on AArch64 | honoured: every AArch64 function starts on a four-byte boundary |
| `-Z min-function-alignment` above that (above 1 off AArch64) | refused `[TCG-OPT-FUNCTION-ALIGNMENT]` |
| `-C code-model` other than `small` | refused `[TCG-OPT-CODE-MODEL]` |
| `-C jump-tables=no` | refused `[TCG-OPT-JUMP-TABLES]` |
| frame pointers `always` (`-C force-frame-pointers=yes`) | warning `[TCG-OPT-FRAME-POINTERS]`: frameless leaves keep none |
| `-C link-dead-code` on an executable-only crate | warning `[TCG-OPT-LINK-DEAD-CODE]`: lowering is demand-driven |
| `-C relocation-model` other than PIC/PIE on aarch64-apple-darwin | note `[TCG-OPT-RELOC-MODEL]`: served by PIC code |
| `-Z codegen-emit-retag` | refused `[TCG-EMIT-RETAG]` (earlier, same function) |

The Linux AArch64 option/output qualification exercises both measured APIs with actual loaded backends. Profile paths or an unavailable profiler runtime can cause earlier frontend errors; metadata/print success does not establish PGO support. The metadata session clears profiling controls only on its options copy. Caller self-profile outputs occur once; CG warns for LLVM time trace and emits no LLVM trace JSON.

Sample-profile spelling follows the actual compiler option field. The newer
`-C` field and its exact path are checked against modern compiler metadata;
full modern backend qualification remains open.

Consulted elsewhere in the bridge, not by this table: `-C opt-level`,
`-C target-cpu`, `-C target-feature`, `-C panic`, `-C overflow-checks`,
`-C debug-assertions` (UB checks), `-C codegen-units` (rustc's partitioning,
whose symbol plan the bridge carries), `-C relocation-model` on Linux
AArch64, and the backend knobs (`-Z trust-ir-cg-args`). Options rustc itself
applies before or after code generation, so a backend has nothing to honour,
are not inspected: `-C symbol-mangling-version`, `-C metadata`,
`-C extra-filename`, the linker options (`-C linker`, `-C link-arg(s)`,
`-C link-self-contained`, `-C prefer-dynamic`, `-C rpath`, `-C strip`,
`-C relro-level`), `-C incremental`, `-C save-temps` and
`-C collapse-macro-debuginfo` (rustc's span walk, which the line tables use).
Also not inspected, and so open rows of this table: `-C control-flow-guard`
(Windows-only), `-C force-unwind-tables` (every Darwin function gets unwind
information regardless), `-C no-redzone` (whether the AArch64 frame
lowering ever uses Darwin's 128-byte red zone has not been audited against
it), and the other `-Z` options; nor are the per-function attributes with a
table row's effect (`#[patchable_function_entry]`, a function alignment
attribute).

## Tests and evidence

Run focused load, execution, and rejection tests from this crate:

```bash
targo --unverified test --release --locked --test hello_loop
targo --unverified test --release --locked --test unsupported_program
```

On an x86-64 host with the pinned target standard library, the `StepBy`
boundary has a dedicated positive/negative regression:

```bash
targo --unverified test --release --locked \
  --test m99_iter_adapters_x86 \
  step_by_is_supported_only_at_default_o0 -- --exact
```

The complete bridge suite is:

```bash
targo --unverified test --release --locked
```

Many integration tests are target-aware and skip when their required host,
target standard library, emulator, or platform tools are unavailable. A skip
does not establish target coverage. Treat the named test, its recorded
preconditions, and the coverage inventory together as the evidence for a
feature.

Each integration test loads the backend library that Cargo built for its own
test build: the `deps/` sibling of the test executable, selected by
[`tests/support/backend_artifact.rs`](tests/support/backend_artifact.rs). A
library that another build, profile or feature set left in the target
directory is never used, and no test builds a backend itself. The three Linux
lane targets below, and the shared harness of the three Linux runtime twins
(`tests/support/linux_runtime_twin.rs`), also accept the runner's exact library
path and SHA-256.
The Darwin runner copies each test executable beside its backend snapshot.
[`scripts/tests/test_bridge_backend_selection.py`](../../scripts/tests/test_bridge_backend_selection.py)
is a regression lint for the known spellings of another route: a backend file
name, a Cargo profile or target directory, or a nested `cargo`/`targo` build.

On native Linux GNU AArch64, the bounded C homogeneous floating-point aggregate
ABI lane, the ELF thread-local lane, the Rust panic unwind/cleanup lane and the
static-data, drop/heap and coroutine runtime twins have a separate required
runner, invoked from the repository root:

```bash
python3 scripts/check_linux_aarch64_bridge.py --jobs 2
```

It performs a locked release build using the bridge's selected toolchain pin, then
runs the complete `aarch64_c_fnabi_aggregate_linux`, `tls_thread_local_linux`,
`unwind_cleanup_linux`, `panic_hook_differential`,
`executable_trap_stub_routes_aarch64`, `scalar_zst_field_differential`,
`static_data_linux`, `drop_heap_linux` and `coroutine_generator_linux`
targets with a retained, hash-checked copy of the exact built library
(`TCG_TEST_BACKEND_PATH`/`TCG_TEST_BACKEND_SHA256`). The panic-hook,
trap-stub and scalar-ZST targets are portable fixtures that select the backend
beside their own executable, so they run from fresh copies placed beside a
byte-identical snapshot. The pair is for the test process only: `trustc` refuses every
`TCG_*` variable, so every compiler the tests start (all begin from
`rustc_driver_command` in `tests/support/toolchain.rs`) drops it. Run
without that pair, as in a plain `scripts/trust_cargo.sh test`, these targets
load and hash the library Cargo built for their own test build. Cargo's
test build may replace its mutable release-cache library; that cache is
recorded separately from the tested copy. The ABI target requires real C/CG
and C/LLVM executions at O0–O3, including each named scalar-cell
alias/read/write family and separately counted unsupported-boundary controls.
The TLS target compiles the Darwin fixture's `#[thread_local]` crate for
`aarch64-unknown-linux-gnu` at O0–O3 with the `no-proof-certs` knob. It checks
with `readelf` that the static is one `STT_TLS` definition in an `SHF_TLS`
section, and that each accessor imports it and carries only complete
relocation sequences of exactly one access model: the general-dynamic TLS
descriptor, initial-exec or local-exec. The bridge takes the model from the
session's relocation model. This `staticlib` session gets the target-default
PIC model, so the accessors use the TLS descriptor
(`R_AARCH64_TLSDESC_{ADR_PAGE21,LD64_LO12,ADD_LO12,CALL}`), and at every
level the CG objects' TLS relocation kinds must equal the LLVM twin's. It
runs every CG and LLVM executable five times against a two-thread isolation
driver. The executable link may relax the descriptor access, so the
descriptor resolver itself is executed by the aggregate target's dlopened
PIC library (`linux_relocations`), not here. A plain-static control must be
detected as shared storage, and a `#[link_section]` thread-local must be
refused by name. The unwind target compiles the Darwin fixture's crate, with
user-`Drop` and nested-frame extensions, at O0–O3 with the `no-proof-certs`
knob. It checks each bridge function's LSDA, FDE and personality slot with
`readelf`, links the objects into an LLVM-compiled Rust driver that catches
every panic with `catch_unwind`, and requires exact payloads, drop order and
`Box` allocation/free counts from every CG executable (the LLVM twin may
remove the allocation of the two boxes that are never read). Zeroing the
landing pad of each protected call in a copy of its object must lose exactly
that frame's cleanups, and the `disable-unwind` knob must refuse each fixture
function by name. The three runtime twins keep the Darwin static-data,
drop/heap and coroutine fixtures' crates and drivers byte-identical, add
Linux crates (zero-initialized and relocated statics; logged `Box`/`Vec`
allocation, reallocation, free and drop order; the `ResumedAfterReturn`
panic edge; upvar, resume-argument and branchy coroutines) and controls (a
store to a read-only static, a misaligned exclusive pair, an out-of-bounds
index, named bridge refusals with LLVM twins), and require every CG and LLVM
executable at O0–O3 to print exactly the model and end exactly as modelled.
Each aborting panic stub names itself on stderr, so a modelled `SIGABRT` must
come from the expected panic entry, the same one for CG and LLVM. Every
bridge compile passes `no-proof-certs`, so they are native testing evidence
without certificates. Each target prints its
own structured marker; a failure in one target never skips another, and the
runner passes only when all pass.
It rejects skipped or empty suites, missing
family/compiler/optimization-level combinations, optimizer/policy overrides, and
records unchanged source and backend identities. Existing libraries cannot
substitute for a failed build. This is separate from the root workspace's
Linux regression floor; neither is full frontend qualification, and the TLS
target is testing evidence without proof certificates.

The root [README](../../README.md) explains trust-cg's evidence levels. Passing
bridge differential tests establishes regression evidence for the tested
programs; it is not an end-to-end formal proof of arbitrary Rust source,
rustc's MIR production, the Trust sysroot, linking, or every emitted byte.

## Reporting a bridge bug

Open a [trust-cg issue](https://github.com/alabsystems/trust-cg/issues) with
the repository revision, pinned `trustc` version, host and target triples,
optimization and MIR flags, the smallest reproducer, the expected result, and
the full `TCG` diagnostic. For suspected wrong code, include an independent
LLVM/`trustc` result and preserve any target-specific runtime preconditions.
