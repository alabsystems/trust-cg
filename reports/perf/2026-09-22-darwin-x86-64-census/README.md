# Darwin x86-64 `library/core` refusal census — 2026-09-22

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The first run of the `core` refusal census on an x86_64-apple-darwin host,
with the rustc-private bridge built ON this host from this checkout. Before
this, the bridge could not link here (the Darwin `trust` pack is cross-built
without `rustc_private`, by design) and the only census of record ran on a
Linux x86-64 host. Nothing here is a completion claim; the
completion plan records what
remains.

## Host and toolchains

| Item | Identity |
| --- | --- |
| Host | `x86_64-apple-darwin`, macOS 13.7.8, MacBookPro14,3 (4 cores, 16 GB) |
| trust-cg source | `de1f19099` (this checkout; bridge built from it) |
| Trust compiler | native stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21) (trustc 0.1.0)` at `trust/build/x86_64-apple-darwin/stage1/bin/trustc`, built from Trust `d7f143f3be` by `scripts/recreate_bootstrap.py` seeded from atpkg pack 6808 (stage0 mode: atpkg); `-Ztrust-verify=off` for every compile |
| `library/core` | Trust `d7f143f3be`'s own `library/core/src/lib.rs` (same tree as the compiler) |
| Bridge | `crates/rustc-codegen-trust-cg` → `target/release/librustc_codegen_trust_cg.dylib` (`backend.sha256`), compiled by pack 6808's `trustc` against the stage-1 build's `stage0-sysroot` (88 compiler rmetas + `librustc_driver-885d74563a8cf05f.dylib`, the driver `stage1/bin/trustc` links), unverified lane |
| Clean | as-found: pack `clean 0.2.0` (no `carcara-verify`, DEGRADED banner); second row: `clean 1.2.0` built from `~/clean` `a8345eaf` with `carcara-verify`, reached by repointing `store/clean/current` (development only, reversible) |
| AY | pack `ay 0.13.0+build.8256` |

## How the bridge was built here

The stage-2 Trust build never finished (its stage-2 `targo-trust` fails
compiling `trust-cg-verify`/`clean-elab` under the new stage-1 compiler),
but the stage-1 build had already assembled
`build/x86_64-apple-darwin/stage0-sysroot/lib/rustlib/x86_64-apple-darwin/lib/`
with every compiler crate's rmeta and the same `librustc_driver` the native
stage-1 `trustc` links. A wrapper at `stage0-sysroot/bin/trustc` (pack `trustc`
plus `--sysroot <stage0-sysroot>`, added only when the caller passes none —
the bridge's build-script probes pass their own, and `build.rs` derives
`<sysroot>/bin/trustc` from `--print sysroot`) then lets
`RUSTC=<wrapper> targo --unverified build --release --locked` produce a
dylib that `stage1/bin/trustc -Zcodegen-backend=<dylib>` loads.

Six relaunches of the stage build were needed, each a real skew fixed
locally and never pushed: the pack-6808 stage0 `targo` refusing a newer
`[trust] compiler_timeout_secs` knob in `first-party/ty`; the superproject's
`first-party/trust-cg` pin predating the x86-64 host gates (moved to
`de1f19099`, with `first-party/trust-ir` to the `7b9146ba` it pins); the
preflight refusing moved pins (`TRUST_SKIP_PREFLIGHT=1`); and verification
leaking into third-party build scripts (`RUSTFLAGS_BOOTSTRAP=-Ztrust-verify=off
TRUST_NO_VERIFY=1` in the launching environment).

## Census (`scripts/trust_ir_cg_census.py` from Trust `main`, `--diag-json`)

| Run | Emitted objects | Failed roots | Distinct reasons | Wall |
| --- | --- | --- | --- | --- |
| `core-x86_64-darwin-O0-asfound` (degraded pack checker) | 3,176 | 270 | 29 | 348 s |
| `core-x86_64-darwin-O0-checker` (carcara checker) | 3,176 | 270 | 29 | 269 s |
| `core-x86_64-darwin-O0-vacuity` (bridge rebuilt with the source-gated call-then-trap exemption) | 3,220 | 226 | 28 | 232 s |
| `core-x86_64-darwin-O0-tuple-pointee` (bridge rebuilt with the tuple arm of the byte-offset pointee lane) | 3,230 | 216 | 28 | 239 s |
| `core-x86_64-darwin-O0-pair-arg` (bridge rebuilt with the two-value `PassMode::Pair` ARGUMENT lane) | 3,298 | 148 | 28 | 240 s |
| `core-x86_64-darwin-O0-union-fat-leaf` (bridge rebuilt with the fat-leaf union layout and whole-element stores) | 3,319 | 127 | 27 | 236 s |
| `core-x86_64-darwin-O0-boundary-guard` (bridge rebuilt with the one-lane wide-pointer boundary guard — a deliberate RISE: 34 silently ABI-wrong signatures now refuse) | 3,285 | 161 | 27 | 234 s |
| `core-x86_64-darwin-O0-dyn-pointee` (bridge rebuilt with the `*const &dyn` pointee lane and the fat-element array pointee) | 3,298 | 148 | 27 | 239 s |
| `core-x86_64-darwin-O0-batch1-small-classes` (bridge rebuilt with the `Array(I128, 1)` return-gate arm, the self-call seed and `type_of` → unreachable) | 3,306 | 140 | 26 | 239 s |
| `core-x86_64-darwin-O0-batch2-small-classes` (bridge rebuilt with the uninhabited-residual `from_residual`, `AtomicPtr` load/store, `const_eval_select` projected slice args, whole `Use` from a memory-backed source) | 3,318 | 128 | 22 | 257 s |
| `core-x86_64-darwin-O0-batch3-i128-shift-union-simd-shell` (bridge rebuilt with the x86 selector's widened i128 shift count and the scalar-union whole read) | 3,337 | 109 | 21 | 239 s |
| `core-x86_64-darwin-O0-closure-slice-param` (bridge rebuilt with the closure slice-parameter fix; a non-regression row — the fix targets no census class) | 3,337 | 109 | 21 | 245 s |
| `core-x86_64-darwin-O0-nonnull-two-lane-slot` (bridge rebuilt with the transparent wide-slice newtype two-lane boundary slot) | 3,383 | 62 | 20 | 522 s |
| `core-x86_64-darwin-O0-pair-arg-lane` (rebased on origin/main; every x86-64 `PassMode::Pair` argument rides the two-value lane) | 3,384 | 62 | 20 | 267 s |

The checker no longer changes the count: the guard-carrier canaries the
degraded checker used to fail closed are now discharged by the portable
certificate tier, which the x86_64-apple-darwin qualification enabled.

The third row is the same compiler and `core` with the bridge rebuilt from
the commit that closes `[TCG-PROOF-465]`: with the bridge running here, the
44 remaining roots were reproduced in seconds and disassembled — under
`-Cpanic=abort` every `-> !` panic entry is emitted as `push rbp; mov rbp,
rsp; [jmp;] call _abort; ud2`, a zero-argument direct call plus the trap
(the `panic_fmt`/`panic_nounwind_fmt` bodies keep an entry block that only
jumps to the panic block). That body has no value semantics, but the row
shape alone cannot tell it from a call whose arguments were dropped, so
the exemption is admitted only against a LIR source that is exactly
`Jump* ; Call (no args, no results) ; Trap`; the refusal text now names
the verifier rows and the source shape so the next such class is
diagnosable from the census alone. 270 → 226; the class is gone.

The fourth row is the bridge rebuilt with a tuple arm in
`memory_aggregate_reference_pointee_lane_ty`: a `&(Range, i16)` /
`&(u16, [u16; 3])` pointee (the `unicode_data::conversions` table elements)
is typed from rustc's layout like a nested-field struct pointee. 226 → 216:
exactly the ten `[TCG-POINTEE-LANES]` tuple roots, zero new or moved roots.

The fifth row is the bridge rebuilt with the x86-64 port of the two-value
`PassMode::Pair` ARGUMENT lane (`scalar_pair_param_plan`, the AArch64-measured
62befd1db with the return side's carrier rule): 216 → 148; `[TCG-ARG-ABI]`
74 → 2. Freed roots that then stop at a later, pre-existing refusal
are listed in the commit; no new reason string appeared.

The sixth row admits a union whose active field holds a fat-pointer leaf
(`MaybeUninit<Part>`) and lowers whole-element stores of it through a slice
and into a local array: 148 → 127, the `ManuallyDrop<Part>` reason 21 → 0;
zero new or moved roots. (An unscoped first cut of the element-store arms
claimed the scalar union `MaybeUninit<u8>` and cost five roots; the re-census
after scoping is the archived row.)

The seventh row is the one-lane wide-pointer boundary guard: a by-value
`NonNull<[T]>` / `Unique<[T]>` parameter or return that the bridge declared as
one scalar while rustc passes `{data, len}` as a pair now refuses by name.
127 → 161: 34 new roots and 13 moved, every one a signature that was emitted
with one register where the ABI has two (`fn ident(p: NonNull<[u8]>) ->
NonNull<[u8]>` was `mov rcx, rdi; mov rax, rcx; ret`). Not a regression of
capability — the closing of a silent cross-backend miscompile channel.

The eighth row types a thin raw pointer whose pointee is a `&dyn Trait`
(`*const &dyn`, `NonNull<&dyn>` — the `slice::Iter<&dyn Debug>` cursor) as
the two-lane image `&&dyn` already had, and a `&[&dyn T; N]` array reference
from the rustc layout: 161 → 148, 13 `POINTEE-DYN-VALUE` roots gone, zero new
or moved.

The ninth row is the first batch of small classes, measured together:
`[TCG-RET-REGCLASS]` 6 → 0 (the gate's SysV leaf collector gained the I128
arm the selector already had), the self-recursive `gcd` root (the body
declared its own symbol as an extern), and `TypeId::info`'s `type_of`
(compile-time only in rustc; lowered as unreachable). 148 → 140, zero new or
moved.

The tenth row is the second batch, measured together: `from_residual` over
an UNINHABITED residual (`array::from_fn`'s `try_from_fn`, `ControlFlow::from_try`)
lowered as the unreachable rustc leaves there, `AtomicPtr<T>` load/store
(a pointer element is the same 8-byte MOV), `const_eval_select`'s runtime arm
receiving a slice argument projected out of the tupled-args place, and a whole
`Use` copy out of a struct whose address was taken (leaves loaded from its slot
at rustc's offsets). 140 → 128, 26 → 22 reasons, zero new or moved.

The eleventh row is the third batch: the x86 selector's i128 shift lowering
zero-extends a narrow (`u32`) shift count into a Gpr64 before its 64-bit
two-address ops — the seven `[TCG-POST-RA-DATAFLOW]` tied-operand refusals were
the validator correctly refusing the mixed-width tie — and a by-value scalar
union (`MaybeUninit<u8|u64>`) read whole resolves to its carrier-typed projected
field. 128 → 109, 19 roots gone, zero new or moved.

The twelfth row is a NON-REGRESSION row for a fix the census did not find:
a closure whose own parameter is a `&[T]` / `&str` slice was passed one
8-byte data pointer where its body declares the 16-byte `{ data, len }` slot
(a SIGSEGV at O0 in `bridge_corpus/closure_slice_arg.rs`, found by the corpus
sweep). The call now passes the address of the pair inside the memory-backed
tupled-args slot. 109 → 109, 0 roots gone, zero new or moved.

The thirteenth row is the capability half of the seventh row's guard: the
`repr(transparent)` newtype chain over a slice / `str` fat pointer
(`NonNull<[T]>`, `NonNull<str>`, `Unique<[T]>`) takes the same two-lane
`{ data, len }` boundary slot `&[T]` has, decided by one layout-checked helper
consulted in lockstep by both classifiers and both lowering seams; the in-body
data-only model is untouched. `[TCG-ARG-ABI]` 23 → 2, `[TCG-RET-ABI]`
26 → 0. 109 → 62, 47 roots gone, zero new or moved.

The fourteenth row is a NON-REGRESSION row for a cross-backend fix no census can
see: on x86-64 every Rust-ABI `PassMode::Pair` argument now rides rustc's two
independent argument values, so a 16-byte two-INTEGER pair with exactly one
integer register left takes R9 plus the stack as rustc does, instead of going
wholly to the stack. Every function with a slice / `str` / `(u64, u64)` /
`Range<usize>` / `Option<u64>` parameter changed its declared arity — measured
with zero arity mismatches, 62 → 62, zero new or moved.

## Against the Linux baseline (335 roots, trust-cg `9da5e237`)

| reason | Linux 2026-09-21 (`9da5e237`) | Darwin 2026-09-22 (this checkout) | delta |
|---|---:|---:|---:|
| `[TCG-ARG-ABI]` | 74 | 74 | +0 |
| `[TCG-PROOF-465]` | 46 | 44 | -2 |
| `[TCG-POINTEE-DYN-VALUE]` | 30 | 30 | +0 |
| `[TCG-REGALLOC-063]` | 46 | 8 | -38 |
| `[TCG-POINTEE-LANES]` | 21 | 21 | +0 |
| `union field mem::manually_drop::ManuallyDrop<num::imp::fmt::Part<'{era` | 19 | 19 | +0 |
| `[TCG-POINTEE-UNSIZED-TAIL]` | 16 | 16 | +0 |
| `[TCG-PASSVAL-067]` | 27 | 0 | -27 |
| `memory-backed slice assignment Rvalue::Cast` | 11 | 11 | +0 |
| `[TCG-RET-REGCLASS]` | 6 | 6 | +0 |
| `whole scalarized aggregate` | 5 | 5 | +0 |
| `Ty::[ascii::ascii_char::AsciiChar` | 4 | 4 | +0 |
| `ADT Use source field <n> before aggregate binding` | 4 | 4 | +0 |
| `[TCG-SSA-071]` | 4 | 4 | +0 |
| `memory leaf type is not a scalar` | 3 | 3 | +0 |
| `direct call slice fat-pointer arg <n> is not a whole-slice place or co` | 3 | 3 | +0 |
| `from_residual for an unmodeled Try type ops::try_trait::NeverShortCirc` | 2 | 2 | +0 |
| `atomic over non-I<n>..I<n>-scalar element *mut io::error::OsFunctions` | 2 | 2 | +0 |
| `unsupported intrinsic `_`` | 2 | 2 | +0 |
| `from_residual for an unmodeled Try type ops::control_flow::ControlFlow` | 2 | 2 | +0 |
| `Place deref memory load type is not scalarizable` | 1 | 1 | +0 |
| `borrowed aggregate reference used without deref` | 1 | 1 | +0 |
| `Place deref memory store from Rvalue::Ref` | 1 | 1 | +0 |
| `loop-carried local _<n>` | 1 | 1 | +0 |
| `memory aggregate whole assignment from non-local operand` | 1 | 1 | +0 |
| `Rvalue::Discriminant before enum aggregate binding` | 1 | 1 | +0 |
| `carrying_mul_add width <n> is not modeled` | 1 | 1 | +0 |
| `Place projection field <n> before aggregate binding` | 1 | 1 | +0 |
| `atomic over non-I<n>..I<n>-scalar element u<n>` | 0 | 1 | +1 |
| `atomic over non-I<n>..I<n>-scalar element i<n>` | 0 | 1 | +1 |
| **total** | 335 | 270 | -65 |

The three classes that moved are exactly the three closed in-repo since the
baseline: partial-eightbyte SysV aggregates (`REGALLOC-063` −38: the 37
`Array(I8|I16, n)` shapes plus one), the popcount certificate miss
(`PASSVAL-067` −27: host qualification), and the trap-only vacuity exemption
(`PROOF-465` −2). Every other class is raised in the bridge and is untouched;
each is now reproducible on this host in ~5 minutes.

## Boundary

A native x86-64 object emission census with certificates on; not a Linux
census (the emitted objects are Mach-O), not execution, not a verified
compiler, not a qualified toolchain (the stage-1 compiler and the repaired
checker are machine-local development installations). The bridge was
compiled by the pack's compiler against a sysroot the stage build assembled,
which is exactly how the stage-1 compiler itself was compiled.
