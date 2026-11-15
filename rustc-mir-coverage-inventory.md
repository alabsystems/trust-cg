# rustc MIR Coverage Inventory

This inventory mirrors the compiled rows in
`crates/rustc-codegen-trust-cg/src/lib.rs`. It is intentionally conservative:
`supported` means admitted by the current frontend, `partial` means admitted
only for the documented slice and otherwise fail-closed, and `fail-closed`
means the stable fallback diagnostic is expected to name the MIR family and
variant.

Rows are curated by hand. The refusals they name are exercised by the
bridge's own behavioural tests (for example `global_asm_refusal_x86.rs`,
`codegen_emit_retag_refusal.rs`, `tls_thread_local_linux.rs`,
`mir_families_aarch64.rs` and the `bridge_differential_*` corpora), not by a
text check of this file.

Readiness invariant: this inventory is not evidence that Trust-CG is full Rust frontend replacement-ready or full `trust-ir` replacement-ready. It is a stale-overclaim guard. Rows marked `supported` or `partial` describe only the current admitted slice, while replacement remains blocked on rustc layout/ABI coverage, non-function mono items, full MIR semantics, runtime/unwind semantics, complete `trust-ir` semantics, and AArch64/x86_64 backend parity.

## Replacement Blocker Anchors

These anchors must stay visible in this inventory and the full replacement
ledger until closed by implementation, positive tests, fail-closed negative
tests, and the documented release-validation lanes:

| Blocker | State | Required before replacement-ready |
| --- | --- | --- |
| Rust frontend parity | blocked | Complete rustc MIR, mono item, `FnAbi`, `TyAndLayout`, ABI attribute, place/memory/projection, statics/vtables, panic/unwind, and runtime semantics. |
| trust-ir semantic parity | blocked | Complete stable `trust-ir` type, constant, instruction, dialect, parser/binary, provenance, proof metadata, interpreter, global, and runtime/lifetime semantics. |
| AArch64 backend parity | blocked | Complete ABI, vector/SIMD, object relocation, TLS, atomics, unwind/EH, debug, proof, AOT, and JIT semantics to the shared replacement contract. |
| x86_64 backend parity | blocked | Complete ABI, aggregate classification, vector/SIMD, ELF/Mach-O/COFF relocation, TLS, atomics, unwind/EH, debug, proof, AOT, and JIT semantics to the shared replacement contract. |

## MonoItem

This frontend admits local `MonoItem::Fn` bodies and the bounded static-data
slice described below. Other mono-item shapes are not silently ignored: every
variant has an explicit admitted or fail-closed path when rustc schedules it
for a codegen unit.

| Variant | State | Diagnostic root | Notes |
| --- | --- | --- | --- |
| `Fn` | partial | `MIR body` | Local functions with admitted MIR and scalar ABI are compiled. Rustc-emitted shims/drop glue still fail through MIR, ABI, or terminator diagnostics. |
| `Static` | partial | `MonoItem::Static` / `compile_static_data_object` | Bounded default-section statics are emitted from rustc's evaluated allocation bytes and admitted pointer relocations. Mutable and address-taken local immutable readers import the definition's canonical symbol (never a per-reader copy); the supported TLS lane uses its canonical definition (the Darwin TLV descriptor, or the ELF `STT_TLS` symbol). A `#[link_section]` static carries its section to the AArch64 Mach-O and ELF object emitters, which place it or refuse the name with a section refusal code (`trust_cg_codegen::object_sections`; on Mach-O: `segment,section` in `__DATA`, `__DATA_CONST` or `__TEXT`, and a `__mod_init_func` constructor table; native positive in `mir_families_aarch64`); other targets refuse it as `[TCG-SECTION-TARGET]`, and a thread-local's custom section stays refused. Unsupported alignment/linkage/relocation shapes, vtable/type-id targets, and unsupported-target TLS still fail closed. A function's `#[link_section]` is refused as `[TCG-SECTION-TARGET]` (it used to be dropped silently). |
| `GlobalAsm` | fail-closed | `MonoItem::GlobalAsm` | Refused with `[TCG-GLOBAL-ASM]`: raw module-level assembly cannot be parsed/modeled/verified, so the driver pushes a failed root instead of silently dropping the item. Real support requires target object-section lowering and proof coverage. |

## RustcAbiLayout

This table tracks the compile-time ABI/layout substrate needed before the
frontend can claim replacement-grade Rust function boundaries. The current
frontend consumes rustc `FnAbi` / `PassMode::Cast` only for the bounded Linux
AArch64 C homogeneous floating-point aggregate (HFA) lane. That lane reads the
actual directional argument/return ABI, preserves consecutive F32/F64 carriers
and matching storage offsets, and rejects unrepresentable HFA plans. The rest
still derives signatures from rustc `fn_sig` (or the MIR locals for coroutine
resume bodies), classifies scalar carriers itself, and uses bounded
`TyAndLayout`-driven aggregate and fat-pointer lanes. This is not full Rust ABI
parity. Complete `FnAbi`, pass-mode, calling-
convention, and attribute integration remains a replacement blocker; shapes
outside the custom classifier's admitted envelope must fail closed rather than
receive a guessed ABI.

| Fact | State | Diagnostic root | Notes |
| --- | --- | --- | --- |
| `TargetPointerWidth` | partial | `RustcTargetLayout` | Rustc target pointer width is recorded and drives `usize`/`isize` lowering. |
| `DirectScalar` | partial | `rust_ty_to_trust_ir_ty` | The custom scalar classifier admits the documented Rust scalar slice; it does not consume rustc `PassMode::Direct`. `bool` and `i8`/`u8`/`i16`/`u16` extern-C boundaries use explicit ABI carriers with extension/truncation. `char`, `i128`, and `u128` are admitted at function boundaries — `rust_ty_to_trust_ir_ty` maps `char` to U32 and 128-bit ints to I128/U128, and i128/u128 args/returns use the tested SysV/AArch64 register-pair path. This is bounded differential evidence, not a complete ABI proof. |
| `ReferencePointer` | partial | `Ty::Ref` | Selected thin references lower to TrustIr references. On Linux AArch64, call-exposed destructor-bearing pointer owners use canonical frame homes when the scalar ABI, extent and alignment check admits them; the Rc/Box native identity regression requires eight matches at O0–O3. Unresolved referents retain `[TCG-REF-ARG-STORAGE]`. Provenance and fat-pointer metadata remain incomplete. |
| `FnAbiPassMode` | partial | `func_ty_for_instance` / `classify_func_ty` / `aapcs64_hfa` | Only the Linux AArch64 C HFA lane consumes actual rustc `FnAbi` and bounded `PassMode::Cast` decisions. General `Ignore`/`Direct`/`Pair`/`Cast`/`Indirect` translation is not implemented; full pass-mode integration remains a hard replacement blocker. |
| `TyAndLayoutShape` | partial | `memory_aggregate_layout` | Bounded aggregate lanes consume rustc `TyAndLayout` sizedness, size, alignment, backend representation, variants, and fields. Arbitrary layout shapes and complete ABI use remain unsupported. |
| `FieldOffsetsAndNiches` | partial | `memory_aggregate_layout` | The memory-aggregate lane consumes rustc field/tag offsets and models selected direct- and niche-tagged enums, padding, and alignment. Unsupported nested leaves, niches, packed/misaligned C-ABI shapes, and other layouts fail closed. |
| `AggregateAbiClassification` | partial | `classify_func_ty` / `fat_ptr_or_memory_aggregate_layout` | Selected struct, tuple, array, enum, union, closure, and fat-pointer boundaries use layout-derived carriers plus the backend's bounded SysV register-pair/stack/sret classifier. Linux AArch64 C HFAs use actual rustc cast carriers for one to four F32/F64 members, with explicit bit-preserving transfer to memory-slot lanes. This remains a bounded admitted slice, not rustc `FnAbi` parity; unsupported target or layout classes fail closed. |
| `IndirectAndSret` | partial | `fat_ptr_or_memory_aggregate_layout` | Selected by-value aggregate returns use the backend's bounded register-pair or sret path, and a hidden caller-location case is modeled. General rustc `Indirect`, byval, inalloca, and hidden-argument semantics are not consumed. |
| `ScalarPairAbi` | partial | `fat_ptr_memory_layout` | Boundary-crossing slice/str fat pointers use a bounded two-lane data/metadata carrier, with selected related aggregate paths. General rustc `ScalarPair` semantics, arbitrary DST metadata, and complete trait-object/option-like ABI coverage remain unsupported. |
| `CallConvAndAttributes` | partial | `classify_func_ty` | The classifier distinguishes rustic from C-compatible ABI families and implements selected narrow-scalar carriers and hidden caller-location handling. It does not consume rustc's complete calling-convention, extension, noalias, noundef, unwind, or target ABI attributes. |
| `VariadicAbi` | partial | `[TCG-VARARG-ABI]` / `TerminatorKind::Call argument count` | Direct scalar C varargs lower on Linux AArch64 only (`variadic.rs`): the declaration is marked `is_vararg` and each anonymous argument is checked against rustc's call-site `FnAbi`, which must place it as one direct scalar of 4 or 8 bytes, a thin pointer or a thin reference with a stable referent; anything else, and a non-C variadic declaration, refuses with `[TCG-VARARG-ABI]`. On every other target a declaration keeps `is_vararg: false`, and a call that passes an anonymous argument is refused by the generic call-argument count check (no anonymous argument is placed as a fixed one); a named `[TCG-VARARG-ABI]` refusal there is still to do. Indirect calls keep their existing admission rules. The aggregate/carrier/hidden-return-buffer scope (`check_aggregate_abi_scope`) and the Linux AArch64 HFA float-`Cast` precondition also refuse variadic `FnAbi`s. This row does not establish how a variadic definition (`...` parameters) is handled. |
| `UnsizedAndFatPointerAbi` | partial | `fat_ptr_or_memory_aggregate_layout` | Boundary-crossing slice and str pointers have a bounded data/length lane, and selected trait-object paths exist. General DST, trait-object, and metadata ABI lowering remains incomplete. |

## StatementKind

| Variant | State | Diagnostic root | Notes |
| --- | --- | --- | --- |
| `Assign` | partial | `Rvalue::*` | Depends on destination place and assigned `Rvalue` support. |
| `FakeRead` | supported | | Debug-analysis no-op. |
| `SetDiscriminant` | partial | `StatementKind::SetDiscriminant` | Every layout `codegen_set_discr` handles: a Direct tag (the discriminant at the tag width, explicit negative, wide and above-127 `repr` values included), a fieldless enum whose whole value is the tag, a niche (written for a niche variant, nothing for the untagged one), a single-variant layout (no tag: a no-op). Admitted places: `(*r)` and `(*r).f…` through a bound thin pointer, a memory-backed local and its `Field`/`Downcast`/`Index` projections (`set_discriminant`). A scalarized local (a bare fieldless enum local included), a slot-backed DST base or an unbound pointer is refused by name. Native positive (custom MIR, 18 slots and 19 writes covering every layout and place class, O0–O3 against LLVM) in `mir_families_aarch64`, without proof certificates. |
| `StorageLive` | supported | | Clears stale local bindings. |
| `StorageDead` | supported | | Clears stale local bindings. |
| `Retag` | fail-closed | `[TCG-EMIT-RETAG]` | Not a `StatementKind` on the pinned Trust rustc: a retag rides on `Rvalue::Use(_, WithRetag)`, lowered as the plain copy/move rustc_codegen_ssa emits without retag emission. `-Zcodegen-emit-retag` (retag calls) is refused for the whole compile before lowering; Rust provenance/alias retag semantics are not modeled. |
| `PlaceMention` | supported | | Debug no-op. |
| `AscribeUserType` | supported | | Type-checking no-op after MIR validation. |
| `Coverage` | fail-closed | `StatementKind::Coverage` | Coverage/profiling instrumentation is not emitted. |
| `Intrinsic` | partial | `StatementKind::Intrinsic` | Bounded slice: `Assume` is a sound no-op; `CopyNonOverlapping` lowers via `lower_copy_nonoverlapping` and fails closed on unmodeled shapes. The inner match is exhaustive, so any future non-diverging intrinsic is a compile error, never a silent no-op. |
| `ConstEvalCounter` | supported | | Const-eval bookkeeping no-op. |
| `BackwardIncompatibleDropHint` | supported | | Lint/drop hint no-op. |
| `Nop` | supported | | Explicit no-op. |

## Rvalue

| Variant | State | Diagnostic root | Notes |
| --- | --- | --- | --- |
| `Use` | partial | `Operand::*` | Scalar operands, selected references, and scalarized aggregate moves are admitted. The `WithRetag` flag lowers as a plain use; see `Retag`. |
| `Repeat` | partial | `Rvalue::Repeat` | Selected scalar/aggregate array repeats with target-usize counts are admitted. |
| `Ref` | partial | `Rvalue::Ref` | Scalar references are admitted; broad aggregate/projection cases fail closed. Exact zero-offset, full-cell primitive field reads and statement writes use the original scalar-cell allocation after checked Rust/storage layout agreement; the chain may pass zero-sized sibling fields and an over-aligned record's padded home, and C borrows of a scalarized HFA formal's whole value and scalar leaf use the same cell (native positives in `aarch64_c_fnabi_aggregate_linux`, without proof certificates). Genuine projected call results still reject unsupported SSA fallback with `[TCG-SCALAR-CELL-PROJECTION]`; `[TCG-SCALAR-CELL-LAYOUT]` rejects projections that do not select the cell's own scalar extent (required controls: a packed record, a borrow of an HFA formal's middle aggregate). The address-taken HFA-formal SSA guard `[TCG-AAPCS64-HFA-ALIASED-SCALAR]` remains, but no Linux bridge test shape reaches it now. Existing memory-aware and single-field raw-address paths are distinct; this is not general alias/projection completeness. |
| `ThreadLocalRef` | partial | `Rvalue::ThreadLocalRef` | Admits the bounded TLS-static lane: canonical descriptor references and Darwin TLV object emission, and on Linux AArch64 ELF one `.tdata`/`.tbss` `STT_TLS` definition with accessor imports in the session relocation model's access model: the target-default `pic` gives TLS-descriptor (`TLSDESC`) accesses, the relocation kinds LLVM emits for the same session (native fixture `tls_thread_local_linux` on executables; `linux_relocations` runs the accessor from a `dlopen`ed `pic` shared object through the dynamic loader's TLS-descriptor resolver), without proof certificates. Unsupported targets and TLS shapes fail closed. |
| `RawPtr` | partial | `Rvalue::RawPtr` | Admits guarded address-of/raw-pointer cases whose place and provenance shapes are represented; unmatched projection, metadata, or provenance shapes fail closed. |
| `Cast` | partial | `CastKind::*` | Selected scalar casts and pointer unsize are admitted. |
| `BinaryOp` | partial | `BinOp::*` | Selected scalar arithmetic/comparison and checked ops are admitted. |
| `UnaryOp` | partial | `UnOp::*` | Selected scalar unary ops and pointer metadata slices are admitted. |
| `Discriminant` | partial | `Rvalue::Discriminant` | `lower_discriminant` reads a single-variant layout's static value, a tracked enum binding, a memory-backed enum local and its projected sub-enums, a tag-only enum's scalar, an enum through a bound thin pointer (`(*r)`, `(*r).f…` at static offsets) and, since L06-P8, an enum through a pointer at a runtime index (`(*r)[i]…`, `set_discriminant::lower_indexed_read`), decoding Direct and niche tags with the shared tag codec. Any other projected source is refused (`Rvalue::Discriminant projected source`). Native positive (custom MIR, 43 reads: explicit negative, wide and above-127 `repr` tags, a fieldless enum, niches in `bool`, `char`, a reference, `NonZeroU64`, an explicit tag and a nested `Option<Option<bool>>`, through a reference, a field, a variant field, a by-value argument and a runtime index, O0–O3 against LLVM) in `mir_families_aarch64`, without proof certificates. |
| `Aggregate` | partial | `AggregateKind::*` | Selected tuple/array/ADT forms are admitted. Closure environments are admitted as scalarized upvars (`lower_closure_aggregate`) or into memory-backed slots (`lower_memory_aggregate_construct` with `closure_memory_layout`). A coroutine frame is constructed only into a memory-backed slot whose `coroutine_memory_layout` validates each state's live-field leaves; the scalar path still refuses `AggregateKind::Coroutine`. Thin `RawPtr` builds (`lower_thin_raw_ptr_aggregate`) and memory-backed slice builds from `(data, len)` (`lower_memory_slice_assign`) are admitted. `CoroutineClosure`, other raw-pointer shapes, and unmodeled layouts fail closed naming the `AggregateKind` or the memory-aggregate refusal. |
| `CopyForDeref` | fail-closed | `[TCG-MIR-NOT-RUNTIME]` | Not a runtime-MIR construct on the pinned compiler: the required `EraseDerefTemps` pass rewrites every one into a plain copy and the MIR validator rejects it in runtime MIR (`rustc_codegen_ssa` treats it as a compiler bug). One reaching the backend is refused. |
| `WrapUnsafeBinder` | fail-closed | `[TCG-UNSAFE-BINDER]` | Unsafe-binder types (the incomplete `unsafe_binders` feature) have no trust-ir mapping (refusal pinned in `mir_families_aarch64`). |

## TerminatorKind

| Variant | State | Diagnostic root | Notes |
| --- | --- | --- | --- |
| `Goto` | supported | | Direct branch. |
| `SwitchInt` | supported | | Integer switch with explicit default. |
| `UnwindResume` | partial | `TerminatorKind::UnwindResume` | The admitted EH lane resumes through the maintained exception slot; shapes outside that modeled lane fail earlier in EH lowering. Native fixtures: `unwind_cleanup_aarch64` (Darwin) and `unwind_cleanup_linux` (Linux AArch64 ELF, O0–O3, `Box` and user-`Drop` cleanups across two bridge frames, without proof certificates). `catch_unwind` inside a bridge frame fails closed. |
| `UnwindTerminate` | partial | `TerminatorKind::UnwindTerminate` | The admitted termination lane lowers to unreachable after the modeled unwind boundary; broader EH semantics remain incomplete. |
| `Return` | partial | `branch-varying scalar reference escapes through return` | Scalar/unit returns are admitted. |
| `Unreachable` | partial | `TerminatorKind::Unreachable` | Unit/never and scalar-return unreachable edges are admitted. |
| `Drop` | partial | `TerminatorKind::Drop` | `lower_drop_terminator` admits bounded drop-glue/destructor shapes and rejects unsupported layout, ABI, or control-flow cases. A `Box<T>` whose payload has drop glue calls rustc's own `drop_glue::<T>` on the box pointer and then frees it, with the box's nested cleanup on unwind, when every part of `T` is kept at rustc's layout (`[TCG-BOX-PAYLOAD-DROP]`, AArch64 Darwin only; recursive lists and trees included, both those linked through `Option<Box<Node>>` and enum cons lists and trees whose glue calls itself on each `Box<Self>`), and a box reached through a projection (`drop(((*_1) as Some).0)`) is freed through its loaded pointer. On AArch64 Darwin only, the loop-carried scalars of a cleanup loop that an unwind edge enters (`drop_in_place::<[T]>`'s nested cleanup, a guard live across an unwinding loop) get frame homes (`cleanup_loop_homes`; a pad that needs no SSA input gets none), and an indirect call or `dyn` drop slot with a live cleanup edge goes through the typed forwarding thunk (`indirect_unwind`) as on Linux AArch64. Native positive with real panics caught in an LLVM harness and every allocation counted, O0–O3, in `mir_families_aarch64`, without proof certificates. `Vec<Box<T>>` with a droppable `T` stays refused. |
| `Call` | partial | `TerminatorKind::Call` | Direct calls with supported scalar ABI are admitted only when the callee is a registered function or explicit bodyless external declaration and trust-ir argument/result signatures validate. |
| `TailCall` | fail-closed | `[TCG-TAIL-CALL]` | `become` guarantees the caller's frame is released before the callee runs; trust-ir has no tail-call instruction and the backend's tail-call pass is an optimization, so no lowering here can keep that guarantee (refusal pinned in `mir_families_aarch64`). |
| `Assert` | partial | `AssertKind::*` | Selected overflow/division/bounds assertions are admitted. |
| `Yield` | fail-closed | `[TCG-MIR-NOT-RUNTIME]` | Not a runtime-MIR construct: the coroutine transform replaces it (the post-transform resume body is lowered through `SetDiscriminant` and `Discriminant` on the frame). `rustc_codegen_ssa` treats one in codegen as a compiler bug. |
| `CoroutineDrop` | fail-closed | `[TCG-MIR-NOT-RUNTIME]` | Not a runtime-MIR construct: the coroutine transform replaces it with the drop shim's body. |
| `FalseEdge` | fail-closed | `[TCG-MIR-NOT-RUNTIME]` | Borrow-checker structure removed before runtime MIR. |
| `FalseUnwind` | fail-closed | `[TCG-MIR-NOT-RUNTIME]` | Borrow-checker structure removed before runtime MIR. |
| `InlineAsm` | partial | `[TCG-INLINE-ASM]` | Only the bounded scalar floating-point grammar of `aarch64_fp_asm` (one exact `fmadd`/`fsqrt`/`frintn` with `s`/`d` vreg operands, `pure, nomem, nostack`) lowers, on AArch64 Linux and Darwin, to a dialect operation the backend selects, encodes and ENC-5 decode-checks (Darwin native positive against a hardware-checked C driver, O0–O3, in `mir_families_aarch64`, without proof certificates). Every other `asm!` block and every naked function is refused: trust-ir carries no assembly (refusal pinned in `mir_families_aarch64`). |

## Intercepted `core`/`std` method & intrinsic call targets

Many `core`/`std` primitive-integer methods reach this frontend **as a call**:
at `-O0` they are a `TerminatorKind::Call` to `core::num::<impl T>::method`, and
at `-O3` rustc inlines them to the bare LLVM-style intrinsic. Rather than fail
closed on these call targets, the frontend **intercepts a fixed, audited set**
and lowers each to a supported `trust-ir` primitive. The resulting operation is
eligible for the same evidence machinery as a source-level operator; that does
not by itself prove the surrounding compilation end to end. `wrapping_*` maps
to the corresponding two's-complement modular operation; see the table below.

Intercepted and lowered for the current ≤64-bit scalar-integer slice (the live
match arms are in `crates/rustc-codegen-trust-cg/src/lib.rs`):

| Method / intrinsic | Lowers to | Intercept site |
| --- | --- | --- |
| `wrapping_add` / `wrapping_sub` / `wrapping_mul` | `Add` / `Sub` / `Mul` (modular) | `wrapping_binop_method` / `lower_wrapping_method_call` |
| `wrapping_div` / `wrapping_rem`, constant nonzero non-`-1` divisor only | `SDiv`/`UDiv` / `SRem`/`URem` | `wrapping_binop_method` |
| `saturating_add` / `saturating_sub` | `Overflow` + clamp `Select` | `saturating_*` intercept |
| `overflowing_{add,sub,mul,div,rem,shl,shr}` | checked op + flag | overflowing intercept |
| `rotate_left` / `rotate_right` | `Shl`/`LShr`/`Or` compose | bit-manip intercept |
| `count_ones` / `count_zeros` | `CtPop` composition | `bitmanip_method` |
| `leading_zeros` / `leading_ones` / `trailing_zeros` / `trailing_ones` | masked `CtPop` compose | `bitmanip_method` |
| `swap_bytes` / `reverse_bits` | shift/mask compose | `bitmanip_method` |
| `is_power_of_two` | `CtPop == 1` | `bitmanip_method` |
| `funnel_shl` / `funnel_shr` / `disjoint_bitor` intrinsics | `Shl`/`LShr`/`Or` / `Or` | `lower_funnel_shift_intrinsic` / `lower_disjoint_bitor_intrinsic` |

Still **fail-closed** (named, safe — the diagnostic cites the method, never a
wrong value): `signum` (needs a signed branchless compare outside the unsigned
bit-manip carrier), `isqrt` (staged lookup-table array aggregate), `ilog2` /
`ilog10` (`Option<NonZero<_>>` enum modeling), `i128`/`u128` `wrapping_*` inside
`-O0` loops (deliberate), and any user/`core` call target whose body this
frontend has not admitted.

**Invariant.** An unsupported call target **fails closed with a diagnostic that
names the MIR family/variant** — it is never silently compiled to an "unknown"
or guessed value. Fail-closed ≠ miscompile.
