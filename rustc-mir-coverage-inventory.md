# rustc MIR Coverage Inventory

This inventory mirrors the compiled rows in
`crates/rustc-codegen-trust-cg/src/lib.rs`. It is intentionally conservative:
`supported` means admitted by the current frontend, `partial` means admitted
only for the documented slice and otherwise fail-closed, and `fail-closed`
means the stable fallback diagnostic is expected to name the MIR family and
variant.

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
| `Static` | partial | `MonoItem::Static` / `compile_static_data_object` | Bounded default-section statics are emitted from rustc's evaluated allocation bytes and admitted pointer relocations. Mutable and address-taken local immutable readers import the definition's canonical symbol (never a per-reader copy); the supported TLS lane uses its canonical descriptor. Custom sections, unsupported alignment/linkage/relocation shapes, vtable/type-id targets, and unsupported-target TLS still fail closed. |
| `GlobalAsm` | fail-closed | `MonoItem::GlobalAsm` | Refused with `[TCG-GLOBAL-ASM]`: raw module-level assembly cannot be parsed/modeled/verified, so the driver pushes a failed root instead of silently dropping the item. Real support requires target object-section lowering and proof coverage. |

## RustcAbiLayout

This table tracks the compile-time ABI/layout substrate needed before the
frontend can claim replacement-grade Rust function boundaries. The current
frontend does **not** consume rustc `FnAbi` or `PassMode`. It derives signatures
from rustc `fn_sig` (or the MIR locals for coroutine resume bodies), classifies
scalar carriers itself, and uses bounded `TyAndLayout`-driven aggregate and fat-
pointer lanes. Those implemented lanes are useful but do not substitute for
rustc's target-specific ABI decisions. Complete `FnAbi`, pass-mode, calling-
convention, and attribute integration remains a replacement blocker; shapes
outside the custom classifier's admitted envelope must fail closed rather than
receive a guessed ABI.

| Fact | State | Diagnostic root | Notes |
| --- | --- | --- | --- |
| `TargetPointerWidth` | partial | `RustcTargetLayout` | Rustc target pointer width is recorded and drives `usize`/`isize` lowering. |
| `DirectScalar` | broad | `rust_ty_to_trust_ir_ty` | The custom scalar classifier admits the documented Rust scalar slice; it does not consume rustc `PassMode::Direct`. `bool` and `i8`/`u8`/`i16`/`u16` extern-C boundaries use explicit ABI carriers with extension/truncation. `char`, `i128`, and `u128` are admitted at function boundaries — `rust_ty_to_trust_ir_ty` maps `char` to U32 and 128-bit ints to I128/U128, and i128/u128 args/returns use the tested SysV/AArch64 register-pair path. This is bounded differential evidence, not a complete ABI proof. |
| `ReferencePointer` | partial | `Ty::Ref` | Selected thin references lower to TrustIr references; provenance and fat-pointer metadata remain incomplete. |
| `FnAbiPassMode` | fail-closed | `func_ty_for_instance` / `classify_func_ty` | rustc `FnAbi` and its `Ignore`/`Direct`/`Pair`/`Cast`/`Indirect` pass modes are not consumed. The current custom signature classifier admits bounded cases and rejects unsupported type/layout shapes; full pass-mode integration remains a hard replacement blocker. |
| `TyAndLayoutShape` | partial | `memory_aggregate_layout` | Bounded aggregate lanes consume rustc `TyAndLayout` sizedness, size, alignment, backend representation, variants, and fields. Arbitrary layout shapes and complete ABI use remain unsupported. |
| `FieldOffsetsAndNiches` | partial | `memory_aggregate_layout` | The memory-aggregate lane consumes rustc field/tag offsets and models selected direct- and niche-tagged enums, padding, and alignment. Unsupported nested leaves, niches, packed/misaligned C-ABI shapes, and other layouts fail closed. |
| `AggregateAbiClassification` | partial | `classify_func_ty` / `fat_ptr_or_memory_aggregate_layout` | Selected struct, tuple, array, enum, union, closure, and fat-pointer boundaries use layout-derived carriers plus the backend's bounded SysV register-pair/stack/sret classifier. This is a custom admitted slice, not rustc `FnAbi` parity; unsupported target or layout classes fail closed. |
| `IndirectAndSret` | partial | `fat_ptr_or_memory_aggregate_layout` | Selected by-value aggregate returns use the backend's bounded register-pair or sret path, and a hidden caller-location case is modeled. General rustc `Indirect`, byval, inalloca, and hidden-argument semantics are not consumed. |
| `ScalarPairAbi` | partial | `fat_ptr_memory_layout` | Boundary-crossing slice/str fat pointers use a bounded two-lane data/metadata carrier, with selected related aggregate paths. General rustc `ScalarPair` semantics, arbitrary DST metadata, and complete trait-object/option-like ABI coverage remain unsupported. |
| `CallConvAndAttributes` | partial | `classify_func_ty` | The classifier distinguishes rustic from C-compatible ABI families and implements selected narrow-scalar carriers and hidden caller-location handling. It does not consume rustc's complete calling-convention, extension, noalias, noundef, unwind, or target ABI attributes. |
| `VariadicAbi` | fail-closed | `RustcAbiLayout::VariadicAbi` | Variadic ABI lowering is not implemented. |
| `UnsizedAndFatPointerAbi` | partial | `fat_ptr_or_memory_aggregate_layout` | Boundary-crossing slice and str pointers have a bounded data/length lane, and selected trait-object paths exist. General DST, trait-object, and metadata ABI lowering remains incomplete. |

## StatementKind

| Variant | State | Diagnostic root | Notes |
| --- | --- | --- | --- |
| `Assign` | partial | `Rvalue::*` | Depends on destination place and assigned `Rvalue` support. |
| `FakeRead` | supported | | Debug-analysis no-op. |
| `SetDiscriminant` | partial | `StatementKind::SetDiscriminant` | Only tracked zero-payload enum locals are admitted. |
| `StorageLive` | supported | | Clears stale local bindings. |
| `StorageDead` | supported | | Clears stale local bindings. |
| `Retag` | fail-closed | `StatementKind::Retag` | Rust provenance/alias retag semantics are not modeled by scalar side tables. |
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
| `Use` | partial | `Operand::*` | Scalar operands, selected references, and scalarized aggregate moves are admitted. |
| `Repeat` | partial | `Rvalue::Repeat` | Selected scalar/aggregate array repeats with target-usize counts are admitted. |
| `Ref` | partial | `Rvalue::Ref` | Scalar references are admitted; broad aggregate/projection cases fail closed. |
| `ThreadLocalRef` | partial | `Rvalue::ThreadLocalRef` | Admits the bounded TLS-static lane, including canonical descriptor references and Darwin TLV object emission; unsupported targets and TLS shapes fail closed. |
| `RawPtr` | partial | `Rvalue::RawPtr` | Admits guarded address-of/raw-pointer cases whose place and provenance shapes are represented; unmatched projection, metadata, or provenance shapes fail closed. |
| `Cast` | partial | `CastKind::*` | Selected scalar casts and pointer unsize are admitted. |
| `BinaryOp` | partial | `BinOp::*` | Selected scalar arithmetic/comparison and checked ops are admitted. |
| `UnaryOp` | partial | `UnOp::*` | Selected scalar unary ops and pointer metadata slices are admitted. |
| `Discriminant` | partial | `Rvalue::Discriminant` | Only tracked enum aggregate bindings are admitted. |
| `Aggregate` | partial | `AggregateKind::*` | Selected tuple/array/ADT forms are admitted; closure/coroutine/raw-ptr aggregates fail closed. |
| `CopyForDeref` | fail-closed | `Rvalue::CopyForDeref` | Deref-copy lowering has not been admitted. |
| `WrapUnsafeBinder` | fail-closed | `Rvalue::WrapUnsafeBinder` | Unsafe-binder semantics are not represented. |

## TerminatorKind

| Variant | State | Diagnostic root | Notes |
| --- | --- | --- | --- |
| `Goto` | supported | | Direct branch. |
| `SwitchInt` | supported | | Integer switch with explicit default. |
| `UnwindResume` | partial | `TerminatorKind::UnwindResume` | The admitted EH lane resumes through the maintained exception slot; shapes outside that modeled lane fail earlier in EH lowering. |
| `UnwindTerminate` | partial | `TerminatorKind::UnwindTerminate` | The admitted termination lane lowers to unreachable after the modeled unwind boundary; broader EH semantics remain incomplete. |
| `Return` | partial | `branch-varying scalar reference escapes through return` | Scalar/unit returns are admitted. |
| `Unreachable` | partial | `TerminatorKind::Unreachable` | Unit/never and scalar-return unreachable edges are admitted. |
| `Drop` | partial | `TerminatorKind::Drop` | `lower_drop_terminator` admits bounded drop-glue/destructor shapes and rejects unsupported layout, ABI, or control-flow cases. |
| `Call` | partial | `TerminatorKind::Call` | Direct calls with supported scalar ABI are admitted only when the callee is a registered function or explicit bodyless external declaration and trust-ir argument/result signatures validate. |
| `TailCall` | fail-closed | `TerminatorKind::TailCall` | Tail-call ABI/control-flow semantics are missing. |
| `Assert` | partial | `AssertKind::*` | Selected overflow/division/bounds assertions are admitted. |
| `Yield` | fail-closed | `TerminatorKind::Yield` | Coroutine yield/state-machine lowering is missing. |
| `CoroutineDrop` | fail-closed | `TerminatorKind::CoroutineDrop` | Coroutine drop lowering is missing. |
| `FalseEdge` | fail-closed | `TerminatorKind::FalseEdge` | Borrow-checker false-edge structure is not represented. |
| `FalseUnwind` | fail-closed | `TerminatorKind::FalseUnwind` | False unwind edges require EH modeling. |
| `InlineAsm` | fail-closed | `TerminatorKind::InlineAsm` | Inline assembly lowering is missing. |

## Intercepted `core`/`std` method & intrinsic call targets

Many `core`/`std` primitive-integer methods reach this frontend **as a call**:
at `-O0` they are a `TerminatorKind::Call` to `core::num::<impl T>::method`, and
at `-O3` rustc inlines them to the bare LLVM-style intrinsic. Rather than fail
closed on these call targets, the frontend **intercepts a fixed, audited set**
and lowers each to a supported `trust-ir` primitive. The resulting operation is
eligible for the same evidence machinery as a source-level operator; that does
not by itself prove the surrounding compilation end to end. `wrapping_*` maps
to the corresponding two's-complement modular `Add`/`Sub`/`Mul` operation.

Intercepted and lowered for the current ≤64-bit scalar-integer slice (the live
match arms are in `crates/rustc-codegen-trust-cg/src/lib.rs`):

| Method / intrinsic | Lowers to | Intercept site |
| --- | --- | --- |
| `wrapping_add` / `wrapping_sub` / `wrapping_mul` | `Add` / `Sub` / `Mul` (modular) | `wrapping_binop_method` / `lower_wrapping_method_call` |
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
