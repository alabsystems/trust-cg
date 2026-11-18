# trust-cg architecture

trust-cg is a multi-target compiler backend with explicit evidence boundaries.
The root workspace builds with the branded Trust package selected by
`rust-toolchain.toml`; `targo --unverified` makes no proof claim about that build.
The optional rustc bridge and cargo-fuzz harness have independent manifests;
root workspace checks do not build or execute those workspaces.

## Source audit and capability boundaries

The September 29–October 1 source audit examined the implementation, its admission
checks and independent tests. The 0.x release tier is a qualification policy;
implementation, native regression evidence, Rust/sysroot completeness and
proof authority are separate dimensions. This inventory describes code paths,
not a fresh full-platform qualification result.

The October 14 completeness audit
checks the reconciled local/upstream source and its remaining acceptance gaps.
Its dated validation does not transfer earlier host or proof results to a new
compiler revision.

| Surface | Implemented source | Boundary to retain |
| --- | --- | --- |
| Native AArch64 | [Pipeline](crates/trust-cg-codegen/src/pipeline.rs): instruction selection, O1–O3 optimization, allocation/spills, frames, branch resolution, encoding and multi-function ELF/Mach-O; globals, linkage, TLS, relocations, DWARF/CFI and selected EH. | Explicit AAPCS64/Darwin target authority; supported ABI and ISA shapes differ. Certified EH remains refused. |
| Native x86-64 | [Independent pipeline](crates/trust-cg-codegen/src/x86_64/pipeline.rs): selection, optimization, allocation, two-address repair, frames, encoding and ELF/Mach-O/COFF. | System V/Win64 support differs; COFF EH has no LSDA path. Native implementation exceeds the certified domain. |
| RISC-V 64 | [Pipeline](crates/trust-cg-codegen/src/riscv/pipeline.rs) and [selector](crates/trust-cg-codegen/src/riscv/isel.rs): integer/pointer AOT, linear-scan allocation with spilling, frames, branch relaxation, multi-function ELF and call relocations. | At most eight GPR parameters and one integer/pointer result. No indirect/variadic calls, FP/vector, Switch or non-entry block parameters; no certified output or JIT. |
| WebAssembly | [Lowering](crates/trust-cg-codegen/src/wasm/lower.rs): structured CFGs, linear memory, globals, direct/indirect calls, function tables, relocatable objects and host-island imports with negotiated stack ownership. | CLI emits closed modules or relocatable objects for `wasm-ld`. Library import support is broader; neither route is a general WASI frontend or complete semantic proof. |
| JIT | [Runtime](crates/trust-cg-codegen/src/jit.rs): host ABI, fixups, code/data mappings, RW-to-RX seal, cache flush/hash readback, the installed-artifact replay of verifying AArch64 publications ([installed_replay.rs](crates/trust-cg-codegen/src/jit/installed_replay.rs): certified words, independently decoded branch targets, veneers), unwind registration, execution leases and reclamation. | Exact host target and static relocation model required. Publication integrity alone supplies no semantic certificate. |
| Optimization | [Pass scheduler](crates/trust-cg-opt/src/pipeline.rs): constant/CFG simplification, CSE/GVN, loops, vectorization, scheduling, PGO and proof-derived transforms; shared pre-ISel LIR inlining. | Per-pass checks and bounded certificates do not prove every pass composition. Per-run translation validation covers the schedulers, mem-pair formation, if-conversion and LICM only, under its own machine model. Inline-only templates retain their documented same-body/authentication premises. |
| LLVM input | [Parser](crates/trust-cg-llvm-import/src/parser.rs) and [vector planner](crates/trust-cg-llvm-import/src/native_vector.rs): substantial textual scalar/FP, CFG, aggregate, global/linkage and fixed-vector lowering; target-sensitive symbol/calling-convention rules and declared target metadata. | Partial LLVM frontend. With a known triple, the importer records byte order and the default address-space pointer width from the datalayout; native adapter admission rejects incompatible widths and big-endian images. This is not a complete LLVM DataLayout implementation: other layout fields remain unmodeled, and a datalayout without a known triple supplies no TargetInfo. Core admission checks triple/ABI identity; compatibility adapter entries do not. |
| Rust input | [CodegenBackend/MIR bridge](crates/rustc-codegen-trust-cg/src/lib.rs): mono-items, CGUs, ABI marshalling, statics/vtables, runtime helpers, object output and native differential tests. | Separate coherent Trust/private-library workspace. Ordinary programs linking LLVM-built std do not demonstrate CG-built std or self-hosting. Unresolved reference-storage and ABI forms require explicit refusals. |
| Heterogeneous compute | [Compute graphs](crates/trust-cg-lower/src/compute_graph.rs) and [dispatch plans](crates/trust-cg-lower/src/dispatch.rs) retain analysis, dependency/transfer planning and property checks. [CoreML](crates/trust-cg-codegen/src/coreml_emitter.rs) provides MIL construction primitives. | Plans do not execute an accelerator runtime. Production CoreML graph emission refuses without an exact compiler-derived tensor recipe; the separate GPU runtime crate was removed. |
| ONNX/Metal | [ONNX importer](crates/trust-cg-onnx-import/src/lib.rs) converts bounded protobuf `.onnx` and JSON graphs to standalone VNN/tensor JSON, without TrustIR; [Metal emitter](crates/trust-cg-codegen/src/metal_emitter.rs) writes MSL and launch descriptors. | ONNX output is not a native TrustIR frontend. These implementations do not establish a general supported accelerator runtime or complete tensor semantics. |

Production AOT and CLI compilation apply adapter admission and lowering checks;
they do not universally call trust-ir's semantic validator. Supported input
contracts and explicit refusals must therefore be checked at those seams.

TrustIR v52 source `Assert { cond, kind }` is classified on the shared,
target-neutral admission floor before optimization or body skipping. An
unspecified kind receives TrustIR's named panic-kind refusal; stated kinds
retain their exact identity and payload IDs in a typed unsupported-runtime
diagnostic. The diagnostic interpreter resolves payloads only on failure, and
SSA liveness still treats those operands as ordinary uses. No native/WASM
route currently lowers these panics faithfully. Internal LIR checked traps
are not a substitute for Rust panic messages, hooks, caller locations or
cleanup edges. The migration record
identifies the existing explicit failure-block and runtime-call contracts to
reuse rather than introducing a consumer-specific panic ABI.

The separate Rust MIR bridge's [`assert_panic`](crates/rustc-codegen-trust-cg/src/assert_panic.rs)
resolves real lang-item `Instance`s and `FnAbi`, then reuses ordinary argument
marshalling, caller-location scope walking and call/invoke contracts. Only its
failure block reads dynamic bounds/misalignment payloads. Fourteen assertion
forms execute against the same Trust compiler's LLVM lane on ARM64/macOS at
O0–O3 and abort/unwind; certificates are explicitly off. Immediate-abort and
unqualified Darwin termination edges refuse. These compiler-derived runtime
authorities are not implicitly granted to a general TrustIR source producer.

The bridge's [`foreign_abort_eh`](crates/rustc-codegen-trust-cg/src/foreign_abort_eh.rs)
separates the Rust panic strategy from actual foreign callee unwindability.
On the implemented ARM64 Darwin adapter it authenticates a resolved direct
callee's `FnAbi`, seeds that call's landing pad and retains its transitive
source cleanup CFG. Rust abort panics and Rust-defined Drop calls remain
nounwind; live foreign cleanup ends at the original reason-specific runtime
entry. Unsupported targets, indirect/variadic continuations, disabled EH and
unmodeled result materialization retain named refusals. Qualification requires
actual mixed-strategy foreign exceptions, not compilation of their edges.

The bridge's MIR-family modules (ledger L06-P8) each own one decision:
[`set_discriminant`](crates/rustc-codegen-trust-cg/src/set_discriminant.rs)
writes a tag (and reads one at a runtime index) through the shared
memory-model address and tag codec,
[`box_payload_drop`](crates/rustc-codegen-trust-cg/src/box_payload_drop.rs)
hands a box pointer to rustc's own payload drop glue on AArch64 Darwin only
when the payload is kept at rustc's layout,
[`cleanup_loop_homes`](crates/rustc-codegen-trust-cg/src/cleanup_loop_homes.rs)
gives frame homes on AArch64 Darwin only to the cleanup-loop state an unwind
edge cannot pass,
[`indirect_unwind`](crates/rustc-codegen-trust-cg/src/indirect_unwind.rs)
admits Darwin to the typed forwarding thunk for indirect calls with a live
unwind edge, [`link_section`](crates/rustc-codegen-trust-cg/src/link_section.rs)
carries a static's section to the object emitter that places or refuses it,
and [`unmodeled_mir`](crates/rustc-codegen-trust-cg/src/unmodeled_mir.rs)
names the families that stay refused (`become`, assembly, the constructs
removed before runtime MIR, unsafe binders). Evidence is native differential
testing on Darwin (`mir_families_aarch64`), not proof.

Native selectors share the
[`whole_aggregate_memory_access_refusal`](crates/trust-cg-lower/src/types.rs)
contract: direct LIR whole-struct/array/enum loads and stores, including
volatile forms, refuse before emission. Adapter byte-copy legalization and
native ABI lane marshalling are separate paths. Aggregate constants also
check that fields supplied as scalar values have scalar carriers.

The Rust bridge keeps cleanup-live scalar values in stable frame cells because
unwind edges cannot supply ordinary SSA arguments. Reference copies and nested
one-leaf temporary aggregates load the live cell value. Cell projections retain
the original allocation and require exact offset, extent, alignment and leaf
type checks. Linux AArch64 additionally admits checked initialized thin-pointer
wrapper chains and types projected borrow addresses at their producer. Loop
header discovery retains structural headers even when all carried state is in
memory. A failed scalar SSA attempt can retry genuine thin raw pointers in
checked cells on Linux AArch64; the full lowering and admission gates rerun.
This storage choice supplies no new pointer or opaque-call proof authority.
Generated allocator signatures use the target's actual unsigned
64-bit `usize` (`U64`), with explicit casts from internal signed byte counts.
These guarded routes and their independent native fixtures are described in
the October 1 audit.

Evidence authority is implemented in code:

- [Function verification](crates/trust-cg-verify/src/function_verifier.rs) and
  [evidence classification](crates/trust-cg-codegen/src/proof_evidence.rs) prevent
  sampling, name-only matches, self-equalities and unverified reports from
  granting required formal credit. Verifying JIT promotion requires actual
  discharged evidence.
- [AY identity](crates/trust-cg-verify/src/ay_identity.rs) binds the producer to
  build-recorded executable bytes and runs a private immutable copy.
  [AY/Clean replay](crates/trust-cg-verify/src/ay_bridge.rs) rejects bare UNSAT,
  absent/empty proofs and failed checking. Clean is capability-probed and
  byte-identity-bound. Ordinary builds discover a capable checker; local
  [overlay builds](crates/trust-cg-verify/src/toolchain_overlay_manifest.rs)
  additionally pin its digest to the build-recorded manifest and forbid
  fallback to another checker.
  [Persistent certificates](crates/trust-cg-verify/src/obligation_cert_store.rs)
  bind exact queries and tool identities and are independently replayed.
  Sealed source-bound queries may also use the bounded, untrusted
  [closed-definition composer](crates/trust-cg-verify/src/closed_definition_alethe.rs).
  Only the captured checker's acceptance against the complete original problem
  establishes its conditional theorem. Constructive provenance records verifier
  source and checker digests, explicitly no AY run; it grants no AY cache/store
  entry or reuse receipt. Generic raw and word-bound recording routes exclude it.
  Literal selection may follow validated acyclic original definitions, but it
  is not proof authority: each equality projects its original defining premise
  and composes congruence before evaluating a closed shallow term. Shared
  histories use a bounded per-composition proof memo; required symbolic or
  unsupported dependencies decline. Exact guarded Boolean roots may derive
  signed units from the original refutation, then prove an actual ITE's chosen
  branch through core Alethe rules. Facts and selected-ITE proofs are local to
  that one root; they never enter unconditional literal metadata. Sparse
  Boolean reverse uses and per-ITE memoization bound repeated work without
  expanding the definition DAG. BV polynomial candidates remain test-only:
  the captured Clean 8606 rejects them. This does not establish the original
  whole machine relation or complete source-to-native certification.
- [AArch64 source-bound replay](crates/trust-cg-verify/src/source_bound_replay.rs)
  owns bounded frame/arithmetic obligations and the
  [whole-body theorem](crates/trust-cg-verify/src/source_bound_a64_body.rs)
  of a frameless Boolean/bitwise/shift/select/acyclic-control body. A separate
  [pure-jump transition theorem](crates/trust-cg-verify/src/source_bound_a64_pure_jump.rs)
  covers zero-argument, zero-result bodies made entirely of unconditional
  jumps, including cycles: every source destination and decoded B displacement
  participates in a next-PC equality replayed by the same independent checker.
  It admits no value-carrying loop, call, memory or EH effect. The
  [Core affine final-byte check](crates/trust-cg-codegen/src/compiler_affine_bytes.rs)
  compares retained source/LIR with the actual encoder buffer and refuses
  fixups in its admitted domain. The Rust checking implementation is trusted.
- The [composed transition record](crates/trust-cg-verify/src/composed_transition.rs)
  (L09-P3) chains one function's stage checks: legalization (TrustIR to
  LIR) and selection (LIR to raw MachIR) from the affine check, one link per
  optimizer pass or scheduler run that changed the function's interface
  (validated for the record by its dedicated validator or the generic region
  check; CEGIS and the extended loop rotation have no validator, so such a
  run is an uncovered link), the post-allocation value-flow comparison and a
  proof-grade, relocation-free encoding (ENC-5 enforced, the CFG-bound layout
  cross-check). Every link names its relation, check, model and the SHA-256
  interface at both ends; the chain composes only when every required link
  is present and established and adjacent links share one interface. The
  [pipeline wiring](crates/trust-cg-codegen/src/composed_transition.rs)
  builds it on proof-grade preparations, and the sealed Core, the verifying
  JIT and `--emit-proofs` objects refuse a function the affine legalization
  check covers unless its chain composes (required right after preparation,
  before proof promotion) and ends at exactly the bytes they publish (the
  JIT's installed range, the object's whole symbol extent with no relocation
  inside). Outside that domain no TrustIR-to-bytes chain exists, and the
  record says why. Each link is exactly decided over its own model by
  trusted Rust; the chain is not a proof.
- [x86 body proofs](crates/trust-cg-verify/src/x86_source_bound_body.rs) bind exact
  LIR to pre-allocation ISel under explicit System V, callee and memory-trace
  premises. Allocation, frames and encoding have separate structural checks.
  The [final-byte envelope](crates/trust-cg-verify/src/x86_source_bound_envelope.rs)
  proves bounded empty-void/diverging-call ABI shapes over pre-relocation bytes;
  relocation patching and veneers remain outside that theorem.
- [trust-ir's compare statement](crates/trust-cg-verify/src/trust_ir_bv.rs)
  instantiates trust-ir's one bit-vector statement of `ICmp`
  (`trust_ir::bv_meaning`, `chc_x86_vector_icmp_spec`) over `SmtExpr`, one
  node per method, so the spec side of the x86-64 vector-compare obligations
  and of the packed compare-mask reconstruction is trust-ir's and not a copy.
  The certificate rule those cells rest on is trust-ir's code
  (`CHC_X86_ICMP_CERTIFICATE_RULE`), which
  [the certificate gate](scripts/check_x86_icmp_certificates.py) reads through
  the compiled dependency and re-runs by building both tools by revision;
  a pass is a Carcara-checked SMT proof, not a kernel certificate.
- [Portable canaries](crates/trust-cg-verify/src/canary_cert.rs) replay embedded
  exact-query certificates without an installed AY producer. They establish
  a bounded theorem family. [JIT certificates](crates/trust-cg-codegen/src/jit_cert.rs)
  separately bind verifier inputs, bytes, configuration and fixups.
  `replay_check()` checks certificate consistency; independent proof replay and
  published-image integrity are different checks.
- [Exception-table obligations](crates/trust-cg-verify/src/eh_obligations/mod.rs)
  re-parse every AArch64 Darwin Mach-O object and unchecked JIT image that
  carries exception tables, with Mach-O, LSDA, CFI and A64 decoders of their
  own, and decide call-site coverage, landing pads, action tables,
  personality and LSDA binding against the machine IR, and the unwind
  description at every call against the frame its words build (L03-P14).
  The emitters fail closed on a violation. These are in-process decisions,
  testing grade: certified promotion still refuses exception tables.

Defaults also differ: with `verify`, x86 JIT selects `CachedVerified`, while
AArch64 and RISC-V select `Unchecked`. Ambient provenance cross-check defaults
are x86 Enforce and AArch64 Warn; proof-required routes enforce their own
policy. Scalar-cell source/frame/byte/image checkers are production-compiled
but currently supply no production admission authority. The
[Lean model](formal/lean) contains arithmetic proofs and simulation machinery
with no `sorry` or explicit axiom, but its x86-64 capstone is vacuous: Lean
proves its premise false for every program (`Trust/MetaTheorem/Vacuity.lean`),
and the faithfulness of its source and machine definitions is assumed, not
proved. It is not an end-to-end compiler theorem.
Its forward simulation is x86-64 only; `formal/lean/Trust/A64` adds an A64
instruction-word model with proved round trips, bound to the AArch64 emitter
and ENC-5 by a generated golden corpus (`lean_a64_encode_golden_binding`),
and an integer machine semantics with proved condition certificates, without
an AArch64 simulation theorem.

## Compilation boundaries

```text
trust-ir module / CLI input / Trust rustc bridge
                         |
                Compiler + CompilePolicy
                         |
         validate / legalize dialects / admit input
                         |
                 trust-cg-lower adapters
                         |
                  instruction selection
                         |
        target machine IR -> optimization -> allocation
                         |
          frame lowering -> encoding -> object or JIT
```

Dialect legalization (`crates/trust-cg-codegen/src/dialect_legalization.rs`,
ledger `L05-P11`) is the first stage of every `Compiler` entry. A
`DialectLegalizationRegistry` resolves each `DialectOp` and `Ty::Dialect` by
exact name against its registrations, checks the payload grammar, and applies
one rule per site: keep the op for the adapter's typed arm, rewrite it through
trust-ir's `lower_module` driver, call a bound runtime entry with a payload
descriptor, substitute a nominal type's declared carrier, or refuse by name.
The proof requirement of the compile selects which evidence classes are
admitted. The legalized module is re-validated and enters the same adapter and
proof path as core trust-ir, and the result carries one receipt per applied
rule. A module with no rewritten site is passed to the adapter unchanged.
`dialect_pipeline` keeps the earlier default-registry entry points. The
separate `trust-cg-dialect` crate (`DialectModule`, a four-op `machir` facade)
is not on this path.

TrustIR `GEP` uses a single scale: `base + sum(indices) * sizeof(pointee_ty)`.
Both native and WebAssembly lowering preserve that scale across all indices;
an empty list preserves the base. Aggregate field projections use
`ExtractField`/`InsertField` or an explicit byte-offset GEP. The LLVM importer
resolves LLVM's nested type walk into byte offsets before constructing TrustIR.
Native strides retain packed and producer-declared layout authority. Negative
indices and overflowing offsets are outside TrustIR's defined execution domain;
this lowering does not add runtime checks or a general pointer-validity proof.

The public library entry point is
[`Compiler`](crates/trust-cg-codegen/src/compiler.rs). It owns configuration,
module admission, target routing, parallel compilation, results, and evidence
assembly. Target pipelines live in `trust-cg-codegen`: the main
[`pipeline`](crates/trust-cg-codegen/src/pipeline.rs) implements the AArch64
path; [`x86_64/pipeline`](crates/trust-cg-codegen/src/x86_64/pipeline.rs) and
[`riscv/pipeline`](crates/trust-cg-codegen/src/riscv/pipeline.rs) retain their
target-specific lowering and emission. The separate
[`wasm` path](crates/trust-cg-codegen/src/wasm) bypasses machine register
allocation and the native optimizer; it emits a closed module, an island in a
host module, or a relocatable object that `wasm-ld` links. Its two
optimizations run at O1 and above: the trust-ir mid-end
([`trust-cg-irmid`](crates/trust-cg-irmid/src/lib.rs), wired by
`wasm/mid.rs`) keeps a function's rewrite only when its witness checker
(`trust_cg_verify::trust_ir_mid_tv`) and an interpreter differential accept
it, and its output is lowered only when it passes the input's admission
again (its pointer facts come from the capture analysis the lane lays out
frames with, `trust-cg-irmid`'s `escape.rs`, shared by both); the local emission pass (`wasm/opt.rs`) emits a rewritten function
only when `trust_cg_verify::wasm_local_tv` validates it against the lane's
own body (its control cleanup by a lockstep simulation, `validate_control`,
and its segment rewrites against the cleaned body). The rustc bridge
routes `wasm32-unknown-unknown` sessions to its object form. At O1 and
above an object's strong hidden crate-private functions may use an internal
multi-value ABI beside their C-form entries; the structural gate
`trust_cg_verify::wasm_internal_abi` checks every object the lane emits, and
the bridge checks a crate's objects together before linking.

The Trust rustc bridge (`crates/rustc-codegen-trust-cg`) enters through
rustc's `CodegenBackend`. `codegen_crate` lowers MIR to trust-ir while rustc's
type context exists and decides there everything that needs it: the compile
environment and output paths, each function's failure route, and the crate's
mono symbols for the link-integrity check. Before lowering anything it decides
every codegen option it reads (`codegen_options::plan`: honoured, noted,
warned or refused by a `[TCG-OPT-*]` code) and the CGU symbol plan that
carries rustc's linkage onto AArch64 symbols (`function_linkage`). When line
tables are requested each MIR statement's span is stamped on the trust-ir it
lowered to (`span_stamp`). `join_codegen` compiles the lowered
modules through `Compiler` after rustc has dropped the type context, as
rustc's LLVM backend does, so the object compile does not stack its memory on
the query arenas and the mapped crate metadata. An object is a pure function of
its module, compile environment and output path, so this split changes no
emitted byte.

Where Trust lets a codegen backend provide queries (verification off, no
`-Ztrust-ir-lower`, no Trust test monitor), the bridge provides an empty
`exported_generic_symbols` for its crate
(`withheld_exported_generic_symbols`). A downstream crate then instantiates
its own copy of a generic instead of linking one the bridge compiled as a
trapping stub or dropped as dead. Where Trust keeps rustc's provider, a dead
body rustc exports is refused by name (`[TCG-DEAD-BODY-EXPORTED]`).

The target OS/ABI is an explicit authority. `Compiler::new` names only an
architecture and derives the OS/ABI, and so the object format and calling
convention, from the host; `Compiler::new_for_target_spec` takes a full triple.
Every `CompilationResult` records the triple and its origin
(`TargetSelectionOrigin`). The AArch64 `Pipeline` has no default target:
`PipelineConfig::target_triple` selects DarwinPCS/Mach-O or AAPCS64/ELF through
`AArch64AbiVariant::from_target_triple`. Instruction selection, allocation
fix-up, frame lowering, debug info and object emission refuse an empty or
unrecognized triple with `PipelineError::TargetAbiUnresolved`. The in-process
JIT names the host triple explicitly. Signature-level ABI refusals are shared
by every lowering entry: variadic definitions (`[TCG-VARIADIC-DEFINITION]`) and
`byval` parameters (`[TCG-BYVAL-ABI]`) have no lowering and are refused by name.
A direct call or invoke through a variadic declaration with no trustworthy
fixed-argument count (`params: []`, the producer's unsigned `(...)`, or any
variadic `CallingConv::Rust` signature) has no known argument placement and is
refused by name too (`[TCG-UNSIGNED-VARIADIC]`); a variadic declaration that
states its fixed prefix lowers with exactly that many fixed arguments. An
edge that carries no fixed/anonymous split into a variadic callee is refused
as well (OD-56): an invoke of a variadic callee off base AAPCS64, and a
non-variadic `CallIndirect` whose pointer visibly names a variadic
declaration.
The TrustIR adapter takes the same resolved `AArch64AbiVariant` for its
call-boundary decisions (caller-side narrow-integer extension and the Swift
aggregate register-fit check); `AArch64AbiVariant` has no `Default`, and an
`InstructionSelector` refuses ABI classification until `set_abi_variant` names
the convention.

A `TargetSpec` may carry a macOS deployment target, from the triple's OS
version (`aarch64-apple-macos12.0`) or captured by a driver from
`MACOSX_DEPLOYMENT_TARGET`
([`apple_deployment`](crates/trust-cg-codegen/src/apple_deployment.rs)). It
renders into the canonical triple, is bound in the compile policy's artifact
projection, and sets the Mach-O `LC_BUILD_VERSION` minimum OS that the AArch64
and x86-64 Mach-O emitters record; the library never reads the environment.

Ordinary AArch64 direct, variadic and indirect call lowering records classified
ABI facts for each emitted call (`MachFunction::call_abi_facts`: stack-argument bytes and stores, hidden result
pointer, variadic, callee-saved set) and each function's incoming
stack-argument extent (`MachFunction::incoming_stack_arg_bytes`). The O2/O3
tail-call pass reads those facts instead of counting operands, refuses a call
without them, and redirects the stack-argument stores of an eligible sibling
call into the caller's own incoming argument area. Indirect calls retain the
metadata for checking, but this tail-call pass still refuses them.

The hidden return-buffer (`sret`) convention reaches the selector through
three LIR channels the adapter fills from trust-ir declarations, never from a
signature's shape: `Function::abi_sret_param` (this function's own leading
hidden parameter, bound from X8), `Function::sret_arg_callees` (direct-call
callee symbols whose argument 0 is the buffer) and
`Function::sret_arg_indirect_callees` (indirect-call callee values, resolved
through trust-ir's `StaticFunctionPointerAnalysis` to a declaration carrying
`ParamAttrs::sret`). A structural aggregate result (`returns: [Struct]`
classified indirect) needs no channel: the selector allocates the buffer and
stages X8 from the call's result types. All three channels are part of the
retained LIR identity payload because they move an argument between X8 and X0.

The AArch64 ELF relocation model (`static`, `pie`, `pic`) is compiler
configuration, not part of `TargetSpec`: the compiler turns it into the
adapter's `ObjectAccessModel` (TLS dialect plus preemption policy), and the
pipeline's AArch64 emitters re-check `pic` objects for PC-relative references
to preemptible symbols (reading the data globals' linkage/visibility and the
per-function symbol bindings) and executable-only TLS relocations; every other
object format refuses `pie`/`pic`. General-dynamic TLS
is selected as one call-like `TlsDescCall`; frame lowering expands it into the
fixed-register TLSDESC slots after register allocation, and the encoder
re-verifies that four-slot shape before emitting its relocations.

[`object_sections`](crates/trust-cg-codegen/src/object_sections.rs) decides,
per object format, whether an explicit output section can be honored and with
which type and flags; the AArch64 ELF emitters lay text out through one plan
(one `.text`, `.text.<symbol>` per function, or COMDAT groups) while every
symbol's binding still comes from the module's symbol-linkage plan; a COMDAT
group's signature is bound to its definition through the checked symbol API,
and the ELF writer's reparse gate independently rechecks group membership,
signatures and entry sizes.

The lowering catalog keeps every source `FuncId` distinct. Functions and
globals share the downstream symbol namespace; only bodyless External
declarations with the same source name, structural signature, calling convention,
and declaration metadata may repeat a symbol. Their call-edge authorizations
remain tied to the original IDs. Definitions, globals, incompatible contracts,
and name-remapping collisions cannot use this import compatibility rule.

The built-in AArch64 Mach-O linker plans section, stub, GOT, TLV-pointer and
zero-fill addresses before symbol resolution and relocation, and keeps TLV
templates contiguous. Every slid or bound pointer, including GOT and TLV
descriptor slots, becomes a `DYLD_CHAINED_PTR_64` fixup in `__DATA_CONST` or
`__DATA`; input `__DATA,__const`/`__DATA_CONST` data joins the `SG_READ_ONLY`
`__DATA_CONST` segment that dyld write-protects after fixups. One emitter with
checked file/virtual layout admission serves executables and dylibs (base 0,
`LC_ID_DYLIB`, an exports trie); a dylib's default-visibility weak
definitions are exported weak and every pointer to one binds through a
weak-lookup import, so dyld can coalesce them across images. BSS expands
mapped memory without adding file bytes. This limited dyld-aware linker is not
a system-linker replacement, and its format/execution regressions are not
formal linker proofs. The emitter ad-hoc signs each image and re-reads it with
[`macho::codesign`](crates/trust-cg-codegen/src/macho/codesign.rs), an
independent parser of the signature SuperBlob that recomputes every page and
special-slot hash; the same verifier checks ld64's signature on arm64 Darwin
system links.

[`macho::linked_image`](crates/trust-cg-codegen/src/macho/linked_image.rs)
binds a linked arm64 executable or dylib (from ld64 or the standalone
linker) to the objects it was linked from. Its own image reader decodes load
commands, the symbol table, the exports trie, and chained-fixup or
`LC_DYLD_INFO` fixups; its object reader splits sections into the atoms a
linker places. Atoms are placed by the image's symbol table or by the
standalone linker's section addresses (`link_with_dylibs_placed`,
`link_dylib_placed`), checked against content, exports and entry. Each consumed
object relocation is replayed against the image (debug sections and the
linker-consumed `__LD,__compact_unwind` are excluded): branches, page pairs,
GOT/TLV slot loads (or ld64's relaxations), stubs, rebased and bound pointers, TLV descriptors and
differences. Nonzero image content outside the object atoms and the
linker-synthesized sections, and fixups outside the atoms and the linker's
pointer slots, are refused. This accounts for nonzero content in the admitted
sections; zero-fill, all-zero bytes and linker-synthesized content retain their
documented exclusions. Binds are checked against supplied export lists (a
dylib image, a TAPI stub, a declared set), every dependent dylib but
libSystem must be bound, and read-only-after-fixup data must lie in
`SG_READ_ONLY` `__DATA_CONST`. A disagreement refuses the record;
`link_driver::record_darwin_linked_image` and `trust-cg --linked-image-evidence`
write it next to the output and remove the output on refusal, and every
`run_link` removes a record an earlier link left there. It is replay evidence
on the image bytes, not a proof, and does not model dyld's run-time choices
beyond the fixup semantics.

On the AArch64 Mach-O AOT path the `Compiler` hands module emission the same
per-function symbol-linkage plan as ELF (local, global or `N_WEAK_DEF`), and
the adapter's `ObjectAccessModel::macho_dyld` addresses dyld-coalescable
(non-hidden weak and link-once) definitions through the GOT; relocated
immutable globals are emitted into `__DATA,__const`.

System links go through
[`link_driver`](crates/trust-cg-codegen/src/link_driver.rs): a validated
`LinkRequest` (output kind, position independence, static/`-nostdlib`, soname,
rpath, `-Wl` groups) becomes host `cc` arguments, failing linker stderr is
classified into `LinkDiagnostic`s, and a successful arm64 Darwin output without
a valid ad-hoc signature is removed and reported as `LinkError::CodeSignature`. [`runtime_deps`](crates/trust-cg-codegen/src/runtime_deps.rs)
reads an emitted object's undefined symbols back (ELF through the reparse
gate's `read_object_records`, Mach-O through the in-crate parser) and groups
them by providing runtime. The AArch64 ELF emitters check each intra-object
relocation displacement against its psABI window (`RelocationWindow`) before
writing, and frame lowering fuses eligible `ADRP+ADD+LDR/STR` sequences into
`ADRP+LDR/STR #:lo12:` using the placement alignments the `Compiler` derives
from the module's data definitions.

The three AArch64 ELF emitters in `pipeline` finish through one funnel that
appends the empty `.note.GNU-stack` marker and serializes through the ELF
reparse gate. Their shared global-section planner places writable all-zero
definitions without pointer slots in SHT_NOBITS `.bss` and all-zero TLS
templates in `.tbss`. The same class decision
(`object_sections::ElfImplicitSection`) names a COMDAT definition's own
grouped `<base>.<symbol>` section, so zero-fill COMDAT data and templates are
SHT_NOBITS `.bss.<sym>`/`.tbss.<sym>` group members. An explicit zero-fill
name (`.bss*`, `.tbss*`, `.sbss*`, `.lbss*`) is SHT_NOBITS for an all-zero,
relocation-free global and a named refusal otherwise. A mutable global in
`.bss.rel.ro[.*]`, which lld places inside `PT_GNU_RELRO`, is refused as
`[TCG-SECTION-READONLY]`, the `.data.rel.ro` rule. The reparse gate
rejects a NOBITS section, grouped or not, with non-zero intended content or
a relocation targeting one, and binds its type, flags, size and group
membership.

AArch64 debug information has one producer.
`dwarf_info::DwarfDebugInfo::try_emit_section_image` checks every line row,
scope and location range against its function. It then emits the DWARF 4
sections together with every relocated field: code addresses, and the
`strp`, `sec_offset`, abbreviation and line-table offsets. `pipeline` builds
one description per path. The single-function path uses provenance-derived
locations, bounded parameter ranges and frame-base clipping. The
whole-module path uses line rows at exact encoder offsets, each function's
rows in its own source file of a multi-file unit, and names a function by its
producer's `display_path` when it has one. Mach-O places the
image in `__DWARF` and relocates only code addresses. The three ELF emitters
use `elf::dwarf::ElfDwarfSections` in three phases: they add the sections
after every other section, add local `STT_SECTION` anchors through the
checked symbol API before any index is read, and add
`R_AARCH64_ABS64`/`ABS32` records after the table freezes. The object then
finishes through the same funnel. Every AArch64 `.eh_frame`/`__eh_frame`
serialization passes `dwarf_cfi_decode_check::verify_eh_frame_roundtrip`
before its terminator is stripped. A decode disagreement is the typed
`PipelineError::EhFrameDecodeCheck`.

AArch64 NEON arrangement, element-width, lane, immediate-byte, and vector-shift
controls are checked before narrowing. DUP/MOVI derive vector width from an
admitted destination register, not their data immediates. The scalar shift
decode-check independently validates its intent range. DWARF unwind round-trips
parse each CIE/FDE through a cursor bounded to its declared body; checked
lengths cannot consume the next entry. These checks detect malformed
serialization and operand shapes, not the
semantic correctness of every vector operation or unwind program.

The integer conditional-select encoder and independent decode checker admit
exactly three same-width W/X GPR or ZR operands and an unmasked four-bit
condition. SP, cross-bank/width operands and malformed controls reject. The
CSET alias requires an invertible condition (EQ through LE): AL and NV are
both always true. Optimizers use checked logical complementation before
swapping arms or forming CSET. A separate decoded-word concrete/symbolic model
and Linux native controls cover the four select variants, aliasing, W-write
zero extension and preserved NZCV. These are semantic-model and regression
boundaries, not registered lowering proofs or source-to-byte authority.

CMP's encoder and independent decode checker require exactly two operands for
both canonical and typed W/X aliases. Register CMP admits matching GPR/ZR
widths, never SP; immediate CMP admits GPR/SP with an unsigned 12-bit immediate,
never a ZR spelling. Typed opcodes must agree with the actual register bank.

The separate source-bound affine APIs also model all ten scalar integer
comparisons on homogeneous I32/U32/I64/U64 inputs with canonical Boolean
results. Exact modular affine operands are retained on both sides of each
predicate; ordered comparisons never cancel a shared wrapping offset. The raw
machine interpreter captures the actual reaching CMP operands and width, then
interprets CSET's condition. Its final-byte counterpart derives these fields
independently from the words. Both distinguish W/X comparison width from the
zero/one result carrier. SealedCore checks both the raw stream and final encoded
bytes against the retained source. Its bounded final check rejects pending
fixups and mismatches after optimization, allocation and frame lowering. These
checks supplement the existing proof gate; they do not establish a formal proof
of the Rust checker or authorize executable publication.

The diagnostic output-store checker binds retained TrustIR signatures and
ordered stores through actual adapter LIR to independently decoded A64 bytes.
It distinguishes frameless bodies from the exact sixteen-byte FP/LR envelope,
and tracks constant MADD address computations and reused argument registers.
The [actual writer qualification](reports/perf/2026-09-20-frameless-output-bytes/README.md)
includes independent conditional byte-map replay and fresh native endpoints.
Caller validity and ownership remain premises; this checker supplies no new
production instruction or publication authority.

`source_bound_frame` returns a typed refusal. Only the admitted source (a
chain or pure-arithmetic diamond view inside the affine domain) decides
applicability; after the frame and control skeleton are recognized, a
disagreeing body, an altered FP/LR envelope or a branch that contradicts the
final layout or recorded CFG is a `FrameBindingMismatch`, and every other
shape is `FrameShapeUnsupported`. The AArch64 function verifier classifies each
name-matched source pair unless source checking is off. Under enforcement a
mismatch is the `SourceBoundFrameMismatch` precondition failure, which every
promotion predicate (proof-required compiles, the sealed Core, verifying JIT
certificates) rejects by name; warn mode reports it as a diagnostic.

`source_bound_a64_body` is the frameless AArch64 whole-body owner, tried
when the frame owner binds nothing. Its source is an acyclic LIR CFG of
`Jump`/`Brif`/`Return` over `I32`/`I64`/`B1` constants, copies, add/sub/neg,
bitwise rows and Boolean connectives, shifts under trust-ir's
`ShiftInRange` rule, comparisons and `Eq`/`Ne` selects; its machine is the
final allocated body read as the words the encoder emits. Both become gated
DAGs (reach bits, edge taken bits, join values by their one taken edge), so
one theorem compares the returned values as functions without pairing paths.
A concrete evaluation can only refuse (`SourceBoundA64BodyMismatch` under
Enforce), and refuses a theorem whose domain premise disagrees with the
evaluated definedness; a replayed proof credits the returned value's slice
and the body's transfers, never copies or constants (E0.2), and exports
travel as `SourceBoundObligationKind::A64Body` on each row's role category.
The word semantics of the admitted rows are trusted translator code, tested
by per-row fixtures with mis-model controls and by a CPU differential of the
theorem's machine term (`aarch64_source_bound_body`).

`x86_source_bound_body` is the x86-64 counterpart for the pre-RA
`X86ISelFunction` the x86 certificate lane verifies: one replayed whole-body
theorem per function (slices 1-2: System V; B1/I8/I16/I32/I64 and pointer
carriers; constants, copies, extensions, truncations, add/sub/mul, logic and
constant shifts, over a bounded jump chain; the observable is the return bits
every caller reads, a `bool` being the backend's clean 32-bit EAX; slice 3:
direct calls with register arguments, the observable adding every call's
arguments and each call's result shared between the two sides after the walk
pairs the calls by position and callee; slice 4: private stack slots bound by
index and modelled exactly byte by byte in both walks, never observed, and
scalar loads and stores of incoming memory stated as an Ackermann-reduced
access trace: the walk pairs each machine access with the source access at
the same world-trace position, a paired load reads one shared input (for a
`bool`, the whole byte, which the source reads as `!= 0` like trust-ir's
`Load Bool`, with no validity premise), and the observable adds every
access's address and every store's value; slice 5: a
two-result return in RAX then RDX, observed lane by lane, and calls with
such pair results, whose `bool` lane defines bit 0 alone (rustc's `{ T, i1 }`
pair return has no `zeroext`); `GlobalRef`/`ExternRef` as one shared free address per
symbol and form, bound to the machine's `LeaRip`/`MovRipRel`; and
branch-free `Icmp`, judged against `cmp` + `setcc` + `movzx` through the
shared x86 EFLAGS model; slice 6: acyclic control flow, every entry-to-end
path of a LIR DAG of `Brif`s, `Switch` compare chains, joins, several
returns and trap paths, each paired with the machine path it must run
through a one-to-one block correspondence found from the rows' TV-1
provenance (a machine CFG without one makes no claim) and stated as one
`(or (not C_P) (and M_P O_P))`
claim per path, the `jcc` (and `cmovcc`) conditions read through the same
EFLAGS model from a `cmp`/`test` of their own block; `Select` as `cmovcc`;
and a path's read of a private byte no store on it wrote as the slot's
initial value, shared with the machine; slice 7: calls through memory, a
private slot's address passed to a direct call (a `&mut`/`&` out-parameter,
or the hidden return buffer of an `sret` callee) making the slot escape to
that call and every later one: each call's observable adds the escaped
slots' contents at the call, in 8-byte chunks, the walk checks that the
machine passes exactly the paired slot and offset, and every byte of every
escaped slot after the call is one free input per call site and byte shared
by the two sides (the Ackermann-reduced call UF extended to its memory
outputs); an incoming access through an address that may derive from an
escaped slot is outside the domain), built from the exact LIR and the exact
ISel stream and tied only by verify-owned System V tables, with live replay
reachable only through the sealed `SourceBoundReplay` owners.
The selector's byte and word
loads are the zero-extending `movzx r32, m8/m16` (`MovzxRM8`/`MovzxRM16`),
which write the whole register, so the walk models their destination exactly
as the loaded bytes zero-extended (the merging `mov r8/r16, m`, whose upper
bits are a free input, is no longer selected). An admitted body that disagrees
is the `SourceBoundX86BodyMismatch` precondition failure
(`[TCG-SOURCE-BOUND-X86-MISMATCH]`); see LIMITATIONS.md for its claim scope.

Scalar FCSEL similarly requires exactly three matching S/D registers and a
four-bit condition. Its independent decoder checks every encoded field and
fixed bit, including the scalar width; V31 is ordinary data storage, not ZR.
The low-level encoding API rejects out-of-range conditions in debug and
optimized builds. Generic FP mux model lemmas do not authorize an emitted
FCSEL: the runtime verifier lacks the required source, operand and flag-producer
correspondence and reports it unverified. Valid diagnostic compilation remains
available separately from proof-required publication.

FCMP's source and machine value models distinguish ordered-not-equal from
hardware NE on NaNs. Their finite tests use an independent IEEE bit oracle.
Scalar comparison templates bind distinct raw IEEE bit inputs through typed FP
reinterpretations. The checked finite evaluator validates these bindings and
evaluates the actual stored trees, not a predicate reconstructed from a name.
Its edge cases and configured random trials remain statistical, including when
the configured integer exhaustive threshold exceeds the operand width. Six
AArch64 templates remain structural identities and receive no independent
static-lowering credit. These models do not bind a concrete FCMP's full NZCV
result or a CSET's source operands, condition and reaching flags; standalone
runtime attribution for both opcodes therefore remains unverified.

AArch64 `LdrRO`/`StrRO` and `LdrbRO`/`LdrhRO`/`StrbRO`/`StrhRO`
encoding validates exact packed modes, operand counts and register roles before
forming fields. The narrow opcodes fix byte/halfword width independently of
their W/X/ZR carriers; floating-point carriers are not narrow integer values.
The independent byte checker reconstructs the fields without using the encoder.
Spill materialization keeps a Gpr32 index's actual W reload while using the
resulting zero-extended X view only where required by full64 addressing modes.
Spill reload CSE tracks the complete post-load X/Q state, not just the slot's
low bytes: a narrow W/H/S/D store alone cannot establish that state. Actual
loads and full X/Q stores can establish facts; overlap and memory barriers
still invalidate them. These admission/dataflow and finite native controls
do not establish source-bound memory proofs or scalable SVE preservation.

Scalar full unrolling preserves the complete RO index scale: both its IV
coefficient and hoisted invariant offset are scaled before base addition.
Only exact default/LSL/SXTX modes with an admitted arithmetic domain are folded;
low32 packed extensions or unsupported typed slices retain RO operations.
Explicit extension of a proven small IV remains eligible. The separate RI
whole-address caller is unchanged and is not qualified by this RO repair.

`CompilerConfig::default()` selects AArch64 for object generation. Embedders
that execute code in the current process must choose `Compiler::for_host()` or
`CompilerConfig::for_host_jit()` and satisfy the JIT's selected evidence policy.
Host selection alone does not certify an artifact.

AArch64 JIT unwind tables live in `jit_unwind`. The compiler passes the frame
layouts recorded by its own preparation; the JIT encodes EH functions with
their resolved LSDA, appends LSDAs, a personality slot and a terminated
`.eh_frame` after code and veneers, binds each pointer through the manifest's
relocation list, and re-decodes the tables, prologues and each FDE's CFA
program (checked against the decoded prologue) before mapping.
`EhFrameJitUnwindRegistration` registers them after the read-execute seal
and deregisters before any unmap, so it follows the buffer's teardown and
lease policy. Proof-grade JIT requests refuse this path by name.

AOT exception metadata is owned by `exception_handling` and the pipeline's
LSDA generation. The lowering adapter selects each function's personality
(`Producer::TRust` selects `rust_eh_personality`, otherwise the module
default) and binds the module's reserved `__trust_cg_eh_type_table`, read
once per module translation and shared (a trust-ir v50 `splat` table stays
one symbol and a length), onto functions with typed catches; the LSDA
builder emits identity TType slots with typeinfo relocations, storing only
the slots the pads bind, the Mach-O emitters bind them
`ARM64_RELOC_POINTER_TO_GOT`, and the module planner binds every
compact-unwind entry and DWARF-fallback CIE to its function's personality.
Typed catches bind only under `__gxx_personality_v0`; the catch-all slot is
fixed by the function's table at lowering, not by the pads that survive
optimization. Unsupported shapes (filters, ELF typed catches, typed catches
under `rust_eh_personality`, ELF or JIT mixed personalities, unbound
indices, and merge inputs that would bind through another input's table)
are refused by name.

## Ownership

| Boundary | Owning crates | Responsibility |
| --- | --- | --- |
| Shared representation | `trust-cg-ir` | Machine instructions, operands, registers, target descriptions, provenance, and traces. |
| Input adaptation | `trust-cg-codegen` (`dialect_legalization`), `trust-cg-dialect`, `trust-cg-lower` | Registry-driven trust-ir dialect legalization with receipts, the `DialectModule` conversion facade, trust-ir admission/lowering, ABI carriers, and instruction selection. |
| Machine transforms | `trust-cg-opt` | Pass scheduling, analyses, rewrite recognition, target transforms, and PGO/vectorization support. |
| trust-ir mid-end | `trust-cg-irmid` | Per-function trust-ir → trust-ir rewrites (wasm32 profile) with snapshot/rollback, witness checks, interpreter differential and proof-table transport; the pointer offset and escape analysis the wasm32 lane shares (`escape.rs`). |
| Equality saturation (Tier E, library only) | `trust-cg-eqsat`, `trust-cg-eqsat-check` | An eager acyclic e-graph over trust-ir function bodies that emits a derivation for each rewrite, and an independent checker that replays it against a rule registry. Not called by `Compiler::compile` or the irmid pass manager (PKG-U3); contract in docs/eqsat-tier-e.md. |
| Equality saturation (Tier S, library only) | `trust-cg-eqsat` (`saturate`), `trust-cg-eqsat-check` (`check_region`) | Budgeted saturation of a bounded region of total operators with declared stages, extraction that prices a shared node once and never returns a costlier region, and an independent checker of (input region, output region, derivation) triples. Nothing cuts a region out of a function or elaborates one back (PKG-U3), and no rule is proved (PKG-U2); contract in docs/eqsat-tier-s.md. |
| Allocation | `trust-cg-regalloc` | Liveness, interference, allocation, coalescing, spills, and allocation validation. |
| Output orchestration | `trust-cg-codegen` | Policy capture, target pipelines, object writers, relocation, JIT publication, and artifact caches. |
| Evidence | `trust-cg-verify`, `trust-cg-drat-trim` | Obligations, evaluator/solver results, certificate handling, and selected independent SAT replay. |
| Process configuration | `trust-cg-process-env` | Shared process-environment access, including coordinated test mutation. |
| Frontends and tools | `trust-cg-cli`, `trust-cg-llvm-import`, `trust-cg-onnx-import`, `trust-cg-lift` | CLI, importers, and binary-lifting experiments. |
| Validation | `trust-cg-test`, `trust-cg-fuzz` | Local test orchestration and differential testing. |
| Research consumers | `trust-cg-jit-matrix`, `trust-cg-sat-host` | JIT matrices and SAT-host workloads. |
| Compatibility | `trust-types` in `crates/trust-types-compat` | Compatibility types for pinned companion interfaces. |

The SMT solver route uses **AY only**, with independent Alethe checking by
**Clean**. Sealed source-bound obligations can additionally supply constructive
closed-definition candidates to that same captured checker against the exact
original query, without invoking or impersonating AY. Unsupported or rejected
candidates retain the ordinary AY route; this does not alter required compiler,
caller or native gates. AY is the owning Trust toolchain's `bin/ay`, admitted by the SHA-256
recorded when `trust-cg-verify` was built (`ay_identity`). In an ordinary build,
Clean is taken first from that same toolchain (`bin/clean`, the checker shipped
with the AY whose proofs it reads), and from aterm's managed package channel
only when that toolchain ships no capable checker; aterm is the self-contained
toolchain, not a wrapper requiring sibling source builds. `aterm_toolchain` resolves
package-store `current` links to versioned executable paths so certificate
identities bind actual tool bytes rather than launcher scripts. Clean's
control-proof probe is mandatory. An incapable installed checker cannot be
concealed by discovering a developer's local Clean build.
An overlay build instead requires its `overlay.json` to match the recorded AY
digest, commit and build number and the current Clean digest at build time.
It pins Clean to that recorded digest, rejects overrides with different bytes
and never falls back to the managed package. An invalid manifest admits neither tool. The manifest and
its Clean source commit are unsigned provenance labels, not a proof of the
tools' implementations. Optional
[proof-tool records](crates/trust-cg-verify/src/proof_tool_record.rs) identify
admitted AY launch requests and identity-bound Clean proof checks; recording is
best effort and does not change a verdict.
A process runs the probe at most once per candidate file state and child
environment: the scheduling hint at backend `init` and every authority capture
share the recorded verdict, so the authority capture's selection can rest on a
verdict the hint reached for the identical state. The authority capture does
not digest a candidate whose recorded verdict is a stable defect (in
authority-first order it digests before it probes), rebinds a reused capable
verdict only if the state is unchanged after its digest, and always carries
the digest of the selected checker's current bytes; `TCG_PARANOID_FILE_HASH`
refuses the reuse. `trust_cg_verify::process_cost` counts the probes, the
executable digests, the AY starts and the assessment spawns. The bridge prints
them under `time`, with a start-path trace of when each step happened after
the process started. The identity warm-up probes the checker on a helper
thread while it admits AY, and requires both results before the first start.
After admission, in a compile whose frontend named its scope (the rustc
bridge), it also replays the certificates the scope's last compile used
([replay prefetch](crates/trust-cg-verify/src/cert_replay_prefetch.rs)), so
the compile's own requests find the positive replay memo. A prefetch replay is
the consume path's full check under the key the consume path derives; the
per-scope hint that names the certificates is an untrusted scheduling input,
and `persist` at the end of the compile stops the prefetch. The same mutex
serializes authority capture, optional resident startup and each replay with
that stop: a delayed hinted startup cannot begin after the stop returns, and
an active hinted operation completes before it returns. Other identity warming
and an existing resident server's exit cleanup retain their own lifecycle.

Verification process execution is separate from proof authority. The private
[`subprocess` boundary](crates/trust-cg-verify/src/subprocess.rs) owns fresh AY
calls, AY version probes and Lean checker capture. It services both output
streams without blocking reader threads and requires complete EOF plus observed
child exit before returning a transcript. Finite deadlines remain active after
direct-child exit; capture errors and timeouts do not publish partial results.
Unix child identity remains unreaped until owned-group cleanup has been
requested. Cleanup polls for at most 100ms and retains unconfirmed exits/errors;
Windows only targets the direct child. AY's zero timeout still means unlimited.
The macOS ARM64 controls do not establish Windows/Linux runtime behavior,
hard real-time bounds, escaped-child cleanup or bounded output memory use.
Resident AY uses the same teardown and a private
[`interactive` exchange](crates/trust-cg-verify/src/subprocess/interactive.rs)
that polls both directions without an I/O worker. Its completion boundary is
the caller's unique sentinel plus all input written, not process exit/EOF.
Partial UTF-8 lines and bytes following a frame are retained without rescanning
consumed prefixes. One elapsed-duration deadline, started when the query is
admitted to the server, covers the spawn, request writing and response reading;
an expired attempt does not retry fresh. Neither time queued behind other
queries nor the first start of a new private AY copy is charged to it: on
macOS that first start is made (or waited for) before any solver deadline
starts, at most once per process, and a completed one is recorded beside the
copy so later processes do not repeat it (`ay_identity::first_start`).
When a process has not yet digested the AY's file state and no copy is
published, one read streams the private copy and is the admission digest; the
source's stamp is checked before the open and after the read, before the
streamed digest is compared (a mismatch is refused from that digest), and the
published copy is still digested before it is used. On macOS a copy this
process has just streamed from admitted bytes and published itself is spawned
suspended and checked to be stopped with no user time
(`ay_private_copy::begin_host_assessment`). Success also requires a successful
kill and an exact-child reap reporting `SIGKILL`. A failed check or cleanup
disables further assessment spawns; the bounded attempt cannot guarantee OS
cleanup on every failure. A copy another process published first is verified
before any priming or ordinary execution. That starts the
host's assessment of the new executable while the copy is verified and the
front end runs. The first start still waits for the assessment to finish.
Frame-handler unwinding immediately stops the interrupted exchange; poisoned
slots discard their process before reuse. Exhausted sequence IDs
cannot reuse a sentinel. AY still owns protocol parsing and proof admission;
a framed UNSAT alone is not independently checked evidence. Windows uses
nonblocking named-pipe writes but is not compiled/runtime-tested on this host.
Clean capability probes/replay and AY cache minting in `obligation_cert_store`
use the same complete-capture runner. Authority-bearing calls receive
`AYConfig::timeout_ms`; scheduling probes use the effective default. Zero
remains unlimited. These are per-subprocess budgets, not a whole-query deadline;
staging and executable hashing are outside them. Promotion distinguishes a
timeout from a rejected proof and does not re-probe merely to format a failure.
Transient timeout/I/O outcomes are not memoized as executable defects.
Both certificate writers share owned, same-directory staging and no-clobber
publication. Existing entries are preserved, including when threads race;
replay still binds exact query, producer, certificate and checker identities.

Encoding evidence crosses the crate boundary in one direction.
trust-cg-codegen's emission decode checks (ENC-3 for x86-64, ENC-5 for AArch64)
run on every emitted instruction. For the opcode families they have an arm
for, they re-decode the emitted bytes independently, except for shapes an
arm itself names as not decoded (on AArch64, 28 named reasons); every other
family is counted against a catch-all allowlist reason and its bytes are not
decoded (on AArch64, 12 of the coverage gate's 302 emittable-class rows: the
12 opaque LL/SC carriers, which have no single-word encoding; the 302 include
scalar ADDP, which no lowering selects yet). ENC-5's
scalar FP/Advanced SIMD and integer slices (`aarch64::decode_check_fp_simd`,
`aarch64::decode_check_int`) read each word by its Arm ARM encoding class. On
proof-grade AArch64 routes an undecoded word is a refusal
(`[TCG-DECODE-CHECK-UNDECODED]`); compatibility routes count it.
[LIMITATIONS.md](LIMITATIONS.md) gives the measured Darwin floor census,
describes the arms' named exits, and lists the opcodes whose
encoder does not read a trailing operand the verifier accepts (the AArch64
encoder does not check arity). For selected opcodes they
also run a trust-cg-verify word-level obligation or decoder
(`x86_encoding_proofs`, `aarch64_value_decode_proofs`, and the FP-compare
decoder of `aarch64_flag_consumer_proofs`) on the bytes they just emitted.
Two `covered_elsewhere` certificates cite one of these checks as their
evidence (x86-64 `MovRI` cites ENC-3's `x86_encoding_proofs` run, AArch64
`AlignNop` ENC-5's NOP decode), so the certificate lane takes the encoding
pipeline's backing for that check (`decode_check::DecodeCheckBacking`) and
issues them positive only when the check ran in enforce mode; otherwise each
is a blocking `covered_elsewhere_withheld` row (X-OPCODES-P13).
Because trust-cg-verify cannot depend on the encoder, its opcode-coverage
credits for those families rest on captured encoder output that test targets
re-derive from the live encoder. For the move-wide, GPR copy, add/sub
immediate, compare, shifted-register, UMULH, direct-branch and scalar
general-purpose load/store shapes (immediate, sign-extending, pre/post-index
writeback and register offset) that
[`aarch64_instruction_word_proofs`](crates/trust-cg-verify/src/aarch64_instruction_word_proofs.rs)
admits, ENC-5 also requires the emitted word to equal the word that module
re-derives from the operands (outside fixup holes); the function verifier
judges those instructions by an obligation over that word's decoded
semantics, which it reports and never credits (L07-P2). For every scalar
memory word (immediate, `H`/`S`/`D`/`Q`, sign-extending, pre/post-index
writeback and register offset; the `H`/`S`/`D`/`Q` words from a verify-side
scalar encoder, L04-P1) and pair (`LDP`/`STP`) memory words,
[`aarch64_memory_effect`](crates/trust-cg-verify/src/aarch64_memory_effect.rs)
states the access as small obligations over the word literal: fields, lane
addresses, writeback and per-lane bytes. ENC-5 requires the emitted word to
be that literal. For the single-instruction atomics (`LDAR`/`STLR`, `CAS`,
`SWP`, `LD<op>`),
[`aarch64_atomic_effect`](crates/trust-cg-verify/src/aarch64_atomic_effect.rs)
states every field, the returned value and the memory window the same way, and
[`aarch64_atomic_forms`](crates/trust-cg-verify/src/aarch64_atomic_forms.rs)
holds the 48 form theorems whose committed certificates
(`verdict_db/atomic_memory_certs/`) credit them under the Formal-only rule
(X-OPCODES-P2);
[`aarch64_neon_structure_forms`](crates/trust-cg-verify/src/aarch64_neon_structure_forms.rs)
holds the 14 NEON `LD1`/`ST1` post-index form theorems whose certificates
(`verdict_db/neon_memory_certs/`) credit those rows the same way, with the
memory-effect decomposition as the per-instruction check (L04-P1). The coverage gate credits a memory or atomic opcode only when
every legal form of it carries that per-instruction authority
([`bound_memory_row_credit`](crates/trust-cg-verify/src/bound_memory_row_credit.rs)). For ordinary opcode rows, the walk applies these obligations
after the row's own lane and the Formal-only bound-memory rule
([`bound_memory_authority`](crates/trust-cg-verify/src/bound_memory_authority.rs)),
which is the only route to credit in those lanes. A source-bound frame
envelope takes an earlier route: the frame theorem judges its establishing
`ADD`, and its save and restore records also take this decomposition, on the
source-bound route described below. The obligations are decided
exactly in process, and a refutation fails the row. For an unbound row they
are replayed live through AY and Clean only under the diagnostic
`memory-effect-replay` knob, and they never credit (L07-P2, X-OPCODES-P1,
L04-P7). A row a source-bound owner binds is the exception
([`aarch64_memory_source_binding`](crates/trust-cg-verify/src/aarch64_memory_source_binding.rs)):
the save and restore records of a source-bound leaf frame, bound to the frame
theorem's record, and each scalar access of a frameless leaf that
[`source_bound_memory_leaf`](crates/trust-cg-verify/src/source_bound_memory_leaf.rs)
matched, in lock step, to its LIR access. Its parts are replayed through the
source-bound route, with receipts bound to their exact queries. The row is
credited only when every part has a Clean-checked certificate, and a frame
record also needs the replayed frame theorem (OD-139 in
docs/decision-record.md). A formal `--emit-proofs`
sidecar that carries the frame theorem carries the twelve frame-record parts
too; a credited leaf access has no exportable obligation, so its function's
sidecar is refused by name.
The NEON LD1/ST1
post-index transfers join the same decomposition, applied to the registry
arm's row (L04-P6). Their sibling,
[`aarch64_neon_lane_effect`](crates/trust-cg-verify/src/aarch64_neon_lane_effect.rs),
states each emitted NEON horizontal reduction or permute (DUP, INS, UMOV,
UMAXV, ADDP, REV32/REV64, RBIT, EXT, MOVI) over its word literal the same way:
fields, and each destination half or GPR computed from the word's
operation-selecting and index fields. ENC-5 binds the emitted word to it; the
parts are decided exactly in process, refute or annotate the row, have no
live replay lane and never credit. The `neon_semantics` models both use are
checked against the CPU by the silicon differential
`tests/aarch64_neon_silicon_differential.rs` (testing evidence).

The CRC32/CRC32C and `SUBS #imm` words are judged by decoded-word
obligations over the word re-derived from the operands (L04-P1):
[`aarch64_crc32_proofs`](crates/trust-cg-verify/src/aarch64_crc32_proofs.rs)
states the Arm ARM `Poly32Mod2` pseudocode of the decoded word against the
reflected shift register of the intrinsic and decides it exactly with
[`gf2_affine_decide`](crates/trust-cg-verify/src/gf2_affine_decide.rs)
(every result bit as an affine form over GF(2), memoized over the shared
division), and
[`aarch64_subs_imm_proofs`](crates/trust-cg-verify/src/aarch64_subs_imm_proofs.rs)
states the destination and NZCV of `AddWithCarry` against the comparison the
operands name, decided by the bit-serial automaton. ENC-5 requires the
emitted word to be the re-derived one; the function verifier reports a
holding row unverified, and the coverage gate credits the rows only through
their families' credit hooks (word, width, polynomial, operand and
flag-meaning controls must refute). Both are testing grade, never credit.

Trap carriers are judged by their expansion (L04-P12).
[`aarch64_trap_expansion`](crates/trust-cg-verify/src/aarch64_trap_expansion.rs)
states, for each guard carrier, the compare/branch/`BRK #1` sequence
`lower::expand_trap_*` emits, decodes its words with its own Arm ARM fields
and semantics, and decides exactly in process (the bit-serial automaton of
[`bitserial_decide`](crates/trust-cg-verify/src/bitserial_decide.rs), or
sound rewriting for the 64-bit multiplications) that they trap exactly when
the carrier's source condition holds. The late expansion records each
expansion in `MachFunction::trap_expansions`; the function verifier judges the
recorded instructions at the closing `BRK` (and a carrier before allocation by
its stated expansion), and the final encoder binds the emitted words of every
recorded expansion to the same obligation after ENC-5's per-word arms (and
refuses a recorded carrier outside the model by name). Only a Clean-checked
live replay credits a conditional row: under an enforced source-bound replay
policy, the register-renamed obligation is a sealed `SourceBoundReplay` owner
replayed through the verification request (its admitted AY and Clean,
policy, refusals and reuse identity), never through the ambient environment
or a process-wide verdict cache.
[`aarch64_trap_guard`](crates/trust-cg-verify/src/aarch64_trap_guard.rs) is
a veto layer over that verdict: it binds each recorded carrier to the source
guard its TV-1 stamp names, requires the window to execute, re-checks the
window with its own model, admits an unconditional `BRK` only in an
established role (the certified stack-limit trap, the word after a noreturn
call, the entry block's source `Trap`), and fails or refuses a function that
lost a source trap; its failures and refusals replace milder rows, and it
never credits a row.

NZCV consumers are bound per instruction, not per opcode.
[`aarch64_flag_consumer_proofs`](crates/trust-cg-verify/src/aarch64_flag_consumer_proofs.rs)
owns the reaching-producer walk shared by the function verifier's general
path and its source-bound CSET path, the producer/consumer obligation families
(FCMP packed NZCV, FCMP -> CSET, CSEL/CSINC/CSNEG over CMP/TST/FCMP), their
captured words, boundary battery, negative controls and coverage-gate credit
hook. Its machine sides reuse the decoded conditional-select model
(`aarch64_csel_semantics`) and the NZCV producer models (`nzcv`), which a
native silicon fixture replays.

A producer enum layout descriptor picks one of three routes in trust-cg-lower.
A Direct encoding (and a descriptor-less enum) is answered by
[`direct_enum`](crates/trust-cg-lower/src/direct_enum.rs): the tag lane is
trust-ir's `canonical_tag_repr` with the discriminant value as the stored
word, the canonical `Type::Enum` is kept where it reproduces the declared
bytes, and any other Direct descriptor lowers to a byte-image carrier of the
declared size and alignment whose tag and field addresses come from the
descriptor (`DirectEnumImage`, shared with the object writer's global
initializer through `module_direct_enum_image`). Untagged and Niche encodings
lower to the payload struct the descriptor states, admitted by equality
(`untagged_enum_carrier` and `niche_enum_carrier` in `adapter.rs`). A niche enum's discriminant belongs to
the [`niche_codec`](crates/trust-cg-lower/src/niche_codec.rs) module. It checks
the niche parameters against trust-cg's own layout, then emits the lane decode
or encode from existing LIR opcodes. It runs only where element 0 or an enum
constant is lowered, so payload-only access keeps its admission when the codec
refuses a descriptor.

Borrows, binding frames and `Undef` pass through one named legalization
stage, [`borrow_frame_undef`](crates/trust-cg-lower/src/borrow_frame_undef.rs)
(`borrow-frame-undef-legalization`). The adapter runs it once per function,
before any instruction of that function is lowered and on every entry: it
rewrites no module, so it is ordinary lowering rather than a
`PreLirTransform`, and the strict entry accepts it. The stage decides the
whole function (borrow structure, frame lineage, slot layout, SSA liveness of
superseded frame handles, and a forward trace of every poison value) and
either refuses it by name (`AdapterError::LegalizationRefused`,
`[TCG-BFU]`) or hands the per-instruction arms a plan they consume
exclusively. The arms lower a borrow to a `Copy`, a frame to one zero-filled
stack slot addressed by `StackAddr`/`Iadd`/`Store`/`Load`, and an admitted
scalar `Undef` to the zero constant of its carrier. They record what they
emitted in `ProofContext::borrow_frame_undef`, a dedicated channel the
retained strict-LIR identity hashes (payload schema v7) and no optimization
reads.

A first-class closure (`Ty::Closure`) is the struct of its declared captures
in capture order, and nothing else: trust-ir's `func` lane has no runtime
layout, so a `Constant::Closure` literal materializes only that environment
(`translate_closure_const` in `adapter.rs`, through the aggregate-constant
recursion that also fills a closure, `FnDef` or `SymbolAddr` nested as an
aggregate field). `CallIndirect` over a closure callee is lowered by
`translate_closure_application` as the direct call to the closure's static
code identity — the defining literal reached through `Copy`/`InsertField`
(`resolve_closure_literal`) — with the captures extracted into synthetic
trust-ir temporaries and spread ahead of the apparent arguments, so the
canonical direct-call arm owns the ABI. The physical signature is checked
against `captures ++ apparent params -> apparent returns`; a closure whose
literal is not visible (parameter, `Select`, projection, `Call` result,
memory) is refused by name. The AOT local-binding census counts such an
application to a module-local body as a direct edge.

Sequences (`Ty::Sequence`) and boxed sets (`Ty::Set(_, Boxed)`) have one
machine image, defined in
[`sequence_layout`](crates/trust-cg-lower/src/sequence_layout.rs) and read by
every path that touches one. trust-ir states only the form ("a packed buffer
(length-prefixed)"); `Module::ty_layout_shape` and the reference
interpreter's `byte_size` give a collection no layout, and trust-ir's codegen
gate names an element op over a sequence `UnlowerableForCodegen`. The image is
therefore this backend's: a `u64` element count, then the elements packed
from offset 8 (`Bool` as a 0/1 byte, `I8`..`I64`, `U8`..`U64`, `F32`, `F64`),
and a collection VALUE is the pointer to an immutable image in one register.
`translate_type_with_enum_tables_inner` admits a collection only in a value
slot (depth 0: parameter, result, block parameter, `Copy`/`Select`/`SeqMap`
result); nested in any other type it is refused, and
`refuse_collection_outside_value_positions` refuses every instruction that
spells one elsewhere (load, store, alloca, GEP, cast, arithmetic) or consumes
one as an operand, and every `ExtractElement`/`InsertElement` over one. A
function whose single result is a collection takes one extra trailing pointer
parameter, the caller-provided result buffer, copies its result image there
and returns it in `x0`; the caller sizes that buffer from the length the
callee publishes (`ModuleLengthFacts`: a static count, or the count of one
sequence parameter, as a least fixpoint over the call graph, computed once per
module translation). That capacity rests on the callee being the body this
module analyzed: a body another object may replace at link or load time
(`Weak`/`LinkOnce`, preemptible under a shared-object relocation model, or a
weak definition dyld may coalesce) publishes no length, and a call to it is
refused by name. At run time the callee traps unless the image it returns has
its published length, and the caller traps unless the returned header is the
count it sized for; the caller's check runs after the callee wrote, so it
detects a broken length but cannot undo an overrun. Constants are fixed frame
slots; a `SeqMapAddK`/`SeqMapNot`/`SeqMap` result is a fixed slot only when
its length is static and its block is on no CFG cycle (a fixed slot traps
before it is written unless its source has that count), otherwise a
runtime-sized stack allocation per execution. A `SeqMap` gives every element
its own cell for the rest of the frame, as trust-ir's interpreter does. The
`SeqMap` family is expanded in the adapter as a
counted loop in blocks of its own: `translate_block` accepts a
`pending_block_split` (the loop header and body plus the continuation the rest
of the trust-ir block lands in), and the general `SeqMap`'s element call
re-enters the direct-call arm, with its exact-call census recorded at the loop
body's coordinates. The image and ABI are defined for AArch64 and the C
calling convention only; other targets and conventions refuse collections by
name.

Every AArch64 encode also runs `aarch64::layout_crosscheck` over its final
image. It recomputes block starts from `block_order` and the
one-word-per-non-pseudo emission rule, bit-extracts every local branch
displacement, jump-table ADR and entry, and ADR/LDR-literal target from the
words, and binds each symbolic fixup to the one emitted instruction that names
its symbol, with the relocated field still the zero placeholder. The relaxing
`lower` path checks its relaxed bytes against still-symbolic branch intents.
Encodes run under an integrity policy: the compatibility policy keeps the
diagnostic environment downgrades of the post-RA reaching-definition,
spill-slot and decode nets, while the proof-grade policy
(`Pipeline::with_proof_grade_aarch64_publication`, selected by the sealed Core,
`emit_proofs` compiles, verifying JIT validation modes and `JitConfig::verify`)
forces them to Enforce, binds every encoded edge to the recorded CFG and
refuses the ambient late-layout controls read by `loop_align` and
`post_index_late` (`pipeline::AARCH64_LATE_LAYOUT_CONTROLS`). This is a
consistency check of final bytes against final layout and recorded CFG, not a
proof of the late passes.

After the layout cross-check, every AArch64 encode runs
`trust_cg_verify::aarch64_switch_binding` over the same final image. It
decodes the dispatch words itself (bit extraction only) and follows register
dataflow backwards inside the dispatch block, where an intervening word
clobbers a register when either the decoded word or the machine-IR def model
writes it: the `BR` register must be the `ADD` of this dispatch's `ADR` base
and its `LDRSW [Xbase, Xindex, LSL #2]` entry, the `CMP/B.HI` bounds check
must cover exactly the table and land on the successor outside it, the index
compared and the index loaded must have one origin (followed through 64-bit
register copies and through `SPILL_SLOT_ACCESS`-flagged reloads of a
frame-pointer-based slot that nothing in between can write), a non-zero `min_val`
must be the `SUB` that origin performs, every table entry must land on its
recorded successor, every `CMP` whose flags reach a `B.cond` binds its
register, width, constant (immediate or MOVZ/MOVK chain), condition and
displacement, fused `CBZ/CBNZ/TBZ/TBNZ` bind register, bit and
displacement, and a `BR` that ends no bound jump-table dispatch is refused.
A refusal is `PipelineError::Aarch64SwitchBinding` on every
pipeline route and `LowerError::SwitchBinding` on the two `lower` routes (the
relaxing route after its relaxed layout cross-check, and
`lower::encode_function`, which has none); neither `lower` route appends jump
tables, so a jump-table dispatch is refused there. The check binds bytes to
the final intent and CFG, group by group; the source case-to-block map is the
ISel normalization gate's obligation.

also run a trust-cg-verify word-level obligation (`x86_encoding_proofs`,
`aarch64_value_decode_proofs`) on the bytes they just emitted. Because
trust-cg-verify cannot depend on the encoder, its opcode-coverage credits for
those families rest on captured encoder output that test targets re-derive
from the live encoder. The half-precision FCVT forms use the same lane; their
bit-level semantics — an Arm `FPConvert` transcription and an independent IEEE
`convertFormat` statement — live in `aarch64_fcvt_half`.

`ieee754_reference` is a third statement of the scalar FP semantics, used
only by tests (ledger `L04-P3`): binary16/32/64 arithmetic, rounding and
conversions as exact integer arithmetic plus one rounding routine, under the
Arm default-FPCR NaN, tininess and flag rules, sharing no code with
`fp_bitmodel`, `aarch64_fcvt_half` or the SMT evaluator. Two native test
targets compare it with the instructions executed on the host CPU, with the
verifier's machine-side models and with TrustIR lowerings compiled on the AOT
and JIT routes; `fp_ieee_evidence` names those results, and the coverage gate
appends that name to the scalar FP rows' notes without changing any row's
class or finding.

The AArch64 pipeline also relates the lowered source to the final machine
stream as a whole for one property: after branch resolution, every function
compiled from a lowered source (each preparation and the one-shot
`compile_to_object` route) projects both onto their volatile loads and stores
and decides, with `trust-cg-verify`'s `volatile_access_preservation`, that
each path performs the same volatile accesses in the same order. The machine
side reads the block successor metadata (checked against branch operands at
the symbolic CFG authority boundary, not re-derived from the resolved words)
plus exception call-site edges; a mismatch or an undecidable pair fails the
compile. Prebuilt-MachIR routes (`compile_ir_function`, `prepare_ir_function`)
have no lowered source and make no such decision.

Object emission's optional AArch64 ISA admission is the target contract
(`AArch64IsaProfile::for_aot_target`) unless `CompilerConfig::aarch64_isa_profile`
names a profile explicitly. The explicit profile reaches the pipeline's target
machine and is recorded in the compile policy, the artifact-cache identity and
the compile service's target descriptor; in-process JIT compilation refuses it
and keeps host-detected admission. A function's own trust-ir
`target_features` extend that admission for the function alone
(`TargetMachine::for_function`, bounded by the target's function ceiling):
selection, the optimizer's feature knobs and the output-feature checks read the
function's machine, the module evidence admits the profile plus the stated
union, and the raw JIT refuses a stated feature the executing CPU lacks and
records the stated features on the buffer for its serialized target contract.
[`aarch64_dispatch`](crates/trust-cg-codegen/src/aarch64_dispatch.rs) owns the
host feature resolution (Darwin `hw.optional.arm.*` sysctls) and the run-time
choice among feature-gated variants and a baseline.

The representations at instruction selection, optimization, and allocation are
related but distinct. Adapters translate their operand and def/use conventions;
moving a transform across a boundary requires preserving those conventions.
The optimizer shares selected analyses and rewrite infrastructure across targets,
while target instruction models and ABI decisions remain explicit.

The two SAT benchmark drivers share a
[measurement boundary](crates/trust-cg-sat-host/src/bin/common/sat_measurement.rs)
for mode selection/restoration, each repetition's verdict, and exact telemetry
deltas. Workload preparation remains outside timing. Memory-only lanes disable
the provider's disk tier; disk experiments use an owned temporary directory,
an actual I/O control, and checked priming. These are measurement controls, not
solver correctness proofs or automatic eligibility for performance headlines.

The optimizer's [`AnalysisCache`](crates/trust-cg-opt/src/pass_manager.rs)
compares the exact entry, block order/domain, and predecessor/successor lists
before serving dominator or loop analyses. Equivalent graph snapshots can share
results; unrelated instruction or function-name edits do not force recomputation.
The driver's CFG hash is an early invalidation hint, not cache-hit authority.
Returned analyses describe the snapshot at lookup; they do not update themselves
after a caller mutates the function. This freshness check is separate from
validating that CFG metadata agrees with branch instructions.

Every pass-manager driver records, per scheduled pass, both its runs and the
runs that reported a change (`PassStats::changed_runs`). AArch64 function
preparation surfaces the latter as
`PreparationMetrics::optimization_pass_changes`, so a native gate can require
that the pass it exercises actually rewrote the function (the `mac-reg-block`
differential does). A change count is observability, not evidence that the
rewrite preserved semantics.

[Per-pass translation validation](crates/trust-cg-opt/src/pass_validation/mod.rs)
is that evidence for the passes it covers. Every pass-manager driver captures
what a pass's validator needs before the run and checks the run after it:
the list schedulers (in the optimizer and the codegen pipeline's final
scheduling) by dependence preservation, `mem-pair-formation` and the three
if-conversion passes by symbolic equivalence of each changed acyclic
single-entry region, and `licm` by its code-motion side conditions; a
covered run that reports no change is checked unchanged (every run is, only
under the `all` scope). The checks read the two
functions only (an instruction-derived CFG, never the pass's own analyses or
the `preds`/`succs` lists) and share the operand-role and memory-effect
tables with the passes. The optimizer records verdicts in
`PassStats::pass_validation`; the codegen pipeline decides what runs and
what a failure does (`Pipeline::pass_validation_config`), decided from the
summary's exact per-pass counters. The default runs
only the schedulers' validator, as a diagnostic (it needs no copy of the
function): it refuses nothing, prints a `trust-cg: warning:` line for each
refuted or unproved run, and hands the merged verdicts to the caller in
`CompilationMetrics::pass_validation`. Proof-grade publication and certified
pass execution run every dedicated validator and refuse a refuted or
unproved covered run with `PipelineError::PassValidationFailed`, and
certified execution adds one certified-pass-chain record per validated pass
(inside the chain's existing `lean5` checker envelope; the record's
`local_checker.kind` names the translation validation). Changed runs of
every other pass, of the extended loop rotation that runs outside the pass
manager, of the post-allocation branch layout and of the opt-in CEGIS
superoptimizer are recorded as uncovered; only `require-coverage` refuses
them. A verdict is translation validation under the validators' model, not
a proof of the pass.

AArch64 load motion and dominated-check folding share one boundary: the
machine function's own stack slots. LICM may execute a loop-invariant load
before the loop even when the loop could exit first, but only a load whose
address it resolves to bytes inside one fixed-size slot, because the frame is
mapped for the whole activation; any other address still needs a load that
runs on every iteration. Every hoisted instruction lands at the end of the
preheader, after each store, call and mid-block trap guard there, so a
hoisted load reads the memory state the loop is entered with; the
value-stability tiers only examine writers inside the loop.
aarch64-bounds-check-elim then reads two plain loads
of the same bytes, in one block with no write between, as one value when it
matches an explicit `cmp; b.hs` bounds check against a dominating loop guard.
Both transforms run on every AArch64 O2/O3 route, proof-grade ones included,
like the other structural passes; they remove or move instructions without
introducing an opcode, and each has a disable-list key (`licmframespec`,
`bcetrapbranch`) for its native on/off differential.

Extended-register address folding binds the shared dominator/loop pair lazily
for its immutable recognition phase. This checks freshness once per invocation
that needs graph analysis, not once per candidate. The snapshot is released
before applying plans; standalone pass entry points supply their own cache.

Thirteen active NEON vectorizers—fill, bit reversal, stencil, butterfly, iota-fill,
FP reduction, integer reduction, min/max, predicated sums, integer maps,
FP maps/counts, FP array reductions/iota fills and integer-array reductions—use the private
[`candidate` boundary](crates/trust-cg-opt/src/candidate.rs).
It owns whole-function candidate publication, checked instruction emission,
unique instruction/layout anchors and entry-edge splicing. Allocation or
construction refusal discards the candidate; recognition remains pass-owned.
Integer reduction's induction-term and memory-chain paths share this boundary.
Its optional shared-multiply recognizer is read-only; emission failure aborts
the candidate instead of being interpreted as an absent optimization pattern.
Min/max includes scalar-value reduction, paired value/index tracking, and
forward-chain diamonds; predicated sums include strict and widening/ordinary
chain paths. Argmin/argmax checks its lane-drained scalar remainder before
construction, so repeated pass iterations cannot keep vectorizing that tail.
Integer-map runtime alias checks and FP-map main/vector-tail loops share the
same publication boundary. Integer MLA recognition is read-only; construction
failure cannot select the generic fallback after partial lowering.
Integer-array construction covers all five builders: ordinary i32/i64,
widening dot, absolute value and byte/halfword reductions. Optional DotProd
constants and invariant broadcasts propagate construction failures rather than
treating them as absent patterns. DotProd stays explicitly target-gated;
successful before/after IR comparisons check construction preservation, not
the semantics of the original vectorization algorithms.
Subsequent native checks exposed entry/domain errors. The recognized shape now
carries unsigned index ordering separately from accumulator width and element
signedness. i64 guards use that ordering; i32 lowering admits wider indices only
when they fit its address domain. A precheck routes rejected domains and rotated
starts at/past the bound directly to scalar entry, not through the vector drain.
Strict top-tested recognition also validates the entire bypassed entry guard
against its latch, rejecting different conditions/bounds and hidden effects.
Bound recognition retains the compared register instead of substituting a
widening source: machine IR permits the source to be reassigned after capture.
Lane width is selected independently of the bound producer. Before a 64-bit
comparison enters the i32 lane/address path, both index and bound must agree
with their sign-extended low words; an X comparison reading a W-defined bound
requires a nonnegative low word. A W comparison uses only the low word of its
bound. These checks preserve scalar entry on refusal and read reconstructed
constants from their fresh preheader materializations, not in-loop registers.
The bounded native suite uses an independent wrapping-arithmetic C reference,
scalar controls and a post-pass vector-iteration observer across all five builders.
FP array reductions and fills also use checked emission and publication, including
the ordered scalar drain and all-pairs store disjointness chain. Fill ranges start
at `base + initial_iv*4`, not the bare base; the latter misses overlap for negative
indices. One post-increment pointer cannot represent repeated stores to the same
base, so that shape is declined. In-loop FP negation also stays scalar until an
exact vector lowering exists; zero-minus-value does not preserve signed zero/NaNs.
The scalar remainder also depends on correct instruction widths: the AArch64
encoder's shared integer/FP conversion helper selects W/X from the integer
source for SCVTF/UCVTF and the integer destination for FCVTZS/FCVTZU. It validates
register files, excludes SP, and requires exactly two operands; existing scalar
V-as-D spellings remain supported. Platform-assembler word checks and bounded
native fill controls cover this seam separately from the IR guard tests.
The conditional-store structural builder also uses this boundary, but public
execution remains inert pending typed writable/single-owner range authority.
Candidate construction cannot supply or bypass that missing memory authority.
`MachFunction::try_sync_vreg_counter` synchronizes the register counter
once against arena operands (including detached instructions) and noalias
parameter identities, then `try_alloc_vreg` issues checked IDs without walking
numeric gaps. Checked instruction, block and stack-slot append APIs reject
indices outside u32 without narrowing. They check identity capacity, not memory
availability or arbitrary IR validity; public operand mutation requires another
freshness scan. At a pass boundary the candidate commit first admits the
function itself (L10-P5, below), so this synchronization only ever covers IDs
the pass itself wrote. A candidate refusal leaves all input state unchanged. Cloning has a
per-candidate cost; no fresh performance result is claimed.

The legacy infallible allocators are no longer trusted to be fresh by
convention (L10-P5). `MachFunction::admit_id_counters`
([`id_admission`](crates/trust-cg-ir/src/id_admission.rs)) re-derives every
register, instruction, block, stack-slot and jump-table identity the function
references (detached instructions, noalias parameters, CFG edges and layout,
jump-table and EH blocks, the stack-limit overflow block, the
instruction-keyed sidecars and trap-expansion records, the protector and
debug slots) and refuses a live
ID at or above the counter that issues its domain's next ID
(`[TCG-MIR-STALE-ID-COUNTER]`) or an exhausted domain
(`[TCG-MIR-ID-EXHAUSTED]`). It runs eagerly where a function changes hands
(the instruction-selection exit, the optimization entry, the pass manager's
entry and exit, the post-convergence rotation's exit, register allocation's
entry and branch resolution's entry) and, in between, at the moment it is
needed: each optimizer pass entry marks the function and the pass's first
allocation of any kind re-derives before issuing an ID; CEGIS, the codegen
scheduler, the post-allocation rewrites after the rebuild and frame lowering
are marked the same way; frame insertion, which numbers its prologue and
epilogue instructions and blocks from the arena lengths in a staged plan, runs
that admission before it plans, and AOT profile instrumentation admits the
function before it numbers its counter registers. A refusal is sticky, stops the
pipeline and is reported as `PipelineError::MachIdAdmission`, naming the
boundary. The allocators themselves saturate at the `u32::MAX` sentinel
instead of wrapping or narrowing. So no allocator issues an ID inside a pass
from a counter that was not re-derived after the pass began, and the next
eager re-derivation refuses an ID written at or above a counter that nothing
raised past it. The passes that number IDs before they can mutate the function
allocate the planned range through the counter before any operand names one:
SROA numbers its shadow registers while it analyses the function, then takes
exactly that range from `MachFunction::try_alloc_vreg_range`, which re-derives
first (it used to raise the counter past its own numbering at the end, which
hid a counter left stale before it). The candidate rewrites (`neon-map`,
`neon-array`, `neon-predsum`, built on a private copy) admit the function itself
before the copy is synchronized, so the synchronization cannot repair a stale
counter into an accepted one; `xorshift-pair-fusion`, which synchronizes the
function's own counter before its two allocations, admits the function first
for the same reason. The machine inliner, the one pass that splices a
foreign body, plans the splice under the callee's own admission and checked
arithmetic and declines otherwise. Scanning at the first allocation rather
than at every boundary keeps the compile corpus byte-identical at +0.27% to
+0.34% instructions retired on the JIT lanes and within measurement noise
(pooled +0.04% to +0.09%) on the AOT lanes against `a7ce025ee`, where a full
scan after every pass cost 2.0-3.0%.
What remains: within one pass, an ID written by hand after that pass's first
allocation and later issued by the same pass is indistinguishable from
deliberate reuse, so allocator-only creation of new IDs is still a code
property. The freshness property test checks on generated and corpus functions
that every new register lies in the range the counter advanced over during its
pass, which a pass that numbers by hand and raises the counter itself would
also satisfy; the stale-counter controls (far and near-miss counters before
each allocating pass on fixtures and, at O2, on the corpus) are what catch that
pattern. Provenance maps beside the function are not admitted. The x86-64 path
is outside the admission: its passes run on `X86ISelFunction`, whose
`PassStats::id_admission` is always `Ok`, and several x86 passes (`x86_sroa`,
`x86_vectorize`, `x86_licm`, `x86_rotate`, `x86_strength_reduce`,
`x86_if_convert`, `x86_cmov_swap`) still number registers by hand from
`next_vreg`.

AArch64 frame lowering separates red-zone support from an explicit zero-storage
leaf policy. Linux can omit an otherwise empty FP/LR frame for audited leaves
without slots, outgoing storage, calls, required stack guards, dynamic allocation, exception
metadata or preserved-register dependencies. The check covers implicit registers
and W aliases, permits LR only for ordinary return, and retains a frame for
unknown or opaque operations. Add/subtract/immediate-shift forms retain their
frame because their existing source-bound Formal evidence owns that exact frame
envelope; omitting it would lose supported arithmetic proof exports. A
returning leaf built only from constants, copies, compares, conditional selects
and branches also keeps the envelope, which binds its complete source/return
relation. Both envelopes are kept only for a function whose LIR source that
owner can judge (`source_admits_frame_owner`, the owner's own applicability
check). A leaf whose source lies outside the owner's chain/diamond affine
domain (a multiply, load or store, for example) earns nothing through the
envelope and gets the ordinary zero-storage audit; raw machine callers
without a source keep the envelope. General frameless body authority remains separate work. Linux gains no red zone; the legacy frame APIs
keep their existing behavior. Darwin keeps its red zone in ordinary compiles
(Mach-O omits these frames through it without consulting the audit), and a
proof-required or verifying compile has no red zone and takes this
zero-storage policy, including the owner-applicability choice, instead. Empty saved-register
epilogues return without touching SP, with ELF CFI retaining CFA=SP+0.
The [native qualification](reports/perf/2026-09-20-linux-zero-storage-leaves/README.md)
includes the actual Rust O1 five-word writer; this does not add proof authority
or establish source-to-native memory refinement.
The [bounded-guard extension](reports/perf/2026-09-20-zero-storage-bounds/README.md)
also admits exact immediate bounds guards over volatile X0–X15 operands. Their
late expansion uses only compare/branch/trap and reserved scratch X16; other
carrier shapes keep the frame. The actual O0 writer now compiles and executes
with backend checks enabled, alongside the O1 writer and fixed-array accesses.
The [direct-address extension](reports/perf/2026-09-20-global-address-leaves/README.md)
also admits exact ADRP/ADD-low-offset shapes with nonempty symbol operands and
volatile X0–X15 registers. Other symbol-bearing operations, GOT/TLS forms and
malformed shapes keep their frames. The existing instruction/relocation proof
checks remain unchanged; actual address-return leaves pass native ABI and CFI
checks without claiming complete source/native composition.

The [emitted-layout frame repair](reports/perf/2026-09-20-emitted-frame-effects/README.md)
calculates production frame effects from the structurally validated emitted
instruction set. Optimizers retain dead arena entries, which must not keep
removed calls or register effects alive in frame calculation. Entry/order,
unique instruction ownership, symbolic CFG edges, jump tables and EH references
are checked before excluding any arena slot. Outgoing arguments, callee-save
and call effects, dynamic allocation, FP dependencies and zero-storage checks
share that immutable view. Declared slots and EH metadata remain conservative;
public compatibility queries preserve their whole-arena behavior. The six live
arithmetic frame owners remain unchanged.

Saturating float-to-i128/u128 conversions compare the original operand with
explicit destination bounds and detect NaN. Raw conversion helpers receive a
finite in-range operand; result selection supplies zero or the destination
bound for exceptional inputs. The backend therefore does not rely on a
platform runtime helper's out-of-range behavior. Return-only machine bodies
with value results retain their frame while proof-required JIT identity
certificates depend on the checked frame envelope. The
[Linux regression repairs](reports/perf/2026-09-20-linux-floor-repairs/README.md)
record the original failures and native/formal-certificate regression controls.

128-bit switch selectors never reach the 64-bit `Switch` opcode directly. The
adapter splits an `I128`/`U128` selector into its halves, groups the case
constants by high half, and emits a balanced unsigned compare tree over those
high halves whose leaves are 64-bit low-half switches sharing the default
edge; ISel then applies its ordinary jump-table, binary-search or linear
strategy to each leaf. The i128/u128 checked multiply is the low product
(`Imul I128`: `MUL; UMULH; MADD; MADD` on AArch64) plus a flag whose expansion
the adapter chooses per target (ruling OD-224): on AArch64 (and every target
but x86-64) a guarded `__udivti3`/`__divti3` division identity; on x86-64 the
division-free limb check (two `I64` `CheckedUmul`s of the cross limbs, a carry
compare against the product's high limb and a both-high-limbs test; signed:
the same core on the magnitudes plus a sign check), which calls no routine.
`trust-cg-verify/src/checked_mul_i128_proofs.rs` owns both idioms' obligations
and credit hook; the coverage gate's `Umulh` row requires the 64-bit
checked-umul obligation and that credit together, and the hook refuses
whenever a negative control survives.

Required AArch64 stack guards use a checked reservation boundary: a fixed
eight-byte, 16-aligned slot and a frame pointer are mandatory. Preparation
allocates a missing reservation; direct frame insertion instead rejects one
before changing instructions. Invalid existing reservations are never silently
treated as disabled protection. `PipelineError::FrameLowering` preserves the
typed error through the public pipeline. Other frame-lowering edits are not
made transactional by this early admission check.

AArch64 frame lowering owns stack-clash protection (`frame.rs`, "Stack
probing"). `StaticStackProbePlan` splits a static SP adjustment into
4096-byte steps, each followed by `str xzr, [sp]`, unrolled up to four steps;
larger adjustments get a counted loop in its own block, placed after the
frame pointer is established so the FP-based CFA describes every iteration.
Runtime-sized `StackAlloc` pseudos expand into a test/step/exit loop that
probes each step and the final SP, splitting the containing block and moving
its successor edges and any EH call site to the continuation. Frame insertion
refuses a probe loop without a frame pointer and a split that would separate
a protected call from its landing pad. DWARF CFI for SP-based layouts mirrors
the unrolled sequence; FP-based frames need no rows after `add x29`. AOT,
`encode_and_emit` and the JIT share this lowering, and the source-bound frame
checker refuses any body that names SP. That checker also requires the exact
16-byte FP/LR envelope. Mach-O targets admit a red zone, so ordinary frame
layout gives a trivial Apple arm64 leaf no frame record, and such a leaf has no
source-bound frame owner and no source-bound ALU binding. A proof-grade
publication (`--emit-proofs`, a verifying JIT, a sealed-Core address-free
compile) therefore disables the red zone and keeps the zero-storage leaf
policy's envelope, in the object, host-JIT and sealed-Core paths alike.
Sealed-Core preparation takes that frame policy from its admission, not from
its pipeline builder.

The C11/Rust -> AArch64 memory-order mapping (which ordering every selected
atomic form implements) is checked on emitted words by
[`aarch64_memory_order`](crates/trust-cg-verify/src/aarch64_memory_order.rs):
its own decoder reads the A/R/L bits, exclusives, LSE and CAS forms, `LDP`/`STP`
and the `DMB` domain and type; a requirement table per operation kind and
ordering (acquire, release, SeqCst entry and exit, fence access pairs) admits
a form or refuses it by name. `aarch64_memory_order_obligations` ties it to
the selector by compiling every admitted request on three profiles at O0-O3.
It is mapping conformance, not a memory-model proof (L03-P3; see
LIMITATIONS.md).

AArch64 atomics without single-instruction LSE forms follow LLVM's
`CMP_SWAP_*` pseudo design. ISel emits one opaque LL/SC pseudo per atomic
([`trust_cg_ir::llsc`](crates/trust-cg-ir/src/llsc.rs) owns the operand
layout and checked immediates). Every register the loop writes is an explicit
def, and every def interferes with every use of the same instruction, so
allocation keeps them distinct. The shared role predicate
`has_explicit_atomic_operand_roles` gives allocation, spill materialization,
debug provenance and the post-RA reaching-definition net the same def/use
partition, including the W status def of every store-exclusive. After frame
lowering, [`llsc::expand_llsc_atomics`](crates/trust-cg-codegen/src/llsc.rs)
rewrites each pseudo in place into its exclusive retry loop. It reuses the
pseudo's instruction ID for the defining load-exclusive and re-validates
register distinctness first. Resolved-stream CFG reconstruction accepts
intra-block branches only inside the exact expanded templates
(`llsc_internal_branches`). The encoder rejects a surviving pseudo, and ENC-5
decode-checks every emitted exclusive word.

Spill materialization applies a whole-window strategy to a pseudo's spilled
operands, since the loop re-reads every use after writing every def.
Spilled uses reload into X16/X17 first. Spilled defs, and any use beyond two,
borrow an allocatable GPR that is not an operand of the pseudo. A register
that a backward physical-liveness solve over the allocated stream finds dead
after the pseudo is borrowed as is. Otherwise a live one is saved to an
emergency 8-byte slot before the reloads and restored after the def spill
stores. Every save, reload, spill store and restore is a flagged spill access
before or after the pseudo, never inside the loop.
`llsc::check_exclusive_windows` enforces this after expansion and again on the
final stream at encoding. It refuses a spill access (`[TCG-LLSC-SPILL-WINDOW]`)
or any other memory access or call (`[TCG-LLSC-WINDOW]`) between a
load-exclusive and the next store-exclusive or `CLREX` on any path.

Within register allocation, `RegAllocFunction::try_alloc_vreg` replaces its
infallible register allocator. A shared private `VRegAllocationPlan` observes
arena and caller-held identities, plans fresh IDs with checked arithmetic,
and commits the counter only on success. Phi elimination plans every
predecessor's copy sequence before emitting any; exhaustion is a required-phase
`AllocError`, not permission to continue with unlowered phis. Optional interval,
loop-reload and argument splits decline without consuming IDs on refusal.
Allocation errors now have a phase-neutral owner in `trust-cg-regalloc`; the
old `linear_scan::AllocError` path remains a re-export.

After allocation, the translation validator (`regalloc_validator.rs`) checks
value flow, vreg interference, phys-reg interference against the allocator's
reservation map, return-sink identities and spill discipline. Its gate (b''')
recomputes AArch64 physical-register liveness in
`independent_physical_liveness.rs` with separate alias keys, the AAPCS64
call-kill table and a round-robin solver, and requires every live point to be
reserved; under-reservation by the shared `physical_liveness::reserve` routine
is therefore rejected rather than trusted.

The final AArch64 stream (after spill materialization, post-RA passes, frame
lowering and branch resolution) is re-checked at encode time by three nets in
`trust-cg-verify`: the structural recheck, the register reaching-definition net
and the frame dataflow net `post_ra_spill_slots`. The last interprets the frame
from the CFA: SP and X29 heights through the prologue, probes (including the
counted probe loop), large-offset scratch addressing and every epilogue form;
byte-ranged frame cells record their possible writers (uninitialized, spill,
other, callee). Spill materialization stamps `InstFlags::SPILL_SLOT_ACCESS`,
which frame-index elimination and offset legalization preserve by rewriting
operands in place. It flags only single-register `LDR`/`STR` accesses, Q
registers (16-byte, 16-byte-aligned slots) included, and the allocator never
forms a pair spill. Before the nets run, the encoder refuses any other flagged
shape by name (`[TCG-A64-PAIR-SPILL]` for a pair, `[TCG-A64-SPILL-SHAPE]`
otherwise), which the frame net would only decline. Calls follow the AAPCS64
clobber table rather than their `implicit_defs`. Because AAPCS64 preserves
only the low halves of V8-V15, a Q-view read of one after a call that did not
redefine it is `call-clobbered-upper-half-read`. An edge into a landing pad
carries the state after the block's calls. Proof-grade transitions force the
nets to Enforce.

Those nets judge the final stream on its own. The post-allocation value-flow
comparison ([`post_ra_value_flow`](crates/trust-cg-verify/src/post_ra_value_flow.rs),
wired by [`crates/trust-cg-codegen/src/post_ra_value_flow.rs`](crates/trust-cg-codegen/src/post_ra_value_flow.rs))
judges it against the function as it entered register allocation: a
`Session` clones that function before `run_regalloc`, notes the arena length
after copy lowering (frame lowering appends after it), and after branch
resolution compares the final stream with the clone under the frame layout
(`Stage::Composed`). Blocks keep their ids through every post-allocation
stage, so a block laid out in both functions is an anchor; inserted blocks
(critical-edge, relaxation, probe and protector blocks) and bypassed
trampolines lie on paths between anchors and may hold no effect. Both
functions are executed symbolically over hash-consed terms; effects are
matched one-for-one, decisions are explored jointly over their condition
atoms, and the entry state of each anchor is a fixpoint over its incoming
edges in which an implementation register or frame cell takes a
specification value only when it holds it on every edge (or, for a 64-bit
location, a common base plus a constant multiple of one specification
value on every edge: an induction pointer), so the location relation is
inferred, not read from the allocator. 64-bit integer add, subtract and
shift-left are affine forms, and every spelling of a plain access (offset,
pre/post-index, register offset, the lo12-fused form) is compared at its
effective address. SP is an argument of every call (and, before frame
lowering, of every exit); a call leaves each caller-saved register its own
unknown and drops the frame cells below its SP; frame-storage cells are kept
private by refusing any storage access at or above the CFA, on a program
stack slot or on the outgoing stack-argument area (a stack probe excepted
only where it writes below every byte an earlier write on any path may have
touched). The comparison runs in
the dedicated and all-passes scopes (so in every proof-grade and certified
pipeline, where it refuses under `PassValidationFailed`) and is recorded as
uncovered in the default tier; `TRUST_CG_POST_RA_VALUE_FLOW_STAGES=split`
compares at the allocation and frame boundaries separately.

A function whose source requested a U10 prologue stack-limit check
(design) passes a fourth net,
[`aarch64_stack_limit`](crates/trust-cg-verify/src/aarch64_stack_limit.rs)
(`[TCG-A64-STACK-LIMIT]`), on every route. It has its own SP and
frame-address model, no diagnostic mode and no decline: it requires the
callee-saved prologue and nothing else before the check, the exact compare
sequence on the resolved limit register with every check branch ending its
block, a deepest CFA offset (SP height and every SP-, FP- or frame-derived
access) within the checked total, and an overflow block that only restores
the callee-saved area before tail-calling the declared handler, or is one
`BRK #0x534c`. The trust-ir adapter decodes the request tags
(`trust_cg_lower::stack_limit`), the pipeline resolves the limit parameter
through AAPCS64/DarwinPCS signature lowering, frame insertion emits the check
and the overflow block, and the pipeline binds the machine function's
requirement to the source LIR's before keeping the net's certificate in
`PreparationMetrics`. Compile results report each requester's certificate
summary and the module reserve bound (`StackLimitModuleReport`) as the
consumer's positive acknowledgment.

The regalloc model's `try_alloc_stack_slot` likewise replaces its infallible
slot allocator. Register and slot plans share one private checked ID cursor.
Slot planning scans existing metadata and all arena slot references once,
including unlinked instructions; it does not walk numeric gaps. Spill metadata
and generic pseudo insertion use the same deduplicated first-occurrence plan
and canonical `RegClass::size_bytes`, preventing policy/width drift. The
separately exported call-save helper also plans every slot before committing.
Both insertion helpers now return `Result`; `StackSlotExhausted` leaves the
helper's input unchanged. The complete allocator propagates required spill
errors but need not roll back earlier phases. Frame size/alignment admission
remains a separate boundary; the canonical machine-IR allocators' freshness,
references past an arena and arena-index narrowing are covered by the L10-P5
identity admission above, which refuses rather than repairs them.

Dialect structure admission now lives with `DialectFunction`, shared by
conversion, legality checks and direct machine-facade emission. It checks
layout, unique definitions and reference existence, ignoring unplaced arena
entries; it is not a dominance verifier. Conversion keeps source and destination
IDs separate: both copy-through and pattern paths require mapped operands,
and rebuilt structure is checked before replacing that function. Failure does
not roll back earlier functions in a module. Forward operation-result uses are
not scheduled/retried; they return `UnmappedValue` instead of aliasing a numeric
destination ID. Block parameters remain pre-mapped across blocks.

The direct `machir` facade separately checks definition order, canonical opcode
types, return shape and function-index admission, then emits into a private
machine function with checked register and instruction IDs. It accepts one
block without block arguments/references, I64 parameters and a void or I64
return. Entry copies preserve unread X0–X7 inputs; later parameters use the
canonical incoming-stack-argument operand. A value return explicitly writes X0
before RET, and full-width literals expand into legal MOVZ/MOVK halfwords.
Allocation, frame lowering and encoding remain owned by the normal downstream
components. Emitted-byte interpreter and bounded macOS ARM64 native controls
exercise this subset. Multi-block conversion is distinct from multi-block
machine emission; floating-point, aggregate and other ABI types are not admitted.

## Policy and evidence

The AArch64 pipeline delegates AOT counter insertion to the private
[`aot_profile` phase](crates/trust-cg-codegen/src/aot_profile.rs). It validates
layout and dense, unique counter metadata, reserves register/instruction IDs,
and plans every block before committing code and metadata under one map lock.
Fresh register IDs account for all arena operands, including unlinked
instructions, and noalias parameters. Poison, malformed layout and exhaustion
return typed errors without changing either input to this phase; this is not
a full CFG/SSA verifier or allocation-failure rollback guarantee.

Both LIR and prebuilt machine-IR compile/preparation routes invoke that phase
after their existing verification and before register allocation. A
profile-generation batch validates its execution budget, then prepares in
input order so counter slots and emitted bytes match serial preparation.
Ordinary batches keep their parallel path. Independently concurrent calls
receive disjoint contiguous site groups, with no inter-call ordering promise.
Earlier pipeline phases/functions are not rolled back on a later error.
The caller still supplies the counter globals/runtime; increments are
non-atomic, wrapping u64 operations, not proof authority. Serialization may
cost throughput; no new performance measurement is claimed.

Compilation policy, deterministic search limits, executor resources, and
wall-clock cancellation have different effects. Artifact-affecting decisions
belong in the captured compilation policy and cache identity. Resource limits
bound execution; a timeout cannot become a successful proof or a partial
published artifact. See [`compile_policy.rs`](crates/trust-cg-codegen/src/compile_policy.rs),
[`resource_limits.rs`](crates/trust-cg-codegen/src/resource_limits.rs), and
[`compile_artifact_cache_profile.rs`](crates/trust-cg-codegen/src/compile_artifact_cache_profile.rs).

JIT tier-up ([`tier_up.rs`](crates/trust-cg-codegen/src/tier_up.rs); design
and plan in docs/jit-tier-up.md) schedules one source at
several optimization levels without changing any of them: every tier is an
ordinary compile-service request derived from the caller's (same generation,
fence, proof policy and manifest), is byte-identical to a plain compile of that
request, and is delivered only while fresh, from tier 0's source, with tier 0's
callable surface. A refused tier never disturbs the installed one; entry tables
keep every installed tier's code mapped for their lifetime.

Evidence is checked at several boundaries: input and carrier admission,
transform/translation validation, allocation, opcode modeling, encoding,
relocation, and JIT publication. JIT publication also records the mapping's
page-protection and allocation state in the installed payload binding and
executable manifest, and enforces the declared teardown policy through execution
leases. On Linux that record pairs the recorded permissions with the kernel's
view of the allocation through `/proc/self/maps`
([`jit_page_witness.rs`](crates/trust-cg-codegen/src/jit_page_witness.rs)).
Three installed routes observe the kernel again before exposing a callable:
`get_contract_symbol_bound`, `native_install_gate_packet(_for_surface)` and
`into_installed_artifact`; raw installed and buffer lookups are not
re-checked. A JIT module's data globals live in a separate read-write data image
whose manifest is part of the buffer's identity; no proof obligation covers
it, so verifying requests refuse data and GOT sites by name. These gates
cover different subsets. A valid
statistical evaluator result, a solver result, and independently replayed
evidence establish different claims; a serializer or a cache hit must preserve
that distinction. [LIMITATIONS.md](LIMITATIONS.md) describes the actual
supported envelope and [SOUNDNESS_CHECK.md](SOUNDNESS_CHECK.md) names the broad
cross-repository gate.

Library report emission and certified CLI export apply the same promotion
rule: every unverified report blocks, and statistical evaluator results and
registry theorems selected by name are reported as unverified rather than
credited. Verifying JIT modes additionally require non-vacuous per-function
evidence; x86 admission uses the same per-function verdict it reports. AArch64 additionally checks its bytes-bound
machine-IR certificate. Neither opcode-inventory coverage nor a replayable
certificate alone establishes function semantics. These gates do not supply
missing exact source provenance or make statistical evidence formal.

Sealed Core address-free compilation retains source custody through the same
`FunctionSourceModules` and captured verifier-request interfaces used by ordinary
AArch64 compilation. Its identity transform borrows the exact admitted module
at both endpoints, captures its lossless identity once per module, and reuses
one explicit `Enforce` request across function workers. Report receipts and
machine-certificate input identities bind these same endpoints alongside the
retained LIR and final MachIR; a legacy LIR-only receipt cannot match. Existing
arithmetic exports come from that same traversal, but their payload identity
still binds the exact LIR/MachIR and query, not the original module pair.
This adds one module identity capture per attempt without a graph clone,
not zero overhead or new frame/call proof coverage. Missing wire images and
unproved machine instructions remain refusals. Source contract custody does
not establish that provider implementations satisfy those contracts.

A separate consuming continuation, `compile_for_installation`, keeps the exact
moved Core/LIR beside the address-free artifact. It replays the existing
source-island certificate and default body-license requirements, then
`CoreInstallationArtifact::install` reaches the same mapping/seal/readback
publisher, installed-payload binding and native-install gate as existing shared
JIT owners. Its result is the existing `InstalledArtifact` plus the exact final
manifest; only an absent compiler-owned native-payload digest is completed.
Wrong supplied claims still refuse. The existing manifest-backed symbol lookup
uses the actual route verdict/strength/assumptions and checked-proof bundle
digest. No raw bytes or address resolver construct this owner. The ordinary
address-free artifact still releases its source and stays noncallable.

This continuation currently publishes only on ARM64/macOS, with complete empty
import/catalog/fixup inventories and text alignment through 4096 bytes. It
rechecks actual host function features before mapping and refuses ADR/ADRP and
PC-relative literal load/prefetch classes pending an explicit placement
transport, including conservative false refusals on data. Direct relative
branches must stay inside the same function. An unsupported inventory
is preserved and refused, including unused imports; no provider implementation
is inferred from a typed import. The independently authored source literal42
executes through the checked owner; the original E1 body/frame/provider
obligations and zero-artifact refusal are separate. See the
source-bound Core installation record.


The separate `compile_for_owned_peer_entry` continuation retains a sealed
conditional replay of the actual source call/result, genuine callee, frame and
final BL. Its diagnostics remain Unverified until its consuming owner takes real
private RW stack storage. The opaque returned entry retains that exact mapping,
checks fresh source-bound invocation loans and uses the same publisher, installed
branch replay, payload gates and fixed runtime adapter. No generic caller
artifact or ordinary export escapes the pending requirement. See the
bounded source-peer contract
for the zero-argument scalar domain, actual framed source42, retained generic
refusals and runtime/platform TCB boundary. The
one-word forwarding extension
seals a single U64 argument, authenticates the zero-byte X0 setup and selects a
separate checked runtime adapter through the same storage owner.

## Maintaining the architecture

Test-process termination has a separate, shared
[`process_termination` boundary](crates/trust-cg-codegen/tests/common/process_termination.rs):
request a kill, perform one nonblocking exit poll, and retain kill/poll errors
and any observed status. Both codegen runners use it; five EH adapters and the
LLDB fixture delegate to the shared direct-command runner. Direct-child signal
statuses remain distinct from the executable runner's Unix shell convention.
The deterministic process model tests delayed/failed termination without
creating an unkillable child. Native shell controls exercise the actual
adapters, not compiler-generated EH or a debugger. This is test infrastructure,
not proof authority or a repository-wide subprocess migration. The verification
runner described above has a separate production ownership/capture contract;
remaining solver/checker and other harness supervisors still require review.

Native AArch64 test fixtures select their host through one helper,
[`native_host`](crates/trust-cg-codegen/tests/common/native_host.rs): the
triple, object container check, independent ELF/Mach-O code reader, link
flags and a fail-closed GNU-to-Apple assembly translation whose Linux arm is
the identity. Explicit-profile compilation there admits optional ISA features
only for tests; it is not generic AOT admission.

Keep shared machine semantics in `trust-cg-ir`, and put target-dependent ABI or
instruction behavior beside the target's implementation. Prefer extracting a
coherent analysis or policy boundary over adding more orchestration to the
large compiler, pipeline, adapter, and rustc-bridge modules. Preserve the
admission checks and independent regression oracles when extracting code.
