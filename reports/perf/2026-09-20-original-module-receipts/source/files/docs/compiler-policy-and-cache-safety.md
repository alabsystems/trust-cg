# Compiler policy and artifact-cache safety

Trust Codegen's reusable native artifacts must be functions of explicit,
canonical inputs. That rule applies to every frontend: Rust, TLA+, LLVM IR,
ONNX, and future source languages.

## Current boundary

`CompileArtifactCacheKey` binds source and lowered TrustIR, explicit
`CompilerConfig`, profile-use input, target facts, proof policy, and dependency
identity. Legacy compiler environment controls are not part of that explicit
configuration. Many `TCG_*` and `TRUST_CG_*` variables change lowering,
optimization, register allocation, proof behavior, or final layout, so reusing
an object while one is active can select bytes compiled under a different
policy.

`trust-cg-process-env` exposes the frontend-neutral
`artifact_reuse_environment_safety` diagnostic API and the transactional
`artifact_reuse_permit` API. They inspect both the raw process environment and
the effective thread-local override view. The immutable raw environment's
blocker names are captured once; an ordinary safe JIT L1 hit then checks only
an empty/tiny override stack and allocates nothing. Reuse is allowed only when
no unkeyed `TCG_*` or `TRUST_CG_*` variable is present. Empty values still
count because legacy switches commonly test presence. Unknown future names
fail closed automatically.

A permit also captures a per-thread compiler-control mutation epoch. Every
unkeyed reserved-control push or removal advances that epoch, so a short-lived
override wholly inside a builder permanently invalidates its original permit
even though the environment looks safe again afterward. Cache clients carry
one permit from lookup through publication; pre/post snapshots alone are not a
sufficient temporal guarantee.

The only exact-name exemptions are cache transport controls and the dependency
identity variables already represented in the canonical object key. There are
no wildcard exemptions. Trust Codegen's production object cache applies this
guard before constructing a lookup context and checks it again before
publication. JIT matrix caching applies the same rule to in-memory compiled
providers, the quarantined executable-buffer tier, and persisted TrustIR:
semantic IR is still builder output, so unknown future controls cannot be
assumed irrelevant to it.

Persistent object reuse also requires source-lock identities for TrustCG,
TrustIR, and AY plus pinned rustc/Cargo identities under every proof policy.
The unchecked policy relaxes proof-bundle admission only; package-version and
build-environment identity defaults now make the production cache context
ineligible rather than allowing replay across same-version source revisions.
Likewise, selecting a proof-bearing cache partition does not silently enable
proof generation. If the compile request did not explicitly enable proofs, the
proof-bearing cache tier is bypassed and compilation behavior is unchanged.

A frontend with its own machine-code cache should apply the same necessary
condition at lookup and publication:

```rust
let permit = trust_cg_codegen::artifact_reuse_permit();
if let Some(permit) = permit.as_ref() {
    // Cache lookup is allowed here.
}
let artifact = compile();
if permit.as_ref().is_some_and(|permit| permit.is_valid()) {
    // Publishing this transaction's artifact is allowed here.
}
```

This guard is not artifact authentication and does not replace the rest of the
cache key. Callers still bind source, target, explicit options, backend and
dependency revision, proof/install policy, frontend-specific controls, and
artifact integrity.

AArch64 compiler verification retains both the caller's original TrustIR module
and the module consumed by the adapter after dialect lowering. Borrowed
`FunctionSourceModules` computes their exact binary identities once per boundary,
including declarations, type tables and floating-point payload bits. A captured
function report binds that pair in addition to its existing machine/LIR and
request identities. A source-bearing report refuses the legacy LIR-only input
matcher. The compiler JIT includes the module pair in its certificate cache key
and checks the retained receipt before reuse; unchanged machine code and LIR
cannot conceal a changed original declaration. Standalone raw-MachIR diagnostics
retain their distinct input identity.

This is custody and cache attribution. It does not prove dialect lowering,
original-source correspondence, callback memory contracts or emitted bytes, and
does not add proof credit to a report. Those consumers must independently check
the retained source endpoints before granting their respective authority.

The compilation process must also keep its real environment immutable. Rust
2024 makes process-environment mutation unsafe on supported Unix hosts, and a
snapshot cannot recover the historical value retained by legacy `OnceLock`
option readers after an out-of-contract mutation.

## Target architecture

The fail-closed guard is a migration boundary, not the final configuration
model. The durable design is one immutable, language-neutral `CompilePolicy`
resolved once at a process/API edge and passed through every compiler phase:

1. Separate byte-affecting policy and proof/install authority from diagnostics,
   telemetry, resource limits, and cache transport.
2. Give every byte-affecting field a stable schema, canonical encoding, and
   policy digest included in every native artifact and install cache key.
3. Resolve legacy environment variables once into that policy in CLI adapters;
   library compilers must not read ambient options during lowering or codegen.
4. Pass the same policy explicitly to worker threads instead of relying on
   thread-local inheritance or process-global `OnceLock` snapshots.
5. Make proof policy and optimization authority typed fields rather than
   independently inferred switches.
6. Add a source audit that rejects new compiler environment reads outside the
   compatibility resolver.
7. Move object-cache lookup ahead of adapter, optimization, register
   allocation, and proof work. The current late lookup mostly saves emission;
   full all-program compile acceleration needs an early canonical identity and
   a replayable, validated proof/metrics receipt so a hit can safely return
   before those phases. Early replay must also require source-lock and pinned
   toolchain identity; the unchecked package-version/build-environment defaults
   are not strong enough to bypass the full pipeline.

Once those conditions hold, a nondefault policy can reuse artifacts through
its canonical digest. Until then, refusing reuse under ambient controls is the
only generalized fail-closed behavior.
