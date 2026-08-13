# trust-cg vision

This document describes the direction of travel, not the guarantees of v0.1.0.
For current behavior and trust boundaries, use the top-level
[`README`](README.md) and [`LIMITATIONS`](LIMITATIONS.md).

## Goal

trust-cg aims to make code generation an inspectable, proof-aware stage of a
larger compilation chain:

```text
source language
      │
      ▼
proof-carrying trust-ir
      │
      ▼
validate → lower → optimize → allocate → encode
      │                                  │
      └──────── evidence ────────────────┘
                         │
                         ▼
               native code + audit trail
```

The long-term target is a compositional argument connecting source semantics,
trust-ir, each admitted backend transformation, object/link behavior, and the
executed machine program. Missing evidence should keep a transformation or
publication path fail-closed.

## Design principles

- Keep source, target, and evidence identities explicit.
- Distinguish exhaustive checks, statistical testing, solver proofs, and
  independently replayed certificates.
- Make unsupported opcodes, ABI cases, relocations, and proof gaps visible.
- Preserve enough provenance to audit a compilation after the fact.
- Prefer small, reviewable semantic surfaces over an opaque general-purpose
  backend contract.
- Connect model-level theorems to the production emitter and runtime rather
  than assuming that correspondence.

## What remains

Reaching the goal requires substantially more than per-rule SMT obligations.
Among other work, the project must complete:

- trust-ir semantic and transport coverage;
- target ABI, aggregate, relocation, TLS, unwind, atomic, and vector coverage;
- faithful models and production bindings for every emitted instruction/byte;
- pass- and whole-function composition;
- cross-function and whole-program reasoning;
- certificate generation and independent replay on every claimed path;
- robust differential validation across targets and operating systems.

v0.1.0 implements useful pieces of this architecture, but does not provide an
unbroken source-to-binary proof or a binary with no trust assumptions.
