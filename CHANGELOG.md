# Changelog

All notable public changes to trust-cg are recorded here. The project follows
[Semantic Versioning](https://semver.org/) for release identifiers, while the
0.x APIs and file formats remain unstable.

## [0.1.0] - Unreleased

Initial research-preview source release.

### Included

- AArch64 and x86-64 compiler backends with AOT object emission and JIT paths.
- Experimental RISC-V 64 lowering and encoding.
- Binary tMBC input plus text and JSON debugging formats.
- Proof obligations, evaluator and solver-backed verification lanes,
  strict `tcg-lrat-cert-v2` canary certificates, structured proof artifacts,
  and fail-closed proof-required compilation.
- Differential, triple-oracle, fuzz, target, object, and soundness test
  infrastructure.
- The SAT-Competition 2026 trust-cg-sat experiment and reproducible benchmark
  material.
- A source-only workspace distribution with exact dependency identities,
  fail-closed publication mapping, and flattened, licensed MicroSAT and
  drat-trim sources.

### Release status

This is an alpha research release, not a production compiler or full Rust
backend. See [`LIMITATIONS.md`](LIMITATIONS.md).
