# Third-party software

trust-cg is licensed under Apache-2.0. The components below retain their own
copyright notices and licenses.

| Component | Upstream | Pinned revision | License | Use |
| --- | --- | --- | --- | --- |
| MicroSAT | [marijnheule/microsat](https://github.com/marijnheule/microsat) | `26985d9b6b9aa5375d345051bd98afd63213043d` | MIT | SAT-Comp host solver and native BCP reference. |
| drat-trim | [marijnheule/drat-trim](https://github.com/marijnheule/drat-trim) | `2e3b2dc0ecf938addbd779d42877b6ed69d9a985` | MIT | Independent DRAT proof replay for selected certificate paths. |
| Kissat | [arminbiere/kissat](https://github.com/arminbiere/kissat) | `8af8e56f174b778aef3aa45af9f739b2a5f492c2` | MIT | Benchmark/reference solver tooling; not linked into the main `trust-cg` binary. |
| xxHash | [Cyan4973/xxHash](https://github.com/Cyan4973/xxHash) | `v0.8.2` | BSD-2-Clause | XXH3 algorithm, constants, default secret, and reference vectors used by codegen tests. |
| Rust standard library | [rust-lang/rust](https://github.com/rust-lang/rust) | `1.97.1` | MIT OR Apache-2.0 | SipHasher13-derived transcription and semantic rewrite used by a codegen slice. |

The build-required MicroSAT and drat-trim sources and their complete license
texts are preserved under `third_party/vendor/`. Kissat is fetched on demand by
`scripts/fetch-kissat.sh`; its license is retained under
`third_party/vendor/kissat/` even when its source checkout is absent. Every
snapshot is attributable to the exact revision above.

The xxHash-derived test material retains its upstream notice in
`third_party/vendor/xxhash-LICENSE` and identifies the mixed-license portions
in each affected source file.

The SipHasher13-derived slice elects the Rust project's MIT terms and retains
them in `third_party/vendor/rust-stdlib-SipHasher13-LICENSE`; its affected
source and integration-test files identify that provenance explicitly.

The SAT fixture corpus under
`crates/trust-cg-sat-host/tests/fixtures/sat_corpus/` is generated entirely
from project-authored Apache-2.0 code. It redistributes no SATLIB or AIM
instances. Eleven historical `uuf*`, `uf*`, and `aim*` filenames remain only
as compatibility identifiers; `generators.py` deterministically produces
their current contents from documented seeds or textbook encodings.

Rust dependencies are resolved by Cargo and recorded in `Cargo.lock`. Each
dependency remains under the terms declared by its upstream package; inclusion
in the dependency graph does not relicense it under Apache-2.0. Use tooling
such as `cargo metadata` and `cargo deny list` when producing a distribution to
generate the complete build-specific dependency and license inventory.

No third-party trademark rights are granted by this repository.
