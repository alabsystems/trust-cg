# Adopt shared ordered-list proof construction

2026-09-07. Base `28b118018142e105430434eb74f820061fde57e0`.
TrustIR advances from `f572adaf04f55edd6ae9e243586caebfcc3bc660` to
`dde92547f4d8d624dc7e22a0f8ba82ea642122e0`. Both workspace declarations,
the independent rustc backend declaration, both lockfiles and the default
artifact-cache TrustIR identity move together. Package versions, rosters,
Clean/AY pins, compiler policies and emitted instruction algorithms do not
change. The independent backend's nightly build is not claimed tested.

The adopted builder exposes linear ordered-list equality candidate assembly
through the same cached polymorphic cons helper used by actual operand
resolution. TrustIR's full 792-test builder suite passes; its proof candidates
still need actual-model consumer replay. This pin does not establish Rust
verification, whole-program refinement or native admission.

All final frozen pin selections passed:

| Selection | Session | Passed | Compile | Test / gate wall | Gate / sampled peak GB |
| --- | --- | --- | --- | --- | --- |
| Full all-feature lowering | 22940 | 2197 | 25.16s | library 5.72s / 40s | 4 / 1.47 |
| Native local-function JIT and callback ABI/clobber | 44383 | 6 | 37.62s | 5.05s + 0.29s / 45s | 4 / 2.19 |
| Complete artifact-cache selection | 25788 | 43 | 20.04s | 0.08s / 21s | 3 / 2.21 |

Lowering comprises 1787 library and 410 integration tests, zero doctests;
no failed or ignored tests. No full-codegen/full-workspace pass is claimed.
All use stock Rust 1.97.1, locked dependencies, two build jobs, serial tests,
no Rayon override, unset compiler wrappers, and empty Rust/rustdoc/encoded
flag overrides. These are regressions, not Trust verification of Rust.
Five-second descendant-tree samples are not unsampled maxima. A comparable
lowering repeat can reserve 3 GB; native and cache rebuilds warrant 4 GB.
Build/test times are not evidence of end-to-end compiler or TLC speedups.

Commands under the recorded environment:

```text
cargo test --locked -j2 -p trust-cg-lower --all-features -- --test-threads=1 --quiet
cargo test --locked -j2 -p trust-cg-codegen --test ty_callback_abi_call_clobber --test local_function_address_jit -- --test-threads=1 --quiet
cargo test --locked -j2 -p trust-cg-codegen --lib artifact_cache -- --test-threads=1 --quiet
```
