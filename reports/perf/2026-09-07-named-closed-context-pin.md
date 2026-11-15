# Adopt shared named-closed proof reuse

2026-09-07. Based on TrustCG `3e987672ed1f4ce30d4d046a5edd622148524598`.
All five IR pin authorities move coherently from `dde92547` to published
`3e2a0a1fd29bc23d047b95704012d991a0ad3cf4`: root manifest/lock, independent
rustc-codegen manifest/lock, and artifact-cache profile. Package rosters,
versions, Clean and AY revisions remain unchanged.

The shared build helper reuses successfully closed named terms with exact
scope-footprint checks; TrustCG does not gain a new instruction, lowering rule,
verification exemption, or native authority policy. Root and independent locks
retain three IR packages each. The separate rustc-private backend is NOT built
by these selections.

| Selection | Session | Result | Compile | Tests | Gate wall / sampled peak GB |
| --- | --- | --- | --- | --- | --- |
| Complete all-feature lower crate | 26605 | 2197 passed | 24.72s | library5.72s | 40s / 1.61 |
| Actual local function-address JIT and callback ABI | 42770 | 6 passed | 38.15s | 4.77s +0.27s | 46s / 2.13 |
| Complete artifact-cache selection | 33308 | 43 passed | 19.82s | 0.07s | 22s / 2.23 |

Lowering comprises1787 library and410 integration tests, no doctests, no failed
or ignored tests. Native comprises two3-test binaries. Cache has3518 filtered
tests; this is not the full codegen or workspace suite. Reservations were3GB,
4GB and4GB respectively. RSS is sampled descendant-tree build/test memory,
not an unsampled maximum or model-checker memory. No workload speedup or TLC/MCC
dominance is claimed.

All commands use stock Rust1.97.1, locked Git dependencies, two Cargo jobs,
serial tests, no Rayon override, unset compiler wrappers and empty Rust/rustdoc/
encoded flags. The Trust toolchain is unavailable; these checks do not verify
the Rust implementation. Reproduce under that environment and the memory gate:

```text
cargo test --locked -j2 -p trust-cg-lower --all-features -- --test-threads=1 --quiet
cargo test --locked -j2 -p trust-cg-codegen --test local_function_address_jit --test ty_callback_abi_call_clobber -- --test-threads=1 --quiet
cargo test --locked -j2 -p trust-cg-codegen --lib artifact_cache -- --test-threads=1 --quiet
```
