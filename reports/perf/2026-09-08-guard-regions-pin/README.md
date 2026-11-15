# Adopt shared immutable guard-region analysis

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

2026-09-08. Based on TrustCG `7756b9f278e7754d08dc768d901dfb6819ae9257`.
All five TrustIR authorities move together to published implementation
`cdf11325f6c4407b9aab0f74953ad46507d4192f`: root manifest/lock, independent
rustc-codegen manifest/lock, and artifact-cache profile. The three IR packages
in each lock advance from 0.13.0 to 0.14.0; the package rosters and Clean/AY
revisions are unchanged. Locked metadata for the independent workspace confirms
one revision for trust-ir, trust-ir-build and trust-ir-giveback. That separate
rustc-private backend is not built by these selections.

Shared TrustIR conditional-premise analysis now independently checks immutable
branch facts using exact edge-dominance regions. Long-lived guard facts need
not be replicated at each intervening block. This update adds no TrustCG
lowering rule, proof exemption, or native authority. The cache profile changes
with the actual dependency identity; it cannot reuse an old-IR artifact under
the new profile.

| Gate | Passed | Compile | Tests | Gated wall / sampled peak GB |
| --- | ---: | ---: | ---: | ---: |
| Complete all-feature lower crate | 2197 | 48.98s | library 5.61s | 1m04s / 2.92 |
| Actual local function-address JIT and callback ABI | 6 | 39.81s | 4.56s + 0.26s | 47s / 2.37 |
| Complete artifact-cache selection | 43 | 19.09s | 0.07s | 20s / 2.23 |

Lowering is 1787 library and 410 integration tests, no doctests. The two native
binaries have three tests each. Cache has 3518 filtered tests: this is not the
full codegen or workspace suite. No failed or ignored tests. Logs are retained
alongside this report. Reservations were 6/5/4 GB; peaks are sampled descendant
build/test memory, not model-checker RSS. No workload or TLC/MCC dominance claim.

Stock Rust 1.97.1, locked Git dependencies, two Cargo jobs, serial tests,
unset compiler wrappers, empty Rust/rustdoc/encoded flags, no Rayon override.
The existing repository default test stack remains unchanged. No Trust compiler
or Rust-verification evidence. Reproduce under that environment and the host
memory gate:

```text
cargo test --locked -j2 -p trust-cg-lower --all-features -- --test-threads=1 --quiet
cargo test --locked -j2 -p trust-cg-codegen --test local_function_address_jit --test ty_callback_abi_call_clobber -- --test-threads=1 --quiet
cargo test --locked -j2 -p trust-cg-codegen --lib artifact_cache -- --test-threads=1 --quiet
cargo metadata --locked --manifest-path crates/rustc-codegen-trust-cg/Cargo.toml --format-version 1
```
