# Adopt typed variadic dialect schemas

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Base: `0e6043a8fb024ed7b382d45a371b0b34a08abd59`.
All five TrustIR pin authorities move to published
`013543033cb5e5e0f9d32fcf10aa1bda72e9a8d0`: root manifest/lock, independent
rustc-codegen manifest/lock, and unchecked artifact-cache profile identity.
Package versions, lock rosters and Clean/AY selectors are unchanged.

The upstream change allows an exact fixed operand prefix followed by one
homogeneous typed variadic tail in registered dialect schemas. It does not
change wire instructions/types or introduce a TrustCG lowering rule, proof
exemption, variable-argument machine function ABI, or native authority.
No downstream exhaustive schema adapters require changes. Real constructor
lowering remains frontend/runtime work and must separately establish lifetime
and initialization contracts.

## Gates

All pass on the actual published Git pin, with no path patch. Stock Rust
1.97.1, two Cargo jobs, serial tests, compiler wrappers unset, empty Rust,
rustdoc and encoded flags; repository test-stack default unchanged. No Trust
verification, whole-backend soundness, or TLC/MCC performance claim.

| Log | Selection | Passed |
| --- | --- | ---: |
| `lower.log` | Complete all-feature lower crate | 2,197 |
| `native.log` | Actual local function-address JIT and callback ABI | 6 |
| `cache.log` | Artifact-cache library selection | 43 |
| `private-metadata.log` | Excluded rustc-private workspace, locked resolution | 3 IR packages at the exact new pin |

Lower has 1,787 library and 410 integration tests. Cache leaves 3,518 tests
unselected; this is not the whole codegen/workspace gate. The separate
rustc-private backend is metadata-checked, not compiled by these selections.

```text
cargo test -p trust-cg-lower --all-features --locked -j2 -- --test-threads=1 --quiet
cargo test -p trust-cg-codegen --test local_function_address_jit --test ty_callback_abi_call_clobber --locked -j2 -- --test-threads=1 --quiet
cargo test -p trust-cg-codegen --lib artifact_cache --locked -j2 -- --test-threads=1 --quiet
cargo metadata --locked --manifest-path crates/rustc-codegen-trust-cg/Cargo.toml --format-version 1
```

Builds ran under the shared heavy gate with 6/5/4 GB reservations and sampled
peaks 1.44/2.26/2.22 GB. The broad soundness attestation lock is untouched:
these selected compatibility tests do not re-attest its separate proof gates.
