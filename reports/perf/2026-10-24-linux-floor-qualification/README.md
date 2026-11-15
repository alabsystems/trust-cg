# Linux AArch64 regression floor at `8faee6c6f` (2026-10-24)

**Claim.** The maintained Linux AArch64 regression floor
(`scripts/check_linux_aarch64.py`) ran on origin/main `8faee6c6f` on this
host with the proof tools required: 249 of 252 required targets passed. It
gives three ledger rows the Linux run their notes named as pending:

| Row | Target | Result |
| --- | --- | --- |
| L03-P12 (AArch64 JIT exception handling) | `trust-cg-codegen` `jit_exception_handling` | 11 passed, 0 failed, no `SKIP` |
| L11-P7 (AArch64 cache-poisoning / stale-source controls) | `trust-cg-codegen` `jit_cert_cache_identity_aarch64` | 9 passed, 0 failed, no `SKIP` (with the discovered AY/Clean authority) |
| X-LEAN-P3 (Lean AArch64 encoder golden binding) | `trust-cg-codegen` `lean_a64_encode_golden_binding` | 4 passed, 0 failed, no `SKIP` |

**Boundary.** Native regression evidence on one host; not proof credit and
not a qualification of the rows' other residuals (each row's note keeps
them). Three floor targets were red at this source and are being repaired
separately: `aarch64_memory_source_binding` (4 tests), `diff_cmp_overflow`
(2) and `sweep3_cmp_branch_fusion` (1).

## Command

```sh
XDG_CACHE_HOME=<fresh 0700 directory> build-slot -- python3 -B scripts/check_linux_aarch64.py \
  --trust-unverified --require-clean --max-rss-gib 16 --require-offline-deps \
  --require-proof-tools --jobs 4 --out <report directory>
```

with `PATH` starting at the overlay toolchain `trust-ae9c2c1d-ay13556`
(ruling LD-94).

## Identities (from the run's `report.json`)

- Source `8faee6c6fb0a9854c508a75dd9cbc27e1a2ebd81`, clean (no tracked diff,
  no untracked file); `Cargo.lock` sha256 `2c46a860abf8b40b…`.
- Host `aarch64-unknown-linux-gnu`; run started 2026-10-24T01:35:42Z.
- Compiler: Trust `ae9c2c1d` (`trustc` sha256 `b2d4fa4bb1ce8106…`), through
  the overlay copy of the sealed package (LD-94).
- AY: `…/trust-ae9c2c1d-ay13556/bin/ay`, route toolchain-sysroot, pinned,
  sha256 `0f4c21c75317bacadaacfd6be2901ec1e70b53683ee4b8f1571d0ccef2572e05`
  (build 13556, `ebde49de3`).
- Clean: `…/trust-ae9c2c1d-ay13556/bin/clean`, route toolchain-sysroot,
  pinned, sha256
  `6a6b27c573c209b9d76c9e98bf8e18e1dda5c16c09ff72735226901d53783a4e`
  (`d0bf4d54`).

The per-target logs and `report.json` are local provenance only, under the
host's floor directory (`run-floor1024b`).
