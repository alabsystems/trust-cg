# Integrated Linux gates with AY admitted, before the thirty-fifth main push (2026-09-27)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

## Why this run has a new baseline

On this host, and on any host with umask 0002, AY had never run inside trust-cg:
- trust-cg created `~/.cache/trust-cg` with a mode taken from the umask (0775).
- The AY private-copy rule (`ay_private_copy::check_ancestors`) refuses a group-writable ancestor.
- So every AY admission ended in `AyIdentityRefusal::Unmaterialized`, and nothing reported it.

Both runs below therefore use a private 0700 cache root (`XDG_CACHE_HOME`), with the `trust-cg` directory pre-created at 0700, so that AY is admitted. `~/.cache` is not modified.

- **`mainx1`:** origin/main `063b6c49a`, unchanged, in Trust development mode (Trust ae9c2c1da, `--trust-unverified`), with AY admitted. This is the new baseline.
- **`i51`:** the integration `499d4146e`. It is origin/main plus:
  - **Ledger updates:** the fifth L02-P6 and eleventh L02-P10 closure audits (both kept PARTIAL), and new rows L02-P13 (LLVM importer function linkage) and L06-P16 (bridge Fn-trait shims).
  - **`fix/weak-declaration-linkage`:** a named refusal, `[TCG-DECLARATION-LINKAGE]`, for a body-less function whose linkage names a definition. Module merge refuses it in either input order. Two verifier rounds.
  - **`perf/linux-row-readiness`:** a performance lane that fails closed.
    - Resource aggregates are exact and fail closed, with preregistered RSS predicates.
    - Every validated row is checked for regressions; results are compared only against like runs; a changed corpus is inconclusive unless an evidence row declares a new lineage.
    - Stamps are recomputed; the canary and sentinel run on Linux; backend freshness covers every build input.
    - Five verifier rounds. The lane still cannot record a qualifying row, because the production bridge refuses the whole corpus with `[TCG-PROOF-465]` (L07-P2).
  - **`fix/ay-private-copy-cache-mode`:** the AY cache fix.
    - Every directory it creates under `<cache>/trust-cg` is 0700 whatever the umask; existing directories are never loosened.
    - A refusal names the directory and the remedy.
    - The floor's `--require-proof-tools` check runs the real admission rule before any target runs (`ay_admission` in `report.json`).
    - Unit tests share one per-user AY copy, and partial copies left by killed writers are cleaned up.
    - Three verifier rounds.

## What admitting AY changes on main (`mainx1` compared with `run-i48`)

**Floor.** Failures drop from 26 tests in 8 targets to 10 tests in 7 targets, and no failure is new:
- `e2e_cegis_superopt` and `jit_cert_cache_identity_aarch64` now pass completely.
- Three `jit_fail_closed_proof_policy` tests and one `jit_source_bound_arithmetic` test now pass.

**Codegen and lower libraries.** Failures drop from 7 to 1.

The other checks are unchanged.

## Result: `i51` has no failure beyond `mainx1`

- **Floor:** the same 10 failing tests, across 204 targets. `records/floor-failed-tests.diff` is empty.
- **Library:** 1 failure, the same test; the integration also runs two more passing tests.
- **CLI, natives and local-call:** the same failures as main (1, 3 and 1).
- **Green checks:** fsym 18 and 20, opt 3,622, symbol binding and relocation model 98 (LLD and gold required), verifier gates 108, and the unwrap ratchet.
- **Bridge:** only the known L06-P1 refusal (`aliased_f32_read`, `[TCG-PROOF-465]`, 10 of 11 tests pass). TLS and unwind each pass 2 of 2.

This is regression evidence only. It does not show complete Linux qualification, proof or Trust-toolchain authority, or release readiness, and every L01–L14 row stays open.
