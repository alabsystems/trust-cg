# Complete current-source Linux regression floor — 2026-09-22

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Result: **PASS**, **142 required target families passed, 0 failed, 795 Rust
tests passed**, on clean source `4ded2b97c4d21fd21bc1b16fe9c1334fa4a1da81`
(origin/main at the time of the run; source fingerprint
`323eda3d5d23afefb729f619b6574def77912ba7d9ed3587e2d53eeb48b8217a` identical
before and after) with stock Rust 1.97.1 on the Linux AArch64 host. This is
the first Linux execution of the 142-target inventory, which grew from the
last retained 129-family run through the owner's merged wave branches
(closures, direct-tag enums, i128 switch selectors, sret through function
pointers, the trust-ir construct inventory gate, concurrency and JIT
exception controls, and the trust-ir `7b9146ba` cohort).

The maintained entry point ran directly, not through an external harness:

```sh
PKG=$HOME/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23
PATH="$PKG/bin:$HOME/.cargo/bin:$PATH" env -u RUSTFLAGS -u CARGO_TARGET_DIR -u RUSTC -u RUSTC_WRAPPER \
  python3 -B scripts/check_linux_aarch64.py --require-clean --max-rss-gib 16 \
    --require-offline-deps --jobs 2 --out /path/outside/source/run2
python3 scripts/check_evidence_archive.py reports/perf/2026-09-22-linux-required-floor
```

Controls: `--require-clean` (tree clean before and after), `--max-rss-gib 16`
with Linux `/proc` supervision (highest sampled peak 162 MiB, every receipt
`within`), `--require-offline-deps` (every pinned companion revision resolved
locally and Cargo ran `--offline`; the lockfile and checkout identities were
unchanged at the end), two Cargo jobs, one test thread, a 1200-second bound
per target. The 142 bounded Cargo invocations took 527 seconds of target wall
time (17:20:20Z to 17:29:13Z overall) against a target directory pre-warmed
with `cargo test --no-run` for exactly these targets at the same commit.

## Identities

- Host: `aarch64-unknown-linux-gnu`, Ubuntu 24.04.4, Linux `6.17.0-1026-nvidia`.
- `rustc 1.97.1 (8bab26f4f 2026-07-14)`, `cargo 1.97.1 (c980f4866 2026-06-30)`
  through the rustup proxies; `cc`/`c++` gcc 13.3.0; GNU readelf 2.42.
- Companion pins from `Cargo.lock`: trust-ir `7b9146ba2ab5d2552514e6842883db9008e1dd9d`,
  Clean `55a85e998d428606ec9745bf6ba65fd1888ea149`, AY `849c19fa0382085174a6a4827739681f059b4615`
  (the report's `dependency_identity` and `final_dependency_identity` bind the
  Cargo database, checkout tree hashes and lockfile SHA-256).
- Proof tools reachable by the verifier: the installed development package
  `09aa977c-ayba60326b-cleand35d6f23` with AY `ec2bf181c384bff0453487b47781fb6d40b959a72c1236bdc760ccc1feee4830`
  and Clean `8d819378eb80696a6a753980bb1722de676f283c4219887f769ac70868f0fff8`,
  pinned through its aterm-style `bin` prefix on PATH. This run predates the
  runner's `proof_tools` record; `records/launch.json` retains the PATH prefix
  and the provisioning record
  the recipe.

## Negative control: the same floor without a pinned checker

`records/run1-negative-control/` retains the first launch of the same commit
with only `$HOME/.cargo/bin` prepended. Its proof-replay targets failed:
`jit_fail_closed_proof_policy` 2 passed / 5 failed in 40 s with
`ProofPromotionRejected ... source-bound frame needs independently replayed
proof` for the `StpPreIndex`/`AddRI`/`LdpPostIndex` frame of a source-bound
leaf, and `jit_source_bound_arithmetic` and `jit_cert_cache_identity_aarch64`
did not complete. The run was interrupted after 78 targets (74 passed, 538
tests) and is retained as `fail`/`interrupted`. The identical test binary
passed 7/7 in 3 seconds with the package prefix on PATH, and run2 above passed
every target. The cause is provisioning, not the compiler: the verifier only
accepts a checker from an explicit override or an aterm-style package prefix
(`crates/trust-cg-verify/src/aterm_toolchain.rs`), and the maintained runner
could not previously say which resolution a run had. The follow-up runner
change records `proof_tools` and adds `--require-proof-tools`.

## Boundary

This is current-source root-workspace regression evidence for the required
Linux floor. It is not complete Linux qualification, proof authority, Trust
toolchain authority or release readiness; the bridge lane, the full test
matrix, the soundness gate and every L01–L14 closure obligation remain
separate. All L01–L14 rows remain OPEN.

## Retained files

`records/run2/` is the complete runner output directory (`report.json` and all
142 per-target logs, each with its resident-set receipt);
`records/run1-negative-control/` is the interrupted first launch;
`records/launch.json` records both invocations and PATH prefixes;
`records/prewarm.sh` and `records/prewarm.log` are the pre-warm build;
`runner-source/` copies the runner and its helpers at this commit.
