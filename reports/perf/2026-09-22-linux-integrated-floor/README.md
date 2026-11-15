# Integrated Linux regression floor before the main push — 2026-09-22

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Result: **PASS**, **144 required target families passed, 0 failed, 809 Rust
tests passed**, on clean source `0e9bdac61d93226fc6f5c1b6409f4809d601a45f`
(source fingerprint `c62cafa1b415ce239341871dc75d829d625b16a026e15b35548e803fa8d43732`,
identical before and after). That commit is origin/main `16c4a4a3f` with the
Linux lane records and runner/harness repairs, the `e2e_aarch64_sret_linux`
(L01-P5) and `e2e_aarch64_direct_enums_linux` (L05-P5) twins merged, the
literal `[TCG-ARG-ABI]`/`[TCG-RET-ABI]` census repair and the sret twin's
Darwin-floor registration. It is the gate run for pushing that content to
remote main; origin/main's own 24 new compiler commits (verify, opt, ELF
writer, x86-64 bridge) are inside this denominator.

This is the first run with every runner control on, including the new
`--require-proof-tools`:

```sh
PKG=$HOME/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23
PATH="$PKG/bin:$HOME/.cargo/bin:$PATH" env -u RUSTFLAGS -u CARGO_TARGET_DIR -u RUSTC -u RUSTC_WRAPPER \
  python3 -B scripts/check_linux_aarch64.py --require-clean --max-rss-gib 16 \
    --require-offline-deps --require-proof-tools --jobs 2 --out /path/outside/source/run3
python3 scripts/check_evidence_archive.py reports/perf/2026-09-22-linux-integrated-floor
```

- `proof_tools` and `final_proof_tools` agree: AY
  `ec2bf181c384bff0453487b47781fb6d40b959a72c1236bdc760ccc1feee4830` and Clean
  `8d819378eb80696a6a753980bb1722de676f283c4219887f769ac70868f0fff8`, both through
  the `aterm-packaged` route of the installed development package.
- Highest sampled resident set 170 MiB against the 16 GiB ceiling; the 144
  bounded Cargo invocations took 527 seconds of target wall time
  (23:34:02Z to 23:43:10Z) against a target directory pre-warmed with
  `cargo test --no-run` for exactly these targets at the same commit.
- Stock Rust 1.97.1 through the rustup proxies, gcc 13.3, GNU readelf 2.42;
  companion pins trust-ir `7b9146ba`, Clean `55a85e99`, AY `849c19fa`, all
  resolved offline and unchanged across the run.
- The two new twins pass here as required floor members: the sret twin 8/8,
  the direct-enum twin 6/6.

The same source also rebuilt the private bridge backend and its native test
with the sealed Trust `a62ae50d` package (the lane compiles the edited
`rustc-codegen-trust-cg/src/lib.rs`); its native target still refuses
`aliased_f32_read` at O0 with `[TCG-PROOF-465]`, identical to the
[bridge checkpoint](../2026-09-22-linux-bridge-checkpoint/README.md) (L06-P1).
That run is identified here by its report, not archived again.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness; every L01–L14 row remains
OPEN.

`records/` is the complete runner output (`report.json` and all 144 per-target
logs with resident-set receipts); `records/bridge-report.json` is the bridge
lane report for the same source; `runner-source/` copies the runner and its
helpers at this commit.
