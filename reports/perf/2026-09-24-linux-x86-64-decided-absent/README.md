# Linux x86-64 floor: the decided-absent record and the bridge lane — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The measurement that qualifies three pieces of floor machinery on a native
`x86_64-unknown-linux-gnu` host: `DECIDED_ABSENT` in the shared runner, the
`e2e_x86_64_swiftcc` row it carries under XD-03, and the
`m143_x86_vectorize_trace` bridge lane. Nothing here closes a completion row;
docs/linux-x86-64-completion.md
records what remains. This is a diagnostic floor, not public-release or proof
qualification, and the bridge lane runs in the explicit UNVERIFIED Trust lane —
no Trust-verified-compilation claim is made by any of it.

## Host and toolchains

| Item | Identity |
| --- | --- |
| Host | `x86_64-unknown-linux-gnu`, Linux 7.0.0-31-generic, Ubuntu gcc 15.2.0; **no clang** |
| trust-cg source | `0bb155abf`, `dirty: false`, same `source_sha` and `source_fingerprint` at start and finish |
| Root toolchain | stock Rust 1.97.1 (`rust-toolchain.toml`), rustup proxies (the machine's aterm Trust default is NOT used for the root workspace) |
| Trust compiler | tree-built stage2 `trustc 1.99.0-dev (3a3e781fe 2026-09-14)` at `$HOME/trust/build/x86_64-unknown-linux-gnu/stage2`, named with `--trust-driver`, `selection: explicit-driver`, `lane: unverified` |

## The run

```sh
python3 scripts/check_linux_x86_64.py --out <dir> --jobs 4 --max-rss-gib 20 \
  --require-clean --trust-driver <stage2>/bin/trustc
```

`floor/` retains `report.json` and every per-target log. Verdict: **FAIL, 56 of
67 targets pass, 11 fail**, `errors: []` (no control refused the run), wall
4m03s, resident supervision `linux-proc` with a 20 GiB ceiling.

What this measurement establishes about the machinery, as opposed to about the
compiler:

* `report.json` carries `decided_absent` with the one row — `trust-cg-codegen`
  / `e2e_x86_64_swiftcc`, decision `XD-03`, and its reason — and
  `controls.trust_driver` records the named Trust package. The summary prints
  `Linux x86-64 regression floor: decided absent, not run: ...` twice, once
  before the first target and once with the verdict.
* The decided-absent target was NOT run: no `trust-cg-codegen--e2e_x86_64_swiftcc.log`
  exists in `floor/`, and `required_targets` has 67 rows that do not include it.
* The bridge lane `rustc-codegen-trust-cg/m143_x86_vectorize_trace` **passes**,
  `2 passed / 0 failed` in 24.4s against its pinned minimum of 2, run with
  `cwd` = `crates/rustc-codegen-trust-cg` and
  `environment_overrides: {"RUSTC": "<stage2>/bin/trustc"}` — both recorded in
  its target record — by `targo --unverified test --release --locked`. Sampled
  peak RSS 1797 MiB against the 20 GiB ceiling.

## The eleven failures, and why none of them is this work

Every failing target is one this change does not touch, in one of three
pre-existing classes. The two files this change does touch that the floor runs
(`e2e_x86_64_calling_conv`, and the bridge lane) both pass.

| Class | Targets | Cause read from the retained log |
| --- | ---: | --- |
| XD-01 proof promotion | 7 | `ProofPromotionRejected` for statistically credited instructions on a formal-capable host: `jit_cert_cache_identity_x86_64`, `jit_sysv_x86_64_spill_replay`, `jit_validation_modes_x86_64`, `jit_x86_64_aggregate_abi_fail_closed`, `jit_x86_64_profile_modes`, `x86_64_constant_pool`, `x86_64_sysv_ay_abi` |
| Upstream fail-closed lowering refusal | 2 | `Adapter(UnsupportedInstruction("Select scalar condition must be Bool, got Vector(Bool, 2)"))` in `jit_integration_x86_64` (34 pass / 5 fail) and `x86_64_target_features` (47 pass / 3 fail) |
| Darwin-only host assumption | 2 | `e2e_x86_64_callee_saved` passes `cc -arch x86_64`, which GNU `cc` rejects (`unrecognized command-line option ‘-arch’`); `guard_kernel_gate_x86_linkrun` prints an explicit `SKIP:` for `aarch64_linkrun_inbounds_returns_value_and_oob_traps` |

## What the swiftcc split changed, measured both ways

`upstream-calling-conv-baseline.log` is `origin/main`'s own
`e2e_x86_64_calling_conv.rs`, copied verbatim into a throwaway target
(`zz_upstream_calling_conv_baseline`, deleted afterwards; the tree in `floor/`'s
provenance is clean) and run on this host. It is **17 passed / 2 failed**:

* `e4_swiftcc_return_placement_is_measured_not_asserted` — the link fails.
  GCC reports `‘swiftcall’ attribute directive ignored [-Wattributes]` and the
  driver is left with undefined references to `sc_two_int`, `sc_two_fp`,
  `sc_mix_2i2f`, `sc_three_int`, …
* `x86_64_calling_conv_control_battery_refutes_every_abi_defect` — the same ELF
  symbol-spelling defect in the (E1..E3) control battery: the hand-written
  assembly defines `_ctl_int_correct` (Mach-O) while the C driver references
  `ctl_int_correct`, so GNU ld reports every control undefined.

After the split the same host reads `e2e_x86_64_calling_conv` as **18 passed /
0 failed** (`floor/trust-cg-codegen--e2e_x86_64_calling_conv.log`): the control
battery links because the assembly now spells its symbols through `host_sym`,
and the swiftcc readings are no longer in that target at all. So this floor's
`56 of 67` is not comparable to a `56 of 66` on `origin/main`: on `origin/main`
this host would read `54 of 66`, because `e2e_x86_64_calling_conv` fails and
`m143_x86_vectorize_trace` is not registered. That number is DERIVED from the
two measurements above, not from a floor run of `origin/main`.

`swiftcc-target-skip.log` is the split-out target run on its own
(`cargo test -p trust-cg-codegen --test e2e_x86_64_swiftcc`): **1 passed**, with
the conforming refusal line

```
SKIP: (E4) NOT RUN — the host `cc` does not honour `__attribute__((swiftcall))` …
```

naming XD-03. This is why the target is decided-absent rather than deleted: it
still compiles, still runs, still refuses honestly, and
`scripts/soundness_check.sh` still gates it — but the floor, which counts a
runtime SKIP as a failure, does not require it on a host that cannot take the
reading.

## Root suites on the same tree

| Suite | Result |
| --- | --- |
| `cargo test -p trust-cg-codegen --lib` | 4,159 passed / **19 failed** / 1 ignored — the documented pre-existing set on this host, listed in `codegen-lib-failures.txt`: 18 `compile_service::tests` rows and `compiler::tests::test_aarch64_parallel_and_serial_multi_function_byte_identical`, every one refused by proof promotion ("proof promotion rejected for target Aarch64 … needs independently replayed proof"), i.e. XD-01 |
| `cargo test -p trust-cg-verify --test soundness_manifest` | 11 passed / 0 failed — the `ABI-x86-cc` invariant now reads the (E4) test, the readings counter, the `swiftcall` text, the not-a-no-op control check and the `SKIP: (E4) NOT RUN` marker out of the SPLIT target, and requires `scripts/soundness_check.sh` to gate it |
| `cargo test -p trust-cg-lower --lib` | 1,906 passed / 0 failed (this change edits two doc comments there) |
| `cargo test -p trust-cg-codegen --test e2e_x86_64_swiftcc` | 1 passed, with the XD-03 skip line (`swiftcc-target-skip.log`) |
| `python3 scripts/tests/test_linux_x86_64_gate.py` | 14 tests, OK |
| `python3 scripts/tests/test_linux_aarch64_gate.py` | 43 tests, OK (1 skipped) — the SHARED runner's own gate, unbroken by these changes |

## Base

The measured tree `0bb155abf` sits on `origin/main` at `43affd4a9`. `origin/main`
advanced to `777ab22cd` while this record was being written; that commit adds
only archive report files under
`reports/perf/2026-09-25-x86-vectorizer-integration/` and touches no file this
measurement compiles, `43affd4a9` is its ancestor, and this branch merges onto it
with no conflict — so the record is NOT re-measured and its stamped revision
stays a real commit in this branch's history.

## Reproduction notes

* The bridge lane's `build.rs` declares `cargo:rerun-if-env-changed=PATH`, so a
  floor run whose ambient `PATH` differs from the last bridge build's rebuilds
  `rustc_codegen_trust_cg` in release inside the lane's own per-target timeout
  (default 1200s). In this run that rebuild plus the two tests took 95s of the
  budget. Keep `PATH` stable between bridge builds and floor runs, or raise
  `--timeout-seconds`, rather than reading a timeout there as a lane defect.
* Floor logs are retained under `floor/`; the per-target runtime is dominated by
  building each test executable, so a cold worktree needs a warm dependency
  graph before the 1200s per-target bound is meaningful.
