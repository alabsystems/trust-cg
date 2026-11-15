# Linux x86-64 floor: the decided-absent row and the bridge lane, on current upstream — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The floor machinery this branch adds, RE-MEASURED on the merged tree instead of
on the tree it was written against, with an `origin/main` floor run taken on the
same host beside it as the baseline. What is measured here is the machinery —
`DECIDED_ABSENT`, the `e2e_x86_64_swiftcc` row it carries under XD-03, and the
`m143_x86_vectorize_trace` bridge lane — now carried onto upstream's rewritten
shared runner (per-target command from `target_build_command`,
`TARGET_ENVIRONMENT` delivery, and a Cargo-configuration audit before any build
tool runs). Nothing here closes a completion row;
docs/linux-x86-64-completion.md
records what remains. This is a diagnostic floor, not public-release or proof
qualification, and the bridge lane runs in the explicit UNVERIFIED Trust lane —
no Trust-verified-compilation claim is made by any of it.

## Host, toolchains, and the two conditions this record discloses

| Item | Identity |
| --- | --- |
| Host | `x86_64-unknown-linux-gnu`, Linux 7.0.0-34-generic, Ubuntu gcc; **no clang**; the stock root toolchain ships **no AY**; the bundled portable-checker identity is **not authorized** by `verdict_db/canary_certs/manifest.v1` |
| Measured tree | `ba41e4726` (`dirty: false` under `--require-clean`, same `source_sha` and `source_fingerprint` at start and finish, `errors: []`) |
| Baseline tree | `origin/main` `9dd72f594`, measured in its own clean worktree on this host (`dirty: false`, `errors: []`). `origin/main` then advanced twice more, to `874c4b3ef` and `e985b634b`, both BRIDGE-ONLY changes (`crates/rustc-codegen-trust-cg/src/lib.rs` and its test corpus, plus docs and a report): no root-workspace crate and no floor script moved, so the baseline's 66 rows still describe that tree, and this branch's floor was re-measured on top of each with identical results — the same 47/67 and the same 20 rows every time |
| Root toolchain | stock Rust 1.97.1 (`rust-toolchain.toml`) through rustup proxies — the machine's aterm Trust default is NOT used for the root workspace |
| Trust compiler | tree-built stage2 `rustc 1.99.0-dev (3a3e781fe 2026-09-14) (trustc 0.1.0)` at `$HOME/trust/build/x86_64-unknown-linux-gnu/stage2`, named with `--trust-driver`; `selection: explicit-driver`, `lane: unverified` |

Two conditions, disclosed because they are choices and not facts about the code:

1. **Both runs were taken in clean detached worktrees, not in the lane
   worktrees.** Upstream's new Cargo-configuration audit refuses any config file
   that is not a byte copy of the committed `.cargo/config.toml`, and the
   parallel worktrees on this host carry a local `[profile] debug = 0` override
   that git is told to ignore. That override is a `[profile]` table, which the
   audit refuses by design. A clean worktree's config is the committed bytes, so
   the audit's exemption applies and both floors ran with `cargo_config` and
   `bridge_cargo_config` problem-free, before and after.
2. **Both runs set `RUSTFLAGS=-Cdebuginfo=0`,** recorded in each `report.json`
   under `provenance.configuration`. That keeps the memory envelope the local
   profile exists for, through a variable the audit deliberately does not cover;
   debug information does not change emitted semantics, and both sides were
   measured identically, so the comparison below is like for like.

## The two runs

```sh
# this branch (67 required targets)
python3 scripts/check_linux_x86_64.py --out <dir> --jobs 4 --max-rss-gib 20 \
  --require-clean --trust-driver <stage2>/bin/trustc
# origin/main 9dd72f594 (66 required targets; its runner has no --trust-driver)
python3 scripts/check_linux_x86_64.py --out <dir> --jobs 4 --max-rss-gib 20 --require-clean
```

| Run | Required | Pass | Fail | Wall | Verdict |
| --- | ---: | ---: | ---: | ---: | --- |
| `origin/main` `9dd72f594` (`baseline/`) | 66 | 46 | 20 | 3m20s | FAIL |
| this branch `ba41e4726` (`floor/`) | 67 | 47 | 20 | 1m53s | FAIL |

Target for target, the two runs differ in exactly TWO rows. Every other row has
the same verdict AND the same `passed`/`failed` counts, so this branch regresses
nothing upstream requires:

* `trust-cg-codegen/e2e_x86_64_calling_conv` — upstream **17 passed / 2 failed**
  (FAIL), this branch **18 passed / 0 failed** (PASS). The two upstream failures
  are `e4_swiftcc_return_placement_is_measured_not_asserted` (gcc reports
  `'swiftcall' attribute directive ignored` and the driver is left with
  undefined swiftcc references) and
  `x86_64_calling_conv_control_battery_refutes_every_abi_defect` (the
  hand-written control assembly spelled its symbols Mach-O style, so GNU ld
  reported every control undefined). The (E4) split and the `host_sym` symbol
  spelling fix both; this is the one row where this branch CHANGES an upstream
  reading, and it changes it in the passing direction.
* `rustc-codegen-trust-cg/m143_x86_vectorize_trace` — absent upstream, and
  **FAILING here** (0 passed / 2 failed against its pinned minimum of 2). See
  below: the cause is upstream's proof-promotion policy, not the lane.

## The machinery, read off the record

* `report.json` carries `decided_absent` with the one row — `trust-cg-codegen` /
  `e2e_x86_64_swiftcc`, decision `XD-03`, and its full reason — and
  `controls.trust_driver` records the named Trust package. The summary prints
  `Linux x86-64 regression floor: decided absent, not run: ...` TWICE, once
  before the first target and once with the verdict.
* The decided-absent target was NOT run: there is no
  `trust-cg-codegen--e2e_x86_64_swiftcc.log` in `floor/`, and `required_targets`
  has 67 rows that do not include it. It is still gated elsewhere, and still
  honest: `swiftcc-target-skip.log` is that target
  run directly on this host — it compiles, probes the driver, prints the
  conforming `SKIP: (E4) NOT RUN` with the XD-03 diagnostic, and passes.
* The bridge lane ran in `crates/rustc-codegen-trust-cg` under
  `targo --unverified test --release --locked`, with `cwd`, the `RUSTC` override
  (`set_environment`) and the two checker variables it runs WITHOUT
  (`unset_environment`: `TCG_EXTERNAL_CLEAN_CHECKER`, `TCG_CLEAN_CHECKER`, which
  `trustc` refuses as untracked compiler controls) all recorded in its target
  record. Sampled peak RSS 1820 MiB against the 20 GiB ceiling.
* The bridge workspace's own Cargo configuration was audited before the pinned
  package was probed and again at the end: `bridge_cargo_config` /
  `final_bridge_cargo_config`, `tool: targo`, `environment_prefixes: ["CARGO_",
  "TARGO_"]`, `problems: []` both times.

## Why the bridge row fails, and what it is not

The row is NOT failing because the vectorizer stopped firing. The trace lines
the test asserts are all present in the transcript — the saxpy-Q row-register
nest, the `movdqu` store fill loop and the runtime byte-fill tier all report
VECTORIZED. The compile is refused afterwards, in two layers:

1. `[TCG-AY-IDENTITY-UNMATERIALIZED]` — `<stage2>/bin/ay` IS admitted, but no
   private copy of its bytes can be made, because `~/.cache/trust-cg` on this
   host is mode 0775 (created by an older trust-cg under Ubuntu's umask 0002).
   Upstream's own fix names this host and this remedy: create the cache 0700, or
   point `XDG_CACHE_HOME` at a directory only this user can write. It never
   changes a directory that already exists.
2. `[TCG-PROOF-465]` proof promotion rejected — the emitted opcode inventory has
   uncovered non-pseudo opcodes (`MovRR`, `Lea`, `MovRM`, `MovMR`, `MovRR32`,
   …) whose only evidence is statistical sampling, which is not proof credit.

`bridge-private-cache.log` is the same target re-run
with `XDG_CACHE_HOME` pointing at a private 0700 directory. AY then materializes
and runs: the `TCG-AY-IDENTITY-*` clause disappears from the transcript entirely
(18 occurrences before, 0 after) and the Alethe certificate store fills. The row
still fails, on layer 2 alone. So the bridge lane's failure is the SAME XD-01
proof-promotion class that fails nine of upstream's own required targets on this
host, reached through the bridge rather than through a JIT or dispatcher row:
since `ProofPromotionEnvironment` was removed, a statistically-sampled
instruction is credited on no host, and the bridge compiles ordinary `std` code
(`lang_start`, the `FnOnce` shims) that emits exactly those opcodes. It passed on
2026-09-24 under the older policy. Closing it needs a formal discharge route for
those opcode classes, not a weaker policy, and not a host repair.

**This is left as a red required row rather than quietly removed.** `TARGETS`
stays all-required, and `DECIDED_ABSENT` is for a recorded ruling with an id —
not something a lane may mint for itself. Ruled 2026-10-02 (OD-45 in the
decision record): the row stays required, and the floor reports it red.

### What the row would need, measured rather than argued

`bridge-knob-probe.log` is the same target with BOTH
halves removed, and it reads exactly its pinned minimum: **2 passed / 0 failed**.
The two halves are:

1. A cache root only this user can write, so AY materializes: `chmod go-w
   ~/.cache/trust-cg`, or `XDG_CACHE_HOME`. That is a one-line HOST repair,
   prescribed by trust-cg's own refusal text and by the upstream commit that
   added the rule. It was not applied here, because `~/.cache/trust-cg` is shared
   with every other lane measuring on this machine right now.
2. The `no-proof-certs` backend knob on the bridge compile. Dozens of the
   bridge's own native-diagnostic tests already carry it, several with comments
   naming this exact situation; the knob is TRACKED (`-Ztrust-ir-cg-args`, in the
   crate hash), so it tells no provenance lie. The probe applied it as a
   ONE-WORD, UNCOMMITTED edit and reverted it.

The knob is NOT in what this branch ships. Turning proof-certificate emission
off is what makes a red row green here, and even in a lane that claims nothing —
the floor's own docstring says the bridge lane makes no
Trust-verified-compilation claim — reducing what a proof-oriented gate exercises
is not a lane's call. Three measured options were on the table: the host repair
plus the knob (the row then measures the tiers it was written to measure), a
decided-absent row under a new decision id while XD-01 is open, or leaving the
row red. OD-45 takes the last: no knob, no decided-absent row.

## The twenty failures, by class

None of them is this work. Nineteen are identical to `origin/main`'s own run on
this host, row for row and count for count; the twentieth is the bridge row.

| Class | Count | Rows |
| --- | ---: | --- |
| No admissible AY / unauthorized portable-checker identity | 7 | `e2e_x86_64_differential`, `guard_bounds_probe_x86`, `guard_kernel_gate_x86_e2e`, `guard_kernel_gate_x86_divzero_e2e`, `guard_kernel_gate_x86_null_e2e`, `guard_kernel_gate_x86_shiftrange_e2e`, `guard_kernel_gate_x86_linkrun` |
| XD-01 `ProofPromotionRejected` | 9 | `e2e_x86_64_dispatcher`, `e2e_x86_64_module_batch_fnptr`, `e2e_x86_64_module_batch_globals`, `jit_sysv_x86_64_spill_replay`, `jit_validation_modes_x86_64`, `jit_x86_64_aggregate_abi_fail_closed`, `jit_x86_64_profile_modes`, `x86_64_constant_pool`, `x86_64_sysv_ay_abi` |
| Upstream fail-closed lowering refusal (`UnsupportedInstruction`) | 2 | `jit_integration_x86_64` (34/5), `x86_64_target_features` (47/3) |
| Darwin-only host assumption (`cc -arch x86_64`) | 1 | `e2e_x86_64_callee_saved` |
| XD-01, reached through the bridge | 1 | `rustc-codegen-trust-cg/m143_x86_vectorize_trace` |

The first class is larger than the eleven failures the 2026-09-24 record
reported, and `jit_cert_cache_identity_x86_64` has moved the other way and now
PASSES. Both movements are upstream's: the guard-carrier canary now asks the
solver where it used to accept a sampled result, and the promotion environment
that used to credit one was removed. The 2026-09-24 numbers are not a baseline
for this tree, which is why `baseline/` was measured rather than cited.
