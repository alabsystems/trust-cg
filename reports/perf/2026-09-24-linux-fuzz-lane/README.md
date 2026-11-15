# Linux AArch64 fuzz lane — 2026-09-24 (L13-P7)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This archive retains the runs of the maintained fuzz lane,
`scripts/run_linux_fuzz_lane.py`, from 2026-09-24 to 2026-09-26, together with:
- the runs that admitted 35 fuzz targets into the Linux floor;
- the compiler defects the lane and its reviews found;
- the evidence for the repairs after three independent verifier rounds.

The host is NVIDIA Grace, `aarch64-unknown-linux-gnu`, Linux
`6.17.0-1026-nvidia`, shared with other jobs. Fuzzing used at most four
processes, and builds used `-j 4`. The plan section is
L13-P7 Linux fuzz lane.

## Runs, newest first

1. **Qualifying run after the third review, clean `096aacc2f`**
   (`records/campaign/`). Status PASS, qualifying, 2026-09-26 03:49Z to 04:37Z.
   The runner records:
   - no ambient variable to remove, and a Cargo configuration audited clean
     before any Cargo command and again at the end;
   - the pinned stable 1.97.1 toolchain at its pinned rustc commit, and the
     pinned nightly.

   The results:
   - **Controls.** All five planted failures were judged FAIL for their
     planted reasons.
   - **Panic-fuzz.** Seven families passed at 10,000 cases, and every
     family's case-count probe printed `configured=10000 run=10000`.
   - **libFuzzer.** The six targets ran 600 s each and left no artifact:
     - `fuzz_encode_instruction`: 259,602,382 executions;
     - `fuzz_macho_fixup`: 103,761,967 executions;
     - `fuzz_translate_function`: 2,730,859 executions;
     - `fuzz_compile_function`: 192,618 executions;
     - `fuzz_compile_x86_64`: 154,433 executions;
     - `fuzz_verify_module`: 5,176 executions;
   - **JIT differential.** Seeds 1–10,000 checked exactly 65,000 rows,
     all executed. 44,996 scalar rows were compared against the
     interpreter, 5,000 consumer-shape rows against their oracle, and
     15,004 scalar rows across the three levels only.
2. **Checks after the third review, at `096aacc2f`**
   (`records/controls-096aacc2f/`).
   - **Reproducers.** `reproducers/` holds 18 runs, each with its
     `report.json`, and `results.json`. The owner's `--trust-unverified`
     floor was given each of six `TARGO_*` config variables. The floor and the
     lane were given a relative `CARGO_HOME` with a `[target]` runner, a FIFO
     `.cargo/config`, a symlink from it to `/dev/stdin`, and a Cargo home with
     an `[alias]`. The floor was also given `CARGO_TERM_QUIET` and `[term]
     quiet`. Each run refused before any build tool ran: its report has no
     `provenance`. A stock floor under `RUSTUP_TOOLCHAIN=trust` stopped at its
     preflight, naming the Trust build of Cargo.
   - **Seven families through the floor.** `floor-panic-fuzz-families/`, with
     `--require-clean`. Each family passed at its new pin, and each probe
     printed its default count. Ambient `CARGO_MANIFEST_DIR`, `CARGO_PKG_NAME`,
     `CARGO_MAKEFLAGS` and `CARGO_FEATURE_NEGATIVE_CONTROL` were recorded and
     removed.
   - **Case-count flips.** `case-count-flips/` puts `env PROPTEST_CASES=7`
     in front of Cargo. All 14 family runs, through the floor at the defaults
     and through the lane at 64 cases, failed on their probe lines. Without it,
     all 14 passed.
   - **Nested checkout.** `nested-checkout-floor/` is a checkout nested in the
     worktree, with a byte-identical committed config. It audited clean and its
     floor row passed. `audit.txt` shows the `08b8d07f0` audit refusing it.
   - **Owner's Trust-mode floor.** `trust-floor-first-12/` ran the first
     twelve targets with Trust `ae9c2c1da`, `--trust-unverified
     --require-offline-deps`. It passed 12/12 (96 tests), with the audit
     prefixes `CARGO_` and `TARGO_`.
   - **Short lane run.** `short-lane/` used 20 s, 64 cases and 50 seeds, and
     passed with exit 3. It had 17 hostile ambient values, all removed and
     recorded. All five controls were detected, and every family's probe
     printed `configured=64 run=64`.
3. **Qualifying run after the second review, clean `7ae258217`**
   (`records/campaign-7ae258217/`), 2026-09-26 01:32Z to 02:23Z. It passed. Its
   `fuzz_macho_fixup` fuzzed the parser that copied every symbol name, and
   only `panic_fuzz_lower` had the case-count probe. Its JIT split is the same
   as in run 1.
4. **Controls at `7ae258217`** (`records/controls-7ae258217/`).
   - **Short lane run.** With 20 s, 64 cases and 50 seeds it passed with
     exit 3. It named the short budgets as its non-qualifying reasons. It ran
     with ten hostile ambient values, and removed and recorded each of them:
     `ASAN_OPTIONS=detect_leaks=0`, `PROPTEST_CASES=1`, `RUSTFLAGS`,
     `RUSTUP_TOOLCHAIN`, `RUSTUP_AUTO_INSTALL=1`, `RUST_MIN_STACK`, `CFLAGS`,
     `CXXFLAGS`, `CARGO_ALIAS_PROBE` and `CARGO_PROFILE_DEV_OVERFLOW_CHECKS`.
     All five controls were detected, and the case-count probe printed
     `configured=64 run=64`.
   - **Flips.** `libfuzzer-flips/`, `panic-fuzz-and-jit-flips/` and
     `case-count-flips/` run the lane's own functions with each planted
     failure taken away, or with a forced Cargo `[env] PROPTEST_CASES` of "0"
     or "7" that bypasses the audit on purpose. Every such control FAILS. The
     case-count probe lines in `case-count-flips/results.json` were taken from
     the logs after the run, because the harness's first extraction missed the
     libtest prefix.
   - **Injection reproducers.** `injection-lane/` is the verifier's reproducer:
     an injected `CARGO_HOME` with `[env]`, plus `CXXFLAGS`, `LD_LIBRARY_PATH`
     and `CARGO_ALIAS_PROBE`. The lane now fails before any build (exit 1).
     `injection-floor-*/` shows the floor refusing before any target, both for
     the verifier's non-forced `[env]` and for `[build] rustflags` plus
     `[profile]`.
   - **Floor probe row.** `floor-probe-row/` runs the floor's
     `panic_fuzz_lower` row with its required probe line under an ambient
     `PROPTEST_CASES=3`. It passed 6 tests with `configured=256 run=256`.
   - **Refused floor.** `floor-refused-proof-tools/` is a full-floor attempt
     that `--require-proof-tools` refused before any target. `main`'s AY
     identity rule (`85e1f504b`) admits only a build toolchain's own `bin/ay`
     or an explicit byte copy, and a stock-toolchain build ships none.
5. **`b6541a6db`** (`records/controls-b6541a6db/`). This short run failed
   `panic_fuzz_lower` because the probe line check required a whole line, and
   libtest prints the line after `test <name> ... `. That was fixed in
   `7ae258217`.
6. **Qualifying run after the first review, clean `1f6343694`**
   (`records/campaign-1f6343694/`), and a 201-target floor at the same source
   (`records/floor-1f6343694/`, 201/201 targets, 1,319 tests). The run's 49,996
   compared JIT rows are 44,996 interpreter-compared scalar rows plus 5,000
   consumer-shape rows. The run had no Cargo-config audit or case-count probe.
7. **Qualifying runs before any review, clean `e26b6e17d` and `b4ce6c61e`**
   (`records/campaign-e26b6e17d/`, `records/campaign-b4ce6c61e/`), and a
   200-target floor at `b4ce6c61e` (`records/floor-b4ce6c61e/`).
   `fuzz_macho_fixup` wrote a 10-second slow unit at `e26b6e17d`.
8. **Candidate floor targets, `d64dcdeb2`** (`records/pre-floor-families/`).
   All 35 fuzz targets passed with the floor's command and classifier: 250
   tests in 958 s.
9. **Findings** (`records/findings/`):
   - the LeakSanitizer input `0x0a 0x0a`, from the first smoke run, with its
     symbolized stacks;
   - `replays.txt`, which replays that input and the slow unit on the fixed
     build.
10. **Mach-O suites** (`records/macho-suites/`), before and after each change.
    - At `096aacc2f` (`macho-lib4.log`, `macho-suites4.log`,
      `macho-probe4.log`), the 250 `macho::` library tests and 11 integration
      targets pass. The six LLVM-built arm64 objects parse, and so does the
      rustc tail-merged object that the `c479e3d8a` bound refused. The
      second review's blow-up shape parses in 6.7 ms (debug build) with every
      name in one allocation. `objects/` holds the objects' sources. The probe
      test was not committed. The tail-merged object itself is a committed
      fixture.
    - At `7ae258217` (`macho-lib3.log`, `macho-suites3.log`), 246 `macho::`
      library tests and 11 integration targets passed under the bound that
      the third review refuted.
    - `main-check.log` shows three proof-dependent failures that unmodified
      `origin/main` `a559dd62c` shares.

The release-gate dry runs that an earlier revision of this archive held were
removed. They ran on `1f6343694`, not on the source their directory named, and
the release-gate integration was dropped from the branch.

## Records

- `campaign*/` holds each lane run's `report.json` and every build, control,
  family, libFuzzer and JIT log. It also holds the JIT run logs and every
  libFuzzer artifact (the controls' marker inputs, and the slow unit in
  `campaign-e26b6e17d/`).
- `floor*/` holds each floor run's `report.json` and one log per target.
- `controls-*/` holds the runs and harness results described above.
- `pre-floor-families/`, `findings/` and `macho-suites/` are as described in
  the list of runs.
- `harnesses/` holds the scratch scripts that ran all of the above, as run
  (`harnesses/round3/` for the third round).

libFuzzer corpora are not retained. Their sizes are in each `report.json`.
`inventory.json` lists every file with its SHA-256 and length, and, for a
gzip file, the stored and the decoded hash and length.

## Boundaries

This is testing evidence at fixed seeds and budgets on one host. It is not
coverage, proof, completeness or release qualification. libFuzzer's execution
counts vary with load at a fixed seed. AddressSanitizer (with LeakSanitizer)
is the only sanitizer. A quarter of the JIT differential's scalar rows test
only agreement between optimization levels.

No full Linux floor was run at the source of the latest qualifying run. The
Trust-mode floor ran its first twelve targets only. The lane is not part of
the public release checks. The Darwin rows added to the Darwin floor
inventory have not been run. Every L01–L14 row, L13-P7 included, remains OPEN
until closure evidence lands and the ledger is updated with
`scripts/closure_ledger.py`.
