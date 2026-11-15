# Bridge tests load their own Cargo backend (L06-P13) — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Row L06-P13 of the
closure ledger: bridge
integration tests reused any existing backend library without a staleness
check, and the ones that named `.dylib` could not run on Linux. Three commits
on origin/main `d64dcdeb2` repair it:

- `361f91e15` moves every bridge test's backend selection to
  `current_test_backend()` and adds a source lint.
- `01fa071c2` records the first Linux runs.
- `45f5b5b4f` repairs what an independent verifier found. The lane targets no
  longer build a backend into the shared target directory when run without
  the runner. The Darwin gate binds its fixtures to its snapshot again. The
  lint is stricter.

This directory retains the Linux AArch64 runs of that code. The ledger row is
not edited here.

Host `aarch64-unknown-linux-gnu`, Linux `6.17.0-1026-nvidia` (NVIDIA Grace, 20
cores shared with other jobs). Trust package `a62ae50d` (`trustc`/`targo`
`1.99.0-dev (a62ae50d8 2026-09-16)`), with the pinned AY/Clean prefix
`~/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin` on `PATH`.
Target directory `/home/ayates/trust-cg-wt/l06p13-target`, `-j 4`, release
profile, `--locked`, `RUSTC=<trustc>` for every `targo` call, as the lane does.

## Source identity

- **Round 1 lane (`records/lane/`).** It recorded source `d64dcdeb2` plus a
  tracked diff with SHA-256 `a0c35a5f…161b` and the untracked lint
  `006ee325…f977`. `git diff --binary d64dcdeb2 361f91e15` without the lint
  file hashes to the same `a0c35a5f…161b`, and the lint blob in `361f91e15`
  hashes to `006ee325…f977`. The runs therefore tested the committed code.
- **Round 2 lane (`records/lane-45f5b5b4f/`).** It ran on clean `45f5b5b4f`:
  `dirty: false`.
- **Round 2 builds and standalone runs.** They ran on an uncommitted working
  tree that differed from `45f5b5b4f` only in the bridge `README.md`, which
  was edited after the builds started.

## The lint

`scripts/tests/test_bridge_backend_selection.py` has 7 tests. Both rounds of
the verifier's plausible bypasses are negative self-tests, and the lint passes
on the final commit. It scans 340 sources, 145 of which call the selector in
code, with 10 allowlisted lines. The `45f5b5b4f` version accepted a selector
named only in a comment, and an environment read that rustfmt split across
lines; the final version checks the call on comment-stripped text and matches
the read across line breaks. That stricter check required `execution_budget`
to call the selector rather than pass it as a function value. It is a
regression lint for known spellings, not a proof.

| Input (`--scan`) | Result |
| --- | --- |
| origin/main `d64dcdeb2` tests | exit 1, 1,361 violations in 145 files (`records/guard/origin-main-scan-v2.txt.gz`) |
| first commit `361f91e15` tests | exit 1, 27 violations in 5 files: the three lane targets' nested builds, `backend_build_command` and `cargo_target_dir` (`records/guard/361f91e15-scan-v2.txt.gz`) |
| final commit | 7/7 pass; `--scan` of its tests reports 0 violations |

The first version's results remain in
`records/guard/origin-main-scan.txt.gz` (1,309 violations in 140 files) and
`one-file-reverted.txt.gz` (9 violations in the reverted file).

## Builds

| Command | Result |
| --- | --- |
| `targo --unverified build --release --locked -j 4` | pass; one pre-existing library warning (`BCE_TRACE` unused, `src/knobs.rs`) (`records/backend-build/backend-build.log.gz`) |
| `targo --unverified test --release --locked -j 4 --no-run` (all 146 test targets), round 1 and round 2 | pass. The only warnings are the library's and two pre-existing test warnings (`RunOutcome::Timeout` never constructed in `bridge_differential_x86.rs`; `Guest::what` never read in `real_program_corpus_a64`), identical in origin/main's sources (`records/backend-build/test-build-all-targets.log.gz`, `test-build-all-targets-round2.log.gz`) |

Cargo's `build` and `test` graphs each rebuild the release library in place
(`deps/librustc_codegen_trust_cg.so`). The lane tests its snapshot
`f9e46b99…6a23` in both rounds. The other default-features runs used the test
build's `ccbfe3c4…b692`, and the all-features run used `425d266e…dc17`
(`records/binaries.sha256`, `records/binaries-round2.sha256`).

## Maintained lane

Both rounds ran `python3 -B scripts/check_linux_aarch64_bridge.py
--target-dir <dir> --jobs 4 --require-proof-tools`, and both FAIL on the ABI
target alone, as on origin/main (`records/lane/`, `records/lane-45f5b5b4f/`).

| Target | libtest (both rounds) |
| --- | --- |
| `aarch64_c_fnabi_aggregate_linux` | 0 passed, 1 failed: `aliased_f32_read` O0 refused with `[TCG-PROOF-465]` (`StpPreIndex`, `StpRI`, `LdpRI`, `LdpPostIndex`), the known L06-P1 refusal |
| `tls_thread_local_linux` | 2 passed |
| `unwind_cleanup_linux` | 2 passed |

## Lane targets without the runner, and the nested-build false all-clear

`records/standalone/` holds two runs. Each is a `targo test` on the round-2
working tree with no `TCG_TEST_BACKEND_PATH`/`SHA256`, and a Cargo target
runner (`librunner.sh`) records the `deps/` library at each test executable's
start.

`standalone.sh` is kept as it ran. Its scratch directory is not archived, and
the `env.sh` it sources set only these values:

- `PATH` begins `/home/ayates/toolchains/trust-a62ae50d/bin`, then
  `$HOME/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin`, then
  `$HOME/.cargo/bin`;
- `TRUSTC` is `/home/ayates/toolchains/trust-a62ae50d/bin/trustc`;
- `TARGO` is `/home/ayates/toolchains/trust-a62ae50d/bin/targo`;
- `T` is `/home/ayates/trust-cg-wt/l06p13-target`;
- `M` is `/home/ayates/trust-cg-wt/l06p13/crates/rustc-codegen-trust-cg/Cargo.toml`.

- **Default features** (`default/`): six targets.
  - `aarch64_c_fnabi_aggregate_linux` fails at the same `[TCG-PROOF-465]`
    refusal.
  - `tls_thread_local_linux` and `unwind_cleanup_linux` pass 2/2. Their
    markers record backend `ccbfe3c4…`.
  - `codegen_emit_retag_refusal` 2/2, `execution_budget` 3/3 and
    `ssa071_shape_a_rescue` 6/6 pass.
  - The library was `ccbfe3c4…` before the run, at every target's start and
    after the run.
- **All features** (`allfeatures/`, the `run_public_release_checks.sh`
  configuration): `aarch64_c_fnabi_aggregate_linux` then
  `codegen_emit_retag_refusal`.
  - The test build produced library `425d266e…`.
  - `aarch64_c_fnabi_aggregate_linux` fails at the same refusal.
  - `codegen_emit_retag_refusal` passes 2/2.
  - Both targets started with `425d266e…`, and it was unchanged after the
    run.

Before `45f5b5b4f`, a target run without the pair built a default-features
backend into the shared target directory. The verifier's reproduction of that
(test build `e538d395…`, then `codegen_emit_retag_refusal` started with
`d802a6e3…`) is its own record; this directory keeps only the repaired runs.

## Every other bridge target (round 1, `361f91e15`)

Each test executable ran directly, as the lane runs its targets, with
`--nocapture --test-threads=2`, the crate as working directory and no `RUSTC`
or `TCG_*`/`TRUST_CG_*` variables (`records/sample/run_sample.py`,
`summary.jsonl`, `logs.tar.gz`). Round 2 changed none of these targets'
sources apart from removing unused support functions.

| Class | Targets |
| --- | --- |
| Pass, backend loaded and exercised on Linux | `codegen_emit_retag_refusal` 2/2, `execution_budget` 3/3, `ssa071_shape_a_rescue` 6/6, `m139_flatmap_bounded_x86` (its five host-native fail-closed canaries pass; its x86-64 run skips) |
| Pass, backend-free | `target_dir_resolution` 8/8 |
| Explicit skip only (libtest reports `ok`) | `hello_loop`, `coroutine_generator_aarch64`, `drop_heap_aarch64`, `static_data_aarch64`, `tls_thread_local_aarch64`, `unwind_cleanup_aarch64`, `real_program_corpus_a64` (each prints the missing `aarch64-apple-darwin` host or target library); 122 x86-64 targets (each backend test prints the missing x86-64 host or x86-64 `rust-std`; their backend-free unit tests pass) |
| Fails because it is Darwin-specific | none: every Darwin-specific target already skips by name |
| Fails on Linux at `[TCG-PROOF-465]` | `fat_pointer_lane_differential` 0/1, `virtual_call_aggregate_return_differential` 1/2, `dyn_fat_leaf_differential` 0/1, `boolean_knob_value_grammar` 0/1, `float_semantics` 2/4, `overflow_asserts` 0/9, `reference_union_semantics` 7/35, `unsupported_program` 4/9, `dom_bounds_dynamic_fail_closed` 0/1 |

The nine failing targets compile for the host without `no-proof-certs`, so
every function with a frame prologue is refused at proof promotion:
`[TCG-PROOF-465] … emitted opcode inventory found … uncovered non-pseudo
opcode(s) [AArch64::StpPreIndex, AArch64::LdpPostIndex, …]`. That is the
opcode wall recorded as L07-P2 and the refusal that fails the lane's ABI
target. `dom_bounds_dynamic_fail_closed` also names `AArch64::NeonStpQPost`.
Every failing test's panic message carries `[TCG-PROOF-465]`, except
`fat_pointer_lane_differential`, which records only the leading
`[TCG-MIR-UNSUPPORTED]` tag of each row. A direct compile of
`bridge_corpus/lane_types-slices-str-arrays_2.rs` at O0 shows 15
`[TCG-PROOF-465]` refusals (`records/repro/fl2.err.gz`). Four of the failing
files (`float_semantics`, `overflow_asserts`, `reference_union_semantics`,
`unsupported_program`) accept a `[TCG-PROOF-465]` refusal only on macOS and
only when it names the object relocation inventory
(`aarch64_macho_promotion_ratchet`). The Linux refusals name the opcode
inventory instead, so these tests fail rather than take that path.

No failing test reported wrong output, a divergence from LLVM, a crash, an
internal compiler error or a backend-load failure; every failure is a named
fail-closed refusal. The x86-64 targets and the Darwin-targeted AArch64
targets run no compiled program on this host.

## A separate fail-closed refusal: `[TCG-REGALLOC-063]`

With certificates on, any function whose EH metadata has unwind information
is refused with `[TCG-REGALLOC-063] … exception-handling sidecar unsupported
at code-only API module_relocation_inventory_report … (fail-closed)`.

- **Where.** It is raised at
  `crates/trust-cg-codegen/src/pipeline.rs:20415-20421`, called from
  `compiler.rs:12102`. That is before `ensure_object_proofs_promotable`
  (`compiler.rs:12118`) raises `[TCG-PROOF-465]`, so such a function reports
  063 instead of 465. The refusal is independent of the pair-opcode wall and
  would remain after L07-P2.
- **Here.** It refused `std::rt::lang_start`'s `FnOnce::call_once` shim in 2
  `unsupported_program` tests and in `m139_flatmap_bounded_x86`.
- **Reproduced.** `records/repro/frem.rs`
  (`fn main() { let _x = 5.0f64 % 2.0f64; }`, default `panic=unwind`) is
  refused with certificates on (`frem_certs.err.gz`). With
  `-Ztrust-ir-cg-args=no-proof-certs` it compiles, links and exits 0
  (`frem_nocerts.err.gz`).

## Boundary

- The lint reads source text. It does not show that any test passes or that
  a selected library is correct.
- Test-side selection is not proof, compiler or Trust-toolchain authority.
- The Darwin gate's executable-copy binding is unit-tested here with fakes.
  It has not run on a Darwin host.
- The lint does not cover scripts or benchmarks outside the bridge crate that
  default to backend paths in a Cargo profile directory; the list is in the
  completion plan.
- Every L01–L14 row remains OPEN.
