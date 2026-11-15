# Linux rustc-bridge unwind and cleanup lane — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

L03-P2 residuals from the 2026-09-24 closure audit. The maintained
`scripts/check_linux_aarch64_bridge.py` gate ran on clean source
`92173b47d7a861c6d3eb1b0a75b3d6366e887f83` (origin/main `3be0b17c6` plus the
commit that adds
[`unwind_cleanup_linux`](../../../crates/rustc-codegen-trust-cg/tests/unwind_cleanup_linux.rs)
and makes it the runner's third required target, and the commit that moves an
invoke following another call into a block of its own), with the sealed Trust
`a62ae50d` package and `--require-proof-tools`. The runner verdict is
**FAIL**, from the ABI target alone:

| Required target | Verdict | libtest |
| --- | --- | --- |
| `unwind_cleanup_linux` | **pass** | `test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 74.09s` |
| `tls_thread_local_linux` | **pass** | `test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 50.56s` |
| `aarch64_c_fnabi_aggregate_linux` | fail (pre-existing, L06-P1) | `test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 69.61s` |

The ABI target fails where the
[2026-09-23 TLS run](../2026-09-23-linux-bridge-tls/README.md) recorded:
`aliased_f32_read` at O0 is refused with `[TCG-PROOF-465]` (`StpPreIndex`,
`StpRI`, `LdpRI`, `LdpPostIndex` without a proof mapping). The runner runs every
target against the same backend snapshot whatever the others' verdicts and
records `target_status` per target.

## What the unwind target established

The crate is the Darwin control's `UNWIND_CRATE` and `PANICKER_CRATE`,
byte-identical, plus `guards_across_unwind(n)` (a user-`Drop` `Guard` and a
`Box<Guard>` live across `panicker::ay_unwind_if(n)`, which panics with a
24-byte typed payload when `n != 0`) and `nested_unwind(n)` (a `Guard` and a
`Box<i64>` live across a call to `guards_across_unwind`). Sources:
`records/unwind-artifacts/unwind.rs`, `panicker.rs`, `driver.rs`.

- **MIR.** The O0 MIR of all three fixture functions has an `unwind: bbN` edge
  into a `(cleanup)` block (`records/unwind-artifacts/unwind.mir.gz`).
- **CG, O0–O3** (backend through `-Zcodegen-backend=<snapshot>` and
  `-Ztrust-ir-cg-args=no-proof-certs`, `-Ccodegen-units=1 -Cpanic=unwind
  -Cforce-unwind-tables=yes`). Eleven objects per level; the allocator shim
  is excluded by its `__rust_alloc` definition and ten are linked. Each
  fixture function's object has `.gcc_except_table`, an `.eh_frame` FDE whose
  `R_AARCH64_PREL32` LSDA pointer targets that section, a CIE naming
  `DW.ref.rust_eh_personality`, whose slot has an `R_AARCH64_ABS64` to
  `rust_eh_personality`, and a `BL _Unwind_Resume`. Its LSDA rows cover
  `[0, size)` contiguously; exactly one covers the `R_AARCH64_CALL26` to the
  panicking callee, with length 4, a landing pad inside the function and
  action 0. LSDA rows per function: 3 / 11 / 7 at O0, 3 / 9 / 5 above.
- **Execution.** The objects are archived and linked into the LLVM-compiled
  Rust driver through `trustc` (`-l static=bridgeunwind`), and each fixture
  function's linked definition has the selected object's size. Three runs per
  executable print exactly:

  ```
  box_across_unwind() caught str:boom from panicker drops=[] box_i32=1/1 box_i64=0/0 hooks=1 late=0
  guards_across_unwind(0) returned 41 drops=[2, 1] box_i32=1/1 box_i64=0/0 hooks=0 late=0
  guards_across_unwind(3) caught payload:21:ay_unwind_if payload drops=[2, 1] box_i32=1/1 box_i64=0/0 hooks=1 late=0
  nested_unwind(0) returned 82 drops=[2, 1, 10] box_i32=1/1 box_i64=1/1 hooks=0 late=0
  nested_unwind(-2) caught payload:-14:ay_unwind_if payload drops=[2, 1, 10] box_i32=1/1 box_i64=1/1 hooks=1 late=0
  ```

  (`box_i32` counts 4-byte, 4-aligned allocations/frees, the `Box<i32>` and
  `Box<Guard>`; `box_i64` 8/8; `late` any tracked allocation while the payload
  is inspected.)
- **LLVM twin, O0–O3.** One object; O0 prints the same. At O1–O3 LLVM removes
  the allocation of the two never-read boxes (`box_across_unwind`'s
  `Box<i32>`, `nested_unwind`'s `Box<i64>`), so those counts read `0/0`
  (`elided_box_frees` 3 per run); every other field is identical.
- **Missing landing pad, 12 controls.** For each fixture function and level a
  copy of its object with the protecting row's landing pad rewritten as a
  same-length ULEB128 zero is linked instead. The panic is still caught with
  the same payload, and the output differs from the model by exactly that
  frame's cleanups: `box_across_unwind` loses its free
  (`box_i32=1/0`), `guards_across_unwind` loses drops 2 and 1 and the
  `Box<Guard>` free in both of its panicking calls, and `nested_unwind` loses
  drop 10 and the `Box<i64>` free.
- **Refusal, O0–O3.** With `-Ztrust-ir-cg-args=no-proof-certs disable-unwind`
  the bridge exits 1 with `[TCG-MIR-UNSUPPORTED]` and one row
  `- <function>: TerminatorKind::Call with cleanup unwind` per fixture
  function (also the three `Box::new` monomorphizations), and no object
  defines a fixture function.

The marker `TCG_BRIDGE_UNWIND_EXECUTION` in `records/runner/unwind-native.log`
carries the 8 lanes, 12 controls and 4 refusals; the runner verified each
against its obligations.

**Retained artifacts.** The runner's own run removes the test's artifacts
directory on success. `records/unwind-artifacts/` comes from a second run of
the runner's exact test executable (SHA-256 `0d70a9ea…`) against the runner's
backend snapshot (`4288b580…`) with `UNWIND_CLEANUP_LINUX_KEEP_ARTIFACTS=1`,
the same environment and `TMPDIR` under the scratch directory; its marker is
byte-identical to the runner's (`test-transcript.log.gz`).

## Residual 2: an invoke after another call

`records/eh-linux/` holds the root-workspace evidence for the adapter change
(the design and the options weighed are in the plan's section "L03-P2 Linux
rustc-bridge unwind and cleanup — 2026-09-24"):

- `e2e-eh-linux-and-catch.log.gz`: `e2e_aarch64_eh_linux` 11/11 and
  `e2e_aarch64_eh_catch` 9/9 at `92173b47d` with `TCG_REQUIRE_LLD=1
  TCG_REQUIRE_GOLD=1`. It prints `EH_LINUX_MERGED_INVOKES moved=2`,
  `EH_LINUX_CXX calls=192 exceptions=120`, `EH_LINUX_RUST calls=160
  panics=100`, `EH_LINUX_OBJECT_TABLES functions=44 resumes=20`,
  `EH_LINUX_TOOL_READBACK functions=44`, `EH_LINUX_CXX_MUTATIONS mutants=44
  dropped=20 retargeted=20 moved=4 unmutated_references=20`,
  `EH_LINUX_RUST_MUTATIONS mutants=20 dropped=8 retargeted=8 moved=4
  unmutated_references=8`, and the remaining refusal at O0–O3 (`EH call block
  BlockId(0) contains 3 eligible BL/BLR calls; exactly one is required by
  block-granular metadata`).
- `split-disabled-control.log.gz` with `split-disabled-control.diff`: the same
  targets with only the new split disabled. `tc_merged` and `tr_merged` are
  refused by name at O0, the first level reached (`EH call block BlockId(0)
  contains 2 eligible BL/BLR calls`), and 9 of the then 10
  `e2e_aarch64_eh_linux` tests fail: the adapter-shape row and every row that
  compiles either module. Only the missing-personality refusal row passes.

`records/root/` holds `cargo test -p trust-cg-codegen --lib` (4204 passed,
1 ignored), the narrow regression over every root target that builds invokes
(`trust-cg-lower` all targets; 11 `trust-cg-codegen` and 4 `trust-cg-verify`
targets; 54 suites, 2704 tests, no failure) and the three gate unit-test
suites (108 tests, 1 skipped). The library and regression runs ran on the
working tree before the commits, with the adapter as committed; the
regression's `e2e_aarch64_eh_linux` then had 10 tests (the
selection-introduced refusal row was added after it and is in the clean run
above). The gate unit tests ran on clean `92173b47d`.

## Follow-up at `98288392a`

An independent verifier passed `aee975a5f`, `92173b47d` and `3484ad441` and
asked for four corrections and two adjacent repairs (see the plan section).
They are commit `98288392a2a52f48553e53476b12991ae14475da`, and
`records/followup/` holds their runs:

- `eh-linux/e2e-eh-linux-and-catch.log.gz`: `e2e_aarch64_eh_linux` 12/12 and
  `e2e_aarch64_eh_catch` 9/9 at `98288392a`, `TCG_REQUIRE_LLD=1
  TCG_REQUIRE_GOLD=1`. New: `tc_early`/`tr_early`, whose earlier plain call
  throws or panics on odd input, so in 20 C++ and 20 Rust calls the exception
  passes the frame's pad to the caller with the pad's cleanup not run
  (`EH_LINUX_CXX calls=224 exceptions=144 past_pad=20`, `EH_LINUX_RUST
  calls=192 panics=124 past_pad=20`); a mutant copying the invoke's pad onto
  the earlier call's row is killed at every level
  (`EH_LINUX_CXX_MUTATIONS mutants=56 dropped=24 retargeted=24 moved=4
  copied=4 unmutated_references=28`, `EH_LINUX_RUST_MUTATIONS mutants=32
  dropped=12 retargeted=12 moved=4 copied=4 unmutated_references=16`); and
  the adapter-emitted `frem` and i128 cast calls split while i128
  `udiv`/`srem` stay refused (`EH_LINUX_ADAPTER_CALL_SPLITS compiled=16
  refused=8`). `EH_LINUX_OBJECT_TABLES functions=52 resumes=24`,
  `EH_LINUX_TOOL_READBACK functions=52`.
- `eh-linux/split-disabled-control.log.gz`, `…-per-function-probe.log.gz`
  and the probe's source `…-probe.rs.gz` (a temporary test, not committed):
  the follow-up source with only the split disabled (the diff in
  `records/eh-linux/split-disabled-control.diff`), before the commit. 10 of
  the 12 tests fail; each of `tc_merged`/`tr_merged` ("2 eligible BL/BLR
  calls") and `tc_early`/`tr_early` ("3 eligible") is refused by name at
  O0–O3 when compiled alone.
- `root/`: `cargo test -p trust-cg-codegen --lib` (4204 passed, 1 ignored),
  `cargo test -p trust-cg-lower` all targets (39 suites, 2539 tests) and the
  three gate unit-test suites (108 tests, 1 skipped), at `98288392a`.
- `x86-f16/`: the `ty_primitives.tmbc` conformance fixture compiled for
  `x86_64-unknown-linux-gnu` at O0–O3 by a CLI built from the follow-up
  source before the commit: each is refused with `[TCG-X86-F16-ABI]` where it
  used to panic.
- `runner/`: the bridge runner on clean `98288392a` with
  `--require-proof-tools`: FAIL from the ABI target alone (L06-P1,
  `[TCG-PROOF-465]` at `aliased_f32_read` O0); `unwind_cleanup_linux` and
  `tls_thread_local_linux` pass 2/2 against backend
  `13b42dbf132c0af6feadeec5658b2178935c3b11e19d1c8de007bf6728b125ac`
  (`binaries.sha256`). The ABI target now removes its artifacts directory
  after its failure (the path its log names no longer exists).

## Identities and controls

- Host `aarch64-unknown-linux-gnu`, Ubuntu 24.04.4 LTS, kernel
  `6.17.0-1026-nvidia`, glibc 2.39, GNU `cc`/`g++` 13.3.0, GNU binutils 2.42.
- `trustc -vV`: `rustc 1.99.0-dev (a62ae50d8 2026-09-16) (trustc 0.1.0)`,
  commit `a62ae50d8bd2b990650db2cf0dd25019c67c6ed8`; `trustc`/`targo` from
  `~/toolchains/trust-a62ae50d/bin`, first on PATH. The root workspace used
  stock `rustc 1.97.1 (8bab26f4f 2026-07-14)`.
- Backend: a fresh locked release build of the committed source (4 m 36 s,
  warm dependency cache), snapshotted read-only in the report directory and
  passed to each test by path and SHA-256
  `4288b5801b76f1262fd9073b2659883fa1fe550477f8b0c6002a7d8f4b6fa574`,
  identical before and after each target. Cargo's test build then replaced the
  mutable cache library (`2bdcea41…`); that copy was not tested.
- AY `ec2bf181c384bff0453487b47781fb6d40b959a72c1236bdc760ccc1feee4830` and
  Clean `8d819378eb80696a6a753980bb1722de676f283c4219887f769ac70868f0fff8`
  resolved through the `aterm-packaged` route, unchanged across the run.
- Source fingerprint `0d501c2e…`, clean and identical after the build, the
  test build and the tests. Controls: `--require-proof-tools`, `--jobs 12`,
  `--timeout-seconds 2400`, `env -i` with a run-local `XDG_CACHE_HOME`; every
  `TCG_*`/`RUSTC*`/`RUSTFLAGS` override absent.

## Trusted base and evidence boundary

This is native testing evidence for the bridge's Linux unwind/cleanup lane and
for the adapter's invoke split, not a proof. The toolchain is unqualified
(owner decision OD-01 is pending). The frontend ran with `-Ztrust-verify=off`,
the backend was built by `targo --unverified`, and the bridge ran with
`no-proof-certs`, so no object carries a certificate. The LSDA rows, FDEs and
personality references are unproven object-side facts read with GNU
`readelf`. The Rust runtime (`rust_eh_personality`, libgcc's unwinder), GNU
`ld`, and the LLVM-compiled driver and panicker are trusted. The catch is in
the driver; `catch_unwind` inside a bridge frame is refused by the bridge.
The x86-64 selector receives the same adapter output but was not run.

The ledger row L03-P2 is not edited here. L06-P1 (the ABI target's proof
refusal) is unchanged. No existing gate, assertion, floor or denominator was
weakened; the Darwin floor minimum for `e2e_aarch64_eh_linux` rose from 4 to 5.

## Records

- `records/runner/`: `report.json`, `build.log`, `test-build.log`,
  `native.log` (ABI target), `tls-native.log`, `unwind-native.log` and the
  console log. The backend snapshot is identified by hash, not archived.
- `records/unwind-artifacts/`: the retained run's complete text output:
  sources, MIR, per-lane compile/archive/link/run logs, `readelf -sW/-SW/-rW`
  dumps of every object, the linked executables' symbol tables, the
  missing-landing-pad controls' logs and the refusal logs. Objects, archives,
  rlibs and executables are excluded; `records/binaries.sha256` lists their
  SHA-256.
- `records/eh-linux/` and `records/root/`: see above.
- `runner-source/`: the runner and the unwind target at the recorded commit.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-24-linux-bridge-unwind
PATH="$HOME/toolchains/trust-a62ae50d/bin:$PKG/bin:$HOME/.cargo/bin:$PATH" \
  python3 scripts/check_linux_aarch64_bridge.py --require-proof-tools --out /path/outside/source \
    --target-dir /path/outside/source/cache --jobs 12 --timeout-seconds 2400
```
