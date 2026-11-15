# CG-owned landing pads, cleanup and unwinding on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Ledger gap L03-P2. All records were produced on the Linux AArch64 host
(`aarch64-unknown-linux-gnu`, Ubuntu 24.04, NVIDIA Grace, kernel
`6.17.0-1026-nvidia`). The records under `records/floor/`, `records/lib/`,
`records/eh-linux/`, `records/prefix/` and `records/bridge/` were produced on
clean source `62234066b3ae51d68df63348c60608ed63610b3d` (base `4d7e2409a`
plus the code commit). The `*-fd1a09822` records were added by the
evidence repair described under [Repair](#repair-fd1a09822), on clean
source `fd1a098223ab4e9f1e349d3c4c8fa5007f37a48e`.
`records/prefix-per-function/` was produced on `fd1a09822` plus the probe
diffs it retains. `inventory.json` lists every file with its SHA-256 and
length; logs and JSON records are stored gzip-compressed and the inventory
records both the stored and the decoded hash.

## Premise re-check at the base

The ledger text was written at `ed3c5c94`. At `4d7e2409a` the four
`e2e_aarch64_eh_*` targets already ran their native legs on Linux GNU through
`tests/common/native_host.rs` (commit `14a3ba3a5`), and the base floor passed
them. Their coverage was one call per shape: catch-all, invoke catch and
cleanup-then-resume at O0, and both paths plus unwind-through at O2. Each
checked a return value or a single flag, with no in-frame destructor
accounting, no independent table readback and no negative control.
`e2e_aarch64_elf_eh_catch_object_emit` still documents the
`TCG_ELF_EH_DUMP` external-runner dump; its link-and-run half is
`e2e_aarch64_eh_catch_all_link_and_run`, which runs natively on Linux. The
Linux native exception test in `e2e_aarch64_elf_link` still passes C++
exceptions only through CG frames that own no handler. The bridge's
`unwind_cleanup_aarch64` is still Darwin-only.

## What the new target does

[`e2e_aarch64_eh_linux`](../../../crates/trust-cg-codegen/tests/e2e_aarch64_eh_linux.rs)
compiles two trust-ir modules for `aarch64-unknown-linux-gnu` at O0, O1, O2
and O3.

- **The C++ module** (personality `__gxx_personality_v0`) has five
  functions. `tc_catch` has a catch-all pad that calls `__cxa_begin_catch`,
  loads the payload's two words itself, reports them and returns
  `code + 1000`. `tc_cleanup` has a cleanup pad that runs a counted cleanup
  and resumes. `tc_nested` is a CG catch around the CG cleanup frame.
  `tc_mid` is a plain CG frame with no handler, and `tc_through` is a CG
  catch around that plain frame.
- **The Rust module** declares `rust_eh_personality`. Its `tr_cleanup`,
  `tr_nested` and `tr_through` cleanup pads resume a real Rust panic, and
  `tr_mid` is a plain frame.

The **C++ -> CG -> C++ rows** link the object first, so its weak `DW.ref`
slot is the one kept, with a `g++` driver against libstdc++/libgcc_s. The
callee throws a counted `Payload` from a frame with a RAII guard, and the
caller has its own guard and a typed catch. Every function runs on all eight
arguments; odd arguments throw and even ones return. Each line must equal the
model exactly: the return value or caught payload, the payload words read by
the CG pad, the ordered stage list (CG stages, callee guard, payload
destructor, caller guard, caller handler), the cleanup count and sum, the
payload constructions and destructions, `std::uncaught_exceptions()` and
`std::current_exception()`. That makes 160 calls and 100 exceptions.

The **Rust -> CG -> Rust rows** build a Rust harness with the checkout's
stock `rustc` 1.97.1 at the matching `-C opt-level` and link the CG object
into it. The callee is `extern "C-unwind"` and raises `panic_any(Payload)`
from a frame with a `Drop` guard; a counting panic hook replaces the default
one. `catch_unwind` in `main` catches the panic and downcasts the payload,
whose `Drop` is a stage. That makes 128 calls and 80 panics. No rustc bridge
is involved.

**Independent readback, per level.**

- GNU readelf reads the relocatable object: a `zPLR` CIE whose personality
  encoding is `0x9b`, one PREL32 against `DW.ref.<personality>`, one PREL32
  per FDE to `.text` and to `.gcc_except_table` (resolved through `r_info`
  and the section symbols), and one `R_AARCH64_ABS64` from the slot to the
  personality.
- In the linked executable, llvm-dwarfdump and GNU readelf must agree on each
  CG function's FDE range and LSDA address. The CIE's personality address
  must be the `DW.ref` symbol, bound by a dynamic relocation to the
  personality.
- The LSDA bytes at that address are decoded by the test's own decoder, not
  the compiler's, and must re-encode byte for byte. Their rows must cover the
  one invoke `bl` that llvm-objdump disassembles in each function with its
  landing pad and the pad's action: a catch-all takes filter 1 to a NULL
  type entry, a cleanup takes action 0. Every other call must be covered by
  a no-handler row.

**Host-neutral rows.** The same decoding runs on every host over the
relocatable objects, with this file's own ELF reader. They also pin that every
`BL _Unwind_Resume` is followed by `BRK #1`, and two named refusals:

- EH metadata whose personality is absent or empty ("contains EH opcodes but
  has no personality symbol", O0-O3);
- a block that ends in an invoke but makes another call first ("exactly one
  is required by block-granular metadata").

**Negative controls on the linked executable.** There are 20 invoke calls:
`tc_catch`, `tc_cleanup`, `tc_nested` and `tc_through` at O0-O3 (16) and
`tr_cleanup` at O0-O3 (4). Each call runs the unmutated image once as a
reference, which must match the model, and then two mutated images. That is
40 mutated images (20 dropped-row, 20 retargeted-pad; 32 C++, 8 Rust) and 20
unmutated reference runs, 60 executions in all. The reference runs are not
counted as controls.

- *Dropping the invoke's LSDA row.* The row is removed and the LSDA is
  re-encoded in place. For the four C++ functions with an invoke this ends
  in SIGABRT with `terminate called after throwing an instance of 'Payload'`
  and no output. For `tr_cleanup` it ends in SIGABRT with `fatal runtime
  error: failed to initiate panic`.
- *Retargeting the invoke's landing pad to the call's return address.* The
  function then resumes on its normal path with the exception still in
  flight: the normal-path stages appear, and `uncaught=1`, or `hook=1` with
  no cleanup for Rust.

`records/eh-linux-fd1a09822/mutations-execve-summary.txt` counts the
executions under `strace -f -e trace=execve`: `eh_cxx` 16 and `eh_rust` 4
reference runs, and 20 dropped-row and 20 retargeted-pad images.

**Missing personality runtime.** A cleanup-only C++-personality object and
the Rust-personality object are linked by `cc` against a C driver at O0 and
O3. Each link fails with exactly one undefined reference, the personality.
The same C++ object links under `g++` and prints `84`.

## The lowering defect the fixtures exposed

Before the code commit, the whole-module run (`records/prefix/enforce.log`)
refused `tc_cleanup` and `tr_cleanup` at O0, the first level each row
reached; a row stops at its first failing level, and a module compile stops
at its first failing function, so that log carries no O1-O3 or `tr_nested`
and `tr_through` evidence:

```text
[TCG-A64-SPILL-SLOT] fn `tc_cleanup` final AArch64 stream spill-slot
violation (caller-callee-saved-value-read): block 3 inst #4 (AddRI):
consumes x20 (w20) which may still hold the caller's callee-saved value
```

AArch64 `select_resume` ended the pad with `BL _Unwind_Resume` and no
terminator. The final-layout CFG (`derive_ir_cfg_edges_from_branch_operands`)
therefore gave the pad a fallthrough edge into the next laid-out block, and
the frame net merged the pad's state into the normal block, which reads the
invoke result from `x20`. The x86-64 selector already ends `Resume` with
`UD2` for this reason. The fix ends the AArch64 pad with `BRK #1`.
`records/prefix/` is the control. `prefix-control.diff` removes only the
`BRK` emission at the code commit.

- `enforce.log`: 9 of the 10 rows fail on the refusal above. Only the
  personality refusal, which stops before instruction selection, passes.
- `warn.log`: with `TCG_AARCH64_POST_RA_SPILL_SLOTS=warn`, the execution,
  readback and mutation rows pass. The fallthrough was latent at run time,
  because `_Unwind_Resume` does not return. The host-neutral object rows
  fail on `BL _Unwind_Resume at 0x4c must be followed by BRK #1`, so the pin
  detects the regression.

`records/prefix-per-function/` covers every function and level. A temporary
probe test (`probe.diff`, not committed to the target) compiles each of the
nine fixture functions on its own at O0-O3: the probe module keeps one
definition and turns the module's other definitions into external
declarations of the same signature. With the same `prefix-control.diff`
applied (`prefix.log`), 16 of the 36 compiles are refused and 20 compile.
The refused ones are exactly the four cleanup-then-resume functions at every
level: `tc_cleanup`, `tr_cleanup` and `tr_nested` on
`caller-callee-saved-value-read`, and `tr_through` on
`return-lane-holds-caller-value` (return/argument lane `w0` may hold a
caller's callee-saved value). The five functions without a `Resume`
(`tc_catch`, `tc_nested`, `tc_mid`, `tc_through`, `tr_mid`) compile at every
level. Without the prefix diff (`fixed.log`) all 36 compile. This is a
compile-time refusal probe on single-definition modules; the execution
evidence for the full modules is the transcript under `records/eh-linux/`.

The change was restored with `git checkout` after the control.

## Records

- **`records/floor/`: the Linux floor.** `scripts/check_linux_aarch64.py
  --jobs 8 --require-clean --max-rss-gib 16 --require-offline-deps
  --require-proof-tools` passed all **149 required targets and 906 tests**,
  from 13:24:50Z to 13:36:11Z with 667 s of target wall time. The source
  fingerprint `d4a240d68084ce4b70ae83d72239f18de1da1a75524a9c235c87aab1e74bd72c`
  and the dependency and AY/Clean identities were the same before and after.
  The highest sampled resident set was 224 MiB.
  - `e2e_aarch64_eh_linux` passed 10/10.
  - The existing EH families passed unchanged: `e2e_aarch64_eh_catch` 7,
    `e2e_aarch64_eh_invoke_trust_ir` 5, `e2e_aarch64_eh_resume_trust_ir` 5,
    `e2e_aarch64_eh_o2_and_walkthrough_trust_ir` 6 and
    `jit_exception_handling` 11.
- **`records/lib/`: library suites.** `cargo test -p trust-cg-codegen -p
  trust-cg-lower --lib` passed codegen 4,113 with 1 ignored (the
  pre-existing `raw_machir_request_cache_real_exhaustive_campaign`) and
  lower 1,879. The lower suite includes the updated
  `select_resume_calls_unwind_resume`, which requires `BL _Unwind_Resume;
  BRK`.
- **`records/eh-linux/`: the new target, run alone.** This is its serial
  `--nocapture` transcript. The evidence lines are:
  - `EH_LINUX_CXX calls=160 exceptions=100`;
  - `EH_LINUX_RUST calls=128 panics=80`;
  - `EH_LINUX_TOOL_READBACK functions=36`;
  - `EH_LINUX_OBJECT_TABLES functions=36 resumes=16`;
  - `EH_LINUX_CXX_MUTATIONS controls=48` and `EH_LINUX_RUST_MUTATIONS
    controls=12`. These counters added 3 per invoke call, so they include
    the 16 and 4 unmutated reference runs: the mutants are 32 and 8. The
    `fd1a09822` transcript prints the counts separately;
  - `EH_LINUX_PERSONALITY_REFUSALS refusals=8` and
    `EH_LINUX_PERSONALITY_LINK_REFUSALS refusals=4`.

  The directory also holds the host tool identities (`g++`/`cc` 13.3.0, GNU
  readelf 2.42, llvm-dwarfdump/llvm-objdump 18.1.3, `rustc` 1.97.1) and their
  SHA-256 hashes.
- **`records/prefix/`.** The pre-fix control described above.
- **`records/bridge/`: the rustc bridge lane.** Because `Resume` lowering is
  shared, `scripts/check_linux_aarch64_bridge.py --require-proof-tools`
  rebuilt the backend with the sealed Trust `a62ae50d` package. The backend
  SHA-256 was `145e416a671939a101a65e9f71f7d1efa43c68793b68831e61264e458a62bad1`;
  the library is identified here, not archived.
  - `tls_thread_local_linux` passed 2/2.
  - `aarch64_c_fnabi_aggregate_linux` still fails only at the known
    `aliased_f32_read` O0 `[TCG-PROOF-465]` refusal (L06-P1).

  The lane verdict is FAIL for that reason alone, the same as at the base.

`harnesses/archive-eh-landing-pads-20260923.py` built this archive from the
capture directories, and
`harnesses/archive-eh-landing-pads-repair-20260923.py` added the repair
records without touching the original ones.

## Repair (fd1a09822)

An adversarial review found two overstatements in the first write-up, both
corrected here, in the plan, in the CHANGELOG and in the L03-P2 ledger note.

- **Mutation count.** The prose called all 60 executions of the two
  mutation tests mutation or negative controls. Only 40 run a mutated image
  (see above). `fd1a09822` changes only the test's counters: each test now
  counts dropped, retargeted and reference runs, asserts 16/16/16 (C++) and
  4/4/4 (Rust), and prints them separately. No assertion was weakened and
  no shape was dropped.
- **Pre-fix scope.** The claim that every cleanup function was refused at
  O0-O3 went beyond `records/prefix/enforce.log`, which shows O0 only. The
  per-function probe above now supports it for the four cleanup-then-resume
  functions, and records that `tr_through` is refused by a different check
  (`return-lane-holds-caller-value`).

Records produced on `fd1a09822`:

- **`records/eh-linux-fd1a09822/`.** The target's serial `--nocapture`
  transcript (10 passed), with `EH_LINUX_CXX_MUTATIONS mutants=32 dropped=16
  retargeted=16 unmutated_references=16` and `EH_LINUX_RUST_MUTATIONS
  mutants=8 dropped=4 retargeted=4 unmutated_references=4`; every other
  evidence line is unchanged. The `strace` execve trace of the two mutation
  tests and its per-image summary are retained beside it.
- **`records/floor-fd1a09822/`.** The Linux floor, run with the same
  options (`--jobs 8 --require-clean --max-rss-gib 16
  --require-offline-deps --require-proof-tools`). It passed all **149
  required targets and 906 tests**, from 14:37:17Z to 15:04:12Z with 1,605 s
  of target wall time on a host shared with other builds. The source
  fingerprint `0f92bdf590be972376d15f2bf0934956264adc17e470532fd851e84e176ff538`
  was the same before and after, and the highest sampled resident set was
  6,562 MiB, under the 16 GiB ceiling. `e2e_aarch64_eh_linux` passed 10/10
  and printed the new mutation lines. `report.json`, the gate's stdout and
  every per-target log are retained.
- **`records/lib-fd1a09822/`.** `cargo test -p trust-cg-codegen -p
  trust-cg-lower --lib`: codegen 4,113 passed with 1 ignored (the
  pre-existing `raw_machir_request_cache_real_exhaustive_campaign`), lower
  1,879 passed.
- **`records/prefix-per-function/`.** The probe described above, run on
  `fd1a09822` plus `probe.diff` (`fixed.log`) and plus `probe.diff` and
  `prefix-control.diff` (`prefix.log`). The tree was restored with
  `git checkout` afterwards.

The bridge lane was not rerun: `fd1a09822` changes only a codegen test file
and the CHANGELOG, and neither enters the bridge build.

## Boundary

This is native execution, tool readback and mutation evidence for these
fixtures on one host. It does not prove LSDA, personality or unwinder
correctness.

- **Pad kinds.** Only catch-all and cleanup pads are covered. Typed
  catches, filters and mixed personalities stay refused (L03-P11).
- **Invoke blocks.** A block that ends in an invoke and makes another call
  is refused by name, not lowered.
- **Rust path.** It uses a stock-`rustc` harness around a CG object, not the
  rustc bridge. The bridge's `unwind_cleanup` twin remains Darwin-only
  future work.
- **Other hosts.** The Mach-O EH native legs were not rerun on macOS after
  the `BRK` change. The new target's four host-neutral rows are registered
  on the Darwin floor but have not run on Darwin.

L03-P2 stays PARTIAL, and every L01–L14 row remains OPEN.
