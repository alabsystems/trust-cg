# Linux x86-64 baseline and first repairs — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The first measured state of trust-cg on a native `x86_64-unknown-linux-gnu`
host, and the repairs that measurement forced. Before this session no Linux
x86-64 execution, bridge or self-host record existed: every x86-64 bridge test
pinned `x86_64-apple-darwin`, the perf ledger's only x86 rows are macOS, and
the completion plans cover AArch64 only. Nothing here closes a completion row;
the Linux x86-64 completion plan
records what remains.

## Host and toolchains

| Item | Identity |
| --- | --- |
| Host | `x86_64-unknown-linux-gnu`, Linux 7.0.0-31-generic, 24 cores, 61 GiB, Ubuntu gcc 15.2.0; no clang |
| trust-cg source | `166093c1a` plus the uncommitted repairs listed below |
| Root toolchain | stock Rust 1.97.1 (`rust-toolchain.toml`), rustup proxies |
| Trust compiler | tree-built stage2 `trustc 1.99.0-dev (3a3e781fe 2026-09-14)`, `trust: 0.1.0`, at `$HOME/trust/build/x86_64-unknown-linux-gnu/stage2` (rustup `trust` link); explicit unverified frontend lane (`-Ztrust-verify=off`) for every compile |
| Trust's trust-cg pin | `first-party/trust-cg` at `9da5e237` (the census script records this pin; the backend measured is this checkout) |
| AY | `ay 0.26.0+build.9624` from the stage2 sysroot |
| Clean | the stage2 `clean 0.9.0` lacks `carcara-verify`; a `carcara-verify` build of the Trust-pinned `first-party/clean` (`ec4b05723`) was dev-linked (see below) |

## Host repairs required before anything measured

1. **Three root test targets did not compile on x86-64 Linux** under the
   workspace's `-D warnings`: `e2e_aarch64_link_runtime` (a helper used only
   under the AArch64 native cfg), `jit_x86_64_aggregate_abi_fail_closed`
   (65 `trust_ir::Function` literals missing the v42 `body_gate`/`display_path`
   fields; the target is `#![cfg(target_arch = "x86_64")]`, so no AArch64 host
   could see it) and `static_indirect_devirtualization` (an import used only
   on AArch64). All three are fixed in this tree.
2. **`cc` on this host is `zig cc`** (`~/.local/bin/cc`), which rejects the
   `--exclude-libs` argument rustc passes when linking the bridge dylib. The
   bridge is built and tested with `/usr/bin` first on `PATH`.
3. **The Trust sysroot's Clean checker has no `carcara-verify`**, so every
   solver UNSAT verdict was unpromotable and every x86-64 guard-carrier
   expansion (`Bounds`, `DivZero`) failed closed at O0/O1. trust-cg's
   discovery accepts only `store/clean/current/bin/clean` in an aterm package
   prefix or the running executable's Trust sysroot, and `trustc` refuses
   `TCG_*` environment overrides, so the repaired checker was built with
   `targo --unverified build --release --locked -p clean --bin clean --features carcara-verify`
   in `$HOME/trust/first-party/clean` and placed at
   `~/.local/share/aterm/pkg/store/clean/current/bin/clean` (a symlink; atpkg
   publishes no `clean`/`ay` for this target). This is a machine-local
   development installation, not a qualified toolchain (plan row X12).

## Bridge smoke on Linux x86-64 (`smoke_run.sh`)

A `#![no_std]`/`#![no_main]` compute program (`wrapping_mul`/`xor` loop,
`% 100`) compiled through the bridge for `x86_64-unknown-linux-gnu`, linked
with gcc and executed:

| Lane | Before the checker repair | After |
| --- | --- | --- |
| LLVM oracle | exit 55 | exit 55 |
| bridge O0 / O1 | refused: guard-carrier `DivZero` canary, solver verdict uncheckable | exit 55 / exit 55 |
| bridge O2 / O3 | exit 55 / exit 55 | exit 55 / exit 55 |
| std `fn main` with `Vec`/`println!`, O0 | refused (checker) | refused: `[TCG-PROOF-465]` on `__rust_no_alloc_shim_is_unstable_v2`, an empty function (see repair 3 below) |

The emitted objects are `ELF 64-bit LSB relocatable, x86-64`.

## `library/core` refusal census (`census/`)

`scripts/trust_ir_cg_census.py` from the Trust checkout, `-Copt-level=0
-Cpanic=abort -Ccodegen-units=1 -Ztrust-verify=off`, certificates on, backend
`target/release/librustc_codegen_trust_cg.so` of this checkout.

| Run | Emitted objects | Failed roots | Distinct reasons | Wall |
| --- | --- | --- | --- | --- |
| `core-x86_64-linux-O0` (stage2 checker) | 2,706 | 726 | 28 | 41 s |
| `core-x86_64-linux-O0-checker` (carcara checker) | 2,810 | 622 | 28 | 74 s |
| `core-x86_64-linux-O0-pair` (rebuilt dylib `9baba785…`, repairs 1 and 3 below) | 3,097 | 335 | 28 | 72 s |
| `core-x86_64-linux-O0-relro` (repairs 5 and 6) | 3,097 | 335 | 28 | — |
| `core-x86_64-linux-O0-boolmask` (repair 8) | 3,097 | 335 | 28 | — |

The 104 roots that disappeared were all `[TCG-REGALLOC-063]` guard-carrier
canary refusals (91 `Bounds`, 14 `DivZero`, one shared). Ranked reasons after
the checker repair:

| Reason | Roots | What it is |
| --- | ---: | --- |
| `[TCG-RET-ABI]` | 282 | rustc `PassMode::Pair` returns (`Option<u8>` 44, `Option<u16>` 39, `Option<u32>` 75, `(u32,u32)`, `ControlFlow`, `Result<u8,_>`, ...) declared as one lane-tuple value; two-register pair lane was AArch64-only |
| `[TCG-PROOF-465]` | 102 | proof promotion rejected: `.static.anchor` functions and other empty bodies have no genuinely discharged instruction proof (x86-64 only vacuity rule) |
| `[TCG-REGALLOC-063]` | 45 | 36 `Array(I8, N)` by-value aggregates under SysV (call result/param/arg/return); 9 other |
| `[TCG-ARG-ABI]` | 32 | `PassMode::Pair` by-value ARGUMENTS (no two-value argument lane on any target) |
| `[TCG-POINTEE-DYN-VALUE]` | 30 | trait-object pointee asked for one value type |
| `[TCG-PASSVAL-067]` | 25 | `x86-popcnt-expand` obligation: AY answers `(:reason-unknown (incomplete self-check-rejected))` |
| `[TCG-POINTEE-LANES]` | 20 | array/struct pointee typing |
| others | 86 | fat-pointer union fields, unsized tails, slice casts, niche/Try shapes, `carrying_mul_add`, intrinsics |

After repairs 1 and 3 (`core-x86_64-linux-O0-pair`): `[TCG-RET-ABI]` 282 → 0,
`[TCG-PROOF-465]` 102 → 46 (the static anchors are gone; the rest are other
bodies with no genuine instruction proof), `[TCG-ARG-ABI]` 32 → 74 (pair
ARGUMENTS previously masked behind the return refusals), `[TCG-REGALLOC-063]`
45 → 46 (37 `Array(I8, N)` SysV aggregates, 7 `[TCG-POST-RA-DATAFLOW]`
tied-operand violations, 2 other). The 335 roots are the current x86-64 Linux
`core` refusal denominator at O0.

For comparison, the Darwin AArch64 census of record (Trust `e2e4c07dd01`,
2026-09-14) had 363 failed roots over 52 reasons; the two are not on the same
backend revision or target and are not directly comparable.

## Repairs made in this tree

1. **x86-64 two-register `PassMode::Pair` return lane** (bridge
   `scalar_pair_abi_plan`, `abi_reg_lanes::trust_cg_return_placement`, and a
   public `X86CallResultReg::is_sse` in `trust-cg-lower`). The x86-64 arm of
   the placement gate now reads the backend's own scalar-return classifier
   (`x86_scalar_return_result_regs`: RAX then RDX, XMM0 then XMM1) for a
   multi-value return, and the plan admits `x86_64`. A `Zext`/`Sext` lane
   narrower than 32 bits is declared as its extended 32-bit carrier
   (`ScalarPairAbiPlan::carriers`, `lane_ext`): the callee widens after the
   lane load and the caller truncates before the lane store, so an LLVM caller
   compiled against `zeroext` reads a defined register. AArch64 carriers are
   the lane types, unchanged.
2. **`tests/m140_x86_scalar_pair_return_xback.rs`**: 17 pair-returning shapes
   (`Option<u8/u16/u32/i32>`, `(u8,u8)`, `(u16,u16)`, `(u32,u32)`, `(u8,bool)`,
   `(i8,i8)`, `(u64,u64)`, `(f64,f64)`, `(u64,f64)`, `(f32,u64)`,
   `Result<u8,u8>`, `ControlFlow<u8,u8>`, `&'static [u32]`, `&'static str`) as
   callee rlibs and caller bins in all four backend combinations at O0–O3;
   every combination must exit with the LLVM+LLVM oracle's code. First run
   (`pair-return-xback-run1.log`, 815 s): **all 17 shapes agree in both
   directions at O0, O1 and O2, zero value mismatches**; 31 O3 combinations
   were refused by the vacuity rule on the empty `__rust_no_alloc_shim_is_unstable_v2`
   (repair 3, dylib not yet rebuilt at that run).
3. **x86-64 empty-body vacuity exemption** (`trust-cg-codegen`
   `x86_64_report_is_empty_body`): the x86-64 certificate path rejected any
   function with zero genuinely verified instructions, which every empty
   function is on x86-64 because `PUSH`/`POP`/`RET` are fail-closed-allowlisted
   with no value proof; the AArch64 path has no such rule. A report that is
   exactly `[Ret]` or `[Push, MovRR, Pop, Ret]` is no longer reported vacuous;
   any longer sequence keeps the rule. Reproduced first with the CLI
   (`--emit-proofs` on a `() -> ()` function: 6 bytes, `push rbp; mov rbp,rsp;
   pop rbp; ret`, refused; accepted after the change with two certificates).
   Two unit tests, including one through the real x86-64 selector and
   verifier.
4. **Bridge x86 tests ported to the host triple**
   (`tests/support/host_target.rs`): 119 files replaced their
   `x86_64-apple-darwin` pin with the host OS's x86-64 triple, the `.dylib`
   name with `DLL_PREFIX`/`DLL_SUFFIX`, and `-mmacosx-version-min` with a
   macOS-only flag list. Three Darwin-unwind tests (`unwind_cleanup_x86_64`,
   `m135_*`, `m138_*`) keep their Darwin host guard and `otool` use.

## First run of the Linux x86-64 floor (`x86-floor-as-found/`)

`scripts/check_linux_x86_64.py` (new; the twin of `check_linux_aarch64.py`
over 67 complete x86-64 integration targets) ran once as found, in a detached
worktree of `166093c1a` plus the three test-target repairs, before the
repairs below: **28 pass, 39 fail**. The failures have four causes:

1. `cc -arch x86_64` in the shared probe `tests/common/rosetta.rs`
   (`probe_cc_x86_64_link_run`) and in `tests/common/x86_64_corpus.rs`
   (`cc_link_x86_64`): GNU `cc` rejects Apple's `-arch`, so every x86-64
   oracle test skipped ("cc -arch x86_64 not available") and the floor counts
   a skip as a failure. Repaired: the flag is passed on macOS only.
2. `trust-cg-sat-host`'s build script compiles MicroSAT with the host `cc`;
   GCC 15 defaults to C23, where `false` is a keyword, and the source names a
   `struct solver` member `false`. Every `trust-cg-verify` integration target
   failed to build. Repaired: `-std=gnu17` (the pre-C23 default) is pinned.
3. Formal-capable environment. With AY (`store/ay/current/bin/ay`, a symlink
   to the stage2 solver) and the carcara-capable Clean both discoverable, the
   proof-promotion policy (`ProofPromotionEnvironment`) rejects any
   statistically-credited instruction instead of admitting it as the
   documented fallback. `jit_sysv_x86_64_spill_replay`,
   `jit_cert_cache_identity_x86_64` and `compile_service::native_install_gate_*`
   then fail on functions whose `jit_fast` compile credited some instructions
   only by sampling. These tests were green only on hosts where no capable
   checker existed (the AArch64 ledger's `X-HOST-P8`); on this host they show
   the JIT lane has no formal discharge for those instruction classes. Not
   repaired (plan row X11).
4. Genuine x86-64 defects to triage: `e2e_x86_64_vector_fp` (the adapter
   refuses `CastOp::Bitcast Vector(F64, 2) -> Vector(I64, 2)`),
   `jit_integration_x86_64` (`v16i8_mul_packuswb` emitted with a VEX prefix
   on this AVX host where the test requires legacy SSE2 encoding),
   `e2e_x86_64_callee_saved` (the SystemV O0 control subject touches no
   callee-saved GPR, a vacuous obligation the test refuses). Not repaired.

The second run (`x86-floor-run2/`, repairs 1 and 2 applied, the AY store
path laid, `e2e_x86_fcmp_cc_audit` removed because it is
`#![cfg(target_arch = "aarch64")]` and executes zero tests here): **46 pass,
21 fail**. The 21: seven host-JIT targets under cause 3 (`x86_64_constant_pool`,
`x86_64_sysv_ay_abi`, `jit_x86_64_profile_modes`, `jit_validation_modes_x86_64`,
`jit_x86_64_aggregate_abi_fail_closed`, `jit_cert_cache_identity_x86_64`,
`jit_sysv_x86_64_spill_replay`); six that hard-code Mach-O output
(`X86OutputFormat::MachO`, `x86_compile_to_macho`), Darwin `_`-prefixed
symbol names in their C drivers, or `cc -arch x86_64` in their own link
commands (`e2e_x86_64_correctness`, `e2e_x86_64_link`,
`e2e_x86_64_opt_correctness`, `e2e_x86_64_scale_emergent`,
`guard_kernel_gate_x86_linkrun`, `e2e_x86_64_calling_conv`); three explicit
Darwin-only EH skips (`e2e_x86_64_eh_catch`, `e2e_x86_64_eh_invoke_trust_ir_run`,
`e2e_x86_64_eh_resume_trust_ir`); and the five under cause 4 plus
`x86_64_target_features` (the adapter refuses the CHC SSE4 helper's `Select`
of `Ptr` under a `Vector(Bool, 2)` condition, the same admission family as
the vector bitcast). The vector bitcast admission is repaired in this tree
(`validate_cast_shape` admits equal-width fixed-vector reinterpretations);
`e2e_x86_64_vector_fp` passes with it.

## Diagnostic benchmark pass (`beat-llvm-diag/`)

`benchmarks/beat-llvm/run.py --target x86_64-unknown-linux-gnu --dylib <.so>
--driver <stage2>/bin/trustc --allow-loaded` on the repaired dylib
(`3e4f88a9…`), quiet machine but dirty tree, so NOT evidence: **0/18 MATCH,
18 INCOMPLETE**. Seventeen programs fail at the bridge lane's link with
`rust-lld: error: relocation R_X86_64_64 cannot be used against symbol
'std::rt::lang_start::<()>::{closure#0}'; recompile with -fPIC`: the bridge's
x86-64 ELF objects carry absolute `R_X86_64_64` relocations that the default
PIE link refuses. Reproduced by hand on `p1_xorshift` at O3; with
`-Crelocation-model=static` the same program links, exits 41 like the LLVM
build, and runs in 0.436 s against LLVM O3's 0.438 s. The eighteenth
(`v3_popcount`) fails closed on unsupported MIR. LLVM-lane compile times are
recorded (about 1.6 s per program); no bridge compile or runtime ratio exists
yet. Plan row X02 (relocation model) is the blocker for X14 on this host.

## Repairs after the second floor run

5. **PIE-safe x86-64 ELF data placement** (`trust-cg-codegen`
   `emit_module_elf`): an immutable global whose bytes hold symbol addresses
   (a vtable, a function-pointer table) now lands in `.data.rel.ro`
   (`SHF_ALLOC|SHF_WRITE`, sealed by RELRO after relocation) instead of
   `.rodata`, as the AArch64 ELF emitter and LLVM already do. Unit test
   `test_module_elf_places_relocated_immutable_globals_in_data_rel_ro`;
   `e2e_x86_64_data_reloc` now requires `.rela.data.rel.ro` for the
   pointer-bearing global. With the rebuilt dylib the minimal std program
   (O0) and `p1_xorshift` (O3) link as `DYN (Position-Independent
   Executable)` and exit 42 / 41, matching LLVM.
6. **Vector bitcast admission** (`trust-cg-lower` `validate_cast_shape`):
   `CastOp::Bitcast` between fixed vectors of equal total width
   (`<2 x f64>` <-> `<2 x i64>`, `<4 x f32>` <-> `<4 x i32>`) is admitted
   again; both selectors lower it as one register move. `e2e_x86_64_vector_fp`
   passes (10 tests).
7. **Linux arms for Darwin-format x86-64 tests**: `e2e_x86_64_opt_correctness`
   (host object format; 4 pass), `e2e_x86_64_correctness` (host format;
   28 pass), `e2e_x86_64_link` (host format; the `otool` validation is
   macOS-only; 17 pass, and `test_x86_64_link_clamp` / `_loop_sum` fail on
   any host with `MalformedFunction: block Block(0) successor metadata {}
   does not match semantic control edges` because their hand-built ISel
   functions predate the successor-metadata validation — pre-existing, not
   repaired), `guard_kernel_gate_x86_linkrun` (host triple; the shared x86
   interpreter fixture `common/x86_interp.rs` gained `extract_text`, which
   reads `.text` from ELF as well as `__TEXT,__text` from Mach-O),
   `e2e_x86_64_calling_conv` (host triple, no `-arch`; 17 pass, and the two
   `swiftcc` cases fail because their C driver needs clang's
   `__attribute__((swiftcall))`, which gcc ignores — this host has no clang).

The third run (`x86-floor-run3/`, repairs 5–7 applied): **49 pass, 17
fail**; `guard_kernel_gate_x86_linkrun` then passed once the shared fixture's
`objdump` cross-check learned GNU binutils' AT&T layout (`push   %rbp` with
spaces, not LLVM's tab), so the effective count is 50 of 66. The 16 that
remain: the seven host-JIT targets under cause 3 (X11), the three Darwin-only
EH tests (X03), `e2e_x86_64_calling_conv` (clang-only `swiftcall` driver),
`e2e_x86_64_link` (pre-existing successor-metadata failure in two hand-built
ISel fixtures), `e2e_x86_64_scale_emergent` (ported afterwards: its C drivers' `__asm__("_name")`
bindings and `nm` symbol constants drop the Mach-O underscore on ELF; 6 pass), `e2e_x86_64_callee_saved`
(vacuous SystemV O0 control), `jit_integration_x86_64` (VEX on an AVX host)
and `x86_64_target_features` (`Select` of `Ptr` under a `Vector(Bool, 2)`
condition refused by the adapter).

## Full root matrix (`full-matrix-report-only.json`)

`TRUST_CG_PROOF_GATE=skip TCG_SKIP_BENCH_STAGE=1 scripts/run_full_test_matrix.sh --report-only`
(NON-QUALIFYING: proof gate and bench stage skipped), the first full-matrix
record on any x86-64 Linux host. It ran for 70 minutes while the bridge was
being rebuilt and the repairs above were landing, so later shards saw later
source than earlier ones; it is a census, not a clean-tree qualification.

| Quantity | Value |
| --- | ---: |
| Shards | 292 |
| Tests passed / failed / ignored | 15,568 / 274 / 4 |
| Shard outcomes: pass / fail / skipped / timeout / incomplete | 121 / 41 / 126 / 2 / 2 |
| Shards with runtime `SKIP` rows | 70 (172 skips) |

The 126 "skipped" shards are mostly auto-assigned AArch64-only integration
targets that compile to zero tests on x86-64 (`#![cfg(target_arch = "aarch64")]`
or Linux-AArch64 host cfgs) plus macOS-guarded families; the two timeouts are
`trust-cg-verify` `lib-other` (`checked_overflow_proofs::tests::test_checked_overflow_i64_z3_cli`
past the 1500 s shard budget) and `trust-cg-verify` `integration`; the two
incomplete shards are `trust-cg-sat-host` (the C23 build failure, repaired
after this run) and `trust-cg-jit-matrix` (suite rollup disagreement). The
41 failing shards include the x86-64 families discussed above
(`integration-x86_64` 92 pass / 48 fail, `integration-jit-runtime` 44 / 53,
`integration-ay-contracts` 101 / 9), `trust-cg-fuzz` (44 / 16), `trust-cg-cli`
(110 / 5), the `e2e_*` Clean-kernel families (`e2e_recursor_iota`,
`e2e_quotient`, `e2e_sprop`, `e2e_inductive_soundness`, `e2e_nat_reduce`,
`e2e_lazy_delta`, `e2e_defeq_cache`, `e2e_phase_completion`) and the JIT
hardening/W^X/teardown families. None of these has been triaged beyond the
x86-64 items named in this report.

8. **Bool-valued pair lanes keep bit 0 only** (bridge
   `ScalarPairAbiPlan::lane_bool`). The pair-return test's third run
   (`pair-return-xback-run3.log`) trapped at `res_u8`, LLVM callee + trust-cg
   caller, O1: reproduced by hand at every opt level (LLVM callee + trust-cg
   caller exits via `SIGILL`; trust-cg callee + trust-cg caller and the
   all-LLVM build exit 160). The LLVM callee returns `Result<u8, u8>`'s tag
   as an `i1`: `al` holds the whole input `n` and only bit 0 means the tag
   (`mov %edi,%eax; test $1,%al; ... ret`), so a consumer that stores the
   full byte reads a tag of 30 and takes the unreachable arm. LLVM's own
   callers mask. The caller half now masks a rustc `is_bool` lane to bit 0 with an
   integer `And` at the carrier's width before the truncation (x86-64 only,
   where the carriers are widened; the qualified AArch64 lane is unchanged and needs
   the same measurement against an LLVM callee). The first run did not
   surface this because its O0–O2 combinations happened to pass on the same
   callee shape; the record is inconclusive about why and the hand
   reproduction is the evidence. Fourth run (`pair-return-xback-run4.log`,
   797 s, dylib with repairs 1, 3, 5, 6 and 8): **the test passes — all 17
   shapes, all four backend combinations, O0 through O3, zero refusals, zero
   mismatches.**

## Diagnostic benchmark pass on the relro dylib (`beat-llvm-diag2/`)

Same command on the dylib with repairs 5 and 6, `--allow-stale-dylib` (the
tree kept changing), dirty tree, matrix and pair test running concurrently:
**NOT evidence** for any gate, but the first per-program Linux x86-64 table.

| Quantity | Value |
| --- | ---: |
| Coverage | 17/18 MATCH, 0 MISMATCH, 1 INCOMPLETE (`v3_popcount`, unsupported MIR) |
| Runtime geomean vs LLVM O3 | 1.169x |
| Scalar-category runtime geomean vs LLVM O3 | 0.988x |
| Worst runtime vs LLVM O3 | 4.079x (`p4_matmul`); `v2_memfill` 4.029x; `h1_vec_push_sum` 1.859x |
| Best runtime vs LLVM O3 | `v1_saxpy` 0.646x, `p7_sieve` 0.740x, `m2_call_heavy` 0.756x |
| Warm proof-enabled compile vs LLVM O2 / O3 | 2.431x / 2.437x |
| Emitted size vs LLVM O3 | 1.0x |

Against the contract's milestones (scalar <= 1.30x: met on this sample; every
vectorizable kernel <= 2.0x: not met, two kernels above 4x; full geomean
< 1.00x and worst <= 1.50x: not met; warm compile <= 1.00x O2: not met), and
against the last macOS x86 row (runtime 1.302x, warm compile 6.66x). A quiet,
clean-tree run with `--retain-dir` is the next step before any number is
appended to the ledger.

## Pre-existing findings recorded, not repaired

- `compile_service::tests::native_install_gate_*` (`..._never_promotes_rejected_artifact_disposition`,
  `..._historical_freshness_is_monotone_deny_only`) fail when run alone on
  this host: the fixture's x86-64 `answer` function has one instruction
  credited only statistically and promotion refuses it; in a full lib run the
  same tests pass, so the outcome depends on test order (shared verdict
  state). Recorded for the matrix census; not fixed here.
- `[TCG-PASSVAL-067]` on `x86-popcnt-expand` is AY's strict self-certification
  rejecting its own proof on a resource envelope (`formal_gap.rs`), not a
  trust-cg lowering defect; the obligation needs a solver-side answer.
- The full root test matrix (`scripts/run_full_test_matrix.sh --report-only`,
  proof gate skipped because no aterm-managed AY/Clean exists for this target,
  bench stage skipped) was started on this host; its JSON is retained beside
  this README when it completes.

## Evidence boundary

Every Trust-compiled result uses the explicit unverified frontend lane;
backend proof checks were on unless stated. This is native regression and
census evidence for one x86-64 Linux host. It establishes no verified-default
authority, no self-hosting, no performance result and no closure of any
completion row.
