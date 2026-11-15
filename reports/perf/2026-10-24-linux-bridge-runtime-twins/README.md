# Linux rustc-bridge runtime twins — 2026-10-24

Ledger rows L03-P7, L06-P4 and L13-P4. Three Darwin-only bridge runtime
fixtures gained Linux AArch64 ELF twins, each a required target of
[`scripts/check_linux_aarch64_bridge.py`](../../../scripts/check_linux_aarch64_bridge.py)
(nine targets now), on branch `feat/linux-bridge-runtime-twins` (from
`origin/main` `4a0668957`):

| Linux twin | Darwin original | Shared harness |
| --- | --- | --- |
| [`static_data_linux`](../../../crates/rustc-codegen-trust-cg/tests/static_data_linux.rs) | `static_data_aarch64` | [`support/linux_runtime_twin.rs`](../../../crates/rustc-codegen-trust-cg/tests/support/linux_runtime_twin.rs) |
| [`drop_heap_linux`](../../../crates/rustc-codegen-trust-cg/tests/drop_heap_linux.rs) | `drop_heap_aarch64` | same |
| [`coroutine_generator_linux`](../../../crates/rustc-codegen-trust-cg/tests/coroutine_generator_linux.rs) | `coroutine_generator_aarch64` | same |

Commits: `e8196601c` adds the twins and registers them; `db2db55ef`
recorded its first lane run, in which the coroutine twin was red on a bridge
refusal; `5d37f4cf1` fixes the cause of that refusal in the optimizer
(trust-cg-opt `scalar_unroll`), adds its regression tests, a coroutine
`shapes` fixture and self-naming aborting stubs. The verdict below is the
lane run at `5d37f4cf1`.

**Evidence class: native testing evidence without certificates.** Every
compile, CG and LLVM alike, runs with `-Ztrust-verify=off`; every bridge
compile passes the `no-proof-certs` knob (once also `batch-cgu=0`); the
backend was built by `targo --unverified`. Nothing here is proof,
certificate, exact-object-binding, shared-object or Darwin evidence. GNU
cc/ld, binutils, glibc, the LLVM-compiled drivers and the standard library
are trusted. The optimizer fix is checked by tests (a unit test, a JIT
execution test, the bridge twin), not proved.

## Lane verdict

`build-slot -- python3 -B scripts/check_linux_aarch64_bridge.py --out <dir>
--target-dir /home/ayates/trust-cg-wt/bridge-twins-bridge-target
--timeout-seconds 10800`, from the clean worktree at `5d37f4cf1` (source
fingerprint `87f4c404c832…`, unchanged from start to end), 2026-10-24
22:36:33Z to 2026-10-25 01:59:27Z, other agents' jobs sharing the host
(load average about 10 on 20 CPUs). The lane rebuilt the backend and tested
its read-only snapshot, SHA-256
`ae685cfccd5961727311a886badc691b062b543faa49660b34725ad0643369db`
(143,729,272 bytes), with every target. **Verdict: FAIL**, on three targets
that are red on `origin/main` too; the three twins pass.

| Required target | Verdict | libtest | Cause |
| --- | --- | --- | --- |
| `aarch64_c_fnabi_aggregate_linux` | fail | 130 passed, 4 failed (6,775 s) | three pre-existing failures and one unreproduced timeout, below |
| `tls_thread_local_linux` | fail | 1 passed, 1 failed (2 s) | pre-existing, below |
| `unwind_cleanup_linux` | fail | 2 passed, 1 failed (5 s) | pre-existing, below |
| `panic_hook_differential` | pass | 2 passed (47 s) | |
| `executable_trap_stub_routes_aarch64` | pass | 5 passed (71 s) | |
| `scalar_zst_field_differential` | pass | 1 passed (48 s) | |
| **`static_data_linux`** | **pass** | 3 passed (138 s) | |
| **`drop_heap_linux`** | **pass** | 3 passed (87 s) | |
| **`coroutine_generator_linux`** | **pass** | 3 passed (80 s) | red at `e8196601c`; fixed by `5d37f4cf1` |
| cross-backend ABI | pass | 3,928 of 4,752 cross cells matched, 824 declined in the 133 listed rows | same counts as the `e8196601c` run |

The expected baseline was the aggregate target alone red (L06-P1). The TLS
and unwind targets are red on `origin/main` as well (below), so that
baseline is stale.

No CG executable differed from its LLVM twin in any twin lane: **no wrong
code was found.** The one new red, the aggregate target's fourth failure,
is a timeout: `atomic128_loads::no_proof_atomic128_loads_match_llvm` killed
its contention executable built from CG objects at O3 at the test's 20 s
bound (exit 124, no output). It is not from this change and not shown to be a
CG/LLVM difference: compiled by hand, that corpus's CG objects are
byte-identical at O0–O3 between the `db2db55ef` test-build backend
(`39dbd203…`, built from the backend source of the `e8196601c` lane, in
which this test passed) and this lane's backend; the CG and LLVM loads use
the same exclusive-pair retry loop for each ordering (`LDXP`/`LDAXP` with
`STXP`/`STLXP`; CG adds a frame record around it); and the same CG O3 executable, rebuilt
from those objects with the test's driver, passed 400 of 400 runs, as did the
LLVM one, at a host load average of 10–12. Two threads contending on one
cache line through exclusive-pair loops can starve, so this is recorded as an
unreproduced timeout under load, left red, and worth watching.

## The coroutine refusal and its fix

At `e8196601c` the bridge refused the Darwin generator `ay_gen_seq` at O2 and
O3 when it emitted the object:

```
error: [TCG-MIR-UNSUPPORTED] rustc_codegen_trust_cg: cannot compile required function with unsupported MIR (failing closed rather than miscompiling):
         - ay_gen_seq: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: [TCG-A64-SWITCH-BIND] fn `ay_gen_seq` switch dispatch binding failed: byte 324: jump-table bounds constant constant register x9 is not materialized by a move-wide chain: no producer in the block
```

(byte 68 at O3). The refusal was fail-closed: no executable was built, so no
wrong code ran. Verifiers found it broader than this fixture: a `move`
coroutine with an upvar and a branchy one were refused the same way at
O2/O3, while a one-yield resume-argument coroutine (four states) compiled. Independent
verifiers also confirmed that every CG lane that did run matched LLVM.

**Cause.** A coroutine's resume loop has the state dispatch as its loop
header. ISel lowers a dense switch to `CMP index, #(len - 1); B.HI default;
ADR; LDRSW; ADD; BR`, and for a coroutine the default (the panic edge) is
outside the loop. `const-trip-guard-normalize`
(`crates/trust-cg-opt/src/scalar_unroll.rs`, `find_const_trip_cmpri_guard`)
rewrites any loop header's `CmpRI x, #imm` that precedes a loop-leaving
`B.cond`, for `imm` in `[4, 0xFFF]`, into `CmpRR x, movz` with the `MOVZ`
hoisted into the preheader, so that constant-trip unrollers see the shape
they match. It did not check that the header is a counted loop's exit test.
Five coroutine states (two yields) give `CMP #4`, the bottom of the window;
the one-yield resume-argument coroutine has four, `CMP #3`, below it.
The per-compile switch binder
(`crates/trust-cg-verify/src/aarch64_switch_binding.rs`) binds a table's
bound only to an immediate or to a move-wide chain inside the dispatch block,
so it refused the hoisted bound.

**Fix (`5d37f4cf1`).** The normalizer declines a header that holds an
`Adr .., JumpTableIndex` or a `Br`. No constant-trip recognizer accepts a
header that ends in an indirect branch, so the rewrite never enabled an
unroll there; code changes only for such headers, which keep the immediate
compare ISel emitted. The binder is unchanged: it
keeps its in-block rule rather than learning to follow a producer outside
the dispatch block (decision record OD-BRIDGE-LINUX-RUNTIME-TWINS-20261024,
point 2).

**Regressions, and that they catch it.** With the normalizer unchanged
(the `e8196601c` source restored for one run) and then with the fix, in one
`build-slot` job from this worktree:

| Test | Without the fix | With the fix |
| --- | --- | --- |
| `scalar_unroll::tests::a_jump_table_dispatch_header_keeps_its_bounds_immediate` (trust-cg-opt) | fails: the dispatch header is normalized | passes; its control (the same guard without the dispatch) is still normalized |
| trust-cg-codegen [`tests/aarch64_jump_table_loop_header_bound.rs`](../../../crates/trust-cg-codegen/tests/aarch64_jump_table_loop_header_bound.rs) | both tests fail: `const-trip-guard-normalize` rewrote the header at O2 (1 change), and the O2 JIT compile is refused `[TCG-A64-SWITCH-BIND] fn jump_table_loop_header ... byte 48: jump-table bounds constant constant register x10 is not materialized by a move-wide chain: no producer in the block` | 2 passed: one jump table and an immediate bound in its dispatch block at O0–O3, and every row equal to the model at O0–O3, including selector 5, the first index past the table |

The codegen test's function is a loop whose header loads a selector and
dispatches through a five-entry jump table whose default returns from the
function; it is the coroutine's shape without the bridge. With the fix, the
trust-cg-opt library tests (4,548 passed, 2 ignored), `pipeline_small_stack`
(3), and the trust-cg-codegen jump-table and switch targets
`aarch64_alias_hoist_jump_table_clone` (3), `aarch64_unroll_jump_table_clone`
(6), `aarch64_unswitch_jump_table_clone` (4), `e2e_aarch64_switch` (3),
`aarch64_final_layout_crosscheck` (6) and
`aarch64_volatile_access_preservation` (4) pass; `targo tippy` is clean for
trust-cg-opt (library and tests) and the new codegen test.

Through the bridge, the Darwin `GEN_CRATE` verbatim as `gen.rs`, compiled
with

```sh
trustc --edition=2021 -Ztrust-verify=off --target aarch64-unknown-linux-gnu \
  -Zcodegen-backend=<backend.so> -Ztrust-ir-cg-args=no-proof-certs \
  --crate-type staticlib -Ccodegen-units=1 -Cpanic=abort -Copt-level=<N> \
  --emit=obj --out-dir out gen.rs
```

and linked with the Darwin driver:

| Backend | O0 | O1 | O2 | O3 |
| --- | --- | --- | --- | --- |
| `39dbd203…` (test build of `db2db55ef`) | `packed=10020030`, exit 0 | `packed=10020030`, exit 0 | refused, byte 324 | refused, byte 68 |
| `1e8e137a…` (test build of the fix) | `packed=10020030`, exit 0 | `packed=10020030`, exit 0 | `packed=10020030`, exit 0 | `packed=10020030`, exit 0 |

## Pre-existing reds

The three other red targets are not from this branch: on it, the backend
and test sources of every other target are those of `origin/main`
`4a0668957`, except that `static_data_aarch64.rs`, `drop_heap_aarch64.rs` and
`coroutine_generator_aarch64.rs` (compiled out on Linux) each gained a
comment naming their twin, and that `5d37f4cf1` changes the optimizer
(trust-cg-opt `scalar_unroll`) for jump-table dispatch headers only.
Another agent's lane at `origin/main` `49a96e1f6`, whose bridge and test
sources equal `4a0668957`'s, failed the TLS (1 passed, 1 failed) and unwind
(2 passed, 1 failed) targets with the same messages; its aggregate target hit
that lane's time bound, and a separate full run of that target on the same
base had the same three failures (131 passed, 3 failed; both retained in the
shared scratch tree and cited by a verifier). None of the three was re-run
here on a `main` checkout.

- **`aarch64_c_fnabi_aggregate_linux`** (130 passed, 4 failed here; the
  fourth is the timeout above):
  `c_fnabi_hfa_all_members_both_directions_and_llvm_twin` fails with the
  L06-P1 proof-coverage refusal (`[TCG-PROOF-465]`, uncovered opcodes);
  `function_linkage::no_proof_private_function_linkage_matches_llvm` finds a
  `FILE LOCAL` symbol named
  `linkage_left.__trust_cg_private…cgu.0.2.rcgu.o` where it expects a private
  definition's binding (an object-shape failure); and
  `residual_conversion::no_proof_reference_identity_refuses_unresolved_storage`
  expects the bridge to refuse `negative_reference_storage.rs` with
  `[TCG-REF-ARG-STORAGE]` and sees exit status 0. That is an expected refusal
  the bridge no longer raises, not an object-shape failure: compiled by hand
  with the `db2db55ef` test-build backend (`39dbd203…`; `-Cpanic=unwind`,
  `diag-json no-proof-certs`), the fixture compiles at O0 and O2 with no
  refusal, and its CG and LLVM objects, linked with a C `identity(a, b)`
  driver (aborting stubs for `panic_cannot_unwind` and
  `rust_eh_personality`), both print `identity=1 same=1`. Which change made
  the bridge accept it was not diagnosed; no wrong code was seen.
- **`tls_thread_local_linux`:** `accessor tls.o must not define X`.
- **`unwind_cleanup_linux`:** `only one empty filter byte follows TType`
  (left 29, right 249).

The TLS, unwind and `function_linkage` messages fit one likely cause, not
bisected: since `e1bc865fb` (2026-10-23, "Implement unchecked multi-object
publication", decision record
DR-UNCHECKED-OBJECT-COMPOSITION-IMPLEMENTATION-20261023) an unchecked bridge
compile that produces several objects for `--emit=obj` publishes one
partially linked object, so `X` and its accessors would share one object,
one `.gcc_except_table` would hold several functions' LSDAs, and the partial
link adds `FILE` symbols. A manual compile of the TLS crate with an earlier
backend of this branch gave one `tls.o` defining `X`, `read_x` and `bump_x`.
These are object-shape assertions failing, not CG/LLVM differences; they are
not repaired here.

## Results per target, compiler and level

Each cell: the ending of every run and passing runs of three. The marker row
also carries the SHA-256 of the observed stdout, equal to the fixture's model
digest in every row the runner accepted.

`static_data_linux` (64 lanes, 192 executions; identical at every level):

| Fixture | CG O0 | CG O1 | CG O2 | CG O3 | LLVM O0 | LLVM O1 | LLVM O2 | LLVM O3 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `immutable` (Darwin) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |
| `mutable` (Darwin) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |
| `overaligned` (Darwin + prelude) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |
| `externs` (Darwin) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |
| `layout` (Linux) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |
| `readonly_store` (control) | SIGSEGV 3/3 | SIGSEGV 3/3 | SIGSEGV 3/3 | SIGSEGV 3/3 | SIGSEGV 3/3 | SIGSEGV 3/3 | SIGSEGV 3/3 | SIGSEGV 3/3 |
| `misaligned_exclusive` (control) | SIGBUS 3/3 | SIGBUS 3/3 | SIGBUS 3/3 | SIGBUS 3/3 | SIGBUS 3/3 | SIGBUS 3/3 | SIGBUS 3/3 | SIGBUS 3/3 |
| `out_of_bounds` (control) | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 |

Every `out_of_bounds` run aborted through the `panic_bounds_check` stub, the
same for CG and LLVM. Object facts at every level and for both compilers: 21
statics checked, 12 pointer relocations, 2 extern imports, storage classes 9
read-only, 6 writable, 1 `NOBITS`, 5 relocated, equal between CG and LLVM.

`drop_heap_linux` (37 lanes, 111 executions):

| Fixture | CG O0 | CG O1 | CG O2 | CG O3 | LLVM O0 | LLVM O1 | LLVM O2 | LLVM O3 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `hooked` (Darwin, bridge only) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | — | — | — | — |
| `hooked_per_function` (bridge only) | exit 0 3/3 | — | — | — | — | — | — | — |
| `indirect` (Darwin, bridge only) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | — | — | — | — |
| `archive_c1` (Darwin) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |
| `archive_c4` (Darwin) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |
| `events` (Linux) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |
| `refused` (control, LLVM twin) | refused | refused | refused | refused | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |

The O0 partitions: batched 2 objects (the codegen unit and the allocator
shim), per-function 15, the two entries in different objects there.

`coroutine_generator_linux` (28 lanes, 84 executions; nothing refused):

| Fixture | CG O0 | CG O1 | CG O2 | CG O3 | LLVM O0 | LLVM O1 | LLVM O2 | LLVM O3 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `sequence` (Darwin) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |
| `resume_after_complete` (Linux) | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 | SIGABRT 3/3 |
| `shapes` (Linux) | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |
| `refused` (control, LLVM twin) | refused | refused | refused | refused | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 | exit 0 3/3 |

Every `resume_after_complete` run aborted through the
`panic_const_coroutine_resumed` stub, the same for CG and LLVM. The O0 MIR
check passed (a coroutine frame aggregate, a `SetDiscriminant`, no `Yield`).
At `e8196601c` the CG `sequence` lanes at O2 and O3 were refused; the
`shapes` fixture did not exist yet.

## What each twin checks

All three share the harness: `twin::require_knobs` asserts the
`-Ztrust-ir-cg-args` option (a missing one fails the test by name; it never
skips), `twin::require_host` the `aarch64-unknown-linux-gnu` host, and every
spawned tool (`cc`, `readelf`, `objdump`, `timeout`, `sha256sum`, `mktemp`)
fails the test when absent. The backend is the runner's snapshot, bound by
path and SHA-256. Every executable runs three times under GNU `timeout`; each
run must print exactly the model on stdout, end exactly as modelled (an exit
code or a signal) and, on a clean exit, print nothing on stderr. Every
aborting stub for an undefined core panic entry writes `TCG_ABORT_STUB
<symbol>` to stderr before `abort()`: a lane that models `SIGABRT` must fire
exactly one stub, the same in every run and for CG and LLVM, and no other
ending may fire one.

- **`static_data_linux`** — five crates per compiler and level: the Darwin
  immutable, mutable, over-aligned and extern-static crates (byte-identical;
  the over-aligned and extern crates with `-Cdebug-assertions=off`, as on
  Darwin) and a Linux `layout` crate (zero-initialized `[u64; 8]` and
  `[u32; 4]`, a `&str`, a `&[u16]`, two `extern "C" fn` pointers, a reference
  to another static, a four-entry table, and Rust accessors whose addresses
  and values its driver compares with its own view). Eight drivers: the four
  Darwin drivers (the over-aligned one after an `LDAXP`/`STLXP` prelude: GNU
  cc lowers the 16-byte `__atomic_fetch_add` to a libatomic call, which does
  not fault on a misaligned address), the `layout` driver, and three
  controls: a store to the immutable `AY_STATIC_N` (`SIGSEGV`), an exclusive
  pair on `AY_WIDE_A + 8` (`SIGBUS`), and `AY_TABLE[4]`, which must abort
  through `core::panicking::panic_bounds_check`. `readelf` facts for all 21
  `#[no_mangle]` statics: one `GLOBAL OBJECT` definition of the right size;
  address and section aligned to the static's alignment; storage class;
  exactly its `R_AARCH64_ABS64` slots and no other relocation; the two extern
  statics imported and named by four data relocations.
- **`drop_heap_linux`** — `hooked` (bridge only, the Darwin crate and
  `build_driver`): each entry's own bytes call `__rust_alloc`,
  `__rust_dealloc` and `__rust_alloc_error_handler`; the run prints both
  values, two allocations and two frees, then drives a failed allocation into
  the handler with its 8/8 layout. `indirect` (bridge only, the Darwin
  address-taken `Box::new` crate and `build_indirect_box_driver`): the entry
  takes one function's address and calls through `BLR`; that body calls
  `__rust_alloc` and the handler, and its path to the first `RET` holds no
  `BRK` except after the non-returning handler call; one allocation, one
  free. These two lanes have no LLVM twin, as on Darwin: an LLVM object does
  not intercept `Box::new`, and LLVM removes the never-escaping boxes above
  O0. `archive_c1`/`archive_c4` (CG and LLVM): the Darwin crate as a staticlib
  archive linked by plain `cc` with the compile's `native-static-libs`.
  `events` (CG and LLVM): a Linux rlib (`Box<Tracked>`, `Vec<Tracked>` within
  capacity, `Vec<i64>` growth through `realloc` 32 -> 64 -> 128 bytes, an
  early and an overwrite drop; every pointer escapes to `black_box`) linked
  into an LLVM Rust driver whose logging `#[global_allocator]` prints each
  call's ordered allocation, reallocation, free and drop log. The control
  crate (`Vec<Box<Tracked>>`, a struct of two `Box<Tracked>`) is refused at
  every level with its two exact rows ("per-element drop glue not lowered",
  "recursive drop glue not lowered") and no definition of `ay_vec_of_boxes`;
  its LLVM twin runs to the model.
- **`coroutine_generator_linux`** — the Darwin MIR check; `sequence` (the
  Darwin `GEN_CRATE` and `DRIVER_C`; the bridge's objects define `ay_gen_seq`
  and keep a call of `panic_const_coroutine_resumed`); `resume_after_complete`
  (yield 1, return 2, then the third resume aborts through
  `panic_const_coroutine_resumed`); `shapes` (a `move` coroutine with an upvar
  and five states, a one-yield resume-argument coroutine with four, and a branchy one
  with six states); and the control crate (a generator whose locals live
  across `yield`, refused at its drop glue as `StatementKind::Nop`; one
  dropped while it holds user-`Drop` guards, `Ty::Coroutine(..)`; and a
  closure borrowing a captured scalar, "borrowed scalar reference used
  without deref"), refused at every level with its three exact rows and no
  definition of the latter two; its LLVM twin prints the values, their order
  and the guards' drop order.

The runner requires, for each twin, one marker declaring `certificates: off`
and `frontend_verify: off`, bound to the snapshot hash, listing every
(fixture, compiler, level) lane exactly once with its ending and model
digest; exactly three passing tests; exactly the expected `no-proof-certs`
knob traces (20, 25 with one `batch-cgu=0`, and 16); the static target's
storage counts and CG/LLVM equality; the drop target's two partitions; the
coroutine MIR facts and an empty `refused_lanes`; and each refusal control at
every level.

## What this is not

- Not certificates, proof or object binding: see the evidence class above.
- The runner checks each lane's observed-stdout digest against the model
  digest the twin itself reports, so the twin source is the only authority on
  the expected output (as for the TLS and unwind twins). A verifier showed
  that a marker whose model and observed digests are all replaced by the
  empty-string digest still classifies as passing. What holds the models in
  place is the twin source: the drop and coroutine twins derive their models
  in a test of their own (`event_models_account_for_every_allocation`,
  `coroutine_models_are_the_documented_sequences`), the static twin pins its
  fixture inventory (`darwin_fixtures_are_the_ones_this_target_runs`), the
  Darwin drivers check their own values and exit nonzero on a mismatch, and
  every lane with an LLVM twin must also equal the LLVM executable's run.
- Coverage differs from the Darwin originals in five stated places. The
  Darwin immutable lane's certificates-on compile and its "only
  `rust_begin_unwind` may be left out" check do not apply: nothing here is
  certificates-on. Every static-data compile here (all four crates, CG and
  LLVM) uses one codegen unit, where Darwin's CG compiles use the default
  and only its LLVM ones pin one, so a definition in one object imported by
  another is not exercised (a verifier's 16-unit probe of the mutable crate
  exited 0 at O0–O3 with CG; not a required lane). The coroutine twin drops
  the Darwin check that the resume body (`ay_gen_seq`'s `{closure#0}`,
  `ay_gen_seq0`) lands in an object of its own: with one codegen unit and
  the partial-link publication there is no separate object to find, and
  the twin checks behaviour against LLVM instead. The indirect `Box::new` check cannot name the taken
  function, because the bridge renames internal symbols to
  `__trust_cg_private.*` even in `-Csave-temps` objects; it checks instead
  that exactly one function address is taken and that its body calls
  `__rust_alloc` and the handler with no trap. At O1–O3 rustc makes one
  codegen unit of the archive crate, so `archive_c4` is a distinct partition
  only at O0 (the same holds on Darwin).
- The other bridge refusals the twins meet are listed in
  [`LIMITATIONS.md`](../../../LIMITATIONS.md) ("Coroutines and drop glue on
  Linux AArch64").

## Before the lane

The step that showed the regressions red and green (above) then built the
bridge (`targo --unverified test --release --locked`) and ran each twin
alone (`--nocapture --test-threads=1`) against the library Cargo built for
that test build (`1e8e137a…`): `coroutine_generator_linux` 3 passed
(79.96 s; 28 lanes, nothing refused, 16 knob traces), `static_data_linux` 3
passed (137.36 s) and `drop_heap_linux` 3 passed (86.38 s). The runner's
classifiers, applied to those transcripts, pass all three. The runner's unit
tests (`scripts/tests/test_linux_aarch64_bridge_gate.py`, 44, now with the
`shapes` lanes and a missing `drop_heap_linux` test artifact) and the
backend-selection lint (`scripts/tests/test_bridge_backend_selection.py`,
11) pass.

## Identities

- Host `aarch64-unknown-linux-gnu`, Ubuntu 24.04.4 LTS, kernel
  `6.17.0-1026-nvidia`, glibc 2.39, GNU cc 13.3.0, GNU binutils 2.42.
- `trustc -vV`: `rustc 1.99.0-dev (ae9c2c1da 2026-09-21) (trustc 0.1.0)`,
  commit `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, LLVM 22.1.2, from
  `~/toolchains/trust-ae9c2c1d-ay13556/bin`; AY
  `0f4c21c75317bacadaacfd6be2901ec1e70b53683ee4b8f1571d0ccef2572e05` and Clean
  `6a6b27c573c209b9d76c9e98bf8e18e1dda5c16c09ff72735226901d53783a4e` from that
  package's sysroot (`toolchain-sysroot` route), unchanged across the run.
- Run environment: a fresh 0700 `XDG_CACHE_HOME` under the scratch tree;
  every `TCG_*`/`RUSTC*`/`RUSTFLAGS` override absent; default `--jobs 2`.
- Backend bytes are not reproducible across target directories (a verifier
  built `6b082c1b…` from `db2db55ef`); each hash here identifies only the run
  that names it.

## Landing

The branch was merged with `origin/main` `2425fd51d` (which had moved the
trust-ir pin) together with `fix/bridge-linkage-visibility-20261024` on the
integration lane `land/linux-20261025`, and the lane was run again on that
merged tree (`98ecfc874`, backend `f70c2a69…`, 2026-10-25):

- every required target except the aggregate one passed:
  `static_data_linux` 3/3, `drop_heap_linux` 3/3,
  `coroutine_generator_linux` 3/3, `tls_thread_local_linux` 2/2,
  `unwind_cleanup_linux` 3/3, `panic_hook_differential` 2/2,
  `executable_trap_stub_routes_aarch64` 5/5,
  `scalar_zst_field_differential` 1/1, and the cross-backend ABI
  differential;
- `aarch64_c_fnabi_aggregate_linux` hit the runner's default 1200 s bound;
  run alone to completion against the same backend snapshot it gave
  136 passed, 2 failed: `c_fnabi_hfa_all_members_both_directions_and_llvm_twin`
  (L06-P1, `[TCG-PROOF-465]` at `repeated_cell_f32` O0) and
  `residual_conversion::no_proof_reference_identity_refuses_unresolved_storage`
  (a stale refusal control, red on the base too).

The root-workspace part (the `scalar_unroll` fix) passed `trust-cg-opt`'s
library tests (4,548), `aarch64_jump_table_loop_header_bound` (2/2),
`scripts/check_fmt.sh` and `targo tippy` on `trust-cg-opt` and
`trust-cg-codegen` (all targets, `-D warnings`) on the same tree.

## Reproduce

```sh
PATH="$HOME/toolchains/trust-ae9c2c1d-ay13556/bin:$PATH" \
  build-slot -- python3 -B scripts/check_linux_aarch64_bridge.py \
    --out /path/outside/source --target-dir /path/outside/source/cache \
    --timeout-seconds 10800
```

The report directory stays on the Linux host and is not archived.
