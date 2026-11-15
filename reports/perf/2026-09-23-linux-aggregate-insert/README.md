# Aggregate `InsertField` / `InsertElement` value semantics on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies a wrong-code fix in the trust-ir adapter
(`crates/trust-cg-lower/src/adapter.rs`) and the new floor target
`e2e_aarch64_aggregate_insert_linux`. The qualifying run used clean source
`14d5d2dbea2b65072f173a6bf1ce7fd7ae623cf9` (tree
`abf5c81cccbd7d00af7e07c67e87d58594fcd575`, base `306912d63`, trust-ir pin
`7b9146ba`). `git status --porcelain --untracked-files=all` was empty before
and after (`records/source.json`). The fix is `ff27f9226`; `c10202d40`
registers the target on both floors and `14d5d2dbe` updates the
documentation. `records/harnesses/qualify.py` ran every qualifying command,
and `records/harnesses/negctl.py` ran the negative control.

## Host

Linux `6.17.0-1026-nvidia` on NVIDIA Grace (aarch64), Ubuntu gcc 13.3.0 as
`cc`, GNU ld 2.42, and rustc/cargo 1.97.1 through the rustup proxies
(`records/tools.json`). Cargo ran with `--locked --offline -j 8`, with PATH
led by the pinned AY/Clean package directory and ambient `TCG_*`/`TRUST_CG_*`
variables removed.

## What was wrong

trust-ir aggregates are values; the backend represents one by the address of
its storage. `InsertField` and `InsertElement` stored the new member into the
source aggregate's storage and returned the same address, so any later read
of the source saw the inserted member. `swap(s) = insert(insert(s, 0, s.1),
1, s.0)` returned `{2,2}` for `{1,2}` over `{i64,i64}`, `{f32,f32}` and
`{f16,f16}` at every level (`records/negative-control/prefix-cli-swap-reproducer.log.gz`,
12/12 cases; the reproducer is `records/reproducer/`).

A second fault shares the mechanism. An aggregate block parameter received
its argument's address, so around a loop it could name a slot that a
re-executed instruction rewrites while the parameter is still read.
`loop_load_prev` has no insert at all: an aggregate `Load` in the loop body
overwrote the value its block parameter carried from the previous iteration.

## The fix

- An insert whose operand has the aggregate type copies the source into a
  fresh stack slot (`Memcpy` of the authoritative extent, since a fresh slot
  overlaps nothing) and writes the member there. It reuses the source's own
  slot only when three exact facts hold: a `Const`, `Load` or insert
  allocated that slot for the source alone, the insert is the source's only
  SSA use in the function, and the source is defined in the same block. A
  materialized `Ty::Sequence` insert copies the buffer size its constant
  recorded.
- Every pointer-represented aggregate block parameter owns a slot, and each
  edge copies the argument's bytes into it. With two or more aggregate
  parameters, an argument that is not storage its own lowering allocated is
  staged first, because an edge may pass one parameter's storage (or a field
  of it) to another. A lone parameter receiving such an argument uses
  `Memmove`, since that argument can only overlap by being the slot itself.
- An `InsertField` whose operand is a pointer to the aggregate (the rustc
  bridge's field store into an `Alloca`, which the reference interpreter
  rejects) keeps its store-through lowering.

## Results on the qualifying source

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_aggregate_insert_linux -- --show-output --test-threads=1` (objects retained) | `test result: ok. 7 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 3.12s` |
| `cargo test -p trust-cg-lower --lib` | `test result: ok. 1879 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 3.27s` |
| `cargo test -p trust-cg-codegen --lib` | `test result: ok. 4113 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 4.65s` |
| `cargo check -p trust-cg-codegen --features verify` | exit 0 |
| `bash scripts/check_fmt.sh` | `check_fmt: OK — every workspace file matches rustfmt` |
| `python3 scripts/check_documentation.py --write`, then `--check` | no change; current |
| `python3 scripts/generate_diagnostics_inventory.py --check` | current |
| `python3 scripts/native_test_host_matrix.py --check` | exit 0 |
| `python3 -B -m unittest -v scripts/tests/test_linux_aarch64_gate.py scripts/tests/test_darwin_aarch64_gate.py scripts/tests/test_linux_aarch64_bridge_gate.py` | `Ran 94 tests`, `OK (skipped=1)` (the `/proc` resident-set supervision row) |

Aggregate-related floor targets, and the two lower targets whose pins
changed (`records/commands/lower-aggregate-targets.log.gz`,
`codegen-aggregate-targets.log.gz`):

| Target | `test result:` |
| --- | --- |
| trust-cg-lower `aarch64_aggregate_stack_abi` | ok. 4 passed; 0 failed |
| trust-cg-lower `aarch64_hva_abi` | ok. 4 passed; 0 failed |
| trust-cg-lower `aggregate_constants` | ok. 13 passed; 0 failed |
| trust-cg-lower `packed_aggregate_constants` | ok. 8 passed; 0 failed |
| trust-cg-lower `niche_enum_codec` | ok. 18 passed; 0 failed |
| trust-cg-lower `trust_ir_construct_inventory` | ok. 15 passed; 0 failed |
| trust-cg-lower `aggregate_ops` (not a floor target) | ok. 14 passed; 0 failed |
| trust-cg-lower `packed_array_stride` (not a floor target) | ok. 10 passed; 0 failed |
| trust-cg-codegen `aggregate_call_results` | ok. 1 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_aggregate_stack_linux` | ok. 1 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_hva_linux` | ok. 2 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_niche_enum_linux` | ok. 4 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_sret_linux` | ok. 8 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_direct_enums_linux` | ok. 6 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_struct_byval` | ok. 1 passed; 0 failed |

Floor sweep: all 150 Linux floor targets ran through `cargo test` in three
chunks (`records/harnesses/floor_chunks.py`,
`records/commands/floor-sweep-{0,1,2}-cargo.log.gz`): 150 `test result:`
lines, 913 passed, 0 failed. This is not the floor runner
(`scripts/check_linux_aarch64.py`), so runtime skips were not rejected and no
floor report was produced.

### `e2e_aarch64_aggregate_insert_linux`

The corpus (`crates/trust-cg-codegen/tests/fixtures/aggregate_insert`) has
one function per shape; each reads a source aggregate after inserting into
it, or carries one around a loop. The C driver calls each with several
inputs and compares every returned field, and every byte a shape may write,
bit-exactly with a C reimplementation: 27 shapes, 1,424 checks per level.
The rows are:

- canonical trust-ir: the corpus validates with `trust_ir_build::validate_module`;
- the reference interpreter equals a closed-form model on 21 shapes (every
  shape without pointer arguments or memory);
- the lowered LIR pins each decision: `swap_i64` copies its parameter once
  and writes every field into that copy, the four-insert result chains are
  built in place, `const_twice`, `fanout` and `copy_shape` copy their shared
  sources, `loop_rotate` gives each block parameter one slot that both edges
  fill, and `phi_join`'s parameter always receives its own slot;
- a bridge-shaped `InsertField` over an `Alloca` pointer is still a store
  through that pointer;
- the corpus compiles for aarch64-unknown-linux-gnu and aarch64-apple-darwin
  at O0-O3;
- Linux only: each ELF object links with `cc` against the driver and prints
  `aggregate-insert shapes_failed=0 checks=1424 failures=0` at O0-O3
  (`records/objects/api/*.stdout`; the test's retained objects are under
  `api/` because the repository ignores `target/` paths).

The objects from the test and from the CLI (`trust-cg --format=text -c
-O<n> --target aarch64-unknown-linux-gnu`, `records/objects/cli/`) are
byte-identical at each level:

| Level | SHA-256 (decoded, first 16) | Bytes |
| --- | --- | ---: |
| O0 | `dcc36a61cca327e9` | 10,552 |
| O1 | `4ef4d30ea2e0f0a8` | 8,504 |
| O2 | `739fb251e71a19d4` | 7,976 |
| O3 | `a9e9939058583b1b` | 7,784 |

## Negative control

`negctl.py` replaced `adapter.rs` with the base revision's
(`fa82373bd`, from `306912d63`), kept every test and fixture at the head,
and restored the head blob (`7992f4720`) afterwards with an empty
`git status` (`records/negative-control/identity.json`).

- The target failed: `test result: FAILED. 4 passed; 3 failed` — the C-oracle
  row, the copy/in-place LIR row (`swap_i64` has no copy: `(0, 0, 0)`
  against `(1, 1, 0)`) and the block-parameter row. The interpreter,
  canonical-corpus, bridge and compile rows are independent of the adapter's
  insert lowering and passed.
- The CLI build of the same corpus failed 23 of 27 shapes at every level,
  505 of 1,424 checks (`records/negative-control/objects/cli-O*.stdout`).

Per-shape failures (pre-fix is the negative control; fixed is the
qualifying run):

| Shape | Checks per level | Pre-fix failures O0/O1/O2/O3 | Fixed failures O0/O1/O2/O3 |
| --- | ---: | --- | --- |
| `swap_i64` | 8 | 4/4/4/4 | 0/0/0/0 |
| `swap_f32` | 8 | 4/4/4/4 | 0/0/0/0 |
| `swap_f16` | 8 | 4/4/4/4 | 0/0/0/0 |
| `old_new` (parameter source, field read after the insert) | 64 | 16/16/16/16 | 0/0/0/0 |
| `big_callee` (32-byte by-reference parameter, called from C) | 20 | 0/0/0/0 | 0/0/0/0 |
| `big_caller` (the same callee called from trust-cg) | 16 | 4/4/4/4 | 0/0/0/0 |
| `load_insert` | 96 | 16/16/16/16 | 0/0/0/0 |
| `global_insert` | 24 | 4/4/4/4 | 0/0/0/0 |
| `nested_inner` (insert into an extracted inner struct) | 64 | 30/30/30/30 | 0/0/0/0 |
| `nested_outer` (aggregate-valued insert) | 64 | 31/31/31/31 | 0/0/0/0 |
| `array_elem` (`InsertElement` on `[i64; 4]`) | 64 | 20/20/20/20 | 0/0/0/0 |
| `copy_shape` | 64 | 32/32/32/32 | 0/0/0/0 |
| `select_shape` | 128 | 64/64/64/64 | 0/0/0/0 |
| `phi_join` | 128 | 64/64/64/64 | 0/0/0/0 |
| `loop_prev` | 96 | 56/56/56/56 | 0/0/0/0 |
| `loop_exit_old` | 96 | 22/22/22/22 | 0/0/0/0 |
| `loop_swap` | 48 | 20/20/20/20 | 0/0/0/0 |
| `loop_rotate` | 96 | 0/0/0/0 | 0/0/0/0 |
| `const_twice` | 16 | 8/8/8/8 | 0/0/0/0 |
| `call_result` | 16 | 4/4/4/4 | 0/0/0/0 |
| `store_after` | 80 | 16/16/16/16 | 0/0/0/0 |
| `vec_shape` (`<4 x i32>` register value) | 16 | 0/0/0/0 | 0/0/0/0 |
| `packed_shape` (explicit-offset path) | 16 | 4/4/4/4 | 0/0/0/0 |
| `fanout` | 64 | 46/46/46/46 | 0/0/0/0 |
| `vec_f32` (`<4 x f32>` register value) | 16 | 0/0/0/0 | 0/0/0/0 |
| `loop_load_prev` (no insert) | 12 | 4/4/4/4 | 0/0/0/0 |
| `loop_const_prev` (in-place insert into a constant in a loop) | 96 | 32/32/32/32 | 0/0/0/0 |

The four shapes that pass before the fix pass for a reason: `big_callee` is
called from C, which passes a copy; `loop_rotate` inserts into two distinct
original storages that are never read again; the vector shapes are register
values. Had inserts copied into per-instruction slots while block
parameters kept receiving addresses, `loop_rotate` and `loop_const_prev`
would read a slot that a later iteration rewrites; that is reasoned from the
lowering, not measured, and the LIR rows pin the parameter storage that
prevents it.

## Characterization corpus and the remaining defect

`records/characterization/` is the first corpus, in the historical
aggregate-typed `extractfield` spelling that the adapter still accepts, with
one extra probe: `cg_calls_c` passes a 32-byte aggregate to a C callee
`c_mutate` that writes its by-value parameter, as AAPCS64 permits (the
caller must pass a copy). Before the fix 22 of 26 shapes failed (473 of
1,332 checks per level); after it only `cg_calls_c` fails (4 of 16 checks
at every level, `records/negative-control/{prefix,fixed}-characterization.log.gz`).
trust-cg passes a by-value aggregate over 16 bytes as the address of the
caller's own storage instead of a copy, so the C callee's write changes the
caller's value. That is a call-lowering ABI defect, not insert value
semantics; it is left open and recorded in LIMITATIONS.md. It is not in the
floor corpus, which must pass.

## Evidence boundary

This is native execution against GCC 13 and the trust-ir reference
interpreter on one Linux host at O0-O3, plus structural checks of the
lowered LIR. It is not a proof. The in-place reuse argument (an unshared
slot, one use, same block) and the block-parameter argument (a value derived
from a slot without passing a block parameter is dominated by the slot's
producer, so it is dead before the producer runs again) are stated in the
adapter, not machine-checked. Direct-tag enum payload inserts stay refused
(`EnumPayloadInsertUnsupported`). The Darwin rows are counted from cfg gates
on this host and have not run on a Darwin floor host. The extra copies (one
per insert whose source stays live, one per aggregate block-parameter edge)
are not measured against the performance ledger.

## Reproduce

From a checkout of `14d5d2dbe` with the host prerequisites above:

```sh
cargo test --locked --offline -p trust-cg-codegen --test e2e_aarch64_aggregate_insert_linux
cargo build --locked --offline -p trust-cg-cli
bash reports/perf/2026-09-23-linux-aggregate-insert/records/harnesses/run_fixture.sh OUT target/debug/trust-cg
```

`run_fixture.sh` and the other harnesses name the absolute paths of the
qualifying run; edit them for another checkout.
