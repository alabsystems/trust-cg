# By-reference composite arguments on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

> Superseded in part by
> [`2026-09-23-linux-large-aggregate-args-2`](../2026-09-23-linux-large-aggregate-args-2/README.md):
> the inline, unbounded selection copy qualified here made compile time grow
> quadratically with the argument (47 s at O1 for 72,000 bytes) and left an
> invoke whose block also held a `Load` refused. The trust-ir adapter now
> makes the copy with a bounded cost. The wrong-code evidence below stands.

This run qualifies two fixes on the branch `fix/aapcs64-large-aggregate-copy`:

- a wrong-code fix in AArch64 instruction selection
  (`crates/trust-cg-lower/src/isel.rs`): a call that passes a composite over
  16 bytes that is not an HFA/HVA now passes a copy the caller owns. The fix
  is `cc42cb5f8`; `299a715a0` registers the new target
  `e2e_aarch64_large_aggregate_args_linux` on both floors and `d70552b6a`
  updates the documentation.
- a regression fix in the trust-ir adapter
  (`crates/trust-cg-lower/src/adapter.rs`): the aggregate insert fix
  (`ff27f9226`) made zero-sized values fail to compile. The fix is
  `5b4f73f59` and `adf503f11` updates the documentation.

The qualifying run used clean source `adf503f11f7b0819399553cdd966c7b389e9cf26`
(tree `dc31b581400a7ad9c50c1df9fdb08efb17bbed57`). The branch base is
`9cc2988fc`, origin/main `306912d63` plus the aggregate insert fix, and the
trust-ir pin is `7b9146ba`. `git status --porcelain --untracked-files=all`
was empty before and after (`records/source.json`), and after each negative
control (`records/negative-control/identity.json`).
`records/harnesses/qualify.py` ran every qualifying command, and
`records/harnesses/negctl.py` ran the negative controls.

## Host

Linux `6.17.0-1026-nvidia` on NVIDIA Grace (aarch64), Ubuntu gcc 13.3.0 as
`cc`, GNU ld 2.42, and rustc/cargo 1.97.1 through the rustup proxies
(`records/tools.json`). Cargo ran with `--locked --offline -j 8`, with PATH
led by the pinned AY/Clean package directory and ambient `TCG_*`/`TRUST_CG_*`
variables removed.

## What was wrong

### By-reference composite arguments

AAPCS64 §6.8.2 B.4 (DarwinPCS keeps the rule) replaces a composite argument
larger than 16 bytes that is not an HFA/HVA by a pointer to a copy that the
caller allocates. The callee owns that copy for the call and may write it;
a C callee that assigns to its parameter does. trust-cg represents an
aggregate value by the address of its storage, and selection put that
address itself in the argument register (or the outgoing stack slot once
X0-X7 were used). A callee's write therefore changed the caller's value. The
aggregate insert run found it with its `cg_calls_c` probe (4 of 16 checks
wrong at every level); `records/negative-control/byref/characterization/`
reproduces that here.

### Zero-sized values after the aggregate insert fix

The aggregate insert fix gives block parameters, staging slots and insert
results storage of their own, filled by a `Memcpy` of the value's extent.
For a zero-sized value (`()`, an empty struct) that extent is 0. Selection
lowers a zero-length `Memcpy` to no machine instruction, and the
dataflow-integrity gate refuses an effectful LIR instruction whose effect
produced none (`[TCG-DATAFLOW-INTEGRITY-FAIL] ... kind=unwitnessed-effect`).
Shapes that origin/main compiled became hard compile errors at every level.
An independent verifier of `ff27f9226` reported it with the reproducer that
`records/objects/zero-sized/zst_repro.trust_ir` retains verbatim.

## The fixes

- `stage_by_reference_argument_copies` (shared by the direct, variadic,
  invoke and indirect call paths) runs before the sret buffer is set up and
  before any argument register or outgoing stack slot is written. For every
  argument the classification passes by reference (`Indirect`, or a >16-byte
  non-HFA `Stack` slot), it allocates a frame slot of the type's size,
  aligned to the type (at least 8). `emit_inline_copy` fills it with LDP/STP
  and residual lanes, advancing both bases every 256 bytes so no pair offset
  leaves its imm7 range. The copy's address is what is passed. No libcall is
  emitted: an invoke's block must hold exactly one call. Nothing elides the
  copy, because selection cannot see whether the source storage is dead
  after the call.
- `CallAbiFacts` gains `by_reference_argument_copies`, and sibling tail-call
  eligibility refuses such a call by name (`ByReferenceArgumentCopy`): the
  copy lives in the frame the tail branch frees. The function-wide
  stack-address guard in `run_tail_call` already kept these calls; the named
  refusal no longer depends on it.
- `copy_into_fresh_slot` and `copy_aggregate_block_args` emit no
  `Memcpy`/`Memmove` when the extent is 0; the parameter still owns its
  slot. `EnumPayloadInsertUnsupported` no longer says the fresh-slot insert
  lowering is not implemented: it exists and is not wired to the direct-tag
  enum carrier.

The callee side is unchanged: a trust-cg function uses the caller's copy as
its by-reference parameter's storage and never writes it (value-semantic
inserts copy a parameter source), and passing that parameter on copies it
again.

## Results on the qualifying source

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_large_aggregate_args_linux -- --show-output --test-threads=1` (objects retained) | `test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 2.83s` |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_aggregate_insert_linux -- --show-output --test-threads=1` | `test result: ok. 10 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 4.00s` |
| `cargo test -p trust-cg-lower --lib` | `test result: ok. 1886 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 3.29s` |
| `cargo test -p trust-cg-opt --lib` | `test result: ok. 3535 passed; 0 failed; 2 ignored; 0 measured; 0 filtered out; finished in 1.75s` |
| `cargo test -p trust-cg-ir --lib` | `test result: ok. 524 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s` |
| `cargo test -p trust-cg-codegen --lib` | `test result: ok. 4113 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 4.63s` |
| `cargo check -p trust-cg-codegen --features verify` | exit 0 |
| `bash scripts/check_fmt.sh` | `check_fmt: OK — every workspace file matches rustfmt` |
| `python3 scripts/check_documentation.py --write`, then `--check` | no change; current |
| `python3 scripts/generate_diagnostics_inventory.py --check` | current |
| `python3 scripts/native_test_host_matrix.py --check` | exit 0 |
| `python3 scripts/check_evidence_archive.py --plan` | exit 0 |
| `python3 -B -m unittest -v scripts/tests/test_linux_aarch64_gate.py scripts/tests/test_darwin_aarch64_gate.py scripts/tests/test_linux_aarch64_bridge_gate.py` | `Ran 94 tests`, `OK (skipped=1)` (the `/proc` resident-set supervision row; the `bridge gate: FAIL` line in the log is a fixture of a test that passes) |

The lower `--lib` total includes the seven new selection rows
(`isel::tests::by_reference_*`, `by_value_composites_get_no_by_reference_copy`)
and the opt total the new `test_by_reference_argument_copy_keeps_the_bl`.

ABI floor targets and the adapter targets the zero-sized fix touches
(`records/commands/lower-targets.log.gz`, `codegen-abi-targets.log.gz`):

| Target | `test result:` |
| --- | --- |
| trust-cg-lower `aarch64_adapter_target_abi` | ok. 4 passed; 0 failed |
| trust-cg-lower `aarch64_aggregate_stack_abi` | ok. 4 passed; 0 failed |
| trust-cg-lower `aarch64_hva_abi` | ok. 4 passed; 0 failed |
| trust-cg-lower `aarch64_variadic_abi` | ok. 3 passed; 0 failed |
| trust-cg-lower `aggregate_ops` | ok. 14 passed; 0 failed |
| trust-cg-lower `direct_enum_projection` | ok. 16 passed; 0 failed |
| trust-cg-lower `packed_array_stride` | ok. 10 passed; 0 failed |
| trust-cg-lower `trust_ir_conformance_manifest` | ok. 6 passed; 0 failed |
| trust-cg-codegen `aggregate_call_results` | ok. 1 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_aggregate_stack_linux` | ok. 1 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_call_arg_ptr_theft` | ok. 2 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_calling_conv` | ok. 2 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_hva_linux` | ok. 2 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_sret_linux` | ok. 8 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_struct_byval` | ok. 1 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_tail_call_abi` | ok. 6 passed; 0 failed |
| trust-cg-codegen `e2e_aarch64_variadic_linux` | ok. 1 passed; 0 failed |
| trust-cg-codegen `enum_field_projection` | ok. 13 passed; 0 failed |
| trust-cg-codegen `multi_result_call_abi` | ok. 1 passed; 0 failed |

Floor sweep: all 151 Linux floor targets ran through `cargo test` in three
chunks (`records/harnesses/floor_chunks.py`,
`records/commands/floor-sweep-{0,1,2}-cargo.log.gz`): 151 `test result:`
lines, 920 passed, 0 failed, 0 ignored. This is not the floor runner
(`scripts/check_linux_aarch64.py`), so runtime skips were not rejected and no
floor report was produced.

### `e2e_aarch64_large_aggregate_args_linux`

The corpora (`crates/trust-cg-codegen/tests/fixtures/large_aggregate_args`)
pass by-reference composites of 20 bytes (five `i32`), 24, 32, 16-aligned 32
(`{i128, i64}`) and 320 bytes. Every C callee in `driver.c` digests the bytes
it received, checks each copy's alignment and that two by-reference
parameters do not share an address, and then writes every by-reference
parameter. Each trust-cg function stores the aggregates it passed into an
out-buffer after its calls. The driver requires those bytes unchanged and
every digest equal to the digest of the original values: 19 shapes, 1,047
checks per level. The rows are:

- the three corpora are canonical trust-ir;
- the main and tail corpora compile for aarch64-unknown-linux-gnu and
  aarch64-apple-darwin at O0-O3; the variadic corpus compiles for Linux and
  Darwin refuses it with `[TCG-VARARG-ABI]` (DarwinPCS by-reference
  anonymous arguments stay refused);
- a call passing a composite by reference keeps its `BL` at every level on
  both targets, while the register-only control `tail_scalar` becomes a `B`
  at O2/O3 (`(B, BL)` = `(0, 4)` at O0/O1, `(1, 3)` at O2/O3);
- Linux only: each level's three objects link with `cc` against the driver
  and print `large-aggregate-args shapes_failed=0 checks=1047 failures=0` at
  O0-O3 (`records/objects/api/*.stdout`).

The objects the test retained and the CLI's (`trust-cg --format=text -c
-O<n> --target aarch64-unknown-linux-gnu`, `records/objects/cli/`) are
byte-identical at every level:

| Corpus | Level | SHA-256 (decoded, first 16) | Bytes | API = CLI |
| --- | --- | --- | ---: | --- |
| corpus | O0 | `08a79b94c6401437` | 5,744 | yes |
| corpus | O1 | `b15f68119b3f0de9` | 5,640 | yes |
| corpus | O2 | `2a530b31ddcd7ec6` | 5,664 | yes |
| corpus | O3 | `a91207ec91bb4d48` | 5,664 | yes |
| tail | O0 | `7e2c5821fd06f755` | 1,752 | yes |
| tail | O1 | `60850bc1d8df0cd8` | 1,752 | yes |
| tail | O2 | `e7a1492126fdec31` | 1,728 | yes |
| tail | O3 | `e7a1492126fdec31` | 1,728 | yes |
| variadic | O0 | `c74c374d7ef28509` | 1,536 | yes |
| variadic | O1 | `b7c9c2368d6ed362` | 1,536 | yes |
| variadic | O2 | `b7c9c2368d6ed362` | 1,536 | yes |
| variadic | O3 | `b7c9c2368d6ed362` | 1,536 | yes |

Per-shape failures (pre-fix is negative control A; fixed is the qualifying
run's CLI objects):

| Shape | Checks per level | Pre-fix failures O0/O1/O2/O3 | Fixed failures O0/O1/O2/O3 |
| --- | ---: | --- | --- |
| `param_pass` (parameter) | 45 | 36/36/36/36 | 0/0/0/0 |
| `const_pass` (constant, passed twice in sequence) | 15 | 12/12/12/12 | 0/0/0/0 |
| `load_pass` (load; the C source is also checked) | 81 | 36/36/36/36 | 0/0/0/0 |
| `twice_pass` (one value as two arguments) | 45 | 36/36/36/36 | 0/0/0/0 |
| `spill_pass` (pointer in an outgoing stack slot) | 45 | 36/36/36/36 | 0/0/0/0 |
| `mixed_pass` (20/24/32/16-aligned 32-byte composites, an HFA, scalars, two stack slots) | 60 | 44/44/44/44 | 0/0/0/0 |
| `huge_pass` (320 bytes, two copy windows) | 123 | 120/120/120/120 | 0/0/0/0 |
| `indirect_pass` (function pointer) | 45 | 36/36/36/36 | 0/0/0/0 |
| `sret_pass` (32-byte sret result as well) | 81 | 36/36/36/36 | 0/0/0/0 |
| `loop_pass` (same argument each iteration) | 60 | 39/39/39/39 | 0/0/0/0 |
| `cg_writes_param` (insert result of the parameter) | 81 | 36/36/36/36 | 0/0/0/0 |
| `cg_to_cg` (trust-cg callee that inserts and calls C) | 45 | 0/0/0/0 | 0/0/0/0 |
| `phi_pass` (block parameter) | 78 | 24/24/24/24 | 0/0/0/0 |
| `tail_pass` | 45 | 0/0/0/0 | 0/0/0/0 |
| `tail_const` | 3 | 0/0/0/0 | 0/0/0/0 |
| `tail_huge` | 123 | 0/0/0/0 | 0/0/0/0 |
| `tail_scalar` (control) | 3 | 0/0/0/0 | 0/0/0/0 |
| `var_mut_pass` (anonymous arguments written through `va_arg(ap, Quad *)`) | 45 | 36/36/36/36 | 0/0/0/0 |
| `var_value_pass` (anonymous arguments read by value) | 24 | 0/0/0/0 | 0/0/0/0 |

13 of 19 shapes, 527 of 1,047 checks, failed at every level before the fix.
The six that pass before it pass for a reason: `cg_to_cg`'s callee already
copies its parameter for the insert, so the C callee writes that copy;
`var_value_pass` has no writer; and the tail shapes never read their value
after the call. Their execution rows are controls; the tail change is shown
by the branch counts. Before the fix, `tail_pass` and `tail_huge` forwarded
their incoming pointer with a tail branch (`(B, BL)` = `(3, 1)` at O2/O3 on
Linux: `c_mut_quad`, `c_mut_huge` and `c_scalar` through `JUMP26`). That was
not wrong code, since the memory belonged to their own caller's copy, but a
caller-frame copy makes it impossible. Such calls now keep their `BL`: with
the fix only `c_scalar` is a `JUMP26`.

The aggregate insert report's characterization probe `cg_calls_c`
(`records/characterization/`, same corpus and driver) fails 4 of 16 checks at
every level before the fix
(`records/negative-control/byref/characterization/prefix-O*.stdout`) and
passes 1,332 of 1,332 checks at every level after it (`fixed-O*.stdout`).

### Zero-sized values

`crates/trust-cg-codegen/tests/fixtures/aggregate_insert/zero_sized.trust_ir`
has eight functions. Three new rows of `e2e_aarch64_aggregate_insert_linux`
use it:

- the lowered LIR has no zero-length copy on the fixed paths, and the
  reference interpreter agrees with a closed-form model on the six shapes it
  executes (it refuses `undef ()`). The older aggregate-field store that
  `zero_insert` and `field_insert_twice` reach still emits a zero-length
  `Memmove`; selection lowers it to a `memmove` libcall, the integrity gate
  accepts it, and the row pins it as it is;
- the corpus and the verbatim reproducer compile for Linux and Darwin at
  O0-O3;
- Linux only: the corpus runs against `zero_sized_driver.c` at O0-O3,
  `zero-sized shapes_failed=0 checks=40 failures=0`.

`records/harnesses/run_zero_sized.sh` compiles each function alone and
the reproducer at O0-O3 through the CLI. Every cell below held at all four
levels (`records/commands/zero-sized-fixture.log.gz`,
`records/negative-control/{zero-sized,origin-main}-zero-sized-fixture.log.gz`):

| Shape | origin/main adapter (`306912d63`) | Insert fix (`9cc2988fc`) | Fixed |
| --- | --- | --- | --- |
| verbatim reproducer (two `()` parameters, `const () { }`) | compiles | refused (integrity) | compiles |
| `unit_pair` (two `()` parameters, `undef ()`) | refused (`not defined before use`) | refused (integrity) | compiles, runs |
| `empty_pair` (two empty-struct parameters, swapped on two edges) | compiles | refused (integrity) | compiles, runs |
| `empty_loop` (two empty-struct parameters rotated in a loop) | compiles | refused (integrity) | compiles, runs |
| `empty_const_param` (one parameter, constant argument) | compiles | refused (integrity) | compiles, runs |
| `zero_insert` (insert into a zero-sized struct used twice) | compiles | refused (integrity) | compiles, runs |
| `undef_unit_pair` (two `()` parameters, `undef ()`, two edges) | refused (`not defined before use`) | refused (integrity) | compiles, runs |
| `empty_field_loop` (lone parameter, extracted field, Memmove path) | compiles | compiles | compiles, runs |
| `field_insert_twice` (zero-sized field of a sized struct) | compiles | compiles | compiles, runs |

The regression is the verbatim reproducer and the four shapes that
origin/main compiled. The two `undef ()` shapes did not compile at
origin/main either; its adapter handed the parameter the undefined argument's
value. They compile now because a zero-sized parameter owns its slot and
copies nothing.

## Negative controls

`negctl.py` ran three controls, each restoring the HEAD blobs with an empty
`git status` afterwards (`records/negative-control/identity.json`):

- A (`byref`): `isel.rs`, `tail_call.rs`, `trust-cg-ir/src/function.rs` and
  `pipeline.rs` from `9cc2988fc`, every test and fixture at HEAD. The new
  target failed `test result: FAILED. 2 passed; 2 failed` (the tail-branch
  row, `(B, BL)` = `(3, 1)` at Linux O2, and the C-oracle row). The corpus
  and compile rows are independent of the call lowering and passed. The CLI
  fixture failed 13 of 19 shapes, 527 of 1,047 checks, at every level, and
  the characterization probe failed 4 of 16.
- B (`zero-sized`): `adapter.rs` from `9cc2988fc`. The aggregate insert
  target failed `test result: FAILED. 7 passed; 3 failed`: the three
  zero-sized rows (the LIR row saw `unit_pair` emit four zero-length
  `Memcpy`s). The CLI refused six of the eight shapes and the reproducer.
- C (`origin-main`): `adapter.rs` from `306912d63`. The CLI compiled the
  reproducer and the four regressed shapes at O0-O3 (the table above).

## x86-64 (reading only, not changed or executed)

The System V MEMORY class (`is_sysv_memory_byval_aggregate`, a struct or
array over 16 bytes) is passed by value in the outgoing argument area:
`emit_memory_copy_to_outgoing_stack` copies the bytes there before the call,
so the callee writes a copy. The callee binds such a formal to that incoming
area (`LEA` from RBP), which it owns. An enum over 16 bytes is refused
(`reject_x86_aggregate_abi`). Windows x64 passes only the two-`i64`
aggregate by reference, through
`materialize_windows_x64_byref_aggregate_argument`, which copies it into a
fresh 16-aligned slot. Its callee also copies the incoming referent into its
own slot. Every other Windows aggregate is refused. The x86-64 selector has
no sibling tail-call path. No analogue of the AArch64 defect was found, but
nothing here executed x86-64 code.

## Evidence boundary and residuals

This is native execution against GCC 13 on one Linux host at O0-O3, with
object-level checks for Darwin. It is not a proof.

- Darwin is not executed. DarwinPCS classifies these arguments the same way
  and selection shares the code, and the selection rows cover both
  conventions, but no Darwin floor host ran the target.
- Nothing elides the copy. Every by-reference argument costs an inline copy
  of its size, and a call that forwards one in tail position keeps its `BL`,
  including one forwarding its own incoming by-reference parameter (which
  the caller could hand on without a copy when it is the parameter's only
  use). The cost is not measured against the performance ledger. The rustc
  bridge declares Rust by-value aggregates the same way, so its calls
  passing `String`, `Vec` or other composites over 16 bytes now copy too;
  the bridge workspace was not run.
- A copy over 256 bytes is still inline (34 instructions per 256 bytes), so
  a very large by-value aggregate costs code size.
- The zero-length `Memmove` of the older aggregate-field store remains (a
  `memmove` libcall of length 0).

## Reproduce

From a checkout of `adf503f11` with the host prerequisites above:

```sh
cargo test --locked --offline -p trust-cg-codegen --test e2e_aarch64_large_aggregate_args_linux
cargo test --locked --offline -p trust-cg-codegen --test e2e_aarch64_aggregate_insert_linux
cargo build --locked --offline -p trust-cg-cli
bash reports/perf/2026-09-23-linux-large-aggregate-args/records/harnesses/run_fixture.sh OUT target/debug/trust-cg
bash reports/perf/2026-09-23-linux-large-aggregate-args/records/harnesses/run_zero_sized.sh OUT2 target/debug/trust-cg
```

The harnesses name the absolute paths of the qualifying run; edit them for
another checkout.
