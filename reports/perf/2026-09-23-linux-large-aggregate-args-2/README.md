# By-reference arguments with bounded cost, and HFAs with zero-sized members, on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies two further fixes on the branch
`fix/aapcs64-large-aggregate-copy`, found by an independent verifier of the
first by-reference fix (`cc42cb5f8`, qualified in
[`2026-09-23-linux-large-aggregate-args`](../2026-09-23-linux-large-aggregate-args/README.md)):

- a compile-time fix (`899336f46`): the first fix copied every by-reference
  argument inline in instruction selection, fully unrolled, with no size
  limit. The trust-ir adapter now makes the copy with a bounded cost.
- an ABI fix (`9a4cd38d0`): a homogeneous floating-point aggregate with a
  zero-sized member was classified differently from GCC.

`24af965de` registers `e2e_aarch64_hfa_zero_sized_linux` on both floors and
raises the Darwin minimum of `e2e_aarch64_large_aggregate_args_linux`;
`bf991f8dd` updates the documentation. The qualifying run used clean source
`bf991f8ddc4b3f1ebd7b01b4833c12e21bbf1b2e` (tree
`dc31b581400a7ad9c50c1df9fdb08efb17bbed57`; branch base `9cc2988fc`,
origin/main `306912d63`, trust-ir pin `7b9146ba`). `git status --porcelain
--untracked-files=all` was empty before and after (`records/source.json`)
and after each negative control (`records/negative-control/identity.json`).
`records/harnesses/qualify.py` ran every qualifying command and
`records/harnesses/negctl.py` the negative controls.

## Host

Linux `6.17.0-1026-nvidia` on NVIDIA Grace (aarch64), Ubuntu gcc/g++ 13.3.0
as `cc`/`c++`, GNU ld 2.42, and rustc/cargo 1.97.1 through the rustup proxies
(`records/tools.json`). Cargo ran with `--locked --offline -j 8`, with PATH
led by the pinned AY/Clean package directory and ambient `TCG_*`/`TRUST_CG_*`
variables removed.

## What was wrong

### The first by-reference copy did not bound its cost

`cc42cb5f8` staged each by-reference composite (AAPCS64 B.4) as an inline
LDP/STP copy in selection, rebasing every 256 bytes, however large the
argument. The copy became one very long block, and at O1+ the scheduler and
the optimization passes are quadratic in block length. Measured here with
the first fix's sources (control `inline-copy`, each compile limited to 80 s
and 8 GiB of address space):

| Input | Level | First fix: wall, peak RSS, instructions | This fix: wall, peak RSS, instructions |
| --- | --- | --- | --- |
| 72,000-byte argument (`big9000`) | O0 | 0.78 s, 53 MB, 9,630 | 0.01 s, 37 MB, 47 |
| | O1 | 43.77 s, 2.05 GB, 18,972 | 0.01 s, 40 MB, 47 |
| | O2 | 46.87 s, 2.05 GB, 19,350 | 0.01 s, 41 MB, 47 |
| | O3 | 68.65 s, 2.05 GB, 19,350 | 0.02 s, 41 MB, 47 |
| 288,000-byte argument (`big36000`) | O0 | 3.06 s, 117 MB, 38,423 | 0.01 s, 38 MB, 100 |
| | O1-O3 | killed at the 80 s limit, 6.8 GB | 0.02 s, 40-41 MB, 100 |
| 64 calls passing 1 KiB (`many1k`) | O0 | 0.81 s, 54 MB, 8,998 | 0.11 s, 40 MB, 678 |
| | O1-O3 | 41.06-59.46 s, 1.9 GB, 8,809-8,997 | 0.38-0.39 s, 45-47 MB, 677 |
| scaling corpus (both big arguments and 64 × 1 KiB) | O0 | 4.73 s, 125 MB, 57,009 | 0.11 s, 40 MB, 952 |
| | O1-O3 | killed at the 80 s limit | 0.38 s, 49-52 MB, 952-954 |

(`records/negative-control/inline-copy-compile-cost.log.gz` and
`records/commands/compile-cost.log.gz`; the objects are under
`records/negative-control/inline-copy/compile-cost/` and
`records/objects/compile-cost/`.) The branch base, which passed the caller's
own storage and so made no copy, compiled the same inputs in 0.01-0.14 s
(`records/negative-control/base-compile-cost.log.gz`); that was wrong code.

The first fix also left invokes exposed. An invoke's protected block may
hold exactly one call, and an aggregate `Load` in the invoke's own block is
a `memmove` call, so `inv_load_copy` (`fixtures/large_aggregate_args/invoke.trust_ir`)
was refused: `EH call block BlockId(0) contains 2 eligible BL/BLR calls;
exactly one is required by block-granular metadata`, both with the first
fix and at the branch base.

### HFAs with zero-sized members were misclassified

AAPCS64 homogeneity is judged after layout. `detect_homogeneous` refused a
struct with more than four declared fields before flattening, so
`struct { double a; struct {} z; double b, c, d; }` (the verifier's `hfa2`
probe, `records/reproducer/hfa2.trust_ir`) was passed by reference in x0,
while GCC 13 on this host passes d0-d3. It also flattened a zero-length array
member to nothing, so `struct { float a; float z[0]; float b; }` went in
s0/s1 and `struct { double a; double z[0]; double b; }` in d0/d1, where GCC
uses x0 and x0/x1. Probing `gcc -O2 -S` on this host: an empty-struct member
anywhere (first, middle, last, nested, or an array of empty structs) is
skipped; a zero-length array member of any element type (`double[0]`,
`float[0]`, `struct {}[0]`) makes the aggregate non-homogeneous. clang's
`isHomogeneousAggregate` has the same two rules (not run here). rustc 1.97
on this host passes `#[repr(C)]` structs with `()`, an empty struct,
`PhantomData` and also `[f64; 0]` members in d0-d3 (probed with `rustc -O
--emit=asm`), so it disagrees with C about `[T; 0]`.

## The fixes

- The trust-ir adapter (`pass_composites_by_reference`) passes every AArch64
  by-reference composite of a direct, variadic, invoke or indirect call as
  an `I64` pointer, which the classifiers place exactly like the
  by-reference aggregate (next GPR, or an 8-byte stack slot):
  - to the value's own slot, addressed with a fresh `StackAddr`, when a
    `Const`, `Load` or insert made that slot for it alone, the call is its
    only SSA use and it is defined in the same block (the facts the
    aggregate insert fix introduced; the slot is recorded in
    `owned_aggregate_slots`);
  - otherwise to a fresh frame slot, aligned to the type (at least 8), filled
    by a `Memcpy` of the type's size: inline up to 32 bytes, a `memcpy` call
    above.
- An invoke with such an argument moves into a LIR block of its own that the
  current block jumps to after every copy; the exception metadata names the
  new block, which carries the invoke's source location and trust-ir origin.
  The landing pad cannot see a partial copy: the copy is complete before the
  protected call, and it is a fresh slot or storage nothing reads later.
- `AppleAArch64ABI::passes_composite_by_reference` is the one predicate the
  classifier, selection and the adapter use.
- Selection keeps a bounded backstop for aggregate-typed by-reference
  arguments from other LIR producers: an inline copy up to 256 bytes, refused
  above with `[TCG-BYREF-COPY]`. The named tail-call refusal
  (`ByReferenceArgumentCopy`) covers it; the adapter's copies are frame-slot
  addresses, which the function-wide stack-address guard already keeps out
  of tail branches.
- `detect_homogeneous` counts members over the flattened layout, with an
  early exit past four. An empty struct, `()` or a non-empty array of them
  contributes none; a zero-length array makes the aggregate
  non-homogeneous. Arguments and returns, both conventions, share it.

## Results on the qualifying source

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_large_aggregate_args_linux -- --show-output --test-threads=1` (objects retained) | `test result: ok. 8 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 8.69s` |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_hfa_zero_sized_linux -- --show-output --test-threads=1` (objects retained) | `test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.43s` |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_aggregate_insert_linux -- --show-output --test-threads=1` | `test result: ok. 10 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 3.75s` |
| `cargo test -p trust-cg-lower --lib` | `test result: ok. 1889 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 3.26s` |
| `cargo test -p trust-cg-opt --lib` | `test result: ok. 3535 passed; 0 failed; 2 ignored; 0 measured; 0 filtered out; finished in 1.64s` |
| `cargo test -p trust-cg-ir --lib` | `test result: ok. 524 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s` |
| `cargo test -p trust-cg-codegen --lib` | `test result: ok. 4113 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 4.78s` |
| `cargo check -p trust-cg-codegen --features verify` | exit 0 |
| `bash scripts/check_fmt.sh` | `check_fmt: OK — every workspace file matches rustfmt` |
| `python3 scripts/check_documentation.py --write`, then `--check` | no change; current |
| `python3 scripts/generate_diagnostics_inventory.py --check` | current |
| `python3 scripts/native_test_host_matrix.py --check` | exit 0 |
| `python3 scripts/check_evidence_archive.py --plan` | exit 0 |
| `python3 -B -m unittest -v scripts/tests/test_linux_aarch64_gate.py scripts/tests/test_darwin_aarch64_gate.py scripts/tests/test_linux_aarch64_bridge_gate.py` | `Ran 94 tests`, `OK (skipped=1)` (the `/proc` resident-set supervision row) |

ABI and adapter targets (`records/commands/lower-targets.log.gz`,
`codegen-abi-targets.log.gz`), every one `0 failed`:

| Target | Passed |
| --- | ---: |
| trust-cg-lower `aarch64_adapter_target_abi` | 4 |
| trust-cg-lower `aarch64_aggregate_stack_abi` | 4 |
| trust-cg-lower `aarch64_hva_abi` | 4 |
| trust-cg-lower `aarch64_variadic_abi` | 3 |
| trust-cg-lower `aggregate_ops` | 14 |
| trust-cg-lower `direct_enum_projection` | 16 |
| trust-cg-lower `packed_array_stride` | 10 |
| trust-cg-lower `trust_ir_conformance_manifest` | 6 |
| trust-cg-codegen `aggregate_call_results` | 1 |
| trust-cg-codegen `e2e_aarch64_aggregate_stack_linux` | 1 |
| trust-cg-codegen `e2e_aarch64_call_arg_ptr_theft` | 2 |
| trust-cg-codegen `e2e_aarch64_calling_conv` | 2 |
| trust-cg-codegen `e2e_aarch64_direct_enums_linux` | 6 |
| trust-cg-codegen `e2e_aarch64_eh_invoke_trust_ir` | 5 |
| trust-cg-codegen `e2e_aarch64_eh_o2_and_walkthrough_trust_ir` | 6 |
| trust-cg-codegen `e2e_aarch64_eh_resume_trust_ir` | 5 |
| trust-cg-codegen `e2e_aarch64_f16_scalar` | 4 |
| trust-cg-codegen `e2e_aarch64_hva_linux` | 2 |
| trust-cg-codegen `e2e_aarch64_niche_enum_linux` | 4 |
| trust-cg-codegen `e2e_aarch64_sret_linux` | 8 |
| trust-cg-codegen `e2e_aarch64_struct_byval` | 1 |
| trust-cg-codegen `e2e_aarch64_tail_call_abi` | 6 |
| trust-cg-codegen `e2e_aarch64_variadic_linux` | 1 |
| trust-cg-codegen `enum_field_projection` | 13 |
| trust-cg-codegen `multi_result_call_abi` | 1 |

Floor sweep: all 152 Linux floor targets through `cargo test` in three
chunks (`records/harnesses/floor_chunks.py`,
`records/commands/floor-sweep-{0,1,2}-cargo.log.gz`): 152 `test result:`
lines, 928 passed, 0 failed. A further 69 AArch64-related codegen targets
outside the floor (`records/harnesses/extra_targets.txt`: JIT, EH, Darwin
object-only, ABI probes) ran in one `--no-fail-fast` invocation
(`records/commands/extra-codegen-targets.log.gz`): 69 `test result:` lines,
661 passed, 0 failed. This is not the floor runner, so runtime skips were
not rejected and no floor report was produced.

### `e2e_aarch64_large_aggregate_args_linux`

The corpus (`crates/trust-cg-codegen/tests/fixtures/large_aggregate_args`)
now has 22 C-checked shapes, 1,089 checks per level (the first run's 19,
plus a 40-byte argument just above the inline limit, a 72,000-byte argument
copied and passed from its own slot, and one 1 KiB value passed to eight
calls in a row), and an invoke corpus checked by a C++ oracle whose callees
write their parameter and throw on odd input, 34 checks per level
(`inv_param`, `inv_load_copy` and `inv_load_fast` with a 320-byte `Load` in
the invoke's own block, and a 72,000-byte `inv_giant`). The rows:

- the five corpora are canonical trust-ir;
- the main, tail, invoke and scaling corpora compile for Linux and Darwin at
  O0-O3, and the variadic corpus for Linux (Darwin refuses it by name);
- tail position: `(B, BL)` = `(0, 5)` at O0/O1 and `(1, 4)` at O2/O3 on both
  targets (`tail_huge`'s copy adds a `BL memcpy`; the scalar control is the
  one `B`);
- the scaling corpus emits at most 1,400 instructions at every level on both
  targets (measured 952-954) and exactly 138 `BL`s (one per call, one
  `memcpy` per copy, one `memmove` per aggregate load and store);
- every invoke with a by-reference argument is alone in its LIR block, named
  by the exception metadata, and its predecessor holds the copy (none for
  `inv_load_fast`, which passes the load's slot);
- the adapter's decisions on the LIR: `Memcpy` lengths `param_pass` [32],
  `const_pass` [32, 32], `load_pass` [32], `twice_pass` [32, 32], `five_pass`
  [40], `giant_pass` [72000], `giant_load_pass` [] and `many_pass`
  [1024 × 8];
- Linux only: `large-aggregate-args shapes_failed=0 checks=1089 failures=0`
  and `large-aggregate-invoke shapes_failed=0 checks=34 failures=0` at O0-O3.

Objects from the test (`records/objects/api/`) and from the CLI
(`records/objects/cli/`) are byte-identical at every level:

| Corpus | Level | SHA-256 (decoded, first 16) | Bytes |
| --- | --- | --- | ---: |
| corpus | O0 | `c9d40ab614b6ebf1` | 7,896 |
| corpus | O1 | `cd9be99021222dde` | 7,704 |
| corpus | O2 | `480d2617778c6486` | 7,824 |
| corpus | O3 | `d7e0259f13ecea09` | 7,824 |
| tail | O0 | `55c722a1d9240c0e` | 1,672 |
| tail | O1 | `e2c56eb4fa4cc983` | 1,664 |
| tail | O2-O3 | `a9376b24e9d97b37` | 1,640 |
| variadic | O0 | `c74c374d7ef28509` | 1,536 |
| variadic | O1-O3 | `b7c9c2368d6ed362` | 1,536 |
| invoke | O0 | `ed0d027d01ef695b` | 3,752 |
| invoke | O1 | `2dc79ac4d4bdc5b9` | 3,712 |
| invoke | O2-O3 | `87e4ebd43a2afd0c` | 3,744 |

### `e2e_aarch64_hfa_zero_sized_linux`

The corpus (`crates/trust-cg-codegen/tests/fixtures/hfa_zero_sized`,
generated by `records/harnesses/gen_hfa_zero_sized.py`) has nine shapes,
each in four directions (trust-cg passes it to C, C passes it to trust-cg,
trust-cg returns it to C, C returns it to trust-cg), 10 checks each:

| Shape | GCC placement | Old classifier |
| --- | --- | --- |
| `de` `{double, struct {}, double ×3}` | d0-d3 | by reference (5 fields) |
| `du` `{double, (), double ×3}` | d0-d3 | by reference (5 fields) |
| `del` `{struct {}, double ×4}` | d0-d3 | by reference (5 fields) |
| `dea` `{double, struct {}[2], double ×3}` | d0-d3 | by reference (5 fields) |
| `dn` `{double, struct { struct {} }, double ×2}` | d0-d2 | d0-d2 |
| `fe` `{float, struct {}, float}` | s0-s1 | s0-s1 |
| `da` `{double, double[0], double ×3}` | x0 by reference | by reference |
| `fa0` `{float, float[0], float}` | x0 | s0-s1 |
| `da2` `{double, double[0], double}` | x0, x1 | d0-d1 |

The old-classifier column follows from its code (a declared-field limit
before flattening; zero-length arrays flattened to nothing), not from a
per-shape run: with it the native driver dies with SIGSEGV before printing a
shape line. The rows: the corpus is canonical trust-ir; the translated types
classify as GCC places them, as arguments under both conventions and as
returns; the corpus compiles for Linux and Darwin at O0-O3; and on Linux
`hfa-zero-sized shapes_failed=0 checks=90 failures=0` at O0-O3. The test's
and the CLI's objects are byte-identical, and identical at every level
(`b0dbd90792d136df`, 8,576 bytes: the functions are straight-line loads,
stores and calls).

## Negative controls

Each control changed only the named files at the qualifying HEAD, kept every
test, fixture and script at HEAD, saved its diff
(`records/negative-control/<control>.diff`) and restored the HEAD blobs with
an empty `git status`:

- `base`: `adapter.rs`, `isel.rs`, `abi.rs`, `function.rs`, `tail_call.rs`
  and `pipeline.rs` from the branch base `9cc2988fc`. The large-argument
  target failed `test result: FAILED. 1 passed; 7 failed` (only the
  canonical-corpus row passed; the compile row failed on the invoke corpus's
  EH refusal), the HFA target `FAILED. 2 passed; 2 failed`, the CLI fixture
  failed 16 of 22 shapes, 545 of 1,089 checks, at every level (the first
  run's 13 shapes with the same counts, plus `five_pass`, `giant_pass` and
  `many_pass`), the invoke corpus did not compile at any level, the
  characterization probe failed 4 of 16, and the HFA driver died with
  SIGSEGV at every level.
- `inline-copy`: `adapter.rs`, `isel.rs` and `abi.rs` from `9a4cd38d0` (the
  first fix with the HFA fix): the compile-cost table above, and the invoke
  corpus refused at O0 with the EH message quoted above.
- `hfa`: `9a4cd38d0`'s `abi.rs` hunks reverse-applied. The HFA target failed
  `FAILED. 2 passed; 2 failed` (classification and native rows) and the
  driver died with SIGSEGV at every level.
- `zero-sized`: the two zero-extent guards removed from `adapter.rs`. The
  aggregate insert target failed `FAILED. 7 passed; 3 failed` (its three
  zero-sized rows) and the CLI refused six of the eight zero-sized shapes and
  the reported reproducer at every level with
  `[TCG-DATAFLOW-INTEGRITY-FAIL]`.

## Evidence boundary and residuals

Native execution against GCC 13 (C and C++) on one Linux host at O0-O3, with
object, code-size, classification and LIR checks for Darwin. Not a proof.

- Darwin is not executed. DarwinPCS classifies these arguments the same way
  and the code is shared; clang's HFA rules match GCC's for these shapes by
  reading clang's classifier, not by running it.
- rustc treats a Rust `[T; 0]` member as ignorable where C disqualifies the
  aggregate; trust-cg follows C (the module's `StructPassingPolicy::NativeC`),
  so such a Rust type is placed differently from rustc. The rustc bridge
  workspace was not run.
- Each copy site owns a frame slot (the 64-call row uses 64 KiB of frame),
  and the existing frame epilogue releases a large frame in 4,080-byte
  `ADD SP` steps, the one part of the emitted code that grows with the
  argument (100 instructions for the 288,000-byte case against 47 for
  72,000). Copies of 33-256 bytes are now `memcpy` calls where the first fix
  inlined them; that cost is not measured against the performance ledger.
- An invoke with a by-reference argument costs one extra jump into its own
  block. An invoke whose block holds another call for any other reason (for
  example an aggregate `Load` feeding a non-by-reference use) is still
  refused by the one-call rule.
- The zero-length `Memmove` of the older aggregate-field store remains (a
  `memmove` call of length 0).
- x86-64 is unchanged (read in the first run: System V MEMORY-class
  arguments are copied to the outgoing area, Windows x64 by-reference
  arguments to a fresh slot).

## Repair: anonymous parameters over 256 bytes, and Darwin variadic invokes

A further independent verifier (about 1,000 adversarial checks at O0-O3, no
wrong code) found one fail-closed regression of `899336f46` and one
pre-existing Darwin defect. `afd970b8b` fixes both and `02318c8bf` updates
the documentation. The repair run (`records/repair/`, harness
`records/repair/harnesses/repair.py`) used clean source
`02318c8bf66020ab2e22eb82701c5e78d5c71181` (tree
`6246cf64597a2d444c6ff0d2a5f1392d6aa4cb54`), with an empty `git status`
before, after and after its negative control
(`records/repair/source.json`, `records/repair/negative-control/identity.json`).

### What was wrong

- `pass_composites_by_reference` read each argument's type from the
  adapter's LIR value types. A function or block parameter has no entry
  there, and only a FIXED argument is retyped to its parameter type
  (`record_aggregate_call_arg_types`), so a parameter over 256 bytes
  forwarded as an ANONYMOUS variadic argument skipped the adapter's copy and
  reached the 256-byte selection copy, which refused it:
  `[TCG-BYREF-COPY] argument 1 is a 1024-byte composite passed by reference`
  (`records/repair/reproducer/var3.trust_ir`, an entry parameter;
  `v3b.trust_ir`, a block parameter). The unbounded inline copy of
  `cc42cb5f8` had compiled both. At exactly 256 bytes they compiled.
- `Opcode::Invoke` carries no fixed-argument count, so selection places an
  invoked variadic callee's anonymous arguments by the named rules. That is
  right for base AAPCS64, but DarwinPCS puts anonymous arguments on the
  stack, so a Darwin invoke of a variadic callee passed them in x1/x2
  (`records/repair/reproducer/dinv.trust_ir`; the verifier read this from
  Darwin disassembly, it is not executable here). The new invoke path also
  passed no fixed count to the by-reference conversion, so a Darwin
  anonymous aggregate over 16 bytes became a pointer instead of reaching the
  `[TCG-VARARG-ABI]` refusal.

### The repair

- An argument with no LIR value type is typed from its trust-ir value (the
  translation its block parameter got), so the adapter copies it like any
  other by-reference argument.
- The invoke path passes the callee's fixed-parameter count, and a Darwin
  invoke of a variadic callee is refused by name: `[TCG-VARARG-ABI] invoke
  of variadic callee ...`. Linux variadic invokes are lowered.

### Results on the repair source

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_large_aggregate_args_linux -- --show-output --test-threads=1` (objects retained) | `test result: ok. 9 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 9.65s` |
| `cargo test -p trust-cg-lower --lib` | `test result: ok. 1889 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 3.26s` |
| `cargo test -p trust-cg-codegen --lib` | `test result: ok. 4113 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 4.44s` |
| `cargo check -p trust-cg-codegen --features verify` | exit 0 |
| `bash scripts/check_fmt.sh` | `check_fmt: OK — every workspace file matches rustfmt` |
| `python3 scripts/check_documentation.py --write`, then `--check` | no change; current |
| `python3 scripts/generate_diagnostics_inventory.py --check` | current |
| `python3 scripts/native_test_host_matrix.py --check` | exit 0 |
| `python3 scripts/check_evidence_archive.py --plan` | exit 0 |
| the three gate script tests | `Ran 94 tests`, `OK (skipped=1)` |

ABI and EH targets (`records/repair/commands/lower-abi-targets.log.gz`,
`codegen-abi-eh-targets.log.gz`), every one `0 failed`: trust-cg-lower
`aarch64_adapter_target_abi` 4, `aarch64_aggregate_stack_abi` 4,
`aarch64_hva_abi` 4, `aarch64_variadic_abi` 3; trust-cg-codegen
`aggregate_call_results` 1, `e2e_aarch64_aggregate_insert_linux` 10,
`e2e_aarch64_aggregate_stack_linux` 1, `e2e_aarch64_call_arg_ptr_theft` 2,
`e2e_aarch64_calling_conv` 2, `e2e_aarch64_darwin_variadic_wide` 0 (its
rows are macOS-only), `e2e_aarch64_direct_enums_linux` 6,
`e2e_aarch64_eh_invoke_trust_ir` 5, `e2e_aarch64_eh_o2_and_walkthrough_trust_ir`
6, `e2e_aarch64_eh_resume_trust_ir` 5, `e2e_aarch64_f16_scalar` 4,
`e2e_aarch64_hfa_zero_sized_linux` 4, `e2e_aarch64_hva_linux` 2,
`e2e_aarch64_niche_enum_linux` 4, `e2e_aarch64_sret_linux` 8,
`e2e_aarch64_struct_byval` 1, `e2e_aarch64_tail_call_abi` 6,
`e2e_aarch64_variadic_call` 1, `e2e_aarch64_variadic_linux` 1 and
`multi_result_call_abi` 1. All 152 Linux floor targets through cargo in
three chunks: 152 `test result:` lines, 929 passed, 0 failed.

The target's new rows: 1,024-byte function and block parameters forwarded
as fixed arguments (`k_param_pass`, `k_block_pass`) and as anonymous
arguments (`var_param_k`, `var_block_k`), and a 264-byte anonymous
parameter (`var_param_m2`), against C callees that write them (shape
`param_big`, 36 checks per level, so the C oracle now makes 1,125 checks);
a variadic-invoke corpus (`invoke_variadic.trust_ir`: a parameter and a
1,024-byte block parameter as anonymous arguments to C++ callees that write
them through `va_arg` pointers and throw on odd input, 20 checks per level);
the Darwin refusal of that corpus at O0-O3; and the adapter's copies for the
fixed-position parameters (`k_param_pass` [1024], `k_block_pass` [1024, 1024]:
the block parameter's edge copy, then the argument copy). The CLI objects
equal the test's at every level (`records/repair/objects/{api,cli}`):

| Corpus | Level | SHA-256 (decoded, first 16) | Bytes |
| --- | --- | --- | ---: |
| corpus | O0 | `6f4743813d285a2c` | 8,544 |
| corpus | O1 | `9ee3742a9cce4fb7` | 8,352 |
| corpus | O2 | `25855c56eba2276e` | 8,504 |
| corpus | O3 | `df1aba0216a991c9` | 8,504 |
| variadic | O0 | `1dd3355b4311e73a` | 2,576 |
| variadic | O1 | `84488688d1e15396` | 2,560 |
| variadic | O2-O3 | `c6c67c39a60860ef` | 2,648 |
| invoke_variadic | O0 | `f6e8fe32ba70da22` | 2,520 |
| invoke_variadic | O1 | `f7cc83d89574d809` | 2,512 |
| invoke_variadic | O2-O3 | `c4b9c0f765035ddb` | 2,520 |

The tail and invoke objects are unchanged from the qualifying run above.
The reproducers (`records/repair/commands/reproducers.log.gz`): `var3` and
`v3b` compile at O0-O3 on Linux, `dinv` compiles at O0-O3 on Linux and is
refused at O0-O3 on Darwin.

### Negative control

`adapter.rs` from `e5286b9bf` (before the repair), every test and fixture at
HEAD (`records/repair/negative-control/adapter.diff`): the target failed
`test result: FAILED. 6 passed; 3 failed` (the compile row, the C-oracle row
and the variadic-invoke row), the CLI could not compile the variadic and
variadic-invoke corpora at any level (`[TCG-BYREF-COPY]`), `var3` and `v3b`
were refused at O0-O3, and `dinv` compiled for Darwin at O0-O3 (the silent
register placement). The invoke corpus, which has no variadic callee, passed
34 of 34 checks as before.

### Recorded, not fixed

Compile time grows faster than linearly with the number of calls in one
block at O1-O3: the verifier measured 14.2 s and 495 MB at O2 for 1,000
scalar calls in one block, and 18.2 s for 500 calls each copying a 40-byte
argument. This predates the by-reference copies (each adds one `memcpy`
call); LIMITATIONS.md records it.

## Reproduce

From a checkout of `bf991f8dd` with the host prerequisites above:

```sh
cargo test --locked --offline -p trust-cg-codegen --test e2e_aarch64_large_aggregate_args_linux
cargo test --locked --offline -p trust-cg-codegen --test e2e_aarch64_hfa_zero_sized_linux
cargo build --locked --offline -p trust-cg-cli
bash reports/perf/2026-09-23-linux-large-aggregate-args-2/records/harnesses/compile_cost.sh OUT target/debug/trust-cg 90
bash reports/perf/2026-09-23-linux-large-aggregate-args-2/records/harnesses/run_fixture.sh OUT2 target/debug/trust-cg
```

The harnesses name the absolute paths of the qualifying run; edit them for
another checkout. `compile_cost.sh` reads the verifier's reproducers, which
are retained under `records/reproducer/`.
