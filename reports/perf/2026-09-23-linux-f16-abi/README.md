# `f16` scalar and `f16` HFA calling convention on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the ledger L01-P7 increment: the Linux floor target
`e2e_aarch64_f16_abi_linux`. It also re-checks the four existing `f16`
native targets and records two findings. The run used clean source
`2ac464924e6b9fc7d651bee4a0a6370e61fc74b4` (tree
`6103446fcd41d44c6fe363cdf418fa0e3162336e`, trust-ir pin `7b9146ba`).
`git status --porcelain --untracked-files=all` was empty before and after
(`records/source.json`). `harnesses/qualify-f16-abi-20260923.py`, stored
verbatim, ran every command and staged this directory.
`harnesses/make-inventory-20260923.py` wrote `inventory.json` afterwards.

## Host

The host is Linux `6.17.0-1026-nvidia` on NVIDIA Grace (aarch64), with glibc
2.39. `AT_HWCAP` is `0xefffffff`, with `fphp` and `asimdhp` set
(`records/host.json`). The tools are Ubuntu gcc 13.3.0 as `cc`, GNU ld 2.42,
LLVM 18.1.3 `llvm-objdump`, and rustc/cargo 1.97.1 through the rustup
proxies; `records/tools.json` has each path, SHA-256 and version. Cargo ran
with `--locked --offline -j 8`, with PATH led by the pinned AY/Clean package
directory and ambient `TCG_*`/`TRUST_CG_*` variables removed.

## Results

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_f16_abi_linux -- --show-output --test-threads=1` with `TCG_F16_ABI_RETAIN` set | `test result: ok. 9 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 11.29s` |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_f16_scalar -- --show-output --test-threads=1` | `test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.29s` |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_f16_fcvt -- --show-output --test-threads=1` | `test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 60.81s` (1,482,652 CG-vs-hardware comparisons) |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_f16_to_i128 -- --show-output --test-threads=1` | `test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.12s` |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_i128_to_f16 -- --show-output --test-threads=1` | `test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.13s` |

Each command has a `records/commands/<name>.capture.json` with its argv,
working directory, relevant environment, UTC start and end times, return
code and log hash. `records/results.json` collects the summaries.

### `e2e_aarch64_f16_abi_linux`, per lane and level

The corpus has 29 shapes, each run in both directions: C calls
`cg_<shape>`, and `cg_call_<shape>` calls the C callee `c_<shape>`. The
driver runs 24 value rounds: one of distinct ordinary values, then one per
binary16 pattern in rotation. The patterns are ±0, ± smallest and largest
subnormal, the smallest normal, ±1, ±max, ±inf, the default qNaN, quiet and
signalling NaNs with payloads of either sign, and ordinary values.

| Object | SHA-256 (decoded) | Bytes | Driver |
| --- | --- | ---: | --- |
| `baseline-O0` | `a967fc9b64c67846…` | 22,984 | `f16-abi shapes=29 calls=1392 slot_checks=12576` |
| `baseline-O1` | `219bf81686ad55ec…` | 20,464 | same |
| `baseline-O2` | `eab07b3e9fcbbd7d…` | 17,992 | same |
| `baseline-O3` | `6f760b687089682d…` | 17,984 | same |
| `explicit-fp16-O0`..`O3` | byte-identical to the baseline object at the same level | | same |

The explicit-fp16 profile produces byte-identical objects, because the
transport corpus needs no FEAT_FP16 instruction. The run executes 11,136
calls and 100,608 slot checks in total, but only 5,568 calls and 50,304
checks run on distinct code. The second lane is admission evidence: the
same corpus compiles and links with the profile recorded. The objects are
`records/objects/corpus/*.o.gz`, and the C driver is
`records/objects/corpus/driver.c` (SHA-256 `c52661632cc763b6…`).

The other rows, from `records/commands/f16_abi_linux.log`:

- **Placement.** `placement: 464 functions (29 shapes x 2 directions x 4 opt
  levels x 2 lanes) match AAPCS64; 256 wrong-model checks rejected`. The
  `trust-cg-lift` decode agrees with the test's AAPCS64 model: each register
  argument is consumed or produced through its H (S/D) register, each stack
  `f16` is stored and loaded by an H transfer at its 8-byte slot, no access
  strays outside the argument slots, and results use H0.. . Both wrong
  models are rejected in both directions wherever they differ from AAPCS64:
  a DarwinPCS-style packed stack (13 shapes) and no NSRN clamp (3 shapes).
  The model also agrees with the lowering classifier on all 29 shapes, and
  single-word stack-transfer mutations are rejected with the moved offset
  named.
- **FEAT_FP16 scan.** `fp16 classifier: 20174 corpus words, none
  FEAT_FP16`. The classifier is a mask test from the Arm encoding tables,
  with 15 FP16 and 13 base-FP control words. The explicit-profile `FADD H`
  object is flagged.
- **Refusal.** `f16` addition over the boundary is refused by name without
  the profile ("FEAT_FP16 is not admitted for FADD H"), including under an
  explicit baseline profile, at O0–O3.
- **Controls.** `controls: 2 mutated objects and 29 mismatched prototypes
  detected`. Retargeting argument 9's stack load in `cg_h12`, or its store
  in `cg_call_h12`, fails the oracle in that direction
  (`records/objects/controls/mutated_*.o.gz`). Building the driver with
  `-DMISMATCH_<shape>` for every shape spells each shape's last `f16`
  argument `float`, and every shape fails.
- **Explicit-profile arithmetic.** `fp16 FADD H over the ABI: 529 pairs x
  O0-O3 bit-exact vs hardware`. `cg_fadd` returns `h1 + h9`, with argument
  9 on the stack, and equals inline-assembly `FADD H` with the same operand
  order on every ordered pattern pair. It also equals the float-promoted C
  sum, NaN-aware (`records/objects/fp16_fadd/`). The test first requires
  `AT_HWCAP` fphp/asimdhp to agree with the runtime detection.

The 15 linked executables are not archived. `results.json`
(`binaries_not_archived`) records each one's SHA-256 and size.

## Findings recorded, not repaired

**DarwinPCS stack packing of HFAs.** `records/darwinpcs-hfa-probe/probe.rs`
is a `no_core` crate. Stock rustc 1.97.1 compiled it with
`RUSTC_BOOTSTRAP=1 --emit=asm -C opt-level=2` for both triples. Like clang,
rustc lowers a stack HFA to `[N x half]`/`[N x float]`. The LLVM placements
of the stack arguments, after eight FP register arguments, are:

| Call | aarch64-apple-darwin | aarch64-unknown-linux-gnu |
| --- | --- | --- |
| `f16` HFA3, then `f16` | members at `sp+0, 2, 4`, `f16` at `sp+6` | members at `sp+0, 2, 4`, `f16` at `sp+8` |
| `f16` HFA1, HFA1, then `f16` | `sp+0`, `sp+2`, `sp+4` | `sp+0`, `sp+8`, `sp+16` |
| `f32` HFA3, then `f32` | members at `sp+0, 4, 8`, `f32` at `sp+12` | members at `sp+0, 4, 8`, `f32` at `sp+16` |

trust-cg's AAPCS64 placement matches the Linux column; this target checks
that. The Darwin classifier rounds every stack HFA to 8 bytes, so it
disagrees with the Darwin column. This is a probe of LLVM's placement, not
a trust-cg Darwin execution. The Darwin half of L01-P7 is open.

**`InsertField` shares storage with its source.**
`records/insertfield-shared-storage/swap_{i64,f32,f16}.trust_ir` define
`swap(s) = insert(insert(s, 0, s.1), 1, s.0)` over a by-value `repr(C)`
pair. The repository CLI (`trust-cg --format=text -c -O0|-O2 --target
aarch64-unknown-linux-gnu`) compiled each one, `cc` linked it against
`swap.c`, and every case printed `swap({1,2}) = {2,2} (expected {2,1})`
and exited 1: six cases of three types at two levels. The adapter lowers
`InsertField` by storing into the source's storage, so the second extract
reads the inserted value. The corpus's permuted HFA return extracts every
member before its first insert.

## Evidence boundary

This is native execution against GCC 13's `_Float16` ABI and decoded object
placement on one Linux host, at O0–O3. It is not a proof. It does not cover
variadic `f16`, `f16` vectors, DarwinPCS execution, or the classifier's
behaviour beyond these 29 shapes. The FP16 classifier covers scalar FP
data-processing, conversion and 3-source forms and the Advanced SIMD
three-same and two-register-misc FP16 groups, but not the by-element or
across-lanes FP16 forms. Ledger L01-P7 stays PARTIAL.

## Reproduce

From a checkout of `2ac464924`, with the host prerequisites above:

```sh
python3 -B reports/perf/2026-09-23-linux-f16-abi/harnesses/qualify-f16-abi-20260923.py \
  "$PWD" /tmp/f16-abi-out <dir holding darwinpcs/probe.rs and insertprobe/{swap.c,swap_*.trust_ir}>
```

The probe and reproducer inputs are the copies under `records/`.
