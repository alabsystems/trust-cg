# Linux x86-64 `PassMode::Pair` arguments (XD-05) — 2026-09-21

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The two-carrier `PassMode::Pair` ARGUMENT lane of the bridge, landed on the
x86-64 census baseline of the same day
([2026-09-21 HEAD census](../2026-09-21-linux-x86-64-head/census/core-x86_64-linux-O0-v45/gap_table.md),
335 failed roots, `[TCG-ARG-ABI]` 74). This directory records the two census
runs the change was gated on and the cross-backend test that measures it.
Nothing here is a proof: the bridge runs in the explicit unverified frontend
lane (`-Ztrust-verify=off`) and the cross-backend results are per-shape
differential tests on a named corpus.

## Host and toolchains

| Item | Identity |
| --- | --- |
| Host | `x86_64-unknown-linux-gnu`, Linux 7.0.0-31-generic, 24 cores, 61 GiB |
| Trust compiler | tree-built stage2 `trustc 1.99.0-dev (3a3e781fe 2026-09-14)` at `$HOME/trust/build/x86_64-unknown-linux-gnu/stage2` |
| Census source | `$HOME/trust/library/core/src/lib.rs`, O0, `panic=abort`, `--emit=obj`, codegen-units=1 (`provenance.json` in each census directory) |
| trust-cg base | `23e081da0` (the HEAD census above); branch `wave1/pair-args` |

## Census results

| Run | Backend state | Failed roots | `[TCG-ARG-ABI]` | Directory |
| --- | --- | ---: | ---: | --- |
| HEAD baseline | `23e081da0` | 335 / 28 reasons | 74 | `../2026-09-21-linux-x86-64-head/census/core-x86_64-linux-O0-v45/` |
| Step 0 | every hand-built argument list routed through `lower_call_arg_for_input`; declaration UNCHANGED | 335 / 28 reasons, byte-identical symbol set and per-symbol reason | 74 | `census/core-x86_64-linux-O0-step0/` |
| Lane | two-carrier declaration (`scalar_pair_param_plan`), sender/receiver halves, x86-64 gate arm | **270** / 28 reasons | **2** | `census/core-x86_64-linux-O0-pair-args/` |

Diff of the lane run against the HEAD baseline, keyed on the census reason
column (not message text — every `[TCG-ARG-ABI]` message quotes the phrase
"arity mismatch"): 65 roots now compile; 7 roots keep failing under a
different, pre-existing reason (their next refusal: 2 fat-pointer union
fields, 2 `ControlFlow` `from_residual`, 3 `[TCG-REGALLOC-063]` `Array(I8, 5|6)`
partial-eightbyte returns); 0 roots are new; no reason class is new. The two
remaining `[TCG-ARG-ABI]` roots take `Option<u128>` by value: rustc's pair
puts each 128-bit scalar in two registers, `scalar_pair_lane_ty` declines a
128-bit lane, and the one-value tuple would pass it `byval` — refused, as for
returns.

## What was measured, and how it is bounded

* The x86-64 placement gate (`abi_reg_lanes::trust_cg_param_placement`) now
  states the System V placement of a multi-value scalar argument from the
  selector's own per-value rule (independent GPR and XMM sequences, per-value
  stack spill) and compares class, count, extent and offset against rustc's
  `FnAbi` for every declaration; it does not compare register numbering.
* The cross-backend test `m142_x86_scalar_pair_arg_xback` (the argument twin
  of m140) compiles a callee rlib and a caller bin in the four backend
  combinations at O0–O3 and requires the oracle's exit code from every
  combination, with a fail-closed refusal counted as a failure. Shapes:
  `Option<u8/u16/u32/i32>`, `(u8,u8)`, `(u16,u16)`, `(u32,u32)`, `(i16,i16)`,
  `(u8,bool)`, `(i8,i8)`, `(u64,u64)`, `(f64,f64)`, `(u64,f64)`, `(f32,u64)`,
  `Result<u8,u8>`, `ControlFlow<u8,u8>`, `Range<u8>`; the pair after six
  integer arguments and after eight float arguments (register exhaustion,
  per-lane stack spill); a `fn`-pointer callee defined in the other crate
  (the indirect lane across the boundary); `Fn` and `FnOnce` closure bodies
  taking the pair (whole-program; the no-env `FnOnce` body exercises the
  dropped-environment index mapping); a caller-side
  `.enumerate().map(|(i, &x)| ..)` chain (the intercepted closure call whose
  `(usize, &T)` item is a pair, whole-program); and `&[T]` / `&str`
  arguments, which must keep passing as one value. The run logs are
  `m142-run1.log` (the first run, whose only failure was the O1 rlib refusal
  below, with `sum_enumerate` and `slice_arg` still calling `.iter()` in the
  rlib) and `m142-run2.log` (the recorded run, on the committed dylib); m140
  was re-run on the same dylib (`m140-rerun.log`), and the whole-program
  differentials `m99_iter_adapters_x86`, `iter_adapters_x86` and
  `closures_x86`, which execute the routed intercept and closure-call paths,
  were run on it as well (`differentials/`).

## Found on the way, not repaired here

`core::slice::iter::Iter<T>::new`, emitted as a standalone monomorphization
in a `no_std` rlib at O1, fails the backend's x86-64 regalloc value-flow
validation — `[TCG-REGALLOC-063] ... x86-64 regalloc failed:
ValidationFailed("... value-flow: use of v48 at BlockId(6)/InstId(39) reads
<unknown>, which holds Some(44), not v48")` — with the HEAD backend
(`23e081da0`) exactly as with this one; O0, O2 and O3 pass, and a bin inlines
the item away (m140's `slice_ref` caller at O1). Reproducer:
`#![no_std] pub fn f(xs: &[u32]) -> u64 { xs.iter().map(|&x| x as u64).sum() }`
compiled as an rlib at `-Copt-level=1`. It is unrelated to argument passing
and is left as a named open item.
* AArch64 emits the same two-carrier declaration with carriers equal to the
  lane types (no widening, no masking) and is checked by the same gate against
  `AppleAArch64ABI::classify_params`, but this host has no AArch64 LLVM peer:
  the AArch64 argument lane has no cross-backend measurement.

## Reproduce

```sh
cd crates/rustc-codegen-trust-cg
export PATH="$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin:/usr/bin:$PATH"
RUSTC=$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin/trustc targo --unverified build --release --locked
RUSTC=$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin/trustc targo --unverified test --release --locked --lib abi_reg_lanes
RUSTC=$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin/trustc targo --unverified test --release --locked --test m142_x86_scalar_pair_arg_xback
cd $HOME/trust
python3 scripts/trust_ir_cg_census.py --trustc build/x86_64-unknown-linux-gnu/stage2/bin/trustc --crate core \
  --backend <trust-cg>/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so \
  --out-dir <dir> --opt-level 0 --panic abort
```
