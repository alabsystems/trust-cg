# Darwin arm64 runtime per program vs LLVM `-O3`: `main` 1.022x -> 0.918x cycles; 12 programs faster in both runs, 5 at parity, `p6` 1.015x; emitted size 1.020x, below `main`'s 1.023x (L14-P8, L14-P10)

Host: Apple M4 Max (`Mac16,5`, 12 performance and 4 efficiency cores), macOS 26.6.2
(`25G83`), the shared development machine. Driver: Trust package 9192 (`trustc`
`321aaeda7`, LLVM 22.1.2, explicit unverified frontend lane `-Ztrust-verify=off`).
Every bridge compile here uses `-Ztrust-ir-cg-args=no-proof-certs`, the diagnostic
lane: the production lane still compiles none of the corpus on this host (`p3_gcd`
and `p1_xorshift` with this branch's backend: `[TCG-MIR-UNSUPPORTED]` from nine
`[TCG-PROOF-465]` refusals each, `std::rt::lang_start`'s uncovered opcode inventory;
ledger `L07-P2`). Nothing here is evidence in the ledger's sense and no ledger row
was appended. Every number is a measurement on one host, not a proof.

The work began on 2026-10-01 against `main` `b422f87fd`, was re-measured on
2026-10-06 against `main` `530a9319a` and twice on 2026-10-07 (runs 1 and 2, after
merging `origin/main` `31ad5cd29` and `f0350c84e`). Review round 2 (2026-10-07) added
three size offsets (section 2, item 7) and merged `origin/main` `a7ce025ee` (L10-P3's
per-pass validation); sections 1 and 5 hold its measurements (runs 3 and 4) and
section 7 keeps the earlier ones where they differ.

Backends, all built with `scripts/trust_cargo.sh build --release --locked`
(`targo --unverified`, no proof claim) in `crates/rustc-codegen-trust-cg`:

| lane | source | backend sha256 |
|---|---|---|
| `base` | `main` `31ad5cd29` | `34956867e164206b…` |
| `final` | this branch at `6885641f0` (after merging `31ad5cd29`) | `0e4ac272f76b14ce…` |
| `base` | `main` `f0350c84e` | `ef966bd80aebd5f8…` |
| `final` | this branch at `ccda0fe59` (after merging `f0350c84e`; later commits change only tests, scripts and this record) | `1c47c3542ba8e0ae…` |
| `base` (runs 3, 4) | `main` `a7ce025ee` | `9c6620608183ec2b…` |
| `prev` (runs 3, 4) | this branch at `9c2f3740a`, round 1's final head (its per-function corpus bytes and instruction classes equal `ccda0fe59`'s) | `55ca13d6e4637f15…` |
| `final` (runs 3, 4) | this branch at `b1e777af5` (the size offsets, then the merge of `a7ce025ee`; later commits change only this record) | `6ec38fc5fda53d0d…` |

The corpus binaries of the two `base` backends, and of the two `final` backends,
have identical `__TEXT,__text`, `__TEXT,__const`, `__TEXT,__cstring`,
`__TEXT,__unwind_info`, `__TEXT,__eh_frame`, `__DATA_CONST,__const` and
`__DATA,__data` (all 36, compared with `otool -s`); they differ only in their
symbol tables (L06-P7's Mach-O linkage). Runs 1 and 2 below therefore measure the
same code. In round 2, `main` `a7ce025ee` emits the same per-program byte counts as
`f0350c84e` (section 5), and the final backend emits all 18 programs with the same
sections as the pre-merge head `cfbb67d31`: the merge of `a7ce025ee` changed no
corpus byte.

**The metric** is **cycles elapsed** of the process (from `/usr/bin/time -l`), the
minimum and the median of interleaved rounds in which every lane runs once per round
in a rotated order (`commands/bench.py`), with instructions retired beside it. Wall
time is listed only with its load range. Two binaries with the same instructions
retired read 0.996-1.004 cycles against each other run to run, so a ratio within
about ±0.5% of 1.000 is parity, not a result. Run 1: 11 rounds, 1-minute load
7.6-8.6, `main` `31ad5cd29` and `6885641f0`. Run 2: 21 rounds, load 5.0-7.2,
`main` `f0350c84e` and `ccda0fe59`. Runs 3 and 4: 21 rounds each, load 5.3-14.8 and
5.8-16.6, four lanes (LLVM `-O3`, `main` `a7ce025ee`, `prev` and `final`).

## Summary

| | base (`main`) | final (this branch) |
|---|---:|---:|
| runtime cycles, geomean x LLVM `-O3`, min / median, run 4 (21 rounds) | 1.022 / 1.013 | **0.918 / 0.919** |
| the same, run 3 (21 rounds) | 1.024 / 1.026 | 0.917 / 0.919 |
| instructions retired, geomean x LLVM `-O3` | 1.175 | 1.086 |
| programs faster than LLVM `-O3` beyond the ±0.5% band on both statistics in both runs (`commands/tables.py classes`) | 6 of 18 | **12 of 18** (`prev`, round 1's head: 10 in the same runs) |
| programs at parity (within the band, or mixed) | 6 | 5: `h3`, `p2`, `p3`, `p4`, `p8` |
| programs slower than LLVM `-O3` beyond the band | 6 | **1: `p6_branch_match`** (1.015-1.020 minimum) |
| programs slower than base | | none beyond the band; `p4_matmul` reads +0.4-0.5% at its edge (section 1) |
| emitted-code size, geomean x LLVM `-O3` | 1.0233 (13,895 B) | **1.0201 (13,839 B)**: below `main`, still above the 1.0x bound (section 5) |
| compiler instructions retired, final / base, geomean (median of 3) | | 0.9999 (final / `prev` 1.0000) |
| compiler peak RSS, final / base, geomean | | 0.9993 |
| exit codes equal to LLVM `-O3`'s and the manifest's | 18 / 18 | 18 / 18 |

## 1. Per-program runtime (`commands/tables.py runtime`, run 4)

Cycles, instructions retired and wall-time minimum as ratios to LLVM `-O3`, 21
interleaved rounds, 1-minute load range of the rounds. `**` marks a final row at or
above 1.000 on either cycle statistic.

| program | base cycles min / med | final cycles min / med | base instr | final instr | final wall min | load |
|---|---:|---:|---:|---:|---:|---|
| b1_mispredict | 1.014 / 1.014 | 0.973 / 0.972 | 1.062 | 1.185 | 0.975 | 7.0-7.4 |
| h1_vec_push_sum | 2.865 / 2.354 | 0.993 / 0.991 | 5.055 | 1.101 | 0.972 | 7.2-7.2 |
| h2_vec_grow | 1.246 / 1.232 | 0.910 / 0.902 | 1.304 | 0.962 | 0.928 | 7.2-7.3 |
| h3_box_leak | 1.184 / 1.196 | 0.982 / 0.996 | 1.223 | 0.959 | 0.997 | 7.3-7.3 |
| h4_vec_dropper | 0.920 / 0.939 | 0.854 / 0.862 | 1.068 | 0.976 | 0.877 | 7.3-7.3 |
| m1_call_chain | 0.931 / 0.931 | 0.931 / 0.932 | 1.087 | 1.087 | 0.946 | 7.1-7.3 |
| m2_call_heavy | 0.972 / 0.973 | 0.912 / 0.918 | 0.539 | 0.654 | 0.916 | 7.1-7.6 |
| p1_xorshift | 1.008 / 1.007 | 0.961 / 0.963 | 1.551 | 1.992 | 0.962 | 6.8-7.7 |
| p2_collatz | 0.998 / 0.998 | 0.998 / 0.999 | 1.139 | 1.139 | 0.999 | 6.4-7.2 |
| p3_gcd ** | 1.001 / 1.001 | 1.000 / 1.000 | 1.189 | 1.189 | 1.000 | 5.9-7.1 |
| p4_matmul ** | 0.995 / 0.996 | 1.000 / 1.001 | 1.076 | 1.076 | 1.002 | 7.1-7.1 |
| p5_struct_acc | 1.000 / 1.000 | 0.889 / 0.889 | 1.000 | 1.099 | 0.890 | 5.8-7.2 |
| p6_branch_match ** | 1.021 / 1.028 | 1.015 / 1.019 | 1.116 | 1.218 | 1.012 | 5.8-16.6 |
| p7_sieve | 0.790 / 0.798 | 0.781 / 0.761 | 0.977 | 0.976 | 0.793 | 15.5-15.5 |
| p8_closure_nest | 0.999 / 0.999 | 0.999 / 0.999 | 1.197 | 1.197 | 1.000 | 13.8-15.5 |
| v1_saxpy | 0.734 / 0.736 | 0.734 / 0.738 | 1.653 | 1.653 | 0.759 | 13.1-13.8 |
| v2_memfill | 0.992 / 1.003 | 0.990 / 0.991 | 1.139 | 1.139 | 0.999 | 13.1-13.1 |
| v3_popcount | 0.705 / 0.696 | 0.696 / 0.702 | 0.618 | 0.618 | 0.773 | 13.1-13.1 |
| **geomean** | 1.0220 / 1.0130 | 0.9179 / 0.9187 | 1.1755 | 1.0860 | 0.9295 | |

Classification over runs 3 and 4 (`commands/tables.py classes llvm_o3 final <run 3>
<run 4>`; "faster" means all four cycle ratios below 0.995):

| program | run 3 min / med | run 4 min / med | class |
|---|---:|---:|---|
| b1_mispredict | 0.972 / 0.971 | 0.973 / 0.972 | faster |
| h1_vec_push_sum | 0.989 / 0.987 | 0.993 / 0.991 | faster |
| h2_vec_grow | 0.896 / 0.910 | 0.910 / 0.902 | faster |
| h3_box_leak | 0.975 / 0.992 | 0.982 / 0.996 | parity or mixed |
| h4_vec_dropper | 0.847 / 0.854 | 0.854 / 0.862 | faster |
| m1_call_chain | 0.931 / 0.931 | 0.931 / 0.932 | faster |
| m2_call_heavy | 0.913 / 0.917 | 0.912 / 0.918 | faster |
| p1_xorshift | 0.962 / 0.965 | 0.961 / 0.963 | faster |
| p2_collatz | 0.999 / 0.999 | 0.998 / 0.999 | parity or mixed |
| p3_gcd | 1.000 / 1.001 | 1.000 / 1.000 | parity or mixed |
| p4_matmul | 0.998 / 1.001 | 1.000 / 1.001 | parity or mixed |
| p5_struct_acc | 0.889 / 0.889 | 0.889 / 0.889 | faster |
| p6_branch_match | 1.020 / 1.024 | 1.015 / 1.019 | slower |
| p7_sieve | 0.781 / 0.778 | 0.781 / 0.761 | faster |
| p8_closure_nest | 0.999 / 0.999 | 0.999 / 0.999 | parity or mixed |
| v1_saxpy | 0.736 / 0.737 | 0.734 / 0.738 | faster |
| v2_memfill | 0.990 / 0.987 | 0.990 / 0.991 | faster |
| v3_popcount | 0.697 / 0.697 | 0.696 / 0.702 | faster |
| **count** |  |  | faster 12, parity or mixed 5, slower 1 |

**Round 2 against round 1's head** (`prev`, the same runs; final / `prev` cycles):
the geomean is 0.9991 / 0.9979 (run 3) and 0.9984 / 0.9978 (run 4), instructions
retired 0.9997-1.0001 per program. 15 of the 18 programs change only in `done`, which
is laid out before `main`, so their hot loops move 4 bytes. Beyond the ±0.5% band:
* `b1_mispredict` 0.990 / 0.990 and `p7_sieve` 0.971-0.989 faster in both runs, and
  `h4_vec_dropper` mixed (run 3 0.993 / 0.999, run 4 1.015 / 1.004; a 41-round rerun
  1.014 / 0.999): placement, not code. With `main` linked at the same address in both
  (`-Wl,-order_file`; `main` byte-identical) `h4` reads 0.832 / 0.844 for `prev` and
  0.828 / 0.848 for final (41 rounds).
* `p6_branch_match` 1.010 / 1.006 (run 3) and 1.002 / 1.000 (run 4); 41-round reruns
  1.011 / 1.022 for `prev` against 1.011 / 1.028 for final, and 1.0135 / 1.0207
  against 1.0125 / 1.0253 (31 rounds). With `main` at the same address it reads
  1.025 / 1.038 against 1.023 / 1.037: parity, and the layout alone moves `p6` by
  about 1.5% (it reads 1.011 at its default address and 1.024 at `0x888`).
* `p4_matmul` 1.003 / 1.003 and 1.006 / 1.005, and 1.005 / 1.003 in a 41-round
  rerun (+0.3-0.6%, and +0.4-0.5% against `main`): the one program that reads worse
  in every run, at the band's edge. Not attributed: its matmul loops are byte-identical
  and, with `done` (56 bytes) linked before `main` in the final build only, at
  identical addresses, where it still reads 1.000 against 0.996 (41 rounds);
  instructions retired are equal; and a backend without const-chain-dedup (built from
  this head with the pass removed, not committed) reads 1.001 / 1.001 like the final
  one, so the merged constants and the moved spill slots are not the cause. What
  remains different is the 576-iteration initialization loop (two pre-shifted
  `% 100`s) and the image layout around `main`; the program runs 116 M cycles, so
  0.4% is about 0.45 M.

Runs 1 and 2 (`main` `31ad5cd29` / `f0350c84e` against `6885641f0` / `ccda0fe59`,
round 1's code) read 1.0209 / 1.0249 and 0.9161 / 0.9229 (run 2) and 1.022 / 1.024
and 0.919 / 0.921 (run 1), with 11 programs faster in both, 6 at parity (the same 5
and `v2_memfill`), and `p6` slower at 1.011-1.018 (section 7 keeps run 2's table).

Earlier runs at higher load, of round 1's binaries (section 7, and the review of this
branch), agree on every class except two. `h1` read
1.003 / 1.008 at load 105 and 0.985 / 1.002 at load 30-47 (its sum runs at the L2
streaming rate in both compilers, section 3), so it is faster here but at parity
under load. `v2_memfill`, whose hot code is identical between base and final, read
0.983 / 0.865 at load 130 and 1.069 / 1.112 at load 55: a memory-bound fill whose
ratio moves with the load in both directions (faster in runs 3 and 4, parity in runs
1 and 2). `h3_box_leak` read 0.974 / 0.966 and
0.968 / 0.947 in the two 2026-10-06 runs (load 101 and 33), but 0.988-1.001 in five
later ones (two here, three in the review at load 8-55): it is at parity, not
below, and its gain over `main` (1.17-1.19x) is real. The 2026-10-06 title's "15 of 18 below parity" counted
programs inside the noise band; it is withdrawn.

## 2. What the branch changes on top of `main`

`main` restored the vectorizable class meanwhile (`b2bf85bb4`: the AArch64
bounds-check eliminator folds a check against a constant that the loop guard's
constant proves), so `v1`, `v2`, `v3` and `p7` are already below LLVM on `main`;
this branch's own constant-bound arm was the same rule and was dropped in the
merge in favour of `main`'s. What `main` still lacks, and this branch adds:

1. **LICM follows `AddRR slot, k`** (`b74d6ec1c`) when `k` is a single constant: the
   field address GVN forms from `AddRI slot, #8`. Hoists `h1`'s `Vec` pointer load,
   after which `neon-array` vectorizes the sum (`h1` 2.901x -> 0.988x).
2. **SROA follows `AddRR root, k`** (`9fd2572bc`): `h1`-`h4` keep `cap`/`ptr`/`len`
   in registers (`h2` 1.234x -> 0.893x, `h4` 0.928x -> 0.847x; spills in `main`
   5 -> 0 in `h1`, 15 -> 6 in `h4`).
3. **Xorshift step-pair fusion** (`f3f799c4f`, `3c1101ce0`, new pass
   `xorshift-pair-fusion`): `y = t ^ (t >> b)` after `t = x ^ (x << a)` becomes
   `t ^ (ubfm(x) ^ (x >> b))`. On this core an ALU instruction reads its shifted
   operand two cycles after it is produced and its plain operand one
   (`commands/alu_operand_latency.c`: 2.01 / 1.06 cycles, `ubfiz` 1.00), so `y` is
   ready 3 cycles after `x` instead of 4 (`commands/xorshift_chain_latency.c`:
   6.03 -> 5.37-5.57 cycles per update). `p1` 1.008x -> 0.963x, `b1` 1.013x ->
   0.981x, `p6` 1.025x -> 1.012x.
4. **`scalar-unroll` for unsigned top-tested gather loops** (`e7f9c2304`,
   `907766ece`): admits the bridge's copied, `LO` header for 64-bit inductions in
   SPLIT mode, drops test-only copies from the lanes, and reads lane `k` of an
   indexed load at `[base + iv*8, #8k]` from one pointer, which `mem-pair` pairs
   into `ldp` (`h3` 1.172x -> 0.989x with fix 2, from above LLVM to parity; the C model
   `commands/h3_gather_unroll_model.c` puts the unroll at 8-10% of the program).
   A SERIAL unroll of a loadless recurrence through the widened header measured no
   gain (`p1`: 0.958x against 0.963x rolled and fused, for 132 more bytes), so the
   widening is SPLIT-only.
5. **Late `Madd` addend added last** (`3f24fd085`): for a `2^k - 1` / `1 - 2^k`
   constant whose addend is computed in the block, `((a<<5) - a) + y` instead of
   `(y + (a<<5)) - a`; `p5`'s 9-cycle recurrence becomes 8 (1.000x -> 0.889x). No
   other corpus program changes a byte.
6. **OD-109 hardening after the merge** (`75869f1f8`). `main`'s `b4872a26b` made
   W/X views of one numeric register ID alias for redefinition barriers and
   requires ordinary metadata and unique block ownership before an instruction is
   rewritten. The fusion pass now uses numeric-ID clobber barriers, refuses a step
   or copy with non-default flags, implicit operands or a proof annotation, and
   refuses a right step that another block (in or out of the layout) also links,
   all before allocating; `scalar-unroll`'s header copies and the late-addend
   lookup use numeric IDs too. The emitted corpus is unchanged by it.
7. **Size offsets (review round 2).** Every corpus program ends in
   `done(code) = exit((code % 126) as i32)`, which emitted 60 bytes against LLVM's 48,
   and two programs materialize one constant twice:
   * **Even-divisor pre-shift** (`1c318c75a`, `trust-cg-lower`'s constant-divisor
     selector). An even divisor `2^z * k` whose full-width magic needs the add-back
     form is divided as `(x >> z) / k`, whose magic over the reduced dividend range
     fits in the register: `lsr #1; umulh; lsr #5` for 126 (clang's sequence and
     constant) instead of `umulh; sub; add ..., lsr #1; lsr #6`. One instruction and
     one dependent step fewer in all 18 `done`s and in `p4`'s initialization loop
     (`% 100`, twice). `magic_udiv` keeps its single cited premise: the
     Granlund-Montgomery lemma is stated for an N-bit dividend, and the reduced-range
     band check is that lemma with N = W - z; the shift identity is proved inline.
   * **W-form remainder tail** (same commit). A 64-bit remainder whose only use is an
     `i32` truncation writes its last instruction (`msub`, or the `2^k ± 1` add/sub)
     in the W form straight into the truncation's result. In `done` this saves
     nothing: the truncation's `mov w0, w3` becomes the call's argument copy
     `mov w0, w3`, because the register allocator never gives a definition the
     register of an operand that dies at the same instruction (clang's
     `msub w0, w8, w9, w0` needs exactly that) and the post-allocation coalescer keeps
     call-argument copies for the argument repair. Where the result is returned or
     stored the move goes (`(x % 126) as i32` returned: `msub w0, w2, w1, w0`, as
     clang). The offset the review projected at 8 bytes per program is therefore 4.
   * **`const-chain-dedup`** (`40397e0fb`, a new `trust-cg-opt` pass at O2/O3 before
     the scheduler). LICM hoists one `movz`+`movk` chain per materialized constant,
     so a constant a loop body spells twice is materialized twice in its preheader,
     in two registers live through the loop: `p3_gcd`'s LCG multiplier and increment
     (32 bytes) and `p4_matmul`'s `% 100` magic and its spilled `% 576` magic (48
     bytes with the spill stores). The pass keeps the first chain of a value in a
     block when the first register is still read at or after the second chain, so no
     live range grows where the duplicate was not already live.

   Together: 13,999 -> 13,839 bytes, 1.0315x -> 1.0201x LLVM `-O3`, below `main`'s
   13,895 and 1.0233x (section 5). Runtime: unchanged beyond the noise band except
   `p4`'s +0.3-0.6% (section 1).

Evidence for every rewrite: unit tests in `trust-cg-opt` with negative controls,
some also against independent evaluators of the opcodes: the fusion for every
shift pair in `1..=63` squared; the late addend for every multiplier `decompose`
splits with a subtracted term (`2^a - 1` for `a` in `3..=20` and `1 - 2^a` for `a`
in `2..=20`; `3` decomposes as `2 + 1`) at 64 and 32 bits; and the lane-offset
loads on an order-sensitive SERIAL chain (`acc = acc*31 + a[k]`, 16 trip counts)
and on the `h3` gather with its base invariant, copied from an invariant, loaded in
the body, or copied from that load (the last two get no lane pointer). Mutants built
and reverted: for the OD-109 refusals (each new refusal test fails under the typed
predicates or without the ownership/metadata filter), and for the lane offsets (a
lane permutation `[0, 2, 1, 3]` and a disabled loop-invariance guard on the base
each fail the order check and the evaluator differential; before these tests both
passed the whole `trust-cg-opt` suite, and the permutation the native differential
too); the corpus
(18 of 18 programs exit with LLVM's code in every round); and a new native
differential, `crates/rustc-codegen-trust-cg/tests/runtime_parity_rewrites_aarch64.rs`
(section 4).

Evidence for the size offsets: `magic_udiv` unit tests, exhaustive where the width
allows: the reduced-range band agrees with brute force (iff) at w = 8 for every
dividend bound, divisor, multiplier, shift and both forms; every even add-back
divisor at w = 4, 6, 8, 10 and 12 is pre-shifted and exact for every dividend; wrong
pre-shifts, add-back multipliers and multipliers or shifts moved by one are refused
unless still exact (w = 8 and 10); LLVM's constants for 14, 28, 100, 126 and 1000 at
both widths; wide samples at W64 and W32. Isel tests pin both shapes and the negative
controls (odd and no-add-back divisors keep their forms; no seeded use counts, a
second use, a truncation to `i16` or a `2^k + 1` tail with k >= 32 keep the 64-bit
tail and the move). `const-chain-dedup` unit tests cover the `p3` preheader, a
straight-line block evaluated before and after (W-view reads included) and a negative
control for each condition. Native: `trust-cg-fuzz`'s `diff_int_divrem` now also
compares every JIT configuration (O0-O3, both allocators) with the host's own integer
operators over 273 dividends for 12 i64 and 8 i32 constant divisors and 8 truncated
remainders (18,016 configurations, 0 defects); and 154 more rows in
`runtime_parity_rewrites_aarch64` (section 4). Mutants built and reverted: pre-shifting
by z + 1 fails every pre-shifted 64-bit divisor in `diff_int_divrem`; dropping the
k >= 32 exclusion fails to compile `% (2^33 + 1)` there (the W form has no such
shift); a dedup without its def-count and class checks fails two unit tests.

## 3. Where the remaining gap is, for every program not faster beyond noise

Hot loops compared against LLVM `-O3`'s from the same corpus build
(`size_attrib.py --keep-work`), with cycles per iteration from the bench JSON.
Ratios are run 4's minimum / median, with run 2's (round 1's code) where the analysis
below was measured on it; round 2 changed the hot loops of no program (`p3` and `p4`
changed only outside them).

* **`p6_branch_match` (1.015 / 1.019; run 2 1.012 / 1.018): mispredicted
  dispatch.** Its ratio also moves about 1.5% with where `main` is linked (section 1). 33.1 cycles per
  iteration against LLVM's 32.7: the random `s % 7` selector mispredicts most
  iterations in both. trust-cg dispatches the 6 dense cases through a jump table
  (`adr; ldrsw; add; br`), LLVM through a compare tree: on this toolchain LLVM's
  AArch64 backend uses a table only from 10 cases (measured: 9 dense cases emit no
  `br`, 10 emit one).
  * *Tried and refuted:* the same rule in trust-cg's AArch64 ISel (a dense switch
    of fewer than 10 cases becomes its binary-search tree; only `p6` changes a
    byte in the corpus) measured **1.022x** against the table's 1.011x (15
    rounds, load 89-105), so it was not kept. trust-cg's tree tests the pivot for
    equality first and needs up to 5 branches to reach a case; LLVM's splits by
    range into linear leaves. Matching LLVM's tree would at best reach LLVM.
  * *The measured lever:* predicating the dispatch. In the C model
    `commands/p6_predicated_dispatch.c` (clang `-O2`, 7 rounds), computing all
    seven cheap, pure arms and picking the result with `csel` runs in **0.243x**
    the cycles of the branched loop (1.60 G against 6.58 G; both exit 62 as `p6`
    does). With a predictable selector (`i % 7`) the same rewrite costs **1.221x**
    (1.50 G against 1.23 G): it needs a predictability signal (a profile), not a
    static rule, so it is not a change for this branch.
  * The `Rot` arm is 7 instructions against LLVM's `neg; ror`: the backend has no
    variable-rotate opcode (only `RorRI`), and three redundant `and`s of the
    rotate amount survive. One arm in seven, off the mispredict path.
* **`h1_vec_push_sum` (0.993 / 0.991; run 2 0.988 / 0.986, 1.003 / 1.008 at load
  105): L2 bandwidth, the same loop.** Both
  compilers sum the 2.4 MB `Vec` with the same NEON loop (two `ldp q` and four
  `add.2d` per 64 bytes; trust-cg's has one more instruction, `cmp` against
  LLVM's count-down `subs`). Built with 0 and 600 passes
  (`commands/mkvariant.sh`): the push phase is 8.07 M cycles against LLVM's
  8.44 M (trust-cg 4% faster), and a pass costs 89.8 k against 88.7 k cycles,
  about 2.4 cycles per 64 bytes in both, the L2 streaming rate. The loop's shape
  is not a lever: `commands/h1_pass_loop_shapes.c` runs LLVM's loop, trust-cg's,
  a 128-byte unroll and LLVM's with a 1 KiB-ahead prefetch within 0.7% of each
  other at the minimum (33.98 / 33.82 / 33.95 / 34.21 M cycles, 15 rounds,
  load 96).
* **`h3_box_leak` (0.982 / 0.996; run 2 0.989 / 0.993; 0.988-1.001 in five runs,
  0.947-0.974 in two earlier ones): the allocator.**
  Built with 0 and 200 passes (`commands/mkvariant.sh` on the source with
  `bb(20u32)` replaced; 15 rounds, load 4.1): the 1.5 M `Box::new` phase is 43.2 M
  cycles against LLVM's 43.8 M (minimum; 283.0 M against 284.5 M instructions, nearly
  all in the system allocator both binaries call), and a pass of the gather sum costs
  1.259 M cycles against 1.276 M, 0.84 against 0.85 cycles per element: two dependent
  loads per element at about the load-port rate, with 3.5 instructions per element
  against LLVM's 4.0 (the unrolled `ldp` lanes). At 20 passes the allocator is 63%
  of the program, so the 1.3% faster loop moves the whole by under 1%. No codegen
  lever was found in the allocation phase: its cost is `malloc`'s.
* **`v2_memfill` (0.990 / 0.991; run 2 0.984 / 1.039, 0.865-1.112 medians across
  runs): bandwidth, identical hot code.** base and final emit the same fill, and its
  ratio moves with the load in both directions; the minimum reads 0.982-0.990.
* **`p3_gcd` (1.000 / 1.000): `udiv` latency in both.** The Euclid loop is the
  same `udiv` -> `msub` chain (362 cycles per gcd in both). trust-cg's loop ends in
  `cbz exit; b loop` where LLVM's ends in one `cbnz loop`: one more not-taken
  branch, off the chain. Round 2 materializes each LCG constant once in the
  preheader (two registers fewer live through the loop; no cycle moved).
* **At parity below 1.000 (within noise):** `p2_collatz` (0.997 / 0.998: the same
  3-cycle `add x, x, x, lsl #1` -> `csinc` recurrence, and the same extra latch
  branch as `p3`), `p8_closure_nest` (0.999 / 0.999: its 4-cycle `madd`
  recurrence would be 3 cycles as a shift-add, but its multiplier,
  `black_box(17) | 1`, is a constant only because the bridge lowers `black_box`
  as an identity where LLVM keeps it opaque; not a fair lever), `p4_matmul`
  (1.000 / 1.001, run 2 0.999 / 0.996: `madd` throughput, register-blocked in
  both; round 2's +0.3-0.6% is analysed in section 1).

## 4. Native differential of the rewrites

`runtime_parity_rewrites_aarch64` (registered in
`scripts/check_darwin_aarch64_bridge.py`) compiles
`tests/bridge_corpus/runtime_parity_rewrites.rs` through the bridge and through
LLVM at `-O2` and `-O3` and requires every row and the exit status to be equal:
15 xorshift shift triples (`A < B`, `A == B`, `A > B`, both ends of `1..=63`),
xorshift128+ on a copy of the carried state, a 32-bit xorshift (refused by the
pass), 15 multipliers for the late addend (`2^k - 1`, `1 - 2^k` and the
`2^k + 1` / `2^k` controls), each at 4 trip counts, and an `h3`-shaped `Box`
gather, a `Vec` push/sum and a `Vec` grow/pop at 17 lengths: 179 rows per level.
It also reads the bridge binary back: every 64-bit `xorshift_pair` instance must
contain a `UBFX`/`UBFIZ`, and at `-O3` `box_sum` must load lanes 2 and 3 with one
`LDP` of two X registers at `#0x10` off a non-SP base. Through `main`'s backend
all 179 rows match too, but 0 of 15 instances carry a bitfield move and
`box_sum`'s only non-SP `LDP` is the `Vec` header at `#0x8`, so the witnesses fail
there; this branch's backend has 15 of 15 and the lane pair. At `-O2` that gather
stays rolled (measured), so it is not required there.

Round 2 adds the size offsets: `rem_i32::<D>` (`(x % D) as i32` for 7, 14, 28, 100,
126, 255, 257, 1000), `div_u64::<D>` (14, 126, 1000, `2^63 - 2`) and `rem_u32::<D>`
(14, 28, 126), each over 10 dividends, and `lcg_twice` (`p3`'s two LCG steps) at the
4 trip counts: 154 more rows, 333 per level, 666 in all. Witnesses: `rem_i32`'s five
`msub` tails are the W form and none of its eight instances narrows with a
`mov w0, wN`; no `div_u64` or `rem_u32` instance has the add-back
`add ..., lsr #1`; `lcg_twice` materializes the LCG multiplier once (one
`movk #0x5851, lsl #48`). Through round 1's backend (`9c2f3740a`) the 154 rows match
at both levels and every witness is absent (5 X-form `msub`s and 8 narrowing moves,
add-back in all 4 + 3 instances, the multiplier twice). With round 2's backend:
666 of 666 rows, 30 fused instances, the `-O3` lane pair, and all witnesses.

## 5. Size and compile cost

Emitted-code size (`size_attrib.py`, `emitted_size.py`'s definition), measured
2026-10-07 for `main` `a7ce025ee`, round 1's head `9c2f3740a` (`prev`) and the final
head: geomean 1.0233x (`main`) -> 1.0315x (round 1) -> **1.0201x** LLVM `-O3`
(13,895 -> 13,999 -> 13,839 bytes; LLVM 20,132).

| program | LLVM B | base B | prev B | final B | base x | prev x | final x |
|---|---:|---:|---:|---:|---:|---:|---:|
| b1_mispredict | 564 | 784 | 792 | 788 | 1.390 | 1.404 | 1.397 |
| h1_vec_push_sum | 936 | 792 | 816 | 812 | 0.846 | 0.872 | 0.868 |
| h2_vec_grow | 940 | 996 | 1,024 | 1,020 | 1.060 | 1.089 | 1.085 |
| h3_box_leak | 956 | 868 | 892 | 888 | 0.908 | 0.933 | 0.929 |
| h4_vec_dropper | 1412 | 900 | 884 | 880 | 0.637 | 0.626 | 0.623 |
| m1_call_chain | 396 | 460 | 460 | 456 | 1.162 | 1.162 | 1.152 |
| m2_call_heavy | 424 | 444 | 452 | 448 | 1.047 | 1.066 | 1.057 |
| p1_xorshift | 488 | 436 | 444 | 440 | 0.893 | 0.910 | 0.902 |
| p2_collatz | 384 | 456 | 456 | 452 | 1.188 | 1.188 | 1.177 |
| p3_gcd | 436 | 536 | 536 | 500 | 1.229 | 1.229 | 1.147 |
| p4_matmul | 984 | 2,142 | 2,142 | 2,082 | 2.177 | 2.177 | 2.116 |
| p5_struct_acc | 400 | 448 | 452 | 448 | 1.120 | 1.130 | 1.120 |
| p6_branch_match | 524 | 628 | 636 | 632 | 1.198 | 1.214 | 1.206 |
| p7_sieve | 9248 | 1,169 | 1,169 | 1,165 | 0.126 | 0.126 | 0.126 |
| p8_closure_nest | 396 | 452 | 452 | 448 | 1.141 | 1.141 | 1.131 |
| v1_saxpy | 656 | 844 | 844 | 840 | 1.287 | 1.287 | 1.280 |
| v2_memfill | 420 | 664 | 664 | 660 | 1.581 | 1.581 | 1.571 |
| v3_popcount | 568 | 876 | 884 | 880 | 1.542 | 1.556 | 1.549 |
| **total / geomean** | 20,132 | 13,895 | 13,999 | 13,839 | **1.0233** | **1.0315** | **1.0201** |

`main`'s per-program bytes are the same at `a7ce025ee` as at `31ad5cd29`, `f0350c84e`
and `e4ae21c81`, and round 1's head's are those of `6885641f0` and `ccda0fe59`.
Function by function, round 2 changes `done` in all 18 programs (60 -> 56 bytes: the
pre-shift) and `main` in two: `p3_gcd` 188 -> 156 (each LCG constant once) and
`p4_matmul` 1,420 -> 1,364 (two pre-shifted `% 100`s, the `% 100` magic once, and
the spilled `% 576` magic once with its four spill stores).

**The task's size bound is still not met, and this record does not claim it.** The
task allows no size regression past a 1.0x geomean. `main` is above it (1.0233x), and
round 1 added 0.8% (1.0315x, +104 bytes). Round 2 removes 160 bytes, so the branch now
emits 56 bytes fewer than `main` (1.0201x, 0.3% below it) while keeping every
runtime rewrite of section 2: it adds no size over `main`, but neither reaches 1.0x.
Getting under 1.0x needs `main`'s own growth back (below) or the structural items
below; landing the branch above 1.0x still needs the owner's or the integrator's
acceptance of the bound. The bytes round 1 added are all speed rewrites: 8 bytes per
fused xorshift pair (`b1`, `h1`-`h3`, `m2`, `p1`, `p6`, `v3`), the NEON sum loop and
its scalar tail that the hoisted `Vec` pointer enables (`h1`, `h2`), the unrolled
gather (`h3`), and 4 bytes in `p5`; `h4` shrinks.

**Why `main` is at 1.0233x and not the 0.951x of
[`2026-09-30-darwin-emitted-size`](../2026-09-30-darwin-emitted-size/README.md).**
That record's 12,484 bytes were its branch on top of `main` `c84d39e93`; today's
`main` emits 13,895, against the same 20,132 bytes of LLVM. Comparing its
per-function attribution (`data/attrib.json`, recovered from `d4e3a331a`, sha256
`3c42a6e5…` as listed there) with today's, function by function: 12 of the 18
programs have the same byte counts, and all 1,411 added bytes are in the `main`
function of six programs and in new constant data beside it:

| program | 2026-09-30 B | `main` B | its `main` fn B | new constant data B | the failure-path calls `main` now makes |
|---|---:|---:|---:|---:|---|
| h1_vec_push_sum | 728 | 792 | 380 -> 444 | 0 | `__rust_alloc_error_handler`, `raw_vec::capacity_overflow` |
| h2_vec_grow | 732 | 996 | 384 -> 504 | 144 | `panic_bounds_check`, `panic_const_rem_by_zero`, the two above |
| h3_box_leak | 648 | 868 | 300 -> 520 | 0 | `__rust_alloc_error_handler` (2), `capacity_overflow` |
| h4_vec_dropper | 740 | 900 | 392 -> 552 | 0 | `__rust_alloc_error_handler`, `capacity_overflow` |
| p4_matmul | 1,576 | 2,142 | 1,092 -> 1,420 | 238 | `panic_bounds_check` (6 sites) |
| p7_sieve | 1,032 | 1,169 | 580 -> 600 | 117 | `panic_bounds_check` |

The constant data is one 24-byte `core::panic::Location` per panic site and the
93-96-byte source path it names. Inside those `main`s the added instructions are the
failure paths themselves (in `p4` and `p7` a bare `brk` became `adrp; add; mov …;
bl panic_bounds_check; brk`, the `brk` count unchanged; in `h1`-`h4` each new
noreturn call also gets a `brk`) and the spills and moves the calls force (spill
instructions +5, +4, +6, +13, +7 and 0). These are `main`'s own lowering
changes between `c84d39e93` and `b422f87fd`, which took the bridge's failure paths
from a trap to the real Rust runtime calls (among them `acb3403fe`, "Adopt coherent
v52 panic cohort with fail-closed Assert semantics", and `c876e3bd0`, "Restore
source-kind Rust panic and foreign-abort cleanup paths"; not bisected here). With
those six programs at their 2026-09-30 sizes, `main` would read the old 0.9514x.

The rest of the gap to LLVM is structural and predates this branch: trust-cg
emits its own `___trustcg_array_fill_*` helpers (96-136 B) where LLVM calls
`memset`; `p4_matmul`'s `main` has 52 spill instructions (56 on `main`; LLVM 19);
and every program's `done` is now 56 B against LLVM's 48: the call's argument copy
`mov w0, w3` that LLVM avoids by writing `msub w0, …, w0` (the allocator interference
of section 2, item 7), and a `brk` after the noreturn `exit` call. Without those two
the branch would read 1.0075x (`main` with all three `done` offsets 1.0043x).

Compiler cost (`ab_measure.py compile`, the same command line as `run.py`, median of
3 after a warmup, load 5.2-8.8, `main` `a7ce025ee`, `prev` and final):
instructions retired final / `prev` 0.9974 to 1.0024 per program, geomean
**1.0000**, final / base 0.9991 to 1.0009, geomean **0.9999**; peak RSS geomean
1.0000 and 0.9993. (Round 1, `main` `f0350c84e` against `ccda0fe59`, load 6.2-7.3:
1.0003 and 1.0001; 2026-10-06, load 122-133: 1.0000 and 0.9992.)

## 6. Correctness and gates

At `df611c4de` (this branch after merging `origin/main` `2ac5b7620`). The backend
built at that merge emits all 18 corpus programs byte-identical to the `75869f1f8`
backend measured above.

* `trust-cg-opt` all targets: lib 4,318 passed, 0 failed, 2 ignored; its 8
  integration targets passed.
* `must_refuse_corpus`: codegen 5 passed, CLI 1 passed.
* `scripts/check_fmt.sh`, `scripts/check_tippy.sh` (its 5 packages clean),
  `scripts/check_documentation.py --check`, `scripts/native_test_host_matrix.py
  --check`: clean. `trust-cg-opt` is outside `check_tippy.sh`'s package list; linted
  directly (`targo tippy -p trust-cg-opt --tests`) it reports 142 lib findings on
  `main`'s code, none in a hunk this branch adds or changes.
* Gate unit tests: `test_darwin_aarch64_bridge_gate` 59 OK;
  `test_darwin_aarch64_gate` with `test_linux_aarch64_gate` 106 OK (4 skipped);
  `test_native_test_host_matrix` 11 OK. Before `df611c4de` the Darwin module failed
  `test_required_inventory_matches_source_census_and_linux_floor` and
  `test_preflight_error_is_retained_and_cannot_pass` identically on `origin/main`
  `2ac5b7620`: two native targets `main` landed without a floor row
  (`a64_refine_byte_invariance`, `aarch64_mem_pair_acquire_order`) made the floor
  inventory refuse every run. `df611c4de` registers them (Darwin minimums 6 and 2,
  both passing here; Linux rows not yet run on a Linux host).
* **Darwin bridge gate** (`scripts/check_darwin_aarch64_bridge.py`, all 27 targets,
  with a private `RUSTUP_HOME` whose `trust` toolchain links the PATH package,
  because this machine's shared rustup `trust` link points at another sysroot and
  the gate refuses that divergence): 19 pass, including the new
  `runtime_parity_rewrites_aarch64` and `opt_loop_state_run`'s four AArch64 tests;
  8 fail. The same gate on `origin/main` `2ac5b7620` (a detached worktree, same
  environment) fails the same 8 targets with the same per-test verdicts: `hello_loop`,
  `float_semantics`, `overflow_asserts`, `reference_union_semantics`,
  `unsupported_program`, `fixed_cost_budget_aarch64` and `real_program_corpus_a64`
  (the certificates-on lane: `[TCG-PROOF-465]` proof promotion, `[TCG-EH-UNPROVED]`)
  and `opt_loop_state_run`'s two x86-64 tests (no Rosetta, no x86-64 execution route
  on this host).
* **Darwin floor** (`scripts/check_darwin_aarch64.py --jobs 3 --timeout-seconds
  3600`, 296 targets): 290 pass, 2,039 executed passes against 2,014 required; 6
  fail, none of them new:
  * `e2e_cegis_superopt` (the same 5 tests fail on `origin/main`:
    `CegisIncomplete { completion: VerifierError }`), `local_function_address_jit`
    (the same 1 test) and `jit_fail_closed_proof_policy` (the same 6 tests): proof
    promotion of the JIT's uncovered opcode inventory;
  * `e2e_aarch64_elf_relocation_model`: 19 passed, but 3 SKIP for want of `rust-lld`
    or `ld.lld` on this host, on `origin/main` too;
  * `jit_source_bound_arithmetic`: exceeded the 3,600 s bound inside its first test
    (proof-required JIT of straight-line add/sub functions, which none of this
    branch's rewrites can touch: no loop, multiply, xorshift pair or stack-slot field
    address); on `origin/main` the same test was still running after 76 minutes when
    stopped;
  * `macos_deployment_target`: did not build in that run (`E0460`: a
    `trust_cg_ir` in the Trust package's sysroot beside `target/debug`'s); run alone
    it passes 5 of 5 on this branch and on `origin/main`.
* The native differential: `runtime_parity_rewrites_aarch64` passes in the bridge
  gate (358 rows, 30 fused instances, the `-O3` lane pair).
* No production-lane corpus program compiles on either tree (see the opening
  paragraph); nothing here changes that.

**At the final head `6d9e281b8`** (after merging `origin/main` `96eac8183`: the
L09-P6 whole-body owner and the trust-ir pin `5dbbf177`). The backend built there
emits all 18 corpus programs byte-identical to the measured one (sha256
`65a536f945910fbb…`).

* `trust-cg-opt` all targets: lib 4,318 passed, 0 failed, 2 ignored, and its 8
  integration targets; `must_refuse_corpus` codegen 5, CLI 1.
* `check_fmt.sh`, `check_documentation.py --check`, `native_test_host_matrix.py
  --check` and the four gate unit-test modules (`test_darwin_aarch64_gate`,
  `test_linux_aarch64_gate`, `test_darwin_aarch64_bridge_gate`,
  `test_native_test_host_matrix`): clean.
* `check_tippy.sh`: one finding, a collapsible `if` at
  `crates/trust-cg-verify/src/closed_definition_alethe_guard.rs:205` from
  `origin/main`'s `b61b71543`; the same gate on `origin/main` `96eac8183` reports the
  same single finding, and this branch does not touch `trust-cg-verify`.
* Darwin bridge gate: 19 pass (the native differential: 358 of 358 rows, 30 fused
  instances, the `-O3` lane pair), the same 8 targets fail with per-test verdicts
  identical to `origin/main` `2ac5b7620`'s run.
* Darwin floor, the 39 targets whose names match the optimizer's areas (loops,
  unroll, vector/NEON, memory pairs, multiplies, pipelines, the fuzz sweeps, the
  two registered targets and the new whole-body owner) with `--only`: 38 pass (278
  executed passes); `e2e_cegis_superopt` fails the same 5 tests as on `origin/main`.
  The full floor ran once, at `df611c4de`, above.

After one more merge (`70132f00b`, `origin/main` `e4ae21c81`: `trust-cg-verify`
guard construction and body-admission bounds only), `check_tippy.sh` is clean (5
packages; `main` fixed the finding above), and `check_fmt.sh`,
`check_documentation.py --check`, `native_test_host_matrix.py --check`, the four gate
unit-test modules (176 tests, 4 skipped), `trust-cg-opt` all targets (4,318 / 0 / 2
and 8 integration targets) and `must_refuse_corpus` (5 and 1) pass.

**Review round 1 (2026-10-07), after merging `origin/main` `31ad5cd29`, `f0350c84e`
and `fcfe21d60`.**

* The full Darwin floor (`--jobs 3 --timeout-seconds 3600`, 297 targets) at the
  `f0350c84e` merge: 292 pass, 2,055 executed passes against 2,024 required; the run
  is marked failed also because this round's test and record commits landed while
  it ran ("source changed"). The 5 failing targets fail with the same per-test
  verdicts on `origin/main` `fcfe21d60` as on this branch's final head:
  `jit_fail_closed_proof_policy` (the same 6 tests), `e2e_cegis_superopt` (the same
  5), `local_function_address_jit` (the same 1), `e2e_aarch64_elf_relocation_model`
  (19 passed, 3 SKIP for want of `rust-lld`/`ld.lld`), and `jit_source_bound_arithmetic`
  (killed at 3,600 s inside its first test,
  `proof_required_arithmetic_executes_all_types_shapes_and_levels`; `origin/main`'s
  test binary, run directly, was killed by the same bound inside the same test). `origin/main`'s own
  floor refuses to start (`a64_refine_byte_invariance` and
  `aarch64_mem_pair_acquire_order` unclassified; this branch registers them), so its
  side was run as `trust_cargo.sh test -p trust-cg-codegen --test <target> --
  --show-output --test-threads=1` in a detached worktree sharing this target
  directory. `macos_deployment_target`, which did not build in the previous full run,
  passed.
* Darwin bridge gate at the `f0350c84e` merge (a private `RUSTUP_HOME` whose `trust`
  links the PATH package; its report also carries `DARWIN_BRIDGE_SOURCE_CHANGED`,
  because this round's lint fix to a test file landed during it): 21 of 29 targets pass, including `runtime_parity_rewrites_aarch64` (358 of 358
  rows, 30 fused instances, the `-O3` lane pair); the other 8 fail, and `origin/main`
  `f0350c84e` (20 of 28) fails the same 8 with identical per-test verdicts (`hello_loop`,
  `float_semantics`, `overflow_asserts`, `reference_union_semantics`,
  `unsupported_program`, `fixed_cost_budget_aarch64`, `real_program_corpus_a64`:
  `[TCG-PROOF-465]`/`[TCG-EH-UNPROVED]` in the certificates-on lane;
  `opt_loop_state_run`: the same two tests). The native differential also passes
  run directly at the final `fcfe21d60` merge.
* The harness at the final merge (`run.py --dylib <that backend> --allow-loaded`):
  diagnostic lane 18 of 18 MATCH, emitted size 1.0315x, wall geomean 0.926x (load
  9-13; per-program wall ratios between its separately run lanes are not results);
  production lane 0 of 18 MATCH, 18 INCOMPLETE, every compile refused with
  `[TCG-PROOF-465]` and `[TCG-MIR-UNSUPPORTED]`. That backend emits all 18 corpus
  programs with sections identical to the binaries measured in section 1's run 2.
* `trust-cg-opt` all targets: lib 4,321 passed (the three new lane-offset tests),
  0 failed, 2 ignored, and its 8 integration targets; `must_refuse_corpus` codegen 5,
  CLI 1; `check_fmt.sh`, `check_tippy.sh` (5 packages clean),
  `check_documentation.py --check`, `native_test_host_matrix.py --check`, and
  `test_darwin_aarch64_gate`, `test_linux_aarch64_gate` and
  `test_darwin_aarch64_bridge_gate` (165 tests, 4 skipped). `targo tippy -p
  trust-cg-opt --tests` reports no finding in a file this round adds or changes.

**At the final head** (after merging `origin/main` `577d3e716`: the L04-P12 merge and
trust-ir pin `b5e09ef1`; `scripts/tests/test_linux_aarch64_gate.py` resolved to 229
Linux rows, main's trap-expansion row plus this branch's two). The backend built
there (sha256 `b004163251a59f72…`) emits all 18 corpus programs with sections
identical to section 1's run 2, so the measurements apply unchanged.
`runtime_parity_rewrites_aarch64` run directly: 358 of 358 rows, 30 fused instances,
the `-O3` lane pair. `trust-cg-opt` all targets (lib 4,321 / 0 / 2, and the 8
integration targets), `must_refuse_corpus` (codegen 5, CLI 1), `check_fmt.sh`,
`check_tippy.sh` (5 packages clean), `check_documentation.py --check`,
`native_test_host_matrix.py --check`, `test_darwin_aarch64_gate` with
`test_linux_aarch64_gate` (106 tests, 4 skipped) and `test_darwin_aarch64_bridge_gate`
(59): pass.
The Darwin bridge gate at `7fdde60ab` (no source change during the run, no
finding): 21 of 29 targets pass with `runtime_parity_rewrites_aarch64`, 73 credited
tests; the same 8 targets fail with per-test verdicts identical to `origin/main`
`f0350c84e`'s run above. Darwin floor, 22 optimizer-area targets with `--only`
(the trap-expansion rows main just added, the unroll, NEON and vector-spill
executions, `e2e_full_pipeline`, `e2e_opt_levels`, `xxh3_main_loop_trust_ir`, the
two rows this branch registers and the multiply and select-flags rows): 22 pass,
119 executed passes.

After one more merge (`origin/main` `7ec11048d`, shared NZCV observations, which
touches `trust-cg-opt`'s effects, DCE and compare fusion): `main` added
`jit_nzcv_observation` (macOS-guarded, one test) without a Darwin floor row, so the
floor inventory refused every run and `test_darwin_aarch64_gate` failed its
inventory and preflight tests, as on `origin/main` (whose floor script names none of
the three unregistered targets). This branch registers it (minimum 1; it passes 1/1
with `--only`; compiled out on Linux, so no Linux row). There: the bridge backend's 18
corpus programs have the measured run's per-function byte and instruction-class
counts (`size_attrib.py`; exit codes equal), `runtime_parity_rewrites_aarch64` 358 of
358, `trust-cg-opt` lib 4,331 / 0 / 2 and
its 8 integration targets, `must_refuse_corpus` 5 and 1, and the format, lint,
documentation, host-matrix and gate unit-test checks pass.

**Review round 2 (2026-10-07), the size offsets, after merging `origin/main`
`a7ce025ee`** (L10-P3's per-pass translation validation and the core-proof cohort).
The merge conflicted in `scripts/tests/test_linux_aarch64_gate.py` only (the Linux
floor's row count: 230, `main`'s pass-validation row plus this branch's two), and
`main` now registers the three Darwin floor rows this branch had added
(`a64_refine_byte_invariance`, `aarch64_mem_pair_acquire_order`,
`jit_nzcv_observation`), so the merged inventory held them twice and refused every
run; `cc3c9ec46` drops this branch's copies (`scripts/check_darwin_aarch64.py` now
equals `main`'s). The new pass has no dedicated per-pass validator; under L10-P3's
policy that is an uncovered run, recorded and not refused, as for most passes. At
the merge `b1e777af5` (the gate scripts and their unit tests at `cc3c9ec46`):

* `trust-cg-opt` all targets: lib 4,418 passed (8 new `const-chain-dedup` tests),
  0 failed, 2 ignored, and its 7 integration targets; `trust-cg-lower` all 50
  targets: 2,710 passed, 0 failed (the new `magic_udiv` and isel tests among them);
  `trust-cg-fuzz` `diff_int_divrem`: 18,016 configurations, 0 defects;
  `must_refuse_corpus`: codegen 5, CLI 1.
* `runtime_parity_rewrites_aarch64` run directly: 666 of 666 rows, 30 fused
  instances, the `-O3` lane pair and the size-offset witnesses.
* `check_fmt.sh`, `check_tippy.sh` (5 packages clean), `check_documentation.py
  --check`, `native_test_host_matrix.py --check`, and `test_darwin_aarch64_gate`,
  `test_linux_aarch64_gate` and `test_darwin_aarch64_bridge_gate` (165 tests, 4
  skipped). `targo tippy -p trust-cg-opt --tests` and `-p trust-cg-fuzz --tests`
  report no finding in a file this round adds or changes.
* **Darwin floor** at `8f7c9b943` (`--jobs 3 --timeout-seconds 3600`, 301 targets,
  no source change during the run): 295 pass, 2,065 executed passes against 2,035
  required; 6 fail, each with the same per-test verdicts on `origin/main`
  `a7ce025ee` (the detached worktree, run as `trust_cargo.sh test -p
  trust-cg-codegen --test <target> -- --show-output --test-threads=1` with this
  worktree's target directory):
  * `jit_fail_closed_proof_policy` (the same 6 tests), `e2e_cegis_superopt` (the same
    5), `local_function_address_jit` (the same 1): as in round 1;
  * `e2e_aarch64_elf_relocation_model`: 19 passed, 3 SKIP for want of `rust-lld` or
    `ld.lld`;
  * `tmbc_roundtrip_prop`, new on `main` since round 1:
    `construct_generator_covers_every_family_and_both_outcomes` ("the generator never
    produced a text-refused `EnumFieldNames`"), a trust-ir codec property test;
  * `jit_source_bound_arithmetic`: killed at 3,600 s inside its first test,
    `proof_required_arithmetic_executes_all_types_shapes_and_levels`, as in round 1;
    `origin/main` `a7ce025ee`'s binary, run the same way under the same bound, was
    killed inside the same test (exit 124 after 3,600 s).

**After one more merge** (`9360d117a`, `origin/main` `4451a21f6`: the L07-P2 merge;
conflicts only in `CHANGELOG.md`, both bullets kept, and the Linux floor's row
count, now 231). The release backend built there (sha256 `ff5204936eb4765f…`)
emits all 18 corpus programs with sections identical to the measured final one, so
sections 1-5 apply unchanged. There: `trust-cg-opt` all targets (lib 4,418 / 0 / 2
and 7 integration targets), `trust-cg-lower` all 50 targets (2,713 passed, 0
failed), `diff_int_divrem` (18,016 configurations, 0 defects), `must_refuse_corpus`
(codegen 5, CLI 1), `runtime_parity_rewrites_aarch64` (666 of 666 rows, every
witness), `check_fmt.sh`, `check_tippy.sh` (5 packages clean),
`check_documentation.py --check`, `native_test_host_matrix.py --check` and the three
gate unit-test modules (165 tests, 4 skipped) pass. The Darwin floor's 20 targets
nearest this round's changes and the merge, with `--only` at `f86b9b028`
(`diff_int_divrem`, the bit-op, cast and pressure sweeps, the pass-validation,
construct-sweep, full-pipeline, opt-level, xxh3 and unroll rows, `main`'s new
`aarch64_memory_source_binding`, `divtest_e2e`, two `trust-cg-lower` constant rows
and the two rows `main` now registers): 20 pass, 185 executed passes against 182
required. The full floor ran once, at `8f7c9b943`, above.

**At the final head** (`01e09b50c`, after merging `origin/main` `0bc9da3ee`, L06-P3's
bridge differential corpus: changes in `crates/rustc-codegen-trust-cg` only; the
conflict was the bridge gate unit test's totals, now `main`'s plus this branch's
`runtime_parity_rewrites_aarch64` row: 142 required tests, 72 certificates-off). The
release backend built there (sha256 `b067c0f056558dff…`) emits all 18 corpus
programs with the measured final sections; `runtime_parity_rewrites_aarch64` 666 of
666 rows with every witness; `check_fmt.sh`, `check_documentation.py --check`,
`native_test_host_matrix.py --check` and the three gate unit-test modules (165
tests, 4 skipped) pass. No root crate changed since `9360d117a`, whose crate gates
above stand.

## 7. Earlier measurements, for the record

**Run 2, 2026-10-07, `main` `f0350c84e` against round 1's `ccda0fe59`** (21
interleaved rounds, load 5.0-7.2; `commands/tables.py runtime`; the corpus byte counts
equal section 5's `prev` column):

| program | base cycles min / med | final cycles min / med | base instr | final instr | final wall min | load |
|---|---:|---:|---:|---:|---:|---|
| b1_mispredict | 1.013 / 1.011 | 0.981 / 0.979 | 1.062 | 1.185 | 0.983 | 7.1-7.2 |
| h1_vec_push_sum | 2.901 / 2.882 | 0.988 / 0.986 | 5.044 | 1.101 | 0.980 | 7.1-7.1 |
| h2_vec_grow | 1.234 / 1.247 | 0.893 / 0.903 | 1.299 | 0.961 | 0.928 | 7.1-7.1 |
| h3_box_leak | 1.172 / 1.189 | 0.989 / 0.993 | 1.221 | 0.960 | 0.993 | 7.0-7.1 |
| h4_vec_dropper | 0.928 / 0.927 | 0.847 / 0.852 | 1.064 | 0.973 | 0.875 | 7.0-7.0 |
| m1_call_chain | 0.931 / 0.932 | 0.931 / 0.932 | 1.087 | 1.087 | 0.929 | 7.0-7.0 |
| m2_call_heavy | 0.974 / 0.973 | 0.912 / 0.917 | 0.539 | 0.654 | 0.917 | 6.8-7.0 |
| p1_xorshift | 1.008 / 1.008 | 0.963 / 0.965 | 1.551 | 1.992 | 0.964 | 5.7-6.8 |
| p2_collatz | 0.997 / 0.998 | 0.997 / 0.998 | 1.140 | 1.139 | 0.998 | 5.3-5.7 |
| p3_gcd ** | 1.001 / 1.001 | 1.001 / 1.001 | 1.189 | 1.189 | 1.000 | 5.0-5.3 |
| p4_matmul | 1.000 / 0.997 | 0.999 / 0.996 | 1.076 | 1.076 | 0.998 | 5.1-5.1 |
| p5_struct_acc | 1.000 / 1.000 | 0.889 / 0.889 | 1.000 | 1.099 | 0.888 | 5.1-6.1 |
| p6_branch_match ** | 1.025 / 1.032 | 1.012 / 1.018 | 1.116 | 1.218 | 1.010 | 5.8-6.7 |
| p7_sieve | 0.783 / 0.792 | 0.782 / 0.793 | 0.977 | 0.977 | 0.808 | 5.9-5.9 |
| p8_closure_nest | 0.999 / 0.999 | 0.999 / 0.999 | 1.197 | 1.197 | 1.010 | 5.9-6.1 |
| v1_saxpy | 0.736 / 0.745 | 0.734 / 0.742 | 1.653 | 1.653 | 0.751 | 6.1-6.2 |
| v2_memfill ** | 0.983 / 0.991 | 0.984 / 1.039 | 1.140 | 1.139 | 1.002 | 6.2-6.2 |
| v3_popcount | 0.696 / 0.709 | 0.689 / 0.707 | 0.617 | 0.618 | 0.785 | 6.2-6.2 |
| **geomean** | 1.0209 / 1.0249 | 0.9161 / 0.9229 | 1.1749 | 1.0858 | 0.9308 | |

**2026-10-06, `main` `530a9319a` against this branch at `75869f1f8`** (11 rounds,
load 72-160; the corpus byte counts equal section 5's `prev` column). Cycles geomean base
1.019 / 1.023, final 0.919 / 0.922 (a second run at load 30-47: 1.0252 / 1.0252 and
0.9192 / 0.9296). Its per-program rows differ from section 1 beyond noise only in
`h1` (1.003 / 1.008; second run 0.985 / 1.002), `h3` (0.974 / 0.966; second run
0.968 / 0.947), `v2` (0.983 / 0.865) and `p4`'s median (0.988; second run 1.011).
`v3` differs from base only in its 4,096-iteration initialization loop (one fused
xorshift pair, 8 bytes), which moves the hot popcount loop by 8 bytes; a median of
0.749 against base's 0.689 in that run did not reproduce in a focused 21-round run
(base 0.701 / 0.684, final 0.686 / 0.676, load 135), nor in runs 1-4.
The harness's own record then (`benchmarks/beat-llvm/run.py --dylib <the merged
backend> --allow-loaded`, both of its lanes): diagnostic lane
(`--bridge-cg-arg no-proof-certs`, load 39) 18 of 18 MATCH, 0 MISMATCH,
emitted-code size 1.0315x, runtime geomean 0.977x in wall time (median of 5 after a
warmup; its lanes run minutes apart, so its per-program wall ratios move with the
load: `p1` 1.22x and `p4` 1.14x where the interleaved cycles read 0.964x and
0.995x); production lane (certificates on, load 36-63) 0 of 18 MATCH, 18
INCOMPLETE, every bridge compile refused (`[TCG-PROOF-465]`).

**2026-10-01, `main` `b422f87fd`.** On 2026-10-01 `main` had lost the whole vectorizable class: the MIR bounds
assertion had begun to lower to the real `panic_bounds_check` call, and the
dominated in-loop checks it raises from were no longer folded (`v1_saxpy` 8.0x,
`v2_memfill` 25.8x, `v3_popcount` 36.0x, `p7_sieve` 3.1x, `h1_vec_push_sum` 2.8x
LLVM cycles; geomean 1.877x). This branch folded them first (`6ed3ba2eb`), and
`main` landed the same rule independently (`0523caaa7` for a length register,
`b2bf85bb4` for a constant), which the merge keeps. That run read the branch at
0.922x / 0.925x (load 32-53) with the same three programs at or above parity
plus `p4` and `v2` within noise, and emitted size 1.0830x -> 1.0253x against
that older base. Those numbers are superseded by sections 1-5.

## 8. Next steps, exact

* **`p6`:** predicate a multi-way dispatch of cheap pure arms only where the
  selector is known unpredictable. The lever is 0.243x in the C model and costs
  1.221x on a predictable selector, so the decision needs profile data (the
  `pgo_round_trip` path) or an explicit unpredictability marker; a static rule
  would trade one program for others. Separately, a variable-rotate opcode
  (`RORV`: encoder, operand roles, verifier semantics) and an AND-of-AND fold for
  the rotate amount shorten the `Rot` arm.
* **Size:** the even-divisor pre-shift and the W-form remainder tail are done
  (section 2, item 7). Left in `done`, 4 bytes each: (a) the argument copy after a
  W-form remainder, which needs the allocator to give a definition the register of an
  operand whose last use is the same instruction (the liveness model ends a use's
  range one past the instruction and starts the definition's at it), or the
  post-allocation coalescer to retarget a producer into a call-argument register
  after the argument repair (`post_ra_coalesce` keeps every call-argument copy until
  then); either changes bytes far beyond the corpus; (b) whether a `brk` after a call
  to a noreturn function is required by the proof lane. Then `p4_matmul`'s spills
  and the array-fill helpers against `memset`.
* **Latch layout:** `p2` and `p3` end their inner loops in `b.cond exit; b loop`
  where LLVM uses one inverted branch; no cycles at stake in these
  latency-bound loops, 4 bytes each.
* **`h1`:** no codegen lever was found; it runs at the L2 streaming rate.

## Files

* `commands/bench.py`: the interleaved runtime A/B (cycles, instructions, wall, load).
* `commands/tables.py`: renders sections 1 and 5 from the JSON, and classifies each
  program over several runs against the ±0.5% band (`classes`).
* `commands/abmodes.py`: the same A/B for one binary's modes (the C models).
* `commands/mkvariant.sh`: compiles a source in each lane as the harness does
  (the `h1` 0- and 600-pass variants, and `h3`'s 0- and 200-pass ones).
* `commands/*.c`: the latency microbenchmarks and C models cited above (build lines
  in each file's header).
* Compile and attribution: `../2026-09-30-darwin-emitted-size/commands/size_attrib.py`
  (`--lane base=<dylib>:no-proof-certs --keep-work`) and `ab_measure.py`
  (`compile --lane …`), unchanged.
* The measurement JSON (bench, attribution, compile, harness record) is kept out of
  tree, per the durable-evidence policy; the tables above are rendered from it.
