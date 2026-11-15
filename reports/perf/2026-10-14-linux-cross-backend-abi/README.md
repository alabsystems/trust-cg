# Cross-backend ABI differential on Linux AArch64 — 2026-10-14

Ledger gap L06-P9: the three cross-backend generators (`benchmarks/abi-xback`,
`benchmarks/regclass-xback`, `benchmarks/sret-xback`) ran in no required Linux
runner. This change adds the required runner
[`scripts/check_linux_aarch64_xback.py`](../../../scripts/check_linux_aarch64_xback.py),
which [`scripts/check_linux_aarch64_bridge.py`](../../../scripts/check_linux_aarch64_bridge.py)
invokes on the backend snapshot that lane builds and qualifies, and the
named-family generator
[`benchmarks/abi-xback/families.py`](../../../benchmarks/abi-xback/families.py).
The ruling on what the step admits is LD-27 in the
decision record. The families found that
over-aligned C arguments were placed unlike rustc's Linux `FnAbi`; the bridge
now places them as rustc does (LD-28), except as a fixed argument of a
C-variadic function, where they are refused by name (LD-29, 2026-10-15).

This is ABI execution evidence in Trust's unverified frontend lane with proof
certificates and the refinement solver off. It is not proof evidence, not a
Darwin record and not a claim about shapes outside the generated domain.

## History: the first implementation and its reviews

The runner was first written on `6d57acba4` (branch `615514fa4`, never
landed): 222 cases, 2,464 of 2,664 cross cells matched, 31 listed refusals, no
wrong value. Its review refuted it. (1) Over-aligned C composites
(`#[repr(C, align(16))]` over 8-, 4- or 1-byte members) were silent wrong
values in both mixed pairings at O0–O3 on that base: the bridge started them on
an even register and a 16-aligned stack slot, rustc's Linux `FnAbi` does not
(`unadjusted_abi_align`); the domain had no such shape. (2) When a group was
rebuilt one case per crate pair, the cells its whole-group attempt had already
executed were dropped unjudged (52 in that record), so a wrong value there
passed. Lesser findings: `byref_fat_rust` was described as splitting a fat
pointer it does not split, two runner mutations survived the unit tests (the
decline-tag union and the certificate knobs), and refused shapes hid inside
declined cases. The review's two reproducers are
[`al16-pair/`](al16-pair/) (`{u64, u64}` at x1 and as a result) and
[`al16-u32/`](al16-u32/) (`{u32}` at x1 and on the stack after a `u8`), run
with [`pair4.py`](pair4.py).

The port onto `395954590` (head `24723c172`, lane at `8df585cd2`: 380 cases,
3,908 of 4,560 cross cells matched, 652 declined cells in 105 rows, no wrong
value) was refuted by its own review on one finding. A trust-cg CALLER of an
LLVM-built C-variadic function passed an over-aligned FIXED argument where
rustc's `FnAbi` does not: `va_pad_u64(u64, #[repr(C, align(16))] {u64}, u64,
...)` read `1020400 135247732` for `1020304 1020304` at O0–O3 (likewise
`{u32}` and `{u8}`, and the repr(C) wrapper around a 16-aligned member), and
generated cases crashed with SIGSEGV on that branch's backends; `395954590`'s
backend printed the same wrong values. The whole-signature check skipped
C-variadic signatures, and the two-unit declaration of LD-28 is not taken on
that route. The runner's `varargs` family had only scalar fixed arguments, so
it could not see this.
Lesser findings: three runner mutants survived the unit tests (V13, a trust-cg
CALLER refusal of a whole group did not have to trigger the per-case rebuild;
V20, group-mode rows could stand in for that rebuild; V21, a group refusal
could be checked against the first per-case refusal's tags instead of their
union), the generator README still counted 326 family cases, and the
thirty-two-argument spill it listed as coverage executes nothing
(`spill_all_c` is refused on both sides). The review's reproducer is
[`va-fixed/`](va-fixed/).

The fix (`217946d09`, record at `03a8d9a31`: 387 cases, 3,920 of 4,644
cross cells matched, 724 declined in 117 rows, no wrong value) was refuted by
the next review on two findings. A call through a C-variadic `fn` pointer
that passes NO anonymous argument takes the ordinary `fn`-pointer route (its
argument count equals the pointer's input count), and on `395954590`'s
backend a trust-cg caller passing `#[repr(C, align(16))] {u64}` that way read
`10200` (O0) or an unrelated value (O1–O3) for `10203`; `217946d09` refused
it only through a branch no test reached (the review's mutant M3 removed it
and every committed check stayed green), and this README said such calls
stayed refused by their argument count, which holds only when an anonymous
argument is passed. Lesser: the new call-site whole-call check never fired,
because the declaration's own check ran first and refused the same inputs
(mutant M1 deleted it unnoticed), and the planted error offered as its
evidence rewrote the check's own input. The review's reproducer is
[`va-pointer/`](va-pointer/). Each finding of the three reviews is closed
below.

## Result

Inside the required bridge lane (below), on the backend it built from
`e15ffc0ea`: **no wrong value and no crash.** Over 396 cases (40 `abi-xback`
seeds, 346 named family cases, 9 `regclass-xback` pairs, 1 `sret-xback` pair),
each at O0, O1, O2 and O3 in all four caller × callee pairings, **3,928 of the
4,752 cross cells** (LLVM caller × trust-cg callee, trust-cg caller × LLVM
callee, trust-cg × trust-cg) executed and printed exactly the LLVM oracle's
output, and every oracle printed the line its generator computed without a
compiler (regclass/sret: exit 42). The other **824 cells are the 133 listed
refusal rows**, each an exit-1 compile whose every error carries a `[TCG-...]`
tag, each declined cell with exactly its row's tag set; none is a build
failure, a link failure or a timeout. The runner also judged the 820 cells
that whole-group attempts executed before their groups were rebuilt one case
per crate pair (764 oracle cells, 56 cross cells): none was wrong.

| suite / family | cases | cross cells matched | declined |
| --- | --- | --- | --- |
| `abi-xback` seeds 1–40 | 40 | 480 | 0 |
| `regclass-xback` | 9 | 108 | 0 |
| `sret-xback` | 1 | 12 | 0 |
| families: integer | 20 | 240 | 0 |
| float | 6 | 72 | 0 |
| hfa | 23 | 240 | 36 |
| hva | 15 | 72 | 108 |
| composite | 13 | 124 | 32 |
| i128 | 6 | 72 | 0 |
| sret | 10 | 120 | 0 |
| byref | 8 | 96 | 0 |
| bool | 6 | 72 | 0 |
| varargs | 20 | 36 | 204 |
| callback | 8 | 72 | 24 |
| exhaustion | 12 | 144 | 0 |
| spill | 6 | 60 | 12 |
| overalign | 95 | 868 | 272 |
| packed | 16 | 108 | 84 |
| union | 16 | 164 | 28 |
| enum | 14 | 144 | 24 |
| niche | 12 | 144 | 0 |
| random (seeded mixed) | 40 | 480 | 0 |
| **total** | **396** | **3,928** | **824** |

Against the lane record at `217946d09` only `varargs` moved, by the nine
cases this round added: `va_none_c` and `va_ptr_none_c` (a direct call and a
call through a C-variadic `fn` pointer, no anonymous argument) match in their
eight trust-cg-caller cells; the over-aligned and `{u64, u64}` fixed
arguments through a pointer and the pointer call with anonymous arguments
are refused by name (100 cells). The 117 rows of that record became 133:
sixteen for the new cases, and the callee rows of five direct over-aligned
cases carry the definition refusals instead of `[TCG-ARG-ABI]` (LD-29,
below). Every other count is unchanged.

Against the record before it (`8df585cd2`), the previous round had moved two
families by seven cases: `varargs` gained six cases with over-aligned fixed
arguments, and `spill` gained `spill_all_exec_c`, the thirty-two arguments of
`spill_all_c` with its three refused shapes (`float32x4_t`, the two-vector
HVA `V2`, `MixF`) replaced by executable ones of the same bank (`H2d`, `H4d`,
`G12`), which matches in all 12 of its cells. Its mixed composites (`H2f`,
`A8`, `G3`, `H3d`, `A16`, `H4f`, `S3`, `B7`, `H1d`, and the `i128`/`u128`
pair) run in one signature, most of them on the stack.

The five layout families are new in this record: over-aligned composites with
`#[repr(align(N))]` for N from 2 to 64 under both ABIs (two 16-aligned shapes
per ABI at every NGRN 0–7 and on the stack at NSAA 0 and 8; every other shape
in registers, on the stack and as a result; nested both ways), `packed` and
`packed(2)` composites, unions, payload enums and niche-carrying scalars; their
149 oracles at O0 were first checked against the generator by hand-built LLVM
pairs. Also new: a fat pointer really split across x7 (data) and the stack
(length), `byref_fat_split_rust`, which matches. Every case keeps ten `u64` and
eight `f64` live across its call; where they live is each compiler's choice.

## The over-aligned arguments

AAPCS64 places a composite of at most 16 bytes by the alignment of its
most-aligned member, and rustc's Linux `FnAbi` casts `#[repr(C, align(16))]
struct { u64, u64 }` (and `{ u64 }`, `{ u32 }`, `{ u8 }`, `{ u32, u32, u32 }`)
to `[2 x i64]`. On `395954590` (backend SHA-256 `441f7005…`, the same runner
and families) the bridge's whole-signature placement check refused those
declarations by name wherever its own placement differed (an odd NGRN, an NSAA
of 8 mod 16) and refused the padded scalar newtypes at every position: the 149
layout-family cases gave no wrong value and no crash, 1,164 of 1,788 cross
cells matched, 624 declined in 103 rows; the `overalign` family's first 91
cases matched 604 cells and declined 488. The first review's wrong values do
not reproduce there: `al16-pair` and `al16-u32` are refused at O0–O3 (trust-cg
callee and caller). The bridge now declares such an argument as rustc's two
`I64` units (`aapcs64_unadjusted_block_plan`, `Aapcs64ScalarBlock`; LD-28):
the same 91 cases match 820 cells and decline 272, the four NSAA-8 cases added
since match all 48 of theirs, and on the `8df585cd2` lane's backend both
reproducers print the right values in all four pairings at O0–O3 (16 of 16
executions each). The required aggregate target's `overaligned_c_arguments`
test (14 calls: x1/x3/x5, the stack with one register left and at NSAA 8,
padded `u8`/`u32`/`u64` newtypes, `{u32, u32, u32}`, a nested 4-aligned
member, a result, a C `fn` pointer and a C callback) prints the values
computed in the test in all 16 executions, and pins the remaining refusals;
against the `395954590` backend it fails because the bridge refuses 11 of its
14 callee functions.

### As fixed arguments of a C-variadic function (LD-29)

`check_signature_placement` returned before judging any C-variadic signature,
and on that route the two-unit declaration is withdrawn (the aggregate ABI
scope refuses every carrier of a variadic signature). A padded scalar newtype
passed as a fixed argument of an LLVM-built variadic function therefore kept
its scalar declaration, and nothing compared where it landed: the review's
`va-fixed` caller put the scalar in x1 and `p2` in x2, where rustc's `FnAbi`
has `[2 x i64]` in x1:x2 and `p2` in x3. Reproduced here on the review's
backend from `24723c172` (SHA-256 `a56d61ec…`): `exit 1 out '1020400
135247732'` at O0 and at O3 for the trust-cg caller and LLVM callee.

The same holds through a C-variadic `fn` pointer when the call passes NO
anonymous argument: such a call has as many arguments as the pointer has
inputs, so it takes the ordinary `fn`-pointer route rather than the
argument-count refusal (the bridge's own `call_pointer_empty` test passes
nothing anonymous through a `fn(u32, ...)` pointer). The third review's
[`va-pointer/`](va-pointer/) caller calls an LLVM-built `va_pad_u64(u64,
Oa16U64, u64, ...)` that way; on `395954590`'s backend (`441f7005…`) the
trust-cg caller prints `10200` at O0 and an unrelated value at O1–O3
(`202928406327816` at O1 in this run) for `10203`, exit 1 each time.

The first fix (`217946d09`) judged every C-variadic declaration on its fixed
arguments AND every Linux AArch64 variadic call whole; the declaration's
check ran first and refused everything the whole-call check would have, so
the latter never fired. Since `e15ffc0ea` each code-emitting use is judged
once (LD-29 as amended):

- a direct call on the Linux AArch64 variadic call lane is judged whole
  against the call-site `FnAbi` (`variadic::call`): the declaration's fixed
  values as `classify_func_ty` recorded them, then one declared value per
  anonymous argument, under the base AAPCS64 variant only. That lane's
  declaration is no longer judged alone: its calls are its only
  code-emitting use (the native adapter refuses every variadic definition,
  and a `fn` pointer to it is judged as its own signature);
- a C-variadic `fn` pointer signature (and an instance on a target without
  the lane) is judged on its fixed arguments; a pointer call that passes
  anonymous arguments stays refused by its argument count.

On this change's backend (built from `e15ffc0ea` in the branch worktree,
SHA-256 `1d862d6f…`):

- `va-fixed` and `va-pointer`: the trust-cg caller is refused at O0–O3,
  `[TCG-ARG-ABI] the C-variadic call of va_pad_u64: argument 1
  vapad::Oa16U64 ...` and `[TCG-ARG-ABI] the fn pointer signature unsafe
  extern "C" fn(u64, vapad::Oa16U64, u64, ...) -> u64: argument 1 ...`
  respectively, each `byte 8 is passed in integer argument register 2 byte 0
  by rustc's FnAbi but in no home at all by the bridge's declaration [I64]`;
  the LLVM pairs print `1020304 1020304` and `10203`.
- The `varargs` family has 20 cases (nine added in this round). Every
  over-aligned fixed argument is refused on the trust-cg CALLER at O0–O3,
  directly (`va_oa16u64_x1_c`, `va_oa16u8_x1_c`, `va_oa2_x1_c`,
  `va_oawrap16_x1_c`, `va_oawrap16_s8_c`: the whole-call check) and through
  a `fn` pointer with no anonymous argument (`va_ptr_*` twins: the pointer
  signature's check), all `[TCG-ARG-ABI]`; `{u64, u64}` by the aggregate
  scope both ways. `va_ptr_anon_c` (anonymous arguments through a pointer)
  is refused by its argument count. A direct call and a pointer call with
  no anonymous argument and ordinary fixed arguments (`va_none_c`,
  `va_ptr_none_c`) execute and match, as do the five scalar-argument cases.
  The trust-cg DEFINITIONS of these callees are refused as variadic
  definitions (`[TCG-VARIADIC-DEFINITION]`, or the inlined `va_arg`
  intrinsic at O2/O3 where the definition reads an anonymous argument), and
  those of the 16-aligned-member wrapper as the `Place projection` that
  reads it. Before this change the placement check refused the over-aligned
  definitions first (`[TCG-ARG-ABI]`); their callee rows in the table now
  carry the definition refusals instead.
- On `395954590`'s backend the same 20 cases give 32 wrong values (no
  crash): `{u64}`, `{u8}`, the wrapper at x1 and the wrapper on the stack, each
  at O0–O3, directly and through the pointer; `align(2) {u8}` matches both
  ways only because its callee reads byte 0 of rustc's one-integer cast.
- The aggregate target's `overaligned_c_arguments` refusal fixture holds the
  direct caller (`oa_va_fixed_x1`) and the zero-anonymous pointer caller
  (`oa_va_pointer_x1`), and asserts both checks by name. `395954590`'s
  backend compiles both callers; `217946d09`'s (its lane snapshot,
  `84f15fbf…`) refuses both but never through the call-site check (the new
  needle `the C-variadic call of xoa_va_pad_u64: argument 1` is absent at
  O0–O3).
- Mutants, each an edit of one statement of `e15ffc0ea`, built like the lane:
  M1 deletes the call-site check in `variadic::call`
  (`e9980922…`), M3 returns before judging a C-variadic `fn`-pointer
  signature (`285b46ff…`), M2 returns before judging any C-variadic
  instance or pointer signature (`0c9c4bd0…`). Each fails the refusal
  fixture at O0–O3 (M1: no `oa_va_fixed_x1` refusal and no call-site
  needle; M3, M2: no `oa_va_pointer_x1` refusal) and the runner's `varargs_c`
  group with 16 wrong values (M1: the four direct over-aligned shapes at
  O0–O3; M3, M2: their four pointer twins).
- M5 ([`variadic-m5-mutant.patch`](variadic-m5-mutant.patch), the landing
  verifier's round-3 residual) runs the whole-call check only for a call that
  passes an anonymous argument. Nothing committed at `e15ffc0ea` caught it: a
  DIRECT call with no anonymous argument and an over-aligned fixed argument
  had no test. Since 2026-10-15 the aggregate target's
  `no_proof_overaligned_variadic_fixed_argument_without_anonymous_refuses_or_matches_llvm`
  makes that call (`overaligned_c_arguments/variadic_caller.rs`) and requires
  the call-site refusal by name or LLVM's value. On the landing batch's
  release backend it passes with 4 refusals (`6729198b…`); with M5
  (`bd9e2f59…`) `no_proof_overaligned_c_arguments_match_llvm` still passes
  and the new test fails at O0 on a wrong value (`…4432ef` for LLVM's
  `…446622`). Decision record LD-29.
- Admitted variadic code is unchanged: the `residual_conversion` variadic
  call and mutation fixtures compile to byte-identical objects at O0 and O2
  under `217946d09`'s lane backend and this change's, and its other seven
  variadic fixtures, compiled the same way (`--crate-type=lib --emit=obj`,
  `-Cpanic=abort`), refuse with the same tags under both.
- [`variadic-negative-control.patch`](variadic-negative-control.patch), the
  planted error recorded for `217946d09` (every anonymous argument declared
  an `f64`), rewrote the check's own input, so it showed only that the
  comparison runs, not that it catches a placement the lowering produces;
  the mutants above are the evidence now.

## The refusals

All at O0–O3. A `callee` row means the trust-cg-compiled callee crate refuses
(cells llvm×tcg and tcg×tcg); a `caller` row, the trust-cg-compiled caller
(cell tcg×llvm, plus tcg×tcg where the callee compiles). `[TCG-MIR-UNSUPPORTED]`
wraps every one. The runner's `EXPECTED_DECLINES` table holds exactly these
rows, with their reasons.

| case(s) | side | tag | what is refused |
| --- | --- | --- | --- |
| `hva_args_c`, `hva_after7_c`, `hva_ret_v1_c`, `hva_spill_c`, `vec_bare_c`, `spill_all_c` | both | `[TCG-SYSV-SSE-AGGREGATE]` | a C-ABI 128-bit vector, bare or as a one-member HVA (`spill_all_c` also holds a two-vector HVA and `MixF`; `spill_all_exec_c` runs its other shapes) |
| `vec64_bare_c` / `vec64_ret_c` | both | `[TCG-ARG-ABI]` / `[TCG-RET-ABI]` | a C-ABI bare 64-bit vector argument / result |
| `hva_vs2_arg_c` / `hva_ret_vs2_c` | both | `[TCG-ARG-ABI]` / `[TCG-RET-ABI]` | a C-ABI argument / result of two 64-bit vectors |
| `hfa_args_rust`, `hfa_after_full_rust`, `hfa_stack_align_rust` | both | `[TCG-ARG-ABI]` | a Rust-ABI one-`f32`/`f64` struct, which rustc casts to a GPR |
| `comp_small_c` | both | `[TCG-ARG-ABI]` | C-ABI `{f32, f64}` (16 bytes, two integer lanes) |
| `comp_mixfi_c` | callee | `[TCG-FIELD-STORE-TYPE]` (`[TCG-IR-LOWER]` before main's WS7.3 repairs) | a C-ABI `{f64, u64}` definition (a trust-cg caller of it matches) |
| `comp_a16_at_x5_rust` | both | `[TCG-RET-ABI]` | a Rust-ABI `A16 { i128 }` result (x8 buffer) |
| `cb_hfa_rust` | callee | `[TCG-RET-ABI]` | a Rust-ABI 12-byte `H3f` result of a `fn`-pointer callback |
| `cb_sret_c`, `cb_sret_rust` | callee | `[TCG-SRET-ABI]`, `[TCG-RET-ABI]` | an x8 result through a `fn` pointer (no callee symbol) |
| `va_ints_regs_c`, `va_ints_stack_c`, `va_f64_c`, `va_after_fixed_c`, `va_oa16u64_x1_c`, `va_oa16u8_x1_c`, `va_oa2_x1_c`, `va_ptr_anon_c` | callee | `[TCG-IR-LOWER]` at O0/O1 (trust-ir's `EntryParamsMismatch` since WS7.3; the adapter's `[TCG-VARIADIC-DEFINITION]` before it); only the wrapper at O2/O3 | a C-variadic definition (at O2/O3 the inlined `va_arg` intrinsic) |
| `va_none_c`, `va_ptr_none_c`, `va_ptr_oa16u64_x1_c`, `va_ptr_oa16u8_x1_c`, `va_ptr_oa2_x1_c` | callee | `[TCG-IR-LOWER]` (as above) | a C-variadic definition that reads no anonymous argument (refused as such at every level) |
| `va_oawrap16_x1_c`, `va_oawrap16_s8_c`, `va_ptr_oawrap16_x1_c`, `va_ptr_oawrap16_s8_c` | callee | wrapper only | a C-variadic definition reading the scalar of its 16-aligned-member wrapper (`Place projection`) |
| `va_oa16u64_x1_c`, `va_oa16u8_x1_c`, `va_oa2_x1_c`, `va_oawrap16_x1_c`, `va_oawrap16_s8_c` | caller | `[TCG-ARG-ABI]` | an over-aligned scalar newtype or 16-aligned-member wrapper as a FIXED argument of a direct C-variadic call (the whole-call check, LD-29) |
| `va_ptr_oa16u64_x1_c`, `va_ptr_oa16u8_x1_c`, `va_ptr_oa2_x1_c`, `va_ptr_oawrap16_x1_c`, `va_ptr_oawrap16_s8_c` | caller | `[TCG-ARG-ABI]` | the same through a C-variadic `fn` pointer with no anonymous argument (the pointer signature's check, LD-29) |
| `va_ptr_anon_c` | caller | wrapper only | anonymous arguments through a C-variadic `fn` pointer (`argument count 3 does not match callee input count 1`) |
| `va_oa16_x1_c`, `va_ptr_oa16_x1_c` | both | `[TCG-AGGREGATE-ABI-SCOPE]` | a `#[repr(C, align(16))] {u64, u64}` fixed argument of a C-variadic function, directly or through a `fn` pointer |
| eight `ov_oa16f64x2*`, `ov_oawraphfa_c`, `ov_ret_oa16f64x2_c` | both | `[TCG-AAPCS64-HFA]` | an over-aligned HFA, argument or result |
| `pa_pkf_c`, `pa_ret_pkf_c` | both | `[TCG-AAPCS64-HFA]` | a packed `{f32, f32}` HFA |
| `ov_oa2_c`, `ov_oa8_c`, `ov_oa2_rust`, `ov_roa4u16_rust` | both | `[TCG-ARG-ABI]` | a padded scalar newtype of at most 8 bytes, which rustc casts to one integer |
| `ov_oawrap16_c` | both | `[TCG-ARG-ABI]` | a repr(C) struct around a 16-aligned member, which rustc casts to `i128` |
| `ov_oa32_c` / `ov_ret_oa32_c`, `ov_ret_roa16u32_rust`, `ov_ret_roa32_rust` | both | `[TCG-ARG-ABI]` / `[TCG-RET-ABI]` | a padded scalar newtype rustc passes or returns through a copy |
| `ov_oa32f32x4_c`, `ov_oa64_c`, `ov_oa64_rust` | both | wrapper only | a 32- or 64-aligned composite (no memory slot of that alignment) |
| `ov_oawrap8_c` | both | wrapper only | a struct holding an over-aligned `{u16}` member |
| `ov_oawrap16_rust` | callee | wrapper only | `Place projection` reading a nested over-aligned newtype |
| `ov_ret_oa16f32x2_c` | both | `[TCG-SYSV-SSE-AGGREGATE]` | a C-ABI over-aligned `{f32, f32}` result (as an argument it matches) |
| `pa_pk_c`, `pa_pk2_c`, `pa_pkbig_c`, `pa_ret_pk_c`, `pa_ret_pk2_c` | both | `[TCG-SYSV-PACKED-AGGREGATE]` | a C-ABI packed composite with a misaligned field |
| `un_unmix_c` | both | `[TCG-SYSV-MIXED-UNION]` | a C-ABI `union { u64, f64 }` |
| `un_ret_runint_rust`, `un_ret_unsmall_c` | caller | wrapper only | a union result with members of different types, received by a trust-cg caller |
| `en_ecr32_c`, `en_ret_ecr32_c` | both | `[TCG-SYSV-SSE-AGGREGATE]` | a C-ABI `repr(C, u32)` enum with an `f32` payload |

Each shape that a refusal used to hide inside another case is now a case of
its own (`vec64_*`, `hva_vs2_arg_c`, `comp_mixfi_c`) or runs in an executable
twin (`spill_all_exec_c`); the two-vector HVA argument inside `spill_all_c`
executes nowhere (every HVA argument is refused, `hva_args_c`). What executes
beside the refusals is listed in the
[generator README](../../../benchmarks/abi-xback/README.md).

## Negative control

[`negative-control.patch`](negative-control.patch) makes
`AArch64AbiVariant::from_target_triple` select DarwinPCS for ELF triples (the
historical Linux stack-slot bug). Its backend (SHA-256 `1558bde3…`, built from
`0543a5979` plus the patch with the lane's command) run through the runner at
`8df585cd2` (`--jobs 2`) fails it with **561 wrong values and 92 crashes** in
81 cases: 533 wrong and 92 crashed matrix cells (320 in trust-cg caller × LLVM
callee, 301 in LLVM caller × trust-cg callee, 4 trust-cg × trust-cg: the
`snprintf` calls into glibc) and 28 wrong cells of superseded group attempts
(in `varargs_c`, `callback_c`, `callback_rust`; each also wrong in its
per-case cell). `abi-xback` matches only 232 of its 480 cross cells; regclass
and sret, which put nothing on the stack, still match. It also reports 34
unlisted refusal rows in 17 cases (the two-unit declaration is an AAPCS64-only
plan, so under the planted variant 14 over-aligned cases are refused by name
again, as are two niche and one union case whose stack placement the planted
rules change) and misses both executed-match floors. It was not re-run after
`8df585cd2`. The variadic mutants of LD-29 are above.

## Inside the required bridge lane

`python3 -B scripts/check_linux_aarch64_bridge.py --out <new dir> --target-dir
<cache> --jobs 4 --timeout-seconds 10800` at `e15ffc0ea`, from a clean
detached worktree of that commit (source fingerprint `2d23f2a6ebc6…`,
unchanged from start to end), 2026-10-15 06:19:57Z to 08:43:11Z, with other
gate runs sharing the host. (A first attempt from the branch worktree stopped
after the build, `source changed during bridge qualification`, because this
README was being edited there.) The lane rebuilt the backend (SHA-256
`9a606eab2a64…`, 140,387,456 bytes) and ran its six native targets, then this
runner on the same read-only snapshot, 08:11:02Z to 08:43:06Z (5,040
compiles, 6,332 executions). **The cross-backend step passed** with the result
above; the lane re-derived that verdict from the cells and bound it to the
snapshot hash and its `trustc`. The TLS, unwind, panic-hook, trap-stub and
scalar-ZST targets passed.

The lane's overall verdict is **FAIL** for the C aggregate target,
`aarch64_c_fnabi_aggregate_linux` (5,521 s with one test thread, under the
10,800 s bound): 125 of its 130 tests passed, among them
`overaligned_c_arguments` (16 executions, 4 refusals, with the new pointer
caller and needles) and the five `residual_conversion` variadic tests (the
scalar, reference and pointer-mutation call matrices against C, and two
refusal tests). The five failures are exactly the five this target already
has on `origin/main` at `6fe8c91a1`:
`c_fnabi_hfa_all_members_both_directions_and_llvm_twin` (`aliased_f32_read`,
L06-P1), `linux_relocations`,
`residual_conversion::no_proof_fat_fn_arguments_keep_callee_refusal`,
`trait_upcasts` and `tuple_memory_elements`.

The lane record at `217946d09` (backend `84f15fbf…`, 2026-10-15 02:43:41Z to
05:05:27Z) passed the same step with 387 cases (3,920 of 4,644 cross cells
matched, 724 declined in 117 rows, 784 superseded-attempt cells judged), and
its aggregate target failed the same five tests of 130 (5,855 s).

The lane record before it, at `8df585cd2` (backend `3c2f09f0…`, 2026-10-14
23:16:27Z to 2026-10-15 01:10:36Z), passed the same step with 380 cases
(3,908 of 4,560 cross cells matched, 652 declined in 105 rows, 776
superseded-attempt cells judged); its aggregate target hit a 3,600 s bound with
59 of 130 tests started, and a separate run of that executable passed 124 of
130 (the five known failures and one O3 run that hit its 20 s bound under load
and passed alone).

## Identities

- Source: branch `feat/l06p9-linux-cross-backend-abi-landed` on
  `395954590`; the lane ran at `e15ffc0ea`; this README's update, the
  `va-pointer/` reproducer and the documentation (decision record,
  LIMITATIONS, the completion document, the generator README) were added
  after it.
- Compiler: Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb` (`rustc 1.99.0-dev
  (ae9c2c1da 2026-09-21) (trustc 0.1.0)`, LLVM 22.1.2) at
  `/home/ayates/toolchains/trust-ae9c2c1d`, `trustc` SHA-256
  `b2d4fa4bb1ce8106539d7c2967f1eb3f3f613293b8c905de586fbb4f5ffa4212`, in its
  explicit unverified frontend lane (`-Ztrust-verify=off`).
- Backends (`targo --unverified build --release --locked`, `RUSTC` that
  `trustc`; hashes identified, not archived): the lane's
  `9a606eab2a6464c2e781dd497ffce5c29cba16453d21ac65a0d96182dd981337`
  (`e15ffc0ea`); the same sources built in the branch worktree, used for the
  LD-29 measurements above,
  `1d862d6f29ae77409eeb501123a9c4b8def20bee2a11e0eb24146526a531a06b`; the
  mutants M1
  `e9980922104b4ff9e6be2274bf410073f204cea2215a286391608ad904ced94a`, M3
  `285b46ffffd442f2be50ff9369c5a1134d669ff5a0944addfe6ff47dd342a31e` and M2
  `0c9c4bd03520a2c457a3b4d79accc4c3e8112702386af17c586cacb167a8daac`; the
  `217946d09` lane's
  `84f15fbff5fb6520f80454a58561e93ae93d072ad0d2b5c1bf11c676af688cb5`; the
  `8df585cd2` lane's
  `3c2f09f056ee64670dae6eba185b43204eab8f545321396b1b72287553509c04`
  (`8df585cd2`); the review's
  `a56d61eca94cc3fd84e5c5e633647b0f2e41752f78e6a795afb51386452d9c23`
  (`24723c172`); before the change (`395954590`)
  `441f70057cb50728b08daec549e16c8e7b720cdd44b791006c24c99cb5e2ce5b`; the
  DarwinPCS negative control
  `1558bde39d78ac8f3cb8ed9f78d2ebcb51912784ec3c27c84a5b315a450a93c7`; the
  `217946d09` round's variadic negative control (its patch on that round's
  bridge sources before a doc-comment edit)
  `e065165a4f9c7161150c0012516edcac83a466c3e789d2c638d1a2be5f976469`.
  Trust-cg halves pass `-Ztrust-ir-cg-args=no-proof-certs
  -Ztrust-ir-cg-args=refine-solver=0`.
- Host: `aarch64-unknown-linux-gnu`, Linux 6.17.0-1026-nvidia, Ubuntu 24.04.4,
  `lscpu` Cortex-X925/Cortex-A725; `trustc` links with `cc` (GCC 13.3.0, GNU ld
  2.42).
- Unit suites: `scripts/tests/test_linux_aarch64_xback.py` (35 tests) and
  `scripts/tests/test_linux_aarch64_bridge_gate.py` (39) pass at `e15ffc0ea`;
  they use
  stand-ins for `trustc`, Cargo and the runner and establish the result
  contract only. Mutation passes over the runner, each mutation against
  `test_linux_aarch64_xback.py`: of the first review's 30, three re-spelled
  where the refactor moved their code, M05 is gone with the row-level tag
  comparison the per-cell one replaced, and only the equivalent M26 survives (a
  timed-out run is killed and is a crash under either label); 8 mutations of
  the group-attempt and per-level tag checks are caught; all 27 of the second
  review's (V01–V27, its own harness pointed at this change's runner) are
  caught, V13, V20 and V21 by three new tests (a stand-in compiler whose
  trust-cg CALLER refuses one case of a group; group-mode matrix rows that are
  no rebuild; a group refusal whose tags are the union of two cases' per-case
  refusals).

```sh
python3 scripts/check_linux_aarch64_xback.py --backend <backend.so> --out <new dir> --jobs 4
python3 -B scripts/check_linux_aarch64_bridge.py --out <new dir> --target-dir <cache> --jobs 4 --timeout-seconds 10800
python3 -m unittest scripts/tests/test_linux_aarch64_xback.py scripts/tests/test_linux_aarch64_bridge_gate.py
python3 pair4.py al16-pair <backend.so> 0,1,2,3     # PATH trustc: the pinned Trust compiler
python3 pair4.py va-fixed <backend.so> 0,1,2,3      # the trust-cg caller must be refused
python3 pair4.py va-pointer <backend.so> 0,1,2,3    # likewise, through a C-variadic fn pointer
python3 scripts/check_linux_aarch64_xback.py --backend <backend.so> --out <new dir> --jobs 4 \
  --suites abi-families --groups varargs_c          # development subset (the mutants' runs)
```

## The manual runners on this host

`benchmarks/regclass-xback/run.sh` and `benchmarks/sret-xback/run.sh` pass no
backend knob, so their trust-cg halves compile with proof certificates on. At
O0 (backend `d7ca892e…`, the first port's bridge sources before formatting)
every trust-cg compile they attempt is refused at proof promotion
(`[TCG-PROOF-465]`, the L07-P2 opcode-inventory wall): regclass reports 18
failures and no executed cross cell, sret 4 failures. Their programs execute
in the required runner.

## Boundary

- One host, one compiler, the generated domain. No Darwin runner exists for
  these suites; `run.sh` alone has a Darwin record, and the over-aligned
  two-unit declaration is not active on Darwin (adjusted alignment). Darwin
  and x86-64 have no variadic call lane; their variadic declarations are now
  judged on their fixed arguments, unmeasured on those hosts.
- Proof certificates off. A certificates-on build of these crates is not
  measured here.
- Each listed refusal is unsupported surface that must stay refused until it
  is implemented and measured across the boundary; none is accepted ABI.
- Floating-point callee-saved registers are exercised only where a compiler
  happens to keep one of the eight live `f64` in d8–d15; nothing forces it.
- `f16`, `f128`, SVE, `extern "C-unwind"` and unwinding across the boundary,
  and `dyn` calls are outside this domain (some have their own bridge targets).
- Logs, generated sources, binaries and the JSON reports stay out of tree.
