# Darwin x86-64 body theorem: OD-210's residuals (OD-216 to OD-218), 2026-10-27

Ruling OD-210 (the hostile review of slice 22, [slice-22 report
§8](../2026-10-27-darwin-x86-64-slice22-i128-division/README.md#8-the-hostile-review-od-210-od-211-and-three-controls))
refuses an x86-64 body theorem whose `I128` division calls a runtime routine
(`__udivti3`, `__divti3`, `__umodti3`, `__modti3`) that the function under
proof is, or that "the module" defines. It recorded two residuals, closed
here on branch `fix/x86-body-od210-crate` (worktree
`~/tcg-scratch/wt-od210c`, from main `4bf54e061`):

| Ruling | Residual | Rule |
| --- | --- | --- |
| OD-216 | the module is one compile unit, not the crate | the rustc bridge names every trusted routine any codegen unit of the crate defines (the symbols of rustc's mono items) to every module it compiles; the verifier refuses a routine the link unit defines (`TheLinkUnit`) |
| OD-217 | slice 13's C memory routines are the same kind of trust | `memcpy`, `memmove`, `memset` (LIR `Memcpy`/`Memmove`/`Memset`) are guarded like the division routines |
| OD-218 | a pass that rewrites code into a call of one | the x86-64 vectorizer's fill tier never routes a fill inside `memset` itself to `memset` |

Host: the shared x86_64 Mac (4 cores, Darwin 22.6, macOS 13.7.8 22H730).
Builds through `scripts/trust_cargo.sh` with the `x86-stage1-ay13556`
overlay (`targo --unverified`, `nice -n 19`, `-j2`, `build-slot`; no proof
claim about any build); bridges with `~/tcg-scratch/build_bridge.sh`
(release, the `x86-stage0-bridge-ay13556` overlay). Replayer pair: AY 0.27.0
build 13556 with Clean 5f09e36c. Payloads are out of tree;
[PAYLOADS.md](PAYLOADS.md) binds each by size and SHA-256.

## Soundness notes first

- **A promoted false credit on main (residual 2, live).** Through the
  census's lane (proofs required, O0, one codegen unit), a crate that
  defines `#[unsafe(no_mangle)] unsafe extern "C" fn memcpy(dest, src, n)
  -> *mut c_void { dest }` (it copies nothing) beside
  `ptr::copy_nonoverlapping` compiles and **promotes** on main: the generic
  `copy_nonoverlapping::<u8>`'s body theorem (an LIR `Memcpy`, the call of
  the crate's own `memcpy`) replays Valid and its 21 rows are credited
  Formal, in the crate's one object (`crates/copy_split.rs`, §1). The same
  holds for a crate's `memmove` that copies through `ptr::copy`, which
  calls itself (`copy_self.rs`). OD-217 refuses both.
- **OD-210's "always with `-C codegen-units=1`" did not hold.** With one
  codegen unit the bridge compiled the review's crate as one merged module,
  OD-210 refused `div` there, the merged compile failed, and the bridge's
  per-function fallback compiled `div` alone: its module does not define
  `__udivti3`, so the theorem replayed Valid and 36 rows were credited
  Formal. With `-C codegen-units=16` (the two items in two units) `div` was
  credited outright. In both, only the bridge's refusal to compose several
  objects under proofs (`[TCG-OBJECT-COMPOSITION-PROOF]`) kept the crate
  from promoting: the per-function credit (what the census and the
  certificate bundle count) was false, the object was not shipped. OD-216
  names the crate's definitions to every module the bridge compiles,
  merged, per codegen unit or per function. OD-210 carries an "Amended"
  line.
- **Main's bridge did not build.** `590b9f398` added
  `X86PipelineError::FunctionLinkageUnsupported` without the bridge's
  exhaustive classifier arm (E0004; the bridge is a workspace the root
  checks do not build). This branch adds the arm (an Object refusal, as its
  visibility sibling) and a classifier test; the baseline bridge of §1 is
  main `4bf54e061` with that one arm, no other change. The identical
  change has since landed on main from a parallel lane (`fc6681945`); this
  branch's merge of it changes no byte.
- No other soundness concern found: the vectorizer's `memset` rewrite is
  never credited (§3), and `core` defines none of the names (§4).

## 1. OD-216: the crate's definitions reach the verifier

**Where the module is.** OD-210 reads the definitions of the trust-ir
module the compiler lowers. The rustc bridge's module is one codegen unit
(CT-BATCH merges a unit's merge-eligible functions), or one function of one:
a merge-ineligible function, every function of a unit whose merged compile
failed (the per-function fallback), and every function under `batch-cgu=0`.
A crate's routine in any other module binds the call unseen.

**How the crate's definitions reach the verifier.** Of the three ways to
get them (rustc's `exported_symbols(LOCAL_CRATE)`, the mono items of every
codegen unit, a per-crate pre-pass over attributes), the mono items are the
exact one: the bridge emits a function or static definition only for a mono
item of rustc's partition, under the mono item's symbol name (the
`#[no_mangle]` name or the `#[export_name]` value verbatim), and rustc's
collector makes every non-generic item with such an attribute a root
(`RootCollector::is_root`: every item when eager; `is_reachable_non_generic`
when lazy, which an item with an extern indicator satisfies), so every such
definition the crate's objects carry is a mono item of some unit.
`exported_symbols` is no superset (it leaves out what rustc does not
export), and a pre-pass would re-derive the partition. The backend's own
modules define none of the routine names; a `global_asm!` block (the crate
is refused, `[TCG-GLOBAL-ASM]`) counts as all of them; a CGU-private copy
the bridge renames and a declared static count under their rustc names,
which only refuses more.

`crate_trusted_routine_definitions` keeps the trusted routines among those
names (`X86ModuleDefinitions::trusted_routine`), `codegen_crate` publishes
them before its first module compile (`CRATE_ROUTINE_DEFINITIONS`, keyed by
the `StableCrateId`), and every native module compile sets them as
`CompilerConfig::link_unit_definitions`. The compiler unions them into the
module's definitions (`X86ModuleDefinitions::with_link_unit`) in the AOT
lane and the JIT; a routine only the rest of the link unit defines is
refused as `X86RoutineDefinition::TheLinkUnit`. The set is verifier input
(a `link_unit routines=[..]` part of the x86 input line, only where it can
change a verdict), a compile-artifact cache field and an Evidence field of
the compile policy, each only when non-empty, so every existing digest is
unchanged; the closed-JIT Core proof-grade boundary refuses a non-empty set
like every other non-default control. `x86-body-trace` names a non-empty
set once per crate. The `dump-trust-ir` sidecar records it and
`compile_corpus` replays it.

**Fails before, refused after** (`run_crates.sh`, the census's lane: the
`x86-stage1-ay13556` trustc, O0, `panic=abort`, proofs required, AY 13556 +
Clean 5f09e36c). Before: main `4bf54e061` with only the bridge's classifier
arm (bridge `a52dc3b0…`). After: this branch (`c5e2ae5e0`, bridge `c08fd2fe…`).

| Crate (`crates/`) | Units | Function | Before (main) | After (this branch) |
| --- | ---: | --- | --- | --- |
| `div_split` | 16 (`div` in `cgu.0`, `__udivti3` in `cgu.1`) | `div` | `bound rows=36 replay=Valid`: **credited Formal**; crate refused only by `[TCG-OBJECT-COMPOSITION-PROOF]` (two objects) | refused, `TheLinkUnit` ("another compile unit of its link unit (crate) defines it"); crate refused naming `div` (`[TCG-PROOF-465]`) |
| `div_split` | 1 | `div` | merged module: refused (`TheModule`, OD-210); the merged compile failed, the per-function fallback compiled `div` alone: `bound rows=36 replay=Valid`, **credited Formal**; crate refused only by the object-composition refusal | merged: `TheModule`; fallback: `TheLinkUnit`; crate refused naming `div` |
| `div_declared` | 16 / 1 | `div` | `bound rows=36 replay=Valid` | the same (the control keeps its credit); at one unit the crate promotes through both bridges (exit 0) |
| `copy_split` | 1 (one object) | `copy_nonoverlapping::<u8>` (an LIR `Memcpy`) | `bound rows=21 replay=Valid`, **credited Formal, the crate promoted** (exit 0) with a `memcpy` that copies nothing | refused, `TheModule` (merged) and `TheLinkUnit` (fallback); crate refused naming it |
| `copy_split` | 16 | `copy_nonoverlapping::<u8>` | `bound rows=21 replay=Valid`, credited; crate refused only by the object-composition refusal | refused, `TheLinkUnit`; crate refused naming it |
| `copy_declared` | 16 / 1 | `copy_nonoverlapping::<u8>` | `bound rows=21 replay=Valid` | the same; at one unit the crate promotes through both bridges (exit 0; at 16 units both refuse only for the object composition) |
| `copy_self` | 1 (one object) | `copy::<u8>` (an LIR `Memmove`), which the crate's `memmove` calls | `bound rows=23 replay=Valid`, **credited, the crate promoted** (a `memmove` that calls itself through `copy::<u8>`) | refused, `TheModule` and `TheLinkUnit`; crate refused |

The placement is rustc's (`-Zprint-mono-items`, in each case's
`stdout.log`); the after-bridge names each crate's set once
(`[TCG-X86-BODY-TRACE] crate=div_split defines trusted runtime routines
{"__udivti3"}`, and `{"memcpy"}`, `{"memmove"}`); the `__udivti3`,
`memcpy` and `memmove` definitions themselves keep their theorems (no call
of a routine in their bodies).

**Below the bridge** (solver-free, `trust-cg-verify` and
`trust-cg-codegen`): `slice22::a_routine_another_unit_of_the_crate_defines_
is_never_trusted` (the module alone builds the theorem; the link unit's
`__udivti3` refuses it as `TheLinkUnit`; another routine, or a name that
is no routine, changes nothing; the module's own stays `TheModule`);
`function_request::tests::request_input_identity_covers_operands_nan_
payloads_and_exact_lir` (the link-unit state is its own digest; a link unit
of no relevant routine keeps the old one); codegen
`x86_body_trace_names_a_routine_the_crate_defines` (the AOT lane: alone,
the division's and the copy's theorems are built; in a link unit that
defines the routine, refused by name, `OD-216`); `compile_policy::tests::
link_unit_definitions_is_an_evidence_field_only_when_non_empty`,
`compiler::tests::compile_artifact_cache_identity_binds_explicit_behavior_
controls` and `proof_grade_core_jit_rejects_every_policy_drift_and_
recovers_exact_plan`. With the replay tools: codegen `a_call_of_a_routine_
the_crate_defines_never_promotes` (alone, Formal; in a crate that defines
the routine, the compile is refused naming the function), and
`slice13_qualification::verifier_credits_no_row_whose_routine_the_crate_
defines` (§2).

**Mutant** (`mutate_od216.py`, one env-gated build, `TCG_OD216_MUTANT`;
`run_od216_mutants.sh`): `od216-link-unit-unread` (`with_link_unit` keeps
nothing: OD-210 as landed) fails `slice22::a_routine_another_unit_of_the_
crate_defines_is_never_trusted`, `slice13::a_memory_routine_the_module_or_
its_crate_defines_is_never_trusted`, the digest test and codegen
`x86_body_trace_names_a_routine_the_crate_defines`; every other control
passes under it.

## 2. OD-217: the C memory routines

Slice 13 states an LIR `Memcpy`, `Memmove` or `Memset` as the selector's
call of `memcpy`, `memmove` or `memset` by symbol (an uninterpreted callee of
the world on both sides) and trusts that the routine the call binds to has
the intrinsic's effect: trust-ir's meaning of the LIR is the copy or the
fill, the theorem's is the call. That is OD-202's kind of trust (a named
routine's contract), and OD-210 did not guard it: a crate's own `memcpy`
that copies nothing binds every copy of the crate (its C prototype passes
rustc's `invalid_runtime_symbol_definitions` lint), and a crate's `memmove`
whose own copy is an LIR `Memmove` calls itself.

**The rule.** The call arm records the routine (`memory_routine`) like a
division's; `check_trusted_routines` refuses the theorem when the function
under proof is the routine (`TheFunction`), the module defines it
(`TheModule`), its link unit does (`TheLinkUnit`, OD-216) or no module is
named (`Unnamed`). `X86ModuleDefinitions::input_line` reads every
`Memcpy`/`Memmove`/`Memset` opcode as its routine's call, so a digest moves
only where a definition (or no module) can change the verdict. The slice-13
test owners, and the cross-slice tests that run slice-13 fixtures (slices
16, 18, 19 and the qualification matrix), name the fixture's module
(`slice22::fixture_owner`: a module that defines the fixture alone, which
`the_slice_thirteen_fixture_modules_define_no_memory_routine` checks against
the real modules); no theorem text changes (the slice-13 golden pins every
fixture's).

**Fails before, refused after.** Through the bridge, `copy_split` and
`copy_self` (§1's table): on main the copy's theorem replays Valid and is
credited Formal, and the one-unit compiles promote; after, each is refused
(`TheModule` in the merged module, `TheLinkUnit` per function) and the
crates are refused naming the copying function; `copy_declared` keeps its
credit. Below the bridge, solver-free (`slice13::`):
`a_memory_routine_the_module_or_its_crate_defines_is_never_trusted` (for
`Memcpy`, `Memmove`, `Memset` and `MemcpyIntoLocal`: the builder's theorem
holds and trusts the routine; called only, it stands; the module defining
the routine, a sibling unit defining it, and no module named refuse it as
`TheModule`, `TheLinkUnit`, `Unnamed`; another routine of the crate's is no
reason); `a_memory_routine_never_copies_through_itself` (the shapes renamed
to their routine: `TheFunction` whatever module is named);
`the_slice_thirteen_fixture_modules_define_no_memory_routine`. With the
replay tools, one test per process (AY 13556 + Clean 5f09e36c),
`slice13_qualification::verifier_credits_no_row_whose_routine_the_crate_
defines`: each theorem replays Valid; the verifier naming the module alone
credits every covered row Formal (`Memcpy` 6 of 6, `Memmove` 6 of 6,
`Memset` 7 of 7, `MemcpyIntoLocal` 10 of 10, `div` 25 of 25), and naming a
sibling unit that defines the routine, or a module that does, credits 0 of
them and exports nothing.

**Mutant** `od217-memory-routine-untrusted` (the call arm records no
routine: slice 13 as landed) fails `a_memory_routine_the_module_or_its_
crate_defines_is_never_trusted`, `a_memory_routine_never_copies_through_
itself` and the codegen crate trace test (its copy cases).

## 3. OD-218: rewrites into a memory routine's call

Every place in the x86-64 compile path that creates a `memcpy`, `memmove`
or `memset` call from something that was not one already (a read-only
sweep of the bridge, `trust-cg-irmid`, `trust-cg-opt`, the adapter, the
LIR passes and the selector):

| Creator | Input | Where relative to the body theorem's LIR | Guard |
| --- | --- | --- | --- |
| bridge: `ptr::copy_nonoverlapping`, `ptr::copy`, `ptr::write_bytes` (`memory_libcall_callee`) | the intrinsic | a call of `core`'s foreign `memcpy`/`memmove`/`memset` (C prototype), which the adapter reads as LIR `Memcpy`/`Memmove`/`Memset` (`classify_direct_call`; a module-local body of that name stays an ordinary call) | OD-217 |
| adapter: aggregate `Load`/`Store`, `InsertField`/`InsertElement`, `MakeAggregate`/splat lanes, `ArraySplat` (byte-uniform: `Memset`, else a doubling `Memcpy`), `copy_into_fresh_slot`, aggregate block arguments, sequence returns | an aggregate value | in the LIR (the bridge spells x86 aggregates as scalar lanes, so few reach it) | OD-217 |
| x86-64 vectorizer fill tier (`apply_fill_memset`) | `for i in 0..N { a[i] = v }` over a local, N constant, at least 1024 bytes, byte-uniform, System V, O2 and above | **after** the LIR: a machine-only `call memset` | OD-218 (by name); never credited |
| bridge `Rvalue::Repeat` | `[v; N]` | a `__trustcg_array_fill_*` helper call or stores, never `memset` | none needed |
| `sroa::match_memcpy_fill` | AArch64 `bl memcpy` | removes calls only | none needed |
| mid-end `mem_call`, `byte_copy`, `fill_call` | wasm32 only (`fill_call` withheld) | not on x86-64 | none needed |

No pass reads the containing function's name or `#![no_builtins]`, and no
other loop-idiom rewrite exists (the vectorizer's popcount, bit-reverse and
CRC idioms emit no call). The selector lowers every LIR `Memcpy`/`Memmove`/
`Memset` to the call by symbol, with no inline expansion on x86-64.

So: inside a crate's own `memset`, a fill of a local of 1024 bytes or more
would become `call memset` at O2 and above, a call of itself with the same
count, without end. The body theorem never credits that call: the LIR has
none there, so the machine's call trace differs from the source's and no
theorem is built, whatever module is named. Measured
(`slice13::the_vectorizers_memset_call_is_never_credited_and_never_
recursive`, a fill of a 1024-byte local, the vectorizer's floor and the most
candidate offsets slice 17 admits): the selector's own lowering has its
theorem; at O2 and O3 the vectorizer replaces the loop by `call memset`,
and the owner refuses the machine function for its own module, a crate that
defines `memset` and no module alike, on the machine side ("a row that
references a stack slot outside a modelled `[slot + disp]` operand"); were
those rows admitted, the walk pairs calls by position and the LIR has no
call there (`X86BodyMismatch::CallCount`). The call row itself is
`FailClosedAllowlisted`, no proven instruction. So it is a miscompile
hazard, not a proof hole, and OD-218 removes it the way LLVM's loop-idiom
recognizer does, by name: a function named `memset` keeps its store loop
(`memset_route_is_withheld_from_memset_itself`, trust-cg-opt; the same
test above finds no call in `memset`'s own fill at O2 and O3). Mutant
`od218-memset-route-recursive` (the name test dropped) fails both.
A crate whose *other* functions fill such a local calls its own `memset`,
as under LLVM without `#![no_builtins]`; `core` documents that it assumes
these symbols exist with C's signatures and semantics.

`memcmp`, `bcmp` and `strlen`, which `core` assumes too: the adapter reads
no call of them as an intrinsic, so a body theorem states each as a call of
the world on both sides and trusts nothing of it; a bridge lowering that
emits such a call for Rust code (the slice comparison's `memcmp`) carries
that assumption in the bridge's MIR lowering, outside these rulings.

## 4. Census safety

Darwin `core` defines none of the seven names, so no census root can change
and no census was run:

- `library/core/src` has no `#[no_mangle]` or `#[export_name]` item outside
  doc comments and no `global_asm!`; it declares `memcpy`, `memmove` and
  `memset` only as foreign lang items (`core::ffi::runtime_symbols`, a
  `unsafe extern "C"` block), which no module defines.
- census-s22 (`~/tcg-scratch/runs/census-s22/`, the slice-22 bridge on
  `core`, one codegen unit): none of the 3457 functions its body trace names
  is one of the seven (every one is a Rust symbol, a CGU-private copy, or
  `__trustcg_array_fill_i8`/`_i32`), and none of the symbols its 3423
  objects define (`nm -U`) is `_memcpy`, `_memmove`, `_memset`,
  `___udivti3`, `___divti3`, `___umodti3` or `___modti3`.
- So the bridge names an empty link-unit set for `core`: the compile is
  configured exactly as before (an empty set is no field of the cache
  identity or the compile policy), and a `core` function with a `Memcpy`
  records `memcpy` in its theorem but is refused only where a definition
  exists, which it does not; its verifier-input digest is unchanged (no
  line where no module or link unit defines the routine).

## 5. Gates

Through `build-slot` (`nice -n 19`, `-j2`), the `x86-stage1-ay13556`
overlay's `targo --unverified`; tool-gated lanes one test per process on
AY 13556 + Clean 5f09e36c. The final trust-cg-verify build is at
`fa077f93d`; trust-cg-codegen and trust-cg-opt did not change after their
build at `0d5a37cf1` (records bound in [PAYLOADS.md](PAYLOADS.md)).

| Gate | Result |
| --- | --- |
| the solver-free x86 body suite (`x86_source_bound_body::tests::`, every library test but the tool-gated lanes) | **412 passed, 0 failed**, 18 ignored (842 s). At `c5e2ae5e0` it found 7 failures, all of one cause (fixed in `fa077f93d`): the ArrayGep and slice-17 owners named no module, and their fixtures carry an LIR `Memmove`/`Memset` |
| `function_request::tests` | 8 passed; the two AArch64 request tests fail on this host before any x86 code runs (the overlay-built trust-cg refuses the test's stand-in Clean by sha256), as slice 22 §8.4 records |
| tool-gated: `slice13_qualification` (host replay, credit, and `verifier_credits_no_row_whose_routine_the_crate_defines`), `slice17_qualification` (replay, refutation, credit), `arraygep_qualification` (replay, credit), `slice22_qualification` (OD-210's lane, credit) | all ok, each 4-48 s |
| `trust-cg-codegen --test x86_source_bound_body` (with the replay tools) | 9 passed (the new `x86_body_trace_names_a_routine_the_crate_defines` and `a_call_of_a_routine_the_crate_defines_never_promotes` included) |
| `trust-cg-codegen --test must_refuse_corpus` | 5 passed |
| `trust-cg-codegen --lib`: `compiler::tests::x86*`, the cache-identity, Core JIT plan and custom-config tests, `compile_policy::tests`, the refusal-layer, decode-backing and x86 envelope JIT modules, the JIT request cache | 67 passed, 1 ignored |
| `trust-cg-opt --lib x86_vectorize` | 213 passed |
| compile check (`targo --unverified check --keep-going`) of every target whose `CompilerConfig` literal changed: trust-cg-codegen tests and benches, trust-cg-jit-matrix, trust-cg-cli, trust-cg-opt, trust-cg-verify | clean, but for the three codegen kernel-JIT fixtures' deliberate `compile_error!` on this compiler (`kernel_fixture_layout_unknown`, not this change) |
| the bridge's own library tests (`targo --unverified test --lib`, its workspace, the bridge overlay) | 729 passed, 14 failed: all 194 `compile_error_diag_tests` pass, the new `FunctionLinkageUnsupported` arm included; 12 failures are tests that compile real Rust and stop at E0514 (the overlay's `std` built by another rustc than the one the test runs) and 2 are `mem_refine` solver timeouts, none in code this lane touched (not re-run on the baseline) |
| `scripts/check_fmt.sh` (the 6808 package's `targo fmt`), and the bridge workspace's `targo fmt --check` | OK |
| `python3 scripts/check_documentation.py --check` | OK (the diagnostics census regenerated for the bridge's new body-trace line) |
| `python3 scripts/full_test_matrix_hosts.py --check` | OK |
| lint (`targo tippy`) | not run: the overlay's targo has no tippy, and the 6808 package's refuses the AY manifest's `[trust] compiler_timeout_secs` (tooling, recorded) |

No census was run (§4).

## 6. Reproducers (this directory)

- `crates/*.rs`: the bridge reproducers (`div_split`: the crate's own
  `__udivti3` in one module, a division in another; `div_declared`: its
  control; `copy_split`: the crate's own `memcpy` (it copies nothing) in one
  module, `ptr::copy_nonoverlapping` in another; `copy_declared`: its
  control; `copy_self`: a crate's `memmove` that copies through `ptr::copy`).
- `run_crates.sh <dylib> <out>`: compiles each (`CASES` overrides the list
  of `crate:codegen-units`) through a release bridge on the census's lane
  with the body trace and `-Zprint-mono-items`, and records every trace
  line, the placement and the objects' defined symbols.
- `payloads.py`: the [PAYLOADS.md](PAYLOADS.md) rows, from a
  `path<TAB>description` list on stdin.
- `mutate_od216.py`, `run_od216_mutants.sh`: the env-gated mutants (each the
  code before its fix) and the controls they fail.
