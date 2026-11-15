# trust-ir-cg census: `core`
* emitted objects in `obj/`: 3337 (per-function/per-batch objects the backend DID produce; not a success count of mono items)

* compiler: `rustc 1.99.0-dev (d7f143f3b 2026-09-21) (trustc 0.1.0)` at `$HOME/trust/build/x86_64-apple-darwin/stage1/bin/trustc`
* backend: `$HOME/trust-cg/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib`; panic=abort; opt-level=0
* repo rev: `unknown`; trust-cg rev: `unknown`
* exit code: `1`; wall: 245s
* typed refusals (JSON): **7** across **7** functions; distinct codes: 3
* failed roots (externally required, fail-closed): **109**; distinct reasons: 21
* skipped internal functions (dropped as unreachable — for a LIBRARY every one is a missing symbol downstream): **0**; distinct reasons: 0
* trapping stubs emitted for dynamic-dispatch shims (link, but TRAP if reached): **0**; distinct reasons: 0
* harness errors (non-backend `error:` lines): 0

## Failed roots by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|
| 1 | `[TCG-RET-ABI]` | 26 | `_RNvMs1_NtNtCs7e1ihmkzmZ8_4core3ptr8non_nullINtB5_7NonNullSAjj4_E8from_refB9_` |
| 2 | `[TCG-ARG-ABI]` | 23 | `_RINvMs1_NtNtCs7e1ihmkzmZ8_4core3ptr8non_nullINtB6_7NonNullSAjj4_E4castBV_EBa_` |
| 3 | `[TCG-POINTEE-UNSIZED-TAIL]` | 16 | `_RNvMNtNtCs7e1ihmkzmZ8_4core5array4iterINtB2_8IntoItercKj3_E10unsize_mutB6_` |
| 4 | `[TCG-POINTEE-DYN-VALUE]` | 15 | `_RINvMsa_NtCs7e1ihmkzmZ8_4core3fmtNtB6_9Formatter8wrap_bufNCNvMs_NtB6_8buildersN` |
| 5 | `Ty::[ascii::ascii_char::AsciiChar` | 4 | `_RINvYINtNtCs7e1ihmkzmZ8_4core6option8IntoIterNtNtB8_4char11EscapeDebugENtNtNtNt` |
| 6 | `[TCG-SSA-071]` | 4 | `_RNvMs0_NtNtNtCs7e1ihmkzmZ8_4core2io5error4reprNtB5_4Repr10new_custom` |
| 7 | `[TCG-POINTEE-LANES]` | 3 | `_RNvMs1l_NtNtCs7e1ihmkzmZ8_4core9core_arch3x86NtB6_7___m128h8as_array` |
| 8 | `from_residual for an unmodeled Try type ops::control_flow::ControlFlow` | 3 | `_RINvYINtNtNtCs7e1ihmkzmZ8_4core5slice4iter4IterhENtNtNtNtBa_4iter6traits12doubl` |
| 9 | `memory leaf type is not a scalar` | 3 | `_RINvNtNtCs7e1ihmkzmZ8_4core3fmt8builders7from_fnNCNCNvXs2_NtNtB6_2io5errorNtNtB` |
| 10 | `Place deref memory load type is not scalarizable` | 1 | `_RNvMs1_NtNtCs7e1ihmkzmZ8_4core3ptr8non_nullINtB5_7NonNulleE6as_refB9_` |
| 11 | `Place deref memory store from Rvalue::Ref` | 1 | `_RNvXNtNtCs7e1ihmkzmZ8_4core3ffi5c_strNtB2_21FromBytesWithNulErrorNtNtB6_3fmt7Di` |
| 12 | `Place projection field <n> before aggregate binding` | 1 | `_RINvMNtCs7e1ihmkzmZ8_4core6optionINtB3_6OptionINtNtNtNtB5_4iter8adapters3map3Ma` |
| 13 | `Rvalue::Discriminant before enum aggregate binding` | 1 | `_RNvXs_NtNtCs7e1ihmkzmZ8_4core3ops12control_flowINtB4_11ControlFlowNtNtB6_9try_t` |
| 14 | `[TCG-REGALLOC-063]` | 1 | `_RINvNtCs7e1ihmkzmZ8_4core10intrinsics20select_unpredictableINtNtNtB4_3mem12mayb` |
| 15 | `atomic over non-I<n>..I<n>-scalar element i<n>` | 1 | `_RINvNtNtCs7e1ihmkzmZ8_4core4sync6atomic11atomic_loadnEB6_` |
| 16 | `atomic over non-I<n>..I<n>-scalar element u<n>` | 1 | `_RINvNtNtCs7e1ihmkzmZ8_4core4sync6atomic11atomic_loadoEB6_` |
| 17 | `borrowed aggregate reference used without deref` | 1 | `_RNvXsb_NtCs7e1ihmkzmZ8_4core4wtf8NtB5_10EncodeWideNtNtNtNtB7_4iter6traits8itera` |
| 18 | `carrying_mul_add width <n> is not modeled` | 1 | `_RNvMs8_NtCs7e1ihmkzmZ8_4core3numo16carrying_mul_addB7_` |
| 19 | `loop-carried local _<n>` | 1 | `_RNvNtCs7e1ihmkzmZ8_4core3fmt5write` |
| 20 | `memory aggregate whole assignment from non-local operand` | 1 | `_RINvMs8_NtCs7e1ihmkzmZ8_4core3anyNtB6_6TypeId2ofNtNvMNtNtB8_5panic10panic_infoN` |
| 21 | `unsupported intrinsic `_`` | 1 | `_RNvMs4_NtNtCs7e1ihmkzmZ8_4core5panic8locationNtB5_8Location6callerB9_` |

## Skipped internal functions by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Trapping stubs by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Typed diagnostic codes

| rank | code | count | example function | example why |
|---:|---|---:|---|---|
| 1 | `TCG-SSA-071` | 4 | `_RNvMs0_NtNtNtCs7e1ihmkzmZ8_4core2io5error4reprNtB5_4Repr10new_custom` | _RNvMs0_NtNtNtCs7e1ihmkzmZ8_4core2io5error4reprNtB5_4Repr10new_custom: trust-ir ssa/loop-completeness check failed: valu |
| 2 | `TCG-REGALLOC-063` | 2 | `core.542ad821d0dce3d0-cgu.0` | rustc_codegen_trust_cg: Trust Codegen object emission failed: adapter error: malformed trust_ir: block 3 branch arg 0 ha |
| 3 | `TCG-MIR-UNSUPPORTED` | 1 | `<crate>` | rustc_codegen_trust_cg: cannot compile required function with unsupported MIR (failing closed rather than miscompiling): |
