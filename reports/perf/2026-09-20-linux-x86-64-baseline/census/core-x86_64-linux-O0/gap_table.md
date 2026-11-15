# trust-ir-cg census: `core`
* emitted objects in `obj/`: 2706 (per-function/per-batch objects the backend DID produce; not a success count of mono items)

* compiler: `rustc 1.99.0-dev (3a3e781fe 2026-09-14) (trustc 0.1.0)` at `$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin/trustc`
* backend: `$HOME/trust-cg/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so`; panic=abort; opt-level=0
* repo rev: `3a3e781fe082b74d3c4de0ade65b1de3cbee7255`; trust-cg rev: `9da5e2376931cfca79f60e82c0acda9633af01c7`
* exit code: `1`; wall: 41s
* typed refusals (JSON): **0** across **0** functions; distinct codes: 0
* failed roots (externally required, fail-closed): **726**; distinct reasons: 28
* skipped internal functions (dropped as unreachable — for a LIBRARY every one is a missing symbol downstream): **0**; distinct reasons: 0
* trapping stubs emitted for dynamic-dispatch shims (link, but TRAP if reached): **0**; distinct reasons: 0
* harness errors (non-backend `error:` lines): 0

## Failed roots by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|
| 1 | `[TCG-RET-ABI]` | 282 | `_RNvYNcNtINtNtNtCs5j7F4uy8uKG_4core3ops12control_flow11ControlFlowNtNtBd_3cmp8Or` |
| 2 | `[TCG-REGALLOC-063]` | 149 | `_RNvYNcNtNtNtNtCs5j7F4uy8uKG_4core3net11socket_addr10SocketAddr2V40INtNtNtBc_3op` |
| 3 | `[TCG-PROOF-465]` | 102 | `<unknown>` |
| 4 | `[TCG-ARG-ABI]` | 32 | `_RINvMNtCs5j7F4uy8uKG_4core6optionINtB3_6OptionhE3mapcNvYcINtNtB5_7convert4Fromh` |
| 5 | `[TCG-POINTEE-DYN-VALUE]` | 30 | `_RINvMs1_NtNtCs5j7F4uy8uKG_4core3ptr8non_nullINtB6_7NonNullRDNtNtBa_3fmt5DebugEL` |
| 6 | `[TCG-PASSVAL-067]` | 25 | `_RINvNtCs5j7F4uy8uKG_4core3ptr12align_offsethEB4_` |
| 7 | `[TCG-POINTEE-LANES]` | 20 | `_RINvMNtCs5j7F4uy8uKG_4core5sliceSTNtNtNtNtB5_7unicode12unicode_data11conversion` |
| 8 | `union field mem::manually_drop::ManuallyDrop<num::imp::fmt::Part<'{erased}>> is a fat pointer` | 19 | `_RINvNtNtCs5j7F4uy8uKG_4core3fmt5float29float_to_decimal_common_exactdEB6_` |
| 9 | `[TCG-POINTEE-UNSIZED-TAIL]` | 16 | `_RNvMNtNtCs5j7F4uy8uKG_4core5array4iterINtB2_8IntoItercKj3_E10unsize_mutB6_` |
| 10 | `memory-backed slice assignment Rvalue::Cast` | 11 | `_RNvMs1_NtNtCs5j7F4uy8uKG_4core3ptr8non_nullINtB5_7NonNullSAjj4_E6as_ptrB9_` |
| 11 | `whole scalarized aggregate` | 5 | `_RINvNtCs5j7F4uy8uKG_4core10intrinsics20select_unpredictableINtNtNtB4_3mem12mayb` |
| 12 | `ADT Use source field <n> before aggregate binding` | 4 | `_RNvMNtCs5j7F4uy8uKG_4core3stre12escape_debug` |
| 13 | `Ty::[ascii::ascii_char::AsciiChar` | 4 | `_RINvYINtNtCs5j7F4uy8uKG_4core6option8IntoIterNtNtB8_4char11EscapeDebugENtNtNtNt` |
| 14 | `[TCG-RET-REGCLASS]` | 4 | `_RNvMs18_NtNtCs5j7F4uy8uKG_4core3num7nonzeroINtB6_7NonZerooE16from_ascii_radixBa` |
| 15 | `direct call slice fat-pointer arg <n> is not a whole-slice place or const-slice literal` | 3 | `_RNvMs3_NtNtCs5j7F4uy8uKG_4core3ffi5c_strNtB5_4CStr29from_bytes_with_nul_uncheck` |
| 16 | `memory leaf type is not a scalar` | 3 | `_RINvNtNtCs5j7F4uy8uKG_4core3fmt8builders7from_fnNCNCNvXs2_NtNtB6_2io5errorNtNtB` |
| 17 | `[TCG-SSA-071]` | 2 | `_RNvMs0_NtNtNtCs5j7F4uy8uKG_4core2io5error4reprNtB5_4Repr10new_custom` |
| 18 | `atomic over non-I<n>..I<n>-scalar element *mut io::error::OsFunctions` | 2 | `_RINvNtNtCs5j7F4uy8uKG_4core4sync6atomic11atomic_loadONtNtNtB6_2io5error11OsFunc` |
| 19 | `from_residual for an unmodeled Try type ops::control_flow::ControlFlow` | 2 | `_RINvNtCs5j7F4uy8uKG_4core5array18try_from_fn_erasedINtNtNtB4_3ops9try_trait17Ne` |
| 20 | `from_residual for an unmodeled Try type ops::try_trait::NeverShortCircuit` | 2 | `_RINvNtCs5j7F4uy8uKG_4core5array11try_from_fnINtNtNtB4_3ops9try_trait17NeverShor` |
| 21 | `unsupported intrinsic `_`` | 2 | `_RNvMs4_NtNtCs5j7F4uy8uKG_4core5panic8locationNtB5_8Location6callerB9_` |
| 22 | `Place deref memory load type is not scalarizable` | 1 | `_RNvMs1_NtNtCs5j7F4uy8uKG_4core3ptr8non_nullINtB5_7NonNulleE6as_refB9_` |
| 23 | `Place deref memory store from Rvalue::Ref` | 1 | `_RNvXNtNtCs5j7F4uy8uKG_4core3ffi5c_strNtB2_21FromBytesWithNulErrorNtNtB6_3fmt7Di` |
| 24 | `Place projection field <n> before aggregate binding` | 1 | `_RINvMNtCs5j7F4uy8uKG_4core6optionINtB3_6OptionINtNtNtNtB5_4iter8adapters3map3Ma` |
| 25 | `Rvalue::Discriminant before enum aggregate binding` | 1 | `_RNvXs_NtNtCs5j7F4uy8uKG_4core3ops12control_flowINtB4_11ControlFlowNtNtB6_9try_t` |
| 26 | `carrying_mul_add width <n> is not modeled` | 1 | `_RNvMs8_NtCs5j7F4uy8uKG_4core3numo16carrying_mul_addB7_` |
| 27 | `loop-carried local _<n>` | 1 | `_RNvNtCs5j7F4uy8uKG_4core3fmt5write` |
| 28 | `memory aggregate whole assignment from non-local operand` | 1 | `_RINvMs8_NtCs5j7F4uy8uKG_4core3anyNtB6_6TypeId2ofNtNvMNtNtB8_5panic10panic_infoN` |

## Skipped internal functions by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Trapping stubs by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Typed diagnostic codes

| rank | code | count | example function | example why |
|---:|---|---:|---|---|
