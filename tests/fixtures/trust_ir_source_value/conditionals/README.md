# Actual conditional producer data

These four boundConditional8/16/32/64 exports come from Clean's maintained
`ws6_7_actual_source_equation_proves_checked_conditional_all_uint_widths`
producer test, with kernel/compiler/reflection source at
`550ad0858df6a00c61a7cdabc7f37fa0bc975258`, kernel tree
`d1a068842f53591e6835c0d4215a6ec8542f0f00`, and an intermediate IR-only
manifest/lock graph selecting IR `81a6f0cf41ab153e3260c95a0db53592cc34e9a4`.
The actual exporter passed at all four widths. This intermediate producer
composition is not a final cross-repository cohort qualification.

The source remains
`def boundConditionalW (a b : UIntW) : UIntW := if a < b then a + 1 else b`.
`PRODUCER-DATA.json` records the measured size and SHA256 of all 40 actual
files. Compared with the previous producer data, only the four complete
module.bin files changed; all 36 original Definition, theorem, closure-digest
and DATA files remain byte-identical. No proof or digest bytes were edited.

Each complete module retains the actual source body and generated helper.
Definition and theorem fields use the canonical Clean Expr v1 codec, including
the full CIC proof. The original Definition is a separate environment input,
rechecked by the consumer. Expected source names and widths are selected
independently of the proposed theorem. The consumer derives its own goal from
the actual complete module and selected function, strictly checks the proof,
and audits it against that original-source goal.

Tests retain source/proof/goal/IR tampering controls and unselected helper
refusals. Producer metadata supplies no consumer authority. These are
value-equation interoperability data: original-environment authentication,
textual frontend fidelity, operational correspondence, helper/runtime/ABI/NoUB,
machine-code proofs and full G4 are separate obligations.
