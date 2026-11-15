# Exact signed i128 limb-check arithmetic

This proves the complete mathematical equation mirrored from
`proof_checked_smul_i128_limb_check_flag()` in
`crates/trust-cg-verify/src/checked_mul_i128_proofs.rs`. It adds no production
verdict and changes no Rust query, proof inventory, allowance, budget, grade,
dependency pin, kernel world or shared formal entry.

The base is unsigned candidate `56d6bc7885b750e8de7f2918692426669feb8794`.
Its source and retained provider are unchanged. The new module is
[`CheckedMulI128Signed.lean`](../../../formal/lean/Trust/Cert/CheckedMulI128Signed.lean).

## Complete statement

`original_signed_limb_check_flag` quantifies over four independent `BitVec 64`
inputs and proves the original one-bit source flag equals the original machine
flag. There are no free-product premises or restricted input valuations.

The source retains sign-bit extraction, the two actual 128-bit magnitudes,
their full original unsigned high calculation, wrapped 128-bit low product,
XOR result sign and distinct positive/negative limits. The machine retains
arithmetic sign masks, the exact `(lo xor mask) - mask` magnitude low word,
masked high word with its original nonzero borrow, raw wrapped product,
XOR masks, masked raw-product high word, all four unsigned core arms, raw
result sign comparison and the indispensable nonzero-result guard.

The proof derives the sign masks bit by bit. It proves the actual
`(lo or -lo) >> 63` borrow identity and transports both masked words through
checked `toNat` arithmetic. Existing `BitVec.neg_mul` / `mul_neg` identities
relate the wrapped raw product to the actual magnitude product; no nonlinear
SAT result is assumed. The unchanged unsigned theorem then applies to those
actual magnitude limbs and their actual product. The signed-limit reduction
is proved for an unrestricted full 128-bit residue with checked arithmetic,
including zero and the most-negative value.

## Actual qualification

The same final source bytes elaborate under genuine Lean 4.31.0 and admitted
Lean 4.30.0-rc2. Each uses its matching immutable unsigned artifact; no artifact
is relabelled across versions. The main module hashes are:

* signed theorem: `465a1ca606cda63384a91dd8c600cca9e88248b3276c2d479f047092c18a8dd6`;
* controls: `b9dbc8ee7fbfb3585e60321ce30050df536a30b61468770bc68980cbaa5ab153`;
* unchanged unsigned theorem: `8c7ee93c5a06680c4098b8653bf587d7f21553ddfb207ad84236cd2d2f823d6b`.

Signed elaboration took 2.315 / 2.394 seconds. Separate `leanchecker` processes
replayed both signed modules in 0.929 / 1.273 seconds. These are reference-Lean
local kernel replays with the imported standard environment, **not independent
Clean or empty-environment replays**. All fourteen audited declaration closures
are subsets of `propext`, `Classical.choice`, `Quot.sound`; the final theorem
uses exactly those three. No `sorryAx`, native-check axiom or new rule remains.

The
[`controls module`](../../../formal/lean/Trust/Cert/CheckedMulI128SignedControls.lean)
checks the seven existing Rust mutation classes: omitted zero guard, sign check
or magnitude core; OR instead of XOR sign; unmasked product high word; raw
unsigned input core; and unsigned dispatch. It preserves their actual witness
limbs. Eight concrete edge cases evaluate both unchanged original expressions:
zero, MIN times negative/positive one, positive limit times one/two, negative
one squared/times two and the negative signed boundary. In each world the
original accepted proof is rejected at all seven mutated goals with an actual
type-mismatch diagnostic. All 24 final command rows met their expectations,
all input source bytes stayed unchanged and all jobs are terminal.

## Preserved failed and insufficient attempts

The first invocation declined because its own Lean search path selected an
incomplete namespace root. The corrected harness imports a hash-bound copy of
the existing unsigned artifact from the **same** Lean world.

An early `bv_decide` version elaborated but its axiom audit exposed native
`ax_1_5` dependencies. That version is explicitly **insufficient evidence**,
despite its zero elaboration exit status. Its exact source, artifact and audit
are preserved. The final source replaces every such helper with explicit
bit-vector/`Nat`/`omega` proofs; no native axiom or relaxed axiom policy was
adopted. Failed arithmetic drafts and the initial controls comment parse error
are retained too. None is overwritten or reclassified as a final pass.

## Remaining production boundary

The mathematical proof is ready for the separately owned original-goal bridge.
Independent Clean export/import/replay under an admitted world and typed,
width/order/name-preserving reconstruction of the actual original `SmtExpr`
equation are still required before this theorem can credit a production row.
The checker must verify the retained proof against that fresh exact goal, not
accept a theorem name, source resemblance, sample agreement or a replacement
normalized formula. The old decoded-word, per-compile source binding and other
documented i128 deferrals remain unchanged. No Rust/native/SourceNoUB/compiler
completion claim follows from this mathematical result.
