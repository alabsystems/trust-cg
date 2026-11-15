# Exact unsigned i128 limb-check arithmetic

This adds a genuine proof term for the unsigned division-free limb-check
equation. It does **not** change a Rust query, proof-database verdict, timeout,
budget, allowance, count, dependency pin or production grade. The missing
independent Clean replay and original-SMT-to-CIC binding remain below.

The selected source is CG `a4e6852a2824b8511a377b2b146eb7dc9acf0024`.
The exact Rust obligation is `proof_checked_umul_i128_limb_check_flag()` in
`crates/trust-cg-verify/src/checked_mul_i128_proofs.rs`. Its source file is
included in the evidence archive and bound by the qualification receipt.

## Statement and proof

The new standalone module is
[`CheckedMulI128Unsigned.lean`](../../../formal/lean/Trust/Cert/CheckedMulI128Unsigned.lean).
Its final theorem `original_unsigned_limb_check_flag` quantifies over four
independent `BitVec 64` inputs and equates the actual one-bit source and machine
flags. There is no restriction on their 256-bit Cartesian input domain.

For `B = 2^64` and `M = B^2`, the source keeps all four exact widened limb
products, both wrapped 128-bit intermediate additions, the actual unsigned
128-bit carry comparison and the widened carry shifted left 64 bits. The
machine keeps the wrapped product of the two actual concatenated 128-bit
operands, its high 64-bit limb, the wrapped 64-bit sum of the two cross-product
low limbs, the original unsigned carry comparison and both high-limb tests.
`high64BV_extract` also checks the high-extraction correspondence.

`original_source_exact` proves that the source's original high calculation is
the untruncated 256-bit product divided by `2^128`. All product bounds and
zero-product facts used by the proof are derived from the actual inputs;
there are no assumed free-product premises. The overflow proof splits on the
two high input limbs: two nonzero high limbs force overflow; when one is zero,
`single_cross_overflow` proves the remaining exact carry/overflow relation.
Checked `toNat` equations transport every original bit-vector operation.

## Actual qualification

The **same source bytes** elaborate under genuine Lean **4.31.0** (the current
formal-project pin) and **4.30.0-rc2** (a version the current Clean NDJSON world
table admits). These produce distinct `.olean` artifacts; neither artifact is
relabelled as the other's world. The source hashes are:

* theorem module: `8c7ee93c5a06680c4098b8653bf587d7f21553ddfb207ad84236cd2d2f823d6b`;
* controls module: `195fa288689f680b2028eefe87113f185adb05360f41849f227da30730cf126a`.

Actual theorem elaboration took 2.800 / 2.490 seconds and fresh-process local
`leanchecker` replay took 1.031 / 0.922 seconds respectively. This is the
reference Lean kernel replaying the local theorem with imported standard
dependencies, **not an independent Clean check or an empty-environment replay**.
The final theorem's printed axiom closure is exactly `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx`, `native_decide`, new arithmetic
axiom or trusted normalization rule is used.

The
[`controls module`](../../../formal/lean/Trust/Cert/CheckedMulI128UnsignedControls.lean)
proves concrete counterexamples for deleting each of the two cross-product
overflow arms, the carry arm or the both-high arm. Both worlds reject applying
the original accepted proof to each deleted-arm goal. The final negative
controls use the identical original proposition on the source side and require
an actual proof type-mismatch diagnostic. The initial alternate Boolean
spelling controls, all failed development attempts and their exact sources are
preserved, without replacing their outcomes.

All jobs are terminal. The 18 final elaboration/replay/identity/control rows and
eight refined hostile substitution rows passed their stated expectations;
source bytes were unchanged. No broad Rust proof campaign or native aggregate
test was repeated for this theorem. The manifest hashes every archive member;
the archive retains commands, tool identities, outcomes and proof artifacts.

## Remaining authority boundary

The current positive route in `ay_bridge.rs::try_closed_definition_proof`
accepts an untrusted Alethe candidate only after the captured checker accepts
it against the original SMT2 query. Its composer is limited to closed defining
equations and requires at least one definition. This original arithmetic query
has no preconditions. The affine polynomial experiment is test-only, at most
64-bit and explicitly not supported by the captured checker. Neither path can
instantiate this theorem. The optional ByteV1 rechecker is a different bounded
invocation theorem and cannot grant this instruction row authority.

The missing implementation must reconstruct the original `SmtExpr` equation
with a typed, width-preserving CIC renderer, bind all four declared variables,
all operators and their order, import the actually checked theorem/dependency
closure under an admitted kernel environment, apply it and independently check
that its type is exactly the reconstructed original goal. A theorem name,
matching sample, structural fingerprint or changed spelling is insufficient.
Changed constants, operand order, widths, comparison kind, assumptions or
formula must be rejected by that check. The current Clean version table does
not admit 4.31 exports; re-elaboration under 4.30rc2 here avoids changing that
table but does not itself perform export or Clean replay. No world row, TCB
policy, shared `Trust.lean` entry or production positive verdict is changed.
