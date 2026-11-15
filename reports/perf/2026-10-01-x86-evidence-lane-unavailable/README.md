# The x86-64 EVIDENCE lane is unavailable on this host — every perf number I have is diagnostic

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux · HEAD `0a6c17244`

## The finding

Running `benchmarks/beat-llvm/run.py` with no knobs at merged HEAD fail-closes on **all 18
of 18** programs. Not a load refusal (load 1.27 against a threshold of 12.0) and not the new
panic route — the error is `[TCG-PROOF-465] proof promotion rejected for target X86_64`,
raised for ordinary opcodes:

```
emitted opcode inventory found 26 uncovered non-pseudo opcode(s) across 8 distinct
opcode(s) [XorRR, MovRR, CmpRI, Jcc, ShlRI, ShrRI, AddRR, AddRI];
first ... is x86_64::XorRR (no operand-exact evidence: registry name lookup is not
proof credit: query `Bxor_I` in x86-64 Lowering selects a theorem by name, not an
obligation built from this instruction)
```

Upstream of it, the compile prints:

```
portable certificate set is DISABLED; CERT-SKIP declined for every query and live
discharge retained: the vendored drat-trim checker ... hashes to 6bd14b38... but
manifest.v1 authorizes <manifest.v1 names no checker for this target>
```

With `-Ztrust-ir-cg-args=no-proof-certs` the same program compiles and runs correctly
(p1_xorshift, exit 41).

## Attribution: pre-existing and structural, NOT an upstream regression

My first hypothesis was that upstream's merge broke it, because the same merge regenerated
`crates/trust-cg-verify/verdict_db/bound_memory_certs/manifest.v1` (17404 -> 17504 bytes).
**That hypothesis is wrong.** Counting the targets the manifest names, before and after:

| revision | `x86_64-unknown-linux` entries |
|---|---|
| `b422f87fd~14` (pre-merge) | **0** |
| `b422f87fd` (post-merge) | **0** |

The manifest covers `aarch64-apple-darwin` (x2) and `aarch64-unknown-linux-gnu` only. The
certificate set has **never** covered x86_64-linux, which is why the `library/core` census on
this host has always needed `no-proof-certs`. The manifest change is unrelated.

## What this does to my numbers — the correction

`benchmarks/beat-llvm/contract/gates.json` states ledger eligibility requires "an
independent proof checker that runs when probed, no DEGRADED-verification banner and **no
backend knob**", and `--bridge-cg-arg`'s own help says it is "a DIAGNOSTIC lane: the row is
never evidence, and the ledger ratchet rejects proof-weakening knobs outright".

**Every beat-llvm number I produced on this host ran with `no-proof-certs`.** That includes
the table in `../2026-10-01-bounds-check-raise-trade/`. So, precisely:

* Those rows are **not** contract/ledger evidence, and must not be cited as parity evidence
  against LLVM. The report that presents them now says so.
* They remain valid **relative A/B measurements**: the knob skips per-compile lowering
  *certificates* ("weakens the evidence the artifact carries"), not any optimization, and in
  the bounds-check-raise case both arms ran in the same lane with only the subject knob
  differing. The 8-program controlled cut (largest move 1.7%) and the vector-class contrast
  (scalar 0.981x vs 2.03x-54.93x) stand as engineering data.
* **Compile-time** ratios from that lane understate the real cost, because skipping
  certificates is exactly a compile-side saving. Runtime ratios are not affected that way.

## Consequence for the standing goal

The goal's performance clause — "at least matching LLVM and clang" — **cannot currently be
evidenced on x86-64 Linux under this repository's own contract.** It can only be measured
diagnostically. That is a gate on the goal, not a property of the generated code, and it was
true before today's work; it had simply never been separated from the measurements.

## The remedy considered here (superseded by the correction below)

> Ruled 2026-10-02 (OD-52 in the decision record): the portable set
> gains a host only through host qualification of that host's checker, never by
> re-authorizing the whole set over an unqualified checker.

The compile's own message names the options: restore the toolchain the manifest was minted
against, or "review the toolchain change and re-authorize the complete set with
`scripts/trust_cargo.sh run --release -p trust-cg-verify --bin regen_canary_certs`".

Since the manifest names no x86_64-linux checker at all, this is not toolchain drift to
repair — it would **mint proof-checker authority for a target the committed set has never
covered**. That writes committed proof-authority data and widens what the artifact claims,
so it was not run. `CLAUDE.md`'s own rule applies: a
proof-required mode must reject unsupported or insufficient evidence.

Until it is taken, the honest shape of any x86-64 perf claim from this host is "diagnostic
lane, lowering only, no proof credit".

---

## CORRECTION: the blocker is NOT the certificate manifest

This report said the remedy was a decision about `regen_canary_certs` — minting
checker authority for a target the committed set never covered — and that this was "the
thing standing between measured and evidenced". **That attribution is wrong**, and it
matters, because it framed the repo's central x86-64 proof frontier as a config decision
someone had declined to make.

Re-checked directly. Compiling even `fn main() { std::process::exit(0) }` with proof
certificates ON (the default) fails, and the reason is not a missing or unauthorized
checker:

```
[TCG-PROOF-465] proof promotion rejected for target X86_64:
  ... first is x86_64::MovRR (no complete evidence: statistical sampling is not
  proof credit: `RECONSTRUCTED x86_64 Copy_64 -> MovRR (real-operand)` found no
  counterexample in 100000 sampled inputs)
```

and for the other opcode class:

```
  ... x86_64::XorRR (no operand-exact evidence: registry name lookup is not proof
  credit: query `Bxor_I` in x86-64 Lowering selects a theorem by NAME, not an
  obligation built from this instruction)
```

Both say the **evidence CLASS is insufficient**, not that a checker is absent. And a
working independent checker IS found on this host — the compile prints
`using $HOME/trust/first-party/clean/target/release/clean`, with no DEGRADED
banner — so `run.py`'s "independent proof checker that runs when probed" requirement is
satisfiable here.

The `manifest.v1 names no checker for this target` warning is real but separate: it
disables the portable bound-memory certificate set (CERT-SKIP), which is a different
mechanism from per-compile lowering proof credit.

## So what actually blocks an EVIDENCED performance claim

x86-64's most basic lowering carries only statistical evidence. `CLAUDE.md` states the
policy this refusal is enforcing: "default wide-integer statistical checks are tests" and
"A proof-required mode must reject unsupported or insufficient evidence". The refusal is
*correct*; the gap is upstream of it.

This is the repo's known x86-64 proof frontier, not a toggle: the `Copy_64 -> MovRR`
obligation is `NOT (x = x)`, a syntactic tautology, so no solver route can discharge it —
only a body theorem or a structural decision about how a register copy earns credit. That
is why the `library/core` proof census on this host sits at one dominant reason with
MovRR/MovRR32 as the overwhelming majority, while the LOWERING lane is clean.

**Therefore:** the performance result in
`../2026-10-01-loop-state-proved-dead/` (geomean 0.880x, 18/18 MATCH) is a sound
MEASUREMENT and is not ledger evidence, and it will not become ledger evidence by any
configuration change available here. It needs the copy-credit decision first. Nothing in
the diagnostic lane is hiding a performance defect — the knob skips certificate emission,
not optimization — but the distinction between "measured" and "evidenced" is real and
belongs in any citation of these numbers.

---

## VERIFIED FROM SOURCE: the copy-credit gap is a recognized, retracted class

The correction above was still partly an assertion ("only a body theorem or a structural
decision can"). Checked against the tree, it is the repo's own position, already named and
enforced:

* **The class has a name.** `crates/trust-cg-verify/src/frame_proofs.rs` calls it the
  **"#62 X==X class"**: obligations where "the computed offset is restated identically on
  both sides with no independent emitter".
* **Its members were RETRACTED, deliberately.** `FRAME_RETRACTED_DEGENERATE` filters six
  degenerate FrameLayout obligations out of the proof set, with the comment keeping the
  genuine ones explicitly ("the 12-bit range check, large-NEGATIVE SUB, SP-alignment
  mod 16/32, callee-save non-overlap, distinct-slot non-aliasing, callee-save restore
  identity, FP/SP addressing, triple callee-save remain").
* **A test forbids new ones.** `positives_are_structurally_distinct`: "Every positive
  obligation must be structurally non-degenerate: the two sides must not be the identical
  expression (the #62 X==X class)."
* **And the producer labels this one.** `Copy_64 -> MovRR` is constructed with
  `degenerate: true`.

So a register copy's obligation restates `x == x`. There is nothing for a solver or an
independent checker to discharge, and no certificate can exist — which is why
`REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT`'s own doc records that name-lookup credit was
"withdrawn on every ISA", closing the only other route by design rather than by omission.

Crediting it therefore requires one of exactly two things, neither of which is a
configuration change (XD-01, ruled 2026-10-02, takes the first until operand
correspondence is carried):

1. **a body theorem** — evidence relating the copy to the surrounding function's semantics
   rather than the instruction in isolation; or
2. **a structural decision** that a copy verified by construction counts as credited — a
   ruling of precisely the kind `bound_memory_authority` records for the Formal-only
   bound-memory rule (owner ruling 2026-09-29).

**This closes the question as far as it can be closed from here.** The x86-64 performance
result is a sound measurement; it cannot become ledger evidence without (1) or (2); and the
refusal that blocks it is the proof contract working as designed, enforced by a committed
test.
