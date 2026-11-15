# The two-address pre-expansion pass was UNREACHABLE through the bridge, and is measured NEUTRAL now that it is not

Host AMD Ryzen 9 9900X3D, Linux, one dylib per measurement, `taskset -c 2`,
interleaved rounds, minimum statistic, both arms carried twice as byte-identical
copies as the noise floor.

## The defect

`crates/trust-cg-codegen/src/x86_64/pipeline.rs` only ever CONSTRUCTED
`X86TwoAddressExpand` under

```rust
if crate::env_lock::var_os("TCG_X86_TWOADDR_EXPAND").is_some() {
```

and `trustc` refuses every `TCG_*` environment variable before the backend loads.
So through the bridge the pass was not merely default-off — it was **unreachable**.
Two consequences, both of which had been recorded as facts about the pass rather
than about its wiring:

1. Its two TRACKED sub-knobs, `x86-twoaddr-commute` and `x86-twoaddr-expand-all`,
   configure a pass that was never in the schedule. Measured before this fix:
   **byte-identical** binaries with `x86-twoaddr-commute` on and off for
   `p4_matmul`, `b1_mispredict`, `p1_xorshift`, `p2_collatz` and `h4_vec_dropper`.
   That was read as "the commuted-tie arm fires on nothing", and it is not what it
   means.
2. The pass's own `enabled()` is DEFAULT-ON (only `TCG_NO_X86_TWOADDR_EXPAND` kills
   it), and that default never applied inside the bridge at all.

The `x86-twoaddr-expand-all` knob's own description already notes that its channel
"was a `TCG_*` env var trustc refuses, so that A/B had never been run through the
bridge". Fixing the sub-knob did not help while the pass's MASTER gate had the same
defect.

Also repaired in passing: the gate is now routed through `tcg_env_flag`, so
`TCG_X86_TWOADDR_EXPAND=0` means OFF. Under `var_os(..).is_some()` it ENABLED the
pass — the same defect class already repaired for three other knobs.

## After the fix: the arms fire, and change nothing

With the tracked `-Ztrust-ir-cg-args=x86-twoaddr-expand` the pass is in the
schedule, and the commuted tie now changes the binary on **all six** programs tested
(previously byte-identical on every one). Time, 40 interleaved rounds:

| program | LLVM | base | base dup | +expand | +expand+commute |
| --- | ---: | ---: | ---: | ---: | ---: |
| `b1_mispredict` | 1.0000 | 1.1203 | 1.1207 | 1.1207 | 1.1213 |
| `p4_matmul` | 1.0000 | 1.0795 | 1.0795 | 1.0799 | 1.0803 |
| `p7_sieve` | 1.0000 | 0.7218 | 0.7205 | 0.7149 | 0.7222 |
| `m2_call_heavy` | 1.0000 | 0.7557 | 0.7554 | 0.7551 | 0.7549 |
| `p1_xorshift` | 1.0000 | 1.0014 | 1.0016 | 0.9993 | 0.9996 |
| `p8_closure_nest` | 1.0000 | 1.0005 | 0.9997 | 0.9986 | 1.0003 |

Every arm sits inside its own base-vs-dup noise floor (0.0004 on b1, 0.0000 on p4).
**The pass is measured NEUTRAL on this corpus**, in both arms.

Two things follow:

- **`b1_mispredict`'s extra register moves do not cost measurable time.** b1's loop
  runs 31-32 instructions per iteration against LLVM's 26-27, and its xorshift chain
  spends 11 instructions where LLVM spends 9 because it materialises each xor into a
  fresh register instead of tying the destination to the dying shift temp. That is
  precisely the shape the commuted-tie arm was written for — its doc names
  `b1_mispredict` explicitly — and with the arm reachable and firing, b1 moves from
  1.1203 to 1.1213. The hypothesis is falsified, not merely unproven.
- **The 2026-08-29 default-on refutation does not reproduce.** It recorded
  `p7_sieve` +43% and `p8_closure_nest` +15% absolute. Measured here, expansion puts
  p7 at 0.7149 against a 0.7218/0.7205 base (slightly FASTER) and p8 at 0.9986
  against 1.0005/0.9997. Whatever produced +43% is not reachable on this host and
  tree. The pass nevertheless stays DEFAULT OFF, because the measurement gives no
  reason to turn it on: it is neutral, and a neutral pass that changes bytes is pure
  risk.

## Why the fix is still worth landing

The pass is now REACHABLE and its knobs mean what they say, so the next lever that
needs it — the XMM commuted tie that `2026-09-29-p4-real-hot-loop/` names as p4's
gap — can be measured at all. Before this, any such measurement would have returned
byte-identical binaries and been read as "the arm does not fire".

This is the tenth instrument found env-only in this campaign. The generalisable rule
is in the `knob-env-fallback-policy` note: an env-gated pass inside the bridge is
dead code, and a tracked sub-knob cannot rescue it while its master gate is env-only.

## Reproduce

```sh
DRV=trust/build/host/stage2/bin/trustc
DYLIB=$PWD/target-bridge/release/librustc_codegen_trust_cg.so
C="-Ztrust-verify=off --edition=2021 --crate-type bin -Cpanic=abort -Copt-level=3"
for p in b1_mispredict p4_matmul p7_sieve m2_call_heavy p1_xorshift p8_closure_nest; do
  for a in "" "-Ztrust-ir-cg-args=x86-twoaddr-expand" \
           "-Ztrust-ir-cg-args=x86-twoaddr-expand -Ztrust-ir-cg-args=x86-twoaddr-commute"; do
    $DRV -Zcodegen-backend=$DYLIB -Ztrust-ir-cg-args=no-proof-certs $a $C \
         -o /tmp/$p.$(echo "$a" | md5sum | cut -c1-6) benchmarks/beat-llvm/progs/$p.rs
  done
done
```
