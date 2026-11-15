# Preserve original zero-addition index proof assumptions

An original byte-address query containing `(bvadd (bvadd sp offset) 0)`
returned UNSAT but emitted an assumption with the zero addition repeated and
an explicit proof hole. Independent Clean rejected that file. The failed
eight-query probe is retained here: all native verdicts matched, three of the
four distinct-address certificates replayed, and the zero-addition certificate
failed. This was an external certificate defect; the CLI warned that its proof
contained an unproved step.

Late checked source reconstruction now validates the canonical spelling that
the replacement proof will actually use after removing its stale presentation
overrides. Raw source expansion, declaration identity, exact term roundtrip,
native strict checking and original assertion authentication remain required.
The early reconstruction path retains its existing spelling check. No resource
limits or first-party verification policy change.

Maintained stock Rust 1.97.1 export `5f9e3c4281beb34c79cded194cd075e06ad2a131`, parent `da0668648426ea628313b5ec537f981dd2d82c88`. Native test selections:

| Selection | Passed |
| --- | ---: |
| New zero-addition regressions | 2 |
| Guarded reconstruction | 17 |
| Store permutation | 12 |
| Original assertion bridge | 35 |
| Proof artifacts | 78 |
| Ground source | 2 |
| Complete memory source | 1 |
| Source spelling and assumption authority | 36 |

Selections overlap and do not constitute a full solver or compiler test run.
The focused tests cover decimal, hexadecimal and binary zero spellings,
identical scoped String and streaming output, a changed-address SAT control,
and an arbitrary declared-function SAT control. Frozen Clean accepts all three
library certificates and rejects nine corruptions.
The first regression coordinator stopped on a zero-match authored-scope filter;
that invocation is preserved and the corrected filter was required to run a
positive number of tests before qualification continued.

The actual CLI passes all eight index probes: four distinct-address UNSAT
certificates replay independently, and all four same-address controls are SAT.
Clean rejects twelve corrupted index packets. Both unchanged original callback
projection queries also replay through the new CLI, with six corruptions
rejected. Commands, original queries, certificates, source inventories, frozen
binary hashes and resource receipts are retained; executable payloads stay
local. Every heavy command ran serially under an exclusive host lease, anchored
16 GiB process-group RSS supervision, zero grace, two build jobs and one test
thread.

The inherited global quality gate remains red: `GATE FAILED: 14 waiver failure(s), 239 file-baseline failure(s), 250 function-baseline failure(s), 0 unsafe-baseline failure(s), 99 construct-baseline failure(s), 2 disabled-test attribute(s), 1 env-flag ratchet mismatch(es).`.
Baseline and candidate printed diagnostics match after normalizing only file
and test-only-site counts; that CLI caps displayed failure lists.

A separate self-check selection has eight passes and one inherited failure on
both the frozen pre-repair binary and this candidate: the letleak publication
case returns UNKNOWN where the test expects UNSAT. That failure remains open.
No new production debt or quality-baseline changes were needed.

These are address subgoals for a proposed saved-register composition. The
whole callback theorem, twelve other isolated memory claims and production
compiler admission remain unresolved. No installed compiler, solver or package
changes here.
