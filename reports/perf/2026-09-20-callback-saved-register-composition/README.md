# All conditional saved-register model claims replay

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Independent Clean accepts original-query certificates for FP, X19 and X20 in
both cell-width models. Together with the [prior LR compositions](../2026-09-20-callback-lr-composition/README.md),
all eight saved-register claims now have independently checked external
compositions. Each proves all eight bytes and the reconstructed 64-bit register.
Original definitions, guards and callback memory effects are retained.

| Original query | Independent replay | Proof bytes |
| --- | --- | ---: |
| cell32-fp.smt2 | Accepted | 23448203 |
| cell64-fp.smt2 | Accepted | 30833550 |
| cell32-x19.smt2 | Accepted | 34242401 |
| cell64-x19.smt2 | Accepted | 41732568 |
| cell32-x20.smt2 | Accepted | 45847539 |
| cell64-x20.smt2 | Accepted | 53400326 |

The producer follows the same checked read-over-write, transitivity, concat
congruence and concat/extract construction as the LR prototype. Repeated index
pairs share one derivation within each proof. A syntax-only dependency pass
removes steps outside each address refutation's dependency chain, retaining
anchor closing steps, their implicit final premises, discharged assumptions
and referenced definitions. Every reduced address certificate is then replayed
independently before composition; reduction itself grants no proof authority.
The isolated reduction test also rejects three corrupted packets.

The six whole-register certificates are accepted and all 18 corrupted packets
are rejected (changed problem, proof hole and missing terminal empty clause).
Six wrong-register queries are separately SAT in AY. Construction independently
replays 1224 address packets and six concat/extract packets, for 1236 accepted
packets total. Components and repeated replays are not additional whole-register
theorems. All final proofs fit the 64 MiB prototype output bound.

Queries, raw and reduced proofs, checker and solver logs, exact commands,
corruptions, identities and resource receipts are archived. Per-index data is
stored in deterministic `records/index-cases/*.tar.gz` bundles; `index-members.json`
records every member's size and SHA-256. The outer inventory binds each complete
tar payload and compressed file. Every bundle was read back and every member
verified before archiving. Other records are individually compressed.

These are external diagnostic compositions. Production AY does not yet build
the corresponding native composite derivations, and no compiler admission,
installed package or verification policy changes. The model still assumes
private-memory preservation/noninterference, valid allocation and source/native
world correspondence. The two cell-result claims, two public-result claims and
both complete callback models remain unresolved. L09-P9 remains PARTIAL and all
L01–L14 remain OPEN.

Heavy commands run serially under the exclusive host lease and anchored 16 GiB
process-group RSS supervision, with zero grace. Timeouts, memory exhaustion,
truncation and cancellation never count as successful evidence.
