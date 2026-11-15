# Original full LR-restoration certificates

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Independent Clean accepts composed certificates for both unchanged original
LR-restoration queries, covering the 32-bit and 64-bit cell models. Each proves
all eight saved LR bytes and the reconstructed 64-bit register. The original
definitions, opaque callback, memory effects and guards are retained. Neither
query is weakened and no component conclusion is added as a problem assumption.

The external prototype obtains checked address refutations from frozen AY,
retains each unconditional disequality derivation, and shares repeated index
pairs. Standard `arrays_idx` and `arrays_row` steps follow the private overlay
and pre-call store chains. Transitivity proves each byte, congruence lifts the
eight byte equalities through concat, and a separately checked concat/extract
identity yields the original register. Resolution discharges the original
negated register equality. The callback array is never constrained or read
through in this register proof.

| Original query | Independent replay | Proof bytes |
| --- | --- | ---: |
| cell32-lr.smt2 | Accepted | 34640244 |
| cell64-lr.smt2 | Accepted | 56750703 |

Clean rejects six corrupted full-register packets: changed original problem,
proof hole and missing terminal empty clause for each width. Both changed
register queries are separately SAT in AY. Full-register construction also
replays 152 address certificates and two concat/extract certificates, for
156 accepted packets total; component packets are not
additional whole-register theorems. The earlier exact-byte prototype accepts
14 packets (12 addresses and two byte claims) and rejects six corruptions.

The ordinary CLI byte checkpoint remains incomplete: all four wrong-address
controls are SAT, both X20 byte claims return UNKNOWN, and both LR byte claims
return UNSAT with incomplete external certificates that Clean rejects. The
compositions above are diagnostic external prototypes, not a production AY
reconstruction path or an in-compiler replay. AY source and installed binaries
are unchanged by this report. The frozen CLI comes from AY development commit
`df71cc092d3a7e2920136359151d457db03feecf` and the previously qualified maintained export.

The archived queries, exact commands, emitted proofs, checker logs, mutations,
source/binary identities and resource receipts include every attempted probe.
Heavy commands run serially under an exclusive host lease, anchored 16 GiB
process-group RSS supervision with zero grace. Final proofs stay below the
prototype's 64 MiB output bound. No timeout or memory exhaustion is counted as
a valid result.

The other six saved-register claims, two cell-result claims, two public-result
claims and both complete models remain unresolved. Production native proof
construction, source Module/cache identity and final call relocation binding
remain separate work. The conditional model still requires private-memory
preservation/noninterference, valid allocation and source/native world
correspondence; these certificates do not prove those premises. L09-P9 remains
PARTIAL and all L01–L14 remain OPEN.
