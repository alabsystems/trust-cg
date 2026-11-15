# Public-memory result compositions

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Independent Clean accepts certificates for both unchanged original public-result
queries. At every observed address outside the complete 48-byte frame, machine
memory after the callback equals source memory after the same modeled event.
Combined with the earlier SP, input-projection, saved-register and cell-result
certificates, all sixteen separate claims in the two conditional models replay.

| Original query | Independent replay | Proof bytes |
| --- | --- | ---: |
| cell32-public_result.smt2 | Accepted | 52606895 |
| cell64-public_result.smt2 | Accepted | 58598982 |

The original implication and nonwrapping SP guard are retained. Its negation
yields the outside-frame condition and the negated read equality using checked
implication rules. Each of 32 native address refutations is independently checked,
then its temporary equality assumption is discharged inside a scoped subproof.
Standard array read-over-write steps skip the private overlay; the independently
proved input-memory projection and function congruence identify the arbitrary
callback result. No new assumption is added to either positive query.

The first discharge experiment omitted the false literal required when closing
an empty-clause subproof. Clean rejected it. The corrected construction resolves
that literal against the checked false rule and passes replay and three rejection
controls. A combined native address batch returned UNKNOWN after strict native
certification failed; every individual address query returned UNSAT with a
certificate accepted by Clean. Both failed approaches are retained.

The first assembled certificate exceeded the 64 MiB prototype limit and stopped
before replay. The second construction uses fresh shorter names for proof labels
and proof-local definitions. This is global alpha-renaming only: every step and
rule remains. The original and resulting byte counts and symbol counts are
recorded. Both final certificates stay below the unchanged limit and are checked
again in full. No native proof output limit or verification policy was relaxed.

Final replay accepts 32 address packets and both full public-result packets,
and rejects six corruptions (changed problem, proof hole and missing terminal
empty clause). Two concrete stale-public-memory controls are independently SAT:
the observed address is 8192, SP is 4096, entry memory is zero and the callback
result arrays contain byte one. The model therefore permits public writes.
These extra constraints occur only in negative controls.

Queries, proofs, prior failures, exact commands, checker logs, binary identities
and process receipts are archived with hashes of both compressed and original
bytes. Heavy commands execute serially under the exclusive lease and 16 GiB
process-group RSS guard with zero grace.

This is an external conditional-model composition, not native AY construction or
compiler admission. Complete callback-query qualification remains separate.
Production source Module/cache identity and final BL relocation binding are also
missing. The model still needs justified private-memory preservation and read
noninterference, valid allocation, matching events and source/native world
correspondence. No production code, package or admission policy changes here.
L09-P9 remains PARTIAL and all L01–L14 remain OPEN.
