# Complete conditional callback-model compositions

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Independent Clean accepts certificates for both complete unchanged original
single-callback models. Each certificate proves the conjunction of restored SP,
equal projected call-input memory, all four restored saved registers, matching
post-call cell bytes and matching observable public-memory bytes. The arbitrary
shared callback may write both the cell and other public memory.

| Original complete query | Independent replay | Final proof bytes |
| --- | --- | ---: |
| cell32-framed.smt2 | Accepted | 32448060 |
| cell64-framed.smt2 | Accepted | 36462783 |

The compositions import the separately checked [sixteen component claims](../2026-09-20-callback-public-result-composition/README.md).
Each original negative claim is discharged in a scoped subproof; checked
double-negation and conjunction rules combine the resulting properties. Every
child must have the same definitions and guards as the complete query. Child
packet hashes and original query identities are retained. No property or new
problem assumption is introduced by composition.

The first whole construction accepted the 32-bit model, but the 64-bit proof
exceeded Clean's cumulative four-million-bit decimal-literal normalization
budget. Both are preserved. Sharing exact typed constants through fresh nullary
definitions let both large proofs replay without changing the original query,
the checker or its limits. Those intermediate external proofs were 131,623,279
and 163,624,452 bytes, within an explicit 384 MiB experimental construction bound,
and are not claimed to meet the native producer's 64 MiB output limit.

The final representation shares equal transparent ground definitions and typed
store/select expressions. It then shares derivations whose transitive premises
contain no assumptions: clauses, rules, arguments and ordered mapped premises
must match exactly. No binder or anchor argument is admitted. The implicit
previous command needed by every subproof closing stays at its original local
position. Every final certificate is replayed in full after these transformations;
the transformations themselves confer no proof authority. Both final outputs
are below the unchanged 64 MiB native size limit, without claiming that native
AY constructs them.

The large-proof cohort accepts two originals and rejects six corruptions. All
twenty original semantic mutation queries return SAT: private reads, private
writes, lost public effects, stale cell results, wrong arguments, pointers,
widths, save offsets, SP and callback targets, at both cell widths. The 64-bit
stale-cell query takes about 170 seconds inside its existing 180-second bound.
The reduced-proof cohort independently accepts both originals and rejects six
more corruptions (proof hole, missing empty clause and changed problem).
Component and repeated replays are not extra complete-model theorems.

The solver logs retain model-gate diagnostics encountered during candidate
search. Final SAT verdicts are reported as observed solver results; no native
model-construction bug is declared repaired here. The earlier unrestricted
isolated-cell UNKNOWN and strict native batch-publication failures remain open
in their respective reports.

All queries, large and reduced certificates, failed attempts, exact commands,
checker logs, binary identities and process receipts are retained. Heavy
commands and representation transforms run serially under the exclusive host
lease and anchored 16 GiB process-group RSS guard with zero grace. Archives bind
both original and compressed bytes and are read back before publication.

This completes external proof of these two conditional single-event models.
It does not prove arbitrary callees preserve or ignore private save storage,
establish allocation validity, justify event coupling or source/native world
correspondence, cover arbitrary multi-call traces, or finish the compiler.
Production AY source sharing and native derivation, compiler replay, original
Module-aware request/cache identity and integration with the existing final-byte
and ELF relocation owners remain unresolved. No production admission, installed
package or release policy changes. L09-P9 remains PARTIAL; all L01–L14 remain OPEN.
