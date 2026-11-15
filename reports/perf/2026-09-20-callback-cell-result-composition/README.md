# Original cell-result memory compositions

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Independent Clean accepts external compositions for both unchanged original
cell-result queries. Machine cell bytes after the callback equal the source
cell bytes after that same modeled event. This retains arbitrary callback
writes; the result is not assumed equal to the cell's pre-call value.

| Original query | Independent replay | Proof bytes |
| --- | --- | ---: |
| cell32-cell_result.smt2 | Accepted | 37112612 |
| cell64-cell_result.smt2 | Accepted | 55892553 |

Each proof imports the checked [input-memory projection derivation](../2026-09-20-callback-index-proof-publication/ay/README.md)
after verifying its archived hash and removing only its final refutation and
unused original negative assumption. Function congruence equates the callback
results at the same arguments. Checked address exclusions permit standard
read-over-write steps through the 32 private overlay stores; select congruence
then connects source and machine reads, and concat congruence joins the bytes.
Every final certificate is checked against the exact original query, including
its original guards and definitions, with no new problem assumptions.

The final cohort accepts both complete certificates and rejects six corruptions
(changed problem, proof hole, missing terminal empty clause). Concrete
stale-cell counterexamples are separately SAT for both widths: SP is 4096,
saved registers, argument and initial cell are zero, entry memory is zero, and
the callback result arrays contain byte one. Those witnesses confirm that the
post-call result may differ from the original cell. They constrain the negative
controls only; the positive original queries are unchanged.

Earlier failures remain archived and unresolved. The first unrestricted 32-bit
stale-cell control produced an invalid candidate model, which AY's model gate
correctly rejected as UNKNOWN. The second construction stopped when a 32-address
batch for the 64-bit cell's byte six computed UNSAT but failed native strict
certification with an unverified trust step; AY returned UNKNOWN. Splitting that
batch into two independently checked groups of 16 succeeded. The final 64-bit
construction uses such groups for every byte; no solver flag, checker or limit
was weakened. The 32-bit positive certificate is retained from the first run.

Final replay accepts 18 packets (16 new address groups and two complete cell
claims) and rejects six corruptions. The earlier 32-bit construction separately
checked its four address batches. Two preparatory batch cohorts each accept
eight packets and reject 18 corruptions. Repeated and component checks are not
additional cell-result theorems. Raw and reduced proofs, query and binary
identities, exact commands, failures, checker logs and resource receipts are
retained. Heavy commands run serially under the exclusive host lease and
anchored 16 GiB process-group RSS supervision, with zero grace. Final proofs
remain below 64 MiB.

The two public-result claims and both complete callback models remain
unresolved. Production native composition and compiler replay, original source
Module/cache identity and final call relocation binding remain missing. The
conditional model still requires private-memory preservation/noninterference,
valid allocation and source/native world correspondence. This report changes
no production code, installed package or admission policy. L09-P9 stays PARTIAL;
all L01–L14 stay OPEN.
