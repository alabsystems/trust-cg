# Original byte-address proof publication

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The original nested zero-addition byte-address query now emits an independently
checkable CLI certificate. Its earlier certificate applied a stale expression
spelling twice, contained an explicitly reported proof hole, and was rejected
by Clean. The [AY qualification](ay/README.md) preserves the failure, repair,
original problems, proofs, source and binary identities, and resource receipts.
AY development main contains the repair and evidence at `df71cc092d3a7e2920136359151d457db03feecf`.

The final CLI passes all eight index probes: four distinct-address UNSAT
certificates replay in frozen Clean and four same-address controls are SAT.
Clean rejects twelve corrupted index packets. The focused library regression
covers decimal, hexadecimal and binary zeros, with three accepted certificates
and nine rejected corruptions. Both unchanged original callback input-memory
projection queries still replay through the new CLI, with six corruptions
rejected. Native source-spelling, assumption-authority, array, bridge and
artifact regressions pass; the selections overlap.

The global AY quality gate remains red with identical inherited failures and
no baseline changes. A broader self-check selection also has the same eight
passes and one letleak completeness failure on the pre-repair and candidate
binaries; that test receives UNKNOWN instead of its expected UNSAT. The failed
zero-match test filter and its corrected 36-test run are retained separately.

These index facts are components for proposed read-over-write composition.
The twelve other isolated memory claims and two complete callback models remain
unresolved. Callback private-memory preservation and noninterference, source
allocation validity, and source/native world correspondence remain explicit
premises. No production compiler admission or installed package changes.
L09-P9 remains PARTIAL; all L01–L14 remain OPEN.
