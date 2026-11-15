# Source-bound conditional callback-memory obligations

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`CheckedAarch64ScalarCellFrame::diagnostic_memory_obligation` constructs the
complete public-memory query from the independently matched original TrustIR,
LIR, and allocated machine caller. The existing exact frame, source, call and
byte checkers retain their admission boundary. This API returns a diagnostic
query, not an instruction proof receipt.

The model covers one through sixteen ordered scalar callbacks, four- or
eight-byte cells, arbitrary public memory effects, all call-input arrays and
argument bits, final cell and return bits, four saved registers, and SP. Every
byte outside the 32 private saved bytes participates in the public observation,
including unused frame padding. Callback functions are shared between source
and machine for each call occurrence, with injective symbol encoding; different
occurrences may have different behavior. Private bytes are projected out of
callback inputs and restored afterward. This explicitly assumes callback
noninterference, private-memory preservation, C ABI callee-saved register
and SP preservation, plus a live writable private frame; typed C
declarations and numeric SP guards do not establish those premises.

Fresh, acyclic array definitions bound expression expansion across calls. Each
has one defining equality and can reference only earlier definitions. These
are conservative extensions of the formula, not assumptions that its desired
conclusion holds.

## Qualification

Commands use the sealed ae9 Trust pack through `targo --unverified`; these
checks make no claim that Trust verified the compiler build. The final
`trust-cg-verify --all-targets` check passes in 234.04 seconds.

All 19 selected unit tests pass in separate processes, with zero ignored cases.
The independent concrete evaluator checks 576 memory states and detects all
14 changed callback/public/private-memory cases. All 24 original captures bind
through the real pipeline; eight chained variants bind at two and sixteen
calls, with removal of a later call rejected. The package all-targets check
and maintained formatting gate pass. The 52 exported problems (38 positive,
14 negative, deduplicated by exact bytes for future replay) remain unproved.

The first compile failed with E0603 because the new module imported `Byte` through a
private re-export. The corrected import uses its defining module. That failure
is retained alongside subsequent actual results. The second run passes 18
of 19 tests and the all-targets check, but stops the concrete positive test
on its incorrect expectation of `QF_AUFBV`: the maintained serializer validly
emits `ALL` for arrays plus uninterpreted functions. The third run corrects
that test expectation, includes literal bytes in the concrete corpus, and
exports both positive and negative queries. No production formula is weakened.

Concrete evaluation is regression evidence. No complete query has a new
independently replayed proof from this change. The full callback environment
premises, encoded-byte/relocation binding, and proof admission remain separate
requirements. The private ABI bridge still refuses the unproved calling frame;
this change does not close L01–L14 or complete the compiler.

`manifest.json` binds each losslessly compressed command log, result, harness,
query and qualified source file to its original bytes. `queries.json` binds exported
queries to their originating test cases and exact source/compiler identities.
