# Current main verifier regression qualification

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

All 28 planned commands pass on clean source
`443ed769f6ba67036e50b219561423dbc8a94ec0`: 899 Rust tests, 60 focused
release-accounting Python tests, all-target checks for verify/opt/codegen, and
the maintained root formatting gate. Every executed Rust test reports zero
failures and ignored tests. Named unit namespaces remain filtered selections;
all nine selected integration targets run completely, with zero filtered tests.

The run covers the incoming non-vacuous sampling and floating-conversion
changes, x86 conditional-move escape controls, symbolic memory/UB semantics and
interpreter-oracle changes, release-accounting rules, and the canonical
AArch64 immediate repair. The original portable-proof regression now passes as
part of all 285 lowering-proof unit tests. Malformed operand refusals and the
wrong-source-opcode proof-authority control also pass unchanged.

This uses stock Rust 1.97.1, the recorded proof-tool PATH, one job, and an 8 GiB
process-group RSS bound. The source remains clean and compiler/tool identities
remain unchanged. The warm target directory belongs to this source path alone.
The complete 167-target Linux floor is a separate queued run; this archive does
not claim its result, private ABI bridge qualification, compiler rebuilding,
source-refinement proof coverage or product completion.

The first qualification's actual portable-proof failure and the focused repair
are archived in `../2026-09-25-aarch64-canonical-reconstruction/`. A second
broader wrapper mistakenly scheduled two nonexistent unit namespaces; review
caught that before reaching them. Its owned process was cancelled during the
lowering suite, and all partial logs and the explicit cancellation reason are
retained. The corrected third run keeps the complete fsym_ub_map integration
target and the real fsym_trust_ir unit namespace. Neither cancelled execution
nor the two prerequisite-rejected floor queues earns success credit.
