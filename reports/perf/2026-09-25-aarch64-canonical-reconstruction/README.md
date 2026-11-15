# AArch64 canonical immediate reconstruction

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Clean candidate `443ed769f` restores canonical query identity for the eight
integer ALU, bitwise and shift immediate families. Canonicalization validates
the real instruction first, then constructs its register-form sibling with a
symbolic second operand. The original immediate-only opcode cannot encode a
register operand and remains refused when presented that malformed input.

The first broader qualification at `2a7527927` passed both package all-target
checks but failed the existing portable-proof regression: 284 lowering unit
tests passed and one failed. That test required a canonical symbolic query but
received the original baked-immediate query. Earlier malformed-operand
hardening correctly refused the synthetic RI/register combination; the
canonical builder then fell back to its original instance.

The new baseline at `9b4bc2417` reproduces the same defect independently for
AddRI/Gpr32/7. Its malformed-input control passes. At `443ed769f`, both new
tests pass: 32 valid combinations cover all eight families at both widths and
two immediates; 48 malformed instructions stay refused by both reconstructors.
The unchanged portable-registry/source-binding regression also passes. All
three repaired tests execute with zero failures or ignored tests, under stock
Rust 1.97.1, one job and an 8 GiB process-group RSS limit.

The canonical theorem still cannot confer source-lowering authority. The
production discharge policy is unchanged, and the existing regression requires
Statistical strength for the reconstructed instruction even when its canonical
theorem has independently replayable proof. This is a focused repair result;
the broader current-main regression campaign and complete Linux floor are
separate measurements. The archived initial failure, baseline, repaired logs,
exact runner and patches retain their original bytes.
