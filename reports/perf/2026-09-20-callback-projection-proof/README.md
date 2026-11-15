# Callback input-memory projection proof

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

AY now proves equality of the source and machine public-input memories in both
32-bit and 64-bit conditional callback models. Writes of saved registers that
are subsequently overwritten by the same private-byte projection have no
observable effect. The bounded recognizer preserves the ordered surviving
writes, so distinct index expressions may alias. Export derives the identity
using ordinary array and propositional proof rules, with no unproved hole.

The [companion qualification](ay/README.md) retains the exact commands, source
and executable identities, native/solver regressions, certificates, corruption
controls and earlier failed attempts. AY commit `2e8cdbed69f3ef34ecd3f25e531fcd719f5d8274` is on development
remote main. Its archived source tree, maintained stock export and frozen
executables pass 2,738 proof-library tests, with one existing external-corpus
harness ignored. Focused solver reconstruction passes for both original widths.
Independent Clean accepts 19 certificate packets and rejects 95 corruptions.
Those packets include both unchanged original callback projection queries with
their original definitions and entry guards. The inherited global AY quality
gate remains red; the normalized diagnostic comparison introduces no new failures.

This advances the [whole-call checkpoint](../2026-09-20-callback-memory-model-checkpoint/README.md),
where these two isolated memory claims were unknown. The complete conditional
callback models, register restoration, returned cell and public result still
need composed proofs. Callback private-memory preservation and noninterference,
source/native allocation and world correspondence remain explicit premises.
The source, machine and ELF correspondence checkers grant no new production
admission here. This report qualifies no new release CLI or installed package.
The compiler's installed artifacts are unchanged; L09-P9 remains PARTIAL and
all L01–L14 remain OPEN.
