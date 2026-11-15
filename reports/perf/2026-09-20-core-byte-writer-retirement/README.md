# Caller allocation history survives root return — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Qualified on base `ecc174485eafb94a158e44b80061f68fbc1acc0d` plus the retained
candidate. The [previous caller-memory theorem](../2026-09-20-core-byte-writer-caller/README.md)
retained an explicit retirement operation in its generic terminal allocation
state. This increment proves that operation preserves every incoming allocation
record and composes that proof into the complete captured writer execution.
Production compiler code, installed tools and dependency pins are unchanged:
TrustIR `25422eb4`, Clean `55a85e99`, AY `849c19fa`.

The new helper theorem quantifies over all allocation lists, byte maps, cursors
and owner bounds. Its premise is the actual ByteV1 memory-ownership admission
predicate with an empty active-owner list. This predicate requires every row's
owner to be below the bound. Induction on Nat proves that the reversed owner
equality test is false; elimination of each allocation constructor proves its
base, size, owner and live flag survive retirement; induction over the complete
list proves the original history remains unchanged. No post-retirement state
is assumed.

The helper is a closed untrusted expression elaborated against the immutable
ByteV1 environment and then independently kernel-checked against a reconstructed
proposition. It adds no axioms or declarations. The standalone helper's private
recheck model is a memory law independent of any target module, and grants no
instruction or compilation authority. Its 7,816-byte DAG is also inserted into
the writer's actual Return proof, where the owner is the real fresh root owner
and admission comes from the writer's original caller premise.

The complete 51-step writer theorem now requires its terminal memory to contain
the **original allocation rows**, exactly five successive eight-byte writes,
the original cursor and host, no active owner, and the successor of the actual
fresh root owner. The source reconstruction states this terminal independently;
the untrusted assembler composes the actual Return with the checked allocation
identity. All previous quantifiers and entry/range/live-access premises remain.
The two concrete applications of the universal theorem still check address 80
and `u64::MAX - 39` with distinct allocation histories, words, cursors, host
states and owner counters, universally over initial bytes.

The maintained gate passes **8 groups, 8 accepted DAGs and 37 refusals**.
Seven accepted DAGs concern whole captured-writer executions; the eighth is the
standalone allocation lemma. The original 36 controls remain, and the new
control requires the kernel to reject using the allocation lemma to justify an
empty final history. Thirty-four refusals require kernel TypeMismatch, two
reject malformed DAG encodings and one rejects a wrapping source interval.
Resource failures earn no rejection credit. Separate micro-check coverage is
false for these terms; this record claims kernel acceptance.

```sh
python3 scripts/check_core_byte_writer.py --output /tmp/core-byte-writer-replay
```

The maintained gate took 1006.20 seconds with peak process-group RSS
6119 MiB. Its 30-minute deadline, 16-GiB ceiling with zero grace,
5,000,000 kernel heartbeat limit and 100,000-entry cache limit are unchanged.
The assembler's 128-lookup limit is unchanged. The source, HEAD, fixture and
resolved dependency identities remain held through qualification. Formatting,
documentation, whitespace and stored/decoded archive checks pass.

The first standalone attempt compiled, then failed elaboration because local
aliases for computed Boolean predicates were opaque to the elaborator's
conversion check. Replacing those aliases with the actual predicates fixed the
candidate. That exact failed source and diagnostic are retained. The second
standalone attempt accepted the lemma and rejected erased history in 121.63
seconds of test execution (141.50 seconds including compilation). The third
attempt accepted the standalone lemma but stopped at an assembler composition
check: a raw terminal state and the lambda application produced by congruence
needed explicit equality transport. The remaining tests were stopped after
that failure; the partial run earns no qualification credit. Explicit kernel-
checked beta conversions connect the intermediate states. The fourth attempt
qualifies the integrated complete writer and the maintained gate.

This establishes allocation preservation in the canonical source model. It
does not prove Rust frontend adequacy, reference validity, native caller or
stack ownership, the relation between canonical and native memory, or compiler
publication. The native writer's frame/opcode refusal remains the recorded
production frontier. **All L01–L14 remain OPEN.**
