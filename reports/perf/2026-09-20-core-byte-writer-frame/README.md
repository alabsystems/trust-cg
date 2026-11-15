# Captured writer preserves a fresh private frame — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Qualified on base `b8a5440ad62d2daeae286b64e481c6db800ae54f` plus the retained
candidate. The actual 51-instruction ByteV1 writer now has a composed theorem
that preserves a sixteen-byte private interval, alongside its complete original
terminal-world contract. The source claim is reconstructed independently from
the retained module and the caller contract. Production compiler code,
installed tools and dependency pins are unchanged: TrustIR `25422eb4`,
Clean `55a85e99`, AY `849c19fa`.

All previous caller quantifiers and actual entry/range/live-access premises
remain. The frame base is arbitrary. Its additional premise is zero overlap
between its sixteen-byte interval and the actual allocation history, including
retired rows. For each of the five stores, the checked fresh-range separation
law derives nonoverlap from that premise and that store's real access guard.
The checked read-preservation and pointwise write-outside laws compose through
all five writes. Equality congruence connects those facts to the **actual
executed result**, using the existing complete writer proof.

The conjunction requires the original full terminal world, equality of the
sixteen-byte read before and after execution, and equality at every byte whose
offset is below sixteen. The pointwise clause preserves initialized values and
uninitialized bytes individually; equality of two failed reads cannot hide a
changed byte. The whole-execution proof is locally let-bound and reused in the
three conclusions. It is still kernel-checked, and the immutable ByteV1
environment gains no definitions, axioms or trusted declarations.

Two applications of the same universal proof use the original caller at
address 80 with frame bases 32 and 128. Both are fresh gaps below the caller's
cursor 512; the frames touch the end of a retired allocation and the end of the
live output allocation, respectively. Both quantify over every initial byte
map. The controls require rejection of frame base 80 (live output overlap)
and base 16 (retired-history overlap), missing freshness, another store's access
proof, a wrong read location, a bound for the wrong byte offset, and reuse after changing the actual final store.
The retired-overlap control documents ByteV1's conservative no-address-reuse
profile; it does not claim that a native stack cannot reuse physical addresses.

The maintained gate passes **9 groups, 11 accepted DAGs and 44 refusals**.
The previous eight DAGs remain; the new ones are the universal frame theorem
and its two concrete applications. Forty-one refusals require kernel TypeMismatch,
two reject malformed DAG encodings and one rejects a wrapping source interval.
Resource failures earn no rejection credit. Separate micro-check coverage is
false for these terms; this record claims kernel acceptance.

```sh
python3 scripts/check_core_byte_writer.py --output /tmp/core-byte-writer-replay
```

The full gate took 1767.36 seconds with peak process-group RSS
6115 MiB. The 30-minute deadline, 16-GiB ceiling with zero grace,
5,000,000 kernel heartbeat limit, 100,000-entry cache limit and 128 assembler
lookup limit are unchanged. Source, HEAD, fixture and resolved dependencies
remain held during qualification. Formatting, documentation, whitespace and
stored/decoded artifact checks pass.

The first attempt failed the unused-must-use compile gate when a profile
reconstruction result was intentionally discarded without a binding. The second
accepted the initial universal read theorem and rejected its four controls in
476.57 test seconds. The third, stronger candidate failed compilation because
an acceptance receipt borrowed a temporary instance source. Giving the source
a local binding fixed its lifetime. These exact failed sources and diagnostics
are retained. The fourth standalone run accepted the pointwise theorem and two
applications with six controls. Before the fifth maintained run, the concrete candidate terms
are beta-specialized from the universal proof and an additional wrong-offset-
bound control is added. Specialization is untrusted assembly; the resulting
closed proof, actual source and independent concrete proposition still undergo
full kernel replay. The fifth attempt then failed compilation on private field
access in that assembler helper; using the public expression accessor fixes it. The sixth
maintained run qualifies the final candidate.

This closes a canonical source-memory framing ingredient. It does not model
actual native instruction execution, connect Nat/Option byte maps to native
bitvector arrays, establish writable stack ownership, or grant production
frame/opcode credit. The original native writer remains refused pending that
composition. These are private integration models; the public Store/Return API
is unchanged. **All L01–L14 remain OPEN.**
