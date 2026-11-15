# Conditional output-memory query: preserved Mac proof failure

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The exact 96,284-byte diagnostic query returned **UNKNOWN**, not UNSAT or a
counterexample. AY exited zero, but its model-validation soundness check
rejected an internal candidate model and reported `incomplete`. No proof was
emitted, so neither certificate construction nor Clean replay was attempted.
This is an unfinished positive proof case, not a passing negative control.

The query has SHA256
`e7cb7c86173f17dfd2445faeaab42604ebe64f31e674f6e49803a93395a0e6c7`.
It is one unique query captured twice by the
[Mac diagnostic qualification](../2026-09-17-output-memory33/README.md), and
remains byte-identical after the arithmetic/output-memory development merge.
The [Linux baseline](../2026-09-17-output-memory-linux-baseline/README.md)
retains a separate timeout on the same query using that host's own tools.
Neither result is silently substituted for the other.

## Actual attempt

The original query, including its 30,000 ms SMT deadline, was submitted once:

```text
ay -smt2 query.smt2 --strict-proofs --proof query.alethe --proof-format alethe
```

The solver receipt records an ordinary exit zero, exact stdout `unknown\n`,
and 188,337 bytes of complete stderr. Its soundness-gate diagnostic, rather
than exit status alone, explains the refusal. There was no retry, query
transformation, increased limit, disabled soundness check or fallback solver.

AY executable SHA256 is
`eaeb6ecdec16702f1e312a7825b488dd948efd229d4e5964bef1b6ce1ecc0cc2`.
The existing Clean binary remains pinned at
`d967ca586211da38c981969c2fb40a49420090f0c9a7fca7cbb6351f25dd6869`
but was not executed here. Their prior seven-canary result is a prerequisite,
not successful replay of this query or authenticated AY build provenance.
No compiler, atpkg package or proof tool was replaced.

The complete explicit environment and existing proof-discovery prefix are
unchanged. The local supervisor retains its 60-second wall/one-second cleanup
and 1 MiB stdout/stderr bounds. The existing 4 GB scheduling reservation is not
a hard memory cap; the proof-size acceptance limit is not a live disk quota.
All input bookends match, owned processes are quiet and the gate token was
released. Native wait4 does not establish complete descendant containment.

Root and independent terminal audits confirmed the preserved failure. Result
SHA256 is `399745a34f84362c1e90be55170a78d4b9a7e511bab35080eb4662bdd93eb404`;
the solver receipt is
`517769bae4247f70d8ca10ae00810644af47998c02848f1ea34bb24b3aef5d2b`.

## Retention and boundary

The archive `strict-query-attempt.tar.gz` (removed from the tree) and byte/mode audit
retain all eleven attempt files plus the actual enabled controller and its
frozen pre-activation plan. Every regular member matches its original bytes
and mode; no executable payload, symlink, escaping name or AppleDouble entry
is included. Absolute paths identify the original experiment, not portable
installation instructions.

Even successful future replay of this conditional query would not establish
caller ownership, live writable storage, the ordinary Rust writer's frontend
coverage, final encoded bytes, production memory admission or TY's connected
source-to-native pipeline. This attempt provides no performance comparison,
native execution, verified-Rust or independently replayed memory-proof claim.
