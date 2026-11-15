# Conditional callback-memory model: unresolved proof checkpoint

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The complete new calling-frame models are **not proved**. No production
compiler admission, callee contract or L01–L14 closure is credited here.

The diagnostic model lets a callback change arbitrary public memory, including
the scalar cell. It explicitly assumes that callback effects depend only on
its visible memory and arguments, and that private saved bytes are preserved.
The model projects private bytes out of the call input and restores them in
the machine's call result. These are conditional environment semantics, not
properties inferred from a typed C declaration. The model checks original and
machine call inputs, SP, four saved registers, the returned cell and every
observable public byte against the arbitrary post-call state. It covers one
call and a four- or eight-byte cell; it is not bound to encoded instructions.

## Executed results

| Run | Queries | Result |
| --- | ---: | --- |
| Original address expressions | 22 | 13 expected SAT mutations; nine `unknown`, including both positive models |
| Equivalent modular affine addresses | 22 | All 20 mutations SAT; both positive models `unknown` |
| Positive models without strict-proof flag, diagnostic only | 2 | Both still `unknown`; no solver-policy change is adopted |
| Individual conjuncts with original guards and definitions | 16 | Both SP restoration claims UNSAT and independently replayed; all 14 memory claims `unknown` |

For the two SP claims, Clean accepts the original certificates and rejects all
six controls: changed proof rule, removed empty-clause conclusion, and the
same proof paired with a changed private-memory problem. These are only SP
claims; they do not establish the missing memory conjunction. There are no
accepted certificates for either complete calling-frame model.

Mutations cover reading or overwriting private bytes, wrong call target,
wrong pointer or scalar argument, lost public effects, stale cell contents,
wrong restored SP, a wrong save offset and a wrong cell-store width. Address
normalization changes `sp - n + k` into modular `sp + (k - n)` consistently;
no conjunct, guard or mutant is removed. The diagnostic mode comparison
isolates solver completeness from the strict-proof transport gate and supplies
no strict-admission evidence.

All runs use the exact installed AY/Clean pair:

- AY SHA-256 `93fe897aea3b4ad5d2ff50c9729c8aa097bfcf36dcbf581e21c4515bbeaf400b`.
- Clean SHA-256 `680069f8d7185a8dbc0cc67e860d57a7df9ca4cf8bd8a4d8951346cbbf594dbc`.

Runs are serial, under the anchored 16 GiB process-group RSS supervisor with
zero grace; AY also receives its 8 GiB internal memory limit. Every command
completed without timeout, RSS breach, cancellation or output truncation.
The exact problems, proofs where produced, checker inputs, logs, identities,
guard records and harnesses are retained. The complete Linux compiler floor
had already finished before these solver runs began.

## Concrete next investigation

The included solver source is read from the exact AY build tree
`43f133d35b620b01320cc3e2d05117a82c393b1c`, not inferred from a newer checkout.
Its bounded packed proof route accepts at most 64 writes per store chain and
terminates chains at variables or supported constant arrays. These models'
machine-input projections contain 68 or 72 writes, and their callback results
are array-valued function applications. Those are concrete limits relevant to
this route; they are not a complete diagnosis of every solver fallback.
Whole-array input equality and callback congruence also need supported proof
transport. Raising a count alone cannot establish all of these obligations.

The remaining work must preserve complete public effects, private-memory
noninterference and ownership premises, exact original-source binding,
independent proof replay, and emitted call-byte/relocation identity. The
previous successful stack-local memory algebra does not supply this whole-call
composition. `inventory.json` records exact and decoded artifact identities.
