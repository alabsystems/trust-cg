# Exact arithmetic AOT proof export

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Clean combined source `deb2dda2889754db7c4b872cebdcf72ab8f5672a` passes all **48/48** required arithmetic AOT
exports and **6,912 native C-oracle comparisons**. The cases cover I32/U32/I64/U64,
ADD, SUB and optimized doubling, at O0–O3. Every successful invocation emits an
ELF object, exact SMT queries, per-rule metadata, a lowering sidecar and a Trust
proof sidecar. The debug CLI's actual SHA256 is
`5f9ed6ae4da1b1131f4ade4cc2d278b6b68e4825478991615cccbf85ff20ff73`. This report qualifies that development executable;
it does not silently replace the installed compiler.

The original installed `c611a263` baseline refuses **48/48 required positives**
before object or sidecar publication: the dynamic arithmetic rule has no static
ProofDatabase entry. This is a missing required feature, not a passing negative
test. That complete failed baseline remains unchanged in the archive.

The verifier now optionally retains the exact arithmetic obligation after its
complete source/body check, independent replay and final enforced provenance
check. An immutable payload binds the original machine/LIR input, function and
instruction. Ordinary verification/cache requests retain no extra obligation
graph. The code generator attaches the payload to the matching instruction row;
artifact and Core proof identities include its query/input/index identity.

Export validates the payload against the public metadata before audit-only
categorization. Every dynamic arithmetic group independently replays all its
queries before publication. Query content identifies filenames and full
obligations identify deduplication, so same-named proofs with different aliases
or immediates remain distinct. Missing payloads, changed metadata or withdrawn
checker authority cannot produce files. Input hashes identify the compiled
subject; these sidecars do not constitute a complete source-to-byte proof.

All **25 CLI unit tests** and **13 CLI publication integration tests** pass with
zero failures, ignores or filters. The new unit test requires two actual O0 SUB
immediates with the same display name to retain distinct SMT files and lowering
rows; an exact duplicate is shared. Six metadata/payload corruptions and checker
withdrawal after a successful compile all refuse before publication. The first
selected run passes 13 tests but its full-target wrapper rejects the 12 filtered
tests. That failed classification is retained; the second run executes all 25.

The arithmetic JIT target still requires **160/160 compilations and 23,040 native
calls**, plus 84 changed-word refusals and the source/request/tool controls. Its
updated request test checks exported input identity, wrong machine/stamp/source,
missing source, no-cache fresh authority and withdrawn solver/checker behavior.
The complete maintained Linux floor passes **50/50 targets, 358
tests**, with 0 failures, 0 ignored,
0 measured and 0 filtered. These overlapping
suite counts are separately scoped, not summed into a whole-system result.

The 48 actual AOT outputs contain **nine distinct exact SMT queries**. A separate
AY command-line campaign exports complete Alethe proofs for all nine, and Clean
independently accepts **9/9 originals** while rejecting **27/27 corruptions**:
hole rule, removed empty conclusion and opposite premise. Exact query/proof
bytes, tool hashes and full transcripts are retained. This checks actual export
bytes rather than reconstructed test formulas. A separate audit checks all 48
sidecars against their actual ELF bytes, exact source identities, query files,
formal strengths and Trust transport hashes. Its first draft omitted the
documented lowering-equivalence hash domain and failed; the corrected second
audit applies that domain and passes all 48 without changing any artifact.

Remote main's output-memory diagnostics were merged before this qualification.
A fresh ordinary verifier build and all **33 frame/diamond/cell/output-memory
tests** pass on this combined Linux tree; unrelated library tests are explicitly
filtered. The output-memory function remains diagnostic and grants no production
admission. The compiler also checks successfully without the verify feature.
Whole-workspace formatting, documentation and gate orchestration checks pass.

All required heavy jobs run sequentially under the exclusive host lease with
two Cargo jobs, 16 GiB process-group RSS ceilings, zero grace and 1,200-second
Cargo deadlines. Native CLI commands use 120-second deadlines; independent AY
and Clean use 180 seconds, with Clean capped at 8 GiB. Quality checks use 4 GiB.
The external floor harness imports the maintained target inventory and parser
and adds RSS supervision. Source and tool identities remain held throughout.

Every stored and decoded artifact is checked against the inventory's SHA256 and
length. The archive includes failed and successful runs, every native oracle,
object and executable, proof sidecars, exact independent certificate mutations,
commands, harnesses and the combined source patch.

All complete-system L01–L14 requirements remain open. This closes the bounded
leaf arithmetic export gap; production calling frames, ownership/provider
contracts, arbitrary memory, full proof composition, self-hosting and complete
runtime/performance qualification remain unfinished. The Rust source/body
checker remains part of the trusted base. No signed release or fully
Trust-verified build is claimed.
