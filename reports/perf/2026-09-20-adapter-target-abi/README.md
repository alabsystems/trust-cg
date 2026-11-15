# Explicit adapter target ABI and prepared Swift rewrite custody

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Result: **PASS** on clean code `c6d2228c62ca174b3546df00c6cda1544c1de82c`: **129/129 required Linux families**,
**697 Rust tests**, zero skipped/ignored/incomplete required executions.
The separate targeted qualification passes **29 tests**, including **384 native
C calls at O0–O3**, and retains the failing unchanged-main reproduction.

Direct and indirect AArch64 calls now classify arguments with the driver-selected
object target: Darwin for Mach-O and AAPCS64 for every supported ELF TLS model.
The boundary fixture covers four signed/unsigned narrow types, two call forms,
two register-pressure cases and five object modes (80 translations). On unchanged
main, an `i8` after `i64`, `i128` and four `i64` arguments is incorrectly widened
to `i32` for ELF. It now retains its narrow stack type; the Darwin register case
and the lower-pressure controls retain their extensions. AArch64 calls under an
unsupported object target refuse classification. Non-AArch64 adapter behavior is
unchanged and is not qualified by this repair.

This boundary follows the distinct pair-alignment rules documented by
[Arm AAPCS64](https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst)
and [Apple's ARM64 calling conventions](https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms).
The native oracle uses the recorded Linux C compiler at O2, checks every argument
including both halves of the i128 and adjacent narrow stack arguments, and crosses
C → generated wrapper → direct/indirect C callee at all four compiler tiers.
This is execution evidence, not a semantic proof for arbitrary calls.

Swift aggregate scalarization is restricted to its witnessed Darwin AArch64
contract. Its fit check takes an explicit ABI. A prepared rewritten owner records
that ABI and rejects reuse under ELF or an unsupported target. The new explicit
preparation API selects the driver's object target; the legacy wrapper retains
its documented Mach-O default. Target-independent preparation remains reusable.
Unsupported Linux Swift aggregates are refused; Linux Swift aggregate support
and native Darwin qualification remain open. Both new test families are required
by the Linux and Darwin inventories.

The gate unit checks also found an inherited Darwin inventory omission for five
Linux families. Four portable families are now required on Darwin; the Linux-only
bounds-trap family is recorded as uncovered. Both unchanged-main and initial
candidate unit failures are retained. The final gate unit run is **59 passed,
1 existing host-specific skip** (the non-/proc supervision case); this is separate
from the zero-skip Linux compiler regression floor. Darwin's declared inventory
is now 167 families and a 1,147-test minimum, not a Darwin execution result.

The first two baseline attempts omitted required target information and stopped
at canonical input validation. The third baseline reached the actual ABI failure.
The first candidate run then exposed a fixture lookup error: unchanged parameter
types live on block parameters rather than in the produced-value type map. After
repairing that lookup, the exact final predicate failed again on unchanged main
and passed on the candidate. All attempts are retained; none is discarded or
counted as successful compiler qualification.

Stock Rust 1.97.1, locked offline dependencies, two Cargo jobs, one test thread,
an anchored 16 GiB RSS limit with zero grace and a 1,200-second deadline per
command were used. Full-floor source, dependency and tool identities match before
and after. Focused library tests intentionally filter unrelated unit tests; the
129 required integration families run whole targets. Exact commands, logs,
source patches, fixtures, guard records, binary hashes and harnesses are retained.
The installed development package is unchanged by this report. No L01–L14 row
is closed and no verified frontend or self-hosting claim is made.
