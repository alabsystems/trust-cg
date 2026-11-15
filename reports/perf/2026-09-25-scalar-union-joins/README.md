# Preserve scalar union field indices across branch joins

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Selecting between two `MaybeUninit<u64>` values in a generic Rust function
failed code generation: a predecessor supplied an integer to a join parameter
typed as an empty struct. The union layout correctly omitted zero-sized fields,
but uniform union binding then numbered the remaining fields from zero. That
attached the payload to `MaybeUninit`'s `uninit: ()` field. Binding now uses the
original field indices retained by the layout. The existing uniform-carrier
admission checks and downstream type validation are unchanged.

The small local generic reproducer fails on the original backend and compiles
with LLVM. The preceding hint-based reproducer emits the same diagnostic for a
helper that is ultimately dropped as unreachable, so its exit zero is not a
hard compile-failure reproduction. Both records are retained.

## Native qualification

Base source is `a8a9eb0002cd7b4c6fe921c41ab8f2b8682a7749`; the third
qualification binds the exact changed source, genuine immutable Trust compiler
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, private SDK and backend bytes.
The private bridge all-targets check, actual dylib build, Cargo test discovery
and named regression pass. Its first qualification failed on a format-string
brace in the new fixture generator; that failed source and log are retained.
The second qualification passed; the third repeats qualification after formatting
the changed binding statement. The maintained root format gate passes, and all
changed test files pass formatting. The private library has pre-existing
formatter differences: the retained base/current comparison requires the exact
same edits on both versions, with no new formatter differences.

The maintained test compares thirteen functions at O0, O1, O2 and O3, using
both LLVM and CG. Five functions select initialized `MaybeUninit` values with
u32, u64, i64, f32 and f64 payloads. Eight functions exercise both scalar fields
of unions with leading, middle, trailing and no zero-sized fields. Ten bit
patterns on each operand and three runtime flags produce 3,900 calls/checks per
execution, 31,200 across eight native executions. C observes exact result bits,
including signed zero, infinities, NaNs and high integer bits. Every object,
executable, source and command log is archived; real Rust runtime support is
linked without symbol stubs. The backend digest is checked throughout.

This regression explicitly uses `no-proof-certs` and an unverified frontend.
It establishes bounded native behavior, not proof admission. The separate
proof-required ABI test remains required and open. Only this named regression
was selected: one passed, zero failed/ignored, two other tests filtered out.

## Full core diagnostic

The unchanged original `library/core`, `stdarch` and `portable-simd` sources
come from the exact compiler revision above. LLVM compiles the entire core
source successfully. CG's second diagnostic reports 61 failed roots and
retains 3,386 emitted objects. The third and fourth repeat the complete source and options
with the repaired backend, before and after that formatting correction:
60 failed roots remain in each. The sole removed failure is
the `select_unpredictable<MaybeUninit<usize>>` branch mismatch; the other sixty
diagnostic entries are byte-for-byte unchanged. Full raw logs, all failed-root
names and emitted objects are retained. Partial object counts are not a count
of proved functions or successful whole-library builds.

The first diagnostic used an incorrect comma separator for the backend knobs
and stopped before CG compilation. The corrected runs use the required single
space-separated argument. That harness failure is preserved. The three CG diagnostic attempts after the first syntax failure
use `no-proof-certs` and an unverified frontend: this is a failure inventory,
not completed core self-hosting, a completed release gate or system completion.

`manifest.json` and `inventory.json` bind compressed and decoded records;
`assets.json` hashes every tar member. `excluded.json` identifies rebuildable
backend/runtime archives by hash and size; generated native artifacts and all
qualification failures are retained losslessly.
