# Original-module verification receipts and JIT cache binding

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Status: PASS for the twelve recorded commands, 64 Rust tests and the verifier-disabled compile check. This is source custody and cache attribution, not a new source-to-machine theorem or complete compiler acceptance.

## Change

AArch64 compiler verification now borrows both the original TrustIR Module and the Module supplied to the LIR adapter. A private, exact lossless binary digest binds both endpoints into captured reports and the JIT verifier-input/cache identity. Source-bearing reports cannot match a legacy LIR-only request. The original/lowered pair survives dialect lowering, per-function proof export and the JIT continuation. This adds no proof credit and does not infer callback memory contracts, dialect correctness or linked-code authority.

Tests retain caller/callee calling-convention, read-only attribute, parameter-type, vararg and target-name mutations on each endpoint with unchanged LIR/machine inputs, plus distinct NaN payload bits. The real cached compiler campaign requires two misses when only the original module changes, two hits on repetition, and two hits when the original source is restored. Existing source and raw-machine negative controls remain required.

The same qualification exposed frame omission for constant-returning scalar leaves. The frame policy now retains the supported source-bound envelope for scalar constants, register copies and conditional returns, as it already does for identity-only and affine arithmetic bodies. Direct frame-policy controls and the existing real encoder/source-frame tests cover this repair.

Code commit: `b488c3cc1` (qualified Rust sources unchanged from the retained patch). Preserving these leaf frames can add the standard sixteen-byte frame and save/establish/restore instructions relative to frame omission; performance qualification remains separate.

## Qualification

The final commands use a fresh checkout-specific Cargo target directory, stock Rust 1.97.1, locked/offline dependencies, two build jobs and one test thread. Each command has an exclusive host resource lease, a zero-grace 16 GiB RSS limit and a 1,200-second timeout. All twelve commands pass with unchanged source fingerprints and no selected ignored/skipped tests. The real-tool campaigns use the exact installed AY and Clean identities retained under `identities/`; the package itself is unchanged.

The qualified source is `17cbab2a86933a4d3a7873938cffcefd388ef023` plus the retained tracked patch and two new source files. Its fingerprint is `26cdd2e4272c753c91d2b8752c4305f0cfcbed7ce454ac0597344f6fa1e82cd5`. Complete commands, outputs, resource observations, source/tool identities and resulting test-binary hashes are retained. The immediately preceding clean-main [127-family regression floor](../2026-09-20-linux-complete-callback-floor/README.md) passed 692 tests; that earlier source run is not a whole-floor qualification of this patch.

## Preserved failures

The first coordinator selected the explicitly ignored raw-cache campaign without `--ignored`; it rejected the zero-test result. The corrected invocation then exposed an inherited stale assertion: SXTH's one 16-bit input now receives exhaustive credit within the existing 65,536-tuple budget. The same assertion fails on unchanged main `6e86e6318247f1f84a0c4c3b6baeaad2045a46f1`. The repaired test keeps SXTH as a positive boundary control and uses the real 32-bit NEG input as the statistical, non-reusable receipt control; verification policy is unchanged.

The real high-level native campaign also failed identically on unchanged main: the zero-storage optimization omitted the constant-return leaf frame, invalidating its required formal source-frame coverage. The separate unchanged-main encoder/source-frame suite also fails three tests for constants, parameter copies and conditional diamonds. The first repair handles constants/copies but retains the diamond failure; the final repair covers the conditional return forms too. The fix preserves that evidence-bearing envelope; it does not remove the campaign's formal-frame, stale-source or raw-source controls.

A diagnostic rebuild after switching checkouts reused stale verifier artifacts from the shared Cargo target and failed to find the newly added APIs. The final fresh-directory rebuild eliminates that contamination and reruns every selected case. The first arithmetic integration invocation omitted the managed package prefix from PATH, so Clean discovery could not find the installed checker. It produced provenance failures and was cancelled through the resource guard; the cancelled record is retained. The remaining integration/build commands use the installed package prefix, matching the preceding Linux floor and keeping exact tool identities. The earlier failed commands and logs remain archived under `prior-attempts/`.

## Limits

This record closes neither L01–L14 nor the open source-to-byte calling-frame work. Whole conditional callback models have external independently replayed certificates, but native proof production, justified external premises and production admission remain separate unfinished work. No installed executable was replaced and no statistical evidence was promoted to Formal.
