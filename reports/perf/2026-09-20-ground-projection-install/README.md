# Installed checked ground-substitution repairs — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The active development package now includes AY's indexed-symbol soundness
repair and checked Boolean projection after ground substitution. The original
Trust letleak query returns `unsat` in both default and self-check CLI modes.
Explicit proof-artifact demand still returns `unknown`: the translated external
certificate retains an unverified step, and that admission boundary is unchanged.

## Qualification and installation

- Package: `/home/ayates/.local/lib/trust-cg/f509f707-ay61734bb9-cleaned2a80d1`.
- AY source commit `f23afa97aebcb218ac67d0a7057c51168fcd14a3`, frozen production
  tree `61734bb99da8ebf401d2b6935b338e7d7f6ce50f`; binary SHA-256
  `a02bce390a38ed168c697189ae1328d5e6b3c112b933ce508e61c810c6aec5fe`.
- The stock Rust release build passes in 616.31 seconds, with a measured peak
  process-group RSS of 6,373 MiB and unchanged exported inputs.
- All three CLI publication modes pass against that exact frozen release.
  All return exit zero; the expected answers are `unsat`, `unsat`, `unknown`.
- All **246 package preflight commands** pass before activation. These repeat
  the [previous installation's](../2026-09-20-adapter-abi-install/README.md)
  return42, select, diamond and arithmetic proof exports/native execution;
  exact-object recompilation and native execution of eighteen Rust backend
  endpoints; and 384 i128/narrow-argument C ABI calls across four optimization
  levels. The backend continues to use the explicit unverified Trust frontend
  development lane, with backend checks enabled.
- The complete required Linux AArch64 inventory passes **129 families and
  697 Rust tests**, with zero failures or ignored tests, against the staged
  package on clean source `9f29ea21170a9b258d9a1d374d45f604f8c7f4c9`. Source, dependency and tool identities
  remain unchanged. The gate's target list, environment rules and result
  classifier are used without modification. This run finishes before activation.
- The activated launcher then passes tool/hash checks, version reporting, O3
  proof export, native linking and return42 execution.

The compiler source `f509f7072657f9e48b74e40648dbd6e904cc711d`, genuine Trust
private backend and Clean checker retain their previously qualified binaries.
The current compiler workspace differs from that source only in documentation
and retained evidence, as checked before installation. The AY dependency is
the package change. Its soundness repair
preserves complete indexed operator identities; its
native proof repair
derives Boolean projection and disjunction repacking from strictly checked whole
substitution images. Native proof rules and publication authority were not weakened.
The source qualification retains 2,746 passing proof-library tests (one pre-existing
corpus-dependent test ignored) and the focused native projection checks. AY's
inherited quality-gate failures remain recorded separately; this is not an
all-gates-green claim.

The launcher at `~/.local/bin/trust-cg` and the `ay`/`clean` links select this
package. Managed discovery uses the package's `bin` prefix and injects no
proof-policy overrides. Previous packages remain available. All heavy commands
run serially under the anchored 16 GiB process-group RSS guard with zero grace;
Cargo uses two build jobs and one test thread.

Complete build/CLI/preflight/floor/smoke logs, proof packets, fixture objects,
tool identities, resource records and harnesses are in this archive. Prior
compiler/backend build provenance and reusable fixture sources remain in the
linked previous installation report. Large tool binaries are identified by hash.
The first nested floor launch refused to start because the preflight installer
still held the exclusive host resource lease. No floor tests ran and no package
was activated by that failed launch. The standalone floor runs after that
installer exits; a separate continuation rechecks the qualified source, tools
and previous launcher before activation. Both the failure and the passing
continuation are retained.

This is a local development installation, not a signed release, a fully
Trust-verified frontend or a verified self-host. External letleak proof export,
native source/callback/frame composition, broader ABI/runtime support and
Darwin qualification remain open. All L01–L14 requirements remain OPEN;
the closure ledger still has 205 unresolved gaps.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-ground-projection-install
```
