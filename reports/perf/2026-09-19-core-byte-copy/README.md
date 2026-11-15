# Typed frontend copies and canonical Copy dependency adoption

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The actual Rust bridge now represents thin typed-reference/raw-pointer address
extraction with `Cast(PtrToPtr)` retaining the original source type. Its existing
same-width integer reinterpretation remains `Cast(Bitcast)`. Exact `Copy` typing
is not relaxed. Fat pointers, Rc, reversed casts and unrelated conversions are
unchanged and remain subject to the validator. The typed output diagnostic
checker follows the explicit RefMut-to-Ptr cast and preserves the original
source module, actual lowered function and reference instruction bytes.

CG coherently pins TrustIR `92628062f11a1477163e82927c1b7eb236ca5f19` and
Clean `55a85e998d428606ec9745bf6ba65fd1888ea149`. The official pin transaction
now controls the verifier's two direct optional Clean dependencies as well as
all three lockfiles, the other manifests and the artifact-cache salt. The
compiled authority guard independently checks those direct dependencies and
the feature wiring. AY remains `849c19fa0382085174a6a4827739681f059b4615`.

Qualified source is the retained patch on `a79466c8871b3445f51f4f9abf48d6c0a9ce7eea`, index tree
`28da17de95a96998fa4ed450e86768a595c19fcf`. Final CG checks passed with zero failed or ignored tests:

- 3 bridge-copy integration tests invoking the production normalizer.
- 24 output-memory diagnostic regression tests.
- 6 canonical ByteV1 Store/Return kernel replay tests, retaining ten proof DAGs.
- 4 compiled dependency-authority tests during the successful pin transaction.
- 57 Python pin-transaction tests, plus formatting/documentation/diff checks.

The new integration checks the five real captured reference extractions at O0
and O1, exact types/operands/metadata, idempotence, four typed thin-pointer forms,
the existing integer reinterpretation, nine unchanged/invalid conversions,
actual adapter lowering and ten forged-cast refusals. Reference instruction
words are diagnostic fixtures; this test does not claim the Rust backend
emitted them. The Store/Return gate requalifies its existing 12 accepted and
33 refused cases against the new dependency family; it still has no conversion
to native-publication authority.

The genuine sealed Trust a62 backend build passed in 447.93 s.
Its exact compiler, backend hash, build command, source fingerprint and finite
16-GiB process-group ceiling are retained. It uses the explicit unverified
frontend development lane; the backend's proof-enforcement policy is unchanged.
Building the library alone supplies no Rust writer admission or native-call
credit. The installed toolchain was not replaced.

Earlier failures are retained. The first integration incorrectly expected the
O0 module to become wholly valid after repairing Copy. Its five bounds claims
also lack certificates and instruction sites, so 15 independent validation
errors correctly remain. The final test checks those exact refusals rather
than hiding them; annotation-free O1 becomes valid. The second runner used a
filter selecting zero regression tests and was rejected by its denominator
guard. The corrected filter selected and passed all 24 intended tests.

Clean's [checked Copy dispatcher and 24 machine tests](https://github.com/alabsystems/clean/blob/55a85e998d428606ec9745bf6ba65fd1888ea149/reports/2026-09-19-core-byte-copy/README.md)
and TrustIR's [reflection, execution and 120-test qualification](https://github.com/alabsystems/trust-ir/blob/92628062f11a1477163e82927c1b7eb236ca5f19/reports/2026-09-19-core-byte-copy/README.md)
are companion evidence. This CG increment consumes those exact commits.
Reference/tuple Core reflection, correct frontend target/ABI metadata,
bounds-certificate transport and the composed source-to-native writer proof
remain open. All L01–L14 completion rows remain OPEN.

`inventory.json` records every artifact's stored and decoded hashes and sizes.
Logs, exact input hashes, patches, commands, failed runs and binary identities
are retained. Reproduce the maintained kernel gate with
`python3 scripts/check_core_byte_store.py --output /tmp/core-copy-store`, and
the bridge regression with `cargo test --locked -p trust-cg-verify --test
bridge_copy_types` using the pinned stock root toolchain. These are scoped
checks, not a full workspace or native acceptance result.
