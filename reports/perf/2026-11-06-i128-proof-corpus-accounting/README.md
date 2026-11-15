# Correct the inherited i128 proof-corpus count, 2026-11-06 UTC

The real required CG landing train found a stale static total: the actual
`ProofDatabase::new()` contains 2,507 obligations while its guard pins 2,504.
Correct that single total after measuring both complete runtime inventories.
Keep the five-name capacity-pending allowance, all formulas, registrations,
solver/checker budgets, evidence requirements and proof grades unchanged.

The maintained `proof_database_inventory --format tsv` example ran through
normal genuine Trust 16387 Targo, separate owned sources and fresh targets:

| Input | Exact revision | Unique names | Arithmetic | Exit | Seconds |
| --- | --- | ---: | ---: | ---: | ---: |
| Historical pre-8ee1 source, original IR f468 / Clean fd856 graph | `e74f215c611e6df19eba6cb3bda6765af9db5c46` | 2,504 | 52 | 0 | 221.598 |
| Candidate source, declared IR 3e3f / Clean c636 graph | `9d670fa3c3956bdf54d3d7d35a3b8f76ed77e3f3` | 2,507 | 55 | 0 | 231.689 |

The measured current tree was byte-identical to the active train candidate
`4f6869891825f69e34a2d427b76379a089aa48d6`. Both inventories preserved their
source and locks throughout their measurements. The exact comparison adds only these names, with no removals
or changes to any existing TSV row; every other category count is unchanged:

- `CheckedSmul_I128 overflow flag -> division-free limb check on the magnitudes (x86-64: unsigned core + sign check; exact 256-bit signed product)`
- `CheckedUmul_I128 overflow flag -> constant-operand limit compare (x86-64: the other operand >u (2^128 - 1) / C; exact 256-bit product high half)`
- `CheckedUmul_I128 overflow flag -> division-free limb check (x86-64: two I64 CheckedUmul + carry + both-high test; exact 256-bit product high half)`

Git primary source traces the two limb checks to `8ee1a205e7a88b6bb28134d3ad21ed4baef92b77`
and the constant-limit check to `a310b4f801b0e69296a013ada1ebb4477a3f982b`.
Those commits already expanded the exact per-family guard from three to six
forms but left the whole-database count unchanged. All four input limbs and
full 128/256-bit equations remain intact. A TSV inventory does not establish
formula equivalence or prove that unchanged names retain identical equations.

The old exact failed control was executed from the existing train binary and
retained its actual 2,507-versus-2,504 assertion and exit 101. In this separate
owned checkout the sole Rust edit is `2_504` to `2_507`. The maintained exact
`solver_capacity_pending_allowlist_is_narrow_unique_and_live` and
`checked_mul_i128_corpus_addition_is_exact_live_and_nondegenerate` controls then
both pass, each as one selected test, source unchanged, total 8.726 seconds.
The family control binds every registered form to its real producer and keeps
all six forms outside the five-name pending allowance. No aggregate-native
suite or solver campaign was repeated for this accounting correction.

The active original train and its actual full-database campaign were not
modified or restarted. Its final mathematical verdict remains a separate
required result; this correction grants no proof, attestation or release
qualification. Preserve every original failure and any later proof refusal.

The [artifact manifest](artifact-manifest.json) binds both complete TSVs,
commands/environments/source hashes, actual results, old failure, exact patch,
focused logs and the relevant old/current source. The original immutable
receipts remain in their recorded owned areas. No stock Rust, injected extern
metadata, dependency substitution, extra assumption, relaxed denominator or
capacity exception was used. The ordinary landing train still owns publication.
