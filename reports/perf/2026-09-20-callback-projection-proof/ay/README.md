# Independently checked shadowed array writes

A saved byte that is overwritten by a later write at the identical index has no
effect on an array's final contents. AY now recognizes bounded chains of this
identity and exports a derivation using standard `arrays_ext`, `arrays_idx`,
`arrays_row`, `cong`, `trans`, and propositional rules. The surviving writes keep
their original order: distinct index terms may alias. Both chains must share a
base and the same ordered final writes, and all store signatures are checked,
including overwritten stores. At least one overwritten write must be removed.
The base may be an opaque array-valued application.

The native schema is bounded to 128 writes per side and independently metered.
Proof export bounds its source rendering and document size; strict publication
shares a 64 MiB work allowance across the proof's shadowed-store render attempts.
Fresh-choice binder collisions, changed source spellings and exhausted budgets
keep the conservative refusal. The authored reconstruction authenticates every
assumption and replays the candidate through the native strict checker. The
wire-capability screen invokes the actual bounded exporter.

Qualified maintained stock Rust 1.97.1 export source tree `a8eaff13e7fbde66bc7b78d8a3dfa739b3ae7337`, based on clean
incoming main `10077b6c88d5aa6e0ff24324c4d2e2eeed454675`. The committed test documentation then
replaces five stale comment lines describing the former hole. The archived
post-export patch and a byte comparison after removing doc-comment lines verify
that executable Rust source is unchanged. The complete proof library passes
**2738 tests**, with 0 failures, 0 filtered and the one existing external-corpus
harness ignored (`CBB_SMT2_DIR` required). Focused native tests pass 14/14.
Strict solver tests pass 3/3: both conditional callback projection widths return
UNSAT; changed values, order and missing writes return SAT; the unsupported
choice-binder collision stays UNKNOWN. Additional solver regression methods:
store-permutation **10**, authored bridge
**35**, proof artifacts **78**,
all with 0 failures/0 ignored. These selections overlap the focused tests; this is
not a complete solver-library or workspace qualification.

Frozen independent Clean accepts **19 certificate packets**
and rejects **95 corruptions** (hole, missing empty clause, wrong extensionality
rule, missing row premise, and changed problem). These include both unchanged
original conditional callback public-input queries with their original
zero-argument definitions and entry guards. The 32-bit and 64-bit certificates
prove equality of the projected memories. Standalone symbolic, uninterpreted-sort and opaque-base
cases, an exhaustive two-element array model with index aliasing, malformed
sorts, order/value/base changes,128/129-store boundaries, source overrides and
resource-poll refusals are covered.

The archive retains earlier failures: incorrect test sort constructors in the
first build; a deliberately bounded but too-small initial raw-text allowance
on the larger projection; an existing bridge test that still expected the old
unproved hole (updated to require the checked derivation, with independent
uninterpreted-sort replay coverage); an external packet-selection harness that accidentally
selected an archived mutant (the anchored filename correction and successful
rerun are both retained); and a quality attempt refused by the already-held
host resource lease. The earlier eight small certificates also replayed, with
40 corruptions rejected. None of these preliminary runs is substituted for the
final candidate qualification.

Commands run serially with an exclusive host resource lease and anchored
16 GiB process-group RSS supervision, zero grace, two build jobs and one test
thread. Source inventories, binary hashes, exact certificates, logs and
supervisor receipts are retained. Executable payloads remain local. All stored
and decoded archive SHA256 values are rechecked.

Quality comparison preserves the clean incoming main's inherited failures.
Only this repair's growth is added to the five existing file ceilings and two
function ceilings. It does not absorb earlier overages. The global gate remains
red: `GATE FAILED: 14 waiver failure(s), 239 file-baseline failure(s), 250 function-baseline failure(s), 0 unsafe-baseline failure(s), 99 construct-baseline failure(s), 2 disabled-test attribute(s), 1 env-flag ratchet mismatch(es).`. The assessment records the full diff.

This proves one component of the conditional callback model. It does not prove
callback private-memory preservation/noninterference, allocation validity,
restored registers, returned cell values, or the whole public-memory result.
There is no new compiler admission receipt, source-to-native memory/world
composition, qualified release CLI, installation, or whole-system completion
claim. The currently installed compiler and solver are unchanged.
