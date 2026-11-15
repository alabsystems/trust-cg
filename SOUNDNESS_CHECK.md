# Local soundness gate

`scripts/soundness_check.sh` aggregates trust-cg tests with checks from sibling
Clean and AY repositories. It is a local evidence gate: it helps reproduce a
particular cross-repository validation state, but it is not hosted CI and it is
not an end-to-end proof of the compiler.

The script fails closed when a configured check is missing, vacuous, errors, or
returns a nonzero status. Known RED opcode-evidence rows are pinned data inside
the passing coverage inventory; an unknown/unclassified RED row fails that test.

This gate runs a configured set of legs, not the whole test inventory. The
per-host full test matrix (docs/testing/full-test-matrix.md)
runs every Darwin-required root-workspace suite with the same strict proof
gate (`scripts/check_proof_gate.sh`) and the `TRUST_CG_RUN_FORMAL_PROOF_TESTS`
campaign, and records the AY and Clean it resolved; neither record substitutes
for the other. On the macOS arm64 host of its
first record that
strict gate fails with the installed Trust package's AY (477 of 2,503
Verified) and with a development AY/Clean overlay (2,294 of 2,503), with zero
counterexamples: AY's own strict self-check rejections, incomplete
certificates and `incomplete` answers, three timeouts and six AY proofs the
managed Clean rejected leave it a host residual there.

Downstream consumers are outside this gate as well. The Darwin
consumer lane (`scripts/check_darwin_consumers.py`,
ledger `L13-P8`) runs trust-cg's TY and AY contract targets, abi-xback in both
directions and the pinned TY repository re-pointed at the checkout under test;
it is a required stage of the Darwin full test matrix, not a leg of this gate,
and its record is testing evidence that neither replaces nor is replaced by an
attestation here.

## Run it

From the trust-cg repository root:

```sh
scripts/gate_env.sh                 # prerequisite check: prints and checks tool identities
scripts/soundness_check.sh          # census: every leg, no record
scripts/soundness_check.sh --attest # committed HEAD: fail fast, write a record
```

The gate supplies its own inputs:

- `TRUST_CG_RUN_FORMAL_PROOF_TESTS` defaults to `1`, since without the campaign
  `proof_gate_strict` reports runtime SKIPs and a SKIP fails the gate. Every
  Cargo leg, that target included, runs through `scripts/trust_cargo.sh` on the
  installed Trust package (`targo --unverified`): the verifier admits only the
  `ay` shipped in the sysroot of the compiler that built it, and trustc refuses
  to run under any `TRUST_CG_*`/`TCG_*` variable, so the wrapper keeps those
  controls out of the compiler and hands them to the tests through a Cargo
  target runner. That target reports the SHA-256 of the `ay` it executes
  (`executed_ay_identity_is_reported`), and an attestation record binds it
  to the `bin/ay` the preflight probed (see
  [Attestation records](#attestation-records));
- the Clean and AY checkouts are the gate's own detached worktrees at the
  candidate revisions (below);
- the vt-island tables are exported from `$ATERM_DIR` (default `$HOME/aterm`)
  at its `origin/main` when `ISLAND_VT_TABLES` is not given; the exported
  commit and the dump's SHA-256 are recorded.

An installed pack can lag the AY and Clean that `proof_gate_strict` needs.
Until a pack ships them, a local **overlay toolchain** stands in:
`scripts/assemble_trust_overlay.py` clones the installed pack (APFS
`clonefile`, or `cp --reflink=auto` on Linux) and puts in an AY and a Clean
built from real git checkouts. It refuses an unnumbered or dirty AY build (a
`git archive` export reports build 0) and a Clean that fails trust-cg's
control proof, for example one built without `carcara-verify`. It writes
`overlay.json`, which names both SHA-256 digests and both source commits. The
Clean commit is the checkout HEAD the assembler was given, because `clean
--version` reports no commit. `TRUST_TARGO=<overlay>/bin/targo
scripts/trust_cargo.sh test ...` then builds with the overlay's compiler.
trust-cg-verify's `build.rs` records the overlay only when the manifest names
the bytes of both `bin/ay` and `bin/clean`, and the AY identity in verdict
provenance and `--print-ay-identity` names it. `trust_cargo.sh` passes the
selected sysroot as `TOOLCHAIN_AY_EXPECTED_SYSROOT`, so `build.rs` records
again whenever the sysroot changes. Without it, Cargo would reuse one clone's
record for another, because their `trustc` bytes are identical. A build from
an overlay checks proofs only with the overlay's own `bin/clean`, with the
manifest's digest. If that checker fails the control proof or has other
bytes, verification stops loudly: there is no fallback to the package checker
or to a `TCG_EXTERNAL_CLEAN_CHECKER` override. `proof_gate_strict`'s
`overlay_build_checks_proofs_only_with_its_own_clean` checks this on the
production discovery path whenever the gate is built from an overlay. In any
build, the unit test
`obligation_cert_store::tests::the_authority_path_applies_the_recorded_overlay_pin`
runs the same discovery under a fixture overlay record. The DEGRADED banner
names the repair for the defect it found: unset an override whose bytes are
not the overlay's, restore or reassemble a `bin/clean` replaced after
assembly, or rebuild Clean with the missing feature. An overlay is not a
published pack and is not a release input.

A run records the proof tools it actually executed when
`TRUST_CG_PROOF_IDENTITY_OUT=<file>` is set: one JSON line
(`trust-cg.proof-tool-use.v1`) per distinct AY and Clean, each with its path,
SHA-256 and overlay manifest digest. Clean is recorded where it checks a
proof, so the record names the checker that ran, with or without an
overlay. For example, under pack 9192 it names `store/clean/8606`, the
checker discovery selected after skipping the pack's own `bin/clean`.
`proof_gate_strict`'s formal test `a_real_proof_check_records_the_tools_that_ran`
re-runs the representative smoke in a child process with the variable set and
a fresh cache, and requires exactly one `clean` line (the checker
`resolve_proof_checker` names) and one `ay` line (the admitted AY). No gate
reads the record yet: `scripts/soundness_check.sh`'s attestation does not
include it.

The x86-64-native legs (`x86_sse_lane_gate` and the three `e2e_x86_64_*`
targets) need x86-64 SILICON. They run locally only on a native x86-64 host,
decided by `scripts/soundness_attestation.py host`: the machine is x86-64, the
process is not translated (Rosetta's `sysctl.proc_translated`), CPUID executes
and names a hardware vendor, and neither CPUID nor `/proc/cpuinfo` shows a
QEMU/TCG CPU or an ARM CPU behind user-mode emulation. Rosetta 2 is
translation, so it never satisfies these legs (OD-34 refused option B). What
a Rosetta run of the SSE silicon anchor would be worth: the x86-64 binary's
SSE instructions execute as Apple's AArch64 translation of them, so a model
that disagreed with the translator would be caught, but not one that
disagreed with an x86-64 CPU where the translator shares the misreading, and
it says nothing about any x86-64 microarchitecture. That is evidence about
the translator, a TEST rung, not silicon. (The arm64 Mac that measured this
on 2026-10-12, an Apple M4 Max on macOS 26.6.2, has no Rosetta 2 installed:
`arch -x86_64 /usr/bin/true` fails with `Bad CPU type in executable`, no
`oahd` runs and `/Library/Apple/usr/libexec/oah` is absent; and the Trust
package's sysroot ships only the `aarch64-apple-darwin` standard library, so
the test harness cannot be built for `x86_64-apple-darwin` there without
`-Zbuild-std`.) On any other host a full run
dispatches them to `SOUNDNESS_X86_HOST` (an ssh destination) through
`scripts/soundness_remote.sh` and imports that host's record. An unset or
unreachable executor is a FAIL, never a SKIP.

The x86-64 host needs: ssh access in `BatchMode`, `git`, `python3`, the
toolchain the candidate's `rust-toolchain.toml` pins (for `channel = "trust"`,
an installed Trust package on `PATH`: a branded `trustc` with a 40-hex commit
identity and `targo` beside it), clang as its `cc` (a GCC `cc` makes
`e2e_x86_64_swiftcc` print `SKIP: (E4) NOT RUN`, XD-03), an LLVM-family
`objdump` or `llvm-objdump` (GNU objdump cannot decode both container formats
that `e2e_x86_64_callee_saved` (E2) reads, so it SKIPs), and read access to the
first-party dependency repositories Cargo fetches (`trust-ir`, `clean`, `ay`).
`scripts/soundness_remote.sh probe` checks all of these; the remote's own
preflight then runs the CPUID check. The remote clone defaults to
`~/.cache/trust-cg/soundness-remote/trust-cg`; `SOUNDNESS_X86_REMOTE_DIR`
names another, as an absolute path, as `~/...` or as a path relative to the
remote HOME (spaces are kept). Its characters must be among
`[A-Za-z0-9 ~/._+,:@=-]`; any other value (non-ASCII, a control character, a
quote, `$`, a backquote, `;`, `*`, `\`) is refused by name before anything is
sent, because bash's `%q` quotes such characters as `$'...'`, which a POSIX
login shell such as dash reads differently. Bundles travel through
`~/.cache/trust-cg/soundness-remote/incoming`.
Every directory the script creates there is `0700` whatever the remote umask
(the rule of `scripts/private_cache.py`, whose source travels with the remote
script), and an existing directory is never changed. Everything written after
that runs under umask 077: the clone (initialized, fetched and checked out),
the x86-64 legs (their build tree and Python caches in the clone, and the
record's Git objects), and both bundles. The clone is entered once, by its
physical path (`cd -P`), so the tree the script checks, the legs it runs and
the remote gate's own `TRUST_CG_DIR` name one directory whatever symlink
`SOUNDNESS_X86_REMOTE_DIR` runs through; the clone's own privacy is not
checked (the executor is trusted to run its legs). AY's private copy lives
under the same `~/.cache/trust-cg`, and under umask 0002 a `mkdir -p` there refused AY
on that host (X-HOST-P13). The phase arguments are quoted
into the one command line ssh hands the remote shell, so an unset
`SOUNDNESS_X86_REMOTE_DIR` arrives as an empty argument (the default) instead
of vanishing and shifting the arguments after it. Because of that quoting the
remote shell no longer expands a `~` in it; the remote script reads a leading
`~/` as the remote HOME itself, as before. Linux and Intel macOS hosts differ in
which container formats and C compilers they offer, so qualify a new host with
`scripts/soundness_check.sh --attest --preflight-only --host-legs x86_64-native`
on it before relying on it.

Exit status `0` means every configured gate passed. Status `1` means at least
one gate failed or could not run, including a missing-prerequisite `SKIP`;
status `2` reports invalid command-line use. A skipped prerequisite also prevents
an attestation record. The same rule applies in wasm-only mode.

Useful modes:

```sh
scripts/soundness_check.sh --list        # print the configured gates
scripts/soundness_check.sh --list-json   # every recorded leg with its host class
scripts/soundness_check.sh --attest --keep-going      # attest-mode census, no fail-fast
scripts/soundness_check.sh --attest --preflight-only  # the attest preflight alone
scripts/soundness_check.sh --help
```

By default the script derives the trust-cg root from its own location. For
Clean and AY it does NOT use the `$HOME/clean` and `$HOME/ay` working trees
as they stand, because those are other workers' checkouts: it adds (or reuses)
a detached worktree of each at exactly the candidate revision resolved from
this repository's Cargo locks, one per revision under `$SOUNDNESS_DEPS_DIR`
(default `<user cache>/trust-cg/soundness-deps`, `<user cache>` an absolute
`XDG_CACHE_HOME`, else an absolute `HOME`'s `.cache`; an empty or relative
`XDG_CACHE_HOME` is ignored), fetching the revision first if
the source repository lacks it. Every directory the gate creates there is
`0700` whatever the umask (`scripts/private_cache.py`), each checkout is
written under umask 077, and an existing directory is never changed. An
existing one another user could rename entries in is refused instead
(`private_cache.py require-private`, the rule the icmp gate holds `ay-cli`
to): `SOUNDNESS_DEPS_DIR` and its ancestors before a checkout is written
into it, and the built Clean binary and its directory before any Clean check
runs; the refusal names the directory, its mode and `chmod go-w`. Each pinned
checkout is judged as a whole tree (`require-private-tree`: every directory
and file this user's and writable by nobody else, a symlink only when every
hop of its literal target stays in the tree, LD-71), before it is used and
again after the Clean build, because Clean is built from its sources and
checks its `proofs/` in place; judging the root alone let a co-group writer
turn a failing pinned proof into an attested pass (X-HOST-P13 fourth closure
audit, LD-65). trust-cg's own proofs are not checked in the candidate
checkout under `--attest`: the gate exports `proofs/` and `formal/lean` of
the attested commit into a fresh `0700` directory below its log directory,
judges it with `require-private-tree`, and runs the inventory, the Clean
checks of `proofs/*.lean` and the lake build with its ratchets only there,
Clean and lake under umask 077. A refused export (for example below a
`TMPDIR` another user can write) runs none of those legs, and each records
FAIL. Checking them in the candidate checkout let a co-group writer turn a
failing proof into `132 total 132 passed` and an attestation record
(X-HOST-P13 fifth closure audit, LD-70). The export is
`private_cache.py export-commit`: the commit and every tree and blob below
those paths are read from the object store with `git cat-file --batch`
under no system or global git configuration, no attributes and no replace
refs, each must hash to its name from the commit id down, and the written
files are read back against their blob hashes. `git archive`, used until
then, applied the smudge filters and attributes of the user's global git
configuration, which turned a failing proof into `132 total 132 passed`
with the candidate untouched (sixth closure audit, LD-70's correction).
Everything else an attested run reads from the candidate checkout is read
in place: the gate's own scripts, the checkout's `.git`, and the Rust
sources and `target/` the Cargo legs build and run. That checkout, the
user's toolchain installs and git's configuration are the host's trust
boundary, which the run judges before it starts (see "The host trust
boundary" below, LD-73). A census run reads `proofs/` and `formal/lean` in
the working tree and writes no record. A checkout with an entry
another user could write is refused with the remedy to remove it
(`git worktree remove --force`, then the gate re-creates it private), since a
`chmod` cannot undo what may already have been written there. The rule judges canonical paths, and
`require-private` prints the canonical path it judged: the gate adds the
checkout below the canonical `SOUNDNESS_DEPS_DIR`, uses the canonical
checkout as `CLEAN_DIR`/`AY_DIR`, and runs (and records) the canonical Clean
binary, so a `SOUNDNESS_DEPS_DIR` or `XDG_CACHE_HOME` reached through a
symlink is used where the symlink led at the check. The
`scripts/tests/test_private_cache.py` case
`test_a_cache_reached_through_a_link_others_can_repoint_runs_only_the_clean_it_checked`
re-points such a symlink in a `0777` directory after the first Clean check;
all 14 Clean checks still run the checked binary (before 2026-10-15, 13 of
them ran the substitute and the run was green). The
Clean lane (its Cargo builds and tests, and `clean check`) runs under umask
077 in whichever Clean checkout it uses, so what it creates in `target/` is
private too; a file a build script copies keeps its source's mode (three
`0644` zstd-sys headers, below `0700` directories; LIMITATIONS.md).
That directory shares `~/.cache/trust-cg` with AY's private copy, which is refused
while any ancestor is group-writable: under umask 0002 a plain `mkdir -p`
made `~/.cache/trust-cg` `0775` and refused AY in every later process
(X-HOST-P13). `$HOME/clean` and `$HOME/ay` are only the
source repositories; `CLEAN_SOURCE_DIR` / `AY_SOURCE_DIR` name others. Setting
`CLEAN_DIR` / `AY_DIR` runs a census against those checkouts exactly as given
instead; `--attest` refuses that, because the record must bind the revisions
the candidate's locks name:

```sh
CLEAN_DIR=/path/to/clean AY_DIR=/path/to/ay scripts/soundness_check.sh
```

The root workspace pins the Trust toolchain in `rust-toolchain.toml`, and
every leg builds in `targo`'s explicit unverified lane, so nothing this gate
checks was itself compiled with Trust verification on, and no such claim is
made. The gate resolves that package (`scripts/trust_toolchain.py`) and
rebuilds `$CLEAN_DIR/target/release/clean` from the selected Clean checkout
with the same package, its locked dependencies and `clean/carcara-verify`
enabled, matching the checker capability in aterm's package recipe. This is a
development build, not installation or publication of a managed package.
Proof-file checks still run against the newly built executable, not a stale
previous binary.
Each Cargo test, Clean build/check, and Lake build runs in a separate process
group with a 7,200-second default limit. Set the positive
`SOUNDNESS_COMMAND_TIMEOUT_SECONDS` environment variable to use another
per-command bound. Timeout or interruption fails the gate and terminates the
whole process group, including descendants that remain in that group.

### Prerequisites and the shared environment prelude

`scripts/gate_env.sh` is the repository's gate environment prelude; this gate
sources it. For this gate it puts `$HOME/.elan/bin` first on `PATH`; the Rust
toolchain is the installed Trust package already on `PATH` (no rustup proxy
directory is prepended). Interactive shells can use
`source scripts/gate_env.sh` (bash or zsh). Sourcing changes only `PATH` and
runs no check.

Running the script directly checks the host before a gate run. It records the
identities it resolves in the log, and each failure has a named `GATE_ENV_*`
code with exit status `1`:

- `rust-toolchain.toml` must pin `channel = "trust"`, and the PATH `trustc`
  and `targo` must be one installed package (atpkg launcher shims followed): a
  branded `trustc` with a 40-hex commit on an `aarch64-apple-darwin` or
  `aarch64-unknown-linux-gnu` host (`--allow-x86_64-host` also accepts
  `x86_64-apple-darwin` and `x86_64-unknown-linux-gnu`; the gate passes it on
  a native x86-64 host), and a package `targo` that accepts `--unverified`
  (upstream cargo shipped under the name rejects it); the package file
  answers, never the shim.
- The Lean toolchain pinned by `formal/lean/lean-toolchain` must be installed
  for the `lake build` leg. When it is absent, the script prints the
  re-provisioning recipe and publisher digest recorded in the
  2026-09-10 prerequisites report.
  It never runs elan's `lake` proxy, which could start a network install.
- rustup's `trust` link and the `trustc` found on `PATH` (or, failing that,
  in aterm's managed package) must be one toolchain: the same root, or a copy
  carrying the same 40-hex commit and byte-identical `bin/trustc`, `lib/` and
  `libexec/`. When they differ, the
  script refuses with `GATE_ENV_TRUST_TOOLCHAINS_DIVERGENT` unless
  `TRUST_CG_TOOLCHAIN_LANE=rustup` or `path` names the one the run uses. Set
  that variable on the `scripts/gate_env.sh` command line only. Trust
  compilers refuse any `TRUST_CG_*` or `TCG_*` variable as an untracked
  codegen control (every invocation except `-vV`), so the script probes their
  identities without those variables and warns when any are set.
- The aterm-managed `ay` and `clean` are resolved through `aterm pkg which` or
  the package store, and their versions are printed. A managed or
  `AY_SOLVER_PATH` AY whose version differs from the `ay-pb` pin in
  `crates/trust-cg-regalloc/Cargo.toml` produces a loud
  `GATE_ENV_AY_PIN_MISMATCH` warning. The script never switches solvers;
  `--require-ay-pin` makes the effective solver's mismatch a failure.

The script installs, relinks and selects nothing, and it enables no Trust
verification. Its probes set `RUSTUP_AUTO_INSTALL=0`, so a missing rustup
toolchain is reported rather than downloaded. A PASS records an environment. It
is not soundness evidence. `python3 -m unittest scripts/tests/test_gate_env.py` runs
its regression tests against fake tool directories. A full soundness run's
preflight runs it as `TRUST_CG_TOOLCHAIN_LANE=path scripts/gate_env.sh
--require-ay-pin`, the PATH package `scripts/trust_cargo.sh` builds with, so an
effective AY that is not the `ay-pb` pin version fails the preflight.

## Configured checks

The package-integration inventory also requires the complete
`trust-cg-codegen --test aarch64_elf_symbol_binding` target. On Linux AArch64
GNU this includes its original83tests and33native tests, including weak
function/data null-on-missing and present-definition controls at O0–O3.
Other hosts run the tests their configuration actually compiles; the omitted
Linux native module supplies no Linux execution credit there. Missing native
linker legs, ignored cases, runtime SKIPs and incomplete summaries prevent a
passing Cargo leg. This functional/object target supplies no new proof grade.
Explicit `TCG_RETAIN_TEST_EVIDENCE` retains native child artifacts and command
records for a separately manifested qualification; ordinary cleanup is unchanged.

The trust-cg portion runs these `trust-cg-verify` integration-test targets:

| Target | Evidence checked |
| --- | --- |
| `coverage_gate_tests` | Accepted/deferred opcode inventory: AArch64 267/302 with 35 RED rows, all deferred models (the 302 include scalar ADDP, credited by its obligation although no lowering selects it yet). The 46 single-instruction atomic rows (`LDAR`/`STLR` x3, `CAS` x4, `SWP` x4, `LD<op>` x32), the 18 scalar memory rows (`LDR`/`STR`/`LDRB`/`LDRH`/`LDRSB`/`LDRSH`/`STRB`/`STRH` immediate and register offset, W/X pre/post-index writeback; their H/S/D/Q forms judged by the exact word-bound memory-effect decomposition) and the six pair rows (`StpRI`, `LdpRI`, `StpPreIndex`, `LdpPostIndex`, `NeonStpQPost`, `NeonLdpQPost`) and the two NEON `LD1`/`ST1` post-index rows (`NeonLd1Post`, `NeonSt1Post`: seven arrangement forms each, `aarch64_neon_structure_forms`) are credited by `bound_memory_row_credit` only when EVERY legal form of the opcode has a committed form-theorem certificate that the vendored independent `drat-trim` replays in process (the bound-memory set, or the separate atomic-memory set `verdict_db/atomic_memory_certs/` or NEON set `verdict_db/neon_memory_certs/`), representative instructions are credited through the Formal-only rule's clauses 2-4 and every machine defect is refuted in process; the six volatile rows follow their plain rows. The RED rows include FRINTN, the three emitted ELF TLS-descriptor slots `LdrTlsdesc`, `AddTlsdescLo12` and `BlrTlsdesc`; the 29 LL/SC atomic rows (the ten single-register and four pair load/store-exclusive forms, `Clrex`, the twelve opaque `LlscRmw*`/`LlscCmpSwap*`/`LlscLoad128`/`LlscStore128` pseudos, `Ldaxr` and `Stlxr`); and `AddTprelHi12`/`AddTprelLo12`, because the TLSLE relocation-arithmetic identities bind no register, word or relocation site (ENC-5 decodes those words, which is emission redundancy and binds no obligation). The eight FEAT_CRC32 forms `Crc32B` through `Crc32Cx` (selected only in a function whose admission includes `crc`) are credited by the CRC32 decoded-word family `aarch64_crc32_proofs`: each form's re-derived word, decoded independently and given its Arm ARM pseudocode (`BitReverse`, `Poly32Mod2`, `BitReverse`; `Xd[63:32]` cleared), equals the reflected least-significant-bit-first CRC intent of the operands for every register value, decided in process by GF(2)-affine evaluation (`gf2_affine_decide`), every word, width, polynomial, operand, bit- and byte-order control refutes, and ENC-5 requires the emitted word to be the re-derived one; this is testing-grade evidence, and the function verifier reports a holding CRC32 instruction unverified. `SubsRI` (the looped stack probe's `SUBS X16, X16, #1`) is credited the same way by `aarch64_subs_imm_proofs`: for both widths the destination value and N, Z, C, V of the decoded word (Arm `AddWithCarry(Rn, NOT(imm), 1)`) equal the operands' difference and comparison flags, each decided for every register value by the bit-serial automaton, with ADDS, SUB, width, shifted-immediate, off-by-one, register and flag-meaning controls refuted. FCMP, CSET, CSEL, CSINC and CSNEG are credited by the per-instruction NZCV producer/consumer family `aarch64_flag_consumer_proofs`, bound to the reaching flag producer, so no row lacks a mapping; the four half-precision FCVT forms are credited by decoded-word obligations comparing the Arm ARM `FPConvert` transcription of each captured word with an independent IEEE 754 `convertFormat` intent (`aarch64_fcvt_half`); `Movk`/`Movn` are credited by a form-polymorphic gate that demands the already-bound per-form obligation of EVERY legal (width, shift) pair, failing closed on a missing, duplicated or illegal form. The five conditional trap carriers (`TrapNullIfZero`, `TrapDivZeroIfZero`, `TrapBoundsCheckExact`, `TrapShiftRangeIfOOB`, `TrapOverflowExact`) are credited by the trap-expansion family `aarch64_trap_expansion`: each modeled form's stated compare/branch/`BRK #1` expansion traps exactly when the carrier's source condition holds, decided in process (a bit-serial automaton over every input; sound rewriting for the 64-bit multiplications), and every corruption control (inverted condition, wrong `BRK` immediate, branches around the trap, off-by-one bound, wrong register or width) refutes. `MovR`, `FmovFprFpr`, `FmovFprGpr`, `FmovGprFpr`, `Smull`, `Bfm`, `Rbit`, `AddRIShift12`, `Mrs` and the typed post-allocation copies `MOVWrr`/`MOVXrr` (emitted by `lower_copies`, each instance bound per form by the function verifier; the `NeonOrrV` row needs both the `ORR Vd.16B, Vn.16B, Vn.16B` copy's decoded-word form and the lanewise ORR obligation the three-register 16B OR binds) are credited by `aarch64_value_decode_proofs`, which gives each emitted form's CAPTURED encoder word an INDEPENDENT Arm ARM decode and pseudo-code semantics over the whole destination register, compared with the machine-IR intent — exactly, as a bit routing, for the copies, RBIT, BFM instances and MRS, and by sampled evaluation for SMULL, the symbolic-field BFM and the shifted ADD — with every negative control refuted for its stated reason; the target re-derives that capture from the live encoder. x86-64 206/206 with 0 RED rows. The five ZERO-EXTENDING loads (`MovzxRM8`, `MovzxRM16`, `MovzxRM8Sib`, `VolatileMovzxRM8`, `VolatileMovzxRM16`: `movzx r32, m8/m16`, the selector's load for every byte and word) are credited by the byte-level address lane, whose SDM decoder reads their `[REX] 0F B6/B7 /r` bytes for the address and for a DESTINATION-WRITE facet (the decoded production's register write, per SDM Vol 1 3.4.1.1, against the access value zero-extended to 64 bits, over dirty old registers and set top bits; a merging `mov r8/r16, m`, a sign extension and the other access width refute through the same comparison, inside the credit hook), together with the MemLoad value reconstruction; `x86_addressing_gate` re-derives the corpus from the live encoder, sweeps every destination, base, index and scale, and checks the destination models against this CPU. `AtomicLoadCmpxchg16b` (the 128-bit atomic-load pseudo: four zeroing `XOR`s and `LOCK CMPXCHG16B`) and the narrow `Cmpxchg8`/`Cmpxchg16` rows are COVERED JOINTLY: the address by the byte-level address lane (the narrow rows' reconstruction refutes no address error), the value by a per-instruction reconstruction — for the 128-bit load, the whole expansion over arbitrary incoming registers against the trust-ir `AtomicLoad` plus the bare CMPXCHG16B transcription against the trust-ir `CmpXchg`, eleven facet equalities with per-facet non-degeneracy; for the narrow CAS, the AL/AX-partial-accumulator facets the i32/i64 CMPXCHG theorems cannot express (RAX[63:w] preserved, returns-old, the conditional store, the adjacent cell and ZF) as one joint obligation with refuting controls. The ten SSE LANE rows (`Pshufd`, `Pmovmskb`, `MovdqaRR`, `Punpcklbw`, `Punpckhbw`, `Punpckldq`, `Punpcklqdq`, `Ptest`, `Pblendvb`, `Packuswb`) are credited by `x86_sse_lane_proofs`: not a per-lane same-width scalar reconstruction, but an INDEPENDENT SDM-derived decode of the real emitted bytes yielding an EXACT bit-level ROUTING denotation, compared against a PARAMETRIC statement of the machine-IR intent, so that equality of the two decides the question for EVERY input rather than sampling it. PACKUSWB's unsigned-saturating narrow is settled EXHAUSTIVELY over all 65536 inputs and PTEST's six status flags by EVALUATION over a structured witness family that reaches ZF=1, which a random 128-bit sweep never does. The WRONG HALF and WRONG ELEMENT WIDTH controls are registered and REFUTE; the degenerate `PackLowQwords` reconstruction is X==X and credits nothing. `MovRI` is credited by an INDEPENDENT SDM-derived decoder of the real emitted bytes, not a const==const model. `x86_encoding_proofs` and `reconstruct_x86_cmpxchg_narrow` carry what those credits do not claim, notably that the narrow-CMPXCHG obligation itself says nothing about the emitted BYTES — that link is ENC-3's, and `decode_check.rs` COVERS `Cmpxchg8`/`Cmpxchg16`, deriving the operand width, the LOCK prefix and the byte-register identity from the bytes alone. `MovsxdRMSib`, the scaled SIGN-EXTENDING load, is in the denominator COVERED even though nothing emits it yet: emitted value/effect debt does not belong in the excluded bucket. The `x86_reconstruct_effective_address` family cannot credit it, because that reconstruction builds BOTH sides of a `SibMemAddr` from the SAME operand with the SAME `recon_base`/`recon_index` symbols and so cannot refute a wrong base, a wrong index or a base/index swap, and has no sign-extending load model at all; `x86_movsxd_sib_proofs` credits it. The EIGHTEEN volatile memory accesses (the sixteen MOV forms and the two zero-extending loads) are credited on a JOINT obligation covering BOTH the load/store value or memory effect AND preservation of the observable volatile access/optimizer-ordering boundary (a byte-identical plain MOV proof alone is insufficient): VALUE from the same memory reconstruction their byte-identical plain siblings use, which must discharge Valid, ADDRESS from `x86_addressing_proofs` decoding the real emitted ModR/M+SIB bytes, and BOUNDARY from `x86_volatile_trace`, whose elide/duplicate/widen/narrow/redirect/reclass/reorder battery refutes INSIDE its credit hook while a benign block-layout permutation is required NOT to refute, and which is ENFORCED per compile at both the selection and optimizer boundaries. `x86_volatile_joint_audit_row` requires all three, the gate returns it for every volatile opcode, a failing leg is `ProofNotDischarged`, and `x86_address_audit_row` refuses a volatile opcode, so the credit cannot decay into a plain-MOV proof. The 40 plain ADDRESS rows likewise require their VALUE reconstruction to discharge as well as the address, and the compare-exchange joint rows take their VALUE leg from the same reconstruction hook. RISC-V 14/17 with 3 RED rows. WebAssembly 128/128 with 0 RED rows. The INTEGER scalar-constant rows are credited by an INDEPENDENT spec-derived signed-LEB decoder, and `f32.const` (0x43) / `f64.const` (0x44) by an INDEPENDENT decoder of the spec's little-endian float production that reads the real emitted raw IEEE-754 payload and compares it BIT-EXACTLY with the pattern the trust-ir binary64 carrier denotes — for `f32.const` through a round-to-nearest-even narrowing stated from the format definitions (NaNs quieted with their high payload kept) and checked against the reference interpreter — so a rounding bug, a quieted signalling NaN or a dropped sign refutes; byte-swap, truncation, width-confusion, quieted-sNaN, unquieted-narrowing, sign-drop, round-toward-zero and negated-claim controls each refute for their stated reason inside the credit hook, and the captured payloads and bodies are re-derived from the live backend by `coverage_gate_tests`, which pins this ratio, and by `wasm_encoding_gate`. The full wasm32 lowering emits 19 further opcodes. Thirteen are reconstructed from their real bytes against independent trust-ir encoders: `clz`/`ctz` (a clz byte for an intended ctz refutes), `rotl`/`rotr` (the other direction refutes; the amount is reduced modulo the width on both sides), `eqz` (a nonzero test refutes), `select` (swapped value operands or an inverted condition refute; `encode_select`'s any-nonzero condition is pinned over a full 32-bit condition) and `copysign` (stated over the operands' bit patterns, the spec's same-sign/negate case split against trust-ir's mask-and-merge, so NaN signs and payloads are observed; swapped operands, `fabs` and `fneg` refute; the row also requires its captured emitted body, which fixes the operand order). `eqz` and `select` share their core predicate with the trust-ir side, so those two obligations check the decoded byte and width, the `Bool`-as-`i32` 0/1 carrier and the stack order, as the two-operand compares do. No single trust-ir instruction lowers to `eqz`: the lowering emits it only as the zero test inside the assert, overflow and wide-integer sequences, so the row credits its value semantics and those sequences rest on the value-domain differential. `min`/`max` are emitted only inside the FMin/FMax sequence, so their four rows are credited by that SEQUENCE: the captured emitted function body is executed under the spec's instruction semantics for every permitted `f.min`/`f.max` NaN result and compared, over a bit-pattern battery reaching every input class, with the RELATIONAL trust-ir contract (a lone NaN gives the other operand bit-exactly, two NaNs give a NaN, an ordered pair the lesser/greater, and a `-0`/`+0` tie either operand, which trust-ir's numerics policy leaves unpinned); opposite-op, unguarded, inverted-guard and NaN-selecting controls refute at their stated class, and a control pinning the tie to the second operand refutes at the tie, so the credit is explicitly conditional on the unpinned reading. This is battery evidence, not a proof over all inputs. `memory.copy`/`memory.fill` are credited because the lowering guards the op with `if (n != 0)` (wasm traps when the range end exceeds the memory size even for a zero byte count, while trust-ir defines a zero-byte MemCopy/MemSet as a no-op even with a dangling pointer): the two rows are credited by the captured guarded MemCopy/MemSet BODIES that a trust-ir MemCopy/MemSet lowers to, executed on a two-page memory under the spec semantics against the relational trust-ir contract over a battery reaching every input class (a zero count returns with the memory unchanged whatever the pointers; an in-memory range is copied as if through a temporary or filled with the operand's low byte; a range past the memory is UB that a trap refines); the unguarded body refutes at a zero-byte out-of-memory range, and inverted-guard, guard-on-destination, swapped-operand, forward-byte-copy and operand-truncation (count to 16 or 8 bits, copy source to 8 bits, a destination bit cleared) controls refute at their stated class. The battery observes bits 0-16 of each pointer and of the count and every bit of the fill byte (clearing any one refutes); the higher bits rest on an operand-provenance check that requires the op's operands to be the function's parameters (the fill byte up to its `u8` mask) and the guard to test the count, and every operand mask, including one clearing only bit 31 of the count, fails it. This too is battery evidence plus a dataflow check of the captured body. `memory.fill` is emitted only in that guarded sequence; `memory.copy` is also emitted unguarded, with a constant nonzero size, by the memory-carried-value layer's aggregate, lane and sret moves (`emit_copy`), which this credit does not cover: their addresses and sizes rest on the lane differentials, and the target pins that every emitted bulk op is one of the two forms. The four lane-wise v128 value ops (`i32x4.add`/`mul`, `f32x4.add`/`mul`) are outside the denominator: the lowerer never selects a v128 value (no v128 carrier, simd128 refused), so they are excluded as never selected like `v128.load`/`store`/`const`, and their lane-wise reconstruction stays built and refutable in `reconstruction_wasm`; the exclusion is checked against emission — a corpus compiled by the live backend is scanned and must contain no `0xfd`-prefixed instruction, and a patched module that does is reported. The `reconstruction_wasm` target, outside this gate, checks that every decoded single-byte opcode equals the constant the wasm encoder writes and every emitted `0xfc` form equals it as the full (prefix, LEB sub-index) pair; the conversions' source side takes the signedness their opcode NAME intends, so a swapped sub-index refutes. A high ratio on THIS gate is not a claim that the wasm lane is verified: the P3 value-domain gate is 16/20 with its 4 named deferrals (its 12 `i64` sub-word / sign-extension bytes are never selected and excluded, which the same live-corpus scan checks; their obligations still discharge; each of its 14 load/store credits also binds the DECODED memarg offsets of a captured module of struct field reads and writes to the trust-ir layout offsets, so a shifted field offset refutes), relooper bisimulation is deferred, and host-memory obligations belong to the host per the ownership map. The test passes with exactly these named classifications and fails on unknown drift. The ratios report accepted evidence obligations for inventoried emitted value/effect opcodes, not correctness-proof or end-to-end compiler-proof percentages. A default `Statistical(N)` Valid result is regression evidence, not a formal proof. |
| `meta_theorems` | Property-level executable invariants. |
| `mutation_catalog` | Mutation-harness invariants. |
| `proof_gate_strict` | Non-degeneracy and fail-closed proof-gate behavior. |
| `fsym_real_function_corpus` | Bounded symbolic preflight on the maintained real-function corpus. |
| `aarch64_affine_lowering` | Independent affine correspondence between exact LIR and raw, pre-optimization AArch64 MachIR, including real instruction selection and adversarial source/machine mutations. This bounded wrapping-integer check does not establish TrustIR correspondence, final-code correctness, or publication authority. |
| `aarch64_trust_ir_affine_lowering` | Independent module-owned TrustIR/LIR/raw AArch64 correspondence for the bounded scalar affine domain. Exact signature, literal ranges and typed sparse SSA bind the source before comparing target semantics; target corruption cannot become an unsupported-source skip. No post-optimization or executable publication authority is granted. |
| `wasm_encoding_gate` | WebAssembly encoding/indexing evidence over the bytes the live backend really emits: the module index spaces (the shift imported functions impose, export targets, the element segment's `table-index == funcidx + 1` mapping (table slot 0 is the null funcref), the little-endian static data image, section order), an INDEPENDENT spec-derived signed-LEB128 decoder applied to every captured `i32.const`/`i64.const` immediate at canonical length, and `TargetInfo` conformance for `wasm32`. Every obligation is a byte-level statement plus a mutation that must refute it. The tally is pinned exactly and reported in three parts, never as a headline: **208 proven / 0 refuted / 110 not-applicable**, plus 6 named RED deferrals. The not-applicable count is load-bearing: every row here quantifies over a set of constructs, and a row whose set is empty for a module (no calls, no globals, no branch, no memory access, no import) reports NOT-APPLICABLE rather than banking that module's silence as credit — which is why a `() -> i32 { ret -1 }` module earns 7 proven rows here and 12 not-applicable (its O2 body is a constant, so it references no local). One module, the full-surface island, makes every row of both families applicable at once, so no row is merely stated. It does NOT establish that the lowering chose the right value, the right call target, or the right control flow — a wrong constant encodes and decodes perfectly. Neither does it catch a forgotten import shift from a single module: that partition is true by the decoder's construction, so the obligation is carried by a TWO-COMPILE differential (the same trust-ir lowered closed and as an island) whose refutation of the exact silent miscompile is asserted, together with the single-module family's measured blindness to it. `f32.const`/`f64.const` immediates are raw IEEE-754 payloads this LEB decoder does not reach; they are credited in the opcode inventory above by the independent float-payload decoder (`wasm_encoding_proofs` section 5d), whose live-emit freshness, bit-exact obligations and refuting controls this target runs, together with the captured `f.min`/`f.max`/`copysign` bodies' freshness and controls and a comparison of the stated binary64-to-binary32 narrowing with the host conversion at every rounding boundary. |
| `x86_encoding_gate` | The x86-64 `MOV r,imm` ENCODING family behind the `MovRI` coverage credit. The row is credited over a CAPTURED corpus of emitted bytes, because the gate crate cannot run the encoder. This target re-derives every captured entry from the LIVE encoder, so the credit cannot rest on a stale capture. `coverage_gate_tests` repeats that re-derivation where it pins the ratio. The target decodes the real emitted bytes with an INDEPENDENT SDM-derived decoder and compares, for every prior register value, the write to the 64-bit root register against the machine-IR intent. It also pins canonicality and exact framing. It runs a STRATIFIED (not exhaustive) live sweep of every register at every width, and every negative control must refute for its stated reason. It shows the credit hook REFUSING a control that survives or refutes for the wrong reason. Decoder controls cover the never-emitted branches: group-11 `/1../7` and memory-destination `C6`/`C7` forms, plus all four AH/CH/DH/BH registers. It shows that trust-cg-codegen's ENC-3 decode-check runs the same obligation on every `MovRI` per compile (default `enforce`; `TCG_DECODE_CHECK=off|warn` or `TCG_NO_DECODE_CHECK=1` remove it). The per-instruction `MovRI` certificate a compile issues cites that run, so since X-OPCODES-P13 it is `covered_elsewhere` (`verified: true`) only when ENC-3 ran in `enforce` for that compile and a blocking `covered_elsewhere_withheld` row otherwise. trust-cg-codegen's unit tests pin that, not this target: the certificate builder over every backing, and the x86-64 AOT and JIT certificate lanes through real compiles, where the backing each lane hands the builder must equal the ENC-3 mode its encode ran. It does NOT establish that the lowering chose the right constant or register. It does NOT compare an RFLAGS/frame effect: that MOV writes no flags is SDM trust base, and the obligation enforces only closure over the four MOV-immediate productions (the `XOR r,r` zeroing idiom refutes). The ISA rules are transcribed from the SDM with no silicon differential. |
| `x86_sse_lane_gate` | The x86-64 SSE LANE-ROUTING family behind the ten `Pshufd`/`Pmovmskb`/`MovdqaRR`/`Punpck{lbw,hbw,ldq,lqdq}`/`Ptest`/`Pblendvb`/`Packuswb` coverage credits. Those rows are credited over a CAPTURED corpus of emitted bytes, because the gate crate cannot run the encoder; this target re-derives every captured entry from the LIVE encoder, so the credits cannot rest on a stale capture, and `coverage_gate_tests` repeats that re-derivation where it pins the ratio. It sweeps all 256 register pairs for every row and all 256 PSHUFD immediates through the live encoder and the whole obligation, and for each immediate it also requires a permutation that is NOT the one the immediate spells to REFUTE. What that does NOT settle is how instruction selection PACKS a PSHUFD ORDER field: the corpus perm is hand transcribed from isel's immediate literals and the sweep hands the encoder an immediate packed by the same convention, so an isel-side packing bug would move both sides together. The claim is stated at that width in the family's non-claims, the ENCODER's placement of the imm8 is what the byte mutants refute, the SDM UNPACKING convention is anchored on silicon, and the one immediate isel COMPUTES rather than spells (`v4i32_mask_shuffle_imm`) is pinned against that convention here. It runs the SDM denotation against NATIVE SILICON on an x86-64 host with SSE4.1: the same operand values go to the model and to the hardware instruction, and any disagreement fails. Every value row issues a real instruction, MOVDQA register-register included — it is spelled with inline asm because no intrinsic names it and the compiler is free to elide a copy; returning the source value there would have counted the row into the silicon tally without an instruction executing. That matters most for MOVDQA and PMOVMSKB, the two rows whose machine and source sides are the SAME construction (a 128-bit copy, a sign-bit gather) and which therefore rest on silicon plus their wrong-model controls rather than on two independent formulations. That is the only part of the family which is not internally consistent by construction, and so the only thing that can catch a shared MISREADING of the SDM; it is one CPU model over a sampled grid, not a proof. PTEST's ZF and CF are anchored the same way; the four flags the SDM says are CLEARED are not read back and remain transcription trust base. It does NOT establish that instruction selection chose the right instruction, permutation, mask or operands — the intent side is the emitted instruction's own intent. It does NOT claim MOVDQA differs from MOVDQU in VALUE (it does not); that separation is the mnemonic-identity conjunct. It does NOT prove a folded `xmm,m128` spill slot is 16-byte aligned; the memory denotations ASSUME it, as the already-green packed rows do. Its host class is `x86_64-native` (`TRUST_CG_X86_NATIVE_GATES`): the silicon half compiles only for `target_arch = "x86_64"`, so the gate runs the target only on a native x86-64 host, with `TRUST_CG_REQUIRE_X86_SILICON=1`, which makes the target FAIL when that half is not compiled in; its no-SSE4.1 notice is spelled `SKIP:` so the result parser counts it. Built for any other target the two silicon tests are named `#[ignore]` stubs that fail if forced, never absent (L13-P14). |
| `aarch64_value_decode_gate` | The AArch64 decoded-word value family behind the `MovR`, `FmovFprFpr`, `FmovFprGpr`, `FmovGprFpr`, `Smull`, `Bfm`, `Rbit`, `AddRIShift12` and `Mrs` coverage credits. Those rows are credited over a CAPTURED corpus of encoder words; this target re-derives every captured word from the LIVE encoder (as `coverage_gate_tests` does where it pins the ratio), then encodes every register pair, every bitfield-insert `(lsb, width)` and every `imm12` — 59,664 words — and requires the per-instance check to accept each: an independent Arm ARM decode whose effect on the whole destination register is compared EXACTLY, as a bit routing, with what the instruction names (copies, FMOV, RBIT, BFM, MRS), or as an instance of the separately checked form (SMULL, the shifted ADD). Every single-bit corruption of every canonical word is refuted except named semantically neutral bits. It shows trust-cg-codegen's ENC-5 decode check running that obligation on every emitted word (default `enforce`; `TCG_DECODE_CHECK_A64=off|warn` or `TCG_NO_DECODE_CHECK=1` remove it) and rejecting wrong pairings its structural fields accepted, including the ORR spelling of a copy from SP, and the credit hook refusing a surviving control. It does NOT establish that the lowering chose the right registers, widths or immediates, that TPIDR_EL0 holds the thread pointer (ELF TLS ABI, trust base), or FEAT_FP16 availability; the Arm ARM rules are transcribed, and this target is not a silicon differential. |
| `x86_movsxd_sib_gate` | The x86-64 SCALED SIGN-EXTENDING LOAD family behind the `MovsxdRMSib` coverage credit — the x86 counterpart of the AArch64 `LDRSW [Xn, Xm, LSL #2]` jump-table proof. The row is credited over a CAPTURED corpus of emitted bytes, because the gate crate cannot run the encoder; this target re-derives every captured entry from the LIVE encoder, and `coverage_gate_tests` repeats that re-derivation where it pins the ratio. The MACHINE side is an INDEPENDENT SDM-derived decode of the real emitted bytes — it models the no-base SIB form, the no-index sentinel, the register-direct and RIP-relative forms, the non-SIB `[base+disp]` form, `63 /r` without REX.W and `REX.W 8B /r`, none of which the `MovsxdRMSib` encoder arm emits — denoted as a write to the 64-bit destination ROOT over per-register leaves NAMED FROM THE DECODED REGISTER NUMBERS. The SOURCE side states the same write from the machine-IR intent alone. The two are structurally distinct by construction (a SHIFT by the raw SIB scale field against a MULTIPLY by the entry size; an explicit sign-extend of a zero-filling load against a signed load) and the comparison REFUSES a machine side identical to the source side, so the credit cannot decay into an `X == X`. The ADDRESS facet is EXACT for every 64-bit base and index (`base + index*s == base + (index << ss)` iff `s == 1 << ss`, with necessity at `index = 1`); the VALUE facet is decided over a witness family that must exercise BOTH sign cases of the loaded doubleword, plus the full `verify_by_evaluation` sampling sweep and an EXHAUSTIVE sweep over a contiguous 2^16 address window here. This target sweeps the whole destination x base x index x scale x displacement product through the live encoder and the obligation, and requires every byte control, source re-claim, WRONG-MODEL control and hand-written SDM decoder control to REFUTE for the reason class it declares, with an unbuildable control counted as a battery DEFECT rather than a refutation. THREE SDM rules this family transcribes are never EVALUATED by the credited MOVSXD r64 family, so each has its own control: the destination WIDTH rule (Vol 1 3.4.1.1) is unreachable because the Extension facet forces `dst_bits == 64` before the Destination facet calls `dst_write_mask`, so six WRITE-MASK vectors decode real bytes for every production in the decoder's language (`REX.W + 63 /r`, `63 /r`, `66 + 63 /r` and the three `8B /r` forms) and pin the width AND the mask of each — a 32-bit operand writes a result ZERO-EXTENDED to 64 and so changes the WHOLE root; REX.B DOES NOT CREATE A BASE REGISTER (Vol 2A Tables 2-2/2-3), and because the encoder never emits `SIB.base=101` with `mod=00` (pinned over the whole operand product), a decoder that added `&& !rex_b` to either branch would read `49 63 04 8D` as `[r13 + rcx*4 + disp32]` — D1b/D1c and D4b/D4c set REX.B, and D1c is stated against the `[r13 + rcx*4]` intent such a decoder would CREDIT; and the ANTI-VACUITY guard, which protects the sign-extension facet from a narrowed witness family, is decided in both directions by an all-negative and an all-non-negative family with the exact row counts demanded. All three batteries run inside the CREDIT HOOK, so they reach the ratio-pinning targets and not only this one. It does NOT establish that anything EMITS the opcode: **nothing does** — the active jump-table path uses 8-byte deltas through `MovRMSib`, `decode_check.rs` still allowlists `MovsxdRMSib` under `JUMP_TABLE`, so unlike `MovRI` this family has NO per-compile check and claims none, and NO runtime or performance claim follows from it. It does NOT establish that instruction selection would choose the right table, selector, entry size or displacement. It is NOT a memory-content theorem: `SmtExpr::MemLoad` models memory as a deterministic function of the address, which is what makes a wrong address refutable and is not a model of aliasing, faulting or what the table holds. That the loaded i32 is `target - table_base` remains the #62 dense-mapping gate's. The ISA rules are transcribed from the SDM with no silicon differential; the `objdump` differential over the same bytes is adjacent evidence, not part of the obligation. |
| `wasm_cfg_structural_gate` | The per-compile CFG structural invariant on the relooper's output, checked against a control-flow-diverse corpus compiled by the live backend, and RUN ON EVERY EVIDENCE-CARRYING COMPILE (`wasm::compile_module_with_evidence[_and_policy]` calls it on the bytes it just emitted; a refuted verdict fails the compile, an inconclusive one is filed uncredited in the evidence's `not_run` list, and a holding one is filed in `ran` and moves nothing else — that compile's verdict stays `MissingEvidence` and its route stays `NotRun`): every `br`/`br_if`/`br_table` depth names a LIVE label, branch operand types and counts follow the spec's polymorphic-stack rule, every `br_table` arm and its default take the same types, join heights and operand types are checked at every `end`/`else`, and the bracket structure is well formed. This is a NECESSARY CONDITION on the structuring, NOT a proof that the structured program computes what the trust-ir CFG computes: relooper BISIMULATION is a named RED deferral, and two blind-spot mutants — a branch retargeted to another live same-arity label, and a `block` opener rewritten as a `loop` — are shipped and asserted NOT to be caught, so the gap is measured rather than claimed away. Also silent on block-parameter (phi) resolution and on code the spec proves unreachable. Its mutation controls use `wasm_cfg_proofs::mutate_nth_local_set_to_get`, a round-9 public helper still pending the owner's sign-off (`docs/wasm32_perf_roadmap.md`, section "Pending owner sign-off"). |
| `wasm_abi_proofs_gate` | The WebAssembly shadow-stack frame refinement and the call/table ABI discipline, over a corpus of REAL emitted module bytes (frozen fixtures re-compiled and required to match byte-for-byte, plus live modules outside the corpus). Reconstructed SMT obligations pin the frame arithmetic (frame size, slot offsets, slot disjointness, the prologue's publish-into-the-global-it-read, the epilogue's restore of the caller's stack pointer on a normal return); decidable structural checks pin the index spaces, direct-call targets, argument and result discipline, function-pointer constants, the element segment, `call_indirect`'s table immediate, and the imported stack base's immutability. Byte-mutation guards are its teeth. It does NOT establish the five HOST obligations named in `crates/trust-cg-codegen/src/wasm/OWNERSHIP.md` (host-memory aliasing under Policy I, stack-reserve sufficiency, stack-pointer restoration on a trap or host throw, stack-base alignment, argument-window validity), the engine's `call_indirect` runtime type check, imported-function behaviour, whole-body operand-stack typing, or call-site correspondence across a reordered CFG — the last of which ships as a declared blind guard. |
| `wasm_internal_abi_gate` | The wasm32 object lane's internal multi-value ABI (P6), over REAL relocatable objects the live lane emits for a fixed corpus at O0-O3: the boundary gate (every multi-value function local, or strong hidden under the reserved crate-private `.tcg.mv` name; not exported; in no element segment; named only by a direct-call relocation; `+multivalue` declared), the return binding of each forwarding C-form entry, its source binding against the trust-ir signature's BasicCABI layout, and the link binding across a crate's objects. Byte-mutation and hand-built negative controls are its teeth. Structural checks only: it does NOT prove that an internal entry computes its trust-ir function, nor that the objects checked are all of a crate's objects. The target exercises surfaces still pending the owner's sign-off (the module `trust_cg_verify::wasm_internal_abi` and the `compile_object_optimized` entry its corpus compiles through; `docs/wasm32_perf_roadmap.md`, section "Pending owner sign-off"), so a change to them before sign-off moves this target with them. |
| `wasm_value_domain_gate` | The WebAssembly P3 value-domain sub-inventory (sub-word and FP linear-memory accesses, sign-extension operators): the grown denominator, the credited set and the named RED deferrals are pinned, so drift in either direction fails. It is a sub-inventory of the wasm backend, not a fifth backend, and does not make the wasm lane verified. |
| `bdefs_differential_bridge` | AArch64 integer bridge. |
| `must_refuse_corpus` (trust-cg-codegen and trust-cg-cli targets, KIND 4) | trust-ir's MUST-REFUSE CORPUS, through this backend's real admission paths: every row of the pinned trust-ir's `trust-ir-conformance` corpus (modules a named trust-ir entry point refuses, modules well-formed by every trust-ir rule that a native backend must still refuse, poisoned byte strings, plus one control row a consumer must ACCEPT) is driven through the reader, the strict adapter, the AOT compiler and the compile service in process, and through the real `trust-cg` binary. A row this backend compiles fails BY NAME unless it is listed as known-accepted with its reason, and that list is exact in both directions, so it only shrinks; the control row must be accepted by every lane, no refusal may come from the license layer, and a row the corpus adds at a later pin fails by name. `scripts/bump_trust_ir_pin.py` runs the codegen target as the last guard of its transaction and rolls a pin move back when it is red. Test-rung evidence about refusals, never proof. |
| `trust_ir_interp_differential` (trust-cg-codegen, plus its `--features mutation-knobs` twin) and `emit_proofs_adapter_disclosure` (trust-cg-cli), WS7.2 | The trust-ir -> LIR adapter step that NO certificate covers (every certificate and sidecar says `"covered_span": "lir->machine"`). The vendored `tests/fixtures/trust_ir_exec/` corpus (the proof program's F-111 witnesses and the WS7.1 aggregate families) and a pinned-seed aggregate-program generator are JIT-compiled at O0-O3 and compared vector by vector with the trust-ir reference interpreter; a vector the interpreter calls undefined is skipped, any other interpreter error fails, and an entry whose every vector is skipped fails. The mutation-knobs leg is the negative twin: with `legacy_in_place_insert` on, the same gate must report the c13 mismatches (`dotOf(1,2,3,4)` native 25 vs 11). The CLI leg checks that `--emit-proofs` prints `trust-ir->lir: NOT COVERED` per function and no function-level `VERIFIED`, and that the shipped binary carries no mutation knob. Statistical evidence, never proof (the trust-ir -> machine obligation is WS7.16). |
| `codegen_license_evidence` (trust-cg-lower and trust-cg-codegen targets) and `codegen_license_flags` (trust-cg-cli), roadmap WS7.5 | The trust-ir CODEGEN LICENSE is bound to evidence and a claim-less body is refused by default (F-006, F-116, F-103; DG-73). `Gated{"clean-kernel-tv"}` licenses a body only when trust-ir's own license layer finds exactly one `Certified` TranslationValidation row whose kernel certificate replays against the current body, and a `Failed` row about the body revokes any license; each refusal is pinned BY NAME (`GatedWithoutEvidence`, `GatedFunctionRefuted`, `UnlicensedBody`) on every adapter entry, every compiler lane (AOT, host JIT with native execution of the real Clean `addmul`, closed-JIT Core, compile service, wasm32) and the CLI, against a positive fixture that compiles under the DEFAULT policy (on the adapter entries and compiler lanes the envelope with the trust-ir v61 `GateEvidence` its pre-v61 license lacks bound in the test, at the CLI `certificate_binding`; DR-KERNEL-TV-CLI-ARMS-20261017). The envelope as decoded is refused as `UnevidencedGate` at the CLI by this row. On the compiler lanes this row's evidence-free negative twins are refused first as `GatedWithoutEvidence`, and `UnevidencedGate` is pinned instead by `must_refuse_corpus` (corpus row `body_gate_kernel_tv_evidence_unrecorded`) on its lanes: the strict adapter, AOT, compile service, wasm32 module and object, and, on AArch64 macOS, host JIT; closed-JIT Core is not among them. `body_gate: None` compiles only under an explicit Permit: the CLI's disclosed `--permit-unlicensed`, and in production only through a named, source-counted `UnlicensedPermitException`. The obsolete license-evidence bypass knob has been retired: it could not bypass the mandatory admission and missing-evidence checks. Mutation-enabled adapter and compiler targets instead require their evidence-free negative twins to remain refused, including inline-only bodies, AOT, compile service and wasm32. No production evidence rule is relaxed. Test-rung evidence, never proof. |
| `bdefs_differential_bridge_x86` | x86-64 bridge. |
| `bdefs_differential_bridge_riscv` | RISC-V bridge. |
| `bdefs_differential_bridge_x86_packed` | x86 SSE packed bridge. |
| `bdefs_differential_bridge_x86_fp` | x86 SSE floating-point bridge. |
| `bdefs_differential_bridge_neon` | AArch64 NEON bridge. |
| `bdefs_differential_bridge_riscv_fp` | RISC-V floating-point bridge. |
| `bdefs_differential_bridge_neon_fp` | AArch64 NEON floating-point bridge. |
| `fp_bitmodel_bridge` | AArch64 floating-point bit-model/silicon bridge. |

The following library-test filters also run, each as a separate required Cargo
gate. A broad integration-target run does not execute these library tests.

| Package | Library filter | Evidence checked |
| --- | --- | --- |
| `trust-cg-verify` | `x86_source_bound_body::tests::qualification_matrix::` | The complete raw-query diagnostic binds canonical bytes to all thirteen committed snapshot families and retains actual wrong-lowering controls from each family. Duplicate family/class/label records refuse. This runs no AY and grants no proof credit; runtime cohort qualification and production credit remain separate. |
| `trust-cg-verify` | `tv2_` | AArch64 and x86-64 missing/mispaired-source prerequisites, including empty reports and explicit diagnostic warn/off behavior. |
| `trust-cg-verify` | `coverage_gate::` | The coverage gate's in-crate inventory pins, which the `coverage_gate_tests` integration target does not run: pair-memory debt rows and the AArch64 emitted denominator they must not shrink, deferred-row reasons, and the per-row audit controls. |
| `trust-cg-verify` | `checked_mul_i128_proofs::tests::credit_` | The i128 checked-multiply credit holds with the registered battery and eight refuted controls, and is refused for a surviving control, a degenerate or missing obligation, and a wrong overflow flag the battery sees. The filter leaves out the AY-backed `formal_attempt_never_refutes`. |
| `trust-cg-verify` | `x86_source_bound_body::tests::slice5::` | The x86-64 body theorem's slice-5 domain (scalar pairs, symbol addresses, branch-free compares) over real selector output: the owner builds for every fixture, the golden SMT-LIB digest, and every negative control ends as a typed mismatch, an unsupported body or a theorem the sampled oracle refutes (swapped or narrowed pair lanes, an unmasked `bool` lane of a pair call, wrong or unreferenced symbols, wrong conditions, a u64 compare made at 32 bits). No AY call: the replay on AY and Clean and the verifier-credit tests are in the separate `slice5_qualification` module, outside the filter. |
| `trust-cg-verify` | `x86_source_bound_body::tests::slice6::` | The x86-64 body theorem's slice-6 domain (acyclic control flow: `Brif` diamonds and joins, several returns, bare and call-then-trap paths, `Switch` compare chains, `cmov` selects, partially written private slots) over real selector output: the owner builds and covers every row (the `jcc`s included) for every fixture, the golden SMT-LIB digest, and every negative control ends as a typed mismatch, an unsupported body or a theorem the sampled oracle refutes (an inverted or wrong-code branch, swapped successors, a flag writer between a compare and its jump, flags from another block or left undefined by a call, a missing trap or a trap on the wrong condition, a join taking the other arm's value, an extra machine path, a wrong early return, a loop). No AY call: the replay on AY and Clean, the rejected-encoding evidence and the verifier-credit tests are in the separate `slice6_qualification` module, outside the filter. |
| `trust-cg-verify` | `x86_source_bound_body::tests::slice7::` | The x86-64 body theorem's slice-7 domain (calls through memory: a private slot's address passed to a direct call as a return buffer of an `sret` callee or as an out-parameter, the slot's contents observed at the call and its bytes call-defined after it, for every later call too) over real selector output: the owner builds and covers every row for every fixture, the golden SMT-LIB digest, slices 1 to 6 declare no call-defined byte, and every negative control ends as a typed mismatch, an unsupported body or a theorem the sampled oracle refutes (another slot or offset passed, a private address for a value, a read moved before the call, the stored value kept across the call or across a later call, another slot or field read back, a narrower read, other or missing contents at the call, an incoming access through an address that may derive from an escaped slot, a stored or returned slot address). Each slice-7 walk rule, disabled alone, fails at least one test of the filter. No AY call: the replay on AY and Clean and the verifier-credit tests are in the separate `slice7_qualification` module, outside the filter. |
| `trust-cg-verify` | `x86_source_bound_body::tests::slice9::` | The x86-64 body theorem's slice-9 domain (acyclic control flow past the slice-6 bounds, stated over the DAG: block and edge guards, values, registers and private bytes joined by the source edges' guards) over real selector output: the owner builds and covers every row for every fixture (diamond chains, bounds-check chains, switch chains and trees, a long arm and a long chain, merged slot bytes, calls, stores and loads on some paths, `bool`s in and out, a 63-block tree), the golden SMT-LIB digest, the sampled EQUIVALENCE of the DAG theorem and the slice-6 per-path theorem on every slice-6 fixture, refutation and variant and every slice-9 fixture (inputs matched by what each stands for), and every negative control ends as a typed mismatch, an unsupported body or a theorem the sampled oracle refutes (an inverted or swapped branch, a retargeted, extra or missing edge, a join taking another arm's value, a wrong call argument or store on one arm, a trap or return swapped, a switch case against the wrong constant, flags across a block boundary, a join of different escapes or root kinds, a redefinition after a join, a `bool` read of a byte one path left unwritten, a `Switch` with two cases of one value, a loop, the size bounds). Each slice-9 rule, disabled alone, fails at least one test of the filter. No AY call: the replay on AY and Clean and the verifier-credit tests are in the separate `slice9_qualification` module, outside the filter. |
| `trust-cg-verify` | `x86_source_bound_body::tests::slice11::` | The x86-64 body theorem's slice-11 domain (`I128` register pairs with `adc`/`sbb` and the tied shifts by CL, 16-byte accesses as two halves, and `f32`/`f64` bit patterns in SSE registers moved, stored, loaded or reinterpreted) over real selector output: the owner builds and covers every row for every fixture with names at most 64 bits wide, the golden SMT-LIB digest, the verify-owned System V classes agree with the selector's, and every negative control ends as a typed mismatch, an unsupported body or a theorem the sampled oracle refutes (a dropped or misused carry or borrow, swapped or crossed halves, a wrong access offset, a wrong constant half, a zero-extended sign, a logical shift for an arithmetic one, float arguments in the wrong XMM register, a `movss` where 64 bits are needed, an SSE register read after a call, a floating-point operation or a variable `i128` shift refused by name). Each slice-11 rule, disabled alone, fails at least one test of the filter. No AY call: the replay on AY and Clean and the verifier-credit tests are in the separate `slice11_qualification` module, outside the filter. |
| `trust-cg-verify` | `x86_source_bound_body::tests::slice12::` | The x86-64 body theorem's slice-12 domain (loops in a reducible CFG, cut at their headers: each region a DAG stated with slice 9's machinery, the cut-point relation on every edge into a header) over real selector output: the owner builds for every fixture (counting, accumulating, swapped and `bool`/`u8` carried values, a call, load or store per iteration, slot-held state, nested and sequential loops, an early exit, a `Switch`, a do-while, an escaping slot, a trap) and its theorem holds on samples, the golden SMT-LIB digest, every header input declared where read, determinism, and every negative control ends as a refusal or a theorem the sampled oracle refutes (loop-carried registers swapped or stale, a copy cycle run in place, a missing or extra iteration, a wrong exit, increment, step or bound, a register the loop writes or a private byte only the machine changes read as its entry value, a carried value tainted by an escape, an entry-block header, an irreducible cycle). No AY call; the replay lives in `slice12_qualification`. |
| `trust-cg-verify` | `x86_source_bound_body::tests::slice13::` | The x86-64 body theorem's slice-13 domain (a private stack address stored as data, escaping where the memory it went to is shared; integer parameters and arguments past the six argument registers through `[rbp + 16 + 8k]` and the outgoing `[rsp + 8k]` area; `Memcpy`/`Memmove`/`Memset` as calls to the C runtime routines; a `bool` read of another store's byte; and scalar atomic loads and `Relaxed`/`Release` stores as their single-threaded plain counterparts, ruling OD-83) over real selector output: the owner builds and covers every row for every fixture, the golden SMT-LIB digest, the verify-owned stack placement agrees with the selector's formal-argument bindings, and every negative control ends as a typed mismatch, an unsupported body or a theorem the sampled oracle refutes (another stored offset, two slots' addresses swapped, a value kept across a call its slot escaped to, swapped or widened stack eightbytes, a frame access through RBP other than a stack parameter's, an unwritten or wrong stack argument, an unbalanced `add rsp` or RSP not restored, swapped `memcpy` operands, a copied word read at another offset, an atomic or bool byte read raw or at another address, an atomic paired with a plain row, a partial read of a stored address, different escaped slots at a call, a sequentially consistent atomic store refused by name). Each slice-13 rule, disabled alone, fails at least one test of the filter, except the union of escaped slots at a DAG join, which fails the slice-9 row's `a_join_of_different_escapes_takes_their_union`. No AY call: the replay on AY and Clean and the verifier-credit tests are in the separate `slice13_qualification` module, outside the filter. |
| `trust-cg-verify` | `x86_source_bound_body::tests::slice14::` | The x86-64 body theorem's slice-14 domain (`Udiv`/`Sdiv`/`Urem`/`Srem` of a word as trust-ir's interpreter computes them, each division's undefined inputs a premise of the paths that divide, the machine `div`/`idiv` with its `cqo`/`cdq`/zeroed-RDX setup and its #DE as a stop the source must not reach, ruling OD-178; the unbound divide-by-zero guard as an observable trap the machine takes exactly where the source does, ruling OD-179; switch cases sharing a target as one edge, ruling OD-180; a jump table as the dispatch the selector's table states, and the machine-table refusal split by cause, ruling OD-181) over real selector output: the owner builds and covers every row for every fixture, the golden SMT-LIB digest, the division meanings agree with the pinned trust-ir interpreter and the machine division with Intel's on boundary operands, the optimizer's O1-O3 output is judged without false mismatches, and every negative control ends as a typed mismatch, an unsupported body or a theorem the sampled oracle refutes (a missing `cqo` or RDX zeroing, `cdq` for `cqo`, a dividend from another register, quotient and remainder swapped, `div` and `idiv` swapped, a narrow divisor not extended, a magic multiplier off by one, a dropped, misplaced or moved guard, a trap the source does not take, a division hoisted above its branch, an extra division by zero, a shared case compared with another value or sent to the default, two cases' arguments swapped, two jump-table entries swapped, the bound one short, the first case not subtracted, a 32-bit selector copied with a 64-bit `mov`, a hole sent to a case). Each slice-14 rule, disabled alone, fails at least one test of the filter. No AY call: the replay on AY and Clean and the verifier-credit tests are in the separate `slice14_qualification` module, outside the filter. |
| `trust-cg-verify` | `x86_source_bound_body::tests::slice15::` | The x86-64 body theorem's slice-15 domain (float constants as trust-ir's `float_bits_from_f64` and `Fneg`/`Fabs` as sign-bit operations through the constant-pool `movss`/`movsd` loads and three-operand `pxor`/`andps`/`andpd`, ruling OD-112; `mov` and ALU rows of mixed 32- and 64-bit registers defining their low 32 bits; a `bool` parameter forwarded as a `bool` argument, observed as the clean 32-bit bool under every caller view after the selector's entry `movzx`, ruling OD-113; loads and stores through an address that may derive from an escaped slot observing the escaped slots, ruling OD-114; `I128` parameters and arguments in the stack areas) over real selector output: the owner builds and covers every row for every fixture, the golden SMT-LIB digest, the float meanings agree with the pinned trust-ir interpreter on every class of bit pattern, the verify-owned `I128` stack placement agrees with the selector, the optimizer's O1-O3 output is judged without false mismatches, and every negative control ends as a typed mismatch, an unsupported body or a theorem the sampled oracle refutes (another constant or NaN payload, a sign mask of another bit, `xor` and `and` swapped, a dropped `abs`, a constant-pool entry of another size or row, an `F32` NaN constant, an aggregate byte dropped by a mixed copy, the high half of a mixed-width copy or `add` observed, the `bool` register forwarded raw, a slot written behind a derived load, a value kept across a derived store, another derived offset, different escaped slots at a derived access, swapped `I128` stack eightbytes or halves). Each slice-15 rule, disabled alone, fails at least one test of the filter, the selector's entry `movzx` included. No AY call: the replay on AY and Clean and the verifier-credit tests are in the separate `slice15_qualification` module, outside the filter. |
| `trust-cg-verify` | `source_bound_negative_memo::` | The source-bound negative memo can only withhold credit: every recorded outcome replays as `Unknown` or `Timeout`; only AY's strict self-check rejection, a disclosed incomplete certificate, the working checker's rejection and a timeout every one of whose deadline expiries used 90 % of its budget in CPU time are recorded (a CPU-starved, unmeasured or unexplained timeout is not, and leaves an existing entry exactly as it is; AY's host-state answers, a bare `unknown`, its model gate, credit, refutations, errors and installation or I/O reasons are not), and an outcome after a SAT verdict never is; every key input changes the key, including the verifier's source identity (re-derived from this build's sources) and the replay protocol (compared with the real resident, fresh, model and Clean commands); the per-box format refuses truncated, corrupt, oversized, foreign-schema, foreign-key and self-inconsistent entries, links and FIFOs (without blocking); the retry policy bounds per-box reuses, in-process hits and age, and a failed re-solve refreshes the entry; a reuse write-back never resurrects a concurrently deleted entry; recordings prune expired and unreadable entries; concurrent writer threads and processes never tear an entry. No AY call. |
| `trust-cg-verify` | `x86_source_bound_body::tests::negative_memo::` | The memo on the real x86-64 body replay path with a fixture AY that counts its replays and a fixture Clean: a second identical request and a fresh process run no AY and change no row; the budget, checker, AY, query and child environment each miss; after the reuse budget, and in one long-lived process after the hit budget, one re-solve refreshes the entry; AY's host-state answers and a model-query timeout after SAT are solved again and never recorded; the bypass re-solves every occurrence and writes nothing; a certified replay credits and deletes the entry, and in a fresh process a proof in the per-box store wins over a negative entry; a timeout whose solver used its budget computing is recorded with that CPU time and replays as a timeout, while one that ran out waiting is solved again at every occurrence and leaves an existing entry untouched. |
| `trust-cg-codegen` | `affine_lowering_tests` | Raw sealed-Core integration, hard mismatch rejection, unsupported-source accounting, and absence of final-code proof promotion. |
| `trust-cg-codegen` | `verification_precondition` | Function-level prerequisite failures survive report adaptation, including empty reports. |
| `trust-cg-codegen` | `jit_cert::tests::` | Certificate authority, non-vacuity, semantic cache identity, and replay controls. |
| `trust-cg-codegen` | `test_generate_proof_certificates_rejects` | Certificate generation refuses missing or mispaired LIR. |
| `trust-cg-codegen` | `x86_authoritative_` | Authoritative source policy survives diagnostic overrides and has a distinct enforced cache domain. |

The slice-23 and constant-I128-shift integration adds two solver-free library
filters to the same required inventory: `x86_source_bound_body::tests::slice23::`
and `x86_source_bound_body::tests::i128_const_shift::`. They check the actual
selector output, stable theorem snapshots, pairing/generalization controls,
all defined constant shift amounts, and wrong-lowering rejection. These checks
call no AY and grant no proof credit. The explicitly ignored slice-23 printer
lives in the separate qualification module; no diagnostic is selected as a check.
Formal AY/Clean qualification remains separate.

These gates use `scripts/trust_cargo.sh test --locked -p <package> --lib <filter> --
--show-output --test-threads=1` (`targo --unverified test`) with the package's default features (including codegen's
`verify` feature). The integration and library inventories are shared by the
runner and `--list`. Every target/filter must exit successfully and emit a
`test result: ok.` summary with an explicit positive passed count and zero
failed tests; a missing or renamed filter
cannot borrow passing tests from another gate. A manifest's textual registration
check alone is not evidence that a test ran.

Two additional required legs explicitly enable `lattice-guard-elision`:
`trust-cg-lower --lib lattice_guard::tests::` and
`trust-cg-codegen --test a64_lattice_guard_elision_differential`. They retain
the same command timeout, result-summary and non-vacuity checks. Predicate
implication and carrier binding do not establish a runtime value's refinement
premise; the controls require declared external and loaded indices to mint no
source capability and retain their bounds guards with the feature on. See the
authority regression record.

Two required representation legs run `trust-cg-lower --test
refine_erasure_hazards` and `trust-cg-codegen --test
a64_refine_byte_invariance`. They check narrow call/return extensions,
register exhaustion, TrustIR's GEP refusal, volatile I128/U128 refusals,
emitted text equality and poisoned register inputs. The codegen target also
links native C controls on its supported Linux GNU or Darwin AArch64 host;
other hosts emit the helper's explicit skip and receive no native execution
credit. The independent text and interpreter checks run on every host. See the
erasure hazard record.

`scripts/test_soundness_check.sh` exercises the production Cargo dispatch and
its failure/non-vacuity guards using a fixture timeout wrapper, as well as the
existing Clean command and dependency-lock controls. The diagnostic
`--self-test-cargo-gates` mode invokes only the shared trust-cg Cargo inventory;
it skips cross-repository qualification and writes no attestation record. It
cannot be combined with `--attest` or any other mode, and a successful focused
run is not a successful full soundness gate.

The same shell regression also executes the production summary, attest and
oracle-only finalization functions and the fail-fast `record()` with synthetic
gate outcomes, the real `hooks/pre-push` in a throwaway repository
(`scripts/test_pre_push_hook.sh`) and the hook Git-environment fixture.
`scripts/test_soundness_check.sh --finalization-only` runs those controls
without Rust compilation; this tests orchestration, not Trust proof evidence.
`scripts/tests/test_soundness_leg_inventory.py`,
`scripts/tests/test_soundness_attestation.py`,
`scripts/tests/test_soundness_remote.py` and `scripts/tests/test_land_main.py`
run the production gate, attestation tool, remote executor and landing train
in a throwaway constellation with a fake toolchain and a fake x86-64 host.

A Cargo target passes only when its process succeeds and the shared captured-
output parser confirms complete, nonvacuous named test results. The harness runs
both Cargo lanes with `-- --show-output`; ignored cases, runtime `SKIP` markers,
unexpected filtering of whole-target gates, inconsistent rollups, and incomplete
output all reject the gate. Explicit library filters permit unrelated filtered
cases while requiring positive captured passes and rejecting skipped selected
cases.
`RUST_TEST_NOCAPTURE` must be unset or `0`. A trailing success line alone cannot
establish a pass, and Cargo's trailing `error: test failed` does not turn a
runtime assertion failure into a compilation-error report.

`proof_gate_strict` contains both hermetic contract tests and 16 opt-in formal
campaigns (the full-database floor, the six-obligation arithmetic smoke and 14
family floors). A complete run requires `TRUST_CG_RUN_FORMAL_PROOF_TESTS=1`, an
AY that trust-cg-verify admits — only the `bin/ay` of the Trust toolchain that
built it, which is why `scripts/trust_cargo.sh` builds this target — and a
capable Clean checker: that toolchain's `bin/clean` first, aterm's managed
package only when that one fails the control-proof probe
(`crates/trust-cg-verify/src/obligation_cert_store.rs`). Without that opt-in,
those bodies emit runtime SKIPs: their libtest `ok` results are not qualified
passes, and this gate fails.
The parser also recognizes their former “external-solver campaign not requested”
message when re-evaluating old captures. Building the source Clean executable
for the proof-file checks does not replace an incapable managed checker.

The `wasm_encoding_gate`, `x86_encoding_gate`, `x86_sse_lane_gate` and `x86_movsxd_sib_gate` targets run in release mode
with `--include-ignored`. For `wasm_encoding_gate` that includes its exhaustive
sweep of all 2^32 signed-i32 encoder inputs. The ordinary default-profile Cargo
invocation leaves that expensive case ignored, so it is not a complete
substitute for this gate. That sweep checks the raw encoder against an
independent decoder and canonical length, not every possible compiled module
or the entire i64 input domain; those broader deferrals remain explicit.
`x86_encoding_gate`, `x86_sse_lane_gate` and `x86_movsxd_sib_gate` have no ignored cases where the
gate runs them, and release mode keeps their sweeps cheap. Built for any other
target, `x86_sse_lane_gate` carries its two silicon tests as NAMED ignored
stubs (L13-P14): a direct or full-matrix run on an arm64 host lists them as
`ignored, x86-64 silicon differential NOT RUN ...`
(`scripts/full_test_matrix_hosts.py` records them in `IGNORED_TESTS`), and
`--include-ignored` makes them FAIL, so their absence is never a silent pass.
The diagnostic `--self-test-cargo-gates` mode runs every dispatch argv on any
host, this target's `--include-ignored` included, so on a host that is not
x86-64 it reports `x86_sse_lane_gate` FAIL; that is the stubs refusing, not a
regression, and attest, portable and landing runs never run the target there. The MOV-immediate sweep is stratified, not
exhaustive over i64. The SSE lane sweeps ARE exhaustive over register pairs
(all 256 per row) and over all 256 PSHUFD immediates, but the silicon
differential samples operand VALUES on a deterministic grid rather than
enumerating them.

The Clean portion checks the maintained B-definition and LRAT-checker proof
files with `clean check`:

```text
aarch64_isa  aarch64_isa_chip  aarch64_fp  aarch64_fp_arith
aarch64_fp_cvt  aarch64_fp_divsqrt  aarch64_fp16  reducible_word
lrat_checker  lrat_checker_word  lrat_checker_tree
```

It also runs `targo --unverified test -p clean-kernel --test micro_diversity_gate`
(through `scripts/trust_cargo.sh`). The AY
source revision is recorded for provenance; qualified formal campaigns invoke
the configured managed AY/Clean tools through trust-cg's proof gate. A sibling
source checkout's revision is not the installed executable's identity.

The same newly built `clean` executable then checks trust-cg's own Clean specs
in `proofs/`:

```text
abi_clobber_spec  sentinel_decide_spec  mir_place_resolution_spec
```

An inventory leg fails if `proofs/` holds a `.lean` file that list does not
name. A rejected check, an incoherent declaration summary or a missing listed
file fails. A failed Clean rebuild blocks these checks instead of running them
against a stale binary, and with no checker binary at all each is a loud SKIP,
so the run cannot be green. These files prove properties of hand-written Lean
models. The Rust weld tests that compare production code with hand re-encodings
of those models remain the only link to the Rust implementation.

Finally, the trust-cg checkout runs `lake build` in `formal/lean`, requires the
`sorry`-line and explicit-axiom counts to remain exactly 0 and 0 (the
`BASELINE_LEAN_SORRY`/`BASELINE_LEAN_AXIOM` pins in the script), runs the
environment audit `formal/lean/scripts/AxiomAudit.lean` (no declaration may
depend on `sorryAx` or on an axiom beyond `propext`, `Classical.choice`,
`Quot.sound` and `bv_decide`'s native ones; `compile_refines` on the first
three only), and runs the `trust-cg-codegen` `lean_encode_golden_binding`
integration test. That test
binds the Lean encoder's shared golden vectors to the production Rust encoder.
Its AArch64 twin, `lean_a64_encode_golden_binding`, binds the rows of the
generated `formal/lean/Trust/A64/EncoderGolden.lean` (each emitter opcode shape
and operands, the A64 instruction the Lean model says it denotes, and the
model's word, all re-checked by the kernel during `lake build`) to the
production `encode_instruction`, the field-level encoding helpers and the ENC-5
decode-check, and requires ENC-5 to refuse every single-bit corruption of a
golden word. Both bindings cover their enumerated rows only.

The separate external-solver database floor may classify obligations as
timeout/unknown. `scripts/check_proof_gate.sh` prints the verified/pending split
and requires zero counterexamples, zero errors, and no statistical fallback.
Pending obligations are not described as proofs.

That runtime proof route uses **AY only**, plus the independent **Clean**
checker shipped by aterm. Normal installations use the self-contained managed
package store; no sibling source checkout or separate checker installation is
required. The Clean source tree above is a development prerequisite for
rechecking proof sources and kernel tests, not the runtime checker's discovery
mechanism. See [README.md](README.md#understand-and-check-the-evidence) for the
current package-capability caveat and explicit development overrides.

Two wasm offline-oracle gates run the backend's differential harnesses as
first-class checks: the `wasm_difftest` example (interpreter-vs-compiled-wasm
over its corpus, replayed under node) and the bounded `wasm_cfg_fuzz` relooper
fuzz. A missing node is a loud SKIP counted in the summary, never a silent
pass; any divergence or vacuous (0-case) run fails the gate.

Two further gates run the shipped ISLANDS' three-way differential
(`wasm_island_differential.mjs`): the generator emits its trust-cg wasm, its
rustc/LLVM twin SOURCE and interpreter-checked expectations, and the runner
then COMPILES the twin for wasm32, instantiates both modules and replays
every expectation against both. A generator run alone never compiles or runs
the twin, so without this gate the islands' "differential-experimental" label
would be a deployment intention rather than repository evidence. The vt
islands need an aterm tables dump (`ISLAND_VT_TABLES=<tables.json>`, schema
`aterm.vt-islands.tables` v1); absent, that one gate SKIPs loudly. The twin
compiler is a STOCK EXCEPTION: Trust ships no wasm32 core/std (measured
`trustc --target wasm32-unknown-unknown` -> E0463 can't find crate for
`core`), so the twin is compiled by the stock rustc named in
`ISLAND_TWIN_RUSTC` (never looked up on PATH, used for wasm32 only); an unset
`ISLAND_TWIN_RUSTC` SKIPs rather than passing.

A SKIP preserves the distinction between an unavailable prerequisite and a
failing check, but it is not success: any SKIP makes census, `--attest`, and
`--run-wasm-oracles` runs exit nonzero. No all-green summary or attestation
record is permitted until every required leg ran and passed. Zero failures
alone is insufficient; the skipped count must also be zero.

Produce the VT input from an explicit aterm commit with the maintained exporter:

```sh
python3 scripts/export_vt_tables.py --aterm /path/to/aterm \
  --revision <aterm-commit> \
  --output /path/to/new-tables.json > /path/to/export-provenance.json
TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 ISLAND_VT_TABLES=/path/to/new-tables.json \
  scripts/soundness_check.sh
```

The exporter compiles the five committed pure-table source files verbatim in a
temporary directory with the installed Trust package's `trustc` in its
unverified lane (`--rustc` names another Trust `trustc`). It does not build or
modify aterm's working tree, use dirty source bytes under a clean commit label,
or replace an existing output. Its provenance report records the full commit,
each source blob and SHA-256, compiler identity/flags, exporter identities, and
exact table-dump SHA-256. Retain that report with the gate logs. This is a
developer evidence utility, not a separate runtime dependency of aterm. These
tables are still common input to all three oracles: agreement checks the
compiler paths, not the correctness of aterm's table specification or any
uncommitted changes to it.

All four are differential evidence, not proofs — the wasm lane's per-op
refinement obligations remain the `wasm_formal` suite's territory.

### x86-64 vector-compare certificates

trust-ir's per-cell rule for x86-64 vector compares (`docs/dialects.md`,
"Vector compares on x86-64 follow one per-cell rule") admits an available
`chc_x86` `icmp.<op>` cell on the instruction model (`eq`/`sgt`, whose
registered obligation is degenerate) or on a certificate. trust-ir answers the
ground per cell (`trust_ir::chc_x86_vector_icmp_cell_ground`) and states the
certificate rule as code (`trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE`): on the
cell's exact non-degenerate query, the rule's AY answers `unsat` under
`--strict-proofs` with an Alethe proof that the rule's Clean `cert
verify-external` accepts in full (exit 0, no `hole`, no `lia_generic`). Both
tools are named by source revision and version, with the build arguments, the
exact invocations, the verdicts and the sha256 of the binaries that certified
the cells. `trust-cg-verify --test x86_icmp_manifest_cells` pins each
certified query's bytes, holds every cell's spec side to trust-ir's statement
(`trust_ir::chc_x86_vector_icmp_spec`, printed by
`trust_cg_verify::trust_ir_bv::SmtAlgebra`) and every machine side to the
instruction models trust-ir publishes for the cell; the leg `x86 icmp
certificates (pinned AY + the rule's Clean)` re-runs the certificate on those
bytes with `scripts/check_x86_icmp_certificates.py`:

1. It regenerates every cell's query with `targo --unverified run -p
   trust-cg-verify --example x86_icmp_certificate_queries`, which reads the
   same table the test reads (`tests/support/x86_icmp_cells.rs`) and writes
   the rule and each cell's ground from the compiled trust-ir into its
   manifest (schema `trust-cg.x86-icmp-cell-queries.v2`). The gate parses no
   prose: a malformed rule, or one that no longer requires `--strict-proofs`,
   `unsat` and `fully verified`, is `rule-unreadable`. The AY revision the
   candidate's `Cargo.lock` pins must be the rule's (`ay-pin-differs-from-rule`;
   trust-ir's gate 7 holds the rule's AY equal to trust-ir's own AY pin).
2. It builds each of the rule's tools by revision, one function: a `git
   archive` export of the revision from the gate's own worktrees' object store
   (AY with the export's Trust-lane block of `.cargo/config.toml` removed,
   `CARGO_PROFILE_RELEASE_LTO=false` and `AY_SOURCE_GIT_COMMIT`; Clean with
   its export's own config), built by `targo --unverified build --release
   --locked` with the rule's build arguments (no proof claim about either
   build). A cold build runs under the rule's Clean's own
   `scripts/heavy_gate.sh run auto:x86-icmp-<tool>-build-cold:40`, exported
   from the rule's Clean revision:
   its state is machine-wide, so the build is counted against every heavy job
   on the host (the actual C6 Clean cold build peaked at 26.58 GiB), and a
   refused admission is a named build failure. A build still queued or
   running after two hours, or one the gate is interrupted during, is
   stopped with its whole process tree, which stays in the gate's process
   group, so no build outlives the admission that counted it. Each binary is
   cached per revision under `$XDG_CACHE_HOME/trust-cg/ay-cli` and
   `.../clean-cli` with the sha256 recorded at build time; a later run
   refuses cached bytes that
   no longer match (`<tool>-cache-tampered`) or a recorded banner that is not
   the rule's (`<tool>-banner-mismatch`). The caches follow
   `scripts/private_cache.py`: every directory created in them is `0700`,
   every file `0600` (the binary `0500`), the build runs under umask 077, and
   nothing that exists is changed. The identity record sits beside the
   binary, so a slot, binary or record another user could write (a group or
   other write bit, or a symlinked slot), or a cache directory with an
   ancestor another user may rename entries in, is refused
   (`<tool>-cache-not-private`) rather than trusted or repaired; the slot is
   checked again after a cold build. The cache directory is resolved once,
   and the lock, the slot, the build and the binary each certificate cell
   runs are all named below the canonical directory that rule checked,
   never through the cache path as given, which may run through a symlink
   another user can re-point. Read and execute bits are not refused: a
   slot an earlier script built under umask 0022 (slot `0755`, binary `0555`,
   record `0644`) is reused as it is. Builds of one revision differ
   byte-wise, so the digest is recorded, not required; the report says
   whether each binary is one of the rule's certifying builds
   (`certifying_bytes`). A cold AY build takes about ten to fifteen minutes,
   a cold Clean build about thirteen; a warm leg under a minute after the
   query dump.
   A historical tool root manifest may contain only the retired clock keys
   `function_budget_ms` and `timeout_ms` (AY also admits the explicitly
   seconds-named `compiler_timeout_secs`). The maintained unverified-build
   recipe removes positive-integer assignments of those keys from the private
   exported manifest, checks equality of every other TOML value, and records
   both manifest hashes and the removed values. Compound policies, unknown
   keys alongside those clocks and syntax the adapter cannot isolate refuse.
   Source repositories, Rust source, features, dependencies, lockfiles and
   `.cargo/config.toml` are unchanged; there is no conversion to solver effort
   and no verified compiler-build claim. Each tool's new cache schema uses a
   separate revision/recipe slot, requires that disclosure and the exact
   build argument vector on warm reuse, and preserves old cache slots. This
   recipe adaptation changes no checker revision, query, certificate rule,
   proof argument, unchecked-rule refusal or required checker verdict.
   Cold builds use separate per-tool auto-weight classes with a 40 GiB initial
   fallback; the maintained estimator derives later reservations from actual
   completed cold builds. Failed pre-build refusals cannot lower weights, and
   warm binary hits never age out a cold peak. The earlier 12 GiB reservation
   under-counted the actual 26.58 GiB Clean build; its original log is retained,
   and the successful v2 binary can be reused without another cold build.
3. It requires every cell trust-ir's reader answers to rest on the ground
   trust-ir answers for it (an unknown ground is `ground-unknown`), and checks
   what each ground implies: instruction-model queries degenerate (`(assert
   false)`) with no pin, certificate queries not degenerate, each with
   exactly one pin, its sha256 equal to that pin (`query-digest-mismatch`) and
   its single assertion stating trust-ir's spec side verbatim
   (`spec-not-trust-ir-statement`: this pins that the query's simplification
   passes the spec through, not the spec's provenance, which the manifest
   test holds), fail-closed cells exactly when the reader says so and with no
   pin, and every pin used exactly once.
4. For each certificate-ground cell it runs AY with the rule's arguments
   (`-smt2 Q --strict-proofs --proof P --proof-format alethe`) and requires
   one `unsat`, AY's `c ay.proof.certificate` report with the rule's fields
   (`unproved_steps=0 foreign_assumes=no trust_free=yes`), and no step of the
   rule's unchecked rules (`hole`, `lia_generic`) in the proof; then `clean
   cert verify-external --verbose`, whose EXIT STATUS is the verdict (it
   exits non-zero on a proof it does not verify in full) and whose
   `Proof status: fully verified` line is a second check (Clean runs the
   Carcara Alethe checker there; no Clean-kernel term is built). AY and Clean
   run with a minimal environment, and both binaries are re-hashed after the
   run.

A missing toolchain input (no Trust package, no AY or Clean source holding
the rule's revision) FAILS the leg.
`SOUNDNESS_SKIP_X86_ICMP_CERTIFICATES=1` turns exactly a missing input into a
loud SKIP (which leaves the run incomplete and nonzero); it never covers a
wrong input, and an `--attest` run refuses the variable in its preflight. The
script runs on its own too (`--skip-missing-toolchain`, `--json-out`,
`tools-path` to obtain the rule's two tools only). `--queries DIR` re-runs a
dump the caller supplies instead of regenerating it; its rule, grounds and
pins are then `DIR/manifest.json`'s, not the compiled trust-ir's, so such a
run is never a pass: without a finding it prints `SUPPLIED-DUMP` and exits 4,
and its report records `queries.source = "supplied"`. The leg never passes
it.

A pass is an SMT proof that the rule's AY produced for each cell's exact
query, which the Carcara Alethe checker inside the rule's Clean `cert
verify-external` accepted in full. It is a checked SMT proof, not a kernel
certificate and not a Lean theorem. It trusts (1) that checker: vendored
Carcara with Clean's downstream soundness fixes, unverified software with a
documented record of false accepts, built by `targo --unverified` into bytes
that are not reproducible; (2) the tie of trust-ir's bit-vector statement of
`ICmp`, which this backend's spec side now is, to trust-ir's `ICmp`
semantics, which trust-ir holds by tests (its interpreter and Lean
differentials), not by proof; (3) this backend's SMT models of the x86
instructions, the machine side. It does not bind an obligation to the bytes
instruction selection emits per compile, and the eight instruction-model
cells remain a trusted-base fact. It runs only when `soundness_check.sh`
runs, which a landing does only through the opt-in hook or the landing
train, so a query re-pinned to a holey digest lands unless someone runs the
leg (`x86_icmp_manifest_cells` catches a changed query, not one re-pinned to
its new digest). The toolchain's AY is no substitute for the rule's: it
answered `unknown` on the 32 composite queries under `--strict-proofs`.

## Attestation records

A green `scripts/soundness_check.sh --attest` run on commit `C` writes one
record per host, locally:

```text
refs/attest/soundness/<C>/<host-triple>
```

A record is a Git commit whose single parent is `C` and whose tree holds
`attestation.json` plus per-leg evidence under `legs/` (the result parser's
summary of each Cargo leg and the last lines of every leg log), so a record can
be audited after the run's log directory is gone. It is never a commit on a
branch, and each host writes its own ref, so hosts never contend. The local
record and the x86-64 record it imports are created in one atomic ref
transaction at the end of a green run (the imported record waits at
`refs/soundness/import/<C>/<triple>` until then and is deleted when the run
stops), so a run that fails or stops leaves nothing under `refs/attest/`.
Nothing is pushed by the gate; `python3 scripts/soundness_attestation.py push
<C>`, a plain `git push <remote> 'refs/attest/soundness/<C>/*:refs/attest/soundness/<C>/*'`
(the hook) or the landing train sends the records to a remote, and `fetch` (or
the matching `git fetch`) brings them back. `attestation.json` (schema `trust-cg-soundness-attestation-v1`)
records:

- the subject commit and its tree, and the scope (`full`; `portable`, every
  per-run and host-independent leg and no x86-64-native class, a landing record
  only; or `x86_64-native` for the remote side);
- the host: triple, OS, machine, Rosetta translation, CPUID vendor, brand and
  hypervisor bit, `/proc/cpuinfo` vendor, and the native-x86-64 verdict with
  its reasons;
- the blobs of `scripts/soundness_check.sh`, `scripts/soundness_attestation.py`,
  `scripts/matrix_results.py`, `scripts/gate_env.sh`, `scripts/trust_cargo.sh`
  and `scripts/trust_toolchain.py` at `C`;
- the declared leg inventory and its digest;
- the dependency tuple: TrustIR, Clean and AY revisions resolved from `C`'s
  three Cargo locks (as `--validate-dependency-locks` does), and the aterm
  commit, origin and vt-table SHA-256;
- whether that Trust package is a derived overlay
  (`toolchains.trust.overlay`: the digest of the `overlay.json` at its sysroot,
  or `null` when there is none; a record without the key is refused);
- the EXECUTED binaries: the Trust package's `trustc` and `targo` (the one
  `scripts/trust_toolchain.py` resolves and `scripts/trust_cargo.sh` runs) and
  its `bin/ay` by SHA-256 (with `ay`'s build stamp read from its bytes),
  cross-checked against the `executed-ay` line `proof_gate_strict`'s
  `executed_ay_identity_is_reported` prints (the AY that test binary admits, by
  the toolchain route only), and the Clean checker binary the proof checks ran;
- `trustc -vV` (branded, with its 40-hex commit), Lean, Node, the island twin
  (`ISLAND_TWIN_RUSTC`: path, SHA-256 and `-vV`) and, on an x86-64 leg host,
  `cc` and `objdump` identities;
- the environment report (below) and every leg's status, detail, seconds and
  log digest; a full record on a non-x86 host also names the imported x86-64
  record by object id.

Records are unsigned today. The schema carries a `signing` object;
`soundness_attestation.py write --sign` signs the record commit with Git's own
commit signing and `verify --require-signature` requires `git verify-commit` to
accept it, so a signing policy (an `allowedSignersFile`) is configuration, not a
schema change. Until then anyone with push access to a remote can forge a
record.

### What `verify` requires

`python3 scripts/soundness_attestation.py verify <C>` exits 0 when `C` is
attested, 1 when a record is incomplete or failing, 2 when one is malformed and
3 when there is none. This is the RELEASE verdict; `verify --landing` is the
landing verdict (see "Landing and the release boundary"). It requires:

- every record's single parent is `C`, its subject tree is `C^{tree}`, its host
  triple is the one its ref names, and its runner blobs, inventory digest,
  dependency tuple and compiler are the ones `C` itself names (for
  `channel = "trust"`: a branded `trustc` with a 40-hex commit whose `-vV`
  names the recorded host, a `targo` of the same build, both bound by
  SHA-256, and, when `C`'s `scripts/run_public_release_checks.sh` pins an
  exact Trust compiler for that host (`<host>) expected_trustc='...'`), exactly
  that `trustc --version` line; a host without a pin (today the x86-64 hosts)
  is reported and its identity recorded, not compared; for an older numbered
  stock channel, that `rustc` release);
- every record contains exactly the legs of `C`'s inventory for its scope and
  host (`scripts/soundness_check.sh --list-json` at `C`), all PASS, and every
  Cargo leg's stored parser summary is `pass`;
- a full-scope record exists (it carries every per-run and host-independent
  leg), and every `x86_64-native` leg passed in a record whose host fields show
  native x86-64 execution (a record from any other host that carries one is
  malformed); a `portable` record never satisfies this verdict, and the
  landing deferral is never read;
- no record was made on a derived overlay toolchain (an overlay is not a
  release input, ruling OD-RELEASE-BOUNDARY-20261008), and every record states
  whether it was;
- the full (or portable) record binds the executed AY (its probed SHA-256
  equals the campaign's, and its version is the `ay-pb` pin version), the Clean
  checker and the aterm dependency; the AY's build commit is reported, not
  required to equal the pin revision;
- the environment report is the `allowlist-v1` policy, refused nothing, found
  no uncommitted Cargo configuration, and `WASM_CFG_FUZZ_FUNCS` is at least its
  floor; every recorded setting is re-classified by the verifier's OWN
  allowlist, so a record that calls `PYTHONPATH` "recorded" is refused.

`verify` reads the records, blobs and pins it judges before it executes `C`'s
`scripts/soundness_check.sh --list-json` (the one piece of `C`'s code it runs,
to read `C`'s declared inventory), so that code cannot change what the verdict
is based on; its output is held to the record's inventory digest and, anchored,
to the anchor's inventory.

### Anchored verification

A commit that weakens `verify` or drops a leg from its own inventory would pass
its own verifier. `verify-anchored <C> --anchor <A>` therefore runs the verifier
committed at `A` — an already-landed proper ancestor such as the remote main
being replaced — against `C`, and that verifier also refuses a leg in `A`'s
inventory that `C` removed (unless named with `--accept-removed-legs`), refuses
a leg that leaves the `x86_64-native` or `per-run` class or becomes a
`dispatch` row, refuses a per-host Trust compiler pin that `A` has and `C`
dropped, and lists every gate-surface file `C` changed since `A` (the gate, the
tool, the remote executor, the result parser, `gate_env.sh`, `trust_cargo.sh`,
`trust_toolchain.py`, the exporter, the train, `landing_checks.sh`, the pin
file and the hook) for review.

A commit never anchors its own verification: `verify-anchored` refuses
`A == C` and an `A` that is not an ancestor of `C` (exit 2), and `verify
--anchor C` of `C` itself is a failing verdict. When `A` predates the tool (the
bootstrap) `verify-anchored` refuses too, unless `--allow-unanchored-bootstrap`
asks it to run `C`'s own verifier, whose verdict is then labelled `UNANCHORED
(bootstrap)` and is not an anchored attestation. The runner itself is trusted to
run the legs it records; the anchored notice is what exposes a change to it.

The pre-push hook and the landing train do not route this through `C`'s copy of
the tool: they extract `scripts/soundness_attestation.py` (and the result
parser) from `A`'s tree and run its `verify C --anchor A` directly with
`python3 -I`, and they fetch and push records with plain `git`. `C`'s
`scripts/soundness_attestation.py` therefore runs nowhere in the hook or the
train; `C`'s committed code still runs as the hook itself (it is read from `C`'s
tree), as `C`'s `--list-json` inside the anchored verifier, and as `C`'s gate
on the slow path. Records are unsigned, so a `C` whose own gate code writes a
complete false record is not caught by the hook; client-side enforcement is only
as strong as the pushing clone, and the release boundary repeats the anchored
verification. `scripts/test_pre_push_hook.sh` covers a `C` whose verifier always
answers "attested" and a `C` whose tool forges a record whenever it runs.

With no landed anchor — a first push of main, a remote main this clone never
fetched, a forced or otherwise non-fast-forward push, or an anchor that carries
no committed verifier — the hook and the train BLOCK: no landed verifier exists
to judge `C`. An anchor that is itself unattested is named in the hook's verdict
next to the predecessor notice.

### The environment allowlist

An `--attest` run's legs see only an allowlist of environment variables.
Before anything else the script re-executes itself through
`soundness_attestation.py exec-scrubbed`, which passes on only the allowlisted
variables of its caller:

- recorded with their values: `PATH`, `HOME`, `TMPDIR`, `USER`, `LOGNAME`,
  `SHELL`, `LANG`, `LC_*`, `TZ`, `SDKROOT`, `DEVELOPER_DIR`,
  `MACOSX_DEPLOYMENT_TARGET`, `XDG_*_HOME`, `CARGO_HOME`, `CARGO_TARGET_DIR`,
  `CARGO_BUILD_JOBS`, `RUSTUP_HOME`, `RUSTUP_TOOLCHAIN`, `RUST_MIN_STACK`,
  `RUST_TEST_THREADS`, `RUST_BACKTRACE`, `ELAN_HOME`, `ATPKG_BIN`,
  `GIT_EXEC_PATH`, `GIT_CONFIG_GLOBAL`, `GIT_CONFIG_NOSYSTEM`,
  `GIT_SSH_COMMAND`, and the gate's own settings (timeouts, source and deps
  directories, `ATERM_DIR`, `SOUNDNESS_X86_HOST`, the island twin
  `ISLAND_TWIN_RUSTC`, `WASM_CFG_FUZZ_FUNCS` of at least 200, and
  `SOUNDNESS_EXTRA_GROUP_FILE`/`SOUNDNESS_EXTRA_PASSWD_FILE`, account entries
  the host trust boundary adds to the host's and that can only make a group
  count as shared);
- the gate's controls at their only allowed value:
  `TRUST_CG_RUN_FORMAL_PROOF_TESTS=1` (required), `TRUST_CG_RUN_ROSETTA_LINKRUN=1`,
  `TRUST_CG_REQUIRE_X86_SILICON=1`, and `TRUST_CG_DIR` naming the script's own
  checkout;
- `CPATH=/usr/local/include` and `LIBRARY_PATH=/usr/local/lib` exactly, which
  the macOS `/usr/bin/python3` launcher adds to every process it starts (so
  every leg run through a Python helper sees them); they name the default
  compiler and linker search directories;
- inert terminal and session plumbing (`TERM*`, `SSH_AUTH_SOCK`, `XPC_*`,
  `MANPATH`, ...), whose names are recorded and values are not.

A caller variable whose name is known to change a leg is REFUSED, with its
reason, by the preflight row `preflight: leg-weakening settings`: `PYTHON*`,
`NODE_*`, `DYLD_*`, `LD_*`, `LEAN_*`/`ELAN_*`/`LAKE_*` (other than `ELAN_HOME`),
every other `CARGO_*` and `RUST*`, `CC`/`CXX`/`CFLAGS`/`LDFLAGS`/`CPATH`/
`LIBRARY_PATH` and the per-target C toolchain variables, `BASH_ENV`, `ENV` and
exported bash functions, other `GIT_*`, other `TRUST_*`, `TRUST_CG_*` and
`TCG_*`, `AY_*`/`CLEAN_*`, `PERL5LIB`-style interpreter injection, unknown
`SOUNDNESS_*`/`ISLAND_*`/`WASM_*` settings, and the explicit input substitutes
`CLEAN_DIR`, `AY_DIR`, `ISLAND_VT_TABLES`, `TRUST_TARGO`, `AY_SOLVER_PATH` and
`SOUNDNESS_SSH`. Any other variable is dropped before the legs run and only its
name is recorded. After the re-execution `check-env` refuses any variable
outside the allowlist, so setting the re-execution marker by hand cannot
smuggle one in. It also refuses an uncommitted Cargo configuration file that
applies to the legs: `.cargo/config.toml` or `.cargo/config` in the checkout, the
deps directory or any of their ancestors, or in `$CARGO_HOME`, unless the
repository that directory belongs to tracks it (the checkout's own
`.cargo/config.toml` is `C`'s). A caller that exports a refused variable must
unset it (for example `env -u PYTHONPATH scripts/soundness_check.sh --attest`).
A census run only prints what `--attest` would refuse.

### The host trust boundary

X-HOST-P13 makes private what trust-cg and the gate create, cache or choose to
execute (the AY copy, the pinned checkouts and their builds, the JIT caches,
the solver memo, the proof export). The user's own toolchain installs
(rustup/cargo, elan/lake, the Trust package), git and its configuration, and
the candidate checkout are the host's trust boundary: no tool can defend a
build against a user who can rewrite the compiler (ruling LD-73). An
`--attest` run still fails closed there. Once its PATH prelude is applied and
its flags are parsed (a usage error exits 2 first), before it starts any
program but bash and python3 (`dirname` and `basename` are parameter
expansion until then), it runs `scripts/host_boundary.py`, which
judges, resolving every path hop by hop: every PATH directory and every
command in it; the running python3 and its own `-I` import path (the
standard library and site directories, with what their `.pth` files and
`sitecustomize` add: every python3 the gate scripts start is that same
interpreter, runs with `-I` and imports from there); the gate's pinned
python3 (`SOUNDNESS_PYTHON3`, below), judged as exactly that file with every
directory it is looked up in and refused unless it is the interpreter
running the check (by canonical path and by device and inode, no `#!`
script, and on Linux the file `/proc/self/exe` names); the python3 a leg
starts by name on the prelude's PATH, refused unless it is that pinned file
reached by a name around which python3 reads no other `pyvenv.cfg` (so the
legs' interpreter and import path are the ones judged here); and what a
python3 run without `-I` (a leg's) adds to it at startup: each directory a
`.pth` file in the user site-packages names, as a tree (a `.pth` line
python3 executes, a `sitecustomize` or `usercustomize` module there, and a
`.pth` file holding a byte outside ASCII or a character `str.splitlines`
breaks a line at other than `\n` and `\r` refuse, since what that code puts
on the path can be judged only by running it, or the lines python3 reads
are not certainly the lines judged); the gate's bash and
`/usr/bin/env`; `HOME` and `XDG_CONFIG_HOME`; `TMPDIR` (else `/tmp`),
writable by others only with the sticky bit; as whole trees `CARGO_HOME`,
`RUSTUP_HOME`, `ELAN_HOME`, the Trust package of the PATH `trustc` and
`targo`, the island twin rustc's install, aterm's managed packages,
`CARGO_TARGET_DIR` when set, python3's user site-packages, node's global
module folders, on macOS `~/lib`, the candidate checkout and the git directories
of it and of the Clean, AY and aterm sources; git's configuration files and
exec path, and the programs and hooks directory that configuration names;
and, in every run (ruling OD-XHOST-FETCH-TRANSPORT-20261016: a pinned checkout's
`git fetch origin` may use ssh whether or not an x86-64 executor is
configured), `~/.ssh` and `/etc/ssh` and the program each of
`GIT_SSH_COMMAND`, `GIT_SSH`, `GIT_PROXY_COMMAND`, `core.sshCommand` and
`core.gitProxy` names. It refuses any of
them that another user can write: world-writable, group-writable by a group
with a member other than this user (`/etc/group` members and every
account's primary group; a name or gid with no entry, or an account source
it cannot enumerate, counts as another member), owned by another account (a
system account's file in a root-owned directory, such as Ubuntu's setuid
`/usr/sbin/lldpcli`, is accepted and listed), or writable through a POSIX
ACL. A group-writable path in a group with no other member passes. On a
refusal the run prints every path, a `[FAIL] preflight: host trust boundary`
row with the remedy and `no attestation record`, and stops there, even with
`--keep-going`; nothing else runs. A passing check is the per-run row
`preflight: host trust boundary`, its report kept as
`<LOGDIR>/host-boundary.log`. `SOUNDNESS_EXTRA_GROUP_FILE` and
`SOUNDNESS_EXTRA_PASSWD_FILE` add account entries (the tests stand in for a
shared group with them); they cannot make a group private: a gid only they
name stays a group with no entry, and a member only they give an account
stays a name with no account (ruling LD-75).

The check does not judge the caller's working directory, so since ruling
OD-XHOST-GATE-CWD-20261025 (2026-10-25) an `--attest` run starts nothing
there. It changes to `/` before its first program (the scrub's python3; `/`
is root's, every judged path is resolved through it, and it holds no
repository the gate uses), and to the candidate checkout, which the check
judges as a whole tree, as soon as the check has passed: the landing train
and the pre-push hook start the gate there, and a manual run now works where
they do. Every python3 the gate and the scripts it starts run, inline
(`python3 -c`, `python3 -`) or a script (the bounded runner, which the gate
no longer starts by its `#!/usr/bin/env python3` line, and the Trust
toolchain resolver in `trust_cargo.sh`, `check_fmt.sh`, `check_tippy.sh`,
the attestation tool and the x86 certificate check), has `-I`, which leaves
the working directory, a script's own directory and the user site-packages
off `sys.path` and ignores `PYTHON*` variables (a gate script that imports a
sibling module inserts the judged candidate's `scripts/` itself). A static
test holds every gate script and the Python tools they start to that, and
every `cd` of the gate scripts to `CDPATH= cd`. Before its
first program the run also finds its own directory with bash builtins and
CDPATH ignored, refuses a directory that does not hold the very script bash
runs, and refuses a relative or empty PATH entry, as the check would
(repair round 2 of the ruling: started as `scripts/soundness_check.sh
--attest`, the gate had looked its directory up in an exported CDPATH and
the scrub had run a `soundness_attestation.py` from a directory nothing
judged; a relative PATH entry found the scrub's python3 relative to the
working directory). Before the ruling the sixth closure audit ran a full
portable `--attest` from a `0777` directory holding a `0666` `json.py`: the
check passed, the gate's own `python3 -c` (leg inventory, host identity) and
`python3 -` (aterm json), and `gate_env.sh`'s `python3 -`, imported it, and
the run ended green and wrote its record; the identities step also ran
`lake --version` there, so a `lean-toolchain` in the caller's directory
chose the record's `toolchains.lake`. An `--attest` run takes no path
argument, its own directory is absolute (found without CDPATH) before the
first `cd`, and every path setting the gate or a leg resolves is refused
when it is not absolute (LD-75 and the rules above), so the change of
directory changes the meaning of no relative path the caller passed; a
CDPATH the caller exported is refused by the scrub (`preflight:
leg-weakening settings`); a relative value
of a recorded variable no rule judges or uses (`XDG_DATA_HOME`, `SDKROOT`,
`DEVELOPER_DIR`, `TRUST_AY_TARGET_DIR`; a relative `XDG_CACHE_HOME` is
ignored) now resolves in the
candidate checkout for a program that reads it, as in a landing-train run.

Repair round 3 of that ruling (2026-10-25) closes two fail-opens older than
the ruling (present since `fa2d651e8`) that its second verification found.
The `gate_env.sh` prelude puts `$HOME/.elan/bin` first on PATH, and the
check's own python3 was found by name after it: not the interpreter the
earlier checks and the scrub saw, and possibly one in a directory nothing had
judged yet, which ran first. The gate now resolves python3 where every PATH
entry has been checked and before the prelude (in an `--attest` run once in
each of its two bash runs, which must agree): `type -P python3` (a
builtin) finds it, it prints the canonical path of its own executable (run
with `-I -S`: no site directory, no `.pth` file), and the gate starts every
python3 by that path from then on, `SOUNDNESS_PYTHON3`, whatever PATH names
first later: the scrub (which exports the canonical path of the interpreter
it runs as; the re-executed run refuses unless it agrees with its own
resolution before the prelude), the cache-base rule, the check (`--python3`,
judged as above) and every tool; the gate exports it to the helpers that
start python3 (`gate_env.sh`'s check, `trust_cargo.sh`,
`soundness_remote.sh`'s local half), which use it when it is set and
otherwise resolve their own once, as `land_main.sh`, the pre-push hook,
`check_fmt.sh` and `check_tippy.sh` do; the scrub runs the gate's bash by
its canonical path too. `SOUNDNESS_PYTHON3` is the gate's own, never an
input: a caller's value refuses an `--attest` run before any program (a
census run replaces it and its note names it); the environment report
carries no row for it (the `allowlist-v1` rules are unchanged) and refuses
one that is not the interpreter running the report. A static test holds
every gate script to starting python3 only by the pinned path after its pin
point. And a run whose script bash read from standard input (`bash -s --
--attest < .../scripts/soundness_check.sh`) or a `-c` string had no
`BASH_SOURCE`, so the directory check judged `$0` (the shell's name or any
word the caller chose) and a `soundness_attestation.py` in the caller's
working directory ran before the check and the run attested. An `--attest`
run is now refused, with builtins and before any program, unless bash reads
it as a script from the candidate's `scripts/soundness_check.sh` file: one
read from standard input or a `-c` string, one sourced into another shell,
and one whose file is not the candidate's `scripts/soundness_check.sh`
(`bash /dev/stdin`) each refuse, naming the remedy (run the script file).

Repair round 4 (2026-10-25) closes what round 3 left open, found by its
verification. The pin covered the gate's own python3 runs, but the legs (a
Cargo test, a Clean test, a `#!/usr/bin/env python3` script) start python3
by name on the prelude's PATH, while the check judged the pinned
interpreter's import path and user site-packages only: a python3 in
`$HOME/.elan/bin` running a virtual environment's interpreter, whose
site-packages any user could write, was the legs' and the run attested
(`8b127f2a4`, whose check ran python3 by name, refused it). A virtual
environment's `bin/python3` first on the caller's PATH did the same without
the prelude: it is a symlink to the base interpreter, which the gate pins,
while a leg running it gets the environment's site-packages. The check now
finds python3 on the PATH it is given (the prelude's) as a lookup does and
refuses the run unless that file is the pinned one (canonical path, device
and inode) and python3 reads the same `pyvenv.cfg` for the name it is found
by as for the pinned name (each one it would read is judged as a path no
other user may create or change): a wrapper, a copy, another installation
or a virtual environment's python3 there refuses without running, and the
remedy is to remove it or deactivate the environment. The pin itself is
refused when it is a `#!` script or, on Linux, not the file `/proc/self/exe`
names: python3 derives its own executable name from `argv[0]`, which a
wrapper that runs another binary under its own name (`exec -a`) chooses
(macOS has no `/proc/self/exe`; a compiled launcher doing that there stays
unjudged). And the two scripts an `--attest` run starts before the check,
the cache-base rule and the check itself, are named by the gate's own
directory, the candidate's `scripts/` that holds the very file bash runs,
never by a caller's spelling of `TRUST_CG_DIR`.

Ruling LD-75 closes four gaps the check had at `fa2d651e8`. Every object
store a judged git directory borrows objects from (`objects/info/alternates`,
followed through the alternates of each store named) is judged as a whole
tree; an alternates file the check cannot read or parse, an entry naming no
directory, an `objects/info/http-alternates` file, and a
`GIT_OBJECT_DIRECTORY` or `GIT_ALTERNATE_OBJECT_DIRECTORIES` in the check's
environment refuse (the environment allowlist already removes and refuses
both). A directory whose POSIX default ACL would let another user write what
is created in it refuses, since a default ACL overrides the umask; once the
check has passed, the rest of the `--attest` run, every leg included, runs
under umask 077, and a git configuration whose `core.sharedRepository` is
anything but `umask` or false refuses, since git would then set the modes of
what it writes itself. Cargo reads `.cargo/config.toml` from its working
directory and every ancestor, so a candidate checkout, `SOUNDNESS_DEPS_DIR`
(where the Clean and AY checkouts are built), the user cache's `trust-cg`
directory, `CARGO_HOME` or `CARGO_TARGET_DIR` below any directory in which
another user can create an entry refuses, sticky or not, unless that
directory is sticky and already holds a `.cargo` directory of this user's
(judged as a tree). **An `--attest` run's checkout, cache and Cargo home,
given as absolute paths, cannot live below `/tmp`** unless it already holds
that `.cargo`; an ancestor whose default ACL would open what is created in it
refuses whether or not it holds one. Since LD-75's repair (2026-10-16) the
check refuses `CARGO_HOME`, `CARGO_TARGET_DIR`, `RUSTUP_HOME`, `ELAN_HOME`,
`SOUNDNESS_DEPS_DIR` or `ATPKG_BIN` set to a value that is not an absolute
path (an empty one included), naming the variable and the remedy (unset it or
make it absolute): Cargo, rustup, elan and the gate resolve such a value
against their working directory, which the check does not judge, and it had
skipped every root that was not absolute. A tree root or `--cargo-root` that
is not absolute refuses too, and so do an empty `TMPDIR` (Rust's
`std::env::temp_dir()` returns the empty path, so temporary files would land
in the unjudged working directory) and a program a git configuration key
names by a relative path with a slash (git runs it from its working
directory). Ruling OD-XHOST-FETCH-TRANSPORT-20261016 (2026-10-16) judges the
fetch transports in every run: before it, `GIT_SSH_COMMAND` was judged only
with an x86-64 executor and only by an absolute first word, so a program in
a `0777` directory, or one named relative to the Clean source's work tree,
ran during the preflight's `git fetch origin` and the run attested. Each of
`GIT_SSH_COMMAND`, `GIT_SSH`, `GIT_PROXY_COMMAND`, `core.sshCommand` and
`core.gitProxy` that is set is judged as git runs it (its words split where
the shell splits them, not at U+00A0): an absolute or `~/`
program is resolved, a bare name is found on the judged PATH, and a relative
path with a slash refuses, as does a value that is empty, holds a character
the shell gives a meaning beyond separating words, begins with an
assignment, or (a program git runs without a shell) holds whitespace; that
ruling also judged every later word of an ssh command that names a path the
same way, a clause the next ruling replaced. A
`protocol.allow` or `protocol.ext.allow` other than `never`, and a
`GIT_ALLOW_PROTOCOL` that lists `ext`, refuse: git's `ext::` transport runs
the command a remote URL names. Ruling OD-XHOST-TRANSPORT-WORDS-20261024
(2026-10-24) closes the round-5 verifier's three fail-opens and three lows,
in a second repair round the five git-command-key shapes two verifiers ran
to an attestation at `9352c20f1`, and in a third the sources git used from a
directory other than the one judged (a `core.worktree` at an ancestor and a
source that is a subdirectory of Clean, each run to an attestation at
`f7919800a` and at `4a0668957`) and a Unicode-whitespace `!` prefix
`9352c20f1` had let pass, and in a fourth an alias a judged command key runs
(`remote.origin.uploadpack = git x` with alias x `!sh <program>` or
`-c uploadpack.packObjectsHook=<program> upload-pack`, a program in a `0777`
directory, each run to an attestation at `a6cbba41b` and at `4a0668957`)
and an alias `!! <program>`, which `4a0668957` refused and `a6cbba41b` let
run; it supersedes OD-XHOST-FETCH-TRANSPORT-20261016's
later-word clause and its "Not covered" list. It refuses any judged path
whose canonical resolution enters `/proc`
or `/dev/fd` (those name the checking process's own view of the filesystem,
not the view git's child has from its working directory, so
`GIT_SSH_COMMAND=/proc/self/cwd/tools/evil` would run elsewhere than it is
judged), in every lookup, every tree, the Cargo ancestry search and an
atpkg shim's exec target. For `GIT_SSH_COMMAND` and `core.sshCommand` it
accepts the program alone and refuses ANY later word (the remedy is
`~/.ssh/config`, which it judges). It judges each `--git-repo` WORK TREE
(the Clean, AY and aterm sources, where the fetch, its lazy fetches and
`git worktree add`'s parent run) as a whole tree, and `$SHELL` (absolute or
refused), `/bin/sh`, and `~/.ssh` of the passwd home as well as of `$HOME`.
For the candidate, each `--git-repo` and each Cargo git database
(`$CARGO_HOME/git/db/*`, whose configuration it now lists), it asks git
which work tree and git directory it uses (`git rev-parse`) and refuses
unless they are the directory itself (a bare repository: as its git
directory) and the git directories it judged: a `core.worktree` naming an
ancestor or any other directory, a subdirectory of a repository or a
directory with no `.git` of its own, a `core.bare` on a work tree's `.git`
and a `GIT_DIR` naming another repository each refuse. The gate asks git
the same of each pinned checkout before its first `git status` and refuses
one whose work-tree top or common git directory is elsewhere (a
`core.worktree` in its `config.worktree`). Every other git command key,
`alias.*` included (a judged command can run git with an alias:
`remote.origin.uploadpack = git x`), is read by the text of its words. git
strips exactly one leading `!` from an alias or a credential helper and none
from any other key; after it only blanks and newlines are skipped, as by
`/bin/sh`, so `!<U+00A0>/x` refuses as the relative program it is. In a
shell command (every value but an alias without `!`), a shell
metacharacter, a first word the shell reads as reserved (`!`, `if`, `time`,
`[[`, ...) or that begins with `!` (`!! /x` runs /x), a first word holding
`=` (`PATH=.. prog`; `LESS=FRX less` is over-refused), a word naming git
followed by a git option (`git -C <dir>`, `--git-dir=`, `-c`; an alias such
as `!git -C <dir> status` is over-refused), and a later word that sets the
environment, holds `..`, holds a `/` or `~` without being exactly an
absolute or `~/` path or a plain `--option=` followed by one (`-S/x`,
`tools/x`, `~user/x`; a sed script `s/a/b/` is over-refused), names such a
path holding `:`, `,`, `=`, `%` or a later `~`, or holds a character outside
`[A-Za-z0-9_.,:@%+=-]` all refuse; an absolute or `~/` later word is
resolved (a directory as a whole tree), and a plain word passes. An alias
without `!` is git's own argument list: a first word that is a git option
(`-c`, `-C`, `--exec-path`, `--git-dir`, `--work-tree`, `--config-env`, ...)
refuses, and every word is read as a later word is
(`fetch --upload-pack=<path>` judges the path). A plain
word's text names nothing outside git's working directory and PATH, and,
per the ruling's inventory of the gate's git commands and Cargo's git
fetch, git starts a configured program only in a directory the check judges
as a tree and verifies is the one git uses (a `--git-repo` work tree, the
candidate, a Cargo git database; a pinned checkout, judged by
`require-private-tree` and verified by the gate), or in the new pinned
checkout `git worktree add` creates under umask 077 in the private deps
directory and `require-private-tree` judges right after; the check's own
`git var` and `git --exec-path`, run in `/` in no repository, start none,
and since ruling OD-XHOST-GATE-CWD-20261025 no git the run starts runs in
the caller's working directory (until then `rev-parse --local-env-vars` and
the identities' `git --version` ran there and started none). A path git
reads from a key (`core.hooksPath`, `core.attributesFile`) is judged as git
reads it, not whitespace-stripped. This host's credential helper
`!/usr/bin/gh auth git-credential` keeps passing: a root-owned program, two
plain words.

Ruling OD-XHOST-GIT-PROGRAM-KEYS-20261024 (2026-10-24) completes the round-5
repair: the round-4 verification confirmed the transport-words repair but
REFUTED a PRE-EXISTING class. A judged git command key reached a
program-valued key the check never listed (`remote.origin.uploadpack = git
web--browse -b <tool>` runs `browser.<tool>.cmd`; `diff.external` through
`--ext-diff` and the `difftool`/`mergetool` `.cmd` keys are the same shape;
R1); git passes a local-path remote's path to a configured upload-pack
command as its last argument, so `uploadpack = sh` runs a script such a
remote names (R2); and `exec-scrubbed` ran PATH's git before the boundary
judged PATH (R3, finding (7)). The set of program-valued keys is open and
cannot be listed completely, so the run's git reads only JUDGED
configuration. Every git the gate starts runs with `GIT_CONFIG_NOSYSTEM=1`
and, as its global configuration, only a file the boundary writes on a pass,
carrying the credential helper(s) the https origins need, the commit identity
and `core.excludesFile` — the keys it judged from the user's system and
global files — and nothing else (it reads the file back with git and refuses
if it does not read as written; the run removes it when it exits). The
repository-local and worktree configuration of every repository the gate
runs git in is judged COMPLETELY: every key refuses unless it is on a short
allowlist of keys that name no program (data keys, plus the five path keys
judged above). Those repositories: the candidate, each `--git-repo`, each
Cargo git database and checkout, each pinned checkout (before its first
`git status`), each local repository a remote names, each submodule git
directory below `<git-dir>/modules`, and — since the round-2 repair, after
both verifiers showed the gate's `git status` entering an EMBEDDED submodule
(or one whose `gitdir:` file names a directory elsewhere) and running its
`core.fsmonitor` with an attestation written — every repository nested in
the work tree of one of them, recursively: every directory there holding a
`.git` and every gitlink path of the index holding one (a symlinked path
included). Each nested repository is judged as a tree with its git
directories, git's view of it must give its own path as the work-tree top,
and its configuration is held to the allowlist. Since the round-3 repair,
each kind of judgement of a repository (its configuration, its nested walk,
as a nested repository, as a local remote) is made once per repository and
never stands in for another, so a populated submodule that a remote also
names as a local repository (judged first as that, without git's view of a
work tree, which upload-pack does not use) still gets the nested judgement:
its `core.worktree` naming a `0777` directory, from which the gate's `git
status` ran a program a nested repository there configured, refuses. A
`remote.*.uploadpack`/`receivepack` refuses outright in every scope (R2); a
`remote.*.url`/`pushurl` (and `submodule.*.url`) naming a local path or
`file://` repository is judged as a repository the run uses git in (tree,
git directories, alternates, configuration), and a relative, `~`, `ext::` or
non-plain `file://` location refuses; so is a local `branch.<n>.remote`,
`branch.<n>.pushRemote` or `remote.pushDefault` naming neither `.` nor a
configured remote. A file in a git directory's `remotes/` or `branches/`
refuses, and the preflight's `git fetch --no-recurse-submodules origin`
refuses to run when the source defines no `remote.origin.url`. A new git
key, or one a helper or extension runs, is refused until it is reviewed and
added — the fail-closed direction. R3: `isolate_git_environment` in
`soundness_attestation.py` runs no program before the boundary (it drops a
fixed superset of git's repository-local variables, checked against the
installed git by a test), and
`EDITOR`/`VISUAL`/`PAGER`/`LESS`/`GIT_EDITOR`/`GIT_PAGER` are dropped from an
attested run (one that reaches the legs past the scrub refuses it). The
writer scrubs more than the `allowlist-v1` rules allow, which stay as
records were written under them: the verifier re-derives each environment
row's verdict, and those six are still `inert` there (round 3 restored that;
the first repair had changed their verdict under the same policy name, so
its verifier refused 25 of the 26 local records). Measured read-only at the
round-3 repair (2026-10-24) over the 26 commits with a local
`refs/attest/soundness` record: the repair's verifier and `96226db68`'s give
identical release and landing verdicts on all 26. The user's system and
global files are still read and judged
by the command, transport and path rules (the check's own git reads them,
and Cargo's built-in libgit2 ignores `GIT_CONFIG_GLOBAL`/`GIT_CONFIG_NOSYSTEM`
and reads them itself; the only programs Cargo runs from them are its
credential helpers, which are judged; libgit2's default files, `/etc/gitconfig`,
the XDG git config and `~/.gitconfig` with their includes, are judged even
when the caller's `GIT_CONFIG_GLOBAL` names another file), so a global key those rules refuse
still refuses the run, as before (a global alias holding a quote, for
instance), and a global `remote.*.uploadpack` now refuses too. A Mac host's
ordinary configuration (`credential.helper=osxkeychain`, a plain
`core.editor` or `core.pager`, plain aliases) passes those rules; only the
helper is carried into the run's file, and only a repository's own local
configuration is held to the allowlist. Still not judged: what a judged
program makes of a plain later word by its own rules (an option that selects
a file of its choosing, such as a login shell's `-l` reading `~/.profile`;
the check reads the words' text, not each program's grammar), such as a git
a judged program starts by its own option in a directory outside every
judged work tree (`env -C /abs/dir git ...`: the directory is judged as a
tree, the configuration of the repository git finds from there is not) or
under another name, or in a bare repository nested in a judged work tree
that is no `.git`; the keys of a repository holding another directory with
a `.cargo` Cargo reads (the Cargo configuration check runs `git ls-files`
there with `core.fsmonitor` off on its command line, so it runs no
configured program; `$HOME` is no repository on this host); a git another
tool starts in a repository none of the rules above reaches (Lake's in a
package outside a judged work tree); what an ssh configuration names (its
programs, an `Include` from outside `~/.ssh` and `/etc/ssh`, and a relative
name in them, resolved in ssh's working directory: git's, or the candidate
checkout for `soundness_remote.sh`'s own ssh), which is out of the check's
scope by ruling, not a gap it claims to close: ssh's configuration files
are judged as files, and a program they name is the user's own choice
inside LD-73's host trust boundary, not one of the programs git or a
configured command runs that the attested gate claims to judge
(OD-XHOST-GATE-CWD-20261025); an absolute program a judged
`--git-repo`'s git starts from outside the judged trees; the `core.worktree`
of a local remote and of an unpopulated submodule git directory (git uses no
work tree there during the run; a local remote git also uses a work tree of,
a populated submodule for instance, has it judged as that one's); an import
hook (a meta-path finder or path hook) that root-owned site code (a system
`.pth` line, the standard library's `sitecustomize`) installs, and where it
loads from; the working directory of a python3 a leg starts with `-c` or
`-` (the candidate checkout, or a directory the test names or creates under
umask 077); and a
repository-local `GIT_*` variable a
git newer than the supported versions adds, outside an attested run. The
pinned Clean and AY checkouts below
`SOUNDNESS_DEPS_DIR` are judged by `scripts/private_cache.py`
`require-private-tree`, before anything is built in them and again after the
Clean build; it refuses, besides any entry that is not this user's or has a
group or other write bit, a POSIX access ACL or a directory's default ACL that
lets anyone but this user or root write (a named user other than root, any group whoever its members
are, or every user), read with `scripts/host_boundary.py`'s ACL reader: a
default ACL would give what the build creates there its grant whatever the
umask. Because of the `/tmp` rule, the script suites' fixtures live below
`scripts/tests/soundness_fixture.py`'s `fixture_root()`: `SOUNDNESS_TEST_TMPDIR`
when set, else the system temporary directory when no group or other user
can write it or any directory above it (macOS's per-user `TMPDIR`), else
`XDG_RUNTIME_DIR` (Linux's `/run/user/<uid>`).
`scripts/tests/test_host_boundary.py` holds the rule and runs the gate in the
fixture with its group shared and private.

### Fail-fast and the leg inventory

`soundness_leg_inventory` in the script declares every recorded row once, with
its class (`per-run`, `host-independent`, `x86_64-native`, `dispatch`); the
runner records exactly those names, `--list-json` publishes them, and the last
row of an attested run (`inventory: executed legs match the declared
inventory`) fails unless the executed set is exactly the declared set for its
scope and host. `--attest` records every preflight row, stops if any failed,
then stops at the first failing leg (the dispatched x86-64 run is stopped
too and its staged record deleted); `--keep-going` runs everything for a
census.
`scripts/tests/test_soundness_leg_inventory.py` checks the call sites against
the inventory and runs the production script in a fixture to check the
executed set, the fail-fast stops (including a stop after the x86-64 record
arrived, which must publish nothing) and the allowlist refusals.

### Unambiguous record JSON

Both retained Git records and local `attestation.json` files must be UTF-8 JSON
objects with unique keys at every nesting level and finite numbers. Repeated
keys are malformed even when their values agree or one key uses a Unicode
escape. Invalid UTF-8, non-object roots, non-finite numeric extensions and nesting
deeper than 128 containers also return malformed status 2. Quoted delimiters do
not count toward nesting. The local writer checks this before any Git command
or ref promotion. Valid records keep their existing schema and evidence checks;
record decoding supplies no additional attestation or proof authority.

The reader and writer also check the container types they traverse and the
string identities of leg, environment and imported-record rows. Wrongly typed
objects or arrays are malformed before semantic checks; imported records must
name a host triple and a full commit ID, never a Git option or revision expression.
The writer applies this check before invoking Git, including when it could
otherwise keep an existing green record. Missing optional evidence still faces
its existing semantic checks.

### Fetching retained attestation records

`scripts/soundness_attestation.py fetch COMMIT --remote origin` routes canonical
GitHub HTTPS and SSH remote URLs through `aterm agh repo clone --mirror`.
This requires an agh build with mirror-clone support. A mirror includes custom
attestation refs and their record commits, which ordinary clones omit. The
import into the caller's repository uses the local-file transport only, moves
only the requested subject's attestation refs, and updates those refs atomically.
It does not force conflicting record refs, change branches or tags, or grant an
attestation verdict. Local repository paths and local `file:` URLs remain
supported. Ambiguous remote URL lists and other network URL forms are refused.
A reader or clone failure imports nothing; there is no native GitHub fallback.

The landing train and pre-push hook still have separate transport paths. This
fetch command alone does not migrate their main publication or authorize a
landing without the full gate and anchored verifier.

### Landing and the release boundary

**The rule, stated once here.** The landing train, `scripts/land_main.sh`,
has two explicit scopes. Ordinary development source uses `--source-only`
with one or more `--source-check 'PROGRAM ARG...'` commands covering the
changed-source build, focused behavior regressions and applicable
proof/certificate checks. It checks tracked-path collisions and candidate
cleanliness, merges current remote main, and publishes a leased fast-forward
update of main alone. It creates or publishes no attestation record and prints
`NOT ATTESTED`. A failing check or changed candidate refuses publication;
advancing main causes a fresh merge and focused checks. Unacknowledged writes
retain their receipts and stop for reconciliation. Full workspace, soundness,
Lean and benchmark campaigns are diagnostics or release qualification rather
than prerequisites for this ordinary source scope (owner directive 2026-11-02).
Existing records and all compiler/verifier refusals retain their authority.

`--resume-source-candidate <full-sha>` continues source-only qualification at
one explicit, existing, clean `--worktree` whose HEAD is exactly that commit.
Freshly authenticated main and every named lane must already be ancestors.
The train keeps its lease, tracked-path check, focused checks and ordinary
expected-ref source publication; it never checks out or recreates the resumed
candidate. If main advances outside that candidate, resume refuses and preserves
the worktree for ordinary merging and qualification. The check program remains
responsible for validating any retained same-commit results and completing its
missing checks; this route grants no attestation or proof grade.

The default **attested scope** retains a `scripts/soundness_check.sh --attest`
run on exactly commit `C`, then the LANDING verdict of the
verifier committed at its base (`soundness_attestation.py verify C --landing
--anchor <base>`, extracted from the base's tree), then one atomic push of
`main` and `refs/attest/soundness/<C>/*`. The pre-push hook,
`publish/DECISIONS.md` and the publication policy (trust-cg's registry entry
`main_writer = "landing-train"`, which writes this repository's pub-managed
block) cite this rule; none restates it. Ordinary source publication grants
neither the landing attestation verdict nor the release verdict below.

**Two verdicts.**

- *Landing* (`verify --landing`): the release verdict's records below, or a
  `portable` record (`soundness_check.sh --attest --scope portable`: every
  per-run and host-independent leg, no x86-64-native class, nothing
  dispatched) while the judging verifier's `DEFERRED_LANDING_CLASSES` names
  the classes it leaves out. Today that constant is `{"x86_64-native":
  "OD-LANDING-X86-DEFERRAL-20261008"}` (the development tree's
  `docs/decision-record.md`):
  a landing host that can neither execute x86-64 natively nor reach
  `SOUNDNESS_X86_HOST` may carry a portable record; the landing hosts are
  Apple-silicon, the only triple atpkg packages Trust for
  (OD-LANDING-HARDWARE-20261008 R3). A host meeting R1's executor clauses was
  measured on `x86_64-unknown-linux-gnu` on 2026-10-15, where all five
  x86-64-native legs pass and the train and the hook already choose a full
  run so this constant is never read; no x86-64-native record has been
  produced there yet. The verdict then prints
  `x86_64-native: NOT ATTESTED (<ruling>)` with its legs, the same for the two
  `dispatch` rows, and names the ten SSE lane-routing coverage credits whose
  silicon anchor (`x86_sse_lane_gate`) did not run as `NOT ANCHORED`. Run
  anchored, the deferral that applies is the anchor's, and it only shrinks:
  the anchored verifier refuses a candidate whose constant names a class the
  anchor's does not (read from the candidate's source without executing it)
  and a leg that moves into a deferred class. Deleting the entry in a landing
  is the withdrawal, once a native executor attests. A record made with a
  derived overlay toolchain is accepted for landing, with a note.
- *Release* (`verify` without `--landing`): see "What `verify` requires". It
  never reads the deferral, so a portable record never releases, and it
  refuses an overlay-made record.

**The interim exception.** This historical gate-bypass rule remains available
to legacy hook callers; ordinary `--source-only` publication above does not
claim or manufacture an exception or attestation verdict.
Ruling OD-LANDING-X86-DEFERRAL-20261008 replaced
the owner's 2026-09-27 exception (a main push may use `git push --no-verify`
while no commit can be attested on this machine, withdrawn only by the owner
after the first green attestation). Its x86-64 premise is now the constant
above. What remains: while no commit on `main`'s history carries an attestation
record ref, a `main` push may bypass the gate. Conservatively, record presence
ends the exception, even for a malformed record; it grants no landing or release
verdict. Do not revalidate historical records under today's verifier to decide
bypass permission: withdrawing a deferral or strengthening the record schema
must not revive it. The exception ends at the first such commit, and a later bypass does
not revive it: `soundness_attestation.py landing-exception --anchor <remote
main> --remote <remote>` decides it. Before a positive answer the CLI fetches
the selected remote's main and every record, then checks that the anchor is
that remote's actual main. Missing or failed discovery and a stale literal
anchor refuse bypass as UNDETERMINED. Retained records can end the exception
without network access; discovery never prunes them. The hook runs the
anchor's copy after fetching every record, passes Git's actual push location when
that copy supports discovery, and retains the old fetched-record path for
older anchors. A named remote resolves its push URL, not a possibly different
fetch URL; multiple push locations require selecting one explicitly. Records
are unsigned, so a forged record can end the exception
early, never extend it. This monotonicity is over retained fetched refs and
forward main history: client-side enforcement cannot prevent an administrator
deleting remote records or rewriting history.
Shallow history, unavailable subjects or ancestry-command errors refuse bypass
permission as UNDETERMINED; they are not evidence of a nonancestor or no record.
Measured 2026-10-08: the dev remote then carried no ref under `refs/attest/`,
`refs/land/` or `refs/soundness/`, and neither clone on
the host where the ruling was taken had the hook installed. The exception was
then in force. That historical measurement is not current authorization.
Only while the actual current query says it remains in force does a lane
land as before: merge `origin/main`, run the gates the change touches, and
fast-forward `main`. A fresh clone's missing custom refs is not such evidence.

**The train.** The gate takes over an hour, and main receives bursts of
landings, so gating every push individually cannot keep up.
`scripts/land_main.sh <lane>...` lands a batch per gate cycle: under a lease,
in a dedicated clean worktree, it merges the queued lanes onto the fetched
`origin/main`, checks tracked-path collisions and runs the actual hook's
trustfmt and tippy scripts before the proof campaign, then runs `--attest`
on the result (`--scope portable` when the
base's verifier defers the x86-64-native class and this host can neither run
it natively nor reach `SOUNDNESS_X86_HOST`), gives it the landing verdict of
the verifier committed at that base (a base without one stops the train), and
pushes `main` and the records in one `git push --atomic`; if main moved
meanwhile it re-merges and re-attests the new commit (no result is reused
across commits), within a bounded number of attempts. A missing base verifier,
failed pre-flight or failed campaign pushes nothing. The final push hook
still runs its checks; the early checks grant no cached authorization.
The lease covers one Git common directory. Independent clones share no lease
or queue, so atomic push ensures commit safety without guaranteeing progress
for a slower campaign. Local attestation alone establishes neither publication
nor a release verdict.

**The release boundary.** A development release candidate is a dev commit `C`
that the verifier committed at `A`, `C`'s landed predecessor on `main`, gives
the RELEASE verdict (`verify C --anchor A`, no `--landing`), on an `A` that the
same verifier accepts for landing. `publish/pre-promote` enforces it (ruling
OD-RELEASE-BOUNDARY-20261008): `pub promote` runs that file as committed in
the attested source commit, before anything public is written, and it refuses
the promote unless both verdicts are 0. It reads `A` from GitHub's activity log
of the dev repository (the `before` of the `refs/heads/main` push whose `after`
is `C`), because first-parent history does not record pushed tips: lanes land
by merging `main` into the lane. A `C` never pushed as main's tip, or forced
onto it, has no landed predecessor and is refused. Tips landed on a portable
record are therefore not release candidates. No commit meets the boundary yet:
the formal campaign needs a Trust sysroot whose AY is the `ay-pb` pin version,
and the release verdict needs the x86-64-native class from a native host.

The Clean and AY revisions are always derived from the commit's Cargo locks
and recorded per commit. `scripts/landing_checks.sh` step 4 gives the landing
base the landing verdict of the verifier committed at that base (records
fetched with plain `git`; the candidate's tool does not run).

### Coherence with the Cargo pins

`python3 scripts/check_companion_coherence.py` compares, for TrustIR, Clean and
AY, the revision the root `Cargo.lock` pins with the tree-wide tuple (every
manifest, lockfile and compile-artifact cache identity). It reports every
disagreement with its file and line and exits 1 while any remains; `--json`
prints the whole comparison. The full `--attest` preflight runs it. Agreement is
bookkeeping: it does not show that a revision was audited, tested, published or
fetched, and it names no installed executable.

## Optional pre-push hook

The repository includes `hooks/pre-push`. Install it per clone with:

```sh
scripts/install-hooks.sh
```

Once installed, a push that updates `main` must carry an attestation the
anchor's verifier accepts for landing.
The hook requires the pushed SHA to be the clean checked-out HEAD and the
remote main it replaces (the anchor) to be a known proper ancestor that carries
a committed verifier; otherwise it blocks (see "Anchored verification"). It
fetches `refs/attest/soundness/<C>/*` and the anchor's records with plain `git
fetch`, decides the fast path with the anchor's verifier (extracted from the
anchor's tree, run with `python3 -I`, `verify --landing`), then runs the format
(`targo fmt`) and lint (`targo tippy`) pre-flights. A `C` attested for landing
takes the fast path; otherwise the hook runs `scripts/soundness_check.sh
--attest` (`--scope portable` under the same condition as the train), pushes
the new records with plain `git push` (a nested push that is not to main) and
verifies again with the anchor's verifier. Where the gate blocks a push, the
hook names the interim exception only while the anchor's verifier reports it
in force (see "Landing and the release boundary"), and never for a block that
precedes the anchor (a first push of main, an unknown or non-fast-forward
remote, a dirty tree). It also checks the anchor's own records and prints
a loud notice when that commit carries no complete attestation, so an earlier
bypass is detected by the next main push. Feature-branch pushes are not gated.

This is detection, not prevention: `--no-verify` cannot be disabled on a client,
GitHub runs no pre-receive hook, and an unconfigured clone has no automatic
enforcement, so release reviewers verify the records independently.

The gate and the attestation tool clear git's repository-local environment
names before querying repositories or launching workloads. Otherwise a hook's
inherited `GIT_DIR` can make even `git -C` read the pushing repository instead
of the selected Clean or AY checkout or the record's repository. The gate
(`scripts/soundness_check.sh`, which runs after the host trust boundary) asks
git for the names (`git rev-parse --local-env-vars`); the attestation tool's
`exec-scrubbed` re-exec runs before the boundary has judged PATH, so it clears
a FIXED superset of those names instead (`GIT_LOCAL_ENVIRONMENT`, checked
against the installed git by a test), running no program before the boundary
(R3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024). After the boundary, every git
program the run starts reads no system configuration and only the gate's own
global file (above), not the user's global file; Cargo's built-in libgit2
ignores both variables and reads the user's files itself, which the boundary
judged. Failed HEAD or status queries are
failures, never evidence of a clean tree.
`scripts/test_soundness_git_environment.sh` exercises these boundaries, and the
record checks (subject tree, host triple), inside real temporary pre-push hooks;
its fixture results do not replace a complete attested soundness run.
