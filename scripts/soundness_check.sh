#!/usr/bin/env bash
#
# soundness_check.sh — the #4 LOCAL soundness meta-gate ("meta-CI", local half).
#
# WHAT THIS IS
# ------------
# One runnable in-repo entrypoint that, at pinned cross-repository revisions,
# runs the configured soundness-evidence checks and fails closed (nonzero exit)
# if a listed gate is missing, vacuous, or erroring. Cargo gates capture successful
# test output and reject ignored cases, runtime SKIPs, filtered cases, and
# incomplete named results. A developer runs this locally before landing a change.
#
# This is not hosted CI. It is a shell script a developer runs locally; see
# SOUNDNESS_CHECK.md for the trust boundary and optional hook behavior.
#
# WHAT IT AGGREGATES
# ------------------
# Every Cargo leg runs on the Trust toolchain (owner directive 2026-09-28)
# through scripts/trust_cargo.sh: `targo --unverified <verb>`, with the
# TRUST_CG_*/TCG_* controls handed to the tests but never to trustc.
#
#   trust-cg (targo --unverified test -p trust-cg-verify --test <target>):
#     - coverage_gate_tests     (accepted/deferred inventory per backend, pinned
#                                with its named RED rows by the per-arch
#                                *_is_honest_under_strict / *_inventory_pins_*
#                                tests; see SOUNDNESS_CHECK.md for what this
#                                gate does NOT claim).
#                                Exact classifications are pinned; unknown drift
#                                fails. Ratios are evidence coverage, not
#                                correctness-proof percentages; Statistical
#                                Valid is regression evidence, not formal proof)
#     - meta_theorems           (properties-not-values headline invariants)
#     - mutation_catalog        (mutation testing harness)
#     - proof_gate_strict       (universal non-degeneracy gate + fail-closed)
#     - fsym_real_function_corpus (real-function symbolic preflight corpus)
#     - aarch64_affine_lowering (independent raw LIR/MachIR correspondence;
#                                not final-code or whole-pipeline authority)
#     - aarch64_trust_ir_affine_lowering (independent module-owned source
#                                binding, typed SSA/signature and mutations)
#     - wasm_encoding_gate      (the P4 ENCODING families: module indexing over
#                                REAL emitted bytes, an INDEPENDENT spec-derived
#                                signed-LEB decoder, and TargetInfo conformance.
#                                Pinned at 208 proven / 0 refuted / 110
#                                not-applicable plus 6 named RED deferrals; a row
#                                whose construct is ABSENT from a module reports
#                                not-applicable, never credit. Establishes that
#                                the emitted ENCODING says what the compiler
#                                meant; says NOTHING about whether the lowering
#                                chose the right value, and a forgotten import
#                                shift is caught by the TWO-COMPILE differential,
#                                not by any single-module row)
#     - x86_sse_lane_gate       (the x86-64 SSE LANE-ROUTING family behind the
#                                ten Pshufd/Pmovmskb/MovdqaRR/PUNPCK*/Ptest/
#                                Pblendvb/Packuswb coverage credits: it
#                                re-derives the captured corpus from the LIVE
#                                encoder, sweeps every register pair and every
#                                one of the 256 PSHUFD immediates, and runs the
#                                SDM denotation against NATIVE SILICON on an
#                                x86-64 host with SSE4.1 — the only part of that
#                                family that is not internally consistent by
#                                construction, and so the only thing that can
#                                catch a shared MISREADING of the manual)
#     - aarch64_value_decode_gate (the AArch64 decoded-word value family
#                                behind the MovR, scalar FMOV, Smull, Bfm,
#                                Rbit, AddRIShift12 and Mrs coverage credits:
#                                it re-derives the captured corpus from the
#                                LIVE encoder, sweeps every register pair and
#                                every BFM field / imm12 through the
#                                per-instance check, pins which single-bit
#                                corruptions are semantically neutral, and
#                                shows ENC-5 running the obligation per
#                                emitted word. Says NOTHING about whether the
#                                lowering chose the right registers, and is
#                                not a silicon differential)
#     - x86_encoding_gate       (the x86-64 MOV r,imm ENCODING family: an
#                                INDEPENDENT SDM-derived decoder over the REAL
#                                emitted bytes. It re-derives the captured corpus
#                                behind the MovRI coverage credit from the LIVE
#                                encoder, so the credit cannot rest on a stale
#                                capture. It also runs a stratified live sweep,
#                                shows the credit hook REFUSING surviving or
#                                misattributed controls, and shows ENC-3 running
#                                the obligation per compile. Release mode. Says
#                                NOTHING about whether the lowering chose the
#                                right constant)
#     - wasm_cfg_structural_gate (the P4 CFG family: the per-compile structural
#                                invariant on the relooper's output — label
#                                liveness, operand discipline, join heights and
#                                types, bracket structure. It really is
#                                per-compile: the evidence-carrying compile
#                                routes run it on the bytes they emit, refusing
#                                a refuted module and crediting nothing for an
#                                inconclusive one. A NECESSARY CONDITION,
#                                NOT a bisimulation: relooper bisimulation is a
#                                named RED deferral and two blind-spot mutants
#                                are shipped as its executable measurement)
#     - wasm_abi_proofs_gate    (the P4 MEMORY and CALL-ABI families:
#                                shadow-stack frame refinement and the
#                                call/table ABI, over REAL emitted module
#                                bytes with byte-mutation guards. Five HOST
#                                obligations stay deferred BY NAME to
#                                crates/trust-cg-codegen/src/wasm/OWNERSHIP.md;
#                                none of this makes the wasm lane "verified")
#     - wasm_internal_abi_gate  (the P6 internal multi-value ABI: the boundary
#                                gate, return, source and link bindings over
#                                REAL lane objects, with byte-mutation and
#                                hand-built negative controls. Structural
#                                checks only: not a proof that an internal
#                                entry computes its trust-ir function)
#     - wasm_value_domain_gate  (the P3 VALUE-DOMAIN sub-inventory: sub-word
#                                and FP linear-memory accesses and the
#                                sign-extension operators, with the accepted,
#                                credited and named-deferral sets pinned)
#     - the 9 differential bridges:
#         bdefs_differential_bridge            (B-aarch64-int)
#         bdefs_differential_bridge_x86        (B-x86-rosetta)
#         bdefs_differential_bridge_riscv      (B-riscv-qemu)
#         bdefs_differential_bridge_x86_packed (B-x86-sse-packed)
#         bdefs_differential_bridge_x86_fp     (B-x86-sse-fp)
#         bdefs_differential_bridge_neon       (B-aarch64-neon)
#         bdefs_differential_bridge_riscv_fp   (B-riscv-fp)
#         bdefs_differential_bridge_neon_fp    (B-aarch64-neon-fp)
#         fp_bitmodel_bridge                   (B-aarch64-fp / FP bit-model)
#
#   trust-cg library-test filters (same non-vacuity and timeout guards):
#     - trust-cg-verify: tv2_ (both architecture source-precondition controls),
#         coverage_gate:: (the in-crate inventory pins the coverage_gate_tests
#         integration target cannot reach, e.g. the pair-debt denominator),
#         checked_mul_i128_proofs::tests::credit_ (the i128 checked-multiply
#         credit refuses a surviving control, a degenerate or missing
#         obligation and a battery-visible wrong flag; no AY call),
#         x86_source_bound_body::tests::slice5:: (the x86-64 body theorem's
#         slice-5 fixtures, golden digest and negative controls: pairs,
#         symbol addresses, compares; no AY call, the AY/Clean replay lives
#         in the separate slice5_qualification module),
#         x86_source_bound_body::tests::slice6:: (slice 6: acyclic control
#         flow, the fixtures, golden digest and negative controls: inverted,
#         swapped or wrong-code branches, flag clobbers, missing or misplaced
#         traps, wrong join values, extra machine paths, loops; no AY call,
#         the replay lives in the separate slice6_qualification module),
#         x86_source_bound_body::tests::slice7:: (slice 7: calls through
#         memory, the return-buffer and out-parameter fixtures, golden
#         digest and negative controls: a wrong slot or offset passed, a
#         read moved before the call, the old contents kept across it or
#         across a later call, another slot or field read, other contents
#         at the call, accesses through escape-derived addresses; no AY
#         call, the replay lives in the separate slice7_qualification
#         module),
#         x86_source_bound_body::tests::slice9:: (slice 9: acyclic control
#         flow over the DAG past the slice-6 bounds, the fixtures, golden
#         digest, the sampled equivalence of the DAG and per-path theorems
#         and negative controls: inverted or swapped branches, retargeted,
#         extra or missing edges, wrong join values, merged slot bytes,
#         flags across blocks, escapes and redefinitions at joins, loops and
#         the size bounds; no AY call, the replay lives in the separate
#         slice9_qualification module),
#         x86_source_bound_body::tests::slice10:: (slice 10: instruction
#         coverage, the checked-arithmetic, not, popcount and indirect-call
#         fixtures, golden digest and negative controls: a wrong or inverted
#         overflow flag, swapped or wrong operands, a flag imul or mul leaves
#         undefined, a narrow count unmasked, a call through another value
#         or of another kind; no AY call, the replay lives in the separate
#         slice10_qualification module),
#         x86_source_bound_body::tests::slice11:: (slice 11: i128 register
#         pairs and float bit patterns, the fixtures, golden digest and
#         negative controls: a dropped or misused carry, swapped or crossed
#         halves, a wrong access offset, a zero-extended sign, float
#         arguments in the wrong XMM register, a movss where 64 bits are
#         needed, an SSE register read after a call; no AY call, the replay
#         lives in the separate slice11_qualification module),
#         x86_source_bound_body::tests::slice12:: (slice 12: loops cut at
#         their headers, the fixtures, golden digest and negative controls:
#         loop-carried registers swapped or stale, a missing or extra
#         iteration, a wrong exit, increment or bound, a register the loop
#         writes or a private byte only the machine changes read as its
#         entry value, a tainted carried value, an entry-block header and an
#         irreducible cycle; no AY call, the replay lives in the separate
#         slice12_qualification module),
#         x86_source_bound_body::tests::slice13:: (slice 13: private
#         addresses stored as data, the stack argument areas, the C memory
#         routines and scalar atomics, the fixtures, golden digest and
#         negative controls: another stored offset, a value kept across a
#         call the slot escaped to, swapped stack eightbytes, an unwritten
#         or wrong stack argument, RSP not restored, swapped memcpy
#         operands, an atomic paired with a plain row; no AY call, the replay
#         lives in the separate slice13_qualification module),
#         x86_source_bound_body::tests::slice14:: (slice 14: integer
#         division as trust-ir's, its undefined inputs a premise of the
#         path that divides, the divide-by-zero guard an observable trap,
#         switch cases sharing a target, jump tables read from the
#         selector's table, the fixtures, golden digest and negative
#         controls: a missing cqo or rdx zeroing, cdq for cqo, quotient and
#         remainder swapped, div and idiv swapped, a dropped or moved
#         guard, a trap the source does not take, a hoisted division,
#         shared cases compared or sent wrong, swapped case arguments, a
#         swapped, short or unbiased jump table, a 32-bit selector copied
#         with a 64-bit mov; no AY call, the replay lives in the separate
#         slice14_qualification module),
#         x86_source_bound_body::tests::slice15:: (slice 15: float
#         constants and sign-bit operations, mixed-width registers, a
#         forwarded bool parameter, accesses through a derived address and
#         I128 in the stack areas, the fixtures, golden digest and negative
#         controls: another constant or NaN payload, a sign mask of another
#         bit, xor and and swapped, a dropped abs, an aggregate byte dropped
#         by a mixed copy, the high half of a mixed-width copy or add
#         observed, the bool register forwarded raw, a slot written
#         behind a derived load, a value kept across a derived store,
#         another derived offset, swapped stack eightbytes or halves; no AY
#         call, the replay lives in the separate slice15_qualification
#         module),
#         x86_source_bound_body::tests::qualification_matrix:: (all thirteen
#         canonical snapshot families bind the diagnostic export, and each
#         family retains actual wrong-lowering controls; no AY call),
#         source_bound_negative_memo:: (the negative memo withholds credit
#         only: stable outcome classes, key and build identity, the replay
#         protocol tied to the real commands, strict per-box format, FIFOs,
#         retry policy, locking, pruning, concurrent writers; no AY call),
#         x86_source_bound_body::tests::negative_memo:: (the memo on the real
#         body replay path with a fixture AY that counts its replays and a
#         fixture Clean: a second identical request runs no AY, every key
#         input misses, host-state answers and post-SAT timeouts re-solve,
#         a long-lived process retries, the bypass re-solves, a stored proof
#         wins in a fresh process, Verified is untouched)
#     - trust-cg-codegen: affine_lowering_tests, verification_precondition,
#         jit_cert::tests::, test_generate_proof_certificates_rejects,
#         x86_authoritative_ (raw-Core scope, certificate and cache authority)
#
#   trust-cg wasm offline oracles (targo run --example + node differential):
#     - wasm-difftest           (control-flow-diverse corpus: the trust-ir
#                                interpreter's expectations replayed against the
#                                compiled wasm under node, bit-for-bit; any
#                                divergence is a miscompile = FAIL)
#     - wasm-cfg-fuzz           (bounded DETERMINISTIC reducible-CFG fuzz:
#                                WASM_CFG_FUZZ_FUNCS random structured CFGs at a
#                                fixed seed, same node oracle)
#     The emit leg (compile_module + interpreter) always runs and fails closed;
#     if node is not on PATH the node leg is a LOUD SKIP (recorded and counted
#     in the summary — never a silent pass).
#
#   Clean checkout:
#     - clean check <file>      for each B-def / LRAT-checker .lean proof
#         aarch64_isa, aarch64_isa_chip, aarch64_fp, aarch64_fp_arith,
#         aarch64_fp_cvt, aarch64_fp_divsqrt, aarch64_fp16, reducible_word,
#         lrat_checker, lrat_checker_word, lrat_checker_tree
#     - targo --unverified test -p clean-kernel --test micro_diversity_gate
#                               (the kernel diversity gate)
#
#   trust-cg checkout (repository proofs, checked with the SAME Clean release
#   binary built above):
#     - clean check proofs/<stem>.lean   for each of trust-cg's OWN Clean specs
#         abi_clobber_spec           (AAPCS64 caller/callee-saved partition)
#         sentinel_decide_spec       (trust_cg_ir::guard::decide contract)
#         mir_place_resolution_spec  (bridge place-resolution dispatch)
#       These specs prove properties of hand-written Lean MODELS; the Rust weld
#       tests compare the real code against hand re-encodings of them. A check
#       here establishes that the model theorems hold, not that the Rust code
#       matches the model. A rejected or incoherent check is a FAIL; a missing
#       proof file, or a proofs/*.lean file this list does not name, is a FAIL;
#       an absent checker is a loud SKIP (recorded, counted, nonzero overall)
#       — never a silent pass.
#
#   x86-64 vector-compare certificates (scripts/check_x86_icmp_certificates.py):
#     - x86 icmp certificates   trust-ir's per-cell rule admits an available
#                               chc_x86 icmp cell on the instruction model
#                               (eq/sgt: a degenerate query) or on a
#                               CERTIFICATE under
#                               trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE, which
#                               the leg reads from the compiled trust-ir (the
#                               query dump writes it; no prose is parsed).
#                               This leg re-runs every certificate: the
#                               rule's AY (which must be the Cargo.lock pin)
#                               and the rule's Clean, each built by revision
#                               from a git archive of the pinned worktrees'
#                               object store into a per-rev cache under the
#                               rule's Clean's own heavy_gate (run 12),
#                               answer each certified query unsat under
#                               --strict-proofs with unproved_steps=0 and no
#                               hole or lia_generic step, and `clean cert
#                               verify-external` (the Carcara Alethe checker,
#                               not Clean's kernel) exits 0 with "Proof
#                               status: fully verified". The queries are
#                               regenerated from the code, must hash to
#                               CERTIFIED_QUERY_SHA256 and state trust-ir's
#                               spec side verbatim; every reader cell must
#                               rest on the ground trust-ir answers for it.
#                               A missing toolchain input FAILS the leg;
#                               SOUNDNESS_SKIP_X86_ICMP_CERTIFICATES=1 turns
#                               ONLY a missing input (no targo, no AY or Clean
#                               source with the rule's revision) into a loud
#                               SKIP (the run is then incomplete and nonzero;
#                               an --attest run refuses the variable in its
#                               preflight). A wrong input (a changed cached
#                               binary, another AY pin) always fails.
#
# EXIT CODE: 0 iff EVERY gate above passes. Nonzero if ANY gate fails, errors,
# or cannot be run (a missing/erroring gate is a FAIL, never a silent skip).
# Missing external runtimes or oracle inputs remain loud SKIP diagnostics
# (recorded, counted and flagged), but make the run incomplete and nonzero.
# A SKIP can never produce an all-green summary or an attestation record.
#
# The gate has no tolerated failing/missing gate target. The opcode inventory has
# pinned, explicitly named RED model gaps; an unknown/unclassified RED fails the
# inventory test. The separately run external-SMT full-database floor reports
# solver-capacity pending results without calling them proofs; see
# scripts/check_proof_gate.sh.
#
# HOST CLASSES. Every leg is declared once, with its class, by
# soundness_leg_inventory below (published by --list-json): per-run rows run in
# every record, host-independent legs in a full run, x86_64-native legs
# (x86_sse_lane_gate and the three e2e_x86_64_* targets) only on a native,
# untranslated, unemulated x86-64 host. A full run on any other host dispatches
# them to SOUNDNESS_X86_HOST through scripts/soundness_remote.sh and imports
# that host's record; an unset or unreachable host is a FAIL, never a SKIP.
# A PORTABLE run (--scope portable) records exactly the per-run and
# host-independent legs and neither runs nor dispatches the x86_64-native
# class: its record is a LANDING record, accepted by `soundness_attestation.py
# verify --landing` only while the verifier that judges it (the anchor's)
# defers that class (DEFERRED_LANDING_CLASSES, ruling
# OD-LANDING-X86-DEFERRAL-20261008), and never a release record.
#
# ATTESTATION. --attest first judges the host trust boundary
# (scripts/host_boundary.py, ruling LD-73: no place its WHAT IS JUDGED list
# names, the tools the run executes and the configuration it reads among
# them, may be writable by another user; its NOT JUDGED list says what it
# does not judge) and stops
# at once, running nothing else, if it refuses. It then sets umask 077 for
# the rest of the run (ruling LD-75), runs the preflight and stops at its
# first failure, then stops at the first failing leg (--keep-going runs everything,
# for census). A green run writes the per-commit record
# refs/attest/soundness/<HEAD>/<host-triple> locally through
# scripts/soundness_attestation.py, together with the x86-64 record it
# imports, in one atomic ref transaction; nothing is pushed. Under --attest the
# run re-executes itself with only the ALLOWLISTED environment (see "The
# environment allowlist" below and in SOUNDNESS_CHECK.md): leg-affecting caller
# variables (PYTHON*, NODE_*, DYLD_*, LD_*, LEAN_*/ELAN_*, CARGO_*, RUST*, the C
# toolchain variables, unknown TRUST_CG_*/TCG_* controls, a low
# WASM_CFG_FUZZ_FUNCS, caller-supplied vt tables, an explicit
# CLEAN_DIR/AY_DIR/TRUST_TARGO, ...) and uncommitted Cargo config files are
# refused, other unlisted variables are dropped, and every variable the legs can
# see is recorded. An --attest run starts nothing in its caller's working
# directory, which no check judges: it works in / until the host trust boundary
# has passed and in the judged candidate checkout from then on, it finds its
# own directory without CDPATH, and every python3 it or a helper starts
# (inline -c and -, and script runs) runs isolated with -I
# (OD-XHOST-GATE-CWD-20261025). It runs only as bash reads it from the
# candidate's scripts/soundness_check.sh file (not from standard input, a -c
# string or a caller's shell), and every python3 it and its helpers start is
# ONE interpreter, pinned by its canonical path before anything changes PATH
# (SOUNDNESS_PYTHON3), which the boundary judges as exactly that file (repair
# round 3 of that ruling).
#
# USAGE
#   scripts/soundness_check.sh                 # run all gates (census; dirty tree allowed)
#   scripts/soundness_check.sh --attest        # clean committed HEAD, fail fast, write a record
#   scripts/soundness_check.sh --attest --keep-going
#                                              # attest mode without fail-fast (census)
#   scripts/soundness_check.sh --attest --preflight-only
#                                              # run the attest preflight and stop (no record)
#   scripts/soundness_check.sh --attest --host-legs x86_64-native
#                                              # the x86-64-native legs only (the remote side)
#   scripts/soundness_check.sh --attest --scope portable
#                                              # every per-run and host-independent leg, no
#                                              # x86-64-native class (a landing record only)
#   scripts/soundness_check.sh --self-test-cargo-gates # Cargo inventory only;
#                                                   # NOT an attestation
#   scripts/soundness_check.sh --list          # list the gates and exit
#   scripts/soundness_check.sh --list-json     # the declared leg inventory, as JSON
#   scripts/soundness_check.sh --validate-clean-summary <log>
#                                              # validate one Clean log and exit
#   scripts/soundness_check.sh --self-test-clean-cargo-command
#                                              # exercise the Clean Trust-Cargo lane only
#   scripts/soundness_check.sh --validate-dependency-locks
#                                              # validate all independent Cargo locks only
#   scripts/soundness_check.sh --run-wasm-oracles
#                                              # run ONLY the wasm offline-oracle
#                                              # gates (difftest + CFG fuzz)
#   scripts/soundness_check.sh -h | --help
#
# --pinned and --update (the retired soundness_revs.lock modes) exit 2 and name
# --attest.
#
# Each Cargo, Clean, and Lake workload is limited to 7200 seconds by default.
# Override that positive duration with SOUNDNESS_COMMAND_TIMEOUT_SECONDS.
#
set -u
set -o pipefail

# ----------------------------------------------------------------------------
# The environment allowlist. An --attest run re-executes itself, before
# anything else, with ONLY the allowlisted variables of its caller
# (scripts/soundness_attestation.py exec-scrubbed; ENV_RECORDED and ENV_INERT
# there). A caller variable whose name is known to change a leg (PYTHON*,
# NODE_*, DYLD_*, LD_*, LEAN_*/ELAN_*, CARGO_*, RUST*, CC/CFLAGS/CPATH, ...)
# is refused by the preflight row "preflight: leg-weakening settings"; any
# other unlisted variable is dropped and only its name is recorded. The legs,
# and every tool this script starts, then see nothing else.
#
# Until the host trust boundary below has passed, an --attest run executes no
# program but this bash, the bash it re-executes, and ONE python3, pinned
# below by its canonical absolute path (SOUNDNESS_PYTHON3): the environment
# scrub, the cache-base rule and the boundary itself run that file, as does
# every later python3 the gate and its helpers start (and, once scrubbed, the
# git the boundary asks). The python3 PATH finds runs before it, only to print
# that canonical path: once in each bash of an --attest run (this one, before
# the scrub, and the re-executed one, which refuses unless it prints the path
# the scrub exported). This file's own directory and name are taken
# apart with parameter expansion, not dirname/basename (a PATH command
# another user could write would run as this user before any check; LD-73).
# These programs start before anything could judge them, with the caller's
# environment as this bash read it before line 1 (BASH_ENV, SHELLOPTS,
# exported functions; the scrub refuses each of those for the re-executed
# run): the boundary judges each of them once it runs, the pinned python3 as
# exactly the file running it (repair round 3 of OD-XHOST-GATE-CWD-20261025).
# ----------------------------------------------------------------------------
SOUNDNESS_ATTEST_RUN=0
for soundness_arg in "$@"; do
  [ "$soundness_arg" != --attest ] || SOUNDNESS_ATTEST_RUN=1
done
unset soundness_arg
soundness_refuse_start() {
  # soundness_refuse_start <detail>: stop an --attest run that has started no
  # program it has not judged, with its FAIL row and no record (builtins).
  printf '  [FAIL] %-46s %s\n' "preflight: host trust boundary" "$1"
  printf '%s\n' "  no attestation record: the run failed or was incomplete. Resolve every FAIL and SKIP first."
  exit 1
}
# An --attest run is read by bash from the candidate's
# scripts/soundness_check.sh FILE, run as a script (`bash <path> --attest`,
# or `<path> --attest` by its #! line), and in no other way (repair round 3
# of OD-XHOST-GATE-CWD-20261025). Read from standard input (`bash -s --
# --attest < .../scripts/soundness_check.sh`) or from a -c string, bash
# names no file: BASH_SOURCE is empty and $0 is the shell's name or any word
# the caller chose, so the directory checks below judged that word, and a
# soundness_attestation.py in the caller's working directory ran before the
# boundary and the run attested. Sourced, the script runs in its caller's
# shell, with that shell's functions, aliases and options. Each is refused
# here, with builtins and before any program; the remedy is to run the file.
if [ "$SOUNDNESS_ATTEST_RUN" -eq 1 ]; then
  case "$-" in
    *c* | *s*)
      soundness_refuse_start "an --attest run must be read by bash from the candidate's scripts/soundness_check.sh file, but this bash reads its commands from a -c string or from standard input (its options are '$-'); remedy: run the script file, as \`bash /path/to/trust-cg/scripts/soundness_check.sh --attest\` (OD-XHOST-GATE-CWD-20261025)" ;;
  esac
  if [ -z "${BASH_SOURCE[0]:-}" ] || [ "${#BASH_SOURCE[@]}" -ne 1 ] || [ "${BASH_SOURCE[0]}" != "$0" ]; then
    soundness_refuse_start "an --attest run must be read by bash from the candidate's scripts/soundness_check.sh file it runs as a script, but bash names no such file here (BASH_SOURCE '${BASH_SOURCE[*]:-}', \$0 '$0': read from standard input or a -c string, or sourced); remedy: run the script file, as \`bash /path/to/trust-cg/scripts/soundness_check.sh --attest\` (OD-XHOST-GATE-CWD-20261025)"
  fi
fi
soundness_self="${BASH_SOURCE[0]:-$0}"
case "$soundness_self" in
  */*) soundness_self_dir="${soundness_self%/*}" ;;
  *) soundness_self_dir=. ;;
esac
# `CDPATH= cd --`: a plain `cd` looks a relative directory up in an exported
# CDPATH first (and prints what it found), so `scripts/soundness_check.sh
# --attest`, as SOUNDNESS_CHECK.md starts it, made this directory one inside
# a CDPATH directory nothing judges and exec'd ITS soundness_attestation.py
# before the boundary (X-HOST-P13 sixth audit, repair round 2,
# OD-XHOST-GATE-CWD-20261025). The variable itself stays in the environment:
# the scrub refuses a CDPATH the caller set, so the run still fails closed at
# "preflight: leg-weakening settings".
soundness_self_dir="$(CDPATH= cd -- "${soundness_self_dir:-/}" && pwd)"
soundness_self_name="${soundness_self##*/}"
# An --attest run uses this directory only when it holds the very file this
# bash is running (`-ef`: same device and inode; the relative name still
# resolves in the caller's directory here) and is absolute: a directory found
# any other way (a lookup this script did not mean, a logical `..` that
# leaves the physical path) would name other scripts to run before any check.
# Its parent is the candidate checkout the scrub is told it judges, and that
# file must be the candidate's scripts/soundness_check.sh; the run then names
# every script it starts before the host trust boundary by the candidate's
# scripts/ (repair rounds 3 and 4: the cache-base rule and the boundary had
# been named by TRUST_CG_DIR, which a caller may spell otherwise), and every
# later one by TRUST_CG_DIR, which the boundary judges as the candidate.
# PATH: a relative or empty entry finds a command relative to the working
# directory, which no check judges, and the pinned python3 is found by PATH
# before the boundary could refuse that entry, so it is refused here first,
# exactly as the boundary refuses it (OD-XHOST-GATE-CWD-20261025, repair
# round 2). Builtins only.
if [ "$SOUNDNESS_ATTEST_RUN" -eq 1 ]; then
  case "$soundness_self_dir" in
    /*) ;;
    *) soundness_self_dir="" ;;
  esac
  if [ -z "$soundness_self_dir" ] || ! [ "$soundness_self" -ef "${soundness_self_dir}/${soundness_self_name}" ]; then
    soundness_refuse_start "an --attest run cannot name the directory of the script it runs (${soundness_self}) by an absolute path that holds that same file; remedy: start it by its absolute path (OD-XHOST-GATE-CWD-20261025)"
  fi
  soundness_candidate_dir="$(CDPATH= cd -- "${soundness_self_dir}/.." && pwd)"
  case "$soundness_candidate_dir" in
    /*) ;;
    *) soundness_candidate_dir="" ;;
  esac
  if [ -z "$soundness_candidate_dir" ] ||
     ! [ "$soundness_self" -ef "${soundness_candidate_dir%/}/scripts/soundness_check.sh" ]; then
    soundness_refuse_start "the file this --attest run reads (${soundness_self}) is not the candidate checkout's scripts/soundness_check.sh (${soundness_candidate_dir:-?}/scripts/soundness_check.sh); remedy: run the candidate's scripts/soundness_check.sh file by its path (OD-XHOST-GATE-CWD-20261025)"
  fi
  soundness_self_dir="${soundness_candidate_dir%/}/scripts"
  soundness_self_name=soundness_check.sh
  soundness_path_rest="${PATH-}:"
  while [ -n "$soundness_path_rest" ]; do
    soundness_path_entry="${soundness_path_rest%%:*}"
    soundness_path_rest="${soundness_path_rest#*:}"
    case "$soundness_path_entry" in
      /*) ;;
      *)
        soundness_refuse_start "PATH entry '${soundness_path_entry}' is relative or empty, so it names a directory relative to the working directory, which this check cannot judge, and the gate's pinned interpreter is found by PATH before the host trust boundary runs; remedy: remove it or make it absolute (LD-75, OD-XHOST-GATE-CWD-20261025)"
        ;;
    esac
  done
  unset soundness_path_rest soundness_path_entry
fi
# An --attest run leaves its caller's working directory before it starts any
# program (OD-XHOST-GATE-CWD-20261025). No check judges that directory, and
# what runs there resolves names in it: a `python3 -c` or `python3 -` puts it
# first on sys.path (a json.py there ran as this user and the run attested,
# sixth closure audit), elan's lake proxy reads a lean-toolchain there, a
# rustup proxy a rust-toolchain.toml, Cargo a .cargo/config.toml, and a
# relative or empty PATH entry finds a command there. Until the host trust
# boundary has passed the run works in /, which every judged path is resolved
# through and which holds no repository the gate uses; once it has passed, in
# the judged candidate checkout (below). The directory and name of this file
# are absolute above (found without CDPATH and checked to hold this file), an
# --attest run takes no path argument, every PATH entry is absolute, and every
# path setting the gate or a leg resolves is refused by the boundary when it
# is not absolute (LD-75), so no relative path the caller passed changes
# meaning here. Builtins only: nothing has been judged yet.
if [ "$SOUNDNESS_ATTEST_RUN" -eq 1 ] && ! cd /; then
  printf '%s\n' "soundness_check.sh: an --attest run cannot leave its caller's working directory for /" >&2
  exit 1
fi
# ----------------------------------------------------------------------------
# The python3 the gate runs, ONE file pinned before the prelude (repair round
# 3 of OD-XHOST-GATE-CWD-20261025). The gate_env.sh prelude below puts
# $HOME/.elan/bin first on PATH, and the boundary's own python3 was found by
# name after it: not the interpreter the checks above and the scrub saw, and
# possibly one in a directory nothing had judged yet, which ran first. So
# python3 is resolved here, where every PATH entry is absolute (an --attest
# run checked that above) and before the prelude changes PATH, to ONE
# canonical absolute path, SOUNDNESS_PYTHON3: `type -P` (a builtin PATH
# search) finds the program, which then prints the realpath of its own
# sys.executable, run with -I -S (no site directory, no .pth file: nothing
# but the interpreter and its standard library, which the boundary judges as
# part of its import path). The gate starts every python3 by that path from
# here on, whatever PATH names first later: the scrub, the cache-base rule,
# the boundary (which judges exactly that file and refuses it unless it is
# the interpreter running the boundary) and every later tool; it exports it
# to the helpers that start python3 (gate_env.sh's check, trust_cargo.sh,
# soundness_remote.sh's local half), which use it when it is set.
#
# The legs do not: a Cargo test, a Clean test or a `#!/usr/bin/env python3`
# script a leg runs starts python3 by name on the prelude's PATH. The
# boundary judges the pinned interpreter's import path and user site, so it
# refuses an --attest run unless the first python3 on that PATH is the pinned
# file, reached by a name around which python3 reads no other pyvenv.cfg
# (repair round 4: round 3 judged the pinned interpreter alone, so a python3
# in $HOME/.elan/bin, or a virtual environment's, was the legs' unjudged).
#
# An --attest run resolves it before the scrub and runs the scrub as that
# file; the scrub exports the canonical path of the interpreter it runs as,
# and the re-executed run, resolving it again from the same PATH before the
# prelude, refuses unless the two agree, so the scrub, the boundary and every
# leg tool run one file. SOUNDNESS_PYTHON3 is the gate's own, never an input:
# a caller's value refuses an --attest run here and is replaced in a census
# run (whose leg-weakening note names it).
# ----------------------------------------------------------------------------
soundness_resolve_python3() {
  # Print the canonical absolute path of the python3 PATH finds now, or fail.
  local SOUNDNESS_FOUND_PYTHON3 soundness_resolved
  SOUNDNESS_FOUND_PYTHON3="$(type -P python3)" || return 1
  case "$SOUNDNESS_FOUND_PYTHON3" in
    /*) ;;
    *) return 1 ;;
  esac
  soundness_resolved="$("$SOUNDNESS_FOUND_PYTHON3" -I -S -c 'import os, sys; print(os.path.realpath(sys.executable))')" ||
    return 1
  case "$soundness_resolved" in
    *$'\n'* | '') return 1 ;;
    /*) ;;
    *) return 1 ;;
  esac
  [ -f "$soundness_resolved" ] && [ -x "$soundness_resolved" ] && ! [ -L "$soundness_resolved" ] || return 1
  printf '%s\n' "$soundness_resolved"
}
soundness_caller_python3=0
[ -z "${SOUNDNESS_PYTHON3+x}" ] || soundness_caller_python3=1
if [ "$SOUNDNESS_ATTEST_RUN" -eq 1 ] && [ "${SOUNDNESS_ENV_SCRUBBED:-}" != 1 ] && [ "$soundness_caller_python3" -eq 1 ]; then
  soundness_refuse_start "SOUNDNESS_PYTHON3 is set by the caller (SOUNDNESS_PYTHON3=${SOUNDNESS_PYTHON3:-}), but it is the gate's own pin of the one interpreter it runs, never an input; remedy: unset it (OD-XHOST-GATE-CWD-20261025)"
fi
soundness_scrub_python3="${SOUNDNESS_PYTHON3:-}"
SOUNDNESS_PYTHON3="$(soundness_resolve_python3)" || SOUNDNESS_PYTHON3=""
if [ "$SOUNDNESS_ATTEST_RUN" -eq 1 ]; then
  if [ -z "$SOUNDNESS_PYTHON3" ]; then
    soundness_refuse_start "the PATH this run was given finds no executable python3, or one that does not print the canonical path of an executable file when run with -I -S; remedy: make an absolute PATH entry name the directory of an executable python3. (OD-XHOST-GATE-CWD-20261025)"
  fi
  if [ "${SOUNDNESS_ENV_SCRUBBED:-}" = 1 ] && [ "$soundness_caller_python3" -eq 1 ] &&
     [ "$soundness_scrub_python3" != "$SOUNDNESS_PYTHON3" ]; then
    soundness_refuse_start "the interpreter the environment scrub ran as (SOUNDNESS_PYTHON3=${soundness_scrub_python3}) is not the one this run's PATH resolves to before the prelude (resolved: ${SOUNDNESS_PYTHON3:-}); remedy: run the script file again, with SOUNDNESS_PYTHON3 and SOUNDNESS_ENV_SCRUBBED unset (OD-XHOST-GATE-CWD-20261025)"
  fi
  # In an attested run the value is the scrub's (a caller's refused above).
  soundness_caller_python3=0
  [ "${SOUNDNESS_ENV_SCRUBBED:-}" != 1 ] || export SOUNDNESS_PYTHON3
else
  export SOUNDNESS_PYTHON3
fi
unset soundness_scrub_python3
if [ "${SOUNDNESS_ENV_SCRUBBED:-}" != 1 ] && [ "$SOUNDNESS_ATTEST_RUN" -eq 1 ]; then
  exec "$SOUNDNESS_PYTHON3" -I "${soundness_self_dir}/soundness_attestation.py" exec-scrubbed \
    --checkout "$soundness_candidate_dir" -- \
    "${BASH:-/bin/bash}" "${soundness_self_dir}/${soundness_self_name}" "$@"
fi

# ----------------------------------------------------------------------------
# Paths (env-overridable; default to this checkout and its $HOME-sibling repos).
# ----------------------------------------------------------------------------
# The gate variables a caller set, captured before any default is applied: the
# attest-mode settings policy (soundness_attestation.py check-env) refuses the
# ones that substitute an input the gate otherwise derives from the commit.
SOUNDNESS_EXPLICIT_SETTINGS=()
for soundness_setting in CLEAN_DIR AY_DIR ISLAND_VT_TABLES WASM_CFG_FUZZ_FUNCS TRUST_TARGO \
  ATERM_DIR TRUST_CG_DIR SOUNDNESS_SSH CLEAN_SOURCE_DIR AY_SOURCE_DIR; do
  [ -z "${!soundness_setting+x}" ] || SOUNDNESS_EXPLICIT_SETTINGS+=("$soundness_setting")
done
unset soundness_setting
# A census run replaced a caller's SOUNDNESS_PYTHON3 with its own pin above;
# its leg-weakening note still names it, as an --attest run refuses it.
[ "$soundness_caller_python3" -eq 0 ] || SOUNDNESS_EXPLICIT_SETTINGS+=(SOUNDNESS_PYTHON3)
unset soundness_caller_python3
TRUST_CG_DIR="${TRUST_CG_DIR:-$(CDPATH= cd -- "${soundness_self_dir}/.." && pwd)}"
# An explicit CLEAN_DIR / AY_DIR is used as given (refused under --attest).
# Otherwise the gate runs against its OWN detached checkouts at the candidate's
# pinned revisions (see "Pinned dependency checkouts" in the preflight), added
# from the object store of CLEAN_SOURCE_DIR / AY_SOURCE_DIR, never the $HOME
# working trees themselves.
CLEAN_DIR_EXPLICIT="${CLEAN_DIR:+1}"
AY_DIR_EXPLICIT="${AY_DIR:+1}"
CLEAN_SOURCE_DIR="${CLEAN_SOURCE_DIR:-$HOME/clean}"
AY_SOURCE_DIR="${AY_SOURCE_DIR:-$HOME/ay}"
CLEAN_DIR="${CLEAN_DIR:-$CLEAN_SOURCE_DIR}"
AY_DIR="${AY_DIR:-$AY_SOURCE_DIR}"
CLEAN_BIN="${CLEAN_DIR}/target/release/clean"
# The user cache base is resolved by the one rule trust-cg's own caches use
# (scripts/private_cache.py `cache-base`: an absolute XDG_CACHE_HOME, else an
# absolute HOME's .cache; an empty or relative value is ignored). With no
# usable base, SOUNDNESS_DEPS_DIR stays empty and the pinned checkouts refuse
# with SOUNDNESS_DEPS_DIR_REFUSAL. The rule runs before the host trust
# boundary, so it is named by this script's own directory (in an --attest run
# the candidate's scripts/, checked above to hold this very file), never by a
# caller's spelling of TRUST_CG_DIR (repair round 4 of
# OD-XHOST-GATE-CWD-20261025).
SOUNDNESS_DEPS_DIR_REFUSAL=""
if [ -z "${SOUNDNESS_DEPS_DIR:-}" ]; then
  if soundness_cache_base="$("$SOUNDNESS_PYTHON3" -I "${soundness_self_dir}/private_cache.py" cache-base 2>&1)"; then
    SOUNDNESS_DEPS_DIR="${soundness_cache_base}/trust-cg/soundness-deps"
  else
    SOUNDNESS_DEPS_DIR=""
    SOUNDNESS_DEPS_DIR_REFUSAL="$soundness_cache_base"
  fi
  unset soundness_cache_base
fi
# Every Cargo leg (trust-cg's and Clean's) runs through this wrapper: the Trust
# toolchain's `targo --unverified`, with TRUST_CG_*/TCG_* removed from the
# compiler's environment and handed to the executables it runs. A
# trust-cg-verify built by it records the Trust sysroot's bin/ay, the one AY
# the proof campaign admits. TRUST_TARGO names the package targo explicitly
# (refused under --attest: the preflight identities probe the package that
# scripts/trust_toolchain.py resolves, which is what trust_cargo.sh runs
# without it).
TRUST_CARGO="${TRUST_CG_DIR}/scripts/trust_cargo.sh"
# The aterm repository the vt-island tables are exported from when
# ISLAND_VT_TABLES is not given (see "VT-island tables" in the preflight). The
# exported commit and the dump's SHA-256 are recorded as a dependency.
ATERM_DIR="${ATERM_DIR:-$HOME/aterm}"
# The x86-64-native legs run on SOUNDNESS_X86_HOST (an ssh destination) when
# this host is not a native x86-64 host; see scripts/soundness_remote.sh.
SOUNDNESS_X86_HOST="${SOUNDNESS_X86_HOST:-}"
# The full-database proof campaign is part of this gate, not an opt-in: without
# it proof_gate_strict reports runtime SKIPs, and a SKIP fails the gate, so a
# gate that left it unset could never pass (2026-09-27).
export TRUST_CG_RUN_FORMAL_PROOF_TESTS="${TRUST_CG_RUN_FORMAL_PROOF_TESTS:-1}"
# The swiftcc SOURCE-side oracle driver: THIS GATE SETS NOTHING
# (OD-SWIFTCC-DRIVER-20261020, OD-SWIFTCC-PREFLIGHT-CAPABILITY-20261020).
#
# `e2e_x86_64_swiftcc` discovers its own driver — `TRUST_CG_SWIFTCALL_CC` if an
# operator names one, then the host `cc`, then the clang spellings — and keeps
# the first whose `__attribute__((swiftcall))` probe compiles, links and runs.
# An earlier version of this script discovered a clang and exported the
# variable; `--attest` then REFUSED the run, and rightly: the environment
# policy classifies a test control the gate sets itself as leg-affecting
# ("a test control variable the gate does not set changes what legs check"),
# because a gate that chooses its own oracle driver is weaker evidence than a
# target that probes for one. So the discovery lives in the target, where the
# probe is the authority, and nothing is exported here.
ATTESTATION_TOOL="${TRUST_CG_DIR}/scripts/soundness_attestation.py"
# Creates the gate's directories under the user cache (SOUNDNESS_DEPS_DIR):
# each new directory 0700 whatever the umask, an existing one never changed.
PRIVATE_CACHE_TOOL="${TRUST_CG_DIR}/scripts/private_cache.py"

private_path() {
  # private_path <path>: prints the CANONICAL path of <path> once
  # scripts/private_cache.py `require-private` accepted it (every canonical
  # ancestor owned by this user or root and renamable by nobody else; a file
  # also regular and writable by nobody else); on a refusal prints the reason
  # and fails. The rule judges the canonical path only, so the caller uses
  # the printed path from then on and never <path> again: <path> may lead
  # there through a symlink in a directory others can write, which they can
  # re-point after the check (X-HOST-P13 third closure audit).
  local resolved
  if ! resolved="$("$SOUNDNESS_PYTHON3" -I "$PRIVATE_CACHE_TOOL" require-private "$1" 2>&1)"; then
    printf '%s\n' "$resolved"
    return 1
  fi
  case "$resolved" in
    *$'\n'* | [!/]* | '')
      printf 'private_cache: require-private printed no single canonical path for %s\n' "$1"
      return 1 ;;
  esac
  printf '%s\n' "$resolved"
}

private_tree_path() {
  # private_tree_path <directory>: private_path for a directory the gate
  # builds and runs a checker from, judged as a WHOLE tree by
  # scripts/private_cache.py `require-private-tree`: the directory and its
  # canonical ancestors as `require-private` judges them, then every entry
  # below it (owned by this user, writable by nobody else, a symlink only
  # into the tree). Judging the checkout root alone let another user rewrite
  # a proof file Clean read in a group-writable subdirectory mid-run and
  # turn a failing pinned proof into an attested pass (X-HOST-P13 fourth
  # closure audit). Prints the canonical path, or the refusal and fails.
  local resolved
  if ! resolved="$("$SOUNDNESS_PYTHON3" -I "$PRIVATE_CACHE_TOOL" require-private-tree "$1" 2>&1)"; then
    printf '%s\n' "$resolved"
    return 1
  fi
  case "$resolved" in
    *$'\n'* | [!/]* | '')
      printf 'private_cache: require-private-tree printed no single canonical path for %s\n' "$1"
      return 1 ;;
  esac
  printf '%s\n' "$resolved"
}
REMOTE_RUNNER="${TRUST_CG_DIR}/scripts/soundness_remote.sh"
TIMEOUT_RUNNER="${TRUST_CG_DIR}/scripts/run_with_timeout.py"
SOUNDNESS_COMMAND_TIMEOUT_SECONDS="${SOUNDNESS_COMMAND_TIMEOUT_SECONDS:-7200}"

# Wasm offline-oracle configuration. The shared node validator replays the
# interpreter-computed expectations against the compiled wasm. The fuzzer
# budget is bounded and deterministic: a fixed function count here, a fixed
# LCG seed inside the example (never wall-clock).
WASM_DIFFTEST_MJS="${TRUST_CG_DIR}/crates/trust-cg-codegen/examples/wasm_difftest.mjs"
WASM_ISLAND_MJS="${TRUST_CG_DIR}/crates/trust-cg-codegen/examples/wasm_island_differential.mjs"
# The vt islands need aterm's exported tables (schema aterm.vt-islands.tables
# v1). Absent = a loud SKIP of that one gate, never a silent pass; point
# ISLAND_VT_TABLES at a dump from scripts/export_vt_tables.py to run it.
ISLAND_VT_TABLES="${ISLAND_VT_TABLES:-}"
ISLAND_VT_TABLES_EXPLICIT="${ISLAND_VT_TABLES:+1}"
WASM_CFG_FUZZ_FUNCS="${WASM_CFG_FUZZ_FUNCS:-200}"

# The Lean forward-simulation development (ENC-1) is a conditional model-level
# theorem with classified gaps. The gate below asserts `lake build` is green and
# pins the classified-sorry and explicit-axiom counts at their baselines. It
# lives at formal/lean below CANDIDATE_PROOF_DIR (export_candidate_proofs).
LEAN_FORMAL_SUBDIR="formal/lean"
# The tree trust-cg's OWN proofs are read from: proofs/*.lean (the inventory
# and the Clean checks) and formal/lean (the lake build and its ratchets).
# A census run reads the working tree. An --attest run reads only a private
# export of exactly the attested commit, made and judged by
# export_candidate_proofs before the first of those legs; until then, and if
# it is refused, those legs do not run.
CANDIDATE_PROOF_DIR="$TRUST_CG_DIR"
CANDIDATE_PROOF_SOURCE="the working tree (a census run writes no record)"
CANDIDATE_PROOF_REFUSAL=""
BASELINE_LEAN_SORRY=0   # source `sorry` lines (grep '^\s*sorry'); none since OD-LEAN-LINK-STEP-20261015
BASELINE_LEAN_AXIOM=0    # explicit axioms: none since the link step (OD-LEAN-LINK-STEP-20261015)
# The environment audit (formal/lean/scripts/AxiomAudit.lean) backs both counts:
# no Trust declaration may depend on sorryAx or on an axiom beyond propext,
# Classical.choice, Quot.sound and bv_decide's native-evaluation axioms, and
# the compile_refines capstone only on the first three.

# Clean is built with the same Trust toolchain as trust-cg (owner directive
# 2026-09-28). Until then this lane compiled Clean with a deliberately diverse
# stock toolchain and neutralized Clean's Trust-only target rustflags for it;
# that machinery lives in the history of this file before the migration.
# Clean's own `-Ztrust-verify=off` target stanza is inert under
# `targo --unverified`, which selects the unverified lane itself.

# Shared PATH prelude: ~/.elan/bin first for the Lean leg. Run
# scripts/gate_env.sh directly to print and check the resolved toolchain
# identities before a full run.
# shellcheck source=scripts/gate_env.sh
if ! source "${soundness_self_dir}/gate_env.sh" ||
   ! gate_env_prelude --with-lean; then
  echo "soundness_check.sh: cannot apply the scripts/gate_env.sh PATH prelude" >&2
  exit 1
fi
unset RUSTUP_TOOLCHAIN RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER RUSTFLAGS CARGO_ENCODED_RUSTFLAGS \
  CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS \
  CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUSTFLAGS \
  CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS \
  CARGO_TARGET_X86_64_APPLE_DARWIN_RUSTFLAGS

# ----------------------------------------------------------------------------
# Flags.
# ----------------------------------------------------------------------------
MODE_ATTEST=0     # --attest : clean committed HEAD, fail fast, write a record
MODE_KEEP_GOING=0 # --keep-going : never stop at the first failure (census)
MODE_PREFLIGHT_ONLY=0 # --preflight-only : stop after the preflight (with --attest)
HOST_LEGS=""      # --host-legs x86_64-native : run only that host class
SCOPE_ARG=""      # --scope portable : per-run + host-independent legs only
MODE_LIST=0       # --list   : list gates and exit
MODE_LIST_JSON=0  # --list-json : print the declared leg inventory and exit
MODE_VALIDATE_CLEAN_SUMMARY=""
MODE_SELF_TEST_CLEAN_CARGO_COMMAND=0
MODE_SELF_TEST_CARGO_GATES=0
MODE_VALIDATE_DEPENDENCY_LOCKS=0
MODE_RUN_WASM_ORACLES=0

usage() {
  # The whole leading comment block (a fixed line range would silently
  # truncate as the header grows).
  awk 'NR == 1 { next } !/^#/ { exit } { sub(/^# ?/, ""); print }' "${soundness_self_dir}/${soundness_self_name}"
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --pinned|--update)
      echo "soundness_check.sh: $1 is retired with soundness_revs.lock; use --attest (a per-commit record under refs/attest/soundness/)" >&2
      exit 2 ;;
    --attest)  MODE_ATTEST=1 ;;
    --keep-going) MODE_KEEP_GOING=1 ;;
    --preflight-only) MODE_PREFLIGHT_ONLY=1 ;;
    --host-legs)
      if [ "$#" -lt 2 ] || [ "$2" != x86_64-native ]; then
        echo "soundness_check.sh: --host-legs takes exactly: x86_64-native" >&2
        exit 2
      fi
      HOST_LEGS="$2"
      shift
      ;;
    --scope)
      if [ "$#" -lt 2 ] || { [ "$2" != portable ] && [ "$2" != full ]; }; then
        echo "soundness_check.sh: --scope takes exactly: portable or full" >&2
        exit 2
      fi
      SCOPE_ARG="$2"
      shift
      ;;
    --list)    MODE_LIST=1 ;;
    --list-json) MODE_LIST_JSON=1 ;;
    --validate-clean-summary)
      if [ "$#" -lt 2 ]; then
        echo "soundness_check.sh: --validate-clean-summary requires a log path" >&2
        exit 2
      fi
      MODE_VALIDATE_CLEAN_SUMMARY="$2"
      shift
      ;;
    --self-test-clean-cargo-command)
      MODE_SELF_TEST_CLEAN_CARGO_COMMAND=1
      ;;
    --self-test-cargo-gates)
      MODE_SELF_TEST_CARGO_GATES=1
      ;;
    --validate-dependency-locks)
      MODE_VALIDATE_DEPENDENCY_LOCKS=1
      ;;
    --run-wasm-oracles)
      MODE_RUN_WASM_ORACLES=1
      ;;
    -h|--help) usage; exit 0 ;;
    *) echo "soundness_check.sh: unknown argument: $1" >&2
       echo "  try --help" >&2
       exit 2 ;;
  esac
  shift
done
# A standalone mode is exactly one of these; the run modes (normal/--attest)
# combine only with --keep-going, --preflight-only, --host-legs and --scope.
standalone_modes=$((MODE_LIST + MODE_LIST_JSON + MODE_SELF_TEST_CLEAN_CARGO_COMMAND + \
  MODE_SELF_TEST_CARGO_GATES + MODE_VALIDATE_DEPENDENCY_LOCKS + MODE_RUN_WASM_ORACLES))
[ -z "$MODE_VALIDATE_CLEAN_SUMMARY" ] || standalone_modes=$((standalone_modes + 1))
if [ "$standalone_modes" -gt 1 ] || \
   { [ "$standalone_modes" -eq 1 ] && \
     { [ "$MODE_ATTEST" -eq 1 ] || [ "$MODE_KEEP_GOING" -eq 1 ] || \
       [ "$MODE_PREFLIGHT_ONLY" -eq 1 ] || [ -n "$HOST_LEGS" ] || [ -n "$SCOPE_ARG" ]; }; }; then
  echo "soundness_check.sh: that mode cannot be combined with another mode" >&2
  exit 2
fi
if { [ "$MODE_PREFLIGHT_ONLY" -eq 1 ] || [ -n "$HOST_LEGS" ]; } && [ "$MODE_ATTEST" -ne 1 ]; then
  echo "soundness_check.sh: --preflight-only and --host-legs require --attest" >&2
  exit 2
fi
if [ -n "$HOST_LEGS" ] && [ -n "$SCOPE_ARG" ]; then
  echo "soundness_check.sh: --scope and --host-legs are two scopes; name one" >&2
  exit 2
fi
# The run's scope: a full run, a portable run (no x86-64-native class), or only
# the x86-64-native class (the remote side).
RUN_SCOPE="full"
[ -z "$SCOPE_ARG" ] || RUN_SCOPE="$SCOPE_ARG"
[ -z "$HOST_LEGS" ] || RUN_SCOPE="$HOST_LEGS"
# Whether this scope carries the host-independent class (full and portable do).
scope_has_host_independent() { [ "$RUN_SCOPE" = full ] || [ "$RUN_SCOPE" = portable ]; }

# ----------------------------------------------------------------------------
# The host trust boundary (ruling LD-73). The user's own toolchain installs,
# git and its configuration and the candidate checkout are the host's trust
# boundary: no tool defends a build against a user who can rewrite the
# compiler. An --attest run still fails closed there:
# scripts/host_boundary.py judges the tools the run executes and the
# configuration it reads that its WHAT IS JUDGED list names, and no more (its
# NOT JUDGED list; OD-XHOST-GATE-CWD-20261025): the PATH above, prelude
# included, and every command in it; the gate's pinned python3
# (SOUNDNESS_PYTHON3, the interpreter running the check, no script, and on
# Linux the program /proc/self/exe names: refused otherwise) and its
# directories; the python3 a leg finds by name on that PATH, which must be the
# pinned file with no other pyvenv.cfg around its name (repair round 4);
# python3's import path, that of a run without -I included (the user
# site-packages and each directory its .pth files name; code there that runs
# at startup refuses); CARGO_HOME,
# RUSTUP_HOME, ELAN_HOME, the Trust package and the island twin rustc's
# install as whole trees; the candidate checkout, the work trees
# of the Clean, AY and aterm sources (where their fetches run) and the git
# directories of all four, with every alternate object store they borrow
# from, each verified with `git rev-parse` to be the work tree and git
# directory git itself uses (no core.worktree elsewhere, no subdirectory of
# another repository), as is each Cargo git database; git's configuration
# files and the programs and paths their keys name; ssh's configuration of
# $HOME and of the passwd home, $SHELL, /bin/sh and the program each fetch
# transport setting names, in every run, since a pinned checkout's `git
# fetch origin` may use ssh (a path through /proc or /dev/fd refuses
# outright: OD-XHOST-TRANSPORT-WORDS-20261024). It refuses any of them that
# another user can write:
# world-writable, group-writable by a group with a member other than this
# user, owned by another account, open through an ACL, or a directory whose
# default ACL opens what is created in it. It also refuses a candidate
# checkout, SOUNDNESS_DEPS_DIR (the Clean and AY builds), user cache,
# CARGO_HOME or CARGO_TARGET_DIR below a directory in which another user can
# create the `.cargo` Cargo reads, sticky or not: an --attest run's checkout
# cannot live below /tmp (ruling LD-75). And it refuses CARGO_HOME,
# CARGO_TARGET_DIR, RUSTUP_HOME, ELAN_HOME, SOUNDNESS_DEPS_DIR or ATPKG_BIN
# set to a value that is not an absolute path, naming the variable: Cargo,
# rustup, elan and this script resolve such a value against the working
# directory, which it cannot judge (LD-75 repair). It runs after the flags
# are parsed (a usage error exits 2 first) and
# before any other program: until here an --attest run executed only this
# bash (and the bash it was re-executed from) and python3 (the PATH python3
# printing its canonical path, once in each of those two bash runs, then that
# pinned file for the environment scrub and the cache-base rule), which it
# judges too: the pinned python3 as the file running the check. On a
# refusal the run prints the FAIL with
# every path and the remedy and stops HERE, even with --keep-going: every
# later step executes one of those tools, which would run another user's code
# as this user. No attestation is written. A census run does not check.
#
# The check judges the state when it runs. Once it has passed, the rest of an
# --attest run, every leg included (the trust-cg Cargo legs, the Clean and
# Lake legs, the x86-64 dispatch, the record), runs under umask 077, and a
# judged directory has no default ACL that could override that umask
# (LD-75). The pinned checkouts below SOUNDNESS_DEPS_DIR are not this
# check's: private_cache.py `require-private-tree` judges each one, its
# default and access ACLs included, before anything is built in it (see
# "Pinned dependency checkouts"). A census run keeps its caller's umask.
# ----------------------------------------------------------------------------
HOST_BOUNDARY_REPORT=""
if [ "$MODE_ATTEST" -eq 1 ]; then
  # The programs the run starts by absolute path: this bash (the one the
  # scrub re-executed, by its canonical path), the Cargo runner's
  # /usr/bin/env (scripts/trust_cargo.sh) and the Rosetta probe's
  # /usr/bin/arch and /usr/bin/true (macOS; a missing one is judged as such).
  # --python3: the gate's pinned interpreter, which runs the check: it judges
  # exactly that file and refuses it unless it is the interpreter running the
  # check (repair round 3 of OD-XHOST-GATE-CWD-20261025).
  host_boundary_args=(--search-path "$PATH" --candidate "$TRUST_CG_DIR" --python3 "$SOUNDNESS_PYTHON3"
    --tool "${BASH:-/bin/bash}"
    --tool /usr/bin/env --tool /usr/bin/arch --tool /usr/bin/true
    --git-repo "$CLEAN_SOURCE_DIR" --git-repo "$AY_SOURCE_DIR" --git-repo "$ATERM_DIR")
  [ -z "${ISLAND_TWIN_RUSTC:-}" ] || host_boundary_args+=(--tool-root "$ISLAND_TWIN_RUSTC")
  # OSTYPE is bash's host identity, so no unjudged discovery program runs here.
  # The boundary judges absolute xcrun, then the compiler and SDK it selects.
  case "$OSTYPE" in darwin*) host_boundary_args+=(--darwin-c-oracle) ;; esac
  # Cargo runs in the pinned Clean and AY checkouts below SOUNDNESS_DEPS_DIR
  # too: the check judges the .cargo Cargo reads above it (LD-75).
  [ -z "$SOUNDNESS_DEPS_DIR" ] || host_boundary_args+=(--cargo-root "$SOUNDNESS_DEPS_DIR")
  # --gate-git-config: on a pass the check also writes the run's own git
  # configuration (the credential helpers and identity it judged, nothing
  # else) and prints its path; every git the run starts reads that file as its
  # global configuration and no system file (OD-XHOST-GIT-PROGRAM-KEYS-20261024).
  host_boundary_args+=(--gate-git-config)
  # -B: the check writes no bytecode into the checkout it is about to judge.
  SOUNDNESS_GATE_GIT_CONFIG=""
  # The check itself is named by this script's own directory, the
  # candidate's scripts/ (checked above to hold this very file), not by
  # TRUST_CG_DIR, which a caller may spell through a path nothing has judged
  # yet (repair round 4 of OD-XHOST-GATE-CWD-20261025).
  if HOST_BOUNDARY_REPORT="$("$SOUNDNESS_PYTHON3" -I -B "${soundness_self_dir}/host_boundary.py" \
         "${host_boundary_args[@]}" 2>&1)"; then
    while IFS= read -r host_boundary_line; do
      case "$host_boundary_line" in
        "host_boundary: gate git configuration /"*)
          SOUNDNESS_GATE_GIT_CONFIG="${host_boundary_line#host_boundary: gate git configuration }" ;;
      esac
    done <<<"$HOST_BOUNDARY_REPORT"
    unset host_boundary_line
    if [ -z "$SOUNDNESS_GATE_GIT_CONFIG" ] || [ ! -f "$SOUNDNESS_GATE_GIT_CONFIG" ]; then
      HOST_BOUNDARY_REPORT="${HOST_BOUNDARY_REPORT}"$'\n'"host_boundary: FAIL: the check passed but named no git configuration file for the run (OD-XHOST-GIT-PROGRAM-KEYS-20261024)"
      SOUNDNESS_GATE_GIT_CONFIG=""
    fi
  fi
  if [ -z "$SOUNDNESS_GATE_GIT_CONFIG" ]; then
    # Builtins only from here: nothing the check refused may run.
    printf '%s\n' "==================== LOCAL SOUNDNESS META-GATE (#4) ====================="
    printf '%s\n' "trust-cg : $TRUST_CG_DIR" "mode     : ATTEST (committed HEAD; record on green)"
    printf '%s\n' "$HOST_BOUNDARY_REPORT"
    printf '%s\n' "---- SUMMARY"
    host_boundary_detail="${HOST_BOUNDARY_REPORT##*$'\n'}"
    printf '  [FAIL] %-46s %s\n' "preflight: host trust boundary" "$host_boundary_detail"
    printf '%s\n' "gates: 1 total  0 passed  1 failed  0 skipped"
    printf '%s\n' "STOPPED at the first failure (preflight: host trust boundary): nothing else ran."
    printf '%s\n' " SOUNDNESS GATE FAILED OR INCOMPLETE — see [FAIL]/[SKIP] rows above."
    printf '%s\n' "  no attestation record: the run failed or was incomplete. Resolve every FAIL and SKIP first."
    exit 1
  fi
  # Everything the run creates from here on is this user's alone (LD-75).
  umask 077
  # Every git program the run starts from here on (this script's, the
  # attestation tool's, private_cache.py's, export_vt_tables.py's,
  # gate_env.sh's, the git Cargo runs for net.git-fetch-with-cli, Lake's, and a
  # git any of their programs starts) reads no system configuration and, as
  # its global configuration, only the file the check just wrote: no key of
  # the user's own files reaches them except what that file carries
  # (OD-XHOST-GIT-PROGRAM-KEYS-20261024). Cargo's built-in libgit2 is the
  # exception: it ignores both variables and reads the default system, XDG
  # and global files itself. The check judged those files' keys by the
  # command, transport and path rules, whatever the caller's GIT_CONFIG_*
  # named, and the only programs Cargo runs from them are the credential
  # helpers, which it judged.
  export GIT_CONFIG_GLOBAL="$SOUNDNESS_GATE_GIT_CONFIG" GIT_CONFIG_NOSYSTEM=1
  # The file and its 0700 directory are this run's: removed when the run
  # exits (only that file, then the directory if it is then empty).
  trap 'rm -f -- "$SOUNDNESS_GATE_GIT_CONFIG"; rmdir -- "${SOUNDNESS_GATE_GIT_CONFIG%/*}" 2>/dev/null || :' EXIT
  # The run works from here on in the candidate checkout the check just
  # judged as a whole tree, as a landing-train or pre-push run starts there:
  # every program it starts by name, every lake and rustup proxy, Cargo
  # outside run_bounded, and the toolchain identities resolve what they look
  # for in the working directory there, never in the caller's
  # (OD-XHOST-GATE-CWD-20261025). After the trap above, so a failure here
  # still removes the gate's git configuration file (repair round 2).
  if ! CDPATH= cd -P -- "$TRUST_CG_DIR"; then
    printf '  [FAIL] %-46s %s\n' "preflight: host trust boundary" \
      "the check passed but the run cannot enter the judged candidate checkout ${TRUST_CG_DIR} (OD-XHOST-GATE-CWD-20261025)"
    printf '%s\n' "  no attestation record: the run failed or was incomplete. Resolve every FAIL and SKIP first."
    exit 1
  fi
fi

# Rosetta 2 is translation, not x86-64 silicon: it never satisfies an
# x86_64-native leg (those are dispatched to a native host). The variable is
# still set when Rosetta answers so that ad-hoc linkrun tests outside this gate
# behave as before (tests/common/rosetta.rs, #582).
if [ "$(uname -s)-$(uname -m)" = Darwin-arm64 ] && /usr/bin/arch -x86_64 /usr/bin/true 2>/dev/null; then
  export TRUST_CG_RUN_ROSETTA_LINKRUN="${TRUST_CG_RUN_ROSETTA_LINKRUN:-1}"
fi

# ----------------------------------------------------------------------------
# Output helpers.
# ----------------------------------------------------------------------------
if [ -t 1 ]; then
  C_RED=$'\033[31m'; C_GRN=$'\033[32m'; C_YEL=$'\033[33m'
  C_BLU=$'\033[34m'; C_BLD=$'\033[1m';  C_RST=$'\033[0m'
else
  C_RED=''; C_GRN=''; C_YEL=''; C_BLU=''; C_BLD=''; C_RST=''
fi

hr() { printf '%s\n' "------------------------------------------------------------------------"; }
section() { printf '\n%s%s%s\n' "$C_BLD" "$1" "$C_RST"; hr; }

# Per-gate result accounting. Parallel arrays keep order + status + detail.
GATE_NAMES=()
GATE_STATUS=()   # PASS / FAIL / SKIP
GATE_DETAIL=()
FAIL_COUNT=0
PASS_COUNT=0
SKIP_COUNT=0
# RUN_PHASE is preflight, legs or post. FAIL_FAST stops a --attest run at the
# first non-PASS leg (the preflight always completes, then stops the run).
RUN_PHASE=preflight
FAIL_FAST=0
LEGS_TSV=""
LAST_RECORD_SECONDS=$SECONDS

record() {
  # record <name> <PASS|FAIL|SKIP> <detail> [<log path>]
  # SKIP identifies an unexecuted external-runtime/data prerequisite, distinct
  # from an executed test failure. Either prevents overall success and any
  # attestation record. Cargo's ignored cases and runtime SKIPs reject that
  # Cargo gate as FAIL. Every name is a leg id of soundness_leg_inventory.
  local seconds=$((SECONDS - LAST_RECORD_SECONDS))
  LAST_RECORD_SECONDS=$SECONDS
  GATE_NAMES+=("$1")
  GATE_STATUS+=("$2")
  GATE_DETAIL+=("$3")
  if [ -n "$LEGS_TSV" ]; then
    printf '%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "$seconds" "${4:-}" \
      "$(printf '%s' "$3" | tr '\t\n' '  ')" >>"$LEGS_TSV"
  fi
  if [ "$2" = "PASS" ]; then
    PASS_COUNT=$((PASS_COUNT + 1))
    printf '  %s[PASS]%s %-46s %s\n' "$C_GRN" "$C_RST" "$1" "$3"
  elif [ "$2" = "SKIP" ]; then
    SKIP_COUNT=$((SKIP_COUNT + 1))
    printf '  %s[SKIP]%s %-46s %s\n' "$C_YEL" "$C_RST" "$1" "$3"
  else
    FAIL_COUNT=$((FAIL_COUNT + 1))
    printf '  %s[FAIL]%s %-46s %s\n' "$C_RED" "$C_RST" "$1" "$3"
  fi
  if [ "$2" != PASS ] && [ "$FAIL_FAST" -eq 1 ] && [ "$RUN_PHASE" = legs ]; then
    STOPPED_AT="$1"
    finish_run
  fi
}

# ----------------------------------------------------------------------------
# Gate inventories (single source of truth — also used by --list).
# ----------------------------------------------------------------------------

# trust-cg test targets (run through scripts/trust_cargo.sh test).
# Gate targets that MUST run in release and include #[ignore]d cases. These
# carry large sweeps (the encoding/lane corpora) that are impractical in debug.
#
# THIS ARRAY IS THE SINGLE SOURCE OF TRUTH, and it exists because duplicating
# the list silently broke the harness self-test: d0aeb997 added
# x86_sse_lane_gate to the dispatch condition below but not to the copy inside
# scripts/test_soundness_check.sh, so 19 of that script's 74 cases failed while
# every cargo target stayed green. `--list` publishes this set and the
# self-test reads it from there, so the two can no longer drift.
TRUST_CG_RELEASE_INCLUDE_IGNORED_GATES=(
  wasm_encoding_gate
  x86_encoding_gate
  x86_sse_lane_gate
  x86_movsxd_sib_gate
)

TRUST_CG_GATES=(
  coverage_gate_tests
  meta_theorems
  mutation_catalog
  proof_gate_strict
  fsym_real_function_corpus
  aarch64_affine_lowering
  aarch64_trust_ir_affine_lowering
  wasm_encoding_gate
  x86_encoding_gate
  x86_sse_lane_gate
  aarch64_value_decode_gate
  x86_movsxd_sib_gate
  x86_addressing_gate
  x86_volatile_trace_gate
  reconstruction_x86
  wasm_cfg_structural_gate
  wasm_abi_proofs_gate
  wasm_internal_abi_gate
  wasm_value_domain_gate
  bdefs_differential_bridge
  bdefs_differential_bridge_x86
  bdefs_differential_bridge_riscv
  bdefs_differential_bridge_x86_packed
  bdefs_differential_bridge_x86_fp
  bdefs_differential_bridge_neon
  bdefs_differential_bridge_riscv_fp
  bdefs_differential_bridge_neon_fp
  fp_bitmodel_bridge
)

# TRUST_CG_GATES targets whose evidence needs x86-64 SILICON. They stay in
# TRUST_CG_GATES; this class array decides where they run: locally only on a native x86-64 host, otherwise on
# SOUNDNESS_X86_HOST. x86_sse_lane_gate's SDM-vs-silicon differential compiles
# only for target_arch x86_64, so an arm64 run of it would pass having compared
# nothing; the dispatched run sets TRUST_CG_REQUIRE_X86_SILICON=1, which makes
# the target fail when that half did not run.
TRUST_CG_X86_NATIVE_GATES=(
  x86_sse_lane_gate
)

# Package|filter pairs, executed separately so a stale/renamed filter cannot
# borrow passing tests from another gate. Codegen's default features include
# verify. These filters are library tests, not integration target names.
TRUST_CG_LIB_GATES=(
  'trust-cg-verify|tv2_'
  'trust-cg-verify|coverage_gate::'
  'trust-cg-verify|source_bound_frame::tests::framed_control_'
  'trust-cg-verify|source_bound_frame::tests::frameless_'
  'trust-cg-verify|source_bound_a64_body::tests::pure_jump_cycle_binds_forward_and_negative_decoded_displacements'
  'trust-cg-verify|source_bound_a64_body::'
  'trust-cg-verify|source_bound_a64_body::tests::narrow_return_carriers_bind_the_source_extension_and_return_bits'
  'trust-cg-verify|source_bound_a64_body::tests::all_integer_zero_extensions_bind_at_their_exact_widths'
  'trust-cg-codegen|affine_lowering_tests'
  'trust-cg-regalloc|post_ra_coalesce::tests::test_identity_only_preserves_distinct_copies_and_wide_observations'
  'trust-cg-codegen|dead_literal_cleanup_preserves_live_values_clobbers_and_invalid_forms'
  'trust-cg-codegen|aarch64_frame_lowering_'
  'trust-cg-codegen|forced_aarch64_frame_pointers_cover_zero_storage_and_red_zone_leaves'
  'trust-cg-codegen|address_free_core_source_checked_structural_returns_'
  'trust-cg-codegen|verification_precondition'
  'trust-cg-codegen|jit_cert::tests::'
  'trust-cg-codegen|test_generate_proof_certificates_rejects'
  'trust-cg-codegen|x86_authoritative_'
  'trust-cg-verify|x86_source_bound_envelope'
  'trust-cg-codegen|x86_envelope_jit_tests'
  'trust-cg-verify|checked_mul_i128_proofs::tests::credit_'
  'trust-cg-verify|x86_source_bound_body::tests::slice5::'
  'trust-cg-verify|x86_source_bound_body::tests::slice6::'
  'trust-cg-verify|x86_source_bound_body::tests::slice7::'
  'trust-cg-verify|x86_source_bound_body::tests::slice9::'
  'trust-cg-verify|x86_source_bound_body::tests::slice10::'
  'trust-cg-verify|x86_source_bound_body::tests::slice11::'
  'trust-cg-verify|x86_source_bound_body::tests::slice12::'
  'trust-cg-verify|x86_source_bound_body::tests::slice13::'
  'trust-cg-verify|x86_source_bound_body::tests::slice14::'
  'trust-cg-verify|x86_source_bound_body::tests::slice15::'
  'trust-cg-verify|x86_source_bound_body::tests::slice16::'
  'trust-cg-verify|x86_source_bound_body::tests::slice23::'
  'trust-cg-verify|x86_source_bound_body::tests::i128_const_shift::'
  'trust-cg-verify|x86_source_bound_body::tests::qualification_matrix::'
  'trust-cg-verify|source_bound_negative_memo::'
  'trust-cg-verify|x86_source_bound_body::tests::negative_memo::'
  # The portable certificate sets' CHECKER-IDENTITY bindings
  # (OD-CERT-SET-HOST-QUALIFICATION-20261022). Each of these fails on a host
  # whose drat-trim bytes its set's manifest does not authorize, and the
  # failure is otherwise SILENT: an unauthorized checker declines CERT-SKIP for
  # every query and reads exactly like a cache miss, so the set credits
  # nothing while the gate says green. That is what happened here — three of
  # them were red on x86_64-unknown-linux-gnu through a census that reported
  # ALL GREEN, because no filter named `canary_cert::`.
  'trust-cg-verify|canary_cert::bound_memory::tests::'
  'trust-cg-verify|canary_cert::tests::committed_set_binds_the_exact_runtime_checker_bytes'
)

# Package|integration-target pairs outside trust-cg-verify. Each is a whole
# integration target (never a filter), so the result parser requires it to run
# unfiltered.
#   insert_field_value_semantics — WS7.1: the adapter lowers InsertField /
#     InsertElement as VALUE updates (F-111); native == closed form == trust-ir
#     interpreter on the proof program's miscompile witnesses and the
#     adversarial loop/swap/parameter/array corpus, store form refused by name.
#   insert_field_store_form — the same store-form refusal on the CLI.
#   ingest_admission — WS7.3 (F-113): every ingestion entry (object/CLI path,
#     host JIT, compile service, wasm lane) refuses what trust-ir's validator
#     refuses, the dialect-rewritten module is re-admitted, and a source scan
#     holds every public compile*/translate_* entry to admission.
#   v41_abi_residue_objects — the codegen-license refusals the ingestion
#     admission runs first (compiler and compile service), with the v41 ABI /
#     linkage residue they share a target with.
#   x86_64_elf_symbol_binding — x86-64 ELF binding of module-local functions
#     and visibility on a function definition (rulings
#     OD-X86-ELF-LOCAL-BINDING-20261027,
#     OD-X86-ELF-DEFINITION-VISIBILITY-20261027): the object-level legs run on
#     every host, and on an x86-64 Linux GNU host the link-and-run legs
#     (two objects whose module-local helpers share a name, the `.dynsym` of a
#     shared link) run too, gated at COMPILE time so no host counts a runtime
#     skip as a pass.
#   x86_source_bound_body — AOT body-theorem routing and runtime-routine
#     module/link-unit refusals, including bodies stated in parts.
TRUST_CG_PACKAGE_INTEGRATION_GATES=(
  'trust-cg-codegen|aarch64_framed_identity_control'
  'trust-cg-codegen|aarch64_nonleaf_frame_control'
  'trust-cg-codegen|aarch64_narrow_return_body'
  'trust-cg-codegen|aarch64_live_constant_body'
  'trust-cg-codegen|insert_field_value_semantics'
  'trust-cg-cli|insert_field_store_form'
  'trust-cg-codegen|ingest_admission'
  'trust-cg-codegen|v41_abi_residue_objects'
  'trust-cg-codegen|aarch64_elf_symbol_binding'
  'trust-cg-codegen|x86_64_elf_symbol_binding'
  'trust-cg-codegen|x86_source_bound_body'
)

# Clean .lean proofs to clean-check (B-defs + LRAT checkers).
CLEAN_LEAN=(
  aarch64_isa
  aarch64_isa_chip
  aarch64_fp
  aarch64_fp_arith
  aarch64_fp_cvt
  aarch64_fp_divsqrt
  aarch64_fp16
  reducible_word
  lrat_checker
  lrat_checker_word
  lrat_checker_tree
)

# trust-cg's OWN Clean specs under proofs/ (the specs the Rust weld tests
# hand-mirror). Every proofs/*.lean file must be listed here: a proof that is
# not gated is unenforced text, so an unlisted file fails the inventory leg.
TRUST_CG_LEAN=(
  abi_clobber_spec
  sentinel_decide_spec
  mir_place_resolution_spec
)

is_x86_native_gate() {
  local gate
  for gate in "${TRUST_CG_X86_NATIVE_GATES[@]}"; do
    [ "$gate" != "$1" ] || return 0
  done
  return 1
}

# ----------------------------------------------------------------------------
# THE LEG INVENTORY: every row an attested run records, with its host class,
# in the order the run records them. This function is the single source of
# truth: --list-json publishes it, scripts/soundness_attestation.py verifies a
# commit against the copy its OWN --list-json prints, an attested run records
# exactly this set (the "inventory:" row below checks it before any record is
# written), and scripts/tests/test_soundness_leg_inventory.py checks that
# every record() call site in this file names a row here and every row here is
# named by a call site. Classes:
#   per-run          recorded by every attested run, full, portable or x86_64-native
#   host-independent recorded by a full or portable run on any host
#   x86_64-native    recorded only where x86-64 silicon executes natively
#   dispatch         recorded by a full run on a host that is not native
#                    x86-64 (it imports the x86-64 host's record instead);
#                    a portable run records neither this nor x86_64-native
# ----------------------------------------------------------------------------
soundness_leg_inventory() {
  local gate stem label
  printf 'per-run\tpreflight: host trust boundary\n'
  printf 'per-run\tpreflight: leg-weakening settings\n'
  printf 'host-independent\tpreflight: clean checkout\n'
  printf 'host-independent\tpreflight: ay checkout\n'
  printf 'host-independent\tpreflight: vt tables exported\n'
  printf 'per-run\tpreflight: Trust toolchain\n'
  printf 'per-run\tpreflight: Trust toolchain ships bin/ay\n'
  printf 'per-run\tpreflight: timeout runner present\n'
  printf 'per-run\tpreflight: positive command timeout\n'
  printf 'per-run\tpreflight: trust-cg dir present\n'
  printf 'host-independent\tpreflight: clean dir present\n'
  printf 'host-independent\tpreflight: ay dir present\n'
  for label in TrustIR Clean AY; do
    printf 'per-run\tpreflight: candidate %s revision\n' "$label"
  done
  printf 'host-independent\tpreflight: gate environment (scripts/gate_env.sh)\n'
  printf 'host-independent\tpreflight: companion coherence\n'
  printf 'host-independent\tpreflight: node present\n'
  printf 'host-independent\tpreflight: rustc wasm32 target\n'
  printf 'per-run\tpreflight: toolchain identities recorded\n'
  printf 'x86_64-native\tpreflight: native x86-64 host\n'
  printf 'dispatch\tpreflight: x86-64 executor reachable\n'
  printf 'per-run\tattest: trust-cg worktree clean\n'
  printf 'host-independent\tattest: clean worktree clean\n'
  printf 'host-independent\tattest: ay worktree clean\n'
  printf 'host-independent\tattest: Clean matches candidate dependency\n'
  printf 'host-independent\tattest: AY matches candidate dependency\n'
  for gate in "${TRUST_CG_GATES[@]}"; do
    if is_x86_native_gate "$gate"; then
      printf 'x86_64-native\t%s\n' "$gate"
    else
      printf 'host-independent\t%s\n' "$gate"
    fi
  done
  for gate in "${TRUST_CG_LIB_GATES[@]}"; do
    printf 'host-independent\t%s --lib %s\n' "${gate%%|*}" "${gate#*|}"
  done
  printf 'host-independent\ttrust-cg-lower --lib lattice_guard::tests:: --features lattice-guard-elision\n'
  printf 'host-independent\ttrust-cg-codegen --test a64_lattice_guard_elision_differential --features lattice-guard-elision\n'
  printf 'host-independent\ttrust-cg-lower --test refine_erasure_hazards\n'
  printf 'host-independent\ttrust-cg-codegen --test a64_refine_byte_invariance\n'
  printf 'host-independent\ttrust-cg-llvm-import --test c_string_escapes_e2e --features driver\n'
  # Named exactly as run_cargo_gate records a non-trust-cg-verify integration
  # target ("<package> --test <target>"); run_trust_cg_cargo_gates runs these
  # after the library, feature-enabled and refinement-representation gates,
  # on the host-independent class.
  for gate in "${TRUST_CG_PACKAGE_INTEGRATION_GATES[@]}"; do
    printf 'host-independent\t%s --test %s\n' "${gate%%|*}" "${gate#*|}"
  done
  for label in "wasm difftest" "wasm cfg-fuzz"; do
    printf 'host-independent\t%s: emit corpus\n' "$label"
    printf 'host-independent\t%s: node oracle\n' "$label"
  done
  for label in "wasm canary island" "wasm memhash island" "wasm vt islands"; do
    printf 'host-independent\t%s: emit island\n' "$label"
    printf 'host-independent\t%s: three-way differential\n' "$label"
  done
  printf 'host-independent\tClean release binary matches checkout\n'
  for stem in "${CLEAN_LEAN[@]}"; do
    printf 'host-independent\tclean-check %s\n' "$stem"
  done
  printf 'host-independent\ttrust-cg proofs/*.lean inventory\n'
  for stem in "${TRUST_CG_LEAN[@]}"; do
    printf 'host-independent\tclean-check trust-cg proofs/%s\n' "$stem"
  done
  printf 'host-independent\tclean-kernel --test micro_diversity_gate\n'
  printf 'host-independent\tformal/lean lake build\n'
  printf 'host-independent\tformal/lean sorry-count == %s\n' "$BASELINE_LEAN_SORRY"
  printf 'host-independent\tformal/lean axiom-count == %s\n' "$BASELINE_LEAN_AXIOM"
  printf 'host-independent\tformal/lean axiom audit (no sorryAx, no project axiom)\n'
  printf 'host-independent\ttrust-cg-codegen --test lean_encode_golden_binding\n'
  printf 'host-independent\ttrust-cg-codegen --test lean_a64_encode_golden_binding\n'
  printf 'x86_64-native\ttrust-cg-codegen --test e2e_x86_64_callee_saved\n'
  printf 'x86_64-native\ttrust-cg-codegen --test e2e_x86_64_calling_conv\n'
  printf 'x86_64-native\ttrust-cg-codegen --test e2e_x86_64_swiftcc\n'
  printf 'host-independent\ttrust-cg-codegen --test must_refuse_corpus\n'
  printf 'host-independent\ttrust-cg-cli --test must_refuse_corpus\n'
  printf 'host-independent\ttrust-cg-codegen --test trust_ir_interp_differential\n'
  printf 'host-independent\ttrust-cg-codegen --test trust_ir_interp_differential --features mutation-knobs\n'
  printf 'host-independent\ttrust-cg-cli --test emit_proofs_adapter_disclosure\n'
  printf 'host-independent\tx86 icmp certificates (pinned AY + the rule'"'"'s Clean)\n'
  printf 'host-independent\ttrust-cg-lower --test codegen_license_evidence\n'
  printf 'host-independent\ttrust-cg-codegen --test codegen_license_evidence\n'
  printf 'host-independent\ttrust-cg-cli --test codegen_license_flags\n'
  printf 'dispatch\tx86_64-native: remote record\n'
  for label in trust-cg clean ay; do
    if [ "$label" = trust-cg ]; then
      printf 'per-run\tpost-run: %s HEAD unchanged\n' "$label"
      printf 'per-run\tpost-run: %s worktree clean\n' "$label"
    else
      printf 'host-independent\tpost-run: %s HEAD unchanged\n' "$label"
      printf 'host-independent\tpost-run: %s worktree clean\n' "$label"
    fi
  done
  printf 'per-run\tinventory: executed legs match the declared inventory\n'
}

soundness_leg_inventory_json() {
  soundness_leg_inventory | "$SOUNDNESS_PYTHON3" -I -c '
import json, sys
legs = []
for line in sys.stdin.read().splitlines():
    leg_class, leg_id = line.split("\t", 1)
    legs.append({"id": leg_id, "class": leg_class})
print(json.dumps({"schema": "trust-cg-soundness-legs-v1", "legs": legs}, indent=2))
'
}

if [ "$MODE_LIST_JSON" -eq 1 ]; then
  soundness_leg_inventory_json
  exit $?
fi

if [ "$MODE_LIST" -eq 1 ]; then
  echo "trust-cg gate test targets (targo --unverified test -p trust-cg-verify --test <name>):"
  for g in "${TRUST_CG_GATES[@]}"; do echo "  - $g"; done
  echo
  echo "trust-cg library gates (targo --unverified test --locked -p <package> --lib <filter> -- --test-threads=1):"
  for g in "${TRUST_CG_LIB_GATES[@]}"; do
    echo "  - ${g%%|*} --lib ${g#*|}"
  done
  echo
  echo "trust-cg feature-enabled authority gates (required, with the same timeout and non-vacuity checks):"
  echo "  - trust-cg-lower --lib lattice_guard::tests:: --features lattice-guard-elision"
  echo "  - trust-cg-codegen --test a64_lattice_guard_elision_differential --features lattice-guard-elision"
  echo
  echo "trust-cg refinement representation gates (required, host-independent):"
  echo "  - trust-cg-lower --test refine_erasure_hazards"
  echo "  - trust-cg-codegen --test a64_refine_byte_invariance"
  echo
  echo "trust-cg LLVM importer comparison gate (driver feature; native rows on matching hosts):"
  echo "  - trust-cg-llvm-import --test c_string_escapes_e2e --features driver"
  echo
  echo "trust-cg package integration gates (targo --unverified test --locked -p <package> --test <name>):"
  for g in "${TRUST_CG_PACKAGE_INTEGRATION_GATES[@]}"; do
    echo "  - ${g%%|*} --test ${g#*|}"
  done
  echo
  echo "trust-cg wasm offline oracles (targo --unverified run --example <name> + node wasm_difftest.mjs):"
  echo "  - wasm_difftest (interpreter-vs-compiled-wasm differential over the CF corpus)"
  echo "  - wasm_cfg_fuzz (${WASM_CFG_FUZZ_FUNCS} reducible CFGs at a fixed seed, same oracle;"
  echo "    node unavailable = loud SKIP of the node leg, never a silent pass)"
  echo
  echo "Clean checkout: clean-check .lean proofs (clean check proofs/<name>.lean):"
  for f in "${CLEAN_LEAN[@]}"; do echo "  - $f"; done
  echo
  echo "Clean checkout: kernel diversity gate:"
  echo "  - targo --unverified test -p clean-kernel --test micro_diversity_gate"
  echo
  echo "trust-cg checkout: clean-check repository proofs (clean check proofs/<name>.lean;"
  echo "  same Clean release binary; checker absent = loud SKIP, never a silent pass;"
  echo "  an unlisted proofs/*.lean file fails the inventory leg):"
  for f in "${TRUST_CG_LEAN[@]}"; do echo "  - $f"; done
  echo
  echo "formal/lean forward-sim (ENC-1):"
  echo "  - lake build (formal/lean) + sorry-count==${BASELINE_LEAN_SORRY} + axiom-count==${BASELINE_LEAN_AXIOM}"
  echo "  - lake env lean scripts/AxiomAudit.lean: no declaration depends on sorryAx or a project"
  echo "    axiom; compile_refines depends on propext, Classical.choice and Quot.sound only"
  echo
  echo "ENC-4 Lean<->backend encoder golden binding:"
  echo "  - targo --unverified test -p trust-cg-codegen --test lean_encode_golden_binding (Rust leg;"
  echo "    Lean leg is the EncoderGolden.lean 'by decide' theorems compiled by lake above)"
  echo
  echo "X-LEAN-P3 Lean A64 instruction-word model <-> AArch64 emitter golden binding:"
  echo "  - targo --unverified test -p trust-cg-codegen --test lean_a64_encode_golden_binding (Rust leg:"
  echo "    encode_instruction, the field-level helpers and ENC-5 against every generated row;"
  echo "    Lean leg is Trust/A64/EncoderGolden.lean's kernel-checked theorems compiled by lake above)"
  echo
  echo "ABI-x86-cs x86-64 callee-saved preservation:"
  echo "  - targo --unverified test -p trust-cg-codegen --test e2e_x86_64_callee_saved (SysV execution"
  echo "    oracle with an 8-control probe battery, plus an objdump-independent"
  echo "    body-touches-vs-prologue-saves refutation for SysV AND Windows x64)"
  echo
  echo "ABI-x86-cc x86-64 non-C calling conventions:"
  echo "  - targo --unverified test -p trust-cg-codegen --test e2e_x86_64_calling_conv (two-direction"
  echo "    clang execution oracle -- clang calls trust-cg and trust-cg calls clang --"
  echo "    with a 19-control wrong-register/wrong-stack-slot assembly battery over"
  echo "    both edges, plus always-running admission controls"
  echo "    including the aarch64-vs-x86-64 Swift-return-budget differential at all"
  echo "    three guard sites and the fail-closed unwitnessed Windows x64 ABI)"
  echo "  - targo --unverified test -p trust-cg-codegen --test e2e_x86_64_swiftcc (the MEASURED"
  echo "    swiftcc return-placement oracle via clang's __attribute__((swiftcall));"
  echo "    prints SKIP: (E4) NOT RUN where the host cc is GCC -- XD-03)"
  echo
  echo "KIND 4 must-refuse corpus (trust-ir's consumer contract, through this backend's real admission paths):"
  echo "  - targo --unverified test -p trust-cg-codegen --test must_refuse_corpus (decode, strict adapter,"
  echo "    AOT compiler and compile-service lanes over every row of the pinned trust-ir's"
  echo "    must-refuse corpus; the control row must be accepted; known-accepted rows are"
  echo "    named with reasons and the list is exact in both directions)"
  echo "  - targo --unverified test -p trust-cg-cli --test must_refuse_corpus (the same corpus handed to the"
  echo "    real trust-cg binary: non-zero exit and no object per row, an object for the control)"
  echo
  echo "WS7.2 trust-ir -> native differential (the adapter step no certificate covers):"
  echo "  - targo --unverified test -p trust-cg-codegen --test trust_ir_interp_differential (the vendored"
  echo "    trust_ir_exec corpus and the pinned-seed aggregate generator, JIT at O0-O3 against the"
  echo "    trust-ir reference interpreter; UB vectors skipped, an all-skipped entry fails)"
  echo "  - targo --unverified test -p trust-cg-codegen --test trust_ir_interp_differential --features mutation-knobs"
  echo "    (negative twin: with legacy_in_place_insert on the same gate must report the c13 mismatches)"
  echo "  - targo --unverified test -p trust-cg-cli --test emit_proofs_adapter_disclosure (--emit-proofs names"
  echo "    trust-ir->lir NOT COVERED, prints no function-level VERIFIED; the release CLI carries no knob)"
  echo
  echo "x86-64 vector-compare certificates (trust-ir's per-cell rule, ground (b)):"
  echo "  - scripts/check_x86_icmp_certificates.py (read trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE from the"
  echo "    compiled trust-ir; build the rule's AY, which must be the Cargo.lock pin, and the rule's Clean"
  echo "    by revision under heavy_gate; regenerate every cell query, require its certified sha256 and"
  echo "    trust-ir's spec side, and re-run AY --strict-proofs + Clean cert verify-external on each;"
  echo "    a missing input FAILS unless SOUNDNESS_SKIP_X86_ICMP_CERTIFICATES=1 makes it a loud SKIP)"
  echo
  echo "WS7.5 codegen license (evidence-bound clean-kernel-tv; claim-less bodies refused by default):"
  echo "  - targo --unverified test -p trust-cg-lower --test codegen_license_evidence (every adapter entry)"
  echo "  - targo --unverified test -p trust-cg-codegen --test codegen_license_evidence (AOT, JIT, Core,"
  echo "    compile service, wasm32; the real Clean addmul compiles and runs natively)"
  echo "  - targo --unverified test -p trust-cg-cli --test codegen_license_flags (the CLI, --permit-unlicensed"
  echo "    and its disclosure line)"
  echo
  echo "trust-cg release-mode gate test targets (targo --unverified test -p trust-cg-verify --test <name> --release -- --include-ignored):"
  for release_gate in "${TRUST_CG_RELEASE_INCLUDE_IGNORED_GATES[@]}"; do
    echo "  - $release_gate"
  done
  echo
  echo "x86_64-native class (run only on a native x86-64 host; dispatched to SOUNDNESS_X86_HOST otherwise):"
  for g in "${TRUST_CG_X86_NATIVE_GATES[@]}"; do echo "  - $g"; done
  echo "  - e2e_x86_64_callee_saved, e2e_x86_64_calling_conv, e2e_x86_64_swiftcc"
  echo
  echo "Every recorded leg with its class: --list-json."
  echo
  echo "Named exclusions: none in the soundness gate."
  exit 0
fi

# ----------------------------------------------------------------------------
# Candidate dependency identities (derived from the commit's own Cargo locks).
# ----------------------------------------------------------------------------
candidate_repository_org() {
  # Read the candidate's declared upstream identity from committed policy.
  # Publication rewrites this field together with dependency source owners,
  # so contributor forks do not depend on their mutable `origin` remote.
  local manifest="${TRUST_CG_DIR}/Cargo.toml"
  local parsed_org
  [ -f "$manifest" ] || { echo INVALID; return 1; }

  if ! parsed_org="$(
    sed -n \
      '/^[[:space:]]*\[workspace\.package\][[:space:]]*$/,/^[[:space:]]*\[/p' \
      "$manifest" |
      grep -E '^[[:space:]]*repository[[:space:]]*=' |
      sed -E 's|^[[:space:]]*repository[[:space:]]*=[[:space:]]*"https://github\.com/([A-Za-z0-9][A-Za-z0-9_.-]*)/trust-cg(\.git)?"[[:space:]]*$|ORG:\1|' |
      awk '
        NF != 1 || $1 !~ /^ORG:[A-Za-z0-9][A-Za-z0-9_.-]*$/ { bad=1; next }
        { count += 1; org = substr($1, 5) }
        END {
          if (!bad && count == 1) print org
          else exit 1
        }
      '
  )"; then
    echo INVALID
    return 1
  fi
  printf '%s\n' "$parsed_org"
}

candidate_dependency_lock_paths() {
  # Independently resolved Cargo roots. AY is deliberately absent from the
  # fuzz graph because the optional AY regalloc feature is not enabled there.
  # TrustIR and its transitive Clean kernel must agree in all three roots.
  case "$1" in
    ay)
      printf '%s\n' \
        "Cargo.lock" \
        "crates/rustc-codegen-trust-cg/Cargo.lock"
      ;;
    clean|trust-ir)
      printf '%s\n' \
        "Cargo.lock" \
        "crates/rustc-codegen-trust-cg/Cargo.lock" \
        "fuzz/Cargo.lock"
      ;;
    *) return 1 ;;
  esac
}

dependency_rev_from_lock() {
  # dependency_rev_from_lock <repo> <relative-lock> <repository-org>
  # Require one exact source identity inside one independently resolved lock.
  local repo="$1" relative_lock="$2" repository_org="$3"
  local lock="${TRUST_CG_DIR}/${relative_lock}"
  local parsed_rev

  if [ ! -f "$lock" ]; then
    echo "soundness_check.sh: dependency authority: missing ${relative_lock}" >&2
    return 1
  fi
  if ! parsed_rev="$(
    grep -E "^[[:space:]]*source = \"git\+[^\"]*/${repo}\\.git([?#\"]|$)" \
      "$lock" 2>/dev/null |
      sed -E "s|^[[:space:]]*source = \"git\\+https://github.com/([^/]+)/${repo}\\.git\\?rev=([0-9a-f]{40})#([0-9a-f]{40})\"[[:space:]]*\$|\\1 \\2 \\3|" |
      awk -v repository_org="$repository_org" '
        NF != 3 || $1 != repository_org || $2 != $3 { bad=1; next }
        { seen[$2]=1 }
        END {
          for (rev in seen) { count += 1; only = rev }
          if (!bad && count == 1) print only
          else exit 1
        }
      '
  )"; then
    echo "soundness_check.sh: dependency authority: ${relative_lock} must contain one exact ${repo} Git revision owned by ${repository_org}" >&2
    return 1
  fi
  printf '%s\n' "$parsed_rev"
}

candidate_dependency_rev() {
  # Resolve one exact first-party Git revision across EVERY Cargo root that can
  # resolve that repository independently. A coherent root Cargo.lock is not
  # enough: the rustc backend and fuzz crates carry standalone lockfiles, and a
  # stale one silently builds a second TrustIR/Clean/AY type universe.
  local repo="$1"
  local repository_org lock_paths relative_lock rev lock_revs parsed_rev

  if ! repository_org="$(candidate_repository_org)"; then
    echo INVALID
    return 1
  fi
  if ! printf '%s\n' "$repository_org" | grep -Eq '^[A-Za-z0-9][A-Za-z0-9_.-]*$'; then
    echo INVALID
    return 1
  fi
  if ! lock_paths="$(candidate_dependency_lock_paths "$repo")"; then
    echo "soundness_check.sh: dependency authority: unknown repository ${repo}" >&2
    echo INVALID
    return 1
  fi

  lock_revs=""
  while IFS= read -r relative_lock; do
    [ -n "$relative_lock" ] || continue
    if ! rev="$(dependency_rev_from_lock "$repo" "$relative_lock" "$repository_org")"; then
      echo INVALID
      return 1
    fi
    lock_revs="${lock_revs}${relative_lock}:${rev}"$'\n'
  done <<<"$lock_paths"

  if ! parsed_rev="$(
    printf '%s' "$lock_revs" |
      awk -F: '
        NF != 2 || $1 == "" || $2 !~ /^[0-9a-f]{40}$/ { bad=1; next }
        { rows += 1; seen[$2]=1 }
        END {
          for (rev in seen) { count += 1; only = rev }
          if (!bad && rows > 0 && count == 1) print only
          else exit 1
        }
      '
  )"; then
    echo "soundness_check.sh: dependency authority: split first-party ${repo} revisions: $(printf '%s' "$lock_revs" | tr '\n' ' ')" >&2
    echo INVALID
    return 1
  fi
  printf '%s\n' "$parsed_rev"
}

validate_candidate_dependency_locks() {
  local trust_ir_rev clean_rev ay_rev
  trust_ir_rev="$(candidate_dependency_rev trust-ir)" || return 1
  clean_rev="$(candidate_dependency_rev clean)" || return 1
  ay_rev="$(candidate_dependency_rev ay)" || return 1
  printf '%s\n' \
    "trust_ir_rev=${trust_ir_rev}" \
    "clean_rev=${clean_rev}" \
    "ay_rev=${ay_rev}"
}

if [ "$MODE_VALIDATE_DEPENDENCY_LOCKS" -eq 1 ]; then
  validate_candidate_dependency_locks
  exit $?
fi

isolate_git_repository_environment() {
  # Git hooks export repository-local variables which override even `git -C`.
  # Use Git's own inventory (not a fixed, incomplete list), as prescribed by
  # https://git-scm.com/docs/githooks . Clear them in this process so Cargo's
  # descendant Git commands also select their own repositories. User/global
  # configuration and credentials outside that repository-local inventory stay.
  local names name
  if ! names="$(git rev-parse --local-env-vars)" || [ -z "$names" ]; then
    echo "soundness_check.sh: cannot enumerate Git repository-local environment" >&2
    return 1
  fi
  while IFS= read -r name; do
    if ! [[ "$name" =~ ^GIT_[A-Z0-9_]+$ ]]; then
      echo "soundness_check.sh: invalid Git repository-local environment name" >&2
      return 1
    fi
    if ! unset "$name"; then
      echo "soundness_check.sh: cannot clear Git repository-local environment: $name" >&2
      return 1
    fi
  done <<<"$names"
}

isolate_git_repository_environment || exit 1

repo_head() {
  # Never turn a failed/partial Git query into a usable identity.
  local head
  head="$(git -C "$1" rev-parse --verify 'HEAD^{commit}')" || return 1
  [[ "$head" =~ ^[0-9a-f]{40}$ ]] || return 1
  printf '%s\n' "$head"
}

check_repo_worktree_clean() {
  # Shared by preflight and post-run checks: empty stdout on a failed status
  # query is NOT evidence of a clean worktree.
  local label="$1" dir="$2" head status
  if ! head="$(repo_head "$dir")"; then
    record "$label" FAIL "cannot read committed HEAD: $dir"
    return 1
  elif ! status="$(git -C "$dir" status --porcelain)"; then
    record "$label" FAIL "cannot query worktree status: $dir"
    return 1
  elif [ -n "$status" ]; then
    record "$label" FAIL "uncommitted files present; refusing to attest HEAD"
    return 1
  fi
  record "$label" PASS "clean HEAD $head"
}

# ----------------------------------------------------------------------------
# Gate runners. Each writes a temp log, inspects the REAL exit status (no pipe
# swallowing), and records PASS/FAIL. A nonzero rc, a compile error, or a
# missing target/file is always a FAIL — never a silent skip.
# ----------------------------------------------------------------------------

run_bounded() {
  # run_bounded <working-directory> <command> [args...]
  local dir="$1"
  shift
  # `"$SOUNDNESS_PYTHON3" -I`, not the runner's `#!/usr/bin/env python3` (the same PATH
  # python3): a script run without -I imports from the user site-packages
  # and runs its .pth files, and every python3 the gate starts is isolated
  # (OD-XHOST-GATE-CWD-20261025, repair round 2).
  "$SOUNDNESS_PYTHON3" -I "$TIMEOUT_RUNNER" --chdir "$dir" \
    "$SOUNDNESS_COMMAND_TIMEOUT_SECONDS" "$@"
}

run_clean_bounded() {
  # run_clean_bounded <command> [args...]
  #
  # Everything the Clean lane runs (its Cargo builds and tests, `clean check`)
  # runs in the Clean checkout under umask 077, so what it writes there is
  # private to this user. An attested run's Clean checkout is the pinned one
  # under SOUNDNESS_DEPS_DIR (<cache>/trust-cg/soundness-deps), and under the
  # caller's umask 0002 its target/ was written group-writable (X-HOST-P13
  # verification, 2026-10-03). The umask is set in a subshell, so the rest of
  # the gate keeps the caller's.
  (umask 077 && run_bounded "$CLEAN_DIR" "$@")
}

clean_gmp_cache_dir() {
  # The PRIVATE gmp-mpfr-sys artifact cache the Clean lane builds against
  # (OD-CLEAN-GMP-CACHE-20261020), or empty when none can be made.
  #
  # `gmp-mpfr-sys`'s build script copies `gmp.h` and `libgmp.a` out of a
  # shared cache with `fs::copy`, WHICH PRESERVES THE SOURCE MODE. Its default
  # is the user cache (`~/.cache/gmp-mpfr-sys`), measured on this host as
  # `drwxrwxr-x` holding `0664` artifacts from July and September: a directory
  # any member of the user's group can traverse and write. So the lane's
  # `umask 077` could not make those two files private — the mode came in with
  # the copy — and `require-private-tree` refused the checkout for them,
  # blocking the Clean binary rebuild and all 13 `clean-check` rows
  # (measured twice, 2026-10-20).
  #
  # That refusal was RIGHT, and not about a mode: artifacts another user may
  # have replaced get linked into the Clean binary that checks this gate's
  # proofs. Pointing the build at a cache this gate creates 0700 and judges
  # closes that path instead of papering over the mode. The cache lives beside
  # the pinned checkouts so it survives a checkout being removed and recreated.
  [ -n "$SOUNDNESS_DEPS_DIR" ] || return 1
  local cache="${SOUNDNESS_DEPS_DIR}/gmp-mpfr-sys-cache"
  "$SOUNDNESS_PYTHON3" -I "$PRIVATE_CACHE_TOOL" mkdir "$cache" >&2 || return 1
  # Judged before the build reads it: a cache that is not private refuses the
  # lane rather than seeding it.
  private_tree_path "$cache"
}

run_clean_cargo_bounded() {
  # run_clean_cargo_bounded <cargo-verb> [args...]
  #
  # Clean builds with the same Trust toolchain as every other leg. Its target
  # directory is its own; the TRUST_CG_*/TCG_* controls this gate exports are
  # kept out of trustc's environment by the wrapper.
  #
  # GMP_MPFR_SYS_CACHE names this gate's own private cache
  # ([`clean_gmp_cache_dir`]). When no private cache can be made the value is
  # `_`, which that build script reads as NO CACHE: it then builds gmp from
  # the vendored source inside the private checkout, under this lane's
  # umask 077. Either way nothing is copied in from a directory another user
  # can write.
  local gmp_cache
  if ! gmp_cache="$(clean_gmp_cache_dir)" || [ -z "$gmp_cache" ]; then
    gmp_cache="_"
  fi
  run_clean_bounded \
    env CARGO_TARGET_DIR="$CLEAN_DIR/target" \
    GMP_MPFR_SYS_CACHE="$gmp_cache" \
    "$TRUST_CARGO" "$@"
}

validate_clean_check_summary() {
  # validate_clean_check_summary <captured-clean-check-log>
  #
  # A successful process status is insufficient evidence: Clean must report
  # exactly one non-empty, internally coherent declaration summary. Keep this
  # parser pure so the focused self-test exercises the production guard.
  local log="$1"
  if [ ! -f "$log" ]; then
    echo "invalid Clean summary: missing log: $log"
    return 1
  fi

  awk '
    /^Checked [0-9][0-9]* declarations( in [^[:space:]][^[:space:]]*)?$/ {
      checked_rows += 1
      declarations = $2 + 0
    }
    /^[[:space:]]*[0-9][0-9]* passed, [0-9][0-9]* failed$/ {
      result_rows += 1
      passed = $1 + 0
      failed = $3 + 0
    }
    END {
      if (checked_rows != 1) {
        printf "invalid Clean summary: expected exactly one Checked row, found %d\n",
          checked_rows
        exit 1
      }
      if (result_rows != 1) {
        printf "invalid Clean summary: expected exactly one result row, found %d\n",
          result_rows
        exit 1
      }
      if (declarations <= 0) {
        print "invalid Clean summary: declaration count must be greater than zero"
        exit 1
      }
      if (passed <= 0) {
        print "invalid Clean summary: passed count must be greater than zero"
        exit 1
      }
      if (failed != 0) {
        printf "invalid Clean summary: failed count must be zero, found %d\n", failed
        exit 1
      }
      if (declarations != passed + failed) {
        printf \
          "invalid Clean summary: declarations (%d) != passed + failed (%d)\n",
          declarations, passed + failed
        exit 1
      }
      printf "Checked %d declarations; %d passed, %d failed\n",
        declarations, passed, failed
    }
  ' "$log"
}

if [ -n "$MODE_VALIDATE_CLEAN_SUMMARY" ]; then
  validate_clean_check_summary "$MODE_VALIDATE_CLEAN_SUMMARY"
  exit $?
fi

LOGDIR="$(mktemp -d "${TMPDIR:-/tmp}/soundness_check.XXXXXX")"
LEGS_TSV="${LOGDIR}/legs.tsv"
: >"$LEGS_TSV"

# 1 when this host executes x86-64 natively (set by the preflight probe).
HOST_NATIVE_X86_64=0
leg_class_runs_here() {
  # leg_class_runs_here <host-independent|x86_64-native>: whether this run
  # executes legs of that class itself. The Cargo-inventory self-test exercises
  # every dispatch argv and runs on any host.
  case "$1" in
    host-independent) scope_has_host_independent ;;
    x86_64-native) [ "$MODE_SELF_TEST_CARGO_GATES" -eq 1 ] ||
                     { [ "$HOST_NATIVE_X86_64" = 1 ] && [ "$RUN_SCOPE" != portable ]; } ;;
    *) return 1 ;;
  esac
}

run_cargo_gate() {
  # run_cargo_gate <repo_dir> <pkg> <target_or_filter> [repo|clean] [integration|lib]
  #                [host-independent|x86_64-native] [features]
  # An x86_64-native gate runs only where this host executes x86-64 natively;
  # elsewhere it records nothing here and the dispatched x86-64 record carries it.
  local dir="$1" pkg="$2" target="$3"
  local cargo_lane="${4:-repo}"
  local selector_kind="${5:-integration}"
  local host_class="${6:-host-independent}"
  local features="${7:-}"
  local gate_name="$target"
  local log="${LOGDIR}/cargo_${pkg}_${selector_kind}_${target}${features:+_features_$features}.log"
  local selection=()
  local rc summary
  local -a cargo_args=(test --locked -p "$pkg")
  local -a parser_args=(--require-unfiltered)
  leg_class_runs_here "$host_class" || return 0
  case "$selector_kind" in
    integration)
      # trust-cg-verify targets keep their bare names (TRUST_CG_GATES); any other
      # package's target is named with its package, so two packages' targets of
      # one name (must_refuse_corpus) are two distinct legs.
      [ "$pkg" = trust-cg-verify ] || gate_name="$pkg --test $target"
      cargo_args+=(--test "$target")
      ;;
    lib)
      gate_name="$pkg --lib $target"
      if [ -z "$target" ]; then
        record "$gate_name" FAIL "empty library-test filter"
        return 1
      fi
      cargo_args+=(--lib "$target")
      parser_args=(--allow-filtered)
      ;;
    *)
      record "$gate_name" FAIL "unknown Cargo test selector: $selector_kind"
      return 1
      ;;
  esac
  if [ -n "$features" ]; then
    gate_name+=" --features $features"
    cargo_args+=(--features "$features")
  fi
  release_include_ignored=0
  if [ "$pkg" = trust-cg-verify ]; then
    for release_gate in "${TRUST_CG_RELEASE_INCLUDE_IGNORED_GATES[@]}"; do
      if [ "$target" = "$release_gate" ]; then release_include_ignored=1; break; fi
    done
  fi
  if [ "$release_include_ignored" -eq 1 ]; then
    cargo_args+=(--release -- --show-output --include-ignored)
  else
    cargo_args+=(-- --show-output)
    [ "$selector_kind" != lib ] || cargo_args+=(--test-threads=1)
  fi
  case "$cargo_lane" in
    repo)
      if [ "$pkg" = trust-cg-codegen ] && [ "$target" = aarch64_elf_symbol_binding ]; then
        # The native Linux module must exercise every original linker leg.
        # trust_cargo.sh passes these controls to tests, never the compiler.
        TCG_REQUIRE_GOLD=1 TCG_REQUIRE_LLD=1 run_bounded "$dir" \
          "$TRUST_CARGO" "${cargo_args[@]}" >"$log" 2>&1
      elif [ "$pkg" = trust-cg-llvm-import ] && [ "$target" = c_string_escapes_e2e ]; then
        TCG_REQUIRE_LLC=1 TCG_REQUIRE_GOLD=1 TCG_REQUIRE_LLD=1 run_bounded "$dir" \
          "$TRUST_CARGO" "${cargo_args[@]}" >"$log" 2>&1
      else
        run_bounded "$dir" \
          "$TRUST_CARGO" "${cargo_args[@]}" >"$log" 2>&1
      fi
      ;;
    clean)
      run_clean_cargo_bounded \
        "${cargo_args[@]}" >"$log" 2>&1
      ;;
    *)
      record "$gate_name" FAIL "unknown cargo lane: $cargo_lane"
      return 1
      ;;
  esac
  rc=$?
  # Reuse the matrix's named-result/captured-output parser. In particular,
  # rc=0 plus a final rollup cannot conceal an ignored case, a runtime SKIP,
  # or an earlier incomplete suite. A failing test is not a compile error
  # merely because Cargo ends its output with "error: test failed".
  if summary="$("$SOUNDNESS_PYTHON3" -I "$TRUST_CG_DIR/scripts/matrix_results.py" \
      check-cargo-gate "$log" "$rc" "${parser_args[@]}" 2>&1)"; then
    record "$gate_name" PASS "$summary" "$log"
    return 0
  fi
  record "$gate_name" FAIL "${summary:-result parser failed without a diagnostic} — see $log" "$log"
  return 1
}

run_trust_cg_cargo_gates() {
  local gate class
  for gate in "${TRUST_CG_GATES[@]}"; do
    class=host-independent
    ! is_x86_native_gate "$gate" || class=x86_64-native
    run_cargo_gate "$TRUST_CG_DIR" trust-cg-verify "$gate" repo integration "$class"
  done
  leg_class_runs_here host-independent || return 0
  for gate in "${TRUST_CG_LIB_GATES[@]}"; do
    run_cargo_gate "$TRUST_CG_DIR" "${gate%%|*}" "${gate#*|}" repo lib
  done
  run_cargo_gate "$TRUST_CG_DIR" trust-cg-lower lattice_guard::tests:: repo lib host-independent lattice-guard-elision
  run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen a64_lattice_guard_elision_differential repo integration host-independent lattice-guard-elision
  run_cargo_gate "$TRUST_CG_DIR" trust-cg-lower refine_erasure_hazards repo integration host-independent
  run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen a64_refine_byte_invariance repo integration host-independent
  run_cargo_gate "$TRUST_CG_DIR" trust-cg-llvm-import c_string_escapes_e2e repo integration host-independent driver
  for gate in "${TRUST_CG_PACKAGE_INTEGRATION_GATES[@]}"; do
    run_cargo_gate "$TRUST_CG_DIR" "${gate%%|*}" "${gate#*|}" repo integration host-independent
  done
}

if [ "$MODE_SELF_TEST_CARGO_GATES" -eq 1 ]; then
  echo "Focused Cargo inventory only: no cross-repository preflight; NOT an attestation record."
  run_trust_cg_cargo_gates
  [ "$FAIL_COUNT" -eq 0 ]
  exit $?
fi

build_clean_binary() {
  local log="${LOGDIR}/clean_release_build.log"
  local rc
  # Match the checker capability enabled by aterm's Clean package recipe.
  # This development build must not replace a capable local binary with the
  # featureless default while checking unrelated Lean proof files.
  run_clean_cargo_bounded \
    build --locked --release -p clean --bin clean \
      --features clean/carcara-verify >"$log" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ] || [ ! -x "$CLEAN_BIN" ]; then
    if [ "$rc" -eq 124 ]; then
      record "Clean release binary matches checkout" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $log" "$log"
    else
      record "Clean release binary matches checkout" FAIL \
        "build failed or binary missing (rc=$rc) — see $log" "$log"
    fi
    return 1
  fi
  # A pinned checkout lives below the user cache (pin_dependency_checkout):
  # its binary runs only if no other user can replace it or rename an entry
  # above it, and every later leg runs exactly the canonical path that check
  # judged (private_path), never the name it was reached by. The whole tree
  # the build wrote (target/, the binary) is judged again first, as the
  # checkout was before the build: nothing in it, the sources Clean reads
  # and the proofs it checks included, can then be changed by another user
  # for the rest of the run. An explicit CLEAN_DIR (refused under --attest)
  # is the caller's.
  local checked tree
  if [ -z "$CLEAN_DIR_EXPLICIT" ]; then
    if ! tree="$(private_tree_path "$CLEAN_DIR")"; then
      record "Clean release binary matches checkout" FAIL "not run: ${tree}" "$log"
      return 1
    fi
    if [ "$tree" != "$CLEAN_DIR" ]; then
      record "Clean release binary matches checkout" FAIL \
        "not run: the Clean checkout ${CLEAN_DIR} now resolves to ${tree}" "$log"
      return 1
    fi
    if ! checked="$(private_path "$CLEAN_BIN")"; then
      record "Clean release binary matches checkout" FAIL "not run: ${checked}" "$log"
      return 1
    fi
    CLEAN_BIN="$checked"
  fi
  record "Clean release binary matches checkout" PASS "$CLEAN_BIN" "$log"
  return 0
}

if [ "$MODE_SELF_TEST_CLEAN_CARGO_COMMAND" -eq 1 ]; then
  build_clean_binary
  run_cargo_gate "$CLEAN_DIR" clean-kernel micro_diversity_gate clean
  [ "$FAIL_COUNT" -eq 0 ]
  exit $?
fi

run_clean_check() {
  # run_clean_check <lean_stem>
  local stem="$1"
  local file="${CLEAN_DIR}/proofs/${stem}.lean"
  local log="${LOGDIR}/clean_check_${stem}.log"
  local rc tail_line summary
  if [ ! -x "$CLEAN_BIN" ]; then
    record "clean-check ${stem}" FAIL "clean binary missing/not executable: $CLEAN_BIN"
    return 1
  fi
  if [ ! -f "$file" ]; then
    record "clean-check ${stem}" FAIL "missing .lean file: $file"
    return 1
  fi
  run_clean_bounded "$CLEAN_BIN" check "$file" >"$log" 2>&1
  rc=$?
  tail_line="$(grep -E 'passed|failed|Checked' "$log" | tail -1)"
  if [ "$rc" -ne 0 ]; then
    if [ "$rc" -eq 124 ]; then
      record "clean-check ${stem}" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $log" "$log"
    else
      record "clean-check ${stem}" FAIL "${tail_line:-rc=$rc} — see $log" "$log"
    fi
    return 1
  fi
  if ! summary="$(validate_clean_check_summary "$log")"; then
    record "clean-check ${stem}" FAIL "$summary — see $log" "$log"
    return 1
  fi
  record "clean-check ${stem}" PASS "$summary" "$log"
  return 0
}

export_candidate_proofs() {
  # export_candidate_proofs: under --attest, makes CANDIDATE_PROOF_DIR a
  # private export of exactly the attested commit's proofs/ and formal/lean.
  # A census run keeps the working tree and changes nothing.
  #
  # The candidate checkout is read in place by everything else, and no rule
  # judges its privacy; a checkout made under umask 0002 is 0775 with 0664
  # files. Reading the proofs there let a co-group writer rewrite a proof
  # Clean rejects while the run was in progress, restore it after its check,
  # and turn a failing proof into `132 total 132 passed` and an attestation
  # record (X-HOST-P13 fifth closure audit). The export is written by
  # scripts/private_cache.py `export-commit` from the object store, by hash:
  # the commit START_TRUST_HEAD (the commit the record names) and every tree
  # and blob below proofs/ and formal/lean are read with `git cat-file
  # --batch`, with no system or global git configuration, no attributes, no
  # filters and no replace refs, and each is hashed again and must hash to
  # its name; the files are written owner-only into a fresh 0700 directory
  # below LOGDIR, read back, and every file's bytes must hash to its blob,
  # with no entry missing or extra. `git archive` ran the smudge filters and
  # attributes of the user's global git configuration, so a co-group writer
  # of ~/.gitconfig made the export hold a substitute proof and credited it
  # (X-HOST-P13 sixth closure audit). The export is then judged as a whole
  # tree with its canonical ancestors (private_tree_path): every entry, the
  # ancestors included, must be one no other user can change. Every later
  # check reads only that canonical tree. Anything else is refused:
  # CANDIDATE_PROOF_REFUSAL says why, and the legs that read the proofs
  # record FAIL without running.
  local dir tree out
  CANDIDATE_PROOF_REFUSAL=""
  [ "$MODE_ATTEST" -eq 1 ] || return 0
  if ! [[ "$START_TRUST_HEAD" =~ ^[0-9a-f]{40}$ ]]; then
    CANDIDATE_PROOF_REFUSAL="no attested commit to export (HEAD ${START_TRUST_HEAD:-unresolved})"
    return 1
  fi
  dir="${LOGDIR}/candidate-proofs"
  if ! out="$("$SOUNDNESS_PYTHON3" -I "$PRIVATE_CACHE_TOOL" export-commit "$TRUST_CG_DIR" "$START_TRUST_HEAD" "$dir" \
                proofs "$LEAN_FORMAL_SUBDIR" 2>&1)"; then
    CANDIDATE_PROOF_REFUSAL="cannot export proofs/ and ${LEAN_FORMAL_SUBDIR} of ${START_TRUST_HEAD}: ${out}"
    return 1
  fi
  if ! tree="$(private_tree_path "$dir")"; then
    CANDIDATE_PROOF_REFUSAL="the export of ${START_TRUST_HEAD} is not private: ${tree} (point TMPDIR at a directory only you can write)"
    return 1
  fi
  CANDIDATE_PROOF_DIR="$tree"
  CANDIDATE_PROOF_SOURCE="a private export of ${START_TRUST_HEAD} (${tree})"
  return 0
}

check_trust_cg_proof_inventory() {
  # Every proofs/*.lean file of the candidate (CANDIDATE_PROOF_DIR) must be
  # named in TRUST_CG_LEAN.
  # A listed stem with no file fails in run_trust_cg_clean_check; this is the
  # converse: a proof file the gate never checks would be unenforced text.
  local name="trust-cg proofs/*.lean inventory"
  local path stem f listed
  local unlisted=""
  for path in "${CANDIDATE_PROOF_DIR}/proofs/"*.lean; do
    [ -e "$path" ] || continue
    stem="$(basename "$path" .lean)"
    listed=0
    for f in "${TRUST_CG_LEAN[@]}"; do
      [ "$f" != "$stem" ] || listed=1
    done
    [ "$listed" -eq 1 ] || unlisted="${unlisted:+$unlisted }$stem"
  done
  if [ -n "$unlisted" ]; then
    record "$name" FAIL \
      "unlisted proof file(s) this gate would never check: $unlisted — add each to TRUST_CG_LEAN"
    return 1
  fi
  record "$name" PASS "${#TRUST_CG_LEAN[@]} listed; no unlisted proofs/*.lean file in ${CANDIDATE_PROOF_SOURCE}"
  return 0
}

run_trust_cg_clean_check() {
  # run_trust_cg_clean_check <lean_stem>
  # Clean-checks trust-cg's OWN proofs/<stem>.lean with the Clean checkout's
  # release binary. The Rust weld tests re-encode these specs by hand, so an
  # unchecked spec is unenforced text. A missing proof file is a FAIL (checked
  # before the checker, so an absent checker can never hide a deleted proof);
  # a rejected or incoherent check is a FAIL; an absent checker is a loud SKIP
  # (recorded, counted, nonzero overall) — never a silent pass. The file is
  # read from CANDIDATE_PROOF_DIR (under --attest, the private export of the
  # attested commit; export_candidate_proofs), and Clean runs there under
  # umask 077, so nothing it writes is open to another user either.
  local stem="$1"
  local file="${CANDIDATE_PROOF_DIR}/proofs/${stem}.lean"
  local log="${LOGDIR}/trust_cg_clean_check_${stem}.log"
  local name="clean-check trust-cg proofs/${stem}"
  local rc tail_line summary
  if [ ! -f "$file" ]; then
    record "$name" FAIL "missing .lean file: $file"
    return 1
  fi
  if [ ! -x "$CLEAN_BIN" ]; then
    record "$name" SKIP "clean checker absent: $CLEAN_BIN — proof NOT checked"
    return 1
  fi
  (umask 077 && run_bounded "$CANDIDATE_PROOF_DIR" "$CLEAN_BIN" check "$file") >"$log" 2>&1
  rc=$?
  tail_line="$(grep -E 'passed|failed|Checked' "$log" | tail -1)"
  if [ "$rc" -ne 0 ]; then
    if [ "$rc" -eq 124 ]; then
      record "$name" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $log" "$log"
    else
      record "$name" FAIL "${tail_line:-rc=$rc} — see $log" "$log"
    fi
    return 1
  fi
  if ! summary="$(validate_clean_check_summary "$log")"; then
    record "$name" FAIL "$summary — see $log" "$log"
    return 1
  fi
  record "$name" PASS "$summary" "$log"
  return 0
}

run_x86_icmp_certificate_gate() {
  # The x86-64 vector-compare certificates (trust-ir docs/dialects.md, the
  # per-cell rule's ground (b)): scripts/check_x86_icmp_certificates.py reads
  # trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE from the compiled trust-ir (the
  # query dump), builds (or reuses, cached per revision) the rule's AY, which
  # must be the AY the candidate's Cargo.lock pins, and the rule's Clean, each
  # exported by revision from the gate's own worktrees' object store and built
  # under the rule's Clean's heavy_gate, regenerates every cell's query from the
  # code and re-runs the certificate on each. Exit 3 is its explicit skip of a
  # MISSING input only, requested here by SOUNDNESS_SKIP_X86_ICMP_CERTIFICATES;
  # it records a SKIP, which leaves the run incomplete and nonzero. A wrong
  # input (another AY pin, a changed cached binary, a changed query) always
  # fails.
  local name="x86 icmp certificates (pinned AY + the rule's Clean)"
  local log="${LOGDIR}/x86-icmp-certificates.log"
  local report="${LOGDIR}/x86-icmp-certificates.json"
  local -a args=(--ay-source "$AY_DIR" --clean-source "$CLEAN_DIR" --json-out "$report")
  local rc summary
  [ -z "${SOUNDNESS_SKIP_X86_ICMP_CERTIFICATES:-}" ] || args+=(--skip-missing-toolchain)
  run_bounded "$TRUST_CG_DIR" "$SOUNDNESS_PYTHON3" -I "${TRUST_CG_DIR}/scripts/check_x86_icmp_certificates.py" \
    "${args[@]}" >"$log" 2>&1
  rc=$?
  summary="$(grep -E '^\[x86-icmp-certificates\] (PASS|FAIL|MISSING|SKIPPED)' "$log" | head -3 | tr '\n' ' ')"
  case "$rc" in
    0) record "$name" PASS "${summary:-certificates re-run}" "$log" ;;
    3) record "$name" SKIP "explicitly skipped (SOUNDNESS_SKIP_X86_ICMP_CERTIFICATES): ${summary:-an input is missing} — certificates NOT re-run" "$log" ;;
    *) record "$name" FAIL "rc=${rc}: ${summary:-see $log}" "$log" ;;
  esac
}

run_lean_formal_gate() {
  # run_lean_formal_gate : build the Lean forward-sim (ENC-1) and pin sorry/axiom counts.
  #   1. `lake build` must be green (a build/compile error is a FAIL, never a skip).
  #   2. classified-sorry count == BASELINE_LEAN_SORRY (growth => fail closed).
  #   3. explicit top-level axiom count == BASELINE_LEAN_AXIOM (a NEW axiom => fail closed).
  #   4. the environment audit: no declaration depends on sorryAx (however it was
  #      written) or on an axiom beyond the standard three and bv_decide's native
  #      ones, and the capstone on the standard three only.
  # It reads formal/lean below CANDIDATE_PROOF_DIR (under --attest, the
  # private export of the attested commit; export_candidate_proofs) and does
  # not run when that export was refused. `lake build` runs under umask 077:
  # it imports the .olean files it wrote earlier in the same build without
  # re-checking them, so none of them may be open to another user.
  local dir="${CANDIDATE_PROOF_DIR}/${LEAN_FORMAL_SUBDIR}"
  local log="${LOGDIR}/lean_formal_build.log"
  local audit_log="${LOGDIR}/lean_formal_axiom_audit.log"
  local rc sc ac
  if [ -n "$CANDIDATE_PROOF_REFUSAL" ]; then
    record "formal/lean lake build" FAIL "not run: ${CANDIDATE_PROOF_REFUSAL}"
    return 1
  fi
  if ! command -v lake >/dev/null 2>&1; then
    record "formal/lean lake build" FAIL "lake not on PATH (need elan: export PATH=\$HOME/.elan/bin:\$PATH)"
    return 1
  fi
  if [ ! -f "${dir}/lakefile.lean" ]; then
    record "formal/lean lake build" FAIL "missing lakefile: ${dir}/lakefile.lean"
    return 1
  fi
  (umask 077 && run_bounded "$dir" lake build) >"$log" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ]; then
    if [ "$rc" -eq 124 ]; then
      record "formal/lean lake build" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $log" "$log"
    else
      record "formal/lean lake build" FAIL \
        "lake build rc=$rc (Lean forward-sim did not build) — see $log" "$log"
    fi
    return 1
  fi
  record "formal/lean lake build" PASS "green (compile_refines capstone builds)" "$log"

  # Sorry ratchet (pinned EXACTLY at baseline).
  sc="$(grep -rEc '^[[:space:]]*sorry\b' "${dir}/Trust" 2>/dev/null | awk -F: '{s+=$2} END{print s+0}')"
  if [ "$sc" -ne "$BASELINE_LEAN_SORRY" ]; then
    record "formal/lean sorry-count == ${BASELINE_LEAN_SORRY}" FAIL \
      "found ${sc} (baseline ${BASELINE_LEAN_SORRY}); growth fails closed — if a sorry was discharged, lower BASELINE_LEAN_SORRY" "$log"
  else
    record "formal/lean sorry-count == ${BASELINE_LEAN_SORRY}" PASS "${sc} classified sorries (pinned)" "$log"
  fi

  # Axiom ratchet (exactly BASELINE_LEAN_AXIOM explicit axioms). Counts every
  # line that declares one, indented or behind an attribute or modifier, so a
  # `private axiom` cannot slip past; a comment line of that shape also counts
  # (fails closed).
  ac="$(grep -rcE '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable|unsafe|partial)[[:space:]]+)*axiom[[:space:]]' "${dir}/Trust" 2>/dev/null | awk -F: '{s+=$2} END{print s+0}')"
  if [ "$ac" -ne "$BASELINE_LEAN_AXIOM" ]; then
    record "formal/lean axiom-count == ${BASELINE_LEAN_AXIOM}" FAIL \
      "found ${ac} top-level axioms (baseline ${BASELINE_LEAN_AXIOM}); a new axiom fails closed" "$log"
  else
    record "formal/lean axiom-count == ${BASELINE_LEAN_AXIOM}" PASS "${ac} explicit trusted axioms (pinned)" "$log"
  fi

  # Environment audit. Its PASS needs exit 0 AND the success line, so a
  # truncated or skipped run cannot pass.
  if [ ! -f "${dir}/scripts/AxiomAudit.lean" ]; then
    record "formal/lean axiom audit (no sorryAx, no project axiom)" FAIL \
      "missing ${dir}/scripts/AxiomAudit.lean" "$audit_log"
    return 1
  fi
  (umask 077 && run_bounded "$dir" lake env lean scripts/AxiomAudit.lean) >"$audit_log" 2>&1
  rc=$?
  if [ "$rc" -eq 0 ] && grep -Eq '^AXIOM-AUDIT declarations=[1-9][0-9]* sorryAx=0 project_axioms=0 ' "$audit_log"; then
    record "formal/lean axiom audit (no sorryAx, no project axiom)" PASS \
      "$(grep -E '^AXIOM-AUDIT ' "$audit_log" | head -n 1)" "$audit_log"
  else
    record "formal/lean axiom audit (no sorryAx, no project axiom)" FAIL \
      "rc=${rc}: $(grep -E 'AXIOM-AUDIT' "$audit_log" | head -n 1) — see $audit_log" "$audit_log"
  fi
}

run_wasm_oracle_gate() {
  # run_wasm_oracle_gate <gate-label> <example-name> [example-args...]
  #
  # One wasm offline oracle, two legs:
  #   emit — `targo --unverified run --example <example>` builds the trust-ir corpus, runs
  #          the trust-ir INTERPRETER over it (the operational semantics), and
  #          compiles it trust-ir→wasm, writing <out>.wasm + <out>.json
  #          expectations. Any compile_module error or interpreter failure is
  #          a panic = nonzero rc = FAIL. Missing/empty artifacts on rc=0 are
  #          a vacuity FAIL.
  #   node — the shared `wasm_difftest.mjs` instantiates the emitted wasm
  #          under node and replays every expectation bit-for-bit; ANY
  #          divergence exits nonzero = FAIL (a real miscompile — this oracle
  #          is how the gcd back-edge relooper bug surfaced).
  # node absent on PATH SKIPs the node leg with a loud recorded notice (never
  # a silent pass); the emit leg has no external runtime and ALWAYS runs.
  local label="$1" example="$2"
  shift 2
  local out="${LOGDIR}/${example}"
  local log="${LOGDIR}/${example}_emit.log"
  local nodelog="${LOGDIR}/${example}_node.log"
  local rc summary
  run_bounded "$TRUST_CG_DIR" \
    "$TRUST_CARGO" run --locked -p trust-cg-codegen --example "$example" -- "$out" "$@" \
    >"$log" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ]; then
    if [ "$rc" -eq 124 ]; then
      record "${label}: emit corpus" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $log" "$log"
    elif grep -qE '^error(\[|:)' "$log"; then
      record "${label}: emit corpus" FAIL "BUILD/COMPILE ERROR (rc=$rc) — see $log" "$log"
    else
      record "${label}: emit corpus" FAIL \
        "rc=$rc (compile_module or interpreter refused the corpus) — see $log" "$log"
    fi
    return 1
  fi
  summary="$(grep -E '^wrote ' "$log" | tail -1)"
  if [ -z "$summary" ] || [ ! -s "${out}.wasm" ] || [ ! -s "${out}.json" ]; then
    record "${label}: emit corpus" FAIL \
      "rc=0 but no 'wrote' line or ${out}.wasm/.json missing/empty (vacuous) — see $log" "$log"
    return 1
  fi
  record "${label}: emit corpus" PASS "$summary" "$log"

  if ! command -v node >/dev/null 2>&1; then
    record "${label}: node oracle" SKIP \
      "node not on PATH — the wasm-vs-interpreter differential DID NOT RUN; install Node.js"
    return 0
  fi
  if [ ! -f "$WASM_DIFFTEST_MJS" ]; then
    record "${label}: node oracle" FAIL "missing validator: $WASM_DIFFTEST_MJS"
    return 1
  fi
  run_bounded "$TRUST_CG_DIR" \
    node "$WASM_DIFFTEST_MJS" "${out}.wasm" "${out}.json" >"$nodelog" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ]; then
    if [ "$rc" -eq 124 ]; then
      record "${label}: node oracle" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $nodelog" "$nodelog"
    else
      record "${label}: node oracle" FAIL \
        "$(grep -E 'DIVERGE|MISSING|FAIL:' "$nodelog" | head -1) (rc=$rc) — see $nodelog" "$nodelog"
    fi
    return 1
  fi
  summary="$(grep -E 'differential checks agree' "$nodelog" | tail -1)"
  if [ -z "$summary" ]; then
    record "${label}: node oracle" FAIL \
      "rc=0 but NO agreement line (vacuous?) — see $nodelog" "$nodelog"
    return 1
  fi
  # Vacuity guard: zero executed checks must never read as agreement.
  if printf '%s' "$summary" | grep -qE '^0/0 '; then
    record "${label}: node oracle" FAIL "0 checks ran (vacuous) — see $nodelog" "$nodelog"
    return 1
  fi
  record "${label}: node oracle" PASS "$summary" "$nodelog"
  return 0
}

run_island_gate() {
  # run_island_gate <gate-label> <example-name> [generator-args...]
  #
  # The ISLANDS' three-way differential. The generators author one spec in
  # three spellings (trust-ir builder, an emitted rustc/LLVM twin SOURCE,
  # interpreter-checked expectations) but a generator run only exercises two
  # of them — it never compiles the twin and never RUNS either module. This
  # gate closes the loop: emit, then `wasm_island_differential.mjs` compiles
  # the emitted twin with rustc for wasm32, instantiates BOTH modules and
  # replays every baked expectation against both. Any divergence between the
  # two compilers or against the interpreter is a FAIL; an empty/torn
  # manifest is a vacuity FAIL. node or ISLAND_TWIN_RUSTC absent = loud SKIP.
  local label="$1" example="$2"
  shift 2
  local out="${LOGDIR}/${example}_island"
  local log="${LOGDIR}/${example}_island_emit.log"
  local difflog="${LOGDIR}/${example}_island_diff.log"
  local rc summary
  mkdir -p "$out"
  run_bounded "$TRUST_CG_DIR" \
    "$TRUST_CARGO" run --locked -p trust-cg-codegen --example "$example" -- "$@" "$out" \
    >"$log" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ]; then
    if [ "$rc" -eq 124 ]; then
      record "${label}: emit island" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $log" "$log"
    else
      record "${label}: emit island" FAIL \
        "rc=$rc (a generator guard, compile_module, or the interpreter refused) — see $log" "$log"
    fi
    return 1
  fi
  local wasm twin json
  wasm="$(ls "$out"/*.wasm 2>/dev/null | head -1)"
  twin="$(ls "$out"/*_twin.rs 2>/dev/null | head -1)"
  json="$(ls "$out"/*expected.json 2>/dev/null | head -1)"
  if [ ! -s "$wasm" ] || [ ! -s "$twin" ] || [ ! -s "$json" ]; then
    record "${label}: emit island" FAIL \
      "rc=0 but the wasm/twin/expectations trio is missing or empty (vacuous) — see $log" "$log"
    return 1
  fi
  record "${label}: emit island" PASS "$(tail -1 "$log")" "$log"

  if ! command -v node >/dev/null 2>&1; then
    record "${label}: three-way differential" SKIP \
      "node not on PATH — the island differential DID NOT RUN; install Node.js"
    return 0
  fi
  # STOCK EXCEPTION (Trust lacks a wasm32-unknown-unknown core/std; measured
  # `trustc --target wasm32-unknown-unknown` -> E0463 can't find crate for
  # `core`): the twin is compiled by the stock rustc named in ISLAND_TWIN_RUSTC,
  # for wasm32 only. It is never looked up on PATH and never used for the host.
  if [ -z "${ISLAND_TWIN_RUSTC:-}" ] || [ ! -x "${ISLAND_TWIN_RUSTC}" ]; then
    record "${label}: three-way differential" SKIP \
      "ISLAND_TWIN_RUSTC names no stock rustc with the wasm32-unknown-unknown target (Trust ships no wasm32 core/std) — the twin could not be built; the differential DID NOT RUN"
    return 0
  fi
  if [ ! -f "$WASM_ISLAND_MJS" ]; then
    record "${label}: three-way differential" FAIL "missing runner: $WASM_ISLAND_MJS"
    return 1
  fi
  run_bounded "$TRUST_CG_DIR" \
    node "$WASM_ISLAND_MJS" "$wasm" "$twin" "$json" >"$difflog" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ]; then
    if [ "$rc" -eq 124 ]; then
      record "${label}: three-way differential" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $difflog" "$difflog"
    else
      record "${label}: three-way differential" FAIL \
        "$(grep -E 'DIVERGE|FAIL:' "$difflog" | head -1) (rc=$rc) — see $difflog" "$difflog"
    fi
    return 1
  fi
  summary="$(grep -E 'island differential checks agree' "$difflog" | tail -1)"
  if [ -z "$summary" ]; then
    record "${label}: three-way differential" FAIL \
      "rc=0 but NO agreement line (vacuous?) — see $difflog" "$difflog"
    return 1
  fi
  record "${label}: three-way differential" PASS "$summary" "$difflog"
  return 0
}

run_island_gates() {
  run_island_gate "wasm canary island" wasm_canary_island
  # P2: the island that reads a HOST's memory. Both modules are handed ONE
  # imported memory object, so a twin that failed to import it (or an index
  # space that shifted under it) shows up as divergence, not silence.
  run_island_gate "wasm memhash island" wasm_memhash_island
  if [ -n "$ISLAND_VT_TABLES" ] && [ -s "$ISLAND_VT_TABLES" ]; then
    run_island_gate "wasm vt islands" wasm_vt_islands "$ISLAND_VT_TABLES"
  else
    record "wasm vt islands: three-way differential" SKIP \
      "no aterm tables dump (set ISLAND_VT_TABLES=<tables.json>) — the vt/wcwidth differential DID NOT RUN"
  fi
}

# ----------------------------------------------------------------------------
# Summary. finish_run is the only exit of a constellation run: the normal end,
# the fail-fast stop inside record() and a failed --attest preflight all call
# it, so every exit prints the same summary and only a green --attest run
# reaches attest_write_record.
# ----------------------------------------------------------------------------
STOPPED_AT=""
PREFLIGHT_OK=1
IMPORTED_RECORDS=()
RUN_STARTED_AT=""
START_TRUST_HEAD=""
REMOTE_PID=""
REMOTE_DIR=""

stop_remote_dispatch() {
  # The dispatched x86-64 run is abandoned when this run stops early.
  # It runs in its own process group (start_remote_dispatch): stop all of it.
  if [ -n "$REMOTE_PID" ]; then
    kill -TERM -- "-$REMOTE_PID" 2>/dev/null || kill -TERM "$REMOTE_PID" 2>/dev/null || :
    wait "$REMOTE_PID" 2>/dev/null || :
    REMOTE_PID=""
  fi
}

drop_staged_imports() {
  # A dispatched x86-64 record waits at refs/soundness/import/<C>/<triple>
  # until the record write publishes it; nothing else may keep it.
  local ref
  [ -n "$START_TRUST_HEAD" ] || return 0
  while read -r ref; do
    [ -n "$ref" ] && git -C "$TRUST_CG_DIR" update-ref -d "$ref" 2>/dev/null || :
  done < <(git -C "$TRUST_CG_DIR" for-each-ref --format='%(refname)' "refs/soundness/import/${START_TRUST_HEAD}/" 2>/dev/null)
}

attest_write_record() {
  # Build the record from this run's logs and write it as
  # refs/attest/soundness/<START_TRUST_HEAD>/<host-triple>. The tool re-checks
  # that the executed legs are exactly the declared inventory, all PASS, and
  # binds the executed AY and Clean binaries; any refusal is a failed run.
  local record_dir="${LOGDIR}/record" out item
  local -a build_args=(build --repo "$TRUST_CG_DIR" --commit "$START_TRUST_HEAD"
    --scope "$RUN_SCOPE" --logdir "$LOGDIR" --out "$record_dir"
    --started-at "$RUN_STARTED_AT" --finished-at "$(date -u +%Y-%m-%dT%H:%M:%SZ)")
  # Spelled out (not scope_has_host_independent): the summary block is
  # self-contained, and scripts/test_soundness_check.sh runs it extracted.
  if [ "$RUN_SCOPE" = full ] || [ "$RUN_SCOPE" = portable ]; then
    build_args+=(--clean-bin "$CLEAN_BIN" --aterm "${LOGDIR}/aterm.json")
  fi
  for item in ${IMPORTED_RECORDS[@]+"${IMPORTED_RECORDS[@]}"}; do
    build_args+=(--imported "$item")
  done
  section "Attestation record (local; nothing is pushed)"
  if ! "$SOUNDNESS_PYTHON3" -I "$ATTESTATION_TOOL" "${build_args[@]}"; then
    printf '%s%s refusing to write an attestation record (see above).%s\n' "$C_RED" "$C_BLD" "$C_RST"
    return 1
  fi
  if ! out="$("$SOUNDNESS_PYTHON3" -I "$ATTESTATION_TOOL" write --repo "$TRUST_CG_DIR" --record-dir "$record_dir")"; then
    printf '%s\n' "$out"
    printf '%s%s the attestation record was not written.%s\n' "$C_RED" "$C_BLD" "$C_RST"
    return 1
  fi
  printf '%s\n' "$out"
  printf '  share it with: python3 scripts/soundness_attestation.py push %s\n' "$START_TRUST_HEAD"
}

finish_run() {
  local i st total overall_rc=0
  # A record() made from here on never re-enters finish_run.
  RUN_PHASE=post
  FAIL_FAST=0
  stop_remote_dispatch
  section "SUMMARY"
  total=$((PASS_COUNT + FAIL_COUNT + SKIP_COUNT))
  for i in ${GATE_NAMES[@]+"${!GATE_NAMES[@]}"}; do
    st="${GATE_STATUS[$i]}"
    if [ "$st" = "PASS" ]; then
      printf '  %s[PASS]%s %s\n' "$C_GRN" "$C_RST" "${GATE_NAMES[$i]}"
    elif [ "$st" = "SKIP" ]; then
      printf '  %s[SKIP]%s %-46s %s\n' "$C_YEL" "$C_RST" "${GATE_NAMES[$i]}" "${GATE_DETAIL[$i]}"
    else
      printf '  %s[FAIL]%s %-46s %s\n' "$C_RED" "$C_RST" "${GATE_NAMES[$i]}" "${GATE_DETAIL[$i]}"
    fi
  done
  hr
  printf 'gates: %d total  %s%d passed%s  %s%d failed%s  %s%d skipped%s\n' \
    "$total" "$C_GRN" "$PASS_COUNT" "$C_RST" \
    "$( [ "$FAIL_COUNT" -gt 0 ] && printf '%s' "$C_RED" || printf '%s' "$C_GRN" )" \
    "$FAIL_COUNT" "$C_RST" \
    "$( [ "$SKIP_COUNT" -gt 0 ] && printf '%s' "$C_YEL" || printf '%s' "$C_GRN" )" \
    "$SKIP_COUNT" "$C_RST"
  if [ "$SKIP_COUNT" -gt 0 ]; then
    printf '%sNOTE: %d gate leg(s) SKIPPED (missing runtime or oracle input) — the constellation is NOT fully attested.%s\n' \
      "$C_YEL" "$SKIP_COUNT" "$C_RST"
  fi
  if [ -n "$STOPPED_AT" ]; then
    printf '%sSTOPPED at the first failure (%s): later legs did not run. Rerun with --keep-going for a full census.%s\n' \
      "$C_RED" "$STOPPED_AT" "$C_RST"
  fi
  if [ "$FAIL_COUNT" -gt 0 ] || [ "$SKIP_COUNT" -gt 0 ] || [ "$PREFLIGHT_OK" -ne 1 ] || [ -n "$STOPPED_AT" ]; then
    overall_rc=1
  fi
  if [ "$overall_rc" -eq 0 ] && [ "$MODE_PREFLIGHT_ONLY" -eq 1 ]; then
    printf '%s%s PREFLIGHT GREEN — no leg ran and no record was written (--preflight-only).%s\n' "$C_GRN" "$C_BLD" "$C_RST"
    exit 0
  elif [ "$overall_rc" -eq 0 ]; then
    printf '%s%s ALL SOUNDNESS GATES GREEN.%s\n' "$C_GRN" "$C_BLD" "$C_RST"
  elif [ "$FAIL_COUNT" -eq 0 ] && [ "$SKIP_COUNT" -gt 0 ] && [ "$PREFLIGHT_OK" -eq 1 ]; then
    printf '%s%s SOUNDNESS GATE INCOMPLETE — required checks skipped. Logs in %s%s\n' "$C_YEL" "$C_BLD" "$LOGDIR" "$C_RST"
  else
    printf '%s%s SOUNDNESS GATE FAILED OR INCOMPLETE — see [FAIL]/[SKIP] rows above. Logs in %s%s\n' "$C_RED" "$C_BLD" "$LOGDIR" "$C_RST"
  fi
  if [ "$MODE_ATTEST" -eq 1 ]; then
    if [ "$overall_rc" -ne 0 ]; then
      echo "  no attestation record: the run failed or was incomplete. Resolve every FAIL and SKIP first."
    elif ! attest_write_record; then
      overall_rc=1
    fi
    drop_staged_imports
  fi
  exit "$overall_rc"
}
# End of summary.

# Single-gate lane: run ONLY the wasm offline oracles and exit by their status
# (same runners, same fail-closed/SKIP semantics as the full constellation).
if [ "$MODE_RUN_WASM_ORACLES" -eq 1 ]; then
  section "trust-cg wasm offline oracles (difftest + reducible-CFG fuzz)"
  run_wasm_oracle_gate "wasm difftest" wasm_difftest
  run_wasm_oracle_gate "wasm cfg-fuzz" wasm_cfg_fuzz "$WASM_CFG_FUZZ_FUNCS"
  section "trust-cg wasm islands (three-way: trust-cg vs rustc/LLVM vs interpreter)"
  run_island_gates
  hr
  printf 'wasm oracles: %d passed  %d failed  %d skipped\n' \
    "$PASS_COUNT" "$FAIL_COUNT" "$SKIP_COUNT"
  if [ "$SKIP_COUNT" -gt 0 ]; then
    printf '%sNOTE: %d leg(s) SKIPPED (missing runtime or oracle input) — the oracle did NOT fully run.%s\n' \
      "$C_YEL" "$SKIP_COUNT" "$C_RST"
  fi
  [ "$FAIL_COUNT" -eq 0 ] && [ "$SKIP_COUNT" -eq 0 ] || exit 1
  exit 0
fi

# ----------------------------------------------------------------------------
# Banner + preflight.
# ----------------------------------------------------------------------------
RUN_STARTED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
[ "$MODE_ATTEST" -ne 1 ] || [ "$MODE_KEEP_GOING" -eq 1 ] || FAIL_FAST=1
printf '%s%s%s\n' "$C_BLD" "==================== LOCAL SOUNDNESS META-GATE (#4) =====================" "$C_RST"
echo "trust-cg : $TRUST_CG_DIR"
echo "clean    : $CLEAN_DIR"
echo "ay       : $AY_DIR"
echo "logs     : $LOGDIR"
echo "timeout  : ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s per Cargo/Clean/Lake command"
echo "mode     : $( [ "$MODE_ATTEST" -eq 1 ] && echo 'ATTEST (committed HEAD; record on green)' || echo 'census (no record)' )$( [ "$FAIL_FAST" -eq 1 ] && echo ', stop at the first failure' )$( [ "$MODE_PREFLIGHT_ONLY" -eq 1 ] && echo ', preflight only' ); scope ${RUN_SCOPE}"
echo "NOTE     : this is a LOCAL meta-gate, NOT GitHub CI."

# Preflight: tooling must exist, or this whole gate is vacuous. Every preflight
# row is recorded before a --attest run stops, so one run names all of them.
section "Preflight"
PREFLIGHT_OK=1
# The host trust boundary passed before anything ran (a refusal stopped the
# run there); its report is kept with the logs.
if [ "$MODE_ATTEST" -eq 1 ]; then
  printf '%s\n' "$HOST_BOUNDARY_REPORT" >"${LOGDIR}/host-boundary.log"
  record "preflight: host trust boundary" PASS "${HOST_BOUNDARY_REPORT##*$'\n'}" "${LOGDIR}/host-boundary.log"
fi
# The declared inventory this run is judged against, recorded with its logs.
soundness_leg_inventory_json >"${LOGDIR}/inventory.json" || PREFLIGHT_OK=0

# The environment allowlist (scripts/soundness_attestation.py check-env). An
# --attest run was re-executed with only the allowlisted variables (top of
# this file); a variable outside the list, a leg-affecting variable the caller
# set, or an uncommitted Cargo configuration file fails this row. A census run
# only reports what --attest would refuse.
settings_args=(check-env --checkout "$(CDPATH= cd -- "${soundness_self_dir}/.." && pwd)"
  --out "${LOGDIR}/environment.json" --effective "WASM_CFG_FUZZ_FUNCS=${WASM_CFG_FUZZ_FUNCS}"
  --effective "SOUNDNESS_COMMAND_TIMEOUT_SECONDS=${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}"
  --effective "SOUNDNESS_X86_HOST=${SOUNDNESS_X86_HOST}" --effective "ATERM_DIR=${ATERM_DIR}"
  --effective "CLEAN_SOURCE_DIR=${CLEAN_SOURCE_DIR}" --effective "AY_SOURCE_DIR=${AY_SOURCE_DIR}"
  --effective "SOUNDNESS_DEPS_DIR=${SOUNDNESS_DEPS_DIR}"
  --effective "ISLAND_TWIN_RUSTC=${ISLAND_TWIN_RUSTC:-}"
  --cargo-root "$TRUST_CG_DIR" --cargo-root "$SOUNDNESS_DEPS_DIR")
[ "$MODE_ATTEST" -eq 1 ] || settings_args+=(--caller)
for soundness_setting in ${SOUNDNESS_EXPLICIT_SETTINGS[@]+"${SOUNDNESS_EXPLICIT_SETTINGS[@]}"}; do
  settings_args+=(--explicit "$soundness_setting")
done
if settings_out="$("$SOUNDNESS_PYTHON3" -I "$ATTESTATION_TOOL" "${settings_args[@]}" 2>&1)"; then
  settings_rc=0
else
  settings_rc=$?
fi
if [ "$MODE_ATTEST" -eq 1 ]; then
  if [ "$settings_rc" -eq 0 ]; then
    record "preflight: leg-weakening settings" PASS "$settings_out" "${LOGDIR}/environment.json"
  else
    record "preflight: leg-weakening settings" FAIL "$settings_out" "${LOGDIR}/environment.json"
    PREFLIGHT_OK=0
  fi
elif [ "$settings_rc" -ne 0 ]; then
  printf '  %sNOTE%s census run; --attest would refuse: %s\n' "$C_YEL" "$C_RST" "$settings_out"
fi

# Pinned dependency checkouts. The proof gates must run against the Clean and
# AY revisions the candidate's Cargo locks name. The $HOME checkouts are other
# workers' trees, left wherever those workers left them, so requiring them to
# sit at the candidate revisions failed every attestation from a shared
# machine (2026-09-27). Unless CLEAN_DIR / AY_DIR is set, the gate adds (or
# reuses) a detached worktree of each source repository at exactly the
# candidate revision, one per revision under SOUNDNESS_DEPS_DIR, fetching the
# revision first if the source repository lacks it. The checks below then
# read those checkouts exactly as they read an explicit CLEAN_DIR / AY_DIR.
#
# SOUNDNESS_DEPS_DIR sits under <cache>/trust-cg by default, the directory
# AY's private copy lives under; AY is refused while that directory (or any
# ancestor) is group-writable. So every directory created there is 0700
# whatever the umask (scripts/private_cache.py; under umask 0002 a plain
# `mkdir -p` made <cache>/trust-cg 0775 and refused AY in every later process,
# X-HOST-P13), the checkout is written under umask 077, the Clean lane builds
# and checks in it under umask 077 (run_clean_bounded), and an existing
# directory is never changed.
#
# The Clean checker the attestation credits is built and run from below
# SOUNDNESS_DEPS_DIR, so an existing directory there that another user could
# rename entries in is refused, never repaired, by the rule the icmp gate
# holds its AY cache to (scripts/private_cache.py `require-private`): the
# dependency directory before anything is written into it, the WHOLE checkout
# before it is used (`require-private-tree`: every directory and file in it,
# since Clean is built from its sources and checks its proofs in place, with
# no POSIX ACL, and no directory a default ACL, that lets anyone else write:
# a default ACL would open what the build creates there whatever the umask;
# X-HOST-P13 round-4 verifier, LD-75 repair), the
# whole checkout again after the build (its target/ included), and the Clean
# binary before it runs. A checkout with any entry another user could write
# is refused with the remedy to remove it (it is then re-created private):
# a chmod cannot undo what another user may already have written there. That
# rule judges CANONICAL paths, so each check's canonical path (private_path)
# is the one used from then on: the checkout is added below the canonical
# dependency directory, the printed checkout is canonical (CLEAN_DIR / AY_DIR),
# and the Clean legs run the canonical binary (build_clean_binary). A
# SOUNDNESS_DEPS_DIR or XDG_CACHE_HOME reached through a symlink in a
# directory others can write is therefore used only where it led at the
# check: re-pointing the symlink afterwards changes nothing the gate runs or
# credits (X-HOST-P13 third closure audit, where 13 of 14 clean-check legs ran
# another program through such a link).
pin_dependency_checkout() {
  # pin_dependency_checkout <label> <source repo> <40-hex revision>: prints
  # the checkout's canonical path; on a privacy refusal prints
  # `refused: <why>` and fails.
  local label="$1" src="$2" rev="$3" deps dir
  [[ "$rev" =~ ^[0-9a-f]{40}$ ]] || return 1
  if [ -z "$SOUNDNESS_DEPS_DIR" ]; then
    printf 'refused: SOUNDNESS_DEPS_DIR has no default: %s\n' "$SOUNDNESS_DEPS_DIR_REFUSAL"
    return 1
  fi
  if ! git -C "$src" cat-file -e "${rev}^{commit}" 2>/dev/null; then
    # The fetch names `origin`, so the source's own configuration must define
    # it: its remote.origin.url is a location the host trust boundary judged
    # (a local repository named there is judged as one). For a name the
    # configuration does not define, git reads a legacy remotes/ or branches/
    # file (the boundary refuses one) or uses the name itself as a path in its
    # working directory, which is no remote location the boundary judged.
    # Fetch only the locked raw commit through native agh on GitHub (which
    # judges the original source config), or a literal local repository. Both
    # routes disable submodule recursion; no GitHub raw-Git fallback exists.
    if [ -z "$(git -C "$src" config --get remote.origin.url 2>/dev/null)" ]; then
      printf 'refused: the pinned revision %s is not in %s, whose own configuration defines no remote.origin.url to fetch it from (git would read a legacy remotes/ file or use `origin` as a path; OD-XHOST-GIT-PROGRAM-KEYS-20261024)\n' \
        "$rev" "$src"
      return 1
    fi
    "$SOUNDNESS_PYTHON3" -I "${TRUST_CG_DIR}/scripts/github_transport.py" --repo "$src" --remote origin pin "$rev" >&2 || return 1
    git -C "$src" cat-file -e "${rev}^{commit}" 2>/dev/null || return 1
  fi
  "$SOUNDNESS_PYTHON3" -I "$PRIVATE_CACHE_TOOL" mkdir "$SOUNDNESS_DEPS_DIR" >&2 || return 1
  if ! deps="$(private_path "$SOUNDNESS_DEPS_DIR")"; then
    printf 'refused: %s\n' "$deps"
    return 1
  fi
  dir="${deps}/${label}-${rev}"
  if [ ! -e "$dir/.git" ]; then
    git -C "$src" worktree prune >&2 || return 1
    (umask 077 && git -C "$src" worktree add --quiet --detach "$dir" "$rev") >&2 || return 1
  fi
  # The whole checkout, not only its root: Clean is built from its sources
  # and checks its proofs in place. Judged before the status check, so the
  # content that check compares can no longer change under another user.
  if ! dir="$(private_tree_path "$dir")"; then
    printf 'refused: %s (`git -C %s worktree remove --force %s`)\n' "$dir" "$src" "${deps}/${label}-${rev}"
    return 1
  fi
  # git's own view of the checkout, before the first command that reads its
  # index (status runs core.fsmonitor): its work-tree top must be the checkout
  # judged above and its common git directory the source's, which the host
  # trust boundary judged. A core.worktree in the checkout's per-worktree
  # config.worktree would make git chdir to another directory and run what it
  # configures there; a .git re-pointed elsewhere would read another
  # repository's configuration (repair round 3 of
  # OD-XHOST-TRANSPORT-WORDS-20261024). rev-parse runs no configured program.
  local top common source_common
  top="$(git -C "$dir" rev-parse --show-toplevel 2>/dev/null)" || top=""
  common="$(git -C "$dir" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)" || common=""
  source_common="$(git -C "$src" rev-parse --path-format=absolute --git-common-dir 2>/dev/null)" ||
    source_common=""
  if [ -z "$top" ] || [ "$top" != "$dir" ] || [ -z "$common" ] || [ "$common" != "$source_common" ]; then
    printf 'refused: git uses the work tree %s and the git directory %s for the checkout %s, not the checkout itself and %s (a core.worktree in its config.worktree, or a .git re-pointed elsewhere; `git -C %s worktree remove --force %s`)\n' \
      "${top:-(none)}" "${common:-(none)}" "$dir" "${source_common:-(none)}" "$src" "$dir"
    return 1
  fi
  # Every key git reads in the checkout from its own configuration (the
  # source's shared config, judged at the host trust boundary, and the
  # checkout's per-worktree config.worktree) must be on the allowlist of keys
  # that name no program, before the first command that reads its index
  # (OD-XHOST-GIT-PROGRAM-KEYS-20261024).
  local judged
  if ! judged="$("$SOUNDNESS_PYTHON3" -I -B "${TRUST_CG_DIR}/scripts/host_boundary.py" --search-path "$PATH" \
         --judge-git-config "$dir" 2>&1)"; then
    printf 'refused: %s (`git -C %s worktree remove --force %s`)\n' \
      "$(printf '%s' "$judged" | tr '\n' ' ')" "$src" "$dir"
    return 1
  fi
  [ "$(repo_head "$dir")" = "$rev" ] || return 1
  [ -z "$(git -C "$dir" status --porcelain)" ] || return 1
  printf '%s\n' "$dir"
}
if scope_has_host_independent; then
  for row in "clean:CLEAN_DIR:CLEAN_SOURCE_DIR:${CLEAN_DIR_EXPLICIT}" "ay:AY_DIR:AY_SOURCE_DIR:${AY_DIR_EXPLICIT}"; do
    label="${row%%:*}"; rest="${row#*:}"; var="${rest%%:*}"; rest="${rest#*:}"
    source_var="${rest%%:*}"; explicit="${rest#*:}"
    if [ -n "$explicit" ]; then
      record "preflight: ${label} checkout" PASS "explicit ${var}=${!var}"
      continue
    fi
    pinned=""
    if rev="$(candidate_dependency_rev "$label")" &&
       pinned="$(pin_dependency_checkout "$label" "${!source_var}" "$rev")"; then
      record "preflight: ${label} checkout" PASS "pinned worktree ${pinned} (from ${!source_var})"
      printf -v "$var" '%s' "$pinned"
    elif [[ "$pinned" == "refused: "* ]]; then
      record "preflight: ${label} checkout" FAIL \
        "refusing the candidate's ${label} checkout under ${SOUNDNESS_DEPS_DIR:-the user cache}: ${pinned#refused: }"
      PREFLIGHT_OK=0
    else
      record "preflight: ${label} checkout" FAIL \
        "cannot check out the candidate's ${label} revision ${rev:-unresolved} from ${!source_var}"
      PREFLIGHT_OK=0
    fi
  done
  CLEAN_BIN="${CLEAN_DIR}/target/release/clean"
  echo "clean    : $CLEAN_DIR (as run)"
  echo "ay       : $AY_DIR (as run)"

  # VT-island tables. The vt islands' three-way differential needs a dump of
  # aterm's committed tables; without one it SKIPs, and a SKIP fails the gate.
  # When ISLAND_VT_TABLES is not given and an aterm repository is present,
  # export the dump here with the maintained exporter from aterm's origin/main
  # (a census run falls back to HEAD), and record the commit, the repository's
  # origin and the dump's SHA-256 as the aterm dependency of the record.
  if [ -z "$ISLAND_VT_TABLES_EXPLICIT" ] && [ -e "$ATERM_DIR/.git" ]; then
    vt_ref="origin/main"
    vt_rev="$(git -C "$ATERM_DIR" rev-parse --verify --quiet 'origin/main^{commit}' || true)"
    if [ -z "$vt_rev" ] && [ "$MODE_ATTEST" -ne 1 ]; then
      vt_ref="HEAD"
      vt_rev="$(git -C "$ATERM_DIR" rev-parse --verify --quiet 'HEAD^{commit}' || true)"
    fi
    vt_out="${LOGDIR}/vt-tables.json"
    if [ -n "$vt_rev" ] &&
       "$SOUNDNESS_PYTHON3" -I "$TRUST_CG_DIR/scripts/export_vt_tables.py" --aterm "$ATERM_DIR" \
         --revision "$vt_rev" --output "$vt_out" >"${LOGDIR}/vt-tables-provenance.json" \
         2>"${LOGDIR}/vt-tables-export.log" &&
       "$SOUNDNESS_PYTHON3" -I - "$ATERM_DIR" "$vt_ref" "$vt_rev" "$vt_out" "$(git -C "$ATERM_DIR" config --get remote.origin.url || true)" \
         >"${LOGDIR}/aterm.json" <<'ATERM_JSON'
import hashlib, json, sys
directory, ref, rev, dump, origin = sys.argv[1:6]
with open(dump, "rb") as handle:
    digest = hashlib.sha256(handle.read()).hexdigest()
print(json.dumps({"dir": directory, "ref": ref, "rev": rev, "origin": origin, "vt_tables_sha256": digest}))
ATERM_JSON
    then
      ISLAND_VT_TABLES="$vt_out"
      record "preflight: vt tables exported" PASS "aterm ${vt_ref} ${vt_rev} -> ${vt_out}" "${LOGDIR}/aterm.json"
    else
      record "preflight: vt tables exported" FAIL \
        "export from ${ATERM_DIR} at ${vt_ref} ${vt_rev:-unresolved} failed: ${LOGDIR}/vt-tables-export.log"
      PREFLIGHT_OK=0
    fi
  elif [ "$MODE_ATTEST" -eq 1 ]; then
    record "preflight: vt tables exported" FAIL \
      "no aterm repository at ${ATERM_DIR} (an attested run exports the vt tables from a recorded aterm commit)"
    PREFLIGHT_OK=0
  fi
fi
# The Trust toolchain every Cargo leg runs on: one installed package whose
# trustc/targo agree (scripts/trust_toolchain.py follows atpkg launchers), and
# whose sysroot ships the bin/ay the proof campaign admits. No stock fallback.
if trust_summary="$("$SOUNDNESS_PYTHON3" -I -B "$TRUST_CG_DIR/scripts/trust_toolchain.py" --print summary 2>&1)" &&
   trust_sysroot="$("$SOUNDNESS_PYTHON3" -I -B "$TRUST_CG_DIR/scripts/trust_toolchain.py" --print sysroot 2>&1)"; then
  record "preflight: Trust toolchain" PASS "$trust_summary"
  if [ -x "$trust_sysroot/bin/ay" ]; then
    record "preflight: Trust toolchain ships bin/ay" PASS "$trust_sysroot/bin/ay"
  else
    record "preflight: Trust toolchain ships bin/ay" FAIL \
      "no $trust_sysroot/bin/ay: trust-cg-verify would admit no AY"
    PREFLIGHT_OK=0
  fi
else
  record "preflight: Trust toolchain" FAIL "${trust_summary:-scripts/trust_toolchain.py failed}"
  PREFLIGHT_OK=0
fi
if [ -x "$TIMEOUT_RUNNER" ]; then
  record "preflight: timeout runner present" PASS "$TIMEOUT_RUNNER"
else
  record "preflight: timeout runner present" FAIL \
    "missing/not executable: $TIMEOUT_RUNNER"
  PREFLIGHT_OK=0
fi
if printf '%s\n' "$SOUNDNESS_COMMAND_TIMEOUT_SECONDS" |
   grep -Eq '^[0-9]+([.][0-9]+)?$' &&
   awk -v timeout="$SOUNDNESS_COMMAND_TIMEOUT_SECONDS" \
     'BEGIN { exit !(timeout > 0) }'; then
  record "preflight: positive command timeout" PASS \
    "${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s"
else
  record "preflight: positive command timeout" FAIL \
    "invalid SOUNDNESS_COMMAND_TIMEOUT_SECONDS=${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}"
  PREFLIGHT_OK=0
fi
if [ -d "$TRUST_CG_DIR" ]; then
  record "preflight: trust-cg dir present" PASS "$TRUST_CG_DIR"
else
  record "preflight: trust-cg dir present" FAIL "missing: $TRUST_CG_DIR"
  PREFLIGHT_OK=0
fi
if scope_has_host_independent; then
  if [ -d "$CLEAN_DIR" ]; then
    record "preflight: clean dir present" PASS "$CLEAN_DIR"
  else
    record "preflight: clean dir present" FAIL "missing: $CLEAN_DIR"
    PREFLIGHT_OK=0
  fi
  if [ -d "$AY_DIR" ]; then
    record "preflight: ay dir present" PASS "$AY_DIR"
  else
    record "preflight: ay dir present" FAIL "missing: $AY_DIR"
    PREFLIGHT_OK=0
  fi
fi
CANDIDATE_TRUST_IR_REV="$(candidate_dependency_rev trust-ir)"
CANDIDATE_CLEAN_REV="$(candidate_dependency_rev clean)"
CANDIDATE_AY_REV="$(candidate_dependency_rev ay)"
for row in \
  "TrustIR:$CANDIDATE_TRUST_IR_REV" \
  "Clean:$CANDIDATE_CLEAN_REV" \
  "AY:$CANDIDATE_AY_REV"; do
  label="${row%%:*}"
  value="${row#*:}"
  if printf '%s\n' "$value" | grep -Eq '^[0-9a-f]{40}$'; then
    record "preflight: candidate ${label} revision" PASS "$value"
  else
    record "preflight: candidate ${label} revision" FAIL \
      "all independently resolved Cargo locks must contain one coherent exact ${label} Git revision"
    PREFLIGHT_OK=0
  fi
done

# Host identity first: whether this host executes x86-64 natively decides
# which of the rows below apply (and gate_env's host contract).
host_json="${LOGDIR}/host.json"
if "$SOUNDNESS_PYTHON3" -I "$ATTESTATION_TOOL" host --json >"$host_json" 2>/dev/null &&
   "$SOUNDNESS_PYTHON3" -I -c 'import json, sys; sys.exit(0 if json.load(open(sys.argv[1]))["native_x86_64"] else 1)' "$host_json"; then
  HOST_NATIVE_X86_64=1
fi

if scope_has_host_independent; then
  # The gate environment contract, in the Trust lane scripts/trust_cargo.sh
  # executes (the PATH package scripts/trust_toolchain.py resolves), requiring
  # the effective AY to be the ay-pb pin. It runs in this bash's own
  # program, not the one the prelude's PATH names first, and its check starts
  # the gate's pinned python3 (SOUNDNESS_PYTHON3; repair round 3 of
  # OD-XHOST-GATE-CWD-20261025).
  gate_env_args=(--require-ay-pin)
  [ "$HOST_NATIVE_X86_64" -ne 1 ] || gate_env_args+=(--allow-x86_64-host)
  if TRUST_CG_TOOLCHAIN_LANE=path "${BASH:-/bin/bash}" "$TRUST_CG_DIR/scripts/gate_env.sh" "${gate_env_args[@]}" \
       >"${LOGDIR}/gate_env.log" 2>&1; then
    record "preflight: gate environment (scripts/gate_env.sh)" PASS \
      "$(grep -E '^gate_env: RESULT' "${LOGDIR}/gate_env.log" | tail -1)" "${LOGDIR}/gate_env.log"
  else
    record "preflight: gate environment (scripts/gate_env.sh)" FAIL \
      "$(grep -E '^gate_env: (FAIL|RESULT)' "${LOGDIR}/gate_env.log" | tr '\n' ' ' | cut -c1-600) — see ${LOGDIR}/gate_env.log" \
      "${LOGDIR}/gate_env.log"
    PREFLIGHT_OK=0
  fi
  if "$SOUNDNESS_PYTHON3" -I "$TRUST_CG_DIR/scripts/check_companion_coherence.py" >"${LOGDIR}/companion_coherence.log" 2>&1; then
    record "preflight: companion coherence" PASS "$(tail -1 "${LOGDIR}/companion_coherence.log")" \
      "${LOGDIR}/companion_coherence.log"
  else
    record "preflight: companion coherence" FAIL \
      "$(grep -E 'DISAGREEMENT|ERROR|INCOHERENT|failed' "${LOGDIR}/companion_coherence.log" | head -3 | tr '\n' ' ') — see ${LOGDIR}/companion_coherence.log" \
      "${LOGDIR}/companion_coherence.log"
    PREFLIGHT_OK=0
  fi
  if command -v node >/dev/null 2>&1 && node_version="$(node --version 2>/dev/null)"; then
    record "preflight: node present" PASS "$(command -v node) ${node_version}"
  else
    record "preflight: node present" FAIL "node not on PATH (the wasm and island differentials need it)"
    PREFLIGHT_OK=0
  fi
  # The island twins are compiled by the stock rustc ISLAND_TWIN_RUSTC names
  # (the Trust package ships no wasm32-unknown-unknown core/std); it is never
  # looked up on PATH. Its identity is recorded with the toolchain identities.
  wasm_libdir=""
  if [ -n "${ISLAND_TWIN_RUSTC:-}" ] && [ -x "${ISLAND_TWIN_RUSTC}" ]; then
    wasm_libdir="$(env -u RUSTUP_TOOLCHAIN "$ISLAND_TWIN_RUSTC" --print target-libdir \
      --target wasm32-unknown-unknown 2>/dev/null || true)"
  fi
  if [ -n "$wasm_libdir" ] && ls "$wasm_libdir"/libcore-*.rlib >/dev/null 2>&1; then
    record "preflight: rustc wasm32 target" PASS "${ISLAND_TWIN_RUSTC}: ${wasm_libdir}"
  else
    record "preflight: rustc wasm32 target" FAIL \
      "ISLAND_TWIN_RUSTC='${ISLAND_TWIN_RUSTC:-}' names no stock rustc with the wasm32-unknown-unknown standard library (the island twins cannot compile)"
    PREFLIGHT_OK=0
  fi
fi
# Toolchain and executed-binary identities: the Trust package every Cargo leg
# runs on (trustc -vV, the SHA-256 of trustc and targo), and in a full run the
# AY its sysroot ships, which trust-cg-verify admits and the proof campaign
# executes (by the SHA-256 of its bytes; its build stamp must name the ay-pb
# pin version), and the island twin rustc; on an x86-64 leg host the clang C
# compiler and an LLVM-family objdump those legs need.
if identities_out="$("$SOUNDNESS_PYTHON3" -I "$ATTESTATION_TOOL" identities --repo "$TRUST_CG_DIR" --scope "$RUN_SCOPE" \
     --island-twin-rustc "${ISLAND_TWIN_RUSTC:-}" --out "${LOGDIR}/identities.json" 2>&1)"; then
  record "preflight: toolchain identities recorded" PASS "$identities_out" "${LOGDIR}/identities.json"
else
  record "preflight: toolchain identities recorded" FAIL "$identities_out" "${LOGDIR}/identities.json"
  PREFLIGHT_OK=0
fi
if [ "$RUN_SCOPE" = portable ]; then
  # A portable run leaves the x86-64-native class out: neither the native-host
  # row nor the executor row is recorded, and nothing is dispatched.
  :
elif [ "$RUN_SCOPE" = x86_64-native ] || [ "$HOST_NATIVE_X86_64" -eq 1 ]; then
  if [ "$HOST_NATIVE_X86_64" -eq 1 ]; then
    record "preflight: native x86-64 host" PASS \
      "$("$SOUNDNESS_PYTHON3" -I "$ATTESTATION_TOOL" host 2>/dev/null | head -1)" "$host_json"
    # x86_sse_lane_gate fails if its silicon half did not run.
    export TRUST_CG_REQUIRE_X86_SILICON=1
  else
    record "preflight: native x86-64 host" FAIL \
      "$("$SOUNDNESS_PYTHON3" -I "$ATTESTATION_TOOL" host 2>/dev/null | tr '\n' ' ')" "$host_json"
    PREFLIGHT_OK=0
  fi
else
  # A full run elsewhere dispatches the x86-64-native legs. An unset or
  # unreachable executor is a FAIL, never a SKIP-pass.
  if [ -z "$SOUNDNESS_X86_HOST" ]; then
    record "preflight: x86-64 executor reachable" FAIL \
      "SOUNDNESS_X86_HOST is unset: this host is not native x86-64, so the x86_64-native legs have no executor"
    PREFLIGHT_OK=0
  elif probe_out="$("$REMOTE_RUNNER" probe --repo "$TRUST_CG_DIR" --host "$SOUNDNESS_X86_HOST" 2>&1)"; then
    record "preflight: x86-64 executor reachable" PASS "$(printf '%s\n' "$probe_out" | tail -1)"
  else
    record "preflight: x86-64 executor reachable" FAIL \
      "$(printf '%s\n' "$probe_out" | tail -3 | tr '\n' ' ')"
    PREFLIGHT_OK=0
  fi
fi

# An attestation records a commit identity, not uncommitted bytes: every
# checkout it reads must be clean and at the revision the candidate names.
START_TRUST_HEAD="$(repo_head "$TRUST_CG_DIR" 2>/dev/null || true)"
START_CLEAN_HEAD=""
START_AY_HEAD=""
if [ "$MODE_ATTEST" -eq 1 ]; then
  attest_repos=("trust-cg:$TRUST_CG_DIR")
  ! scope_has_host_independent || attest_repos+=("clean:$CLEAN_DIR" "ay:$AY_DIR")
  for row in "${attest_repos[@]}"; do
    label="${row%%:*}"
    dir="${row#*:}"
    if ! check_repo_worktree_clean "attest: ${label} worktree clean" "$dir"; then
      PREFLIGHT_OK=0
    fi
  done
  [ -n "$START_TRUST_HEAD" ] || PREFLIGHT_OK=0
  if scope_has_host_independent; then
    START_CLEAN_HEAD="$(repo_head "$CLEAN_DIR")" || PREFLIGHT_OK=0
    START_AY_HEAD="$(repo_head "$AY_DIR")" || PREFLIGHT_OK=0
    if [ "$START_CLEAN_HEAD" = "$CANDIDATE_CLEAN_REV" ]; then
      record "attest: Clean matches candidate dependency" PASS "$START_CLEAN_HEAD"
    else
      record "attest: Clean matches candidate dependency" FAIL \
        "checkout=$START_CLEAN_HEAD candidate=$CANDIDATE_CLEAN_REV"
      PREFLIGHT_OK=0
    fi
    if [ "$START_AY_HEAD" = "$CANDIDATE_AY_REV" ]; then
      record "attest: AY matches candidate dependency" PASS "$START_AY_HEAD"
    else
      record "attest: AY matches candidate dependency" FAIL \
        "checkout=$START_AY_HEAD candidate=$CANDIDATE_AY_REV"
      PREFLIGHT_OK=0
    fi
  fi
fi
if [ "$PREFLIGHT_OK" -ne 1 ] && [ "$FAIL_FAST" -eq 1 ]; then
  STOPPED_AT="preflight"
  finish_run
fi
[ "$MODE_PREFLIGHT_ONLY" -ne 1 ] || finish_run

# ----------------------------------------------------------------------------
# x86-64-native dispatch. A full run on a host that is not native x86-64 runs
# those legs on SOUNDNESS_X86_HOST in the background, overlapping the local
# legs, and imports that host's record (scripts/soundness_remote.sh). The
# remote side checks out exactly this commit and refuses a different tree.
# ----------------------------------------------------------------------------
REMOTE_COLLECTED=0
start_remote_dispatch() {
  REMOTE_DIR="${LOGDIR}/remote"
  mkdir -p "$REMOTE_DIR"
  # Its own process group (job control on for this one start), so a stop
  # reaches the ssh and everything under it.
  set -m
  "$REMOTE_RUNNER" run --repo "$TRUST_CG_DIR" --commit "$START_TRUST_HEAD" \
    --host "$SOUNDNESS_X86_HOST" --out "$REMOTE_DIR" >"${REMOTE_DIR}/run.log" 2>&1 &
  REMOTE_PID=$!
  set +m
}
collect_remote_dispatch() {
  local rc=0 oid triple
  [ "$REMOTE_COLLECTED" -eq 0 ] || return 0
  REMOTE_COLLECTED=1
  if [ -n "$REMOTE_PID" ]; then
    wait "$REMOTE_PID" || rc=$?
    REMOTE_PID=""
  else
    rc=1
  fi
  oid="$(cat "${REMOTE_DIR}/record_oid" 2>/dev/null || true)"
  triple="$(cat "${REMOTE_DIR}/triple" 2>/dev/null || true)"
  if [ "$rc" -eq 0 ] && [[ "$oid" =~ ^[0-9a-f]{40}$ ]] && [ -n "$triple" ]; then
    IMPORTED_RECORDS+=("${triple}=${oid}")
    record "x86_64-native: remote record" PASS \
      "staged ${triple} record ${oid}; published as refs/attest/soundness/${START_TRUST_HEAD}/${triple} with this run's record" "${REMOTE_DIR}/run.log"
  else
    record "x86_64-native: remote record" FAIL \
      "rc=${rc}: $(tail -3 "${REMOTE_DIR}/run.log" 2>/dev/null | tr '\n' ' ') — see ${REMOTE_DIR}/run.log" \
      "${REMOTE_DIR}/run.log"
  fi
}
poll_remote_dispatch() {
  # A dispatched run that already failed stops a fail-fast run now, not after
  # the local legs.
  [ -n "$REMOTE_PID" ] || return 0
  kill -0 "$REMOTE_PID" 2>/dev/null && return 0
  collect_remote_dispatch
}
DISPATCH_X86=0
if [ "$RUN_SCOPE" = full ] && [ "$HOST_NATIVE_X86_64" -ne 1 ]; then
  DISPATCH_X86=1
  REMOTE_DIR="${LOGDIR}/remote"
  mkdir -p "$REMOTE_DIR"
  if [ -z "$SOUNDNESS_X86_HOST" ]; then
    printf '%s\n' "SOUNDNESS_X86_HOST is unset: x86_64-native legs have no executor; no remote connection was attempted" \
      >"${REMOTE_DIR}/run.log"
  elif [ -n "$START_TRUST_HEAD" ] && [ -z "$(git -C "$TRUST_CG_DIR" status --porcelain 2>/dev/null)" ]; then
    start_remote_dispatch
  else
    echo "the x86-64-native legs run on a committed tree; this census run's worktree is dirty" \
      >"${REMOTE_DIR}/run.log"
  fi
fi

# ----------------------------------------------------------------------------
# Run the constellation. A census run attempts every gate even after a failed
# preflight (so the summary is complete); an --attest run stops at the first
# failing leg (record() calls finish_run).
# ----------------------------------------------------------------------------
RUN_PHASE=legs
section "trust-cg integration and library gates"
run_trust_cg_cargo_gates
poll_remote_dispatch

if leg_class_runs_here host-independent; then
  # The wasm offline oracles: interpreter-vs-compiled-wasm differentials (the
  # relooper's execution oracle — per-instruction proofs cannot see CFG
  # structuring bugs). The fuzz budget is bounded + deterministic (fixed seed in
  # the example, WASM_CFG_FUZZ_FUNCS functions).
  section "trust-cg wasm offline oracles (difftest + reducible-CFG fuzz)"
  run_wasm_oracle_gate "wasm difftest" wasm_difftest
  run_wasm_oracle_gate "wasm cfg-fuzz" wasm_cfg_fuzz "$WASM_CFG_FUZZ_FUNCS"

  # The shipped islands: the SAME spec compiled by two compilers and executed
  # against the interpreter's expectations. This is the gate that makes the
  # islands' "differential-experimental" label repository evidence rather than
  # a deployment intention.
  section "trust-cg wasm islands (three-way: trust-cg vs rustc/LLVM vs interpreter)"
  run_island_gates
  poll_remote_dispatch

  section "Clean checkout: clean-check (B-def / LRAT-checker proofs)"
  # The build's exit status GATES the checks. `$CLEAN_BIN` is a path into Clean's
  # target dir, so when the build fails a PREVIOUS binary is usually still sitting
  # there — and `run_clean_check`'s only precondition is that the path is
  # executable. Measured 2026-08-26: a failed build left a stale `clean` behind and
  # the three LRAT legs then ran against it and emitted Lean kernel type mismatches
  # ("rigid head/arity mismatch: List.rec vs Bool.rec"), which read exactly like
  # broken proofs. They were not: rebuilt correctly, the same three files check
  # 218/183/215 declarations with zero failures. Fail-closed either way, but attribute
  # it to the build rather than manufacturing a proof failure against the checkout.
  CLEAN_BIN_REBUILT=0
  if build_clean_binary; then
    CLEAN_BIN_REBUILT=1
    for f in "${CLEAN_LEAN[@]}"; do
      run_clean_check "$f"
    done
  else
    for f in "${CLEAN_LEAN[@]}"; do
      record "clean-check ${f}" FAIL \
        "BLOCKED: Clean binary was not rebuilt — not run against a possibly stale $CLEAN_BIN"
    done
  fi

  section "trust-cg checkout: clean-check repository proofs (AAPCS64 clobber / sentinel decide / MIR place resolution)"
  # Same stale-binary discipline as the Clean checkout legs above: a failed
  # rebuild must not run these proofs against a leftover binary. With no binary
  # at all, each proof records a loud SKIP (incomplete, nonzero) — never a pass;
  # a missing proof file is still a FAIL. The inventory leg needs no checker.
  # Under --attest every leg that reads these proofs (and formal/lean below)
  # reads the private export of the attested commit, never the working tree;
  # a refused export runs none of them.
  if ! export_candidate_proofs; then
    record "trust-cg proofs/*.lean inventory" FAIL "not run: ${CANDIDATE_PROOF_REFUSAL}"
    for f in "${TRUST_CG_LEAN[@]}"; do
      record "clean-check trust-cg proofs/${f}" FAIL "not run: ${CANDIDATE_PROOF_REFUSAL}"
    done
  else
    check_trust_cg_proof_inventory
    if [ "$CLEAN_BIN_REBUILT" -eq 1 ] || [ ! -x "$CLEAN_BIN" ]; then
      for f in "${TRUST_CG_LEAN[@]}"; do
        run_trust_cg_clean_check "$f"
      done
    else
      for f in "${TRUST_CG_LEAN[@]}"; do
        record "clean-check trust-cg proofs/${f}" FAIL \
          "BLOCKED: Clean binary was not rebuilt — not run against a possibly stale $CLEAN_BIN"
      done
    fi
  fi
  poll_remote_dispatch

  section "Clean checkout: kernel diversity gate"
  run_cargo_gate "$CLEAN_DIR" clean-kernel micro_diversity_gate clean

  section "formal/lean forward-sim (ENC-1: lake build + sorry/axiom ratchet)"
  run_lean_formal_gate
  poll_remote_dispatch
fi

# ENC-4: the golden-vector binding of the Lean byte encoder to the REAL backend encoder.
# TWO legs anchored to ONE shared set of bytes (formal/lean/Trust/Model/EncoderGolden.lean):
#   * Lean leg  — `by decide` in EncoderGolden.lean pins the MODEL's `encode` to those bytes;
#                 already checked by `run_lean_formal_gate` above (lake build compiles it).
#   * Rust leg  — this Rust test target parses that same file and asserts the real `encode.rs` emits
#                 byte-for-byte the identical lists (and that the golden key-set covers the bound
#                 matrix). A drift on EITHER encoder — or a hand-edited golden — fails a gate.
section "ENC-4: Lean<->backend encoder golden-vector binding (Rust leg)"
run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen lean_encode_golden_binding

# X-LEAN-P3: the AArch64 twin. formal/lean/Trust/A64/EncoderGolden.lean is generated from the
# Lean A64 instruction-word model's emitter corpus; its kernel-checked theorems (Lean leg, compiled
# by `run_lean_formal_gate` above) pin every row's word to the model's encode/decode. The Rust leg
# requires the production encode_instruction, the field-level helpers and ENC-5 to agree with
# every row and ENC-5 to refuse every single-bit corruption. Enumerated rows, not a refinement proof.
section "X-LEAN-P3: Lean A64 model<->AArch64 emitter golden binding (Rust leg)"
run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen lean_a64_encode_golden_binding

# ABI-x86-cs: x86-64 callee-saved register preservation across calls.
# THREE kinds of evidence in one target, of deliberately unequal strength:
#   (E1) a System V EXECUTION oracle — an assembly probe pins a sentinel in each
#        of RBX/RBP/R12-R15, calls the subject and reports which sentinels died,
#        with an EIGHT-control battery (one clobbered register each, plus a
#        clean callee and an all-six callee) that must refute for its own stated
#        reason before the subject is judged. Needs an x86-64 host with
#        `cc -arch x86_64`; it announces itself LOUDLY when it cannot run.
#   (E2) an INDEPENDENT structural refutation for BOTH ABIs, over an external
#        LLVM-family objdump decode: the callee-saved registers the function
#        BODY mentions must all be in the set the PROLOGUE pushes, with the
#        epilogue an exact mirror. This is the only teeth the Windows x64 GPR
#        and XMM6-XMM15 lanes have here, because Win64 code cannot be executed
#        on a Darwin/SysV box. GNU objdump cannot decode both container
#        formats, so the x86-64 host needs llvm-objdump.
#   (E3) an always-available encoder-faithfulness floor (in-file SDM decode of
#        PUSH/POP/MOVDQU vs the frame's own save counts) which is explicitly NOT
#        independent and is labelled as such in the target.
# Gated here so the control batteries cannot be deleted, or defeated, with the
# local meta-gate green. Class x86_64-native: it runs only on a native
# x86-64 host (see soundness_leg_inventory).
section "ABI-x86-cs: x86-64 callee-saved preservation (SysV execution oracle + independent decode)"
run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen e2e_x86_64_callee_saved repo integration x86_64-native

# ABI-x86-cc: x86-64 NON-C CALLING CONVENTIONS — admit or fail closed.
#
# A trust-ir `CallingConv` never reaches x86 lowering (`X86PipelineConfig`'s
# `call_abi` is chosen from the target OS alone), so the ONLY thing a convention
# does is the adapter's admission decision — and that decision was written in
# AAPCS64 terms and applied unchanged to x86-64. Four kinds of evidence:
#   (E1) EXECUTION, in BOTH directions: clang calls trust-cg functions declared
#        Rust/Fast/Cold, and trust-cg functions declared at those conventions
#        call a clang-defined extern "C" reference. Every parameter carries a
#        distinct weight, so any permutation/drop/misplacement changes the
#        result. Reaches all six integer argument registers, all eight XMM
#        argument registers, both stack boundaries and both FP widths. Needs an
#        x86-64 host with `cc -arch x86_64`; announces itself LOUDLY when it
#        cannot run.
#   (E2) NINETEEN hand-written ASSEMBLY controls, each a REAL wrong-register or
#        wrong-stack-slot SysV assignment (five of them correct anchors), each
#        of which must produce its OWN independently predicted value. They cover
#        the CALLEE edge, the CALLER edge (assembly callers forwarding to a
#        clang callee) and the mixed lane's two independent class counters.
#   (E3) ADMISSION controls that always run, including the ARCHITECTURE
#        DIFFERENTIAL that makes the per-target Swift return budget
#        non-vacuous (the same module refused for x86-64 and accepted for
#        aarch64) at ALL THREE guard sites — definition, direct call and
#        indirect call — plus the fail-closed refusal of the UNWITNESSED
#        Windows x64 ABI and of a Win64 second return register, and riscv64's
#        Unwitnessed case end to end.
#   (E4) THE SWIFTCC SOURCE SIDE, MEASURED: hand-written assembly deposits known
#        values in named registers and clang reads the same symbol back through
#        __attribute__((swiftcall)) and through the plain C convention, with
#        sret witnesses and controls that must be read WRONG. Without it the
#        budget's source side is prose and the only measured half is trust-cg's
#        own constant.
# Gated here so the control batteries cannot be deleted, or defeated, with the
# local meta-gate green.
section "ABI-x86-cc: x86-64 non-C calling conventions (two-direction clang oracle + admission controls)"
run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen e2e_x86_64_calling_conv repo integration x86_64-native
# The (E4) swiftcc SOURCE-side measurement lives in its own target since the
# Linux x86-64 floor recorded it decided-absent under XD-03 (a host `cc` that is
# GCC ignores `__attribute__((swiftcall))`). It is gated HERE too, and gating it
# is NOT free on such a host: `targo` exits 0 and the target prints the
# conforming `SKIP: (E4) NOT RUN`, but `matrix_results.py check-cargo-gate`
# classifies a nonzero runtime-SKIP count as `skipped` and returns 1, so this
# gate records FAIL on any clang-less host. That is the honest reading — the
# measurement did not happen — and it is still not a licence to delete the
# evidence. The x86-64 host therefore needs clang as its cc.
run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen e2e_x86_64_swiftcc repo integration x86_64-native

# KIND 4 (2026-09-24): trust-ir's MUST-REFUSE CORPUS, run through this
# backend's REAL admission paths. trust-ir ships, at the pinned revision, a
# byte-pinned corpus of wire artifacts a conforming consumer must refuse (a
# module a named trust-ir entry point refuses; a module well-formed by every
# trust-ir rule that a native backend must still refuse — `Unclassified`
# struct passing beside a by-value aggregate, an unrecorded narrow FFI
# extension on DarwinPCS, `RegionHavocStore`, ...; poisoned byte strings) plus
# one control row a consumer must ACCEPT. The codegen target drives every row
# through the reader, the strict adapter, the AOT compiler and the compile
# service; the CLI target hands every row to the real `trust-cg` binary. A row
# this backend compiles fails BY NAME unless it is listed as known-accepted
# with its reason, and that list is exact in both directions, so it can only
# shrink. A row the corpus adds at a later pin fails by name (`uncovered`),
# which is why a trust-ir pin bump is not complete until both targets are
# green: scripts/bump_trust_ir_pin.py runs the codegen target as the last
# guard of its transaction and rolls the move back when it is red, and this
# gate runs both on every attested commit.
section "KIND 4: trust-ir must-refuse corpus through the real admission paths (in-process lanes + the trust-cg binary)"
run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen must_refuse_corpus
run_cargo_gate "$TRUST_CG_DIR" trust-cg-cli must_refuse_corpus

# WS7.2 (F-111): every certificate trust-cg writes covers LIR -> machine; the
# trust-ir -> LIR adapter is outside it (an InsertField that aliased its base
# compiled silently and still earned [VERIFIED] rules). Until an end-to-end
# trust-ir -> machine obligation exists (WS7.16), this differential is the
# check on that step: the vendored trust_ir_exec corpus and a pinned-seed
# aggregate generator, JIT-compiled at O0-O3 and compared with the trust-ir
# reference interpreter. The mutation-knobs leg is the gate's own negative
# twin (legacy_in_place_insert must reproduce the c13 mismatches), and the CLI
# leg holds the disclosure (trust-ir->lir NOT COVERED, no function-level
# VERIFIED) and the knob absence of the shipped binary. Statistical evidence,
# never proof.
section "WS7.2: trust-ir -> native differential and the adapter disclosure"
run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen trust_ir_interp_differential
run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen trust_ir_interp_differential repo integration host-independent mutation-knobs
run_cargo_gate "$TRUST_CG_DIR" trust-cg-cli emit_proofs_adapter_disclosure

# The x86-64 vector-compare certificates: trust-ir's per-cell rule admits the
# composite icmp cells on a certificate (CHC_X86_ICMP_CERTIFICATE_RULE: AY
# --strict-proofs unsat, Clean's `cert verify-external` exit 0 and fully
# verified, no hole). x86_icmp_manifest_cells pins the query BYTES; this leg
# re-runs the certificate on them, with the rule's AY (the pinned one) and Clean.
if leg_class_runs_here host-independent; then
  section "x86-64 vector-compare certificates (pinned AY --strict-proofs + the rule's Clean, per cell)"
  run_x86_icmp_certificate_gate
fi

# Roadmap WS7.5 (F-006, F-116, F-103; DG-73): the codegen LICENSE is bound to
# evidence, and a claim-less body is refused by default. `clean-kernel-tv`
# licenses a body only with its kernel-replayed TranslationValidation
# certificate, on every adapter entry (trust-cg-lower), every compiler lane —
# AOT, host JIT with native execution, closed-JIT Core, compile service,
# wasm32 (trust-cg-codegen) — and the CLI, whose `--permit-unlicensed` is the
# only operator spelling of a claim-less compile and discloses what it
# admitted (trust-cg-cli).
section "WS7.5: the codegen license is bound to evidence; claim-less bodies are refused by default"
run_cargo_gate "$TRUST_CG_DIR" trust-cg-lower codegen_license_evidence
run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen codegen_license_evidence
run_cargo_gate "$TRUST_CG_DIR" trust-cg-cli codegen_license_flags

if [ "$DISPATCH_X86" -eq 1 ]; then
  section "x86-64-native legs on ${SOUNDNESS_X86_HOST:-<no SOUNDNESS_X86_HOST>} (imported record)"
  collect_remote_dispatch
fi

# An attested run judges committed source, so detect any checkout mutation or
# commit movement that occurred while the long gate was running.
RUN_PHASE=post
if [ "$MODE_ATTEST" -eq 1 ]; then
  section "Post-run revision and cleanliness check"
  post_rows=("trust-cg:$TRUST_CG_DIR:$START_TRUST_HEAD")
  ! scope_has_host_independent || post_rows+=("clean:$CLEAN_DIR:$START_CLEAN_HEAD" "ay:$AY_DIR:$START_AY_HEAD")
  for row in "${post_rows[@]}"; do
    label="${row%%:*}"
    remainder="${row#*:}"
    expected="${remainder##*:}"
    dir="${remainder%:*}"
    if ! live="$(repo_head "$dir")"; then
      record "post-run: ${label} HEAD unchanged" FAIL "cannot read committed HEAD: $dir"
    elif [ "$live" != "$expected" ]; then
      record "post-run: ${label} HEAD unchanged" FAIL \
        "started $expected, ended $live"
    else
      record "post-run: ${label} HEAD unchanged" PASS "$live"
    fi
    check_repo_worktree_clean "post-run: ${label} worktree clean" "$dir" || :
  done

  # The executed rows must be exactly the declared inventory for this scope and
  # host: a leg the inventory declares but this run never recorded, or a row
  # it recorded that the inventory does not declare, fails the attestation.
  inventory_leg="inventory: executed legs match the declared inventory"
  expected_rows="$(soundness_leg_inventory | awk -F'\t' -v scope="$RUN_SCOPE" -v native="$HOST_NATIVE_X86_64" '
    $1 == "per-run" { print $2; next }
    $1 == "host-independent" && (scope == "full" || scope == "portable") { print $2; next }
    $1 == "x86_64-native" && (scope == "x86_64-native" || (scope == "full" && native == 1)) { print $2; next }
    $1 == "dispatch" && scope == "full" && native != 1 { print $2 }
  ' | LC_ALL=C sort)"
  actual_rows="$( { printf '%s\n' "${GATE_NAMES[@]}"; printf '%s\n' "$inventory_leg"; } | LC_ALL=C sort)"
  duplicate_rows="$(printf '%s\n' "$actual_rows" | uniq -d | tr '\n' ';')"
  if [ "$FAIL_COUNT" -gt 0 ] || [ "$SKIP_COUNT" -gt 0 ]; then
    record "$inventory_leg" FAIL "not evaluated: the run is already failing"
  elif [ "$expected_rows" = "$actual_rows" ] && [ -z "$duplicate_rows" ]; then
    record "$inventory_leg" PASS "$(printf '%s\n' "$expected_rows" | wc -l | tr -d ' ') legs, exactly the ${RUN_SCOPE} inventory for this host"
  else
    record "$inventory_leg" FAIL \
      "missing: $(comm -23 <(printf '%s\n' "$expected_rows") <(printf '%s\n' "$actual_rows") | tr '\n' ';') undeclared: $(comm -13 <(printf '%s\n' "$expected_rows") <(printf '%s\n' "$actual_rows") | tr '\n' ';') duplicated: ${duplicate_rows}"
  fi
fi

finish_run
