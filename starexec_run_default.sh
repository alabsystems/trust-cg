#!/bin/sh
# starexec_run_default.sh - SAT-Comp 2026 per-instance wrapper for
# trust-cg-sat.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Contract (SAT-Competition 2024/2026 No-Limits and Main tracks)
# --------------------------------------------------------------
# The judging harness invokes this wrapper with two positional
# arguments:
#
#   $1   path to the DIMACS CNF instance.
#   $2   path to a writable temporary directory in which the solver
#        may place auxiliary artefacts. For DRAT-checked tracks the
#        harness reads `<tmpdir>/proof.drat` after the solver exits
#        with code 20 (UNSAT); see the SAT-Comp 2024 rules document,
#        section "Proofs of unsatisfiability". For the No-Limits
#        track no proof is consumed, but emitting one anyway is
#        harmless and lets the same wrapper double for both tracks.
#
# Stdout / exit-code contract
# ---------------------------
# trust_cg_sat already conforms to the SAT-Comp contract directly:
#
#   * `s SATISFIABLE` + `v <lit> ... 0` lines + exit 10.
#   * `s UNSATISFIABLE`                       + exit 20.
#   * `s UNKNOWN` (or anything else)          + exit 0.
#
# This wrapper is therefore a thin forwarder: locate the solver
# binary, translate the (cnf, tmpdir) pair into the
# `<cnf> <proof>` invocation trust_cg_sat expects, and let the exit
# code propagate.
#
# POSIX `sh` only.

set -u

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

if [ "$#" -lt 1 ]; then
    printf 'c starexec_run_default: usage: %s <instance.cnf> [tmpdir]\n' "$0"
    printf 's UNKNOWN\n'
    exit 0
fi

INSTANCE=$1
# StarExec passes a tmpdir; if our local harness invokes us without one
# we fall back to the system temp area so DRAT emission stays
# parameter-free.
TMPDIR_ARG=${2:-${TMPDIR:-/tmp}}

# Locate the solver binary. Order of precedence:
#   1. `TRUST_CG_SAT_BIN` env var (lets a graded run override).
#   2. `./bin/trust_cg_sat` next to this script (the layout produced
#      by starexec_build).
#   3. `/usr/local/bin/trust_cg_sat` (the Docker image layout).
#   4. `target/release/trust_cg_sat` (for running directly out of a
#      developer cargo build without invoking starexec_build first).
#   5. anything named `trust_cg_sat` on PATH.
SOLVER=""
if [ -n "${TRUST_CG_SAT_BIN:-}" ] && [ -x "${TRUST_CG_SAT_BIN}" ]; then
    SOLVER=${TRUST_CG_SAT_BIN}
elif [ -x "${SCRIPT_DIR}/bin/trust_cg_sat" ]; then
    SOLVER="${SCRIPT_DIR}/bin/trust_cg_sat"
elif [ -x /usr/local/bin/trust_cg_sat ]; then
    SOLVER=/usr/local/bin/trust_cg_sat
elif [ -x "${SCRIPT_DIR}/target/release/trust_cg_sat" ]; then
    SOLVER="${SCRIPT_DIR}/target/release/trust_cg_sat"
elif command -v trust_cg_sat >/dev/null 2>&1; then
    SOLVER=$(command -v trust_cg_sat)
else
    printf 'c starexec_run_default: trust_cg_sat binary not found.\n'
    printf 'c   Looked in $TRUST_CG_SAT_BIN, %s/bin/, /usr/local/bin/,\n' "${SCRIPT_DIR}"
    printf 'c   %s/target/release/, and $PATH.\n' "${SCRIPT_DIR}"
    printf 's UNKNOWN\n'
    exit 0
fi

# Ensure the proof directory exists (StarExec usually provides one, but
# a local run via /tmp may not have a per-invocation subdir). `mkdir -p`
# is a no-op if it already exists.
mkdir -p "${TMPDIR_ARG}" 2>/dev/null || true
# Strip any trailing slash to avoid `dir//proof.drat` in stdout, which
# is cosmetically ugly in build logs even though it is filesystem-
# equivalent to a single slash.
TMPDIR_NORM=$(printf '%s' "${TMPDIR_ARG}" | sed 's:/*$::')
PROOF_PATH="${TMPDIR_NORM:-/}/proof.drat"

# Exec into the solver so signals propagate cleanly (a SAT-Comp
# timeout SIGTERM goes directly to trust_cg_sat rather than this
# wrapper). Exit-code-10/20/0 propagation is automatic.
exec "${SOLVER}" "${INSTANCE}" "${PROOF_PATH}"
