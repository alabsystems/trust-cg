#!/usr/bin/env python3
"""Per-commit soundness attestation records: build, write, verify, exchange.

A green `scripts/soundness_check.sh --attest` run on commit C is recorded as a
Git commit object whose single parent is C and whose tree holds
`attestation.json` plus per-leg evidence (parser summaries and log tails). The
record lives at

    refs/attest/soundness/<C>/<host-triple>

one ref per host, so hosts never contend and a record is never a commit on any
branch. A record is written locally; `push` copies the refs of one subject to a
remote. Nothing here pushes a branch.

`verify C` answers whether C is attested: every leg of C's declared inventory
(`scripts/soundness_check.sh --list-json` at C) passed in a record whose scope
and host allow it, with the x86-64-native legs covered by a record from a
native (not translated, not emulated) x86-64 host; the subject tree, runner
blobs, dependency tuple, pinned toolchain (the per-host trustc pin included),
executed AY and environment allowlist all match what C itself names.
`verify-anchored C --anchor A` runs the verifier committed at A (an
already-landed proper ancestor; never C itself) against C, so a change to this
file or to C's inventory is judged by A's code, not C's; the anchored verifier
also refuses a leg that A's inventory has and C's does not or that moved to a
weaker class, and lists every gate-surface file C changed since A. Verifying
still executes C's own `soundness_check.sh --list-json` (after the records are
loaded), and records are unsigned: C's own gate code can write a complete false
record, which only record signing would expose.

Two verdicts, one rule each (SOUNDNESS_CHECK.md, "Landing"):

* `verify C` (no `--landing`) is the RELEASE verdict: a full-scope record plus
  x86-64-native coverage from a native host, made on a toolchain that is not a
  derived overlay (an overlay is not a release input, OD-RELEASE-BOUNDARY-20261008).
  It never reads DEFERRED_LANDING_CLASSES and never accepts a portable record.
* `verify --landing C` is the LANDING verdict the pre-push hook and the train
  use: it also accepts a `portable` record (every per-run and host-independent
  leg) while THIS verifier's DEFERRED_LANDING_CLASSES names the classes the
  record leaves out, and prints each such class as NOT ATTESTED with the
  coverage credits that rest on it as NOT ANCHORED. Run anchored, this verifier
  is the anchor's, so the deferral is the anchor's; a candidate may only shrink
  it (the anchor refuses a candidate whose constant names a class its own does
  not). An overlay-made record is accepted for landing with a note.

Subcommands (see --help of each):
  host            print this host's identity and native-x86-64 verdict
  check-env       apply the environment allowlist (preflight row)
  exec-scrubbed   re-execute a command with only the allowlisted environment
  identities      record toolchain and executed-binary identities
  build           assemble a record directory from a finished run
  write           write a record directory as refs/attest/soundness/<C>/<triple>
  check-record    validate one record commit (used for imported remote records)
  verify          decide whether C is attested (release, or --landing)
  verify-anchored run the anchor commit's verifier on C
  deferred-classes print DEFERRED_LANDING_CLASSES (what a landing run may leave out)
  landing-exception decide whether the interim main-push exception is still in force
  fetch / push    exchange refs/attest/soundness/<C>/* with a remote
  show            print the records of C

Exit status of verify: 0 attested, 1 incomplete or failing, 2 malformed or
tooling error, 3 no record. Other subcommands: 0 success, 1 refused, 2 usage.

Records are unsigned today. The schema carries a `signing` object and `write
--sign` / `verify --require-signature` use Git's own commit signing, so a
signing policy is a configuration change, not a schema change.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Iterable, Optional

SCHEMA = "trust-cg-soundness-attestation-v1"
INVENTORY_SCHEMA = "trust-cg-soundness-legs-v1"
ENV_SCHEMA = "trust-cg-soundness-environment-v2"
ENV_POLICY = "allowlist-v1"
REF_PREFIX = "refs/attest/soundness"
# Count JSON containers, including the root object, independently of the
# interpreter decoder's recursion limit. Real records need only a few levels.
MAX_RECORD_JSON_DEPTH = 128
FULL_SHA = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
TRIPLE = re.compile(r"[A-Za-z0-9_.-]+\Z")
LEG_CLASSES = ("per-run", "host-independent", "x86_64-native", "dispatch")
# full: every class this host can run plus the x86-64 dispatch; x86_64-native:
# the remote side; portable: exactly the per-run and host-independent legs (a
# landing record while the x86-64-native class is deferred; never a release one).
SCOPES = ("full", "x86_64-native", "portable")
# Scopes whose record carries every per-run and host-independent leg and binds
# the executed AY, the Clean checker and the aterm dependency.
HOST_INDEPENDENT_SCOPES = ("full", "portable")
# THE LANDING DEFERRAL. Leg classes a LANDING verdict (`verify --landing`) may
# accept as NOT ATTESTED, each with the ruling that defers it. Ruling
# OD-LANDING-X86-DEFERRAL-20261008 (docs/decision-record.md; OD-34 option C,
# landing only): no landing host can execute x86-64 natively until a native
# x86-64 executor exists (pending hardware, OD-LANDING-HARDWARE-20261008), so a
# landing may carry a portable record. It replaces the 2026-09-27 exception's
# x86-64 premise. Rules: the RELEASE verdict never reads this constant; run
# anchored, the constant that applies is the anchor's (this file as committed
# at the anchor); it only SHRINKS: the anchored verifier refuses a candidate
# whose constant names a class this one does not (`deferred_landing_classes_in`),
# so a landing can never defer a class for its successors. Deleting the entry
# in a landing is the withdrawal, once a native x86-64 executor attests.
DEFERRED_LANDING_CLASSES = {"x86_64-native": "OD-LANDING-X86-DEFERRAL-20261008"}
# Classes that leave with a deferred class: the dispatch rows are the x86-64
# transport (the executor preflight and the imported record), which a portable
# record does not run.
DEFERRED_WITH = {"x86_64-native": ("dispatch",)}
# Coverage credits whose evidence rests on a deferred class. The ten x86-64
# SSE lane-routing credits are anchored on native silicon by x86_sse_lane_gate
# (an x86_64-native leg); MOVDQA and PMOVMSKB rest on silicon plus their
# wrong-model controls alone (SOUNDNESS_CHECK.md, x86_sse_lane_gate). A landing
# verdict that defers the class names them NOT ANCHORED. The list is
# trust-cg-verify's SSE_LANE_ROWS (src/x86_sse_lane_proofs.rs), held equal by
# scripts/tests/test_soundness_attestation.py.
DEFERRED_CLASS_DEPENDENT_CREDITS = {
    "x86_64-native": ("Pshufd", "Pmovmskb", "MovdqaRR", "Punpckldq", "Punpcklqdq", "Punpcklbw", "Punpckhbw",
                      "Ptest", "Pblendvb", "Packuswb"),
}
X86_MACHINES = ("x86_64", "amd64")
# Leg-weakening policy. The floor equals soundness_check.sh's default; a lower
# fuzz budget is a green but weaker leg, so an attestation refuses it.
WASM_CFG_FUZZ_FUNCS_FLOOR = 200
# TRUST_CG_*/TCG_* variables the gate itself sets, with the only value allowed.
# Every other TRUST_CG_*/TCG_* variable changes test behaviour (TCG_NO_DECODE_CHECK,
# TCG_NO_PROOF_CACHE, ...) and is refused in an attested run.
ALLOWED_CONTROL_VALUES = {
    "TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1",
    "TRUST_CG_RUN_ROSETTA_LINKRUN": "1",
    "TRUST_CG_REQUIRE_X86_SILICON": "1",
    "TRUST_CG_DIR": None,  # checked against the checkout below
}
REQUIRED_CONTROLS = {"TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1"}
# Explicit settings that substitute an input the gate otherwise derives from C.
REFUSED_WHEN_EXPLICIT = {
    "CLEAN_DIR": "an explicit Clean checkout replaces the pinned worktree at C's Clean revision "
                 "(set CLEAN_SOURCE_DIR to choose the object source instead)",
    "AY_DIR": "an explicit AY checkout replaces the pinned worktree at C's AY revision "
              "(set AY_SOURCE_DIR to choose the object source instead)",
    "ISLAND_VT_TABLES": "caller-supplied vt tables replace the dump exported from a recorded aterm commit",
    "TRUST_TARGO": "scripts/trust_cargo.sh would run a targo other than the package the preflight "
                   "identities probe (scripts/trust_toolchain.py)",
    "AY_SOLVER_PATH": "a solver override is not the executed-AY identity this record binds",
    "SOUNDNESS_SSH": "a replacement ssh transport is not the recorded x86-64 executor",
}
# THE ENVIRONMENT ALLOWLIST. An attested run's legs see only these variables:
# under --attest, soundness_check.sh re-executes itself through `exec-scrubbed`
# with exactly the allowlisted variables of its caller, and `check-env` then
# refuses any variable outside this list. A variable the caller set that is not
# on the list is REFUSED when its name is known to change what a leg does
# (LEG_AFFECTING below) and otherwise DROPPED (only its name is recorded).
#
# Recorded with their values: locations and settings a leg may read.
ENV_RECORDED = frozenset({
    "PATH", "HOME", "TMPDIR", "USER", "LOGNAME", "SHELL", "LANG", "LC_ALL", "TZ",
    "SDKROOT", "DEVELOPER_DIR", "MACOSX_DEPLOYMENT_TARGET",
    "XDG_CACHE_HOME", "XDG_CONFIG_HOME", "XDG_DATA_HOME",
    "CARGO_HOME", "CARGO_TARGET_DIR", "CARGO_BUILD_JOBS", "RUSTUP_HOME", "RUSTUP_TOOLCHAIN",
    "RUST_MIN_STACK", "RUST_TEST_THREADS", "RUST_BACKTRACE", "ELAN_HOME", "ATPKG_BIN",
    "GIT_EXEC_PATH", "GIT_CONFIG_GLOBAL", "GIT_CONFIG_NOSYSTEM", "GIT_SSH_COMMAND",
    # the gate's own settings
    "SOUNDNESS_COMMAND_TIMEOUT_SECONDS", "SOUNDNESS_DEPS_DIR", "SOUNDNESS_X86_HOST",
    "SOUNDNESS_X86_REMOTE_DIR", "SOUNDNESS_SSH_CONNECT_TIMEOUT", "CLEAN_SOURCE_DIR", "AY_SOURCE_DIR",
    "ATERM_DIR", "TRUST_AY_TARGET_DIR", "ISLAND_TWIN_RUSTC", "WASM_CFG_FUZZ_FUNCS",
    # scripts/host_boundary.py: one more group / account file whose entries are
    # ADDED to the host's (they can only make a group count as shared).
    "SOUNDNESS_EXTRA_GROUP_FILE", "SOUNDNESS_EXTRA_PASSWD_FILE",
})
ENV_RECORDED_PATTERNS = (re.compile(r"LC_[A-Z]+\Z"),)
# Allowed, name recorded, value not: terminal and session plumbing that no leg
# reads (a value may be a socket path or a session token).
ENV_INERT = frozenset({
    "TERM", "TERM_PROGRAM", "TERM_PROGRAM_VERSION", "TERM_SESSION_ID", "COLORTERM", "COLUMNS", "LINES",
    "SHLVL", "PWD", "OLDPWD", "_", "SSH_AUTH_SOCK", "SSH_AGENT_PID", "SSH_CLIENT", "SSH_CONNECTION",
    "SSH_TTY", "XPC_FLAGS", "XPC_SERVICE_NAME", "__CFBundleIdentifier", "__CF_USER_TEXT_ENCODING",
    "COMMAND_MODE", "SECURITYSESSIONID", "MAIL", "DISPLAY", "EDITOR", "VISUAL", "PAGER", "LESS",
    "GIT_EDITOR", "GIT_PAGER", "HOSTNAME", "TMUX", "TMUX_PANE",
})
# ENV_RECORDED, ENV_RECORDED_PATTERNS, ENV_INERT, ENV_PLATFORM_DEFAULTS,
# LEG_AFFECTING and classify_variable are the RULES of ENV_POLICY
# (allowlist-v1): the verdict every row of a record's environment report must
# have, which the record verifier re-derives row by row. They are what they
# were when records were first written under allowlist-v1 and must stay so:
# a change of any verdict is a new policy, applied by the verifier only to
# records that carry it (repair round 3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024;
# 850f69fd0 made the six names below `unknown` under the same policy name, so
# its verifier refused 25 of the 26 local records, main's 96226db68 included).
#
# The WRITER may scrub more than the rules allow, never less: these six,
# inert under allowlist-v1, are dropped from an attested run's environment
# (scrub_environment; only their names are recorded, under `dropped`) and
# refused by environment_report if they reach it (no record is written), so
# no record this writer produces carries a row for them and every one it
# does produce is an allowlist-v1 record by those rules. Each names a program,
# or options of one, that git or a git helper runs (an editor, a pager),
# which the host trust boundary does not judge; no leg reads them, and a git
# the run starts then uses PATH's `vi` and `less` (judged) instead. A new
# policy name was not minted for this: the landing train verifies a
# candidate's records with the BASE's verifier, which accepts allowlist-v1
# only, so no record of a renamed policy could ever land, and the rules a
# verifier applies did not change (OD-XHOST-GIT-PROGRAM-KEYS-20261024).
ENV_DROPPED_PROGRAMS = frozenset({"EDITOR", "VISUAL", "PAGER", "LESS", "GIT_EDITOR", "GIT_PAGER"})
ENV_DROPPED_PROGRAMS_REASON = ("names a program git or a git helper runs, which the host trust boundary does not "
                               "judge; an attested run drops it (OD-XHOST-GIT-PROGRAM-KEYS-20261024)")
# The macOS /usr/bin/python3 launcher (xcrun) adds these to every process it
# starts, so every leg run through a Python helper sees them. Each value names a
# directory the C compiler and linker search by default; any other value is a
# caller's setting and is refused (LEG_AFFECTING).
ENV_PLATFORM_DEFAULTS = {"CPATH": "/usr/local/include", "LIBRARY_PATH": "/usr/local/lib"}
# Set by the gate itself around the re-execution.
ENV_GATE_INTERNAL = frozenset({"SOUNDNESS_ENV_SCRUBBED", "SOUNDNESS_CALLER_REFUSED", "SOUNDNESS_CALLER_DROPPED"})
# The interpreter the gate pinned (repair round 3 of OD-XHOST-GATE-CWD-20261025):
# `exec-scrubbed` sets SOUNDNESS_PYTHON3 to the canonical path of the python3
# it runs as, and soundness_check.sh and its helpers start every python3 by
# that path. It is the gate's own, never a caller's setting, and it is not a
# rule of allowlist-v1 (classify_variable still calls the name an unknown gate
# setting, so a record row of it would not verify): the WRITER handles it
# outside those rules, scrubbing more, never less. A caller's value is refused
# by the scrub (soundness_check.sh refuses it with builtins before that), and
# environment_report writes no row for the gate's own, refusing one that is
# not the interpreter running the report.
ENV_GATE_PINNED = frozenset({"SOUNDNESS_PYTHON3"})
ENV_GATE_PINNED_REASON = ("is the gate's own pin of the one python3 it runs (soundness_check.sh sets it), never a "
                          "caller's setting; remedy: unset it (OD-XHOST-GATE-CWD-20261025)")
# Names known to change what a leg runs or how its result is judged. A caller
# variable matching one is refused (not silently dropped), with its reason.
LEG_AFFECTING = (
    (re.compile(r"PYTHON[A-Z0-9_]*\Z"),
     "changes what the gate's Python tools and result parsers import or execute"),
    (re.compile(r"NODE_[A-Z0-9_]*\Z"), "changes the node oracle's runtime"),
    (re.compile(r"DYLD_[A-Z0-9_]*\Z"), "injects or redirects dynamic libraries in every process (macOS)"),
    (re.compile(r"LD_[A-Z0-9_]*\Z"), "injects or redirects shared libraries in every process (Linux)"),
    (re.compile(r"(CPATH|C_INCLUDE_PATH|CPLUS_INCLUDE_PATH|OBJC_INCLUDE_PATH|LIBRARY_PATH|CPPFLAGS|LDFLAGS)\Z|"
                r"((TARGET_|HOST_)?(CC|CXX|AR|CFLAGS|CXXFLAGS|RANLIB))(_[A-Za-z0-9_]+)?\Z|CRATE_CC_NO_DEFAULTS\Z"),
     "changes the C toolchain (headers, libraries, compiler or flags) that build scripts and native legs use"),
    (re.compile(r"(LEAN|ELAN|LAKE)_[A-Z0-9_]*\Z"),
     "selects another Lean toolchain, library path or Lake setting than the pinned one"),
    (re.compile(r"CARGO_[A-Z0-9_]*\Z"),
     "Cargo configuration (runner, profile, rustflags, config, env, unstable) can change what a test "
     "binary is or whether it runs"),
    (re.compile(r"RUST[A-Z0-9_]*\Z"),
     "compiler selection or flags, or test-harness behaviour, differ from the pinned toolchain's defaults"),
    (re.compile(r"(TRUST_CG|TCG)_[A-Z0-9_]*\Z"),
     "a test control variable the gate does not set changes what legs check"),
    (re.compile(r"TRUST_[A-Z0-9_]*\Z"),
     "selects Trust toolchain inputs other than the package the preflight identities probe"),
    (re.compile(r"(AY|CLEAN)_[A-Z0-9_]*\Z"), "selects AY or Clean inputs other than the pinned ones"),
    (re.compile(r"GIT_[A-Z0-9_]*\Z"), "changes Git's configuration, object view or transport"),
    (re.compile(r"(BASH_ENV|ENV|SHELLOPTS|BASHOPTS|CDPATH|GLOBIGNORE|IFS|PS4)\Z|BASH_FUNC_.*"),
     "runs or alters code in every bash leg"),
    (re.compile(r"(PERL5LIB|PERL5OPT|PERLLIB|RUBYOPT|RUBYLIB|JAVA_TOOL_OPTIONS|_JAVA_OPTIONS)\Z"),
     "injects code into interpreters a leg may start"),
    (re.compile(r"(SOUNDNESS|ISLAND|WASM)_[A-Z0-9_]*\Z"), "a gate setting this policy does not know"),
)
# Cargo reads configuration from every ancestor of its working directory and
# from $CARGO_HOME. Outside the checkout (whose .cargo/config.toml is C's own)
# such a file can set a runner, rustflags, a profile or [env] for every leg.
CARGO_CONFIG_NAMES = ("config.toml", "config")
TRUSTC_PIN_FILE_PATH = "scripts/run_public_release_checks.sh"
# Files whose change between an anchor and a candidate alters what the gate
# checks. The anchored verifier lists every one C changed, for review.
GATE_SURFACE = (
    "scripts/soundness_check.sh", "scripts/soundness_attestation.py", "scripts/soundness_remote.sh",
    "scripts/matrix_results.py", "scripts/gate_env.sh", "scripts/trust_cargo.sh", "scripts/trust_toolchain.py",
    "scripts/run_with_timeout.py", "scripts/export_vt_tables.py", "scripts/check_x86_icmp_certificates.py",
    "scripts/private_cache.py", "scripts/host_boundary.py", "scripts/land_main.sh",
    "hooks/pre-push", "scripts/landing_checks.sh", "scripts/github_transport.py", TRUSTC_PIN_FILE_PATH,
)
RUNNER_FILES = {
    "soundness_check": "scripts/soundness_check.sh",
    "attestation_tool": "scripts/soundness_attestation.py",
    "matrix_results": "scripts/matrix_results.py",
    "gate_env": "scripts/gate_env.sh",
    "trust_cargo": "scripts/trust_cargo.sh",
    "trust_toolchain": "scripts/trust_toolchain.py",
}
DEPENDENCY_LOCKS = {
    "ay": ("Cargo.lock", "crates/rustc-codegen-trust-cg/Cargo.lock"),
    "clean": ("Cargo.lock", "crates/rustc-codegen-trust-cg/Cargo.lock", "fuzz/Cargo.lock"),
    "trust-ir": ("Cargo.lock", "crates/rustc-codegen-trust-cg/Cargo.lock", "fuzz/Cargo.lock"),
}
# AY's build stamp (see scripts/gate_env.sh): read from the bytes, never executed.
AY_BUILD_STAMP = re.compile(
    rb"(\d+\.\d+\.\d+)\+build\.(\d+)\.([0-9a-f]{7,40})@\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ")
# Owner decision pending: whether the executed AY's build commit must equal the
# ay-pb pin revision. Until then the version must match and the commit is reported.
AY_BUILD_COMMIT_POLICY = "report"
# Printed by proof_gate_strict's executed_ay_identity_is_reported: the AY that
# trust_cg_verify::ay_identity admits in that test binary (the Trust sysroot's
# bin/ay whose bytes its build recorded). The path is last: it may hold spaces.
CAMPAIGN_AY_LINE = re.compile(
    r"^proof_gate_strict: executed-ay sha256=([0-9a-f]{64}) route=(\S+) ay=(.+?)\s*$", re.M)
CAMPAIGN_AY_UNRESOLVED = re.compile(r"^proof_gate_strict: executed-ay unresolved: (.*)$", re.M)
CAMPAIGN_AY_ROUTE = "toolchain-pinned-ay"
CAMPAIGN_LEG = "proof_gate_strict"
TAIL_LINES = 80


class Refused(Exception):
    """A decision that is a refusal, not a tooling error."""


class Malformed(Exception):
    """A record or input that cannot be interpreted."""


# ---------------------------------------------------------------------------
# small helpers

def run(argv: list[str], *, cwd: Optional[Path] = None, check: bool = True, input_bytes: Optional[bytes] = None,
        env: Optional[dict] = None, timeout: int = 120) -> subprocess.CompletedProcess:
    return subprocess.run(argv, cwd=None if cwd is None else str(cwd), input=input_bytes, capture_output=True,
                          check=check, env=env, timeout=timeout)


def git(repo: Path, *args: str, check: bool = True, input_bytes: Optional[bytes] = None) -> str:
    result = run(["git", "-C", str(repo), *args], check=False, input_bytes=input_bytes)
    if check and result.returncode != 0:
        raise Malformed(f"git {' '.join(args)}: {result.stderr.decode(errors='replace').strip()}")
    return result.stdout.decode(errors="replace")


def git_ok(repo: Path, *args: str) -> bool:
    return run(["git", "-C", str(repo), *args], check=False).returncode == 0


def rev_parse(repo: Path, spec: str) -> str:
    value = git(repo, "rev-parse", "--verify", "--quiet", "--end-of-options", spec).strip()
    if not FULL_SHA.match(value):
        raise Malformed(f"cannot resolve {spec}")
    return value


def show_blob(repo: Path, commit: str, path: str) -> Optional[str]:
    result = run(["git", "-C", str(repo), "show", f"{commit}:{path}"], check=False)
    return result.stdout.decode(errors="replace") if result.returncode == 0 else None


def blob_id(repo: Path, commit: str, path: str) -> Optional[str]:
    result = run(["git", "-C", str(repo), "rev-parse", "--verify", "--quiet", f"{commit}:{path}"], check=False)
    value = result.stdout.decode().strip()
    return value if result.returncode == 0 and FULL_SHA.match(value) else None


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def first_line(text: str) -> str:
    for line in text.splitlines():
        if line.strip():
            return line.strip()
    return ""


def probe_environment() -> dict:
    """The environment identity probes run under: a Trust compiler refuses to run
    at all while a TRUST_CG_*/TCG_* control is set (scripts/trust_cargo.sh)."""
    return {key: value for key, value in os.environ.items() if not key.startswith(("TRUST_CG_", "TCG_"))}


def tool_version(argv: list[str]) -> Optional[str]:
    if shutil.which(argv[0]) is None:
        return None
    try:
        result = run(argv, check=False, timeout=60, env=probe_environment())
    except (OSError, subprocess.TimeoutExpired):
        return None
    text = (result.stdout or result.stderr).decode(errors="replace")
    return text.strip() if result.returncode == 0 and text.strip() else None


# The C drivers `e2e_x86_64_swiftcc` will try, in the order it tries them
# (OD-SWIFTCC-DRIVER-20261020). Kept identical to that target's own list so
# this preflight records the driver the target will actually select.
SWIFTCALL_CC_CANDIDATES = ("cc", "clang", "clang-21", "clang-20", "clang-19", "clang-18")


def swiftcall_driver() -> tuple[Optional[str], list[str]]:
    """The first C driver that honours `__attribute__((swiftcall))`, and every
    candidate tried.

    A CAPABILITY probe, not a name check: `__attribute__((swiftcall))` is what
    `e2e_x86_64_swiftcc` needs, and a driver merely CALLED clang could be too
    old for it while a `cc` that already IS a capable clang would be refused by
    name. GCC reports the attribute as ignored, which `-Werror` turns into a
    failed compile.

    It COMPILES, LINKS AND RUNS, exactly as that target's own probe does, and
    for a measured reason: on a host where `cc` resolves to zig's clang the
    attribute compiles while the link is the step that fails
    (`host-cc-must-be-gcc`), so a compile-only probe would record a driver the
    target cannot use. A candidate is accepted only when the binary it
    produces exits 0.
    """
    tried: list[str] = []
    env_driver = os.environ.get("TRUST_CG_SWIFTCALL_CC", "").strip()
    candidates = ([env_driver] if env_driver else []) + [
        name for name in SWIFTCALL_CC_CANDIDATES if name != env_driver
    ]
    with tempfile.TemporaryDirectory(prefix="trust_cg_swiftcall_probe_") as scratch:
        source = Path(scratch) / "probe.c"
        source.write_text("__attribute__((swiftcall)) int probe(void) { return 1; }\n"
                          "int main(void) { return probe() - 1; }\n")
        for candidate in candidates:
            tried.append(candidate)
            if shutil.which(candidate) is None and not Path(candidate).is_file():
                continue
            binary = Path(scratch) / f"probe_{len(tried)}"
            try:
                built = run([candidate, "-Werror", "-o", str(binary), str(source)],
                            check=False, timeout=180, env=probe_environment())
                if built.returncode != 0:
                    continue
                ran = run([str(binary)], check=False, timeout=60, env=probe_environment())
            except (OSError, subprocess.TimeoutExpired):
                continue
            if ran.returncode == 0:
                return candidate, tried
    return None, tried


def canonical_json(value) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def ref_name(commit: str, triple: str) -> str:
    return f"{REF_PREFIX}/{commit}/{triple}"


# ---------------------------------------------------------------------------
# host identity and the native-x86-64 verdict

CPUID_PROBE = r"""
#include <cpuid.h>
#include <stdio.h>
#include <string.h>
int main(void) {
  unsigned a, b, c, d, max_ext, i;
  char vendor[13] = {0}, brand[49] = {0}, hv_vendor[13] = {0};
  unsigned regs[12];
  __cpuid(0, a, b, c, d);
  memcpy(vendor, &b, 4); memcpy(vendor + 4, &d, 4); memcpy(vendor + 8, &c, 4);
  __cpuid(1, a, b, c, d);
  int hypervisor = (c >> 31) & 1, sse41 = (c >> 19) & 1;
  __cpuid(0x80000000, max_ext, b, c, d);
  if (max_ext >= 0x80000004) {
    for (i = 0; i < 3; i++) __cpuid(0x80000002 + i, regs[4*i], regs[4*i+1], regs[4*i+2], regs[4*i+3]);
    memcpy(brand, regs, 48);
  }
  if (hypervisor) {
    __cpuid(0x40000000, a, b, c, d);
    memcpy(hv_vendor, &b, 4); memcpy(hv_vendor + 4, &c, 4); memcpy(hv_vendor + 8, &d, 4);
  }
  printf("vendor=%s\nbrand=%s\nhypervisor=%d\nhypervisor_vendor=%s\nsse41=%d\n",
         vendor, brand, hypervisor, hv_vendor, sse41);
  return 0;
}
"""


def cpuid_probe() -> dict:
    """Execute CPUID through a compiled probe. Only meaningful on x86-64."""
    compiler = shutil.which("cc") or shutil.which("clang")
    if compiler is None:
        return {"available": False, "reason": "no C compiler to build the CPUID probe"}
    with tempfile.TemporaryDirectory() as temporary:
        source = Path(temporary) / "cpuid.c"
        binary = Path(temporary) / "cpuid"
        source.write_text(CPUID_PROBE)
        built = run([compiler, "-O0", "-o", str(binary), str(source)], check=False, timeout=120)
        if built.returncode != 0:
            return {"available": False, "reason": "CPUID probe did not compile: "
                    + first_line(built.stderr.decode(errors="replace"))}
        ran = run([str(binary)], check=False, timeout=30)
        if ran.returncode != 0:
            return {"available": False, "reason": f"CPUID probe exited {ran.returncode}"}
    fields = dict(line.split("=", 1) for line in ran.stdout.decode(errors="replace").splitlines() if "=" in line)
    return {
        "available": True, "vendor": fields.get("vendor", "").strip(), "brand": fields.get("brand", "").strip(),
        "hypervisor": fields.get("hypervisor") == "1", "hypervisor_vendor": fields.get("hypervisor_vendor", "").strip(),
        "sse41": fields.get("sse41") == "1",
    }


def sysctl(name: str) -> Optional[str]:
    if shutil.which("sysctl") is None:
        return None
    result = run(["sysctl", "-n", name], check=False, timeout=10)
    return result.stdout.decode(errors="replace").strip() if result.returncode == 0 else None


def linux_cpuinfo() -> dict:
    try:
        text = Path("/proc/cpuinfo").read_text(errors="replace")
    except OSError:
        return {}
    info: dict = {}
    for line in text.splitlines():
        if ":" not in line:
            continue
        key, value = (part.strip() for part in line.split(":", 1))
        if key in ("vendor_id", "model name", "flags", "CPU implementer") and key not in info:
            info[key] = value
    return info


def compiler_host_triple() -> Optional[str]:
    """The host triple of the compiler the legs run: the Trust package
    scripts/trust_cargo.sh builds with (TRUST_TARGO unset), as the
    scripts/trust_toolchain.py beside this file resolves it from PATH for the
    `workspace` purpose and reads it from that package's own `trustc -vV`. The
    PATH `trustc` is never executed: it may be an atpkg launcher shim whose
    shell prelude the resolver reads but never runs
    (DR-ATPKG-PRELUDE-SHIM-20261015), and the record's ref is named by this
    triple. There is no stock rustc fallback: without a resolvable package no
    Cargo leg runs, and the triple is unknown."""
    resolver = Path(__file__).resolve().parent / "trust_toolchain.py"
    env = {key: value for key, value in probe_environment().items() if key != "RUSTUP_TOOLCHAIN"}
    try:
        # -I: no user site-packages or .pth file (OD-XHOST-GATE-CWD-20261025).
        result = run([sys.executable, "-I", "-B", str(resolver), "--purpose", "workspace", "--print", "host"],
                     check=False, env=env, timeout=300)
    except (OSError, subprocess.TimeoutExpired):
        return None
    triple = result.stdout.decode(errors="replace").strip()
    return triple if result.returncode == 0 and TRIPLE.match(triple) else None


def native_x86_64_verdict(host: dict) -> tuple[bool, list[str]]:
    """Whether `host` executes x86-64 natively. Pure: unit-tested with synthetic probes."""
    reasons = []
    if host.get("machine") not in X86_MACHINES:
        reasons.append(f"machine is {host.get('machine')!r}, not x86-64")
    if host.get("translated"):
        reasons.append("the process is translated (Rosetta: sysctl.proc_translated=1)")
    cpuid = host.get("cpuid") or {}
    if not cpuid.get("available"):
        reasons.append("CPUID was not executed: " + str(cpuid.get("reason", "no probe")))
    else:
        if cpuid.get("vendor") not in ("GenuineIntel", "AuthenticAMD"):
            reasons.append(f"CPUID vendor {cpuid.get('vendor')!r} is not a hardware vendor")
        if "QEMU" in cpuid.get("brand", "").upper() or "TCG" in cpuid.get("hypervisor_vendor", "").upper():
            reasons.append("CPUID reports a QEMU/TCG emulated CPU")
    cpuinfo = host.get("cpuinfo") or {}
    if host.get("system") == "Linux":
        if "CPU implementer" in cpuinfo:
            reasons.append("/proc/cpuinfo describes an ARM CPU (user-mode emulation)")
        if cpuinfo.get("vendor_id") not in ("GenuineIntel", "AuthenticAMD"):
            reasons.append(f"/proc/cpuinfo vendor_id {cpuinfo.get('vendor_id')!r} is not a hardware vendor")
        if "QEMU" in cpuinfo.get("model name", "").upper():
            reasons.append("/proc/cpuinfo names a QEMU CPU model")
    return (not reasons), reasons


def probe_host(*, run_cpuid: bool = True) -> dict:
    machine = platform.machine().lower()
    system = platform.system()
    host = {
        "triple": compiler_host_triple(), "system": system, "release": platform.release(), "machine": machine,
        "hostname": platform.node(), "translated": False,
    }
    if system == "Darwin":
        host["translated"] = sysctl("sysctl.proc_translated") == "1"
        host["cpu_brand"] = sysctl("machdep.cpu.brand_string")
        host["hypervisor_present"] = sysctl("kern.hv_vmm_present") == "1"
    elif system == "Linux":
        host["cpuinfo"] = {key: value for key, value in linux_cpuinfo().items() if key != "flags"}
        flags = linux_cpuinfo().get("flags", "").split()
        host["cpuinfo_flags"] = {"hypervisor": "hypervisor" in flags, "sse4_1": "sse4_1" in flags}
        try:
            host["binfmt_qemu_x86_64"] = Path("/proc/sys/fs/binfmt_misc/qemu-x86_64").exists()
        except OSError:
            host["binfmt_qemu_x86_64"] = None
    host["cpuid"] = cpuid_probe() if (run_cpuid and machine in X86_MACHINES) else {
        "available": False, "reason": "not an x86-64 machine"}
    native, reasons = native_x86_64_verdict(host)
    host["native_x86_64"] = native
    host["native_x86_64_refusals"] = reasons
    return host


def cmd_host(args) -> int:
    host = probe_host()
    if args.json:
        print(json.dumps(host, indent=2, sort_keys=True))
    else:
        print(f"host triple: {host['triple']}; machine {host['machine']}; native x86-64: {host['native_x86_64']}")
        for reason in host["native_x86_64_refusals"]:
            print(f"  not native x86-64: {reason}")
    if args.require_native_x86_64 and not host["native_x86_64"]:
        return 1
    return 0


# ---------------------------------------------------------------------------
# the environment allowlist

def classify_variable(name: str, value: str, checkout: str) -> tuple[str, str]:
    """(verdict, reason) of one environment variable under the allowlist:
    ok (a gate control at its only allowed value), recorded, inert, internal,
    refused (a known leg-affecting name) or unknown (not on the allowlist)."""
    if name in ENV_GATE_INTERNAL:
        return "internal", ""
    if name in REFUSED_WHEN_EXPLICIT:
        return "refused", REFUSED_WHEN_EXPLICIT[name]
    if name == "TRUST_CG_DIR":
        if os.path.realpath(value) == os.path.realpath(checkout):
            return "ok", ""
        return "refused", "the gate must judge its own checkout"
    if name.startswith(("TRUST_CG_", "TCG_")):
        if name in ALLOWED_CONTROL_VALUES and value == ALLOWED_CONTROL_VALUES[name]:
            return "ok", ""
        return "refused", "a test control variable the gate does not set changes what legs check"
    if name in ENV_RECORDED or any(pattern.match(name) for pattern in ENV_RECORDED_PATTERNS):
        return "recorded", ""
    if name in ENV_INERT or name == "MANPATH":
        return "inert", ""
    if ENV_PLATFORM_DEFAULTS.get(name) == value:
        return "recorded", ""
    for pattern, reason in LEG_AFFECTING:
        if pattern.match(name):
            # An empty value states no setting; the variable is still kept from the legs.
            return ("unknown", "empty, and not on the environment allowlist") if value == "" else ("refused", reason)
    return "unknown", "not on the environment allowlist"


def scrub_environment(environ: dict, checkout: str) -> tuple[dict, list[dict], list[str]]:
    """The caller's environment split into what the legs may see (the allowlisted
    variables), the refused leg-affecting variables and the dropped unknown ones.
    ENV_DROPPED_PROGRAMS are dropped too, although allowlist-v1 holds them
    inert: the writer scrubs more than the policy's rules allow, never less."""
    kept: dict = {}
    refused: list[dict] = []
    dropped: list[str] = []
    for name in sorted(environ):
        if name in ENV_DROPPED_PROGRAMS:
            dropped.append(name)
            continue
        if name in ENV_GATE_PINNED:
            refused.append({"name": name, "reason": ENV_GATE_PINNED_REASON})
            continue
        verdict, reason = classify_variable(name, environ[name], checkout)
        if verdict in ("ok", "recorded", "inert"):
            kept[name] = environ[name]
        elif verdict == "refused":
            refused.append({"name": name, "reason": reason})
        elif verdict == "unknown":
            dropped.append(name)
    return kept, refused, dropped


def cargo_config_files(roots: Iterable[str], *, cargo_home: Optional[str], home: Optional[str]) -> list[dict]:
    """Cargo configuration files that apply to a leg and are not committed.

    Cargo merges `.cargo/config.toml` (or `config`) from the working directory
    and every ancestor, then `$CARGO_HOME/config.toml`. A file tracked by the Git
    repository of the directory it sits in is that repository's own committed
    configuration (C's, or a pinned dependency's); every other file is reported."""
    candidates: list[Path] = []
    for root in roots:
        if not root:
            continue
        path = Path(root).resolve()
        candidates += [directory / ".cargo" / name for directory in (path, *path.parents)
                       for name in CARGO_CONFIG_NAMES]
        if path.is_dir():
            # The pinned dependency worktrees are children of the deps directory.
            candidates += sorted(path.glob("*/.cargo/config.toml")) + sorted(path.glob("*/.cargo/config"))
    base = Path(cargo_home) if cargo_home else (Path(home) / ".cargo" if home else None)
    if base is not None:
        candidates += [base / name for name in CARGO_CONFIG_NAMES]
    found: dict[str, dict] = {}
    for candidate in candidates:
        try:
            if not candidate.is_file() or str(candidate) in found:
                continue
        except OSError:
            continue
        directory = candidate.parent.parent if candidate.parent.name == ".cargo" else None
        # `directory` may be in a repository whose own configuration nothing
        # judged (an ancestor of the checkout). core.fsmonitor, the configured
        # program `git ls-files` runs when it reads the index (no hook runs and
        # no pager starts with stdout captured), is turned off on the command
        # line, so this listing runs no configured program
        # (OD-XHOST-GIT-PROGRAM-KEYS-20261024).
        if directory is not None and git_ok(directory, "-c", "core.fsmonitor=false", "ls-files", "--error-unmatch",
                                            "--", str(candidate.relative_to(directory))):
            continue
        found[str(candidate)] = {"path": str(candidate), "sha256": sha256_file(candidate)}
    return list(found.values())


def environment_report(environ: dict, *, explicit: Iterable[str], effective: dict, checkout: str,
                       cargo_configs: Iterable[dict] = (), running_python3: Optional[str] = None) -> dict:
    """Classify the environment the legs run under. Pure: `environ` is that
    environment (after the --attest re-execution through `exec-scrubbed`),
    `explicit` the gate variables the caller set, `effective` the values the
    gate uses (defaults applied), `cargo_configs` the uncommitted Cargo
    configuration files found (cargo_config_files). Every variable must be on the
    allowlist; anything else is refused. Values are recorded only for recorded
    and gate-owned settings, never for inert or unknown names. The gate's
    pinned interpreter (ENV_GATE_PINNED) gets no row; when `running_python3`
    (the canonical path of the python3 making the report) is given, a pin that
    names another file is refused."""
    explicit = set(explicit)
    settings = []
    refused = []

    def add(name, value, verdict, reason="", **extra):
        row = {"name": name, "explicit": name in explicit, "verdict": verdict}
        if value is not None:
            row["value"] = value
        if reason:
            row["reason"] = reason
        row.update(extra)
        settings.append(row)
        if verdict == "refused":
            refused.append(f"{name}: {reason}")

    fuzz = environ.get("WASM_CFG_FUZZ_FUNCS", effective.get("WASM_CFG_FUZZ_FUNCS", str(WASM_CFG_FUZZ_FUNCS_FLOOR)))
    if not re.fullmatch(r"[0-9]+", fuzz or "") or int(fuzz) < WASM_CFG_FUZZ_FUNCS_FLOOR:
        add("WASM_CFG_FUZZ_FUNCS", fuzz, "refused",
            f"the CFG fuzz budget must be an integer of at least {WASM_CFG_FUZZ_FUNCS_FLOOR}")
    else:
        add("WASM_CFG_FUZZ_FUNCS", fuzz, "ok")
    for name in sorted(explicit & set(REFUSED_WHEN_EXPLICIT)):
        if name not in environ:
            add(name, effective.get(name), "refused", REFUSED_WHEN_EXPLICIT[name])
    for name in sorted(environ):
        if name == "WASM_CFG_FUZZ_FUNCS":
            continue
        if name in ENV_DROPPED_PROGRAMS:
            # exec-scrubbed drops it, so it reaches here only past the scrub:
            # refused, and no record is written (allowlist-v1 would have
            # called it inert, so a record row would not show what happened).
            add(name, None, "refused", ENV_DROPPED_PROGRAMS_REASON + "; it reached the legs past the scrub")
            continue
        if name in ENV_GATE_PINNED:
            # The gate's own pin, outside the allowlist-v1 rules: no row. One
            # that is not the interpreter making this report is refused.
            if running_python3 is not None and environ[name] != running_python3:
                add(name, environ[name], "refused", "names {}, not the interpreter the gate runs ({}), so the "
                    "gate's python3 runs are not one judged file (OD-XHOST-GATE-CWD-20261025)".format(
                        environ[name], running_python3))
            continue
        verdict, reason = classify_variable(name, environ[name], checkout)
        if verdict == "internal":
            continue
        if verdict == "unknown":
            add(name, None, "refused", reason)
        elif verdict == "inert":
            add(name, None, "inert")
        else:
            add(name, environ[name], verdict, reason)
    try:
        caller_refused = json.loads(environ.get("SOUNDNESS_CALLER_REFUSED") or "[]")
    except ValueError:
        caller_refused = [{"name": "SOUNDNESS_CALLER_REFUSED", "reason": "not JSON"}]
    for item in caller_refused if isinstance(caller_refused, list) else [{"name": "?", "reason": "malformed"}]:
        name = str((item or {}).get("name")) if isinstance(item, dict) else "?"
        reason = str((item or {}).get("reason")) if isinstance(item, dict) else "malformed"
        add(name, None, "refused", f"set by the caller: {reason}", caller=True)
    for name, value in REQUIRED_CONTROLS.items():
        if environ.get(name) != value:
            add(name, environ.get(name), "refused", f"must be exactly {value} in an attested run")
    named = {row["name"] for row in settings}
    for name in sorted(ENV_RECORDED - named):
        if name not in environ and effective.get(name) not in (None, ""):
            add(name, effective[name], "recorded", default=True)
    for item in cargo_configs:
        add(f"cargo config {item['path']}", item.get("sha256"), "refused",
            "an uncommitted Cargo configuration file applies to the legs (runner, rustflags, profile or [env] "
            "can change what a test binary is or whether it runs)")
    dropped = [name for name in (environ.get("SOUNDNESS_CALLER_DROPPED") or "").split(",") if name]
    return {"schema": ENV_SCHEMA, "policy": ENV_POLICY, "settings": settings, "refused": refused,
            "dropped": dropped, "cargo_configs": list(cargo_configs),
            "wasm_cfg_fuzz_funcs_floor": WASM_CFG_FUZZ_FUNCS_FLOOR}


def cmd_check_env(args) -> int:
    environ = dict(os.environ)
    if args.caller:
        # A census run is not re-executed: report what --attest would refuse.
        # It exported its own SOUNDNESS_PYTHON3; the caller's is named only
        # when the census run says the caller set one (--explicit).
        for name in ENV_GATE_PINNED - set(args.explicit):
            environ.pop(name, None)
        _, refused, dropped = scrub_environment(environ, args.checkout)
        effective = dict(item.split("=", 1) for item in args.effective)
        fuzz = effective.get("WASM_CFG_FUZZ_FUNCS", environ.get("WASM_CFG_FUZZ_FUNCS", ""))
        if not re.fullmatch(r"[0-9]+", fuzz) or int(fuzz) < WASM_CFG_FUZZ_FUNCS_FLOOR:
            refused.append({"name": "WASM_CFG_FUZZ_FUNCS",
                            "reason": f"the CFG fuzz budget must be an integer of at least {WASM_CFG_FUZZ_FUNCS_FLOOR}"})
        if refused:
            print("an --attest run would refuse: "
                  + "; ".join(f"{item['name']}: {item['reason']}" for item in refused))
            return 1
        print(f"no leg-affecting variable; --attest would drop {len(dropped)} unlisted name(s)")
        return 0
    effective = dict(item.split("=", 1) for item in args.effective)
    configs = cargo_config_files(args.cargo_root, cargo_home=environ.get("CARGO_HOME"), home=environ.get("HOME"))
    report = environment_report(environ, explicit=args.explicit, effective=effective,
                                checkout=args.checkout, cargo_configs=configs,
                                running_python3=running_interpreter())
    if args.out:
        Path(args.out).write_bytes(canonical_json(report))
    if report["refused"]:
        print("refused leg-affecting settings: " + "; ".join(report["refused"]))
        return 1
    recorded = [row["name"] for row in report["settings"] if row["verdict"] == "recorded"]
    print(f"environment is the allowlist ({ENV_POLICY}); WASM_CFG_FUZZ_FUNCS={effective.get('WASM_CFG_FUZZ_FUNCS', '')}; "
          f"recorded: {', '.join(recorded) or 'none'}; dropped from the caller: "
          f"{', '.join(report['dropped']) or 'none'}")
    return 0


def running_interpreter() -> str:
    """The canonical absolute path of the python3 running this tool, or ""
    when it cannot name its executable by an absolute path."""
    executable = sys.executable
    return os.path.realpath(executable) if executable and os.path.isabs(executable) else ""


def cmd_exec_scrubbed(args) -> int:
    """Re-execute argv with only the allowlisted variables of this environment.
    Refused and dropped names travel to the re-executed gate, whose check-env
    row reports them; the variables themselves do not."""
    argv = list(args.argv)
    if argv[:1] == ["--"]:
        argv = argv[1:]
    if not argv:
        raise Refused("exec-scrubbed needs a command after --")
    # The interpreters the re-executed gate runs, pinned (repair round 3 of
    # OD-XHOST-GATE-CWD-20261025): the command (the gate's bash) by its
    # canonical path, and SOUNDNESS_PYTHON3, the canonical path of the python3
    # running this scrub, which soundness_check.sh started by its pinned path
    # and compares with its own resolution before the prelude.
    if not os.path.isabs(argv[0]):
        raise Refused(f"exec-scrubbed runs a command named by an absolute path, not {argv[0]!r}")
    interpreter = running_interpreter()
    if not interpreter:
        raise Refused("the python3 running exec-scrubbed cannot name its own executable by an absolute path")
    command = os.path.realpath(argv[0])
    kept, refused, dropped = scrub_environment(dict(os.environ), args.checkout)
    kept.update(SOUNDNESS_ENV_SCRUBBED="1", SOUNDNESS_CALLER_REFUSED=json.dumps(refused),
                SOUNDNESS_CALLER_DROPPED=",".join(dropped), SOUNDNESS_PYTHON3=interpreter)
    sys.stdout.flush()
    os.execve(command, [command, *argv[1:]], kept)
    return 2  # not reached


# ---------------------------------------------------------------------------
# toolchain and executed-binary identities

def ay_identity(path: Path) -> dict:
    """AY build identity read from its bytes (never executed), as gate_env.sh does."""
    try:
        data = path.read_bytes()
    except OSError as error:
        return {"path": str(path), "error": str(error)}
    builds = sorted({match.groups() for match in AY_BUILD_STAMP.finditer(data)})
    identity = {"path": str(path), "sha256": sha256_bytes(data)}
    if len(builds) == 1:
        version, increment, commit = (part.decode() for part in builds[0])
        identity.update(version=version, build=int(increment), commit=commit)
    else:
        identity["version"] = None
        identity["stamp_problem"] = "no AY build stamp" if not builds else f"{len(builds)} different stamps"
    return identity


def trust_package(repo: Path) -> tuple[Optional[dict], str]:
    """The Trust package scripts/trust_cargo.sh runs (TRUST_TARGO unset): the one
    `scripts/trust_toolchain.py --print json` resolves from PATH."""
    env = {key: value for key, value in probe_environment().items() if key != "RUSTUP_TOOLCHAIN"}
    resolver = repo / "scripts" / "trust_toolchain.py"
    if not resolver.is_file():
        return None, f"{resolver} is missing"
    # -I: no user site-packages or .pth file (OD-XHOST-GATE-CWD-20261025).
    result = run([sys.executable, "-I", "-B", str(resolver), "--print", "json"], check=False, env=env, timeout=300)
    if result.returncode != 0:
        return None, "no Trust package resolves: " + first_line(
            (result.stderr or result.stdout).decode(errors="replace"))
    try:
        package = json.loads(result.stdout.decode())
    except ValueError as error:
        return None, f"scripts/trust_toolchain.py printed no JSON: {error}"
    for key in ("compiler", "targo", "sysroot", "commit", "host", "identity"):
        if not isinstance(package.get(key), str) or not package[key]:
            return None, f"scripts/trust_toolchain.py names no {key}"
    return package, ""


OVERLAY_MANIFEST = "overlay.json"


def overlay_identity(sysroot: Path) -> Optional[dict]:
    """The overlay manifest at a Trust sysroot, or None when there is none.

    scripts/assemble_trust_overlay.py writes `overlay.json` at the root of the
    sysroot it assembles (its `bin/trustc --print sysroot` must name that
    directory). An overlay is a local stand-in, not a published pack, and so
    not a release input (OD-RELEASE-BOUNDARY-20261008)."""
    manifest = sysroot / OVERLAY_MANIFEST
    if not manifest.exists():
        return None
    identity: dict = {"path": str(manifest)}
    try:
        data = manifest.read_bytes()
    except OSError as error:
        identity["error"] = str(error)
        return identity
    identity["sha256"] = sha256_bytes(data)
    try:
        identity["schema"] = json.loads(data.decode()).get("schema")
    except (ValueError, AttributeError, UnicodeDecodeError):
        identity["schema"] = None
    return identity


def pin_ay_version(repo: Path, commit: Optional[str] = None) -> tuple[Optional[str], Optional[str]]:
    rel = "crates/trust-cg-regalloc/Cargo.toml"
    text = show_blob(repo, commit, rel) if commit else (repo / rel).read_text(errors="replace")
    if not text:
        return None, None
    pins = re.findall(r"^ay-pb\s*=\s*\{([^}\n]*)\}\s*$", text, re.M)
    if len(pins) != 1:
        return None, None
    version = re.search(r'\bversion\s*=\s*"=?(\d+\.\d+\.\d+)"', pins[0])
    rev = re.search(r'\brev\s*=\s*"([0-9a-f]{40})"', pins[0])
    return (version.group(1) if version else None), (rev.group(1) if rev else None)


DARWIN_XCRUN = "/usr/bin/xcrun"


def darwin_c_oracle() -> dict:
    """The same Apple compiler/SDK selection as the native importer tests.

    Lean ships a clang too. PATH must never select it for the Darwin C/IR
    oracle, nor split the compiler from the linker or the SDK headers.
    """
    selected = []
    for arguments in (("--find", "clang"), ("--show-sdk-path",)):
        command = [DARWIN_XCRUN, "--sdk", "macosx", *arguments]
        result = run(command, check=False, env=probe_environment(), timeout=30)
        value = result.stdout.decode("utf-8").strip()
        if result.returncode or not value or len(value.splitlines()) != 1 or not Path(value).is_absolute():
            raise Refused(f"Darwin C oracle discovery failed: {command}: "
                          f"{result.stderr.decode(errors='replace').strip() or value!r}")
        selected.append(Path(value).resolve(strict=True))
    compiler, sdk = selected
    if not compiler.is_file() or not os.access(compiler, os.X_OK) or not sdk.is_dir():
        raise Refused("Darwin C oracle requires an executable compiler and an SDK directory")
    settings = next((sdk / name for name in ("SDKSettings.json", "SDKSettings.plist")
                     if (sdk / name).is_file()), None)
    if settings is None:
        raise Refused(f"Darwin C oracle SDK has no SDKSettings file: {sdk}")
    version = tool_version([str(compiler), "--version"])
    if not version:
        raise Refused(f"Darwin C oracle compiler does not answer --version: {compiler}")
    result = run([str(compiler), "-isysroot", str(sdk), "-Werror", "-x", "c", "-fsyntax-only", "-"],
                 check=False, env=probe_environment(), timeout=30,
                 input_bytes=b"#include <stdio.h>\nint main(void) { return puts(\"oracle\") < 0; }\n")
    if result.returncode:
        raise Refused("Darwin C oracle cannot compile the SDK stdio.h probe: "
                      + result.stderr.decode(errors="replace").strip())
    return {"discovery": {"program": DARWIN_XCRUN, "sdk": "macosx"},
            "compiler": {"path": str(compiler), "sha256": sha256_file(compiler), "version": version},
            "sdk": {"path": str(sdk), "settings": str(settings), "sha256": sha256_file(settings)}}


def darwin_c_oracle_problem(record: dict) -> Optional[str]:
    """Validate the recorded identity without asking the verifier's local SDK."""
    oracle = (record.get("toolchains") or {}).get("darwin_c_oracle") or {}
    if not isinstance(oracle, dict) or oracle.get("discovery") != {"program": DARWIN_XCRUN, "sdk": "macosx"}:
        return "the Darwin C oracle does not record Apple SDK discovery"
    for name in ("compiler", "sdk"):
        item = oracle.get(name) or {}
        if not isinstance(item, dict) or not Path(str(item.get("path", ""))).is_absolute() \
                or not SHA256.fullmatch(str(item.get("sha256", ""))):
            return f"the Darwin C oracle {name} is not bound by absolute path and SHA-256"
    version = oracle["compiler"].get("version")
    if not isinstance(version, str) or not version.strip():
        return "the Darwin C oracle compiler has no version identity"
    settings = Path(str(oracle["sdk"].get("settings", "")))
    if settings.parent != Path(oracle["sdk"]["path"]) or settings.name not in ("SDKSettings.json", "SDKSettings.plist"):
        return "the Darwin C oracle SDK settings do not belong to its recorded SDK"
    return None


def collect_identities(repo: Path, scope: str, host: dict,
                       island_twin_rustc: Optional[str] = None) -> tuple[dict, list[str]]:
    problems = []
    toolchains: dict = {"git": tool_version(["git", "--version"]), "python3": sys.version.split()[0]}
    executed: dict = {}
    if scope in HOST_INDEPENDENT_SCOPES and (host.get("system") == "Darwin"
                                            or str(host.get("triple", "")).endswith("-apple-darwin")):
        try:
            toolchains["darwin_c_oracle"] = darwin_c_oracle()
        except (Refused, OSError, UnicodeError, subprocess.TimeoutExpired) as error:
            problems.append(str(error))
    # Every Cargo leg of either scope runs on the Trust package (trust_cargo.sh).
    package, why = trust_package(repo)
    if package is None:
        problems.append(why)
    else:
        compiler, targo = Path(package["compiler"]), Path(package["targo"])
        toolchains["trust"] = {key: package.get(key) for key in (
            "compiler", "targo", "sysroot", "commit", "host", "release", "identity", "targo_version",
            "selection", "launchers")}
        # Whether the package is a derived overlay (scripts/assemble_trust_overlay.py
        # writes overlay.json at the sysroot it assembles). Always present: None
        # states "no overlay manifest at the sysroot", so a record that omits the
        # key is refused rather than read as a published pack.
        toolchains["trust"]["overlay"] = overlay_identity(Path(package["sysroot"]))
        pin_file = repo / TRUSTC_PIN_FILE
        pins = trustc_pins(pin_file.read_text(errors="replace") if pin_file.is_file() else None)
        version_line = package["identity"].splitlines()[0] if package["identity"] else ""
        pinned = pins.get(package["host"])
        if pinned is not None and version_line != pinned:
            problems.append(f"the Trust package's trustc is {version_line!r}, but {TRUSTC_PIN_FILE} pins "
                            f"{pinned!r} for {package['host']}")
        executed["trust_sysroot"] = package["sysroot"]
        executed["trustc"] = {"path": str(compiler), "sha256": sha256_file(compiler)}
        executed["targo"] = {"path": str(targo), "sha256": sha256_file(targo)}
    if scope in HOST_INDEPENDENT_SCOPES:
        toolchains.update(lake=tool_version(["lake", "--version"]), node=tool_version(["node", "--version"]))
        # The wasm islands' twin: the stock rustc ISLAND_TWIN_RUSTC names (the
        # Trust package ships no wasm32 std), recorded by path, bytes and -vV.
        twin = Path(island_twin_rustc) if island_twin_rustc else None
        if twin is None or not (twin.is_file() and os.access(twin, os.X_OK)):
            problems.append(f"ISLAND_TWIN_RUSTC {island_twin_rustc!r} names no executable stock rustc")
        else:
            toolchains["island_twin"] = {"path": str(twin), "sha256": sha256_file(twin),
                                         "rustc": tool_version([str(twin), "-vV"])}
            if toolchains["island_twin"]["rustc"] is None:
                problems.append(f"ISLAND_TWIN_RUSTC {twin} does not answer -vV")
        if package is not None:
            ay = Path(package["sysroot"]) / "bin" / "ay"
            if not os.access(ay, os.X_OK):
                problems.append(f"the Trust package {package['sysroot']} ships no executable bin/ay")
            else:
                executed["ay"] = ay_identity(ay)
                version, rev = pin_ay_version(repo)
                executed["ay"]["pin_version"], executed["ay"]["pin_rev"] = version, rev
                if version is None:
                    problems.append("cannot read the ay-pb pin")
                elif executed["ay"].get("version") != version:
                    problems.append(f"executed AY {ay} is version {executed['ay'].get('version')}, "
                                    f"not the ay-pb pin version {version}")
    if scope == "x86_64-native" or host.get("native_x86_64"):
        cc = tool_version(["cc", "--version"])
        objdump = tool_version(["llvm-objdump", "--version"]) or tool_version(["objdump", "--version"])
        toolchains.update(cc=cc, objdump=objdump)
        # What `e2e_x86_64_swiftcc` needs is a driver that HONOURS
        # `__attribute__((swiftcall))`, which is not the same as `cc` being
        # clang: since OD-SWIFTCC-DRIVER-20261020 the target probes a
        # candidate list and keeps the first that honours it, so a GCC `cc`
        # beside a capable clang is fine and this row must not refuse it.
        # Recording WHICH driver was selected keeps the reading attributable:
        # a row read by a different compiler than the record names is a
        # different measurement.
        swiftcall_cc, swiftcall_tried = swiftcall_driver()
        toolchains["swiftcall_cc"] = (
            None
            if swiftcall_cc is None
            else {"driver": swiftcall_cc,
                  "version": tool_version([swiftcall_cc, "--version"]),
                  "tried": swiftcall_tried}
        )
        if swiftcall_cc is None:
            problems.append(
                "no C driver honours `__attribute__((swiftcall))` "
                f"(tried {', '.join(swiftcall_tried)}); e2e_x86_64_swiftcc SKIPs under XD-03 "
                "without one. Install a clang, or name one in TRUST_CG_SWIFTCALL_CC")
        if objdump is None or "llvm" not in objdump.lower():
            problems.append("no LLVM-family objdump (e2e_x86_64_callee_saved (E2) needs one that decodes "
                            "both Mach-O and ELF; GNU objdump SKIPs it)")
    return {"toolchains": toolchains, "executed": executed, "host": host}, problems


def cmd_identities(args) -> int:
    host = probe_host()
    identities, problems = collect_identities(Path(args.repo), args.scope, host,
                                              island_twin_rustc=args.island_twin_rustc)
    identities["problems"] = problems
    Path(args.out).write_bytes(canonical_json(identities))
    if problems:
        print("; ".join(problems))
        return 1
    ay = identities["executed"].get("ay")
    summary = f"host {host['triple']} native-x86-64={host['native_x86_64']}"
    if ay:
        summary += f"; executed AY {ay.get('version')} sha256 {ay.get('sha256', '')[:16]}"
    print(summary)
    return 0


# ---------------------------------------------------------------------------
# dependency tuple and inventory, both derived from C itself

def repository_org(cargo_toml: str) -> Optional[str]:
    section = re.search(r"^\[workspace\.package\]\s*$(.*?)(?=^\[|\Z)", cargo_toml, re.M | re.S)
    if not section:
        return None
    found = re.findall(r'^\s*repository\s*=\s*"https://github\.com/([A-Za-z0-9][A-Za-z0-9_.-]*)/trust-cg(?:\.git)?"\s*$',
                       section.group(1), re.M)
    return found[0] if len(found) == 1 else None


def dependency_tuple(repo: Path, commit: str) -> dict:
    """The same rule as soundness_check.sh candidate_dependency_rev, read from C's blobs."""
    cargo_toml = show_blob(repo, commit, "Cargo.toml")
    org = repository_org(cargo_toml or "")
    if org is None:
        raise Malformed(f"{commit}: Cargo.toml names no single upstream repository")
    result = {}
    for name, locks in DEPENDENCY_LOCKS.items():
        revs = set()
        for lock in locks:
            text = show_blob(repo, commit, lock)
            if text is None:
                raise Malformed(f"{commit}: missing {lock}")
            rows = re.findall(rf'^\s*source = "git\+[^"]*/{re.escape(name)}\.git(?:[?#"]|$)[^\n]*$', text, re.M)
            lock_revs = set()
            for row in rows:
                match = re.fullmatch(
                    rf'\s*source = "git\+https://github\.com/([^/]+)/{re.escape(name)}\.git\?rev=([0-9a-f]{{40}})'
                    rf'#([0-9a-f]{{40}})"\s*', row)
                if not match or match.group(1) != org or match.group(2) != match.group(3):
                    raise Malformed(f"{commit}: {lock} has a non-exact {name} source")
                lock_revs.add(match.group(2))
            if len(lock_revs) != 1:
                raise Malformed(f"{commit}: {lock} must pin exactly one {name} revision")
            revs |= lock_revs
        if len(revs) != 1:
            raise Malformed(f"{commit}: split first-party {name} revisions {sorted(revs)}")
        result[name.replace("-", "_") if name != "ay" else "ay_source"] = revs.pop()
    return result


def toolchain_channel(repo: Path, commit: str) -> Optional[str]:
    text = show_blob(repo, commit, "rust-toolchain.toml") or ""
    channels = re.findall(r'^channel\s*=\s*"([^"]+)"\s*$', text, re.M)
    return channels[0] if len(channels) == 1 else None


def list_json_at(repo: Path, commit: str) -> Optional[dict]:
    """Run `soundness_check.sh --list-json` as committed at `commit` (needs only that
    script and gate_env.sh). None when the commit predates --list-json."""
    script = show_blob(repo, commit, "scripts/soundness_check.sh")
    if script is None or "--list-json" not in script:
        return None
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        (root / "scripts").mkdir()
        (root / "scripts/soundness_check.sh").write_text(script)
        gate_env = show_blob(repo, commit, "scripts/gate_env.sh")
        if gate_env is not None:
            (root / "scripts/gate_env.sh").write_text(gate_env)
        env = {key: value for key, value in os.environ.items() if not key.startswith(("TRUST_CG_", "TCG_"))}
        env.update(TRUST_CG_DIR=str(root), HOME=os.environ.get("HOME", str(root)))
        result = run(["bash", str(root / "scripts/soundness_check.sh"), "--list-json"], check=False, env=env,
                     timeout=60)
    if result.returncode != 0:
        raise Malformed(f"{commit}: soundness_check.sh --list-json failed: "
                        + first_line(result.stderr.decode(errors="replace")))
    return parse_inventory(result.stdout.decode())


def parse_inventory(text: str) -> dict:
    try:
        value = json.loads(text)
    except ValueError as error:
        raise Malformed(f"leg inventory is not JSON: {error}") from None
    if value.get("schema") != INVENTORY_SCHEMA or not isinstance(value.get("legs"), list):
        raise Malformed("leg inventory has the wrong schema")
    seen = set()
    for leg in value["legs"]:
        if not isinstance(leg, dict) or leg.get("class") not in LEG_CLASSES or not isinstance(leg.get("id"), str):
            raise Malformed(f"malformed inventory row {leg!r}")
        if leg["id"] in seen:
            raise Malformed(f"duplicate leg id {leg['id']!r}")
        seen.add(leg["id"])
    return value


def expected_legs(inventory: dict, scope: str, native_x86_64: bool) -> dict[str, str]:
    """leg id -> class, for a record of `scope` written on a host with that verdict."""
    wanted = {"per-run"}
    if scope == "full":
        wanted.add("host-independent")
        wanted.add("x86_64-native" if native_x86_64 else "dispatch")
    elif scope == "portable":
        wanted.add("host-independent")
    elif scope == "x86_64-native":
        wanted.add("x86_64-native")
    return {leg["id"]: leg["class"] for leg in inventory["legs"] if leg["class"] in wanted}


def inventory_sha(inventory: dict) -> str:
    return sha256_bytes(json.dumps(inventory["legs"], sort_keys=True).encode())


# ---------------------------------------------------------------------------
# build: assemble a record directory from a finished run

def read_legs_tsv(path: Path) -> list[dict]:
    legs = []
    for number, line in enumerate(path.read_text(errors="replace").splitlines(), 1):
        if not line:
            continue
        fields = line.split("\t")
        if len(fields) != 5:
            raise Malformed(f"{path}:{number}: expected 5 tab-separated fields")
        name, status, seconds, log, detail = fields
        if status not in ("PASS", "FAIL", "SKIP"):
            raise Malformed(f"{path}:{number}: status {status!r}")
        legs.append({"id": name, "status": status, "seconds": int(seconds) if seconds.isdigit() else None,
                     "log": log or None, "detail": detail})
    return legs


def matrix_results_module():
    """scripts/matrix_results.py, the parser the gate's Cargo legs are judged by."""
    name = "_attestation_matrix_results"
    if name in sys.modules:
        return sys.modules[name]
    spec_path = Path(__file__).resolve().parent / "matrix_results.py"
    if not spec_path.exists():
        return None
    import importlib.util
    spec = importlib.util.spec_from_file_location(name, spec_path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module  # dataclasses resolve their module while it loads
    spec.loader.exec_module(module)
    return module


def matrix_parse(log: Path) -> Optional[dict]:
    module = matrix_results_module()
    if module is None:
        return None
    with open(log, encoding="utf-8", errors="replace") as handle:
        result = module.parse_log(handle, mode="plain", rc=0, capture_available=True)
    keep = ("status", "passed", "failed", "ignored", "runtime_skipped", "filtered", "suites",
            "incomplete_suites", "parse_problems")
    return {key: result.get(key) for key in keep}


def cmd_build(args) -> int:
    repo = Path(args.repo)
    logdir = Path(args.logdir)
    out = Path(args.out)
    commit = rev_parse(repo, args.commit + "^{commit}")
    if FULL_SHA.match(args.commit) is None or commit != args.commit:
        raise Refused("build needs the full subject commit id")
    tree = rev_parse(repo, commit + "^{tree}")
    inventory = parse_inventory((logdir / "inventory.json").read_text())
    identities = json.loads((logdir / "identities.json").read_text())
    environment = json.loads((logdir / "environment.json").read_text())
    host = identities["host"]
    if args.scope == "x86_64-native" and not host.get("native_x86_64"):
        raise Refused("an x86_64-native record needs a native x86-64 host: "
                      + "; ".join(host.get("native_x86_64_refusals", [])))
    if environment.get("refused"):
        raise Refused("refused environment settings: " + "; ".join(environment["refused"]))
    legs = read_legs_tsv(logdir / "legs.tsv")
    expected = expected_legs(inventory, args.scope, bool(host.get("native_x86_64")))
    ran = [leg["id"] for leg in legs]
    if len(ran) != len(set(ran)):
        raise Refused("a leg was recorded twice: " + ", ".join(sorted({x for x in ran if ran.count(x) > 1})))
    missing, extra = sorted(set(expected) - set(ran)), sorted(set(ran) - set(expected))
    if missing or extra:
        raise Refused(f"executed legs differ from the inventory: missing {missing}, undeclared {extra}")
    not_passed = [f"{leg['id']}={leg['status']}" for leg in legs if leg["status"] != "PASS"]
    if not_passed:
        raise Refused("not every leg passed: " + ", ".join(not_passed))
    if out.exists():
        shutil.rmtree(out)
    (out / "legs").mkdir(parents=True)
    rows = []
    campaign_ay = None
    for index, leg in enumerate(legs):
        row = {"id": leg["id"], "class": expected[leg["id"]], "status": leg["status"],
               "seconds": leg["seconds"], "detail": leg["detail"]}
        log = Path(leg["log"]) if leg["log"] else None
        if log is not None and log.is_file():
            data = log.read_bytes()
            row["log_sha256"] = sha256_bytes(data)
            tail = b"\n".join(data.splitlines()[-TAIL_LINES:]) + b"\n"
            (out / "legs" / f"{index:03d}.tail").write_bytes(tail)
            row["log_tail"] = f"legs/{index:03d}.tail"
            if log.name.startswith("cargo_"):
                parsed = matrix_parse(log)
                if parsed is not None:
                    (out / "legs" / f"{index:03d}.json").write_bytes(canonical_json(parsed))
                    row["parser"] = f"legs/{index:03d}.json"
                    row["parser_status"] = parsed["status"]
            if leg["id"] == CAMPAIGN_LEG:
                text = data.decode(errors="replace")
                matches = CAMPAIGN_AY_LINE.findall(text)
                unresolved = CAMPAIGN_AY_UNRESOLVED.search(text)
                if unresolved is not None:
                    raise Refused(f"{CAMPAIGN_LEG} admitted no AY: {unresolved.group(1)}")
                if len({m[0] for m in matches}) != 1:
                    raise Refused(f"{CAMPAIGN_LEG} log must name exactly one executed AY, found {len(matches)}")
                sha, route, path = matches[0]
                if route != CAMPAIGN_AY_ROUTE:
                    raise Refused(f"{CAMPAIGN_LEG} admitted its AY by route {route}, not {CAMPAIGN_AY_ROUTE}")
                campaign_ay = {"path": path, "sha256": sha, "route": route}
        elif leg["log"]:
            raise Refused(f"leg {leg['id']} names a log that does not exist: {leg['log']}")
        rows.append(row)
    executed = dict(identities.get("executed", {}))
    if args.scope in HOST_INDEPENDENT_SCOPES:
        ay = executed.get("ay")
        if not ay or not ay.get("sha256"):
            raise Refused(f"the {args.scope} scope must bind the executed AY")
        if campaign_ay is None:
            raise Refused(f"the {args.scope} scope ran no {CAMPAIGN_LEG} leg naming its AY")
        if campaign_ay["sha256"] != ay["sha256"]:
            raise Refused(f"{CAMPAIGN_LEG} executed AY sha256 {campaign_ay['sha256']}, "
                          f"but the preflight probed {ay['sha256']}")
        executed["campaign_ay"] = campaign_ay
        if not args.clean_bin or not Path(args.clean_bin).is_file():
            raise Refused(f"the {args.scope} scope must bind the executed Clean checker binary")
        executed["clean"] = {"path": str(Path(args.clean_bin)), "sha256": sha256_file(Path(args.clean_bin))}
    dependencies = dependency_tuple(repo, commit)
    if args.aterm:
        aterm = json.loads(Path(args.aterm).read_text())
        dependencies["aterm"] = aterm
    elif args.scope in HOST_INDEPENDENT_SCOPES:
        raise Refused(f"the {args.scope} scope must record the aterm revision the vt tables came from")
    imported = []
    for item in args.imported or []:
        triple, _, oid = item.partition("=")
        if not TRIPLE.match(triple) or not FULL_SHA.match(oid):
            raise Refused(f"malformed --imported {item!r}")
        imported.append({"triple": triple, "record": oid})
    if imported and args.scope != "full":
        raise Refused(f"a {args.scope} record imports nothing: only a full run dispatches the x86-64 legs")
    record = {
        "schema": SCHEMA,
        "subject": {"commit": commit, "tree": tree},
        "scope": args.scope,
        "host": host,
        "runner": {name: blob_id(repo, commit, path) for name, path in RUNNER_FILES.items()},
        "inventory": {"sha256": inventory_sha(inventory), "legs": inventory["legs"]},
        "dependencies": dependencies,
        "rust_toolchain_channel": toolchain_channel(repo, commit),
        "toolchains": identities.get("toolchains", {}),
        "executed": executed,
        "environment": environment,
        "legs": rows,
        "imported": imported,
        "started_at": args.started_at, "finished_at": args.finished_at,
        "signing": {"scheme": None, "note": "unsigned; `write --sign` signs the record commit with Git"},
    }
    (out / "attestation.json").write_bytes(canonical_json(record))
    print(f"record for {commit} ({args.scope}, {host.get('triple')}): {len(rows)} legs PASS -> {out}")
    return 0


# ---------------------------------------------------------------------------
# write: the record directory becomes refs/attest/soundness/<C>/<triple>

def write_tree(repo: Path, directory: Path) -> str:
    """mktree over a two-level directory (attestation.json + legs/*) without an index."""
    def blob(path: Path) -> str:
        return git(repo, "hash-object", "-w", "--", str(path)).strip()

    entries = []
    for path in sorted(directory.iterdir()):
        if path.is_dir():
            sub = [f"100644 blob {blob(child)}\t{child.name}" for child in sorted(path.iterdir()) if child.is_file()]
            sub_tree = git(repo, "mktree", input_bytes=("\n".join(sub) + "\n").encode() if sub else b"").strip()
            entries.append(f"040000 tree {sub_tree}\t{path.name}")
        else:
            entries.append(f"100644 blob {blob(path)}\t{path.name}")
    return git(repo, "mktree", input_bytes=("\n".join(entries) + "\n").encode()).strip()


def record_document(data: bytes, label: str) -> dict:
    """One bounded-depth UTF-8 JSON object with unique keys and finite numbers."""
    def unique(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise ValueError("duplicate JSON object key")
            value[key] = item
        return value

    def finite(text):
        value = float(text)
        if not math.isfinite(value):
            raise ValueError("non-finite JSON number")
        return value

    def constant(text):
        raise ValueError("non-finite JSON number")

    try:
        # The JSON decoder's recursion ceiling varies between Python builds.
        # Bound nesting before decoding; delimiters in strings are data.
        depth = 0
        quoted = escaped = False
        for byte in data:
            if quoted:
                if escaped:
                    escaped = False
                elif byte == 92:
                    escaped = True
                elif byte == 34:
                    quoted = False
            elif byte == 34:
                quoted = True
            elif byte in (91, 123):
                depth += 1
                if depth > MAX_RECORD_JSON_DEPTH:
                    raise ValueError(f"JSON nesting exceeds {MAX_RECORD_JSON_DEPTH} containers")
            elif byte in (93, 125):
                depth -= 1
        value = json.loads(data.decode("utf-8"), object_pairs_hook=unique,
                           parse_float=finite, parse_constant=constant)
        if not isinstance(value, dict):
            raise ValueError("record must be a JSON object")
        return value
    except (ValueError, RecursionError) as error:
        raise Malformed(f"{label}: attestation.json is not unambiguous UTF-8 JSON: {error}") from None


def load_record(repo: Path, oid: str) -> dict:
    # Read raw bytes: show_blob's replacement decoding would hide invalid UTF-8.
    result = run(["git", "-C", str(repo), "show", f"{oid}:attestation.json"], check=False)
    if result.returncode != 0:
        raise Malformed(f"record {oid} has no attestation.json")
    record = record_document(result.stdout, f"record {oid}")
    record_shape(record, f"record {oid}")
    return record


def record_shape(record: dict, label: str) -> None:
    """Check the container and identity types consumers traverse, before Git writes.

    Missing optional evidence keeps its existing semantic refusal. This is a
    shape check, not a replacement for subject, inventory or proof validation.
    """
    def expect(value, kind, where):
        if not isinstance(value, kind):
            name = {dict: "object", list: "array", str: "string"}[kind]
            raise Malformed(f"{label}: {where} must be a JSON {name}")

    def object_field(parent, key, where, *, nullable=False):
        if key not in parent or (nullable and parent[key] is None):
            return {}
        value = parent[key]
        expect(value, dict, where)
        return value

    def strings(parent, keys, where):
        for key in keys:
            if key in parent:
                expect(parent[key], str, f"{where}.{key}")

    objects = {key: object_field(record, key, key) for key in
               ("subject", "host", "inventory", "dependencies", "toolchains", "executed", "environment")}
    strings(record, ("schema", "scope"), "record")
    strings(objects["subject"], ("commit", "tree"), "subject")
    strings(objects["host"], ("triple", "machine", "system"), "host")
    strings(objects["toolchains"], ("rustc",), "toolchains")
    for key in ("cpuid", "cpuinfo"):
        info = object_field(objects["host"], key, f"host.{key}", nullable=True)
        strings(info, ("brand", "hypervisor_vendor", "model name"), f"host.{key}")
    object_field(objects["dependencies"], "aterm", "dependencies.aterm", nullable=True)
    trust = object_field(objects["toolchains"], "trust", "toolchains.trust", nullable=True)
    object_field(trust, "overlay", "toolchains.trust.overlay", nullable=True)
    for key in ("trustc", "targo", "ay", "campaign_ay", "clean"):
        object_field(objects["executed"], key, f"executed.{key}", nullable=True)
    for parent, key, identity in ((record, "legs", ("id", "status")),
                                  (record, "imported", ("triple", "record")),
                                  (objects["environment"], "settings", ("name",))):
        if key not in parent:
            continue
        rows = parent[key]
        expect(rows, list, key)
        for index, row in enumerate(rows):
            where = f"{key}[{index}]"
            expect(row, dict, where)
            for name in identity:
                expect(row.get(name), str, f"{where}.{name}")
            if key == "imported" and not (TRIPLE.fullmatch(row["triple"]) and
                                          FULL_SHA.fullmatch(row["record"])):
                raise Malformed(f"{label}: {where} must name a host triple and full record commit")


def check_record(repo: Path, oid: str, commit: str, triple: str, *, require_signature: bool = False) -> dict:
    """Structural checks every record must pass before its legs are read."""
    parents = git(repo, "rev-list", "--parents", "-n", "1", oid).split()
    if parents[1:] != [commit]:
        raise Malformed(f"record {oid} must have exactly one parent, the subject {commit}")
    record = load_record(repo, oid)
    if record.get("schema") != SCHEMA:
        raise Malformed(f"record {oid}: schema {record.get('schema')!r}")
    subject = record.get("subject") or {}
    if subject.get("commit") != commit:
        raise Malformed(f"record {oid} names subject {subject.get('commit')}, not {commit}")
    if subject.get("tree") != rev_parse(repo, commit + "^{tree}"):
        raise Malformed(f"record {oid}: subject.tree is not {commit}^{{tree}}")
    host = record.get("host") or {}
    if host.get("triple") != triple:
        raise Malformed(f"record {oid} was written on {host.get('triple')}, but its ref names {triple}")
    if record.get("scope") not in SCOPES:
        raise Malformed(f"record {oid}: unknown scope {record.get('scope')!r}")
    if record.get("scope") == "x86_64-native" or any(
            leg.get("class") == "x86_64-native" for leg in record.get("legs", [])):
        native, reasons = native_x86_64_verdict(host)
        if not (native and host.get("native_x86_64")):
            raise Malformed(f"record {oid} carries x86_64-native legs from a host that is not native "
                            f"x86-64: {'; '.join(reasons) or 'host did not claim native execution'}")
    if require_signature and not git_ok(repo, "verify-commit", oid):
        raise Malformed(f"record {oid} carries no signature Git accepts")
    return record


def cmd_write(args) -> int:
    """Write the local record and promote the remote records it imports, in one
    atomic ref transaction: either every ref of this run exists afterwards or
    none does (a stopped run leaves no record under refs/attest/)."""
    repo = Path(args.repo)
    directory = Path(args.record_dir)
    record = record_document((directory / "attestation.json").read_bytes(), f"record directory {directory}")
    record_shape(record, f"record directory {directory}")
    commit = record.get("subject", {}).get("commit", "")
    triple = record.get("host", {}).get("triple", "")
    if not FULL_SHA.match(commit) or not TRIPLE.match(triple or ""):
        raise Refused("record names no full subject commit or no host triple")
    transaction: list[str] = []
    for item in record.get("imported", []):
        imported_ref = ref_name(commit, str(item.get("triple")))
        imported_oid = str(item.get("record"))
        try:
            imported = check_record(repo, imported_oid, commit, str(item.get("triple")))
        except Malformed as error:
            raise Refused(f"imported record {item} fails its checks: {error}") from None
        if imported.get("scope") != "x86_64-native" or any(
                leg.get("status") != "PASS" for leg in imported.get("legs", [])):
            raise Refused(f"imported record {item} is not a green x86_64-native record")
        current = run(["git", "-C", str(repo), "rev-parse", "--verify", "--quiet", imported_ref], check=False)
        if current.returncode == 0:
            if current.stdout.decode().strip() != imported_oid:
                raise Refused(f"{imported_ref} already names another record; refusing to replace it")
            transaction.append(f"verify {imported_ref} {imported_oid}")
        else:
            transaction.append(f"create {imported_ref} {imported_oid}")
    ref = ref_name(commit, triple)
    existing = run(["git", "-C", str(repo), "rev-parse", "--verify", "--quiet", ref], check=False)
    if existing.returncode == 0:
        oid = existing.stdout.decode().strip()
        try:
            old = check_record(repo, oid, commit, triple)
        except Malformed as error:
            raise Refused(f"{ref} already exists and is not a valid record ({error}); inspect it before "
                          "replacing it") from None
        if not (all(leg.get("status") == "PASS" for leg in old.get("legs", [])) and
                old.get("scope") == record["scope"]):
            raise Refused(f"{ref} already exists with different content ({oid}); refusing to replace it")
        if transaction:
            git(repo, "update-ref", "--stdin", input_bytes=("\n".join(transaction) + "\n").encode())
        print(f"{ref} already holds a green {old.get('scope')} record {oid}; kept it")
        print(oid)
        return 0
    tree = write_tree(repo, directory)
    env = dict(os.environ)
    if not git(repo, "config", "user.name", check=False).strip():
        env.setdefault("GIT_AUTHOR_NAME", "trust-cg soundness gate")
        env.setdefault("GIT_COMMITTER_NAME", "trust-cg soundness gate")
    if not git(repo, "config", "user.email", check=False).strip():
        env.setdefault("GIT_AUTHOR_EMAIL", "soundness-gate@localhost")
        env.setdefault("GIT_COMMITTER_EMAIL", "soundness-gate@localhost")
    passed = sum(1 for leg in record["legs"] if leg["status"] == "PASS")
    message = (f"soundness attestation {commit} {triple}\n\nscope: {record['scope']}\n"
               f"legs: {passed} PASS of {len(record['legs'])}\ninventory: {record['inventory']['sha256']}\n")
    argv = ["git", "-C", str(repo), "commit-tree", tree, "-p", commit, "-F", "-"]
    if args.sign:
        argv.insert(4, "-S")
    result = run(argv, check=False, input_bytes=message.encode(), env=env)
    if result.returncode != 0:
        raise Refused("commit-tree failed: " + result.stderr.decode(errors="replace").strip())
    oid = result.stdout.decode().strip()
    # The record must pass the same structural checks a verifier applies
    # before any ref names it.
    check_record(repo, oid, commit, triple)
    # Create-only updates in one transaction: a concurrent writer of any of
    # these refs makes the whole write fail.
    transaction.append(f"create {ref} {oid}")
    git(repo, "update-ref", "--stdin", input_bytes=("\n".join(transaction) + "\n").encode())
    for line in transaction[:-1]:
        print(f"promoted imported record {line.split()[1]} -> {line.split()[2]}")
    print(f"wrote {ref} -> {oid}")
    print(oid)
    return 0


def cmd_check_record(args) -> int:
    repo = Path(args.repo)
    record = check_record(repo, args.record, args.commit, args.triple, require_signature=args.require_signature)
    if args.scope and record.get("scope") != args.scope:
        raise Malformed(f"record {args.record} has scope {record.get('scope')}, expected {args.scope}")
    bad = [leg.get("id") for leg in record.get("legs", []) if leg.get("status") != "PASS"]
    if bad:
        print("record carries legs that did not pass: " + ", ".join(bad))
        return 1
    print(f"record {args.record}: {record.get('scope')} on {args.triple}, {len(record.get('legs', []))} legs PASS")
    return 0


# ---------------------------------------------------------------------------
# verify

def records_for(repo: Path, commit: str) -> dict[str, str]:
    prefix = f"{REF_PREFIX}/{commit}/"
    out = git(repo, "for-each-ref", "--format=%(refname) %(objectname)", prefix)
    records = {}
    for line in out.splitlines():
        name, oid = line.split()
        records[name[len(prefix):]] = oid
    return records


TRUSTC_PIN_FILE = TRUSTC_PIN_FILE_PATH
# `<host>) expected_trustc='<rustc --version of the certified Trust compiler>'`,
# the per-host pin the public-release gate enforces.
TRUSTC_PIN = re.compile(r"^\s*([a-z0-9_]+-[a-z0-9_.-]+)\)\s*expected_trustc='([^'\n]+)'", re.M)


def trustc_pins(text: Optional[str]) -> dict[str, str]:
    """host triple -> the exact `trustc --version` line C pins for it."""
    pins: dict[str, str] = {}
    for host, line in TRUSTC_PIN.findall(text or ""):
        if pins.get(host, line) != line:
            raise Malformed(f"{TRUSTC_PIN_FILE} pins two Trust compilers for {host}")
        pins[host] = line
    return pins


def toolchain_mismatch(record: dict, channel: Optional[str], pins: Optional[dict] = None) -> Optional[str]:
    """Why the record's compiler is not the one C pins.

    `channel = "trust"`: the legs ran on a Trust package, identified by a
    branded trustc -vV with a 40-hex commit, the SHA-256 of trustc and targo,
    and a targo of the same build. When C's public-release gate pins an exact
    Trust compiler for the record's host, the record's `trustc --version` line
    must be that line. A numbered stock channel (older commits): stock rustc of
    that release.
    """
    toolchains = record.get("toolchains") or {}
    if channel == "trust":
        trust = toolchains.get("trust") or {}
        executed = record.get("executed") or {}
        identity = str(trust.get("identity") or "")
        if not re.search(r"^binary: trustc$", identity, re.M):
            return "the legs' compiler is not a branded trustc"
        if not FULL_SHA.match(str(trust.get("commit", ""))) or \
                not re.search(rf"^commit-hash: {re.escape(str(trust.get('commit')))}$", identity, re.M):
            return "the Trust compiler carries no 40-hex commit identity"
        host = str(trust.get("host") or "")
        if not host or not re.search(rf"^host: {re.escape(host)}$", identity, re.M):
            return f"the Trust compiler's host {host!r} is not the one its -vV reports"
        version_line = identity.splitlines()[0] if identity else ""
        pinned = (pins or {}).get(host)
        if pinned is not None and version_line != pinned:
            return f"the legs' trustc is {version_line!r}, but {TRUSTC_PIN_FILE} pins {pinned!r} for {host}"
        build = re.fullmatch(r"rustc (\S+ \([^)]*\)) \(trustc [^)]*\)", version_line)
        targo_version = str(trust.get("targo_version") or "")
        if build is None or not targo_version.startswith(f"targo {build.group(1)} (targo "):
            return f"the executed targo {targo_version!r} is not the build of {version_line!r}"
        for tool in ("trustc", "targo"):
            if not SHA256.match(str((executed.get(tool) or {}).get("sha256", ""))):
                return f"the executed {tool} is not bound by SHA-256"
        return None
    if channel and re.fullmatch(r"\d+\.\d+\.\d+", channel):
        rustc = toolchains.get("rustc") or ""
        if not re.search(rf"^release: {re.escape(channel)}$", rustc, re.M):
            return "stock rustc release differs"
        return None
    return "the pinned channel is neither `trust` nor a numbered stock release"


def verify(repo: Path, commit_spec: str, *, anchor: Optional[str] = None, accept_removed: Iterable[str] = (),
           require_signature: bool = False, landing: bool = False) -> tuple[int, list[str]]:
    """The release verdict, or with `landing` the landing verdict (module docstring)."""
    lines: list[str] = []
    try:
        commit = rev_parse(repo, commit_spec + "^{commit}")
    except Malformed as error:
        return 2, [str(error)]
    records = records_for(repo, commit)
    if not records:
        return 3, [f"{commit}: no record under {REF_PREFIX}/{commit}/"]
    # Everything read from the repository is read BEFORE C's own
    # soundness_check.sh runs (list_json_at executes C's --list-json), so that
    # code cannot change which records, blobs or pins this verdict is based on.
    try:
        loaded = {triple: (oid, check_record(repo, oid, commit, triple, require_signature=require_signature))
                  for triple, oid in sorted(records.items())}
        deps = dependency_tuple(repo, commit)
        channel = toolchain_channel(repo, commit)
        pins = trustc_pins(show_blob(repo, commit, TRUSTC_PIN_FILE))
        pin_version, pin_rev = pin_ay_version(repo, commit)
        runner = {name: blob_id(repo, commit, path) for name, path in RUNNER_FILES.items()}
        anchor_commit = None
        if anchor is not None:
            anchor_commit = rev_parse(repo, anchor + "^{commit}")
            anchor_pins = trustc_pins(show_blob(repo, anchor_commit, TRUSTC_PIN_FILE))
            candidate_deferred = deferred_landing_classes_in(show_blob(repo, commit, RUNNER_FILES["attestation_tool"]))
            anchor_inventory = list_json_at(repo, anchor_commit)
        inventory = list_json_at(repo, commit)
        if inventory is None:
            return 2, [f"{commit}: its soundness_check.sh has no --list-json inventory"]
    except Malformed as error:
        return 2, [str(error)]
    problems: list[str] = []
    classes = {leg["id"]: leg["class"] for leg in inventory["legs"]}
    covered: dict[str, list[str]] = {leg_id: [] for leg_id in classes}
    full_records = []
    portable_records = []
    x86_hosts = []
    for triple, (oid, record) in loaded.items():
        where = f"{triple} ({oid[:12]})"
        host = record["host"]
        native = bool(host.get("native_x86_64")) and native_x86_64_verdict(host)[0]
        if record.get("inventory", {}).get("sha256") != inventory_sha(inventory):
            problems.append(f"{where}: recorded inventory differs from {commit}'s --list-json")
        if record.get("runner") != runner:
            problems.append(f"{where}: runner blobs {record.get('runner')} are not {commit}'s {runner}")
        recorded_deps = {key: value for key, value in record.get("dependencies", {}).items() if key != "aterm"}
        if recorded_deps != deps:
            problems.append(f"{where}: dependency tuple {recorded_deps} is not what {commit}'s locks resolve {deps}")
        toolchain_problem = toolchain_mismatch(record, channel, pins)
        if toolchain_problem:
            problems.append(f"{where}: {toolchain_problem} ({commit}'s rust-toolchain.toml channel {channel!r})")
        trust_host = str(((record.get("toolchains") or {}).get("trust") or {}).get("host") or "")
        if channel == "trust" and trust_host not in pins:
            lines.append(f"note: {where}: {commit[:12]}'s {TRUSTC_PIN_FILE} pins no exact Trust compiler for "
                         f"{trust_host or 'an unnamed host'}; its identity is recorded, not compared")
        if channel == "trust":
            overlay_problem, overlay_line = overlay_verdict(record, where, landing)
            if overlay_problem:
                problems.append(overlay_problem)
            if overlay_line:
                lines.append(overlay_line)
        env = record.get("environment") or {}
        if env.get("schema") != ENV_SCHEMA or env.get("policy") != ENV_POLICY or env.get("refused"):
            problems.append(f"{where}: environment report is missing, not the {ENV_POLICY} policy, or refused "
                            f"{env.get('refused')}")
        else:
            settings = {row.get("name"): row for row in env.get("settings", [])}
            fuzz = (settings.get("WASM_CFG_FUZZ_FUNCS") or {}).get("value")
            if record.get("scope") in HOST_INDEPENDENT_SCOPES and (not str(fuzz or "").isdigit()
                                                                    or int(fuzz) < WASM_CFG_FUZZ_FUNCS_FLOOR):
                problems.append(f"{where}: WASM_CFG_FUZZ_FUNCS {fuzz!r} is below the floor "
                                f"{WASM_CFG_FUZZ_FUNCS_FLOOR}")
            for row in env.get("settings", []):
                name, verdict = str(row.get("name")), row.get("verdict")
                if verdict not in ("ok", "recorded", "inert"):
                    problems.append(f"{where}: setting {name} was {verdict}")
                    continue
                if name in ("TRUST_CG_DIR", "WASM_CFG_FUZZ_FUNCS"):
                    continue  # the writer's checkout path; the fuzz floor is checked above
                # Re-derived under THIS verifier's allowlist, not the writer's.
                derived = classify_variable(name, str(row.get("value", "")), "\0")[0]
                if derived != verdict:
                    problems.append(f"{where}: setting {name} is {verdict} in the record but {derived} under "
                                    f"the {ENV_POLICY} allowlist")
            if env.get("cargo_configs"):
                problems.append(f"{where}: uncommitted Cargo configuration applied: {env.get('cargo_configs')}")
        expected = expected_legs(inventory, record["scope"], native)
        legs = {leg.get("id"): leg for leg in record.get("legs", [])}
        if len(legs) != len(record.get("legs", [])):
            problems.append(f"{where}: a leg is recorded twice")
        missing, extra = sorted(set(expected) - set(legs)), sorted(set(legs) - set(expected))
        if missing:
            problems.append(f"{where}: legs missing from the record: {missing}")
        if extra:
            problems.append(f"{where}: legs outside this record's scope/host: {extra}")
        for leg_id, leg in legs.items():
            if leg.get("status") != "PASS":
                problems.append(f"{where}: {leg_id} is {leg.get('status')}")
            elif leg.get("parser_status") not in (None, "pass"):
                problems.append(f"{where}: {leg_id} parser status {leg.get('parser_status')}")
            elif leg_id in covered and leg_id in expected:
                covered[leg_id].append(triple)
        if record["scope"] in HOST_INDEPENDENT_SCOPES:
            (full_records if record["scope"] == "full" else portable_records).append(triple)
            if triple.endswith("-apple-darwin") or (record.get("host") or {}).get("system") == "Darwin":
                oracle_problem = darwin_c_oracle_problem(record)
                if oracle_problem:
                    problems.append(f"{where}: {oracle_problem}")
            executed = record.get("executed") or {}
            ay, campaign = executed.get("ay") or {}, executed.get("campaign_ay") or {}
            if not SHA256.match(str(ay.get("sha256", ""))) or ay.get("sha256") != campaign.get("sha256"):
                problems.append(f"{where}: the executed AY is not bound (probe {ay.get('sha256')}, "
                                f"campaign {campaign.get('sha256')})")
            if ay.get("version") != pin_version:
                problems.append(f"{where}: executed AY version {ay.get('version')} is not the ay-pb pin {pin_version}")
            elif AY_BUILD_COMMIT_POLICY == "report" and pin_rev and not str(pin_rev).startswith(
                    str(ay.get("commit") or "-")):
                lines.append(f"note: {where}: executed AY build commit {ay.get('commit')} is not the ay-pb pin "
                             f"revision {pin_rev} (reported; owner decision pending)")
            if not SHA256.match(str((executed.get("clean") or {}).get("sha256", ""))):
                problems.append(f"{where}: the executed Clean checker binary is not bound")
            aterm = (record.get("dependencies") or {}).get("aterm") or {}
            if not FULL_SHA.match(str(aterm.get("rev", ""))) or not SHA256.match(str(aterm.get("vt_tables_sha256", ""))):
                problems.append(f"{where}: the aterm revision / vt-table digest is not recorded")
            for item in record.get("imported", []):
                if records.get(item.get("triple")) != item.get("record"):
                    problems.append(f"{where}: imported record {item} is not the one under its ref")
        if native:
            x86_hosts.append(triple)
    not_attested: list[str] = []
    if full_records:
        # A full record already carries every per-run and host-independent leg
        # (the missing-leg check above); only the x86-64-native class comes from
        # other records.
        for leg_id, leg_class in classes.items():
            if leg_class == "x86_64-native" and not covered[leg_id]:
                problems.append(f"x86_64-native leg {leg_id} has no PASS from a native x86-64 host")
    elif portable_records and landing:
        # The landing verdict on portable records: every class those records
        # leave out (x86_64-native and its dispatch rows) must be deferred by
        # THIS verifier's constant, or be covered by a native record.
        for leg_class, ruling, leg_ids in deferred_coverage(classes, covered):
            if ruling is None:
                problems.extend(f"{leg_class} leg {leg_id} has no PASS and the class is not deferred for landing"
                                for leg_id in leg_ids)
            else:
                not_attested.extend(not_attested_lines(leg_class, ruling, leg_ids))
    elif portable_records:
        problems.append("no full-scope record: a portable record is a landing record (verify --landing), "
                        "never a release record")
    else:
        problems.append("no full-scope record" + ("" if not landing else " and no portable-scope record"))
    if anchor_commit is not None:
        anchored_problems, anchored_lines = anchor_checks(repo, commit, anchor_commit, inventory, anchor_inventory,
                                                          accept_removed, pins=pins, anchor_pins=anchor_pins,
                                                          candidate_deferred=candidate_deferred)
        problems.extend(anchored_problems)
        lines.extend(anchored_lines)
    verdict = "attested for landing" if landing else "attested"
    if problems:
        return 1, lines + [f"{commit}: NOT {verdict}"] + [f"  {problem}" for problem in problems]
    if not_attested:
        return 0, lines + not_attested + [
            f"{commit}: {verdict} by {', '.join(sorted(records))} ({len(classes)} legs; portable scope; "
            "NOT a release record)"]
    return 0, lines + [f"{commit}: {verdict} by {', '.join(sorted(records))} "
                       f"({len(classes)} legs; x86-64-native from {', '.join(x86_hosts)})"]


def overlay_verdict(record: dict, where: str, landing: bool) -> tuple[Optional[str], Optional[str]]:
    """(problem, note) for a record's Trust package: a derived overlay is a landing
    input only (OD-RELEASE-BOUNDARY-20261008); a record that does not say whether
    its package was one is refused, never read as a published pack."""
    trust = (record.get("toolchains") or {}).get("trust") or {}
    if "overlay" not in trust:
        return (f"{where}: the record does not state whether its Trust package was a derived overlay "
                "(toolchains.trust.overlay)"), None
    overlay = trust["overlay"]
    if overlay is None:
        return None, None
    digest = str((overlay or {}).get("sha256") or "unreadable")
    if landing:
        return None, (f"note: {where}: made with a derived overlay toolchain (overlay.json sha256 {digest[:16]}); "
                      "accepted for landing only, an overlay is not a release input")
    return (f"{where}: made with a derived overlay toolchain (overlay.json sha256 {digest[:16]}); an overlay is "
            "not a release input, so this record never satisfies release verification "
            "(OD-RELEASE-BOUNDARY-20261008)"), None


def deferred_coverage(classes: dict[str, str], covered: dict[str, list[str]]):
    """(class, ruling or None, uncovered leg ids) for every class a portable
    record leaves out, in LEG_CLASSES order. The ruling is THIS verifier's."""
    groups: dict[str, list[str]] = {}
    for leg_id, leg_class in classes.items():
        if leg_class in ("per-run", "host-independent") or covered[leg_id]:
            continue
        groups.setdefault(leg_class, []).append(leg_id)
    owner = {companion: deferred for deferred, companions in DEFERRED_WITH.items() for companion in companions}
    for leg_class in LEG_CLASSES:
        if leg_class not in groups:
            continue
        deciding = owner.get(leg_class, leg_class)
        if deciding != leg_class and deciding not in groups:
            # The transport rows of a class every leg of which a native record
            # covers are not needed: nothing was left out.
            continue
        yield leg_class, DEFERRED_LANDING_CLASSES.get(deciding), groups[leg_class]


def not_attested_lines(leg_class: str, ruling: str, leg_ids: list[str]) -> list[str]:
    lines = [f"{leg_class}: NOT ATTESTED ({ruling}): {', '.join(leg_ids)}"]
    credits = DEFERRED_CLASS_DEPENDENT_CREDITS.get(leg_class)
    if credits:
        lines.append(f"{leg_class}: coverage credits NOT ANCHORED on native silicon in this landing: "
                     f"{', '.join(credits)} (x86_sse_lane_gate did not run)")
    return lines


def deferred_landing_classes_in(source: Optional[str]) -> dict:
    """DEFERRED_LANDING_CLASSES as a candidate's verifier source states it, read
    without executing it. No assignment (or no file) is an empty deferral (the
    withdrawal). The check is syntactic: one module-level literal dict of str ->
    str, and no other binding or in-place change of the name anywhere in the
    file; anything else is Malformed. A candidate's verifier is gate surface
    (GATE_SURFACE), so what this cannot see is listed for review."""
    if source is None:
        return {}
    try:
        tree = ast.parse(source)
    except SyntaxError as error:
        raise Malformed(f"the candidate's {RUNNER_FILES['attestation_tool']} does not parse: {error}") from None
    name = "DEFERRED_LANDING_CLASSES"
    literal = []
    for node in tree.body:
        targets = node.targets if isinstance(node, ast.Assign) else [node.target] if isinstance(
            node, ast.AnnAssign) else []
        if any(isinstance(target, ast.Name) and target.id == name for target in targets):
            literal.append(node)
    for node in ast.walk(tree):
        if isinstance(node, ast.Name) and node.id == name and not isinstance(node.ctx, ast.Load) and not any(
                node in getattr(top, "targets", [getattr(top, "target", None)]) for top in literal):
            raise Malformed(f"the candidate binds {name} outside one module-level literal")
        if isinstance(node, (ast.Global, ast.Nonlocal)) and name in node.names:
            raise Malformed(f"the candidate declares {name} global or nonlocal")
        if isinstance(node, ast.alias) and (node.asname or node.name) == name:
            raise Malformed(f"the candidate binds {name} by an import")
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and node.name == name:
            raise Malformed(f"the candidate defines a function or class named {name}")
        if isinstance(node, ast.Attribute) and node.attr == name and not isinstance(node.ctx, ast.Load):
            raise Malformed(f"the candidate rebinds {name} as an attribute of another object")
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == name \
                and node.attr not in ("get", "items", "keys", "values"):
            raise Malformed(f"the candidate changes {name} in place (.{node.attr})")
        if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id == name \
                and not isinstance(node.ctx, ast.Load):
            raise Malformed(f"the candidate changes {name} in place (item assignment)")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ("globals", "setattr",
                                                                                              "vars", "exec", "eval"):
            raise Malformed(f"the candidate's verifier calls {node.func.id}(), which can rebind {name} "
                            "beyond what a syntactic read sees")
    if not literal:
        return {}
    if len(literal) > 1:
        raise Malformed(f"the candidate assigns {name} more than once")
    try:
        value = ast.literal_eval(literal[0].value)
    except (ValueError, SyntaxError):
        raise Malformed(f"the candidate's {name} is not a literal") from None
    if not isinstance(value, dict) or not all(isinstance(key, str) and isinstance(item, str)
                                              for key, item in value.items()):
        raise Malformed(f"the candidate's {name} is not a dict of class -> ruling strings")
    return value


def anchor_checks(repo: Path, commit: str, anchor: str, inventory: dict, anchor_inventory: Optional[dict],
                  accept_removed: Iterable[str], *, pins: Optional[dict] = None,
                  anchor_pins: Optional[dict] = None,
                  candidate_deferred: Optional[dict] = None) -> tuple[list[str], list[str]]:
    """What the anchor (an already-landed ancestor) requires of the candidate.

    Run anchored, this verifier is the anchor's, so DEFERRED_LANDING_CLASSES
    here is the anchor's deferral: the candidate's may only be a subset of it
    (shrink-only), and no leg may move into a class it defers."""
    problems, lines = [], []
    added = sorted(set(candidate_deferred or {}) - set(DEFERRED_LANDING_CLASSES))
    for leg_class in added:
        problems.append(f"{commit[:12]}'s DEFERRED_LANDING_CLASSES defers {leg_class!r}, which the anchor's does not: "
                        "a landing may only shrink the deferral (OD-LANDING-X86-DEFERRAL-20261008)")
    for leg_class in sorted(set(DEFERRED_LANDING_CLASSES) - set(candidate_deferred or {})):
        lines.append(f"note: {commit[:12]} withdraws the landing deferral of {leg_class!r}")
    deferred_now = set(DEFERRED_LANDING_CLASSES) | {companion for deferred in DEFERRED_LANDING_CLASSES
                                                   for companion in DEFERRED_WITH.get(deferred, ())}
    if anchor == commit:
        return [f"anchor {anchor} is the candidate itself: a commit never anchors its own verification"], lines
    if not git_ok(repo, "merge-base", "--is-ancestor", anchor, commit):
        return [f"anchor {anchor} is not an ancestor of {commit}"], lines
    if anchor_inventory is None:
        lines.append(f"note: anchor {anchor[:12]} predates the leg inventory; no shrinkage check against it")
    else:
        now = {leg["id"]: leg["class"] for leg in inventory["legs"]}
        accepted = set(accept_removed)
        for leg in anchor_inventory["legs"]:
            if leg["id"] not in now:
                if leg["id"] in accepted:
                    lines.append(f"note: leg {leg['id']!r} removed since the anchor (explicitly accepted)")
                else:
                    problems.append(f"leg {leg['id']!r} is in anchor {anchor[:12]}'s inventory but not in "
                                    f"{commit[:12]}'s (removal needs --accept-removed-legs)")
            elif now[leg["id"]] != leg["class"]:
                change = f"leg {leg['id']!r} changed class {leg['class']} -> {now[leg['id']]} since the anchor"
                # Leaving the native-silicon or every-record class, or becoming
                # a dispatch row, weakens where the leg must pass.
                if leg["class"] in ("x86_64-native", "per-run") or now[leg["id"]] == "dispatch":
                    problems.append(change)
                elif now[leg["id"]] in deferred_now:
                    # Moving a leg into a class a landing may leave NOT ATTESTED
                    # would let a portable record skip it.
                    problems.append(change + " (into a class this verifier defers for landing)")
                else:
                    lines.append("note: " + change)
    for host in sorted(set(anchor_pins or {}) - set(pins or {})):
        problems.append(f"{TRUSTC_PIN_FILE}: the anchor pins a Trust compiler for {host}, {commit[:12]} pins none")
    changed = [path for path in GATE_SURFACE if blob_id(repo, anchor, path) != blob_id(repo, commit, path)]
    for path in changed:
        lines.append(f"notice: gate surface changed since anchor {anchor[:12]}: {path}")
    return problems, lines


def cmd_verify(args) -> int:
    rc, lines = verify(Path(args.repo), args.commit, anchor=args.anchor, accept_removed=args.accept_removed_legs,
                       require_signature=args.require_signature, landing=args.landing)
    print("\n".join(lines))
    return rc


def cmd_verify_anchored(args) -> int:
    """Run the verifier committed at the anchor against the candidate.

    The anchor must be a proper ancestor of the candidate: a commit never
    anchors its own verification. An anchor that predates this tool is a
    bootstrap, refused unless --allow-unanchored-bootstrap asks for the
    candidate's OWN verifier, whose verdict is then labelled UNANCHORED."""
    repo = Path(args.repo)
    try:
        anchor = rev_parse(repo, args.anchor + "^{commit}")
        commit = rev_parse(repo, args.commit + "^{commit}")
    except Malformed as error:
        print(error)
        return 2
    if anchor == commit:
        print(f"refused: the anchor {anchor[:12]} is the candidate itself; a commit never anchors its own "
              "verification (name an already-landed proper ancestor)")
        return 2
    if not git_ok(repo, "merge-base", "--is-ancestor", anchor, commit):
        print(f"refused: the anchor {anchor[:12]} is not an ancestor of {commit[:12]}")
        return 2
    anchored = show_blob(repo, anchor, "scripts/soundness_attestation.py")
    passthrough = ["verify", commit, "--repo", str(repo), "--anchor", anchor]
    if args.landing:
        passthrough.append("--landing")
    for leg in args.accept_removed_legs:
        passthrough += ["--accept-removed-legs", leg]
    if args.require_signature:
        passthrough.append("--require-signature")
    if anchored is None:
        if not args.allow_unanchored_bootstrap:
            print(f"refused: UNANCHORED: anchor {anchor[:12]} carries no scripts/soundness_attestation.py, so no "
                  "verifier outside the candidate exists (--allow-unanchored-bootstrap runs the candidate's own, "
                  "labelled UNANCHORED)")
            return 2
        print(f"UNANCHORED (bootstrap): anchor {anchor[:12]} carries no scripts/soundness_attestation.py, so "
              "this candidate is judged by its OWN verifier; this is not an anchored attestation")
        return cmd_verify(build_parser().parse_args(passthrough))
    with tempfile.TemporaryDirectory() as temporary:
        tool = Path(temporary) / "scripts" / "soundness_attestation.py"
        tool.parent.mkdir()
        tool.write_text(anchored)
        matrix = show_blob(repo, anchor, "scripts/matrix_results.py")
        if matrix is not None:
            (tool.parent / "matrix_results.py").write_text(matrix)
        print(f"anchored: verifier from {anchor[:12]} (blob {blob_id(repo, anchor, 'scripts/soundness_attestation.py')})")
        sys.stdout.flush()
        return subprocess.call([sys.executable, "-I", str(tool), *passthrough])


def cmd_deferred_classes(args) -> int:
    """Print this verifier's landing deferral as JSON ({} when none). The hook
    and the train ask the ANCHOR's verifier, to choose a portable landing run."""
    print(json.dumps(DEFERRED_LANDING_CLASSES, sort_keys=True))
    return 0


def landing_exception(repo: Path, anchor_spec: str) -> tuple[bool, list[str]]:
    """Whether the interim main-push exception is still in force at `anchor`.

    The exception (OD-LANDING-X86-DEFERRAL-20261008, replacing the 2026-09-27
    owner exception) lets a main push bypass the gate only while no commit can
    be attested for landing. Conservatively, it ENDS at the first commit on the
    anchor's history (the anchor included) carrying a record ref. Do not replay
    historical records under today's verifier to decide whether bypassing is
    allowed: withdrawing a deferral or strengthening a schema must never revive
    the exception. Presence is NOT a successful attestation. Only records
    present in `repo` are read: the caller fetches refs/attest/soundness/*
    first. Records are unsigned, so a forged record can end the exception early
    (stricter), never extend it."""
    anchor = rev_parse(repo, anchor_spec + "^{commit}")
    if git(repo, "rev-parse", "--is-shallow-repository").strip() != "false":
        return False, ["UNDETERMINED: incomplete Git history cannot authorize the interim bypass"]
    out = git(repo, "for-each-ref", "--format=%(refname)", REF_PREFIX + "/")
    subjects = sorted({name[len(REF_PREFIX) + 1:].split("/", 1)[0] for name in out.splitlines()
                       if FULL_SHA.match(name[len(REF_PREFIX) + 1:].split("/", 1)[0])},
                      key=lambda subject: (subject != anchor, subject))  # the anchor first: usually the answer
    for subject in subjects:
        if not git_ok(repo, "cat-file", "-e", subject + "^{commit}"):
            return False, [f"UNDETERMINED: unavailable attestation subject {subject}; bypass refused"]
        ancestry = run(["git", "-C", str(repo), "merge-base", "--is-ancestor", subject, anchor], check=False)
        if ancestry.returncode == 1:
            continue
        if ancestry.returncode != 0:
            return False, [f"UNDETERMINED: cannot establish {subject}'s ancestry; bypass refused"]
        return False, [f"ENDED: {subject} on {anchor[:12]}'s history carries an attestation record ref; "
                       "every main push now needs an attestation (no --no-verify). "
                       "Record presence grants no landing or release verdict."]
    return True, [f"IN FORCE: no commit on {anchor[:12]}'s history carries an attestation record ref"]


def discovered_landing_exception(repo: Path, anchor_spec: str, remote: str) -> tuple[bool, list[str]]:
    """Authorize no bypass from the absence of unfetched local record refs.

    A retained record can already end the exception without network access.
    A positive answer additionally needs a successful fetch of the selected
    remote's main and ALL record refs, and an anchor matching its actual main.
    Never prune retained records: deletion elsewhere must not revive a bypass.
    This only discovers policy inputs; record presence grants no verdict.
    """
    in_force, lines = landing_exception(repo, anchor_spec)
    if not in_force:
        return False, lines
    if not remote or remote.startswith("-") or any(c in remote for c in "\x00\r\n"):
        return False, ["UNDETERMINED: invalid record-discovery remote; bypass refused"]
    try:
        named = run(["git", "-C", str(repo), "remote", "get-url", "--push", "--all", remote],
                    check=False, timeout=30)
        if named.returncode == 0:
            locations = named.stdout.decode("utf-8").splitlines()
            if len(locations) != 1 or not locations[0]:
                return False, ["UNDETERMINED: select one actual push location; bypass refused"]
            fetched_url = run(["git", "-C", str(repo), "remote", "get-url", remote],
                              check=False, timeout=30)
            # Retain ordinary tracking-ref refresh only when fetch and push
            # really use the same URL. A decoy fetch URL supplies no authority.
            selector = (remote if fetched_url.returncode == 0
                        and fetched_url.stdout.decode("utf-8").splitlines() == locations else locations[0])
        elif ":" in remote or "/" in remote:
            selector = remote  # an explicit push URL/path, including Git's hook argument
        else:
            return False, ["UNDETERMINED: record-discovery remote is not configured; bypass refused"]
        if not selector or selector.startswith("-") or any(c in selector for c in "\x00\r\n"):
            return False, ["UNDETERMINED: invalid actual push location; bypass refused"]
        fetched = run(["git", "-C", str(repo), "fetch", "--quiet", selector, "refs/heads/main",
                       f"{REF_PREFIX}/*:{REF_PREFIX}/*"], check=False, timeout=120)
    except (OSError, subprocess.SubprocessError, UnicodeError):
        return False, ["UNDETERMINED: record discovery failed; bypass refused"]
    if fetched.returncode != 0:
        return False, ["UNDETERMINED: cannot fetch main and all attestation refs from the selected remote; "
                       "bypass refused"]
    in_force, lines = landing_exception(repo, anchor_spec)
    if not in_force:
        return False, lines
    try:
        advertised = run(["git", "-C", str(repo), "ls-remote", "--refs", selector, "refs/heads/main"],
                         check=False, timeout=120)
        rows = advertised.stdout.decode("ascii").splitlines()
        fields = rows[0].split() if len(rows) == 1 else []
        if (advertised.returncode != 0 or len(fields) != 2 or not FULL_SHA.fullmatch(fields[0])
                or fields[1] != "refs/heads/main"):
            return False, ["UNDETERMINED: remote main discovery is incomplete; bypass refused"]
        actual_anchor = rev_parse(repo, anchor_spec + "^{commit}")
    except (OSError, subprocess.SubprocessError, UnicodeError, Malformed):
        return False, ["UNDETERMINED: remote main discovery failed; bypass refused"]
    if actual_anchor != fields[0]:
        return False, ["UNDETERMINED: the anchor is not the selected remote's current main; "
                       "refresh main and retry; bypass refused"]
    return True, [*lines, "Record refs and main were discovered from the selected remote; "
                  "this is not a landing or release verdict."]


def cmd_landing_exception(args) -> int:
    in_force, lines = discovered_landing_exception(Path(args.repo), args.anchor, args.remote)
    print("\n".join(lines))
    return 0 if in_force else 1


def cmd_fetch(args) -> int:
    repo = Path(args.repo)
    commit = rev_parse(repo, args.commit + "^{commit}")
    # Lazy, separate transport: the verifier extracted from an anchor still
    # works with only its own file and matrix_results.py, as before.
    transport = Path(__file__).with_name("github_transport.py")
    result = run([sys.executable, "-I", str(transport), "--repo", args.repo, "--remote", args.remote,
                  "records", "--subject", commit], check=False, timeout=300)
    if result.returncode != 0:
        print("fetch failed: " + result.stderr.decode(errors="replace").strip())
        return 1
    print(f"fetched {len(records_for(repo, commit))} record(s) for {commit}")
    return 0


def cmd_push(args) -> int:
    commit = rev_parse(Path(args.repo), args.commit + "^{commit}")
    if not records_for(Path(args.repo), commit):
        print(f"no local record for {commit}")
        return 1
    transport = Path(__file__).with_name("github_transport.py")
    result = run([sys.executable, "-I", str(transport), "--repo", args.repo, "--remote", args.remote,
                  "push-records", commit], check=False, timeout=300)
    if result.returncode != 0:
        print("push failed: " + result.stderr.decode(errors="replace").strip())
        return 1
    print(f"pushed the records of {commit} to {args.remote}")
    return 0


def cmd_show(args) -> int:
    repo = Path(args.repo)
    commit = rev_parse(repo, args.commit + "^{commit}")
    records = records_for(repo, commit)
    if not records:
        print(f"no record for {commit}")
        return 3
    for triple, oid in sorted(records.items()):
        record = load_record(repo, oid)
        legs = record.get("legs", [])
        print(f"{ref_name(commit, triple)} {oid} scope={record.get('scope')} "
              f"legs={sum(1 for leg in legs if leg.get('status') == 'PASS')}/{len(legs)} PASS")
    return 0


# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0], allow_abbrev=False)
    sub = parser.add_subparsers(dest="command", required=True)
    default_repo = str(Path(__file__).resolve().parents[1])

    p = sub.add_parser("host", help="print this host's identity")
    p.add_argument("--json", action="store_true")
    p.add_argument("--require-native-x86_64", action="store_true")
    p.set_defaults(func=cmd_host)

    p = sub.add_parser("check-env", help="apply the environment allowlist (preflight row)")
    p.add_argument("--checkout", required=True)
    p.add_argument("--explicit", action="append", default=[], help="a gate variable the caller set")
    p.add_argument("--effective", action="append", default=[], help="NAME=VALUE as the gate uses it")
    p.add_argument("--cargo-root", action="append", default=[],
                   help="a directory legs run Cargo under (its ancestors' .cargo/config files are checked)")
    p.add_argument("--caller", action="store_true",
                   help="classify a caller environment (census): report the names --attest would refuse")
    p.add_argument("--out")
    p.set_defaults(func=cmd_check_env)

    p = sub.add_parser("exec-scrubbed", help="re-execute a command with only the allowlisted environment")
    p.add_argument("--checkout", required=True)
    p.add_argument("argv", nargs=argparse.REMAINDER)
    p.set_defaults(func=cmd_exec_scrubbed)

    p = sub.add_parser("identities", help="record toolchain and executed-binary identities")
    p.add_argument("--repo", default=default_repo)
    p.add_argument("--scope", choices=SCOPES, required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--island-twin-rustc", help="the stock rustc ISLAND_TWIN_RUSTC names (wasm islands' twin)")
    p.set_defaults(func=cmd_identities)

    p = sub.add_parser("build", help="assemble a record directory from a finished run")
    p.add_argument("--repo", default=default_repo)
    p.add_argument("--commit", required=True)
    p.add_argument("--scope", choices=SCOPES, required=True)
    p.add_argument("--logdir", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--clean-bin")
    p.add_argument("--aterm", help="JSON file with the aterm dependency (rev, origin, vt_tables_sha256)")
    p.add_argument("--imported", action="append", help="TRIPLE=OID of an imported remote record")
    p.add_argument("--started-at")
    p.add_argument("--finished-at")
    p.set_defaults(func=cmd_build)

    p = sub.add_parser("write", help="write a record directory as refs/attest/soundness/<C>/<triple>")
    p.add_argument("--repo", default=default_repo)
    p.add_argument("--record-dir", required=True)
    p.add_argument("--sign", action="store_true", help="sign the record commit (commit-tree -S)")
    p.set_defaults(func=cmd_write)

    p = sub.add_parser("check-record", help="validate one record commit")
    p.add_argument("--repo", default=default_repo)
    p.add_argument("--record", required=True)
    p.add_argument("--commit", required=True)
    p.add_argument("--triple", required=True)
    p.add_argument("--scope", choices=SCOPES)
    p.add_argument("--require-signature", action="store_true")
    p.set_defaults(func=cmd_check_record)

    for name, func in (("verify", cmd_verify), ("verify-anchored", cmd_verify_anchored)):
        p = sub.add_parser(name, help="decide whether a commit is attested")
        p.add_argument("commit")
        p.add_argument("--repo", default=default_repo)
        p.add_argument("--anchor", required=(name == "verify-anchored"),
                       help="an already-landed ancestor whose inventory C must not shrink")
        p.add_argument("--accept-removed-legs", action="append", default=[],
                       help="a leg id the anchor has and C deliberately removed")
        p.add_argument("--require-signature", action="store_true")
        p.add_argument("--landing", action="store_true",
                       help="the landing verdict: also accept a portable record while this verifier's "
                            "DEFERRED_LANDING_CLASSES names what it leaves out (never a release verdict)")
        if name == "verify-anchored":
            p.add_argument("--allow-unanchored-bootstrap", action="store_true",
                           help="with an anchor that predates this tool, run the candidate's own verifier "
                                "(labelled UNANCHORED)")
        p.set_defaults(func=func)

    p = sub.add_parser("deferred-classes", help="print DEFERRED_LANDING_CLASSES as JSON")
    p.set_defaults(func=cmd_deferred_classes)

    p = sub.add_parser("landing-exception",
                       help="exit 0 while the interim main-push exception is in force at --anchor, 1 once it ended")
    p.add_argument("--repo", default=default_repo)
    p.add_argument("--anchor", required=True, help="the remote main a push would replace")
    p.add_argument("--remote", default="origin",
                   help="record/main discovery push remote or location (default: origin)")
    p.set_defaults(func=cmd_landing_exception)

    for name, func in (("fetch", cmd_fetch), ("push", cmd_push)):
        p = sub.add_parser(name, help=f"{name} refs/attest/soundness/<C>/*")
        p.add_argument("commit")
        p.add_argument("--repo", default=default_repo)
        p.add_argument("--remote", default="origin")
        p.set_defaults(func=func)

    p = sub.add_parser("show", help="print the records of a commit")
    p.add_argument("commit")
    p.add_argument("--repo", default=default_repo)
    p.set_defaults(func=cmd_show)
    return parser


# Git's repository-local environment variables (environment.c local_repo_env,
# what `git rev-parse --local-env-vars` prints), as a FIXED superset over the
# git versions the gate supports (2.31, which added GIT_CONFIG_COUNT, through
# 2.47; the installed git's own list is checked against it by
# test_soundness_attestation). It is fixed, not asked of git, because this
# tool's `exec-scrubbed` runs before the host trust boundary has judged PATH,
# and no program may run before that (survey finding 7, R3 of
# OD-XHOST-GIT-PROGRAM-KEYS-20261024): the git first on PATH had run here with
# the caller's environment.
GIT_LOCAL_ENVIRONMENT = (
    "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_CONFIG", "GIT_CONFIG_PARAMETERS", "GIT_CONFIG_COUNT",
    "GIT_OBJECT_DIRECTORY", "GIT_DIR", "GIT_WORK_TREE", "GIT_IMPLICIT_WORK_TREE", "GIT_GRAFT_FILE",
    "GIT_INDEX_FILE", "GIT_NO_REPLACE_OBJECTS", "GIT_REPLACE_REF_BASE", "GIT_PREFIX", "GIT_SHALLOW_FILE",
    "GIT_COMMON_DIR",
)


def isolate_git_environment() -> None:
    """Drop Git's repository-local variables (GIT_DIR, GIT_WORK_TREE, ...).

    A pre-push hook runs with GIT_DIR exported, and those variables override
    even `git -C`, so every query below would read the pushing repository
    instead of the one named by --repo. The fixed GIT_LOCAL_ENVIRONMENT is
    used, so this runs no program (R3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024);
    scripts/soundness_check.sh isolate_git_repository_environment, which runs
    after the host trust boundary, still asks git.
    """
    for name in GIT_LOCAL_ENVIRONMENT:
        os.environ.pop(name, None)


def main(argv: Optional[list[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        isolate_git_environment()
        return args.func(args)
    except Refused as error:
        print(f"refused: {error}")
        return 1
    except Malformed as error:
        print(f"malformed: {error}")
        return 2
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(f"soundness_attestation: {type(error).__name__}: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
