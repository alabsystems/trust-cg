#!/usr/bin/env python3
"""Re-run the certificates behind the x86-64 vector-compare cells.

    scripts/check_x86_icmp_certificates.py                 # the gate
    scripts/check_x86_icmp_certificates.py --skip-missing-toolchain
    scripts/check_x86_icmp_certificates.py tools-path      # obtain the rule's AY and Clean only
    scripts/check_x86_icmp_certificates.py --queries DIR   # re-run a supplied dump: never a PASS

trust-ir's per-cell rule for x86-64 vector compares (`docs/dialects.md`,
"Vector compares on x86-64 follow one per-cell rule"; its one reader is
`trust_ir::chc_x86_vector_icmp_cell_status`, and
`trust_ir::chc_x86_vector_icmp_cell_ground` is its projection onto the
ground) admits an available `chc_x86` `icmp.<op>` cell on exactly one of two
grounds:

(a) INSTRUCTION MODEL (`icmp.eq`, `icmp.sgt`): one instruction whose model IS
    the predicate, so this backend's obligation is degenerate and its query is
    `(assert false)`; no certificate is claimed;
(b) CERTIFICATE (every other available cell): on the cell's exact
    non-degenerate query, the AY that `trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE`
    names answered `unsat` under `--strict-proofs` with an Alethe proof that
    the Clean the rule names accepts in full.

THE RULE IS CODE. This gate reads `CHC_X86_ICMP_CERTIFICATE_RULE` and each
cell's ground from the trust-ir this checkout compiles against:
`examples/x86_icmp_certificate_queries.rs` (schema
`trust-cg.x86-icmp-cell-queries.v2`) writes both into its manifest. No prose
is parsed, and no ground is re-derived here.

1. Every cell's query bytes are regenerated from the code (`targo
   --unverified run -p trust-cg-verify --example x86_icmp_certificate_queries`,
   which reads the same table `tests/x86_icmp_manifest_cells.rs` reads), with
   the rule (`read_certificate_rule`: a malformed rule, or one that no longer
   requires `--strict-proofs`, `unsat` and `fully verified`, is
   `rule-unreadable`);
2. the AY this checkout's `Cargo.lock` pins must be the rule's `ay.rev`
   (`ay-pin-differs-from-rule`): moving either alone re-certifies nothing;
3. both tools are built BY REVISION, one function (`obtain_build`): a `git
   archive` export of the rule's `ay.rev` / `clean.rev` (AY with its export's
   checked-in `.cargo/config.toml` retained,
   `CARGO_PROFILE_RELEASE_LTO=false` and `AY_SOURCE_GIT_COMMIT`; Clean with
   its export's own config; both with the disclosed clock-only manifest
   adaptation below), `SOURCE_DATE_EPOCH` the commit time, built by
   `targo --unverified build --release --locked <build_args>` (no proof claim
   about either build) into a cache keyed by revision and recipe (`--cache-dir`, default
   `<cache>/trust-cg/ay-cli`; `--clean-cache-dir`, default
   `<cache>/trust-cg/clean-cli`; `<cache>` an absolute `$XDG_CACHE_HOME`,
   else `$HOME/.cache`: the one user-cache rule of scripts/private_cache.py
   and trust-cg, so an empty or relative XDG_CACHE_HOME is ignored, and with
   neither absolute there is no default and the gate fails
   `<tool>-cache-not-private`). A cold build runs under the machine-wide admission gate
   of the rule's Clean, `scripts/heavy_gate.sh run
   auto:x86-icmp-<tool>-build-cold:40` exported from
   `clean.rev` (the actual C6 Clean cold build peaked at 26.58 GiB), so it waits
   for, and is counted against, every heavy job on the host; certification
   starts only after both binaries exist. A build still running (or still
   queued) after `BUILD_TIMEOUT_SECONDS`, or one the gate is interrupted
   during, is stopped with its whole process tree (`run_admitted_build`), so
   no build outlives the admission that counted it. The binary's sha256 is
   recorded at build time; a later run re-hashes it and refuses a cached
   binary whose bytes changed (`<tool>-cache-tampered`). Builds of one
   revision are not byte-identical, so the digest is recorded, not required:
   the report says whether it is one of the rule's `certifying_sha256`
   (`certifying_bytes`). The AY banner names its revision. Clean accepts the
   exact legacy version, that version with the full rule revision, or its
   source-owned literal unknown-provenance suffix for an archive. Unknown stays
   unknown; the exact export and build recipe bind its source. The caches
   follow trust-cg's private-cache rule (scripts/private_cache.py): every
   directory created in them is 0700 and every file 0600 (the binary 0500)
   whatever the umask, the build runs under umask 077, and nothing that exists
   is changed. The identity record sits beside the binary, so it binds the
   bytes only while no other user can write the slot: a cache directory with
   an ancestor another user may rename entries in, or a slot, binary or record
   another user may write, is refused (`<tool>-cache-not-private`), never
   repaired;
   A tool's unverified build may adapt a root `[trust]` table containing ONLY
   retired positive-integer `function_budget_ms` / `timeout_ms` keys (AY also
   admits the retired seconds-named `compiler_timeout_secs`).
   It removes those isolated assignments in the private export, checks every
   other TOML value for equality, and records original/derived manifest hashes
   and removed values. Compound policies and ambiguous syntax refuse. No
   milliseconds-to-effort conversion, source/dependency/feature/config/lock
   change or proof-policy change is made. The checker is still built with
   verification OFF; no verified-build claim follows. Each v2 recipe has a
   separate cache slot and requires that receipt; old slots are left intact.
   Memory weights use the maintained cold-only auto estimator per tool, with
   a 40 GiB first-build fallback. Successful measured runs can lower it; failed
   pre-build refusals cannot. Warm binary hits never enter that class;
4. coverage (`coverage_findings`): every reader cell exactly once, each with a
   ground trust-ir answers (`ground-unknown` otherwise), fail-closed exactly
   when the reader says so, an instruction-model query degenerate with no pin,
   a certificate query non-degenerate with exactly one pin and its single
   assertion stating trust-ir's spec side verbatim (`(assert (not (= <spec>
   ...`, else `spec-not-trust-ir-statement`; this pins that the query's
   simplification passes the spec through, not the spec's provenance, which
   `tests/x86_icmp_manifest_cells.rs` holds), a fail-closed cell with no pin;
   and every certificate query's sha256 the pinned digest
   (`query-digest-mismatch`);
5. per certificate cell, AY with the rule's `ay_args` must answer exactly one
   `ay_verdict` (trust-cg's `ay_stdout_is_exact_unsat` contract) and print
   exactly one `c ay.proof.certificate` report with the rule's
   `ay_certificate_report` fields, and the proof must carry none of the rule's
   `unchecked_proof_rules` (`proof-hole`, `proof-unchecked-rule`);
6. Clean with the rule's `clean_args` must EXIT 0, the machine verdict
   (`cert verify-external` exits non-zero on a proof it does not verify in
   full), and, as a second check, print the `Proof status: <clean_proof_status>`
   line (`clean_alethe_stdout_is_fully_verified`).

Each failure is a named finding. Missing toolchain INPUTS (no targo, no AY or
Clean source repository that has the revision) FAIL the gate unless
`--skip-missing-toolchain` is given, which turns exactly those into a stated
SKIP (exit 3); a wrong input (another AY revision, a changed cached binary, a
wrong banner) is never skippable.

A SUPPLIED dump is never a verdict. `--queries DIR` re-runs the
certificates of a dump the caller supplies (one kept by `--keep-work`, say)
instead of regenerating it, and then the rule, the grounds and the pins are
read from `DIR/manifest.json`, which any writer of `DIR` controls, not from
the compiled trust-ir. Such a run reports every finding as usual, but without
one it exits 4 and says `SUPPLIED-DUMP`, never `PASS`, and its report records
`queries.source = "supplied"`; `tools-path` refuses `--queries` (it obtains
the compiled rule's tools).

Exit status: 0 pass; 1 a finding; 2 usage; 3 explicitly skipped; 4 a supplied
dump re-run without a finding (not a pass).

What a pass is, and what it trusts. A pass is an SMT proof that AY `ay.rev`
produced for each cell's exact query, which the Carcara Alethe checker inside
Clean `clean.rev`'s `cert verify-external` accepted in full: exit 0, no
`hole`, no `lia_generic`. It is a checked SMT proof, not a kernel certificate
and not a Lean theorem. It trusts (1) that checker: vendored Carcara with
Clean's downstream soundness fixes, which is unverified software with a
documented record of false accepts, built by `targo --unverified` into bytes
that are not reproducible. (2) The SMT encoding of the trust-ir predicate,
the spec side: since this backend states it through trust-ir's own statement
(`trust_ir::chc_x86_vector_icmp_spec`, printed by `SmtAlgebra`), what remains
trusted is that statement's tie to trust-ir's `ICmp` semantics, which trust-ir
holds by tests, not by proof. (3) This backend's SMT models of the x86
instructions, the machine side. It does not bind the obligation to the
instructions ISel emits for a given compile. It runs only when this script (or
the soundness leg that calls it) is run; nothing runs it per landing. The
eight instruction-model cells stay trusted base.
"""

from __future__ import annotations

import argparse
from collections import deque
import concurrent.futures
import ctypes
import datetime
import errno
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import time
import tomllib
from typing import Callable, Iterable, NamedTuple, Optional

ROOT = Path(__file__).resolve().parents[1]


def _load_private_cache():
    """scripts/private_cache.py, by path: `python3 -I` puts no script directory
    on sys.path, and none is added (a file there must never shadow a module)."""
    spec = importlib.util.spec_from_file_location("private_cache", Path(__file__).resolve().parent / "private_cache.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


private_cache = _load_private_cache()


def _load_resource_transport():
    """Reuse the canonical pin owner's numeric transport without adding sys.path."""
    name = "trust_cg_certificate_pin_resources"
    spec = importlib.util.spec_from_file_location(
        name, Path(__file__).resolve().parent / "bump_trust_ir_pin.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    # Dataclass annotation resolution needs its actual defining module.
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


pin_resources = _load_resource_transport()
SCHEMA = "trust-cg.x86-icmp-certificates.v2"
QUERY_MANIFEST_SCHEMA = "trust-cg.x86-icmp-cell-queries.v2"
CACHE_SCHEMAS = {"ay": "trust-cg.ay-cli-build.v3", "clean": "trust-cg.clean-cli-build.v2"}
EXPORT_SCHEMAS = {"ay": "trust-cg.ay-unverified-export.v1", "clean": "trust-cg.clean-unverified-export.v1"}
RETIRED_CLOCK_KEYS = {
    "clean": frozenset(("function_budget_ms", "timeout_ms")),
    "ay": frozenset(("function_budget_ms", "timeout_ms", "compiler_timeout_secs")),
}
REMOVED_CLOCK_FIELDS = {"clean": "removed_legacy_clock_ms", "ay": "removed_legacy_clock_settings"}
AY_CACHE_SCHEMA = CACHE_SCHEMAS["ay"]
SOURCE_ENVIRONMENT = {"ay": "AY_SOURCE_DIR", "clean": "CLEAN_SOURCE_DIR"}
EXAMPLE = "x86_icmp_certificate_queries"
EXIT_PASS, EXIT_FAIL, EXIT_USAGE, EXIT_SKIPPED, EXIT_SUPPLIED = 0, 1, 2, 3, 4
GROUNDS = ("instruction-model", "certificate", "fail-closed")
# The machine-wide reservation of one cold tool build: a cold Clean checker
# build peaked at 9.79 GB here against 8 reserved (heavy_gate: UNDER-RESERVED),
# so 12 leaves about 20% headroom.
# Actual C6 Clean cold build peaked at 26.58 GiB. The maintained auto estimator
# learns only from cold builds, never warm cache hits or pre-build refusals.
# Use a conservative 40 GiB first-build fallback for each compiler-built tool.
TOOL_BUILD_FALLBACK_GB = {"clean": 40, "ay": 40}

SHA1 = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
SEMVER = re.compile(r"\d+\.\d+\.\d+\Z")
AY_TIMEOUT_SECONDS = 600
CLEAN_TIMEOUT_SECONDS = 600
BUILD_TIMEOUT_SECONDS = 7200
QUERY_DUMP_TIMEOUT_SECONDS = 7200


class Finding(Exception):
    """A named reason the gate fails. Never skippable."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


class MissingInput(Exception):
    """A toolchain input that is absent (not wrong). Fails the gate unless the
    caller explicitly skips missing inputs."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def log(message: str) -> None:
    print(f"[x86-icmp-certificates] {message}", flush=True)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def tool_environment(extra: Optional[dict] = None) -> dict:
    """A minimal environment for AY and Clean: nothing a caller set can change
    what they decide (no AY_*/CLEAN_*/RUST* variable reaches them)."""
    env = {
        "PATH": "/usr/bin:/bin:/usr/sbin:/sbin",
        "HOME": os.environ.get("HOME", "/"),
        "TMPDIR": os.environ.get("TMPDIR", "/tmp"),
        "LANG": "C",
        "LC_ALL": "C",
    }
    if extra:
        env.update(extra)
    return env


def build_environment() -> dict:
    """The caller's environment without what trustc refuses (TRUST_CG_*/TCG_*)
    or what would change the build outside the recipe (flags, wrappers, a
    target directory, a rustup override)."""
    drop = {
        "RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_ENCODED_RUSTDOCFLAGS",
        "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTUP_TOOLCHAIN", "CARGO_TARGET_DIR",
        "CARGO_BUILD_TARGET_DIR", "CARGO_BUILD_RUSTFLAGS", "CARGO_BUILD_RUSTC_WRAPPER", "RUSTC",
    }
    return {
        key: value for key, value in os.environ.items()
        if key not in drop and not key.startswith(("TRUST_CG_", "TCG_", "CARGO_PROFILE_"))
    }


# ---------------------------------------------------------------------------
# The candidate's pins (Cargo.lock) and the rule (the compiled trust-ir).
# ---------------------------------------------------------------------------

def lock_git_revs(lock_text: str, repository: str) -> dict[str, set[str]]:
    """`{package: {rev}}` for every lock package sourced from `<org>/<repository>.git`."""
    found: dict[str, set[str]] = {}
    source = re.compile(r'^source = "git\+https://[^"]+/' + re.escape(repository)
                        + r'\.git\?rev=([0-9a-f]{40})#([0-9a-f]{40})"$')
    for block in lock_text.split("[[package]]")[1:]:
        name = re.search(r'^name = "([^"]+)"$', block, re.M)
        for line in block.splitlines():
            match = source.match(line.strip())
            if match and name:
                if match.group(1) != match.group(2):
                    raise Finding("lock-unreadable",
                                  f"{name.group(1)}: source rev {match.group(1)} resolves to {match.group(2)}")
                found.setdefault(name.group(1), set()).add(match.group(1))
    return found


def pinned_rev(lock_text: str, repository: str, package: str) -> str:
    """The one revision `package` (and every other package from the same
    repository) is pinned to in the lock."""
    revs = lock_git_revs(lock_text, repository)
    if package not in revs:
        raise Finding("lock-unreadable", f"Cargo.lock pins no `{package}` from {repository}.git")
    every = set().union(*revs.values())
    if len(every) != 1:
        raise Finding("lock-ambiguous",
                      f"Cargo.lock pins {repository}.git at {len(every)} revisions ({', '.join(sorted(every))})")
    return next(iter(every))


class Tool(NamedTuple):
    """One certifying tool as the rule names it (`ChcX86IcmpCertifyingBuild`).
    A NamedTuple, not a dataclass: the tests load this file by path without
    registering it in `sys.modules`, which a dataclass needs."""

    package: str
    rev: str
    version: str
    build_args: tuple[str, ...]
    certifying_sha256: tuple[str, ...]

    @property
    def cache_schema(self) -> str:
        return CACHE_SCHEMAS[self.package]

    @property
    def cache_key(self) -> str:
        # A derived unverified-build recipe must not overwrite or masquerade as
        # an older exact-export build. The two tools have separate cache roots.
        recipe = 2 if self.package == "ay" else 1
        return f"{self.rev}-unverified-export-v{recipe}"


def _rule_unreadable(why: str) -> Finding:
    return Finding("rule-unreadable", f"the manifest's certificate_rule {why}")


def _string_list(value, what: str) -> list[str]:
    if not isinstance(value, list) or not value or not all(isinstance(item, str) and item for item in value):
        raise _rule_unreadable(f"has no non-empty string list `{what}`")
    return list(value)


def _rule_tool(block: dict, package: str) -> Tool:
    entry = block.get(package)
    if not isinstance(entry, dict):
        raise _rule_unreadable(f"names no `{package}` build")
    if entry.get("package") != package:
        raise _rule_unreadable(f"names package {entry.get('package')!r} as its `{package}` build")
    rev, version = entry.get("rev"), entry.get("version")
    if not isinstance(rev, str) or not SHA1.match(rev):
        raise _rule_unreadable(f"names no 40-hex `{package}.rev` ({rev!r})")
    if not isinstance(version, str) or not SEMVER.match(version):
        raise _rule_unreadable(f"names no `{package}.version` ({version!r})")
    build_args = _string_list(entry.get("build_args"), f"{package}.build_args")
    if ["-p", package] != build_args[:2]:
        raise _rule_unreadable(f"`{package}.build_args` {build_args} do not start `-p {package}`")
    digests = _string_list(entry.get("certifying_sha256"), f"{package}.certifying_sha256")
    if not all(SHA256.match(digest) for digest in digests):
        raise _rule_unreadable(f"`{package}.certifying_sha256` holds a value that is not a sha256")
    return Tool(package, rev, version, tuple(build_args), tuple(digests))


def read_certificate_rule(manifest: dict) -> dict:
    """`trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE` as the query dump wrote it from
    the compiled trust-ir, shape-checked: a block that is malformed, or that no
    longer requires `--strict-proofs`, `unsat` and `fully verified`, is
    `rule-unreadable`."""
    block = manifest.get("certificate_rule")
    if not isinstance(block, dict):
        raise _rule_unreadable("is missing")
    ay, clean = _rule_tool(block, "ay"), _rule_tool(block, "clean")
    ay_args = _string_list(block.get("ay_args"), "ay_args")
    if ay_args.count("{query}") != 1 or ay_args.count("{proof}") != 1:
        raise _rule_unreadable(f"`ay_args` {ay_args} do not name `{{query}}` and `{{proof}}` once each")
    if "--strict-proofs" not in ay_args:
        raise _rule_unreadable(f"`ay_args` {ay_args} no longer require `--strict-proofs`")
    if block.get("ay_verdict") != "unsat":
        raise _rule_unreadable(f"`ay_verdict` is {block.get('ay_verdict')!r}, not `unsat`")
    report = block.get("ay_certificate_report")
    if not isinstance(report, list) or not report or not all(
            isinstance(pair, list) and len(pair) == 2 and all(isinstance(part, str) and part for part in pair)
            for pair in report):
        raise _rule_unreadable("has no `ay_certificate_report` list of [field, value] pairs")
    fields = dict((field, value) for field, value in report)
    if len(fields) != len(report):
        raise _rule_unreadable("`ay_certificate_report` names a field twice")
    unchecked = _string_list(block.get("unchecked_proof_rules"), "unchecked_proof_rules")
    if "hole" not in unchecked:
        raise _rule_unreadable(f"`unchecked_proof_rules` {unchecked} no longer refuse `hole`")
    clean_args = _string_list(block.get("clean_args"), "clean_args")
    if clean_args.count("{certificate}") != 1:
        raise _rule_unreadable(f"`clean_args` {clean_args} do not name `{{certificate}}` once")
    if block.get("clean_proof_status") != "fully verified":
        raise _rule_unreadable(f"`clean_proof_status` is {block.get('clean_proof_status')!r}, not `fully verified`")
    return {"ay": ay, "clean": clean, "ay_args": ay_args, "ay_verdict": "unsat",
            "ay_certificate_report": fields, "unchecked_proof_rules": unchecked, "clean_args": clean_args,
            "clean_proof_status": "fully verified"}


def rule_summary(rule: dict) -> dict:
    """The rule, JSON-serializable, for the report."""
    def tool(item: Tool) -> dict:
        return {"package": item.package, "rev": item.rev, "version": item.version,
                "build_args": list(item.build_args), "certifying_sha256": list(item.certifying_sha256)}
    return dict({key: value for key, value in rule.items() if key not in ("ay", "clean")},
                ay=tool(rule["ay"]), clean=tool(rule["clean"]))


def require_rule_ay(ay_rev: str, rule: dict, trust_ir_rev: str) -> None:
    """The AY this checkout pins must be the AY the rule's certificates name:
    moving either alone re-certifies nothing (trust-ir's gate-7 test holds the
    rule's AY equal to trust-ir's own AY pin)."""
    if ay_rev != rule["ay"].rev:
        raise Finding("ay-pin-differs-from-rule",
                      f"Cargo.lock pins ay {ay_rev}, the rule at trust-ir {trust_ir_rev[:12]} names the certifying "
                      f"AY {rule['ay'].rev}; re-certify under the new AY and move the rule, or keep the pins equal")


# ---------------------------------------------------------------------------
# AY and Clean: exactly the revisions the rule names, built once per revision.
# ---------------------------------------------------------------------------

def cargo_home() -> Path:
    return Path(os.environ.get("CARGO_HOME") or Path.home() / ".cargo")


def git_dirs_with(rev: str, candidates: Iterable[Path]) -> list[Path]:
    """The git directories (work trees or bare) among `candidates` that hold `rev`."""
    held = []
    for candidate in candidates:
        if not candidate.exists():
            continue
        probe = subprocess.run(["git", "-C", str(candidate), "cat-file", "-e", f"{rev}^{{commit}}"],
                               capture_output=True)
        if probe.returncode == 0:
            held.append(candidate)
    return held


def source_candidates(package: str, explicit: Optional[Path]) -> list[Path]:
    if explicit is not None:
        return [explicit]
    named = os.environ.get(SOURCE_ENVIRONMENT[package])
    return (([Path(named)] if named else [Path.home() / package])
            + sorted((cargo_home() / "git" / "db").glob(f"{package}-*")))


def source_with(package: str, rev: str, explicit: Optional[Path]) -> Path:
    candidates = source_candidates(package, explicit)
    held = git_dirs_with(rev, candidates)
    if held:
        return held[0]
    # Use the soundness gate's exact-pin transport on the original source;
    # never fall back to raw GitHub Git or accept a failed fetch's output.
    for candidate in candidates:
        if (candidate / ".git").exists():
            transport = Path(__file__).with_name("github_transport.py")
            result = subprocess.run([sys.executable, "-I", str(transport), "--repo", str(candidate),
                                     "--remote", "origin", "pin", rev], capture_output=True)
            if result.returncode == 0 and git_dirs_with(rev, [candidate]):
                return candidate
            break
    raise MissingInput(f"{package}-source-missing",
                       f"no {package} repository among {', '.join(map(str, candidates))} has commit {rev}")


def ay_source_with(rev: str, explicit: Optional[Path]) -> Path:
    return source_with("ay", rev, explicit)


def unverified_tool_export(original: bytes, package: str) -> tuple[bytes, dict]:
    """Adapt only an obsolete clock-only policy in a private tool export.

    The checker is deliberately built with verification OFF. There is no
    conversion from old milliseconds to current solver effort, no acceptance
    of unknown policy, and no edit to a source repository. Rust, dependencies,
    features, profiles, lockfile and compiler refusals are not changed.
    """
    try:
        text = original.decode("utf-8")
        document = tomllib.loads(text)
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        raise Finding(f"{package}-export-policy-unrecognized", str(error)) from error
    policy = document.get("trust", {})
    retired_keys = RETIRED_CLOCK_KEYS[package]
    removed = {key: policy[key] for key in sorted(retired_keys) if key in policy} \
        if isinstance(policy, dict) else {}
    derived = original
    if removed:
        # This deliberately does not migrate an active/compound policy. Such a
        # revision needs an explicit new recipe or an authority pin transaction.
        if set(policy) != set(removed) or any(type(value) is not int or not 0 < value < 2**64
                                              for value in removed.values()):
            raise Finding(f"{package}-export-policy-unrecognized",
                          "only a clock-only [trust] table with positive integer retired budgets can be adapted")
        lines, counts, in_policy = [], dict.fromkeys(removed, 0), False
        for line in text.splitlines(keepends=True):
            if line.lstrip(" \t").startswith("["):
                in_policy = re.fullmatch(r"[ \t]*\[trust\][ \t]*(?:#[^\r\n]*)?(?:\r?\n)?", line) is not None
            match = re.fullmatch(
                r"[ \t]*(function_budget_ms|timeout_ms|compiler_timeout_secs)[ \t]*=[ \t]*([0-9][0-9_]*)[ \t]*"
                r"(?:#[^\r\n]*)?(?:\r?\n)?", line,
            ) if in_policy else None
            if match and match[1] in removed and int(match[2].replace("_", "")) == removed[match[1]]:
                counts[match[1]] += 1
            else:
                lines.append(line)
        derived = "".join(lines).encode("utf-8")
        expected = dict(document, trust={})
        try:
            actual = tomllib.loads(derived.decode("utf-8"))
        except tomllib.TOMLDecodeError as error:
            raise Finding(f"{package}-export-policy-unrecognized", str(error)) from error
        if any(count != 1 for count in counts.values()) or actual != expected:
            raise Finding(f"{package}-export-policy-unrecognized",
                          "cannot isolate the retired policy assignments without changing other manifest values")
    return derived, {
        "schema": EXPORT_SCHEMAS[package], "manifest": "Cargo.toml",
        "original_sha256": hashlib.sha256(original).hexdigest(),
        "build_sha256": hashlib.sha256(derived).hexdigest(),
        REMOVED_CLOCK_FIELDS[package]: removed,
    }


def valid_tool_export_record(record: object, package: str) -> bool:
    """Version-two cache records must disclose the derived manifest recipe."""
    removed_field = REMOVED_CLOCK_FIELDS[package]
    if not isinstance(record, dict) or set(record) != {
            "schema", "manifest", "original_sha256", "build_sha256", removed_field}:
        return False
    removed = record[removed_field]
    return record["schema"] == EXPORT_SCHEMAS[package] and record["manifest"] == "Cargo.toml" \
        and all(isinstance(record[key], str) and re.fullmatch(r"[0-9a-f]{64}", record[key])
                for key in ("original_sha256", "build_sha256")) \
        and isinstance(removed, dict) and set(removed) <= RETIRED_CLOCK_KEYS[package] \
        and all(type(value) is int and 0 < value < 2**64 for value in removed.values()) \
        and (record["original_sha256"] != record["build_sha256"]) == bool(removed)


def tool_banner(binary: Path) -> str:
    result = subprocess.run([str(binary), "--version"], capture_output=True, text=True,
                            env=tool_environment(), timeout=120)
    return (result.stdout or result.stderr).strip().splitlines()[0] if (result.stdout or result.stderr) else ""


def banner_names(banner: str, rev: str, version: str) -> bool:
    """`ay <version>+build.<n>.<commit>@<date>` naming exactly `rev`."""
    match = re.match(r"^ay (\d+\.\d+\.\d+)\+build\.(\d+)\.([0-9a-f]{40})@", banner)
    return bool(match) and match.group(1) == version and match.group(3) == rev


def banner_is_the_rules(tool: Tool, banner: str) -> bool:
    """Exact source-owned spellings; an archive's unknown label is not identity."""
    if tool.package == "ay":
        return banner_names(banner, tool.rev, tool.version)
    prefix = f"{tool.package} {tool.version}"
    return banner in {
        prefix,
        prefix + "+g" + tool.rev,
        prefix + " (git sha unknown: built without git provenance)",
    }


def resolve_targo() -> Path:
    # -I: no user site-packages or .pth file (OD-XHOST-GATE-CWD-20261025).
    # Ordinary library/tool builds do not link rustc_private. Use the existing
    # workspace purpose; compiler/sysroot/brand/host identity remains mandatory.
    result = subprocess.run([sys.executable, "-I", "-B", str(ROOT / "scripts" / "trust_toolchain.py"),
                             "--purpose", "workspace", "--print", "targo"],
                            capture_output=True, text=True, env=build_environment())
    if result.returncode != 0 or not result.stdout.strip():
        raise MissingInput("targo-missing",
                           "no installed Trust package resolves (scripts/trust_toolchain.py): "
                           + (result.stderr.strip() or "no output"))
    return Path(result.stdout.strip())


def commit_time(repo: Path, rev: str) -> str:
    return subprocess.run(["git", "-C", str(repo), "show", "-s", "--format=%ct", rev],
                          capture_output=True, text=True, check=True).stdout.strip()


def export_tree(repo: Path, rev: str, destination: Path, paths: tuple[str, ...] = ()) -> None:
    """`git archive` of `rev` (only `paths`, when given) extracted into
    `destination`, with owner-only modes (`tar.umask=0077`)."""
    archive = destination.parent / f"{destination.name}.tar"
    with open(archive, "wb") as handle:
        subprocess.run(["git", "-C", str(repo), "-c", "tar.umask=0077", "archive", "--format=tar", rev, *paths],
                       stdout=handle, check=True)
    with tarfile.open(archive) as tar:
        tar.extractall(destination)
    archive.unlink()


# `admission(tool, label, work)` returns the prefix a cold build runs under.
Admission = Callable[[Tool, str, Path], list]


def heavy_gate_admission(clean: Tool, clean_source: Optional[Path]) -> Admission:
    """The machine-wide admission of a cold tool build: the rule's Clean's own
    `scripts/heavy_gate.sh run auto:x86-icmp-<tool>-build-cold:40 <label> --`, exported by object from
    `clean.rev` into the build's work directory (the script and the weights
    file it sources). Its state (`/tmp/heavy_gate`) is machine-wide, so the
    build is counted against every heavy job on the host, and the script comes
    from the source the gate already builds its checker from. Separate cold-only
    classes learn from actual completed builds; cache hits cannot age out peaks."""

    def admit(tool: Tool, label: str, work: Path) -> list:
        repo = source_with("clean", clean.rev, clean_source)
        probe = subprocess.run(["git", "-C", str(repo), "cat-file", "-e", f"{clean.rev}:scripts/heavy_gate.sh"],
                               capture_output=True)
        if probe.returncode != 0:
            raise Finding("heavy-gate-missing", f"Clean {clean.rev} has no scripts/heavy_gate.sh to admit {label}")
        gate = work / "heavy-gate"
        gate.mkdir()
        export_tree(repo, clean.rev, gate, ("scripts",))
        script = gate / "scripts" / "heavy_gate.sh"
        phase = "resume" if label.startswith(f"x86-icmp-{tool.package}-resume-") else "cold"
        weight = f"auto:x86-icmp-{tool.package}-build-{phase}:{TOOL_BUILD_FALLBACK_GB[tool.package]}"
        return [str(script), "run", weight, label, "--"]

    return admit


def not_private(package: str, error: OSError, remedy: str) -> Finding:
    return Finding(f"{package}-cache-not-private", f"{error.strerror or error}; {remedy}")


def require_private_ancestry(cache_dir: Path, package: str = "ay") -> Path:
    """Refuse `cache_dir` unless no other user can rename entries in it or any
    ancestor: the tool is executed from inside it. Nothing is changed. Returns
    the canonical directory, which is what was checked: the caller uses it
    instead of `cache_dir`, which may lead there through a symlink in a
    directory others can write (re-pointable after the check)."""
    try:
        return Path(private_cache.canonical_owner_private_directory(cache_dir))
    except PermissionError as error:
        raise not_private(package, error, f"{package} is executed from {cache_dir}: run `chmod go-w` on the "
                                          "directory named, or name a cache directory (or XDG_CACHE_HOME) only you "
                                          "can write") from error


def require_private_cache_dir(cache_dir: Path, package: str = "ay") -> Path:
    """Create `cache_dir` by the private-cache rule (each new directory 0700;
    an existing one is never changed), then `require_private_ancestry`.
    Returns the canonical directory that rule checked."""
    private_cache.create_private_dir_all(cache_dir)
    return require_private_ancestry(cache_dir, package)


def require_private_slot(slot: Path, binary: Path, identity_file: Path, package: str = "ay") -> None:
    """The slot the tool is executed from (never a symlink), its binary and its
    identity record must be writable by no other user, and the cache directory
    holding the slot must pass `require_private_ancestry`: the record sits
    beside the binary it names. Read and execute bits are allowed (neither is
    secret), so a slot an earlier version of this script built under umask
    0022 (slot 0755, binary 0555, record 0644) is used as it is; one it built
    under umask 0002 (a group-writable slot and record) is refused. The slot
    must be named below the CANONICAL cache directory (`obtain_build` names
    it so), or the entries checked here are not the ones the ancestor rule
    vouched for."""
    canonical = require_private_ancestry(slot.parent, package)
    if canonical != slot.parent:
        raise Finding(f"{package}-cache-not-private",
                      f"{slot} is not named by its canonical cache directory {canonical}; the slot executed must be "
                      "the one the ancestor rule checked")
    try:
        private_cache.check_owner_only_writable(slot, True)
        private_cache.check_owner_only_writable(binary, False)
        private_cache.check_owner_only_writable(identity_file, False)
    except PermissionError as error:
        raise not_private(package, error, f"so the identity record cannot vouch for the binary beside it; delete "
                                          f"{slot} to rebuild (a cold build takes ten to twenty minutes)") from error


def obtain_build(tool: Tool, cache_dir: Path, source: Optional[Path], keep_build: bool,
                 admission: Admission, resume_work: Optional[Path] = None) -> dict:
    """The cached build of `tool` at its revision, building it on a miss
    (under `admission`). Returns its identity record, with `path`: the binary
    to execute, named below the CANONICAL cache directory the privacy rule
    checked. Everything here (lock, slot, build, binary) is named below that
    canonical directory, never below `cache_dir` itself, which may lead there
    through a symlink in a directory others can write: re-pointed after the
    check, it would hand the caller a binary nothing checked (X-HOST-P13
    third closure audit)."""
    package = tool.package
    cache_dir = require_private_cache_dir(cache_dir, package)
    slot = cache_dir / tool.cache_key
    identity_file = slot / "identity.json"
    binary = slot / package
    with os.fdopen(private_cache.open_lock_file(cache_dir / f"{tool.rev}.lock"), "r+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if identity_file.exists():
            if resume_work is not None:
                raise Finding(f"{package}-resume-already-published", "use the normal verified warm cache hit")
            if not binary.is_file():
                raise Finding(f"{package}-cache-tampered", f"{identity_file} names a binary that is gone: {binary}")
            require_private_slot(slot, binary, identity_file, package)
            identity = json.loads(identity_file.read_text())
            digest = sha256_file(binary)
            if identity.get("schema") != tool.cache_schema or identity.get("rev") != tool.rev \
                    or identity.get("sha256") != digest:
                raise Finding(f"{package}-cache-tampered",
                              f"{binary} has sha256 {digest}; its build record names {identity.get('sha256')} "
                              f"for rev {identity.get('rev')} (delete {slot} to rebuild)")
            recipe = identity.get("recipe")
            if not isinstance(recipe, dict) \
                    or recipe.get("command") != ["--unverified", "build", "--release", "--locked", *tool.build_args] \
                    or not valid_tool_export_record(recipe.get("unverified_export"), package) \
                    or (package == "ay" and recipe.get("cargo_config") != "export's own .cargo/config.toml"):
                raise Finding(f"{package}-cache-tampered", f"{identity_file} omits a valid unverified export recipe")
            if not banner_is_the_rules(tool, str(identity.get("banner", ""))):
                raise Finding(f"{package}-banner-mismatch",
                              f"the cached build of {package} {tool.rev} recorded `{identity.get('banner')}`, not "
                              f"{package} {tool.version}")
            identity.update(cache="warm", path=str(binary))
            return identity
        repo = source_with(package, tool.rev, source)
        targo = resolve_targo()
        # Everything the build writes under the cache (its work directory, the
        # export, Cargo's target directory, the slot) is created under umask
        # 077, and the export's entries carry 0600/0700 (tar.umask).
        with private_cache.private_umask():
            return build_tool(tool, cache_dir, slot, binary, identity_file, repo, targo,
                              keep_build, admission, resume_work=resume_work)


def export_entries(root: Path) -> dict:
    """Exact private source namespace, without following any exported symlink."""
    entries = {}
    for directory, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            path = Path(directory) / name
            relative = str(path.relative_to(root))
            info = path.lstat()
            mode = stat.S_IMODE(info.st_mode)
            if stat.S_ISLNK(info.st_mode):
                value = ("link", mode, os.readlink(path))
            elif stat.S_ISDIR(info.st_mode):
                value = ("dir", mode)
            elif stat.S_ISREG(info.st_mode):
                value = ("file", mode, sha256_file(path))
            else:
                raise Finding("resume-source-not-regular", f"unsupported source entry {relative}")
            entries[relative] = value
    return entries


def check_resumed_export(tool: Tool, cache_dir: Path, work: Path, repo: Path) -> dict:
    """Resume DATA is not a build receipt: authenticate it, then actually build."""
    if (not work.is_absolute() or work.parent != cache_dir
            or not work.name.startswith(f"build-{tool.rev[:12]}-")
            or require_private_ancestry(work, tool.package) != work):
        raise Finding(f"{tool.package}-resume-work-invalid", "resume must name this tool's private original work directory")
    for name in ("src", "target"):
        path = work / name
        if path.is_symlink() or not path.is_dir():
            raise Finding(f"{tool.package}-resume-work-invalid", f"{name} must be an original regular directory")
    try:
        target = work / "target"
        if Path(private_cache.require_private_tree(target)) != target:
            raise PermissionError("resume target is not canonical")
    except OSError as error:
        raise Finding(f"{tool.package}-resume-target-not-private", str(error)) from error
    with private_cache.private_umask(), tempfile.TemporaryDirectory(prefix="resume-source-", dir=work) as temporary:
        expected = Path(temporary) / "src"
        expected.mkdir()
        export_tree(repo, tool.rev, expected)
        manifest = expected / "Cargo.toml"
        derived, record = unverified_tool_export(manifest.read_bytes(), tool.package)
        manifest.write_bytes(derived)
        expected_entries, actual_entries = export_entries(expected), export_entries(work / "src")
        if expected_entries != actual_entries:
            changed = [name for name in sorted(expected_entries.keys() | actual_entries.keys())
                       if expected_entries.get(name) != actual_entries.get(name)]
            raise Finding(f"{tool.package}-resume-source-mismatch",
                          "retained export differs from exact immutable source and recipe: "
                          + ", ".join(changed[:8]))
        return record


def obtain_ay(rev: str, version: str, cache_dir: Path, source: Optional[Path], keep_build: bool,
              admission: Admission) -> dict:
    """`obtain_build` for AY `rev` at `version` with the certifying recipe's
    build arguments."""
    return obtain_build(Tool("ay", rev, version, ("-p", "ay", "--features", "cli"), ()), cache_dir, source,
                        keep_build, admission)


def darwin_child_pids(pid: int) -> list[int]:
    """Read child PIDs without executing macOS's setuid /bin/ps.

    proc_listchildpids takes a buffer size in bytes but returns a PID count.
    A full buffer is retried; an unavailable listing is never an empty tree.
    """
    library = ctypes.CDLL("/usr/lib/libproc.dylib", use_errno=True)
    listing = library.proc_listchildpids
    listing.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_int]
    listing.restype = ctypes.c_int
    capacity = 128
    while capacity <= 1048576:
        buffer = (ctypes.c_int * capacity)()
        ctypes.set_errno(0)
        count = listing(pid, buffer, ctypes.sizeof(buffer))
        error = ctypes.get_errno()
        if count < 0 or (count == 0 and error not in (0, errno.ESRCH)):
            raise OSError(error or errno.EIO, "cannot list process children")
        if count < capacity:
            return [child for child in buffer[:count] if child > 0]
        capacity *= 2
    raise OSError(errno.EOVERFLOW, "process child listing did not fit")


def descendants(pid: int) -> list[int]:
    """Every live descendant, using libproc on macOS or a ps parent listing."""
    if sys.platform == "darwin":
        found, frontier, seen = [], [pid], {pid}
        while frontier:
            children = []
            for parent in frontier:
                for child in darwin_child_pids(parent):
                    if child not in seen:
                        seen.add(child)
                        children.append(child)
            found.extend(children)
            frontier = children
        return found
    listing = subprocess.run(["ps", "-A", "-o", "pid=,ppid="], capture_output=True, text=True,
                             check=True)
    children: dict[int, list[int]] = {}
    for line in listing.stdout.splitlines():
        fields = line.split()
        if len(fields) == 2 and fields[0].isdigit() and fields[1].isdigit():
            children.setdefault(int(fields[1]), []).append(int(fields[0]))
    found, frontier = [], [pid]
    while frontier:
        frontier = [child for parent in frontier for child in children.get(parent, ())]
        found += frontier
    return found


def stop_tree(process: subprocess.Popen, grace_seconds: float = 10.0) -> None:
    """TERM `process` and every descendant, listed while `process` still holds
    them (a descendant orphaned first is out of reach of a parent walk), then
    KILL whatever is left after `grace_seconds`. The tree stays in the
    caller's process group, so a bounded runner that kills the group
    (scripts/run_with_timeout.py) still reaches all of it."""
    tree = [process.pid, *descendants(process.pid)]
    for pid in tree:
        try:
            os.kill(pid, signal.SIGTERM)
        except (ProcessLookupError, PermissionError):
            pass
    try:
        process.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired:
        pass
    deadline = time.monotonic() + grace_seconds
    for pid in tree:
        while time.monotonic() < deadline:
            try:
                os.kill(pid, 0)
            except (ProcessLookupError, PermissionError):
                break
            time.sleep(0.05)
        else:
            try:
                os.kill(pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
    process.wait()


def run_admitted_build(command: list, cwd: Path, env: dict, log_handle, timeout: float) -> Optional[int]:
    """Run `command` (the admission prefix and the build) to completion, or
    stop its whole process tree when `timeout` passes (the admission's queue
    counts) or the gate is interrupted. `subprocess.run`'s timeout kills only
    the direct child, which orphans a queued `heavy_gate.sh acquire` or a
    running build whose admission token is then reaped: memory in flight that
    no admission counts. Returns the exit status, or None on a timeout."""
    # Discover an unavailable supervisor before starting anything it could
    # orphan. Keep children in this group: outer timeout/RSS supervision must
    # still reach them, including if this gate itself is killed.
    try:
        descendants(os.getpid())
    except (OSError, subprocess.SubprocessError) as error:
        raise Finding("process-supervision-unavailable", str(error)) from error
    try:
        descriptors = pin_resources.resource_fds(env)
    except pin_resources.Refusal as error:
        raise Finding("inherited-resources-invalid", str(error)) from error
    process = subprocess.Popen(command, cwd=cwd, env=env, stdout=log_handle,
                               stderr=subprocess.STDOUT, pass_fds=descriptors)
    try:
        return process.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        stop_tree(process)
        return None
    except BaseException:
        stop_tree(process)
        raise


def build_tool(tool: Tool, cache_dir: Path, slot: Path, binary: Path, identity_file: Path, repo: Path,
               targo: Path, keep_build: bool, admission: Admission,
               resume_work: Optional[Path] = None) -> dict:
    """Build `tool` at its revision into `slot` (the caller holds the
    revision's lock)."""
    package, rev = tool.package, tool.rev
    resumed_export = (check_resumed_export(tool, cache_dir, resume_work, repo)
                      if resume_work is not None else None)
    work = resume_work or Path(tempfile.mkdtemp(prefix=f"build-{rev[:12]}-", dir=cache_dir))
    started = time.monotonic()
    try:
        src = work / "src"
        if resume_work is None:
            src.mkdir()
            log(f"exporting {package} {rev} from {repo}")
            export_tree(repo, rev, src)
        env = build_environment()
        env.update(CARGO_TARGET_DIR=str(work / "target"), SOURCE_DATE_EPOCH=commit_time(repo, rev))
        recipe_env = {"SOURCE_DATE_EPOCH": env["SOURCE_DATE_EPOCH"]}
        if package == "ay":
            env.update(CARGO_PROFILE_RELEASE_LTO="false", AY_SOURCE_GIT_COMMIT=rev)
            recipe_env.update(CARGO_PROFILE_RELEASE_LTO="false", AY_SOURCE_GIT_COMMIT=rev)
        cargo_config = "export's own .cargo/config.toml"
        manifest = src / "Cargo.toml"
        original = manifest.read_bytes()
        derived, export_record = unverified_tool_export(original, package)
        if resumed_export is not None:
            export_record = resumed_export
        if derived != original:
            manifest.write_bytes(derived)
            log(f"{package} unverified-build export: retired clock-only policy removed; "
                f"manifest {export_record['original_sha256']} -> {export_record['build_sha256']}; "
                f"removed {export_record[REMOVED_CLOCK_FIELDS[package]]}; source and proof rule unchanged")
        command = [str(targo), "--unverified", "build", "--release", "--locked", *tool.build_args]
        label = f"x86-icmp-{package}-{'resume-' if resume_work is not None else ''}{rev[:12]}"
        admission_work = (Path(tempfile.mkdtemp(prefix="resume-admission-", dir=work))
                          if resume_work is not None else work)
        prefix = admission(tool, label, admission_work)
        log(f"building: {' '.join(command)} (in {src}; admitted by {' '.join(prefix[:4]) or 'nothing'}; "
            "no proof claim for the build)")
        build_log = work / "build.log"
        if resume_work is not None:
            descriptor, name = tempfile.mkstemp(prefix="resume-build-", suffix=".log", dir=work)
            os.close(descriptor)
            build_log = Path(name)
        with open(build_log, "w") as handle:
            returncode = run_admitted_build(prefix + command, src, env, handle, BUILD_TIMEOUT_SECONDS)
        built = work / "target" / "release" / package
        if returncode is None:
            tail = build_log.read_text(errors="replace").splitlines()[-30:]
            raise Finding(f"{package}-build-failed",
                          f"no build within {BUILD_TIMEOUT_SECONDS}s, the admission's queue included; its process "
                          "tree was stopped; last lines:\n  " + "\n  ".join(tail))
        if returncode != 0 or not built.is_file():
            tail = build_log.read_text(errors="replace").splitlines()[-30:]
            raise Finding(f"{package}-build-failed", f"exit {returncode}; last lines:\n  " + "\n  ".join(tail))
        if resume_work is not None:
            if check_resumed_export(tool, cache_dir, work, repo) != resumed_export:
                raise Finding(f"{package}-resume-source-mismatch", "source recipe changed during resumed build")
        staged = work / package
        if resume_work is not None:
            descriptor, name = tempfile.mkstemp(prefix="resume-tool-", dir=work)
            os.close(descriptor)
            staged = Path(name)
        shutil.copy2(built, staged)
        staged.chmod(0o500)
        digest = sha256_file(staged)
        banner = tool_banner(staged)
        if not banner_is_the_rules(tool, banner):
            raise Finding(f"{package}-banner-mismatch",
                          f"the built binary reports `{banner}`, not {package} {tool.version} at {rev}")
        identity = {
            "schema": tool.cache_schema, "rev": rev, "version": tool.version, "sha256": digest, "banner": banner,
            "source": str(repo), "targo": str(targo),
            "recipe": {"command": command[1:], "cargo_config": cargo_config, "env": recipe_env},
            "admission": prefix[1:4] if prefix else [],
            "built_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "build_seconds": round(time.monotonic() - started, 1),
        }
        if resume_work is not None:
            identity["resumed_build"] = {"work": str(work), "log": str(build_log),
                                         "source_checked_before_and_after": True}
        identity["recipe"]["unverified_export"] = export_record
        if slot.exists():
            shutil.rmtree(slot)
        private_cache.create_private_dir_all(slot)
        os.replace(staged, binary)
        tmp_identity = slot / "identity.json.tmp"
        private_cache.write_private_file(tmp_identity, json.dumps(identity, indent=2, sort_keys=True) + "\n")
        os.replace(tmp_identity, identity_file)
        require_private_slot(slot, binary, identity_file, package)
        identity.update(cache="cold", path=str(binary))
        return identity
    finally:
        if keep_build or resume_work is not None:
            log(f"kept the build directory {work}")
        else:
            shutil.rmtree(work, ignore_errors=True)


# ---------------------------------------------------------------------------
# The cells: the query dump, its coverage, and the per-cell certificate.
# ---------------------------------------------------------------------------

def dump_queries(out: Path) -> None:
    command = [str(ROOT / "scripts" / "trust_cargo.sh"), "run", "--locked", "-p", "trust-cg-verify",
               "--example", EXAMPLE, "--", str(out)]
    log(f"regenerating the cell queries and the rule: {' '.join(command[1:])}")
    # This can compile the example before dumping. Keep the existing argv and
    # inherited environment, but use the build runner's descendant cleanup on
    # timeout/interruption. Spool output rather than retaining a build transcript
    # in memory; only the final thirty diagnostic lines survive a refusal.
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8", errors="replace") as output:
        returncode = run_admitted_build(command, ROOT, dict(os.environ), output, QUERY_DUMP_TIMEOUT_SECONDS)
        if returncode == 0:
            return
        output.seek(0)
        tail = [line.rstrip("\r\n") for line in deque(output, maxlen=30)]
    reason = (f"no query dump within {QUERY_DUMP_TIMEOUT_SECONDS}s; its process tree was stopped"
              if returncode is None else f"exit {returncode}")
    raise Finding("queries-dump-failed", reason + "; last lines:\n  " + "\n  ".join(tail))


def asserted_terms(query: str) -> list[str]:
    return [line.strip() for line in query.splitlines() if line.strip().startswith("(assert")]


def spec_findings(name: str, cell: dict, terms: list[str]) -> list[Finding]:
    """A certificate query states trust-ir's spec side verbatim: its single
    assertion is `(assert (not (= <spec> <machine>)))`. This pins that the
    query's simplification passes the spec subterm through; the spec's
    provenance (that it IS trust-ir's statement) is held by
    `tests/x86_icmp_manifest_cells.rs`."""
    spec = cell.get("spec")
    if not isinstance(spec, dict) or not isinstance(spec.get("text"), str) or not spec["text"] \
            or spec.get("sha256") != sha256_bytes(spec["text"].encode()):
        return [Finding("spec-unreadable", f"{name}: the dump carries no spec text with its sha256")]
    if len(terms) != 1 or not terms[0].startswith(f"(assert (not (= {spec['text']} "):
        return [Finding("spec-not-trust-ir-statement",
                        f"{name}: the query's assertion does not state trust-ir's spec side "
                        f"({spec.get('fn')}, sha256 {spec['sha256'][:12]}) verbatim")]
    return []


def coverage_findings(manifest: dict, queries: Path) -> list[Finding]:
    """Check (4): every reader cell exactly once, each with a ground trust-ir
    answers, each ground's consequences (instruction-model queries degenerate,
    certificate queries not and stating trust-ir's spec, fail-closed exactly
    when the reader says so), and every pin used exactly once. The ground is
    trust-ir's answer, as dumped; it is not re-derived here."""
    findings: list[Finding] = []
    if manifest.get("schema") != QUERY_MANIFEST_SCHEMA:
        return [Finding("queries-manifest-unreadable", f"schema {manifest.get('schema')!r}")]
    for descriptor in manifest["descriptors"]:
        if not descriptor.get("shape"):
            findings.append(Finding("cell-uncovered",
                                    f"trust-ir descriptor <{descriptor['lanes']} x i{descriptor['lane_bits']}> has no "
                                    "shape in the cell table, so none of its reader cells is checked"))
    expected = {(d["shape"], op) for d in manifest["descriptors"] if d.get("shape")
                for op in manifest["operations"]}
    seen: dict[tuple[str, str], int] = {}
    for cell in manifest["cells"]:
        key = (cell["shape"], cell["cond"])
        seen[key] = seen.get(key, 0) + 1
    for key in sorted(expected - set(seen)):
        findings.append(Finding("cell-uncovered", f"{key[0]} {key[1]}: a reader cell with no row in the dump"))
    for key, count in sorted(seen.items()):
        if key not in expected:
            findings.append(Finding("cell-uncovered", f"{key[0]} {key[1]}: a dumped cell no descriptor covers"))
        if count != 1:
            findings.append(Finding("cell-duplicated", f"{key[0]} {key[1]}: {count} rows"))
    pins_used: dict[tuple[str, str], int] = {}
    for cell in manifest["cells"]:
        name = f"{cell['shape']} {cell['cond']}"
        ground = cell.get("ground")
        if ground not in GROUNDS:
            findings.append(Finding("ground-unknown", f"{name}: ground {ground!r} is none of {', '.join(GROUNDS)}"))
            continue
        if (ground == "fail-closed") != bool(cell["reader"]["fail_closed"]):
            findings.append(Finding("ground-mismatch",
                                    f"{name}: ground {ground}, but the reader answers the cell "
                                    + ("fail-closed" if cell["reader"]["fail_closed"] else "available")))
            continue
        if cell["certified_sha256"] is not None:
            key = (cell["shape"], cell["cond"])
            pins_used[key] = pins_used.get(key, 0) + 1
        if ground == "fail-closed":
            if cell["certified_sha256"] is not None:
                findings.append(Finding("pin-on-fail-closed-cell", f"{name}: a fail-closed cell carries a pin"))
            continue
        if cell["obligation_count"] != 1 or not cell.get("query_file"):
            findings.append(Finding("obligation-count",
                                    f"{name}: {cell['obligation_count']} registered obligations, expected one"))
            continue
        query = (queries / cell["query_file"]).read_text()
        terms = asserted_terms(query)
        if ground == "instruction-model":
            if not cell["degenerate"] or terms != ["(assert false)"]:
                findings.append(Finding("instruction-model-not-degenerate",
                                        f"{name}: the obligation is not degenerate (assertions {terms[:3]}); it "
                                        "claims evidence the rule does not publish for this cell"))
            if cell["certified_sha256"] is not None:
                findings.append(Finding("pin-on-instruction-model-cell", f"{name}: carries a certificate pin"))
        else:
            if cell["degenerate"] or terms == ["(assert false)"]:
                findings.append(Finding("certificate-degenerate",
                                        f"{name}: a certificate-ground obligation is DEGENERATE; a tautology is "
                                        "never a certificate"))
                continue
            if cell["certified_sha256"] is None:
                findings.append(Finding("pin-missing", f"{name}: a certificate-ground cell with no certified pin"))
            findings += spec_findings(name, cell, terms)
    pin_rows: dict[tuple[str, str], int] = {}
    for shape, cond, _ in manifest["certified_pins"]:
        pin_rows[(shape, cond)] = pin_rows.get((shape, cond), 0) + 1
    for (shape, cond), count in sorted(pin_rows.items()):
        if count != 1:
            findings.append(Finding("pin-duplicated", f"{shape} {cond}: {count} CERTIFIED_QUERY_SHA256 rows"))
    for shape, cond, _ in manifest["certified_pins"]:
        if pins_used.get((shape, cond), 0) != 1:
            findings.append(Finding("pin-unused",
                                    f"{shape} {cond}: CERTIFIED_QUERY_SHA256 names no certificate-ground cell"))
    return findings


def ay_stdout_is_exact_unsat(returncode: int, stdout: str) -> bool:
    """trust-cg-verify `obligation_cert_store::ay_stdout_is_exact_unsat`: a
    successful child, no SMT-LIB error row, and exactly one verdict, `unsat`."""
    if returncode != 0 or any(line.lstrip().startswith("(error") for line in stdout.splitlines()):
        return False
    verdicts = [line.strip() for line in stdout.splitlines() if line.strip() in ("sat", "unsat", "unknown")]
    return verdicts == ["unsat"]


def clean_alethe_stdout_is_fully_verified(stdout: str) -> bool:
    """trust-cg-verify `obligation_cert_store::clean_alethe_stdout_is_fully_verified`."""
    lines = [line.strip().lower() for line in stdout.splitlines()]
    return ("external certificate verification: passed" in lines
            and "type: alethe smt proof" in lines
            and "proof status: fully verified" in lines
            and not any("failed" in line or "holey" in line or "incomplete" in line for line in lines))


def proof_certificate_lines(stderr: str) -> list[dict]:
    """AY's `c ay.proof.certificate k=v ...` reports, one dict per line."""
    rows = []
    for line in stderr.splitlines():
        match = re.match(r"^c ay\.proof\.certificate\s+(.*)$", line.strip())
        if match:
            rows.append(dict(field.split("=", 1) for field in match.group(1).split() if "=" in field))
    return rows


# The report fields every certifying measurement recorded; the rule's
# `ay_certificate_report` states them (and the gate reads them from there).
CERTIFICATE_FIELDS = {"unproved_steps": "0", "foreign_assumes": "no", "trust_free": "yes"}


def certificate_report_findings(stderr: str, fields: Optional[dict] = None) -> list[tuple[str, str]]:
    fields = CERTIFICATE_FIELDS if fields is None else fields
    rows = proof_certificate_lines(stderr)
    if len(rows) != 1:
        return [("ay-unproved-steps", f"{len(rows)} `c ay.proof.certificate` report lines, expected exactly one")]
    wrong = {key: rows[0].get(key, "absent") for key, want in fields.items() if rows[0].get(key) != want}
    if not wrong:
        return []
    code = "ay-unproved-steps" if "unproved_steps" in wrong else "ay-proof-not-trust-free"
    return [(code, " ".join(f"{key}={value}" for key, value in wrong.items())
             + " (required " + " ".join(f"{k}={v}" for k, v in fields.items()) + ")")]


def unchecked_rules_in(proof: str, rules: Iterable[str]) -> list[str]:
    """The rules of `rules` that some step of `proof` uses."""
    return [rule for rule in rules if re.search(r":rule\s+" + re.escape(rule) + r"(?![\w.-])", proof)]


def proof_has_hole(proof: str) -> bool:
    return bool(unchecked_rules_in(proof, ["hole"]))


def fill(arguments: list[str], **values: str) -> list[str]:
    """The rule's argument list with each `{name}` placeholder replaced."""
    filled = []
    for argument in arguments:
        for name, value in values.items():
            argument = argument.replace("{" + name + "}", value)
        filled.append(argument)
    return filled


def certify_cell(cell: dict, queries: Path, work: Path, ay: Path, clean: Path, rule: dict,
                 keep: bool = False) -> dict:
    """(5) and (6) for one certificate-ground cell whose query matched its pin."""
    name = f"{cell['shape']}_{cell['cond']}"
    query_path = queries / cell["query_file"]
    proof_path = work / f"{name}.alethe"
    row = {"cell": f"{cell['shape']} {cell['cond']}", "query_sha256": cell["query_sha256"], "findings": []}
    started = time.monotonic()
    try:
        solved = subprocess.run([str(ay), *fill(rule["ay_args"], query=str(query_path), proof=str(proof_path))],
                                capture_output=True, text=True, env=tool_environment(), timeout=AY_TIMEOUT_SECONDS)
    except subprocess.TimeoutExpired:
        row["findings"].append(("ay-timeout", f"no answer in {AY_TIMEOUT_SECONDS}s"))
        return row
    row["ay_seconds"] = round(time.monotonic() - started, 2)
    reports = proof_certificate_lines(solved.stderr)
    row["ay_certificate"] = reports[0] if len(reports) == 1 else reports
    if not ay_stdout_is_exact_unsat(solved.returncode, solved.stdout):
        verdict = " ".join(solved.stdout.split())[:200]
        row["findings"].append(("ay-not-unsat", f"exit {solved.returncode}, stdout `{verdict}`"))
        return row
    row["findings"] += certificate_report_findings(solved.stderr, rule["ay_certificate_report"])
    if not proof_path.is_file() or not proof_path.stat().st_size:
        row["findings"].append(("proof-missing", "AY answered unsat but wrote no proof"))
        return row
    proof = proof_path.read_text()
    row["proof_sha256"] = sha256_bytes(proof.encode())
    row["proof_bytes"] = len(proof.encode())
    for unchecked in unchecked_rules_in(proof, rule["unchecked_proof_rules"]):
        code = "proof-hole" if unchecked == "hole" else "proof-unchecked-rule"
        row["findings"].append((code, f"the Alethe proof carries a `:rule {unchecked}` step, which the checker "
                                      "accepts without checking"))
    certificate = work / f"{name}.cert.json"
    certificate.write_text(json.dumps({"type": "alethe_certificate", "version": "1.0",
                                       "problem": query_path.read_text(), "proof": proof}))
    started = time.monotonic()
    try:
        checked = subprocess.run([str(clean), *fill(rule["clean_args"], certificate=str(certificate))],
                                 capture_output=True, text=True, env=tool_environment(), timeout=CLEAN_TIMEOUT_SECONDS)
    except subprocess.TimeoutExpired:
        row["findings"].append(("clean-timeout", f"no verdict in {CLEAN_TIMEOUT_SECONDS}s"))
        return row
    row["clean_seconds"] = round(time.monotonic() - started, 2)
    row["clean_exit"] = checked.returncode
    status = [line.strip() for line in checked.stdout.splitlines()
              if re.search(r"status|passed|failed|holey|incomplete", line, re.I)][:4]
    if checked.returncode != 0:
        # The machine verdict: `cert verify-external` exits non-zero on a
        # proof it does not verify in full.
        row["findings"].append(("clean-not-fully-verified", f"exit {checked.returncode}; {'; '.join(status)}"))
    elif not clean_alethe_stdout_is_fully_verified(checked.stdout) or \
            f"proof status: {rule['clean_proof_status']}" not in [line.strip().lower()
                                                                  for line in checked.stdout.splitlines()]:
        row["findings"].append(("clean-not-fully-verified",
                                f"exit 0, but stdout does not report `Proof status: {rule['clean_proof_status']}` "
                                f"cleanly; {'; '.join(status)}"))
    if not keep:
        proof_path.unlink(missing_ok=True)
        certificate.unlink(missing_ok=True)
    return row


# ---------------------------------------------------------------------------
# The gate.
# ---------------------------------------------------------------------------

def default_cache_dir(package: str = "ay") -> Path:
    """`<cache>/trust-cg/<package>-cli`, `<cache>` by the one user-cache rule
    (`private_cache.user_cache_base`: an empty or relative XDG_CACHE_HOME is
    ignored). Raises `ValueError` when no absolute cache base is named."""
    return Path(private_cache.user_cache_base()) / "trust-cg" / f"{package}-cli"


def lock_pins(lock_text: Optional[str] = None) -> dict:
    lock_text = (ROOT / "Cargo.lock").read_text() if lock_text is None else lock_text
    return {"trust_ir_rev": pinned_rev(lock_text, "trust-ir", "trust-ir"),
            "ay_rev": pinned_rev(lock_text, "ay", "ay")}


def load_manifest(args, work: Path) -> tuple[Path, dict]:
    """The query dump (regenerated unless `--queries` names one) and its
    manifest. Only a regenerated dump carries the compiled trust-ir's rule,
    grounds and pins; `run_gate` never passes a supplied one."""
    queries = args.queries if args.queries else work / "queries"
    if not args.queries:
        resolve_targo()
        dump_queries(queries)
    try:
        manifest = json.loads((queries / "manifest.json").read_text())
    except (OSError, ValueError) as error:
        raise Finding("queries-manifest-unreadable", f"{queries / 'manifest.json'}: {error}") from error
    if manifest.get("schema") != QUERY_MANIFEST_SCHEMA:
        raise Finding("queries-manifest-unreadable",
                      f"schema {manifest.get('schema')!r}, expected {QUERY_MANIFEST_SCHEMA}")
    return queries, manifest


def obtain_tools(args, rule: dict, report: dict) -> tuple[dict, list[MissingInput]]:
    """Both of the rule's tools, Clean first (its export also supplies the
    admission gate), each as `{path, identity}`; absent inputs are collected."""
    admission = heavy_gate_admission(rule["clean"], args.clean_source)
    tools: dict = {}
    missing: list[MissingInput] = []
    for tool, cache_dir, source in ((rule["clean"], args.clean_cache_dir, args.clean_source),
                                    (rule["ay"], args.cache_dir, args.ay_source)):
        try:
            resume = getattr(args, "resume_tool_build", {}).get(tool.package)
            options = {"resume_work": resume} if resume is not None else {}
            identity = obtain_build(tool, cache_dir, source, args.keep_build, admission, **options)
        except MissingInput as absent:
            missing.append(absent)
            continue
        # Exactly the binary obtain_build checked, named below the canonical
        # cache directory; never re-derived from `cache_dir`.
        path = Path(identity["path"])
        identity = dict(identity, certifying_bytes=identity["sha256"] in tool.certifying_sha256)
        report[tool.package] = identity
        tools[tool.package] = path
        log(f"{tool.package}: {path} ({identity['cache']} cache; sha256 {identity['sha256']}"
            f"{' (a certifying build)' if identity['certifying_bytes'] else ' (not one of the certifying builds)'}; "
            f"`{identity['banner']}`; built in {identity['build_seconds']}s)")
    return tools, missing


def run_gate(args) -> tuple[int, dict]:
    report: dict = {"schema": SCHEMA, "findings": [], "missing": [], "cells": [],
                    "queries": ({"source": "supplied", "path": str(args.queries)} if args.queries
                                else {"source": "regenerated"})}
    started = time.monotonic()
    try:
        pinned = lock_pins()
        report.update(pinned)
        with tempfile.TemporaryDirectory(prefix="x86-icmp-certificates-") as temporary:
            work = Path(args.keep_work) if args.keep_work else Path(temporary)
            work.mkdir(parents=True, exist_ok=True)
            try:
                queries, manifest = load_manifest(args, work)
            except MissingInput as absent:
                return missing_inputs([absent], args, report)
            rule = read_certificate_rule(manifest)
            report["rule"] = rule_summary(rule)
            report["trust_ir_build"] = manifest.get("trust_ir_build")
            log(f"rule (trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE, trust-ir {manifest.get('trust_ir_build')}): "
                f"AY {rule['ay'].rev} ({rule['ay'].version}), Clean {rule['clean'].rev} ({rule['clean'].version})")
            require_rule_ay(pinned["ay_rev"], rule, pinned["trust_ir_rev"])
            tools, missing = obtain_tools(args, rule, report)
            if missing:
                return missing_inputs(missing, args, report)
            ay, clean = tools["ay"], tools["clean"]
            findings = coverage_findings(manifest, queries)
            certificate_cells = []
            for cell in manifest["cells"]:
                if cell.get("ground") != "certificate" or not cell.get("query_file") \
                        or cell["certified_sha256"] is None:
                    continue
                digest = sha256_file(queries / cell["query_file"])
                if digest != cell["certified_sha256"]:
                    findings.append(Finding("query-digest-mismatch",
                                            f"{cell['shape']} {cell['cond']}: query sha256 {digest} is not the "
                                            f"certified {cell['certified_sha256']}; re-certify before the row stays "
                                            "available"))
                    continue
                certificate_cells.append(dict(cell, query_sha256=digest))
            log(f"coverage: {len(manifest['cells'])} reader cells; {len(certificate_cells)} certificate-ground "
                f"queries match their pins; re-running AY + Clean on each ({args.jobs} at a time)")
            ay_before, clean_before = sha256_file(ay), sha256_file(clean)
            with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
                rows = list(pool.map(lambda cell: certify_cell(cell, queries, work, ay, clean, rule,
                                                               bool(args.keep_work)),
                                     certificate_cells))
            for row in rows:
                report["cells"].append({key: value for key, value in row.items() if key != "findings"})
                for code, message in row["findings"]:
                    findings.append(Finding(code, f"{row['cell']}: {message}"))
                status = "ok" if not row["findings"] else "FAIL " + ",".join(code for code, _ in row["findings"])
                steps = row.get("ay_certificate", {}).get("unproved_steps", "-") \
                    if isinstance(row.get("ay_certificate"), dict) else "-"
                log(f"  {row['cell']:<10} query {row['query_sha256'][:12]} ay {row.get('ay_seconds', '-')}s "
                    f"unproved_steps={steps} proof {row.get('proof_sha256', '-')[:12]} "
                    f"clean {row.get('clean_seconds', '-')}s exit {row.get('clean_exit', '-')}  {status}")
            if sha256_file(ay) != ay_before or sha256_file(clean) != clean_before:
                findings.append(Finding("tool-changed-during-run", "the AY or Clean bytes changed while the gate ran"))
            report["instruction_model_cells"] = sum(1 for c in manifest["cells"]
                                                    if c.get("ground") == "instruction-model")
            report["certificate_cells"] = sum(1 for c in manifest["cells"] if c.get("ground") == "certificate")
            report["fail_closed_cells"] = sum(1 for c in manifest["cells"] if c.get("ground") == "fail-closed")
        if findings:
            raise_findings(findings, report)
        report["seconds"] = round(time.monotonic() - started, 1)
        summary = (f"{len(report['cells'])} certificate-ground cells re-certified (AY {rule['ay'].rev[:12]} "
                   f"{rule['ay_verdict']}, {' '.join(f'{k}={v}' for k, v in rule['ay_certificate_report'].items())}, "
                   f"no {'/'.join(rule['unchecked_proof_rules'])}; Clean {rule['clean'].rev[:12]} exit 0, "
                   f"{rule['clean_proof_status']}); {report['instruction_model_cells']} instruction-model cells "
                   f"degenerate; {report['fail_closed_cells']} fail-closed; certifying bytes: "
                   f"ay {report['ay']['certifying_bytes']}, clean {report['clean']['certifying_bytes']}; "
                   f"{report['seconds']}s")
        if args.queries:
            # The rule, the grounds and the pins above are the supplied
            # manifest's, which nothing ties to the compiled trust-ir.
            log(f"SUPPLIED-DUMP (not a PASS): {summary}; the rule, grounds and pins were read from "
                f"{args.queries / 'manifest.json'}, not regenerated from the compiled trust-ir")
            return EXIT_SUPPLIED, report
        log(f"PASS: {summary}")
        return EXIT_PASS, report
    except Finding as finding:
        report["findings"] = report["findings"] or [{"code": finding.code, "message": finding.message}]
        report["seconds"] = round(time.monotonic() - started, 1)
        for item in report["findings"]:
            log(f"FAIL {item['code']}: {item['message']}")
        return EXIT_FAIL, report


def missing_inputs(missing: list[MissingInput], args, report: dict) -> tuple[int, dict]:
    """Absent toolchain inputs: a stated SKIP when explicitly requested, else a
    failure. The certificates were not re-run either way."""
    report["missing"] = [{"code": item.code, "message": item.message} for item in missing]
    for item in missing:
        log(f"MISSING {item.code}: {item.message}")
    if args.skip_missing_toolchain:
        log("SKIPPED (explicit --skip-missing-toolchain): the certificates were NOT re-run")
        return EXIT_SKIPPED, report
    raise Finding("toolchain-input-missing",
                  ", ".join(item.code for item in missing)
                  + " (the certificates were NOT re-run; --skip-missing-toolchain makes this a SKIP)")


class Findings(Finding):
    pass


def raise_findings(findings: list[Finding], report: dict) -> None:
    report["findings"] = [{"code": item.code, "message": item.message} for item in findings]
    raise Findings(findings[0].code, f"{len(findings)} finding(s)")


def tools_path(args) -> int:
    """Obtain both of the rule's tools and print their identities."""
    report: dict = {}
    try:
        with tempfile.TemporaryDirectory(prefix="x86-icmp-certificates-") as temporary:
            _, manifest = load_manifest(args, Path(temporary))
            rule = read_certificate_rule(manifest)
            require_rule_ay(lock_pins()["ay_rev"], rule, lock_pins()["trust_ir_rev"])
            _, missing = obtain_tools(args, rule, report)
    except (Finding, MissingInput) as error:
        log(f"FAIL {error}")
        return EXIT_FAIL
    if missing:
        for item in missing:
            log(f"FAIL {item}")
        return EXIT_FAIL
    print(json.dumps(report, indent=2, sort_keys=True))
    return EXIT_PASS


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0], allow_abbrev=False)
    parser.add_argument("command", nargs="?", default="check", choices=("check", "tools-path"),
                        help="check (the gate, default) or tools-path (obtain the rule's AY and Clean and print "
                             "their identities)")
    parser.add_argument("--cache-dir", type=Path, default=None,
                        help="AY build cache, one slot per revision/recipe (default: <cache>/trust-cg/ay-cli, where <cache> "
                             "is an absolute $XDG_CACHE_HOME, else $HOME/.cache)")
    parser.add_argument("--clean-cache-dir", type=Path, default=None,
                        help="Clean build cache, one slot per revision/recipe (default: <cache>/trust-cg/clean-cli, "
                             "<cache> as for --cache-dir)")
    parser.add_argument("--ay-source", type=Path, default=None,
                        help="AY git repository to export the rule's revision from "
                             "(default: $AY_SOURCE_DIR or ~/ay, then Cargo's git database)")
    parser.add_argument("--clean-source", type=Path, default=None,
                        help="Clean git repository to export the rule's revision (and its heavy_gate) from "
                             "(default: $CLEAN_SOURCE_DIR or ~/clean, then Cargo's git database)")
    parser.add_argument("--queries", type=Path, default=None,
                        help="re-run an existing query dump (manifest.json + *.smt2) instead of regenerating it; "
                             "its rule, grounds and pins are the dump's, so such a run is never a PASS (exit 4 "
                             "without a finding)")
    parser.add_argument("--skip-missing-toolchain", action="store_true",
                        help="an ABSENT toolchain input is a stated SKIP (exit 3) instead of a failure")
    parser.add_argument("--jobs", type=int, default=4, help="cells certified concurrently (default: %(default)s)")
    parser.add_argument("--keep-build", action="store_true", help="keep each cold build's export and target directory")
    parser.add_argument("--resume-tool-build", action="append", default=[], metavar="TOOL=/ABS/WORK",
                        help="revalidate a retained exact export and rerun its normal build in the same private target")
    parser.add_argument("--keep-work", default=None, help="write queries, proofs and certificates here and keep them")
    parser.add_argument("--json-out", type=Path, default=None, help="write the run's report as JSON")
    args = parser.parse_args(argv)
    resumes = {}
    for entry in args.resume_tool_build:
        tool, separator, path = entry.partition("=")
        if not separator or tool not in {"ay", "clean"} or tool in resumes or not Path(path).is_absolute():
            parser.error("--resume-tool-build requires one unique ay|clean=/absolute/work per tool")
        resumes[tool] = Path(path)
    args.resume_tool_build = resumes
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.command == "tools-path" and args.queries:
        parser.error("tools-path obtains the compiled trust-ir rule's tools; --queries would name a supplied rule")
    for attribute, tool in (("cache_dir", "ay"), ("clean_cache_dir", "clean")):
        if getattr(args, attribute) is None:
            try:
                setattr(args, attribute, default_cache_dir(tool))
            except ValueError as error:
                option = "--" + attribute.replace("_", "-")
                log(f"FAIL {tool}-cache-not-private: no {option} and no default: {error}")
                return EXIT_FAIL
    args.cache_dir = args.cache_dir.expanduser().resolve()
    args.clean_cache_dir = args.clean_cache_dir.expanduser().resolve()
    if args.command == "tools-path":
        return tools_path(args)
    code, report = run_gate(args)
    report["exit"] = code
    if args.json_out:
        args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
