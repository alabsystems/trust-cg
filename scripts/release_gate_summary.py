#!/usr/bin/env python3
"""Machine-readable accounting and proof-tool resolution for the release gates.

scripts/run_public_release_checks.sh and scripts/run_public_release_codegen_tests.sh
record every planned or executed lane, every applied exclusion or `--skip`, every
package moved to another lane, and the resolved AY/Clean executable identities in
one JSON document. A run that excluded a solver-backed or host-locked lane is
therefore retained as non-qualifying rather than only announced on stderr.

`non_qualifying_reasons` is the verdict. An empty list means the gate ran in
solver-required (`TRUST_CG_PROOF_GATE=require`) mode, recorded pinned AY and
Clean identities that did not change during the run, applied no exclusion and
executed exactly the code-owned lane and partition roster for its gate and host.
The x86 public-release profiles are accounting-only and always non-qualifying:
their missing native floor/bridge lanes cannot be replaced by AArch64 evidence.
That is a statement about this gate's lane set on this host only: it is not
platform completion, proof authority or release readiness, and it does not
replace the full test matrix or the pinned soundness gate. It accounts for
lanes, lane-level exclusions and `--skip` filters; it does not observe a test
that returns early inside a passing libtest run, whose output libtest captures.

Proof-tool resolution reproduces the verifier's routes exactly.

AY has one rule (crates/trust-cg-verify/src/ay_identity.rs): an absolute
`AY_SOLVER_PATH`, which is authoritative even when it resolves nothing (a bare
name is refused: the verifier has no PATH lookup), otherwise
`<build compiler sysroot>/bin/ay`, the sysroot `$RUSTC --print sysroot` (else
the Trust package's `trustc` on PATH) names for the tests this gate runs. Nothing else is consulted:
not aterm's managed AY package, PATH, TRUST_SYSROOT or source checkouts, so they
are not evidence of a solver here either. The verifier then admits that AY only
when the SHA-256 of its bytes equals the digest recorded when trust-cg-verify
was built; this gate cannot see that record, so a different AY is caught by the
solver-backed tests, which FAIL on it rather than skip. The gate never executes
an AY: its record is the file's SHA-256, not a `--version` banner. A "pinned"
route is a naming route, not an admission; a script that runs the resolved AY
itself must first have the trust-cg build admit those bytes
(`trust-cg --print-ay-identity`), as the AArch64 arithmetic AOT runner does.

Clean (crates/trust-cg-verify/src/obligation_cert_store.rs,
`default_clean_checker_candidates`): an explicit override
(`TCG_EXTERNAL_CLEAN_CHECKER`, then `TCG_CLEAN_CHECKER`), authoritative even when
it resolves nothing, then the build compiler's `<sysroot>/bin/clean` when that
sysroot is a Trust toolchain (`lib/rustlib` and `bin/trustc`) and the checker
fully verifies the verifier's control proof, then aterm's managed package store
(crates/trust-cg-verify/src/aterm_toolchain.rs). The toolchain's checker comes
first because it must read the proofs of the AY that toolchain ships. Clean is
never taken from a generic `clean` on PATH.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import Optional, Sequence, Tuple


SCHEMA = "trust-cg-public-release-summary-v1"
SCOPE = (
    "release-gate accounting against the code-owned lane and partition roster "
    "for this gate and host; not platform "
    "completion, proof authority, release readiness, the full test matrix or the "
    "pinned soundness gate; lane-level exclusions and --skip filters are recorded, "
    "but a test that returns early inside a passing libtest run is not observed"
)
KERNEL_LAYOUT_GATE = "kernel_layout_fixture_qualification"
KERNEL_LAYOUT_SCOPE = (
    "isolated native-versus-JIT tests of the existing kernel-layout fixtures "
    "on the recorded compiler and host; not full release qualification, "
    "proof authority, regenerated fixtures or another compiler/host; "
    "a test that returns early inside a passing libtest run is not observed"
)
MODES = ("auto", "require")
LANE_STATUSES = ("planned", "running", "pass", "fail", "excluded", "unavailable")
FINAL_STATUSES = ("pass", "fail", "dry-run")
PINNED_ROUTES = ("env-override", "aterm-packaged", "toolchain-sysroot")
RESOLVE_NOT_FOUND = 3
RESOLVE_INVALID_OVERRIDE = 4
NOT_QUALIFYING = 5
OVERRIDES = {
    "ay": ("AY_SOLVER_PATH",),
    "clean": ("TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER"),
}
REPO_ROOT = Path(__file__).resolve().parents[1]
AY_NOT_EXECUTED = (
    "not executed: AY is identified by the SHA-256 of its bytes, and the gate "
    "never runs an AY the verifier has not admitted"
)

CODEGEN_LANES = frozenset(("codegen-complement", "codegen-doctests", "codegen-capstones"))
X86_RELEASE_HOSTS = frozenset(("x86_64-apple-darwin", "x86_64-unknown-linux-gnu"))
X86_ACCOUNTING_LANES = frozenset(("pgo-runtime", "codegen-capstones"))
RELEASE_COMMON_LANES = frozenset((
    "authority-preflight", "companion-coherence", "python-unit-tests", "harness-syntax",
    "harness-helper-syntax",
    "timeout-runner-tests", "soundness-harness-tests", "sat-fixtures", "vendor-licenses",
    "cargo-metadata", "cargo-check-workspace", "cargo-check-fuzz", "pgo-runtime",
    "proof-gate", "workspace", "codegen", "bridge-toolchain-pin", "bridge-env",
    "bridge-tests",
)) | CODEGEN_LANES
EXPECTED_LANES = {
    "run_public_release_checks": {
        "aarch64-apple-darwin": RELEASE_COMMON_LANES | {
            "darwin-aarch64-floor", "darwin-aarch64-bridge",
        },
        "aarch64-unknown-linux-gnu": RELEASE_COMMON_LANES | {
            "linux-aarch64-floor", "linux-aarch64-bridge", "aarch64-aot-arithmetic",
        },
        "x86_64-apple-darwin": X86_ACCOUNTING_LANES | {
            "darwin-x86_64-floor", "darwin-x86_64-bridge",
        },
        "x86_64-unknown-linux-gnu": X86_ACCOUNTING_LANES | {
            "linux-x86_64-floor", "linux-x86_64-bridge",
        },
    },
    "run_public_release_codegen_tests": {
        "aarch64-apple-darwin": CODEGEN_LANES,
        "aarch64-unknown-linux-gnu": CODEGEN_LANES,
    },
    KERNEL_LAYOUT_GATE: {
        "aarch64-apple-darwin": frozenset(("kernel-layout-fixtures",)),
    },
}
EXPECTED_PARTITIONS = {
    "run_public_release_checks": (
        {"package": "trust-cg-codegen", "from_lane": "workspace", "covered_by": "codegen"},
    ),
    "run_public_release_codegen_tests": (),
}


class ResolveError(Exception):
    """An explicit override is set but does not name an executable file."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load(path: Path) -> dict:
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise SystemExit(f"release_gate_summary: cannot read {path}: {error}") from error
    if not isinstance(document, dict) or document.get("schema") != SCHEMA:
        raise SystemExit(f"release_gate_summary: {path} is not a {SCHEMA} document")
    return document


def store(path: Path, document: dict) -> None:
    document["non_qualifying_reasons"] = non_qualifying_reasons(document)
    document["qualifying"] = not document["non_qualifying_reasons"]
    document["updated_utc"] = utc_now()
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def blockers(document: dict, lane_prefix: str = "") -> list:
    """Reasons known before any lane runs: exclusions and lanes that cannot run."""
    reasons = []
    for exclusion in document.get("exclusions", []):
        if not exclusion["lane"].startswith(lane_prefix):
            continue
        reasons.append(
            f"exclusion: lane {exclusion['lane']} {exclusion['kind']} {exclusion['value']} "
            f"({exclusion['reason']})"
        )
    for lane in document.get("lanes", []):
        if not lane["name"].startswith(lane_prefix):
            continue
        if lane["status"] in ("excluded", "unavailable"):
            detail = f" ({lane['detail']})" if lane.get("detail") else ""
            reasons.append(f"lane {lane['name']}: {lane['status']}{detail}")
    return reasons


def non_qualifying_reasons(document: dict) -> list:
    """Every reason this run is not an exact-roster, zero-exclusion, solver-required pass."""
    reasons = []
    mode = document.get("mode")
    gate = document.get("gate")
    host = document.get("host")
    if gate == KERNEL_LAYOUT_GATE:
        reasons.append("layout-fixture qualification only: not full release or proof qualification")
    if mode != "require":
        reasons.append(f"mode={mode}: solver-required zero-exclusion mode (TRUST_CG_PROOF_GATE=require) was not selected")
    if gate == "run_public_release_checks" and host in X86_RELEASE_HOSTS:
        reasons.append(f"host={host}: x86 release profile is accounting-only; native floor and bridge are not qualified")
    reasons.extend(blockers(document))
    lanes = document.get("lanes", [])
    profiles = EXPECTED_LANES.get(gate)
    if profiles is None:
        reasons.append(f"unknown gate: {gate}")
        expected_lanes = None
    else:
        expected_lanes = profiles.get(host)
        if expected_lanes is None:
            reasons.append(f"unsupported host profile for {gate}: {host}")
    if expected_lanes is not None:
        by_name = {}
        for lane in lanes:
            by_name.setdefault(lane["name"], []).append(lane)
        for name in sorted(expected_lanes):
            matches = by_name.get(name, [])
            if not matches:
                reasons.append(f"required lane {name}: missing")
            elif len(matches) != 1:
                reasons.append(f"required lane {name}: recorded {len(matches)} times")
            elif matches[0]["status"] != "pass":
                reasons.append(f"required lane {name}: {matches[0]['status']} instead of pass")
        for name in sorted(by_name.keys() - expected_lanes):
            reasons.append(f"unexpected lane {name} for {gate} on {host}")

    partitions = document.get("partitions", [])
    if gate == "run_public_release_checks" and host in X86_RELEASE_HOSTS:
        expected_partitions = ()
    else:
        expected_partitions = EXPECTED_PARTITIONS.get(gate, ())
    if profiles is not None:
        for partition in expected_partitions:
            count = partitions.count(partition)
            if count != 1:
                reasons.append(
                    f"required partition {partition['package']} from {partition['from_lane']} "
                    f"to {partition['covered_by']}: recorded {count} times"
                )
        for partition in partitions:
            if partition not in expected_partitions:
                reasons.append(f"unexpected partition: {partition}")
    if not lanes:
        reasons.append("no lane was recorded")
    planned = [lane["name"] for lane in lanes if lane["status"] == "planned"]
    if planned:
        reasons.append(f"{len(planned)} lane(s) planned but not executed: {', '.join(planned)}")
    for lane in lanes:
        if lane["status"] in ("running", "fail"):
            state = "did not complete" if lane["status"] == "running" else "failed"
            reasons.append(f"lane {lane['name']}: {state}")
    by_name = {lane["name"]: lane for lane in lanes}
    for partition in partitions:
        if not isinstance(partition, dict) or not all(
            key in partition for key in ("package", "from_lane", "covered_by")
        ):
            continue
        covering = by_name.get(partition["covered_by"])
        status = covering["status"] if covering else "missing"
        if status != "pass":
            reasons.append(
                f"partition: {partition['package']} left lane {partition['from_lane']}; "
                f"its covering lane {partition['covered_by']} is {status}"
            )
    solver = document.get("solver") or {}
    if mode == "require":
        for tool in ("ay", "clean"):
            record = solver.get(tool)
            if record is None:
                reasons.append(f"mode=require: no {tool} identity was recorded")
            elif record.get("pinning") != "pinned":
                reasons.append(f"mode=require: {tool} was resolved through unpinned route {record.get('route')}")
    for drift in document.get("solver_drift", []):
        reasons.append(f"solver identity changed during the run: {drift}")
    status = document.get("status")
    if status != "pass":
        reasons.append(f"gate status: {status}")
    return reasons


def file_identity(path: Path) -> dict:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return {"path": str(path), "sha256": digest.hexdigest(), "size": path.stat().st_size}


def version_probe(path: Path) -> dict:
    """Best-effort `--version` transcript. Capability is decided by the Rust proof gate."""
    try:
        result = subprocess.run(
            [str(path), "--version"], capture_output=True, text=True, timeout=20, check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return {"returncode": None, "error": str(error)}
    return {"returncode": result.returncode, "stdout": result.stdout[-2000:], "stderr": result.stderr[-2000:]}


def executable_file(candidate: Path) -> Optional[Path]:
    try:
        resolved = candidate.resolve(strict=True)
    except (OSError, RuntimeError):
        return None
    if resolved.is_file() and os.access(resolved, os.X_OK):
        return resolved
    return None


def packaged_prefixes(path_env: str, home: str, platform: str) -> list:
    """aterm_toolchain.rs: `<prefix>/bin` entries on PATH, then the platform default."""
    prefixes = []
    for entry in path_env.split(os.pathsep):
        if not entry:
            continue
        bin_dir = Path(entry)
        if bin_dir.name == "bin" and bin_dir.parent not in prefixes:
            prefixes.append(bin_dir.parent)
    if home:
        default = (
            Path(home) / "Library/Application Support/aterm/pkg"
            if platform == "darwin"
            else Path(home) / ".local/share/aterm/pkg"
        )
        if default not in prefixes:
            prefixes.append(default)
    return prefixes


def packaged_tool(tool: str, path_env: str, home: str, platform: str) -> Optional[Path]:
    for prefix in packaged_prefixes(path_env, home, platform):
        found = executable_file(prefix / "store" / tool / "current" / "bin" / tool)
        if found is not None:
            return found
    return None


def resolve_override(tool: str, name: str, value: str) -> Path:
    """Resolve an explicit override the way every child test process will see it."""
    trimmed = value.strip()
    if not trimmed:
        raise ResolveError(f"{name} is set but empty; the verifier treats that as no {tool}")
    candidate = Path(trimmed)
    if candidate.is_absolute():
        found = executable_file(candidate)
    else:
        # The verifier refuses a relative or bare AY_SOLVER_PATH
        # (TCG-AY-IDENTITY-OVERRIDE-NOT-ABSOLUTE; there is no PATH lookup).
        # Cargo runs each test binary from its package directory, so a relative
        # path would name a different file in the tests than in this gate.
        raise ResolveError(f"{name}={trimmed!r} is relative; the release gate requires an absolute path")
    if found is None:
        raise ResolveError(f"{name}={trimmed!r} does not name an executable file")
    return found


def _launcher_target(path: Path) -> Optional[Path]:
    """scripts/trust_toolchain.py's `launcher_target`: the file an atpkg shim execs."""
    spec = importlib.util.spec_from_file_location(
        "_release_gate_trust_toolchain", REPO_ROOT / "scripts" / "trust_toolchain.py")
    if spec is None or spec.loader is None:
        raise RuntimeError("scripts/trust_toolchain.py is missing")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.launcher_target(path)


def build_compiler_sysroot(environ: dict) -> Optional[Path]:
    """The sysroot of the compiler targo will build the tests with, as build.rs asks it.

    trust-cg-verify's build script records `$RUSTC --print sysroot`; targo
    supplies RUSTC, and without an override builds with the installed Trust
    package's own trustc, the one on PATH beside targo. Only that compiler is
    executed; a stock `rustc` on PATH is never consulted. When the PATH
    `trustc` is an atpkg launcher shim, the package file its final exec names
    runs, never the shim: its shell prelude is read, never run, by the resolver
    (scripts/trust_toolchain.py `launcher_target`, DR-ATPKG-PRELUDE-SHIM-20261015),
    and the package targo builds with that file, not with the shim.
    """
    rustc = environ.get("RUSTC", "").strip()
    if not rustc:
        found = shutil.which("trustc", path=environ.get("PATH", ""))
        if not found:
            return None
        target = _launcher_target(Path(found).resolve())
        rustc = str(target) if target is not None else found
    try:
        result = subprocess.run(
            [rustc, "--print", "sysroot"], capture_output=True, text=True, timeout=120,
            check=False, env=environ, cwd=REPO_ROOT,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    sysroot = result.stdout.strip()
    if result.returncode != 0 or not sysroot:
        return None
    return Path(sysroot)


def is_trust_sysroot(sysroot: Path) -> bool:
    """obligation_cert_store.rs: an absolute sysroot with `lib/rustlib` and `bin/trustc`."""
    return (
        sysroot.is_absolute()
        and (sysroot / "lib" / "rustlib").is_dir()
        and (sysroot / "bin" / "trustc").is_file()
    )


# obligation_cert_store.rs's control pair (CHECKER_PROBE_SMT2/CHECKER_PROBE_ALETHE):
# a one-step Alethe refutation of `p` and `not p` that any working checker accepts.
CHECKER_PROBE_SMT2 = "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n"
CHECKER_PROBE_ALETHE = "(assume t0 p)\n(assume t1 (not p))\n(step t2 (cl) :rule resolution :premises (t1 t0))\n"


def clean_passes_control_probe(clean: Path, environ: dict) -> bool:
    """Whether `clean` fully verifies the control proof, judged as the verifier judges it.

    A Trust sysroot `clean` built without `carcara-verify` refuses every proof;
    the verifier then skips it for the managed package, so the gate must too.
    """
    with tempfile.TemporaryDirectory() as directory:
        certificate = Path(directory) / "cert.json"
        certificate.write_text(json.dumps({
            "type": "alethe_certificate", "version": "1.0",
            "problem": CHECKER_PROBE_SMT2, "proof": CHECKER_PROBE_ALETHE,
        }))
        try:
            result = subprocess.run(
                [str(clean), "cert", "verify-external", str(certificate), "--verbose"],
                capture_output=True, text=True, timeout=120, check=False, env=environ,
            )
        except (OSError, subprocess.TimeoutExpired):
            return False
    lines = [line.strip().lower() for line in result.stdout.splitlines()]
    return (
        result.returncode == 0
        and "external certificate verification: passed" in lines
        and "type: alethe smt proof" in lines
        and "proof status: fully verified" in lines
        and not any(word in line for line in lines for word in ("failed", "holey", "incomplete"))
    )


def resolve_tool(tool: str, host: str, environ: dict, platform: str) -> Optional[Tuple[Path, str]]:
    """Return (executable, route) or None; raise ResolveError for a broken explicit override."""
    path_env = environ.get("PATH", "")
    home = environ.get("HOME", "")
    for name in OVERRIDES[tool]:
        if name in environ:
            # An explicit override is authoritative: the verifier never repairs
            # a missing or invalid one through fallback discovery.
            return resolve_override(tool, name, environ[name]), f"env-override:{name}"
    if tool == "ay":
        # ay_identity.rs: the build toolchain's own `bin/ay`, and nothing else.
        sysroot = build_compiler_sysroot(environ)
        if sysroot is None:
            return None
        found = executable_file(sysroot / "bin" / "ay")
        return (found, "toolchain-sysroot") if found is not None else None
    # obligation_cert_store.rs: the build toolchain's own checker first, the
    # package only when that toolchain ships no capable one.
    sysroot = build_compiler_sysroot(environ)
    if sysroot is not None and is_trust_sysroot(sysroot):
        found = executable_file(sysroot / "bin" / tool)
        if found is not None and clean_passes_control_probe(found, environ):
            return found, "toolchain-sysroot"
    found = packaged_tool(tool, path_env, home, platform)
    if found is not None:
        return found, "aterm-packaged"
    return None


def route_pinning(route: str) -> str:
    """Whether `route` is one of the verifier's naming routes.

    "pinned" means the candidate was NAMED the way the verifier names it; it
    says nothing about the candidate's bytes. For AY, admission is the SHA-256
    comparison against the digest compiled into the trust-cg build, which this
    module cannot see. Nothing here executes an AY. A caller that EXECUTES the
    resolved AY must first obtain admission of exactly those bytes from the
    trust-cg build it qualifies (`trust-cg --print-ay-identity`; see
    scripts/check_aarch64_aot_arithmetic.py `ay_admission`).
    """
    return "pinned" if route.split(":", 1)[0] in PINNED_ROUTES else "unpinned"


def command_init(args: argparse.Namespace) -> int:
    path = args.path
    if path.exists():
        print(f"release_gate_summary: refusing to overwrite retained summary {path}", file=sys.stderr)
        return 1
    path.parent.mkdir(parents=True, exist_ok=True)
    document = {
        "schema": SCHEMA,
        "scope": KERNEL_LAYOUT_SCOPE if args.gate == KERNEL_LAYOUT_GATE else SCOPE,
        "gate": args.gate, "mode": args.mode, "host": args.host,
        "command": args.command, "evidence_dir": args.evidence_dir,
        "started_utc": utc_now(), "status": "incomplete",
        "lanes": [], "exclusions": [], "partitions": [], "solver": None, "solver_drift": [],
    }
    store(path, document)
    print(f"release summary: {path}")
    return 0


def command_lane(args: argparse.Namespace) -> int:
    document = load(args.path)
    record = {"name": args.name, "status": args.status, "updated_utc": utc_now()}
    if args.detail:
        record["detail"] = args.detail
    if args.output:
        record["output"] = args.output
    if args.log:
        record["log"] = args.log
    for existing in document["lanes"]:
        if existing["name"] == args.name:
            for key in ("detail", "output", "log"):
                if key in existing and key not in record:
                    record[key] = existing[key]
            existing.clear()
            existing.update(record)
            break
    else:
        document["lanes"].append(record)
    store(args.path, document)
    return 0


def command_exclusion(args: argparse.Namespace) -> int:
    document = load(args.path)
    key = (args.lane, args.kind, args.value)
    if not any((row["lane"], row["kind"], row["value"]) == key for row in document["exclusions"]):
        document["exclusions"].append({
            "lane": args.lane, "kind": args.kind, "value": args.value,
            "reason": args.reason, "recorded_utc": utc_now(),
        })
    store(args.path, document)
    return 0


def command_partition(args: argparse.Namespace) -> int:
    document = load(args.path)
    record = {"package": args.package, "from_lane": args.from_lane, "covered_by": args.covered_by}
    if record not in document["partitions"]:
        document["partitions"].append(record)
    store(args.path, document)
    return 0


def tool_record(tool: str, binary: Optional[str], route: str) -> Optional[dict]:
    if binary is None:
        return None
    resolved = executable_file(Path(binary))
    if resolved is None:
        raise SystemExit(f"release_gate_summary: {tool} executable is not a file: {binary}")
    version = {"not_executed": AY_NOT_EXECUTED} if tool == "ay" else version_probe(resolved)
    return {**file_identity(resolved), "route": route, "pinning": route_pinning(route),
            "version": version}


def command_solver(args: argparse.Namespace) -> int:
    document = load(args.path)
    document["solver"] = {
        "ay": tool_record("ay", args.ay, args.ay_route),
        "clean": tool_record("clean", args.clean, args.clean_route),
        "recorded_utc": utc_now(),
    }
    store(args.path, document)
    return 0


def solver_drift(document: dict, environ: dict, platform: str) -> list:
    """Re-resolve and re-hash every recorded tool; the run must end on the same bytes."""
    drift = []
    for tool in ("ay", "clean"):
        record = (document.get("solver") or {}).get(tool)
        if record is None:
            continue
        try:
            resolved = resolve_tool(tool, document.get("host", ""), environ, platform)
        except ResolveError as error:
            drift.append(f"{tool}: {error}")
            continue
        if resolved is None or str(resolved[0]) != record["path"]:
            drift.append(f"{tool}: now resolves to {resolved[0] if resolved else 'nothing'}, recorded {record['path']}")
            continue
        try:
            observed = file_identity(Path(record["path"]))
        except OSError as error:
            drift.append(f"{tool}: {error}")
            continue
        if observed["sha256"] != record["sha256"]:
            drift.append(f"{tool}: sha256 {observed['sha256']} differs from recorded {record['sha256']}")
    return drift


def command_blockers(args: argparse.Namespace) -> int:
    for reason in blockers(load(args.path), args.lane_prefix):
        print(reason)
    return 0


def command_finish(args: argparse.Namespace) -> int:
    document = load(args.path)
    document["status"] = args.status
    document["finished_utc"] = utc_now()
    document["solver_drift"] = solver_drift(document, dict(os.environ), sys.platform)
    store(args.path, document)
    reasons = document["non_qualifying_reasons"]
    if reasons:
        print(f"release summary: status={args.status} NON-QUALIFYING ({len(reasons)} reason(s)): {args.path}", file=sys.stderr)
        for reason in reasons:
            print(f"  - {reason}", file=sys.stderr)
    else:
        print(f"release summary: status={args.status} QUALIFYING zero-exclusion solver-required pass: {args.path}", file=sys.stderr)
    # The single stdout word is the shell-facing verdict; details go to stderr.
    print("non-qualifying" if reasons else "qualifying")
    if args.require_qualifying and reasons:
        if document["status"] == "pass":
            document["status"] = "fail"
            document.setdefault("notes", []).append(
                "require mode refused a non-qualifying final verdict; status changed from pass to fail"
            )
            store(args.path, document)
        return NOT_QUALIFYING
    return 0


def command_resolve(args: argparse.Namespace) -> int:
    try:
        resolved = resolve_tool(args.tool, args.host, dict(os.environ), sys.platform)
    except ResolveError as error:
        print(f"release_gate_summary: {error}", file=sys.stderr)
        return RESOLVE_INVALID_OVERRIDE
    if resolved is None:
        return RESOLVE_NOT_FOUND
    found, route = resolved
    print(f"{found}\t{route}\t{route_pinning(route)}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="subcommand")
    commands.required = True

    def with_path(subparser: argparse.ArgumentParser) -> argparse.ArgumentParser:
        # The path is always explicit: the gates never export a TRUST_CG_*/TCG_*
        # control that child targo tests would refuse as an unknown override.
        subparser.add_argument("--path", type=Path, required=True, help="summary document")
        return subparser

    init = with_path(commands.add_parser("init", help="create a new summary document"))
    init.add_argument("--gate", required=True)
    init.add_argument("--mode", required=True, choices=MODES)
    init.add_argument("--host", required=True)
    init.add_argument("--evidence-dir", required=True)
    init.add_argument("--command", default="")
    init.set_defaults(func=command_init)

    lane = with_path(commands.add_parser("lane", help="record or update a lane"))
    lane.add_argument("--name", required=True)
    lane.add_argument("--status", required=True, choices=LANE_STATUSES)
    lane.add_argument("--detail", default="")
    lane.add_argument("--output", default="", help="report directory a lane's own runner retains")
    lane.add_argument("--log", default="", help="retained combined stdout/stderr transcript of the lane")
    lane.set_defaults(func=command_lane)

    exclusion = with_path(commands.add_parser("exclusion", help="record an applied exclusion or --skip"))
    exclusion.add_argument("--lane", required=True)
    exclusion.add_argument("--kind", required=True)
    exclusion.add_argument("--value", required=True)
    exclusion.add_argument("--reason", required=True)
    exclusion.set_defaults(func=command_exclusion)

    partition = with_path(commands.add_parser("partition", help="record a package moved to another required lane"))
    partition.add_argument("--package", required=True)
    partition.add_argument("--from-lane", required=True)
    partition.add_argument("--covered-by", required=True)
    partition.set_defaults(func=command_partition)

    solver = with_path(commands.add_parser("solver", help="record resolved AY/Clean executable identities"))
    solver.add_argument("--ay")
    solver.add_argument("--ay-route", default="")
    solver.add_argument("--clean")
    solver.add_argument("--clean-route", default="")
    solver.set_defaults(func=command_solver)

    blockers_parser = with_path(commands.add_parser("blockers", help="print plan-time exclusions and unavailable lanes"))
    blockers_parser.add_argument("--lane-prefix", default="", help="only lanes whose name starts with this prefix")
    blockers_parser.set_defaults(func=command_blockers)

    finish = with_path(commands.add_parser("finish", help="record the final status and print the verdict"))
    finish.add_argument("--status", required=True, choices=FINAL_STATUSES)
    finish.add_argument("--require-qualifying", action="store_true",
                        help=f"exit {NOT_QUALIFYING} and record status fail unless the verdict is qualifying")
    finish.set_defaults(func=command_finish)

    resolve = commands.add_parser(
        "resolve",
        help=(f"print '<path>\\t<route>\\t<pinned|unpinned>'; exit {RESOLVE_NOT_FOUND} if absent, "
              f"{RESOLVE_INVALID_OVERRIDE} for an invalid explicit override"),
    )
    resolve.add_argument("--tool", required=True, choices=("ay", "clean"))
    resolve.add_argument("--host", required=True)
    resolve.set_defaults(func=command_resolve)
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
