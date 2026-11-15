#!/usr/bin/env python3
"""Run the Darwin required set of the root-workspace test matrix (ledger L13-P6).

`scripts/full_test_matrix_hosts.py` partitions every Cargo test suite of the
root workspace into per-host required sets. This runner executes the Darwin
set on an aarch64-apple-darwin host with the installed Trust package
(`scripts/trust_cargo.sh test`, `targo --unverified`; no proof claim about the
build), each suite in its own bounded process group with its own TMPDIR, and
writes report.json:

1. Preflight: the Darwin floor's identity record (Trust package, host tools,
   proof-tool file digests, Cargo configuration, source fingerprint), and the
   AY and Clean the verifier's child processes resolve, with their versions
   and SHA-256.
2. The opcode-evidence inventory gate (`scripts/check_opcode_coverage_gate.sh`,
   default features) and the strict proof gate (`scripts/check_proof_gate.sh
   --test full_database_is_formally_verified`, the full ProofDatabase floor
   through AY and Clean). Neither gate inherits a selection variable
   (PROOF_GATE_FILTER, COVERAGE_GATE_FEATURES), and a gate passes only on a
   zero exit plus the success lines that gate prints for exactly that
   spelling. The strict gate is always run; when the host's tools cannot
   discharge it, its failure is recorded as a named host residual and the
   matrix is not green. The third gate is the downstream-consumer lane
   (`scripts/check_darwin_consumers.py`, ledger L13-P8: TY and AY contract
   targets, the pinned TY consumer re-pointed at this checkout, abi-xback in
   both directions at O0-O3); it passes only on its PASS line, and its
   report.json is kept beside its log.
3. A build phase per package (`test --no-run`), then every Darwin-required
   suite with captured `--show-output`. A suite passes only when it reports at
   least its minimum of executed passes, no failure, no runtime skip line (the
   matrix SKIP spellings, the Darwin floor's broader skip spellings, and the
   opt-in campaign notices such as "set TRUST_CG_RUN_..._TESTS=1 to run")
   either in a test's captured output or anywhere else in the transcript, no
   unlisted ignored test, exactly its host-skipped tests filtered, and no
   leftover entry in its TMPDIR.
4. The proof campaigns: tests that execute only under
   TRUST_CG_RUN_FORMAL_PROOF_TESTS=1, or under TRUST_CG_RUN_EXTERNAL_CERT_TESTS=1
   with the resolved AY and Clean named explicitly, run as separate exact
   invocations with only that suite's campaign variables set.

`--census` runs every suite of the workspace without the classification's
skips and records each test's runtime skip and opt-in lines; it is a
classification aid, never a qualification. `--only SUITE` runs selected
required suites and is never a matrix pass.

The report is testing evidence, plus the strict gate's solver-backed and
checker-accepted results at the strength that gate states. It is not full
compiler completion, release qualification or a Linux result: the Linux set
is classified but not executed by anything in this repository.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from datetime import datetime, timezone
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
SCHEMA = "trust-cg-darwin-full-test-matrix-v1"
HOST = "darwin"
TRUST_CARGO = SCRIPTS / "trust_cargo.sh"
TIMEOUT_RUNNER = SCRIPTS / "run_with_timeout.py"
COVERAGE_GATE = SCRIPTS / "check_opcode_coverage_gate.sh"
PROOF_GATE = SCRIPTS / "check_proof_gate.sh"
CONSUMER_LANE = SCRIPTS / "check_darwin_consumers.py"
OUTPUT_PREFIX = "trust-cg-darwin-full-matrix-"
# Suites whose single-threaded run is long: a bound of their own.
SUITE_TIMEOUT_SECONDS = {
    "trust-cg-codegen/lib": 10800.0,
    "trust-cg-verify/lib": 10800.0,
}
# The library suite of trust-cg-verify (4,500+ tests; the verifier serializes
# its AY subprocesses itself) runs on libtest's default thread count: run one
# test at a time it had not left its first ten percent of tests after 26
# minutes on the Apple M4 Max host (L13-P6 census). Every other suite runs
# with --test-threads=1, as scripts/run_full_test_matrix.sh runs them.
SUITE_TEST_THREADS: dict[str, int | None] = {"trust-cg-verify/lib": None}
# Controls a matrix runner must not pass to child suites or gates: libtest
# capture must stay on, keep-scratch knobs would leave TMPDIR entries by
# request, and the gates' selection variables would replace the full-database
# strict floor (PROOF_GATE_FILTER) or the default coverage inventory
# (COVERAGE_GATE_FEATURES) with another one.
CHILD_UNSET_ENVIRONMENT = (
    "RUST_TEST_NOCAPTURE", "TRUST_CG_KEEP_TEST_OBJECTS", "TRUST_CG_KEEP_LINKRUN",
    "TRUST_CG_RUN_FORMAL_PROOF_TESTS", "TRUST_CG_RUN_EXTERNAL_CERT_TESTS",
    "TRUST_CG_RUN_MEASUREMENT_TESTS", "TRUST_CG_RUN_ROSETTA_LINKRUN",
    "TRUST_CG_AY_TIMEOUT_MS", "TRUST_CG_PROOF_GATE",
    "PROOF_GATE_FILTER", "COVERAGE_GATE_FEATURES",
)
# The gates exactly as the matrix runs them, with the lines each prints only
# after a complete pass of that spelling: check_proof_gate.sh prints the
# full-database line (and AY's STRICT GATE OK summary) only for
# full_database_is_formally_verified, never for the smoke or another test; the
# downstream-consumer lane (L13-P8) prints its PASS line only for a complete,
# all-steps run, never for --only. A zero exit without every line is a failed
# stage. "{stage_output}" is replaced by the stage's own new directory beside
# its log (stage_command).
GATE_STAGES = (
    ("coverage_gate", "coverage-gate", (str(COVERAGE_GATE),), ("check_opcode_coverage_gate: PASS",)),
    ("proof_gate", "proof-gate", (str(PROOF_GATE), "--test", "full_database_is_formally_verified"), (
        "proof gate OK: full-database zero-soundness/no-statistical-fallback floor passed.",
        "STRICT GATE OK:",
    )),
    ("consumer_lane", "consumer-lane", (sys.executable, str(CONSUMER_LANE), "--out", "{stage_output}"), (
        "Darwin consumer lane: PASS",
    )),
)
# A stage whose own steps are bounded inside it gets at least this long.
STAGE_MINIMUM_TIMEOUT_SECONDS = {"consumer_lane": 14400.0}
# An opt-in campaign notice: the test returned without executing its body.
OPT_IN_NOTICE = re.compile(
    r"\bcampaign not requested\b|\bset TRUST_CG_RUN_[A-Z_]+=1\b|\bTRUST_CG_RUN_[A-Z_]+ is not 1\b"
    r"|\b(?:test|lane) not run\b|\bhelper not requested\b"
)
# Report lines that contain a skip spelling but say nothing about the test
# having run: the opcode-evidence audit log's `[skip    ] <opcode>
# pseudo/trap` classification bucket, and fsym's typed per-function
# accounting (`skip function=<name> reason=<Kind> ...`). Each is a row of the
# test's own checked output, never an early return.
NOT_A_SKIP = re.compile(
    r"^\s*\[skip\s*\]\s+\S+::\S+\s+pseudo/trap\b|^\s*skip function=\S+ reason=\S+ detail="
)
STDOUT_HEADER = re.compile(r"^---- (.+) stdout ----$")
TEST_RESULT = re.compile(r"^test (.+) \.\.\. (ok|FAILED|ignored)(?:, .*| <.*>)?$")
# Strict proof gate outcomes the matrix names instead of treating as a
# compiler regression; each is still non-green.
HOST_RESIDUAL_MARKERS = (
    ("proof toolchain unavailable", "AY + Clean proof toolchain unavailable on this host"),
    ("lacks carcara", "the resolved Clean checker lacks carcara-verify"),
    ("self-check", "the resolved AY rejected its own proof self-check"),
    ("reason-unknown", "the resolved AY answered unknown"),
    ("PENDING", "solver-capacity PENDING obligations outside the audited allowlist"),
)


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"required helper is missing: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


HOSTS = _load("_darwin_full_matrix_hosts", SCRIPTS / "full_test_matrix_hosts.py")
FLOOR = HOSTS.darwin_floor()
MATRIX = FLOOR.MATRIX
SHARED = FLOOR.SHARED


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


# ---------------------------------------------------------------------------
# Transcript classification.
# ---------------------------------------------------------------------------

def line_owners(lines: Sequence[str]) -> list[str | None]:
    """The test whose captured output each line is, or None for every other line.

    A section starts at libtest's `---- <name> stdout ----` header (the header
    itself is owned by no test). A test's captured output may hold a child
    test binary's own rollup, so only libtest's section lines end it.
    """
    owners: list[str | None] = []
    owner = None
    for line in lines:
        header = STDOUT_HEADER.fullmatch(line.strip())
        if header:
            owner = header[1]
            owners.append(None)
            continue
        if owner is not None and line.startswith(("successes:", "failures:", "---- ")):
            owner = None
        owners.append(owner)
    return owners


def test_outputs(transcript: str) -> dict[str, list[str]]:
    """Each test's captured lines, from libtest's named stdout sections."""
    outputs: dict[str, list[str]] = {}
    lines = transcript.splitlines()
    for line, owner in zip(lines, line_owners(lines)):
        if owner is not None:
            outputs.setdefault(owner, []).append(line)
    for line in lines:
        header = STDOUT_HEADER.fullmatch(line.strip())
        if header:
            outputs.setdefault(header[1], [])
    return outputs


def is_skip_line(line: str) -> bool:
    """A skip or opt-in spelling that is not one of the exempt report-row shapes."""
    return not NOT_A_SKIP.match(line) and bool(
        MATRIX.SKIP.match(line) or FLOOR.SKIP_LINE.search(line) or OPT_IN_NOTICE.search(line))


def stray_skip_lines(transcript: str) -> list[str]:
    """Skip or opt-in lines outside every test's captured section.

    Such a line was written past libtest's capture (a direct stderr write, a
    child's inherited stream, a write from another test's thread) or follows a
    section marker inside a test's own output; either way no test can be
    credited or exempted for it, so it fails the suite, as the Darwin floor's
    transcript-wide skip scan does. libtest's own result and name-list lines
    are not output.
    """
    lines = transcript.splitlines()
    results = test_results(transcript)
    stray = []
    for line, owner in zip(lines, line_owners(lines)):
        stripped = line.strip()
        if owner is not None or STDOUT_HEADER.fullmatch(stripped) or TEST_RESULT.fullmatch(stripped) \
                or stripped in results:
            continue
        if is_skip_line(line):
            stray.append(stripped)
    return list(dict.fromkeys(stray))


def test_results(transcript: str) -> dict[str, str]:
    results = {}
    for line in transcript.splitlines():
        match = TEST_RESULT.fullmatch(line.strip())
        if match:
            results[match[1]] = match[2]
    return results


def not_executed(transcript: str, exemptions: dict[str, str] | None = None) -> dict[str, list[str]]:
    """Tests whose captured output says their body did not run (skip or opt-in notice).

    `exemptions` maps a test to the one output-line prefix its checked
    behavior prints (full_test_matrix_hosts.SKIP_OUTPUT_EXEMPTIONS).
    """
    exemptions = exemptions or {}
    found: dict[str, list[str]] = {}
    for name, lines in test_outputs(transcript).items():
        prefix = exemptions.get(name)
        hits = [
            line.strip() for line in lines
            if not (prefix and line.strip().startswith(prefix)) and is_skip_line(line)
        ]
        if hits:
            found[name] = sorted(set(hits))
    return found


def classify_suite(
    returncode: int, transcript: str, *, minimum: int, filtered: int | None, ignored: Sequence[str] | None,
    doc: bool, exemptions: dict[str, str] | None = None,
) -> dict:
    """Pass only a complete, captured suite with enough executed passes and nothing hidden.

    `filtered` is the exact number of tests the invocation filters out (None
    for a campaign run, which selects its tests by exact name); `ignored` the
    exact ignored test names (None allows any, for doc-tests).
    """
    errors: list[str] = []
    parsed = MATRIX.parse_log(transcript.splitlines(), mode="plain", rc=returncode, capture_available=True)
    if returncode != 0:
        errors.append(f"command exited {returncode}")
    for problem in parsed["parse_problems"]:
        errors.append(f"transcript problem: {problem}")
    if parsed["suites"] != 1 or parsed["incomplete_suites"]:
        errors.append(f"expected exactly one completed suite, observed {parsed['suites']} "
                      f"({parsed['incomplete_suites']} incomplete)")
    results = test_results(transcript)
    failed = sorted(name for name, outcome in results.items() if outcome == "FAILED")
    if parsed["failed"] or failed:
        errors.append(f"{max(parsed['failed'], len(failed))} failed: {', '.join(failed[:20])}"
                      + (" ..." if len(failed) > 20 else ""))
    skipped = not_executed(transcript, exemptions)
    for name, lines in sorted(skipped.items()):
        errors.append(f"did not execute {name}: {lines[0]}")
    # matrix_results attributes a test's output up to the next test's header,
    # past a nested section marker; its SKIP findings count here too.
    for detail in parsed["runtime_skip_details"]:
        prefix = (exemptions or {}).get(detail["test"])
        messages = [message for message in detail["messages"] if not (prefix and message.startswith(prefix))]
        if messages:
            skipped.setdefault(detail["test"], sorted(set(messages)))
            errors.append(f"runtime SKIP in {detail['test']}: {'; '.join(messages)}")
    for line in parsed["unattributed_skips"]:
        errors.append(f"unattributed runtime skip: {line}")
    for line in stray_skip_lines(transcript):
        errors.append(f"skip line outside any test's captured output: {line}")
    observed_ignored = sorted(name for name, outcome in results.items() if outcome == "ignored")
    if ignored is not None and observed_ignored != sorted(ignored):
        unexpected = sorted(set(observed_ignored) - set(ignored))
        missing = sorted(set(ignored) - set(observed_ignored))
        if unexpected:
            errors.append(f"ignored tests not in IGNORED_TESTS: {', '.join(unexpected)}")
        if missing:
            errors.append(f"IGNORED_TESTS entries not ignored by this run: {', '.join(missing)}")
    if filtered is not None and parsed["filtered"] != filtered:
        errors.append(f"filtered {parsed['filtered']} tests, expected exactly {filtered}")
    # `skipped` holds every non-exempt skip either attribution found, so an
    # exempt test's checked line does not cost it its pass.
    executed = parsed["libtest_passed"] - len([name for name in skipped if results.get(name) == "ok"])
    executed = max(0, executed - parsed["unclassified_passes"])
    required = max(minimum, 1)
    if executed < required:
        errors.append(f"executed passes {executed} are below the required minimum {required}")
    counts = {
        key: parsed[key] for key in (
            "libtest_passed", "failed", "ignored", "filtered", "runtime_skipped", "suites", "incomplete_suites",
        )
    }
    counts["executed_passes"] = executed
    return {
        "status": "fail" if errors else "pass", "counts": counts, "minimum": required,
        "matrix_status": parsed["status"], "timeout_detected": parsed["timeout_detected"],
        "failed_tests": failed, "ignored_tests": observed_ignored,
        "not_executed": skipped, "errors": errors, "doc": doc,
    }


# ---------------------------------------------------------------------------
# Processes.
# ---------------------------------------------------------------------------

class Supervisor:
    """Bounded child processes that a cancellation can reach from any thread."""

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.live: set[subprocess.Popen] = set()
        self.cancelled: int | None = None

    def cancel(self, signum: int) -> None:
        with self.lock:
            if self.cancelled is None:
                self.cancelled = signum
            for process in list(self.live):
                try:
                    process.send_signal(signum)
                except ProcessLookupError:
                    pass

    def run(self, command: Sequence[str], log_path: Path, timeout: float, environment: dict,
            *, cwd: Path = ROOT) -> dict:
        bounded = [sys.executable, str(TIMEOUT_RUNNER), "--grace-seconds", "5", str(timeout), *command]
        started = time.monotonic()
        load_start = load_average()
        with log_path.open("x", encoding="utf-8") as log:
            with self.lock:
                if self.cancelled is not None:
                    log.write(f"not started: cancelled by signal {self.cancelled}\n")
                    return {"command": list(command), "returncode": 128 + self.cancelled,
                            "elapsed_seconds": 0.0, "log": log_path.name, "timeout_seconds": timeout}
                try:
                    process = subprocess.Popen(
                        bounded, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                        start_new_session=True, env=environment, stdin=subprocess.DEVNULL,
                    )
                except OSError as error:
                    log.write(f"launch error: {error}\n")
                    return {"command": list(command), "returncode": 125, "elapsed_seconds": 0.0,
                            "log": log_path.name, "timeout_seconds": timeout}
                self.live.add(process)
            try:
                returncode = process.wait()
            finally:
                with self.lock:
                    self.live.discard(process)
        return {
            "command": list(command), "returncode": returncode, "timeout_seconds": timeout,
            "elapsed_seconds": round(time.monotonic() - started, 3), "log": log_path.name,
            "log_sha256": sha256_file(log_path),
            # Other work shares the host; timing-sensitive tests are read with this.
            "load_average": {"start": load_start, "end": load_average()},
        }


def load_average() -> list[float] | None:
    try:
        return [round(value, 2) for value in os.getloadavg()]
    except OSError:
        return None


def child_environment(base: dict | None = None) -> dict:
    environment = FLOOR.child_environment(base)
    for name in CHILD_UNSET_ENVIRONMENT:
        environment.pop(name, None)
    # Parity with scripts/run_full_test_matrix.sh: the large-stack proof and
    # generated-code tests run on a 64 MiB stack, one test at a time.
    environment.setdefault("RUST_MIN_STACK", "67108864")
    return environment


def default_invocation(suite_id: str, census: bool) -> tuple[list[str], dict[str, list[str]], list[str], list[str]]:
    """A suite's host-skipped tests, campaign tests, excluded tests and default libtest filter.

    The default run leaves out, by exact name, every test another host,
    another lane or an opt-in owns and every proof-campaign test (those run in
    their own campaign invocation). A census run leaves out nothing.
    """
    if census:
        return [], {}, [], []
    skipped = HOSTS.host_skipped_tests(suite_id, HOST)
    campaigns = HOSTS.campaign_tests(suite_id)
    excluded = sorted(set(skipped) | {name for names in campaigns.values() for name in names})
    libtest = ["--exact", *[part for name in excluded for part in ("--skip", name)]] if excluded else []
    return skipped, campaigns, excluded, libtest


def classify_campaign(returncode: int, transcript: str, names: Sequence[str]) -> dict:
    """A campaign invocation passes only when exactly its named tests ran and passed."""
    verdict = classify_suite(returncode, transcript, minimum=len(names), filtered=None, ignored=[], doc=False)
    ran = verdict["counts"]["libtest_passed"] + verdict["counts"]["failed"]
    if ran != len(names):
        verdict["errors"].append(f"ran {ran} tests, expected exactly the {len(names)} campaign tests")
        verdict["status"] = "fail"
    return verdict


def cargo_test(suite, jobs: int, *, offline: bool, libtest: Sequence[str] = (), no_run: bool = False) -> list[str]:
    command = [str(TRUST_CARGO), "test", "--locked", *(["--offline"] if offline else []),
               "--color", "never", "-j", str(jobs), *suite.cargo_arguments()]
    if no_run:
        return command + ["--no-run"]
    threads = SUITE_TEST_THREADS.get(suite.id, 1)
    return command + ["--no-fail-fast", "--", "--show-output",
                      *([f"--test-threads={threads}"] if threads else []), *libtest]


# ---------------------------------------------------------------------------
# Proof tools.
# ---------------------------------------------------------------------------

def proof_tool_identities(environment: dict) -> dict:
    """AY and Clean as the verifier's child processes resolve them on Darwin, with versions."""
    resolver = SHARED.proof_tool_resolver()
    record = {}
    for tool in SHARED.PROOF_TOOLS:
        compiler_environment = {key: value for key, value in environment.items()
                                if key not in SHARED.RUNTIME_CHECKER_ENVIRONMENT}
        try:
            found = resolver.resolve_tool(tool, FLOOR.HOST, compiler_environment if tool == "ay" else environment,
                                          sys.platform)
        except resolver.ResolveError as error:
            record[tool] = {"resolved": None, "route": None, "pinned": False, "error": str(error)}
            continue
        if found is None:
            record[tool] = {"resolved": None, "route": None, "pinned": False}
            continue
        path, route = found
        entry = {"resolved": str(path), "route": route, "pinned": resolver.route_pinning(route) == "pinned",
                 "sha256": sha256_file(path), "bytes": path.stat().st_size}
        try:
            version = subprocess.run([str(path), "--version"], capture_output=True, text=True, timeout=30,
                                     check=False, stdin=subprocess.DEVNULL)
            entry["version"] = (version.stdout + version.stderr).strip()[:2000]
        except (OSError, subprocess.TimeoutExpired) as error:
            entry["version_error"] = str(error)
        record[tool] = entry
    return record


def ay_admission(environment: dict) -> dict:
    """The built CLI's answer to whether it admits the resolved AY (no AY is executed)."""
    cli = ROOT / "target" / "debug" / "trust-cg"
    target_dir = environment.get("CARGO_TARGET_DIR")
    if target_dir:
        cli = Path(target_dir) / "debug" / "trust-cg"
    if not cli.is_file():
        return {"error": f"no built CLI at {cli}"}
    try:
        result = subprocess.run([str(cli), "--print-ay-identity"], capture_output=True, text=True, timeout=60,
                                check=False, env=environment, stdin=subprocess.DEVNULL)
    except (OSError, subprocess.TimeoutExpired) as error:
        return {"error": str(error)}
    record = {"cli": str(cli), "returncode": result.returncode, "stderr": result.stderr[-2000:]}
    try:
        record["report"] = json.loads(result.stdout)
    except ValueError:
        record["stdout"] = result.stdout[-2000:]
    return record


# trust-cg-verify's unit tests keep one private copy of the admitted AY per
# user at `<TMPDIR>/trust-cg-verify-ay-exec-uid<uid>/trust-cg/ay-exec/<sha256>/`
# (`ay` and its `ay.first-start` stamp; crates/trust-cg-verify/src/
# ay_private_copy.rs) and reuse it across runs by design. In exactly that
# shape it is recorded as a cache, like the Darwin floor's host-tool caches;
# anything else in it is a leak. The runner removes it with the suite's TMPDIR.
VERIFY_AY_CACHE = re.compile(r"trust-cg-verify-ay-exec-uid\d+")
HEX64 = re.compile(r"[0-9a-f]{64}")


def is_verify_ay_cache(entry: Path) -> bool:
    try:
        if not VERIFY_AY_CACHE.fullmatch(entry.name) or entry.is_symlink() or not entry.is_dir():
            return False
        for directory, directories, files in os.walk(entry):
            parts = Path(directory).relative_to(entry).parts
            if parts in ((), ("trust-cg",)):
                if files or directories != [("trust-cg", "ay-exec")[len(parts)]]:
                    return False
            elif parts == ("trust-cg", "ay-exec"):
                if files or not directories or not all(HEX64.fullmatch(name) for name in directories):
                    return False
            elif len(parts) == 3:
                if directories or not set(files) <= {"ay", "ay.first-start"} or "ay" not in files:
                    return False
            else:
                return False
            if any((Path(directory) / name).is_symlink() for name in (*directories, *files)):
                return False
        return True
    except OSError:
        return False


def check_leftovers(result: dict, directory: Path) -> None:
    """The Darwin floor's TMPDIR leak check, also admitting the verify AY cache in its exact shape."""
    caches = []
    try:
        for entry in directory.iterdir():
            if is_verify_ay_cache(entry):
                caches.append(entry.name)
                shutil.rmtree(entry, ignore_errors=True)
    except OSError:
        pass
    FLOOR.check_temporary_leftovers(result, directory)
    result["temporary_tool_caches"] = sorted([*result.get("temporary_tool_caches", []), *caches])


def host_residuals(transcript: str) -> list[str]:
    return sorted({label for marker, label in HOST_RESIDUAL_MARKERS if marker in transcript})


# ---------------------------------------------------------------------------
# Orchestration.
# ---------------------------------------------------------------------------

def campaign_environment(lane: str, tools: dict) -> tuple[dict, list[str]]:
    """The variables a proof campaign runs with, or the reasons it cannot run here."""
    if lane == "formal":
        return {"TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1"}, []
    if lane == "external-cert":
        problems = [f"{tool}: not resolved" for tool in ("ay", "clean") if not (tools.get(tool) or {}).get("resolved")]
        if problems:
            return {}, problems
        # The verifier's campaigns name the checker explicitly; the codegen
        # JIT source campaign also binds both tools' bytes by SHA-256
        # (crates/trust-cg-codegen/src/compiler_jit_source_campaign.rs).
        return {
            "TRUST_CG_RUN_EXTERNAL_CERT_TESTS": "1",
            "AY_SOLVER_PATH": tools["ay"]["resolved"],
            "TCG_EXTERNAL_CLEAN_CHECKER": tools["clean"]["resolved"],
            "TCG_JIT_REQUEST_CACHE_AY": tools["ay"]["resolved"],
            "TCG_JIT_REQUEST_CACHE_AY_SHA256": tools["ay"].get("sha256", ""),
            "TCG_JIT_REQUEST_CACHE_CLEAN": tools["clean"]["resolved"],
            "TCG_JIT_REQUEST_CACHE_CLEAN_SHA256": tools["clean"].get("sha256", ""),
        }, []
    return {}, [f"unknown campaign lane {lane}"]


def selected_suites(found, only: Sequence[str] | None, census: bool):
    pool = list(found) if census else HOSTS.required_set(found, HOST)
    if not only:
        return pool
    chosen = []
    for name in only:
        matches = [suite for suite in pool if name in (suite.id, suite.name)]
        if len(matches) != 1:
            what = "workspace suite" if census else "Darwin-required suite"
            raise ValueError(f"--only {name!r} does not name exactly one {what}; use the suite id")
        if matches[0] not in chosen:
            chosen.append(matches[0])
    return chosen


def run_suite(supervisor: Supervisor, suite, output: Path, args, environment: dict, tools: dict,
              census: bool) -> dict:
    timeout = SUITE_TIMEOUT_SECONDS.get(suite.id, args.timeout_seconds)
    skipped, campaigns, excluded, libtest = default_invocation(suite.id, census)
    safe = suite.id.replace("/", "--")
    temporary = FLOOR.target_temporary_directory()
    result = supervisor.run(
        cargo_test(suite, args.jobs, offline=args.require_offline_deps, libtest=libtest),
        output / f"{safe}.log", timeout, {**environment, "TMPDIR": f"{temporary}/"},
    )
    transcript = (output / result["log"]).read_text(encoding="utf-8", errors="replace")
    if census:
        parsed = MATRIX.parse_log(transcript.splitlines(), mode="plain", rc=result["returncode"],
                                  capture_available=True)
        results = test_results(transcript)
        verdict = {
            "status": "census", "counts": {key: parsed[key] for key in (
                "libtest_passed", "failed", "ignored", "filtered", "runtime_skipped", "suites", "incomplete_suites")},
            "failed_tests": sorted(name for name, outcome in results.items() if outcome == "FAILED"),
            "ignored_tests": sorted(name for name, outcome in results.items() if outcome == "ignored"),
            "not_executed": not_executed(transcript, HOSTS.skip_output_exemptions(suite.id)),
            "stray_skip_lines": stray_skip_lines(transcript),
            "parse_problems": parsed["parse_problems"],
            "timeout_detected": parsed["timeout_detected"], "errors": [],
        }
    else:
        verdict = classify_suite(
            result["returncode"], transcript, minimum=HOSTS.minimum_passes(suite, HOST),
            filtered=len(excluded), ignored=None if suite.kind == "doc" else HOSTS.ignored_tests(suite.id),
            doc=suite.kind == "doc", exemptions=HOSTS.skip_output_exemptions(suite.id),
        )
    result.update(verdict)
    check_leftovers(result, temporary)
    if census and result["errors"]:
        result["status"] = "census-leak"
    result.update({"id": suite.id, "class": suite.klass, "features": list(suite.features),
                   "host_skipped_tests": skipped, "campaigns": []})
    for lane, names in sorted(campaigns.items()):
        variables, problems = campaign_environment(lane, tools)
        entry = {"lane": lane, "tests": names, "environment": sorted(variables)}
        if problems:
            entry.update(status="fail", errors=[f"campaign cannot run: {problem}" for problem in problems])
        else:
            temporary = FLOOR.target_temporary_directory()
            run = supervisor.run(
                cargo_test(suite, args.jobs, offline=args.require_offline_deps, libtest=["--exact", *names]),
                output / f"{safe}--{lane}.log", timeout,
                {**environment, **variables, "TMPDIR": f"{temporary}/"},
            )
            text = (output / run["log"]).read_text(encoding="utf-8", errors="replace")
            entry.update(run)
            entry.update(classify_campaign(run["returncode"], text, names))
            entry["residuals"] = host_residuals(text) if entry["status"] != "pass" else []
            check_leftovers(entry, temporary)
        result["campaigns"].append(entry)
        if entry["status"] != "pass":
            result["status"] = "fail"
            result["errors"].append(f"{lane} campaign failed")
    return result


def stage_verdict(name: str, returncode: int, text: str, required_lines: Sequence[str]) -> dict:
    """A gate passes on a zero exit that printed every line its full spelling prints on success."""
    errors = [] if returncode == 0 else [f"{name} exited {returncode}"]
    if returncode == 0:
        lines = text.splitlines()
        errors += [f"{name} exited 0 without the success line {marker!r}"
                   for marker in required_lines if not any(marker in line for line in lines)]
    summary = [line.strip() for line in text.splitlines()
               if "STRICT GATE OK" in line
               or line.startswith(("proof gate", "check_opcode_coverage_gate:", "Darwin consumer lane:"))]
    return {
        "status": "fail" if errors else "pass", "errors": errors, "required_lines": list(required_lines),
        "residuals": host_residuals(text) if errors else [], "summary_lines": summary[-5:],
    }


def stage_command(stage: tuple, output: Path, *, jobs: int | None = None, require_clean: bool = False,
                  offline: bool = False) -> list[str]:
    """A GATE_STAGES command with its output directory and the matrix's own run options.

    The consumer lane gets the matrix's job count and clean-tree rule; under
    --require-offline-deps it resolves offline and may not fetch, otherwise it
    may fetch exactly its pinned consumer commits into its own cache.
    """
    key, name, command, _ = stage
    command = [part.replace("{stage_output}", str(output / f"stage--{name}")) for part in command]
    if key == "consumer_lane":
        if jobs is not None:
            command += ["--jobs", str(jobs)]
        if require_clean:
            command.append("--require-clean")
        command.append("--offline" if offline else "--fetch-consumers")
    return command


def run_gate(supervisor: Supervisor, stage: tuple, output: Path, timeout: float, environment: dict,
             command: Sequence[str] | None = None) -> dict:
    """Run one GATE_STAGES entry: its exact command, judged by its own success lines."""
    key, name, default_command, required_lines = stage
    temporary = FLOOR.target_temporary_directory()
    timeout = max(timeout, STAGE_MINIMUM_TIMEOUT_SECONDS.get(key, 0.0))
    result = supervisor.run(list(command if command is not None else default_command), output / f"stage--{name}.log",
                            timeout, {**environment, "TMPDIR": f"{temporary}/"})
    text = (output / result["log"]).read_text(encoding="utf-8", errors="replace")
    result.update(stage_verdict(name, result["returncode"], text, required_lines))
    lane_report = output / f"stage--{name}" / "report.json"
    if lane_report.is_file():
        result["stage_report"] = str(lane_report.relative_to(output))
    check_leftovers(result, temporary)
    return result


def build_groups(suites) -> list[tuple[str, tuple[str, ...], list]]:
    groups: dict[tuple[str, tuple[str, ...]], list] = {}
    for suite in suites:
        groups.setdefault((suite.package, suite.features), []).append(suite)
    return [(package, features, members) for (package, features), members in sorted(groups.items())]


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
                                     allow_abbrev=False)
    parser.add_argument("--list", action="store_true", help="print the Darwin required set without probing or executing")
    parser.add_argument("--out", type=Path, help="new output directory outside the source tree")
    parser.add_argument("--timeout-seconds", type=SHARED.positive_seconds, default=2400.0,
                        help="bound for each suite's Cargo invocation (default: 2400; the library suites have their own)")
    parser.add_argument("--build-timeout-seconds", type=SHARED.positive_seconds, default=14400.0,
                        help="bound for each package's build (default: 14400)")
    parser.add_argument("--stage-timeout-seconds", type=SHARED.positive_seconds, default=7200.0,
                        help="bound for the coverage and strict proof gates (default: 7200; the consumer lane "
                             "gets at least 14400)")
    parser.add_argument("--jobs", type=SHARED.positive_jobs, default=2, help="Cargo build jobs (default: 2)")
    parser.add_argument("--parallel", type=SHARED.positive_jobs, default=1,
                        help="suites run at the same time after the build phase (default: 1)")
    parser.add_argument("--only", action="append", metavar="SUITE",
                        help="run only this Darwin-required suite (any workspace suite with --census), by id or "
                             "name; repeatable; never a matrix pass")
    parser.add_argument("--census", action="store_true",
                        help="run every workspace suite without the classification's skips; never a qualification")
    parser.add_argument("--skip-gates", action="store_true",
                        help="do not run the coverage gate, the strict proof gate or the consumer lane; never a "
                             "matrix pass")
    parser.add_argument("--require-clean", action="store_true", help="refuse to run on a dirty source tree")
    parser.add_argument("--require-offline-deps", action="store_true",
                        help="run Cargo with --offline and refuse unless every pinned Git revision is local")
    parser.add_argument("--archive", nargs=2, type=Path, metavar=("RUN", "DESTINATION"),
                        help="archive a finished run's report and cited logs into DESTINATION (which holds only "
                             "its README.md); nothing is executed")
    parser.add_argument("--archive-nested", nargs=2, type=Path, metavar=("RUN", "DESTINATION"),
                        help="archive a triage run into a new DESTINATION inside an archive whose README cites it")
    args = parser.parse_args(argv)
    if args.archive or args.archive_nested:
        try:
            if args.archive_nested:
                return archive(*args.archive_nested, nested=True)
            return archive(*args.archive)
        except (OSError, ValueError) as error:
            print(f"Darwin full test matrix: archive error: {error}", file=sys.stderr)
            return 1
    try:
        found = HOSTS.suites(HOSTS.load_metadata())
    except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"Darwin full test matrix: inventory error: {error}", file=sys.stderr)
        return 1
    try:
        selected = selected_suites(found, args.only, args.census)
    except ValueError as error:
        parser.error(str(error))
    if args.list:
        for suite in selected:
            skipped = HOSTS.host_skipped_tests(suite.id, HOST)
            campaigns = HOSTS.campaign_tests(suite.id)
            extra = "".join(f" skip={name}" for name in skipped)
            extra += "".join(f" {lane}={','.join(names)}" for lane, names in sorted(campaigns.items()))
            print(f"{suite.id} minimum={HOSTS.minimum_passes(suite, HOST)}{extra}")
        return 0
    try:
        if args.out is None:
            output = Path(tempfile.mkdtemp(prefix=OUTPUT_PREFIX))
        else:
            output = args.out.absolute()
            if output.resolve().is_relative_to(ROOT):
                raise OSError("output must be outside the source tree so logs cannot change source provenance")
            output.mkdir(mode=0o700)
    except OSError as error:
        print(f"Darwin full test matrix: output directory error: {error}", file=sys.stderr)
        return 1
    mode = "census" if args.census else ("only" if args.only else "required")
    report = {
        "schema": SCHEMA,
        "scope": ("Darwin required set of the root-workspace test matrix; testing evidence plus the strict "
                  "proof gate at its stated strength; not completion, release or Linux qualification"),
        "host": FLOOR.HOST, "mode": mode, "status": "incomplete", "started_utc": utc_now(),
        "options": {key: (str(value) if isinstance(value, Path) else value) for key, value in vars(args).items()},
        "inventory": {"summary": HOSTS.summary(found), "suites": [HOSTS.record(suite) for suite in found]},
        # Tests in required suites that no AArch64 matrix executes (other-lane
        # tools or hosts, opt-in campaigns): a residual of every record.
        "required_by_neither_host": HOSTS.required_by_neither_host(),
        "selected": [suite.id for suite in selected],
        "stages": {}, "builds": [], "suites": [], "errors": [],
    }
    report_path = output / "report.json"
    SHARED.write_report(report_path, report)
    print(f"Darwin full test matrix logs: {output}", flush=True)
    supervisor = Supervisor()
    previous = {signum: signal.signal(signum, lambda number, _frame: supervisor.cancel(number))
                for signum in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)}
    environment = child_environment()
    try:
        issues = HOSTS.problems(found)
        if issues:
            raise RuntimeError("inventory is inconsistent: " + "; ".join(issues))
        report["provenance"] = FLOOR.preflight(environment)
        environment["TRUST_TARGO"] = report["provenance"]["tools"]["targo"]
        if args.require_clean and report["provenance"]["dirty"]:
            raise RuntimeError("source tree is dirty; --require-clean refuses to run")
        report["dependency_identity"] = SHARED.dependency_identity(report["provenance"]["tools"]["git"], environment)
        offline = SHARED.dependency_recorder().offline_problems(report["dependency_identity"])
        if offline and args.require_offline_deps:
            report["errors"].extend(f"--require-offline-deps: {problem}" for problem in offline)
            raise RuntimeError("--require-offline-deps refuses this Cargo home")
        tools = proof_tool_identities(environment)
        report["proof_tools"] = tools
        report["proof_tool_problems"] = SHARED.proof_tool_problems(tools)
        SHARED.write_report(report_path, report)
        if not args.skip_gates and mode != "census":
            for stage in GATE_STAGES:
                command = stage_command(stage, output, jobs=args.jobs, require_clean=args.require_clean,
                                        offline=args.require_offline_deps)
                report["stages"][stage[0]] = run_gate(supervisor, stage, output, args.stage_timeout_seconds,
                                                      environment, command)
                SHARED.write_report(report_path, report)
        for package, features, members in build_groups(selected):
            if supervisor.cancelled is not None:
                break
            print(f"Building {package}" + (f" --features {','.join(features)}" if features else ""), flush=True)
            command = [str(TRUST_CARGO), "test", "--locked", *(["--offline"] if args.require_offline_deps else []),
                       "--color", "never", "-j", str(args.jobs), "-p", package,
                       *(["--features", ",".join(features)] if features else []), "--no-run"]
            # Doc-tests are compiled by rustdoc when they run; Cargo refuses
            # to mix --doc with other target selections.
            for suite in members:
                if suite.kind != "doc":
                    command.extend(suite.cargo_arguments()[2 + (2 if features else 0):])
            if all(suite.kind == "doc" for suite in members):
                continue
            label = f"build--{package}" + (f"--{'-'.join(features)}" if features else "")
            build = supervisor.run(command, output / f"{label}.log", args.build_timeout_seconds, environment)
            build.update(package=package, features=list(features), suites=[suite.id for suite in members],
                         status="pass" if build["returncode"] == 0 else "fail")
            report["builds"].append(build)
            SHARED.write_report(report_path, report)
        report["ay_admission"] = ay_admission({**environment, "AY_SOLVER_PATH": (tools.get("ay") or {}).get("resolved") or ""})
        SHARED.write_report(report_path, report)
        lock = threading.Lock()
        with ThreadPoolExecutor(max_workers=args.parallel) as pool:
            futures = {pool.submit(run_suite, supervisor, suite, output, args, environment, tools, args.census): suite
                       for suite in selected}
            for future in as_completed(futures):
                suite = futures[future]
                try:
                    result = future.result()
                except Exception as error:  # a runner defect fails the suite, never the record
                    result = {"id": suite.id, "class": suite.klass, "status": "fail",
                              "errors": [f"runner error: {error!r}"]}
                with lock:
                    report["suites"].append(result)
                    report["suites"].sort(key=lambda row: row["id"])
                    SHARED.write_report(report_path, report)
                print(f"{result['status'].upper()}: {suite.id}", flush=True)
        if supervisor.cancelled is not None:
            report["errors"].append(f"interrupted by signal {supervisor.cancelled}; the run is incomplete")
        report["totals"] = totals(report)
        report["final_source"] = SHARED.source_provenance(report["provenance"]["tools"]["git"])
        if report["final_source"]["source_fingerprint"] != report["provenance"]["source_fingerprint"]:
            report["errors"].append("source changed while suites were running")
        report["final_proof_tools"] = proof_tool_identities(environment)
        if report["final_proof_tools"] != tools:
            report["errors"].append("proof-tool identity changed during the run")
        report["final_dependency_identity"] = SHARED.dependency_identity(report["provenance"]["tools"]["git"], environment)
        changes = SHARED.dependency_recorder().identity_changes(report["dependency_identity"],
                                                                report["final_dependency_identity"])
        report["errors"].extend(f"dependency identity changed during the run: {change}" for change in changes)
        report["status"] = verdict(report, mode, args.skip_gates)
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        report["errors"].append(str(error))
        report["status"] = "fail"
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)
    report["finished_utc"] = utc_now()
    SHARED.write_report(report_path, report)
    print(f"Darwin full test matrix: {report['status'].upper()} ({report_path})")
    unrun = report["required_by_neither_host"]
    print("not executed by any AArch64 matrix (residual, listed in the report): "
          + ", ".join(f"{len(names)} {lane}" for lane, names in unrun.items()))
    for error in report["errors"]:
        print(error, file=sys.stderr)
    return 0 if report["status"] in ("pass", "partial-pass", "census") else 1


def archive(run: Path, destination: Path, *, nested: bool = False) -> int:
    """Copy a finished run's report and the logs it cites into an evidence archive.

    The destination is a directory holding only the README.md its author
    wrote beforehand, or, for a `nested` run (a triage re-run cited by an
    enclosing record), a new directory the enclosing archive's README
    describes. report.json is copied as is; every stage and build log, and
    every log of a suite or campaign that did not pass, is stored
    gzip-compressed; a passing suite's log is cited by the SHA-256 the report
    records. inventory.json lists every stored file in the form
    scripts/check_evidence_archive.py verifies.
    """
    import gzip
    report_path = run / "report.json"
    report = json.loads(report_path.read_text(encoding="utf-8"))
    if report.get("schema") != SCHEMA or report.get("status") == "incomplete":
        raise ValueError(f"{report_path} is not a finished {SCHEMA} report")
    if nested:
        destination.mkdir(parents=False, exist_ok=False)
    elif not (destination / "README.md").is_file():
        raise ValueError(f"{destination} needs its README.md before the payload is archived")
    if any(path.name != "README.md" for path in destination.iterdir()):
        raise ValueError(f"{destination} already holds files other than README.md")
    logs = [stage["log"] for stage in report.get("stages", {}).values() if stage.get("log")]
    # A stage's own report (the consumer lane's report.json) is stored with its log.
    logs += [stage["stage_report"] for stage in report.get("stages", {}).values() if stage.get("stage_report")]
    logs += [build["log"] for build in report.get("builds", []) if build.get("log")]
    for row in report.get("suites", []):
        if row.get("status") != "pass" and row.get("log"):
            logs.append(row["log"])
        logs += [campaign["log"] for campaign in row.get("campaigns", [])
                 if campaign.get("status") != "pass" and campaign.get("log")]
    artifacts = []
    data = report_path.read_bytes()
    (destination / "report.json").write_bytes(data)
    artifacts.append({"path": "report.json", "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)})
    for name in sorted(set(logs)):
        raw = (run / name).read_bytes()
        stored = gzip.compress(raw, compresslevel=9, mtime=0)
        relative = f"logs/{name}.gz"
        (destination / relative).parent.mkdir(parents=True, exist_ok=True)
        (destination / relative).write_bytes(stored)
        artifacts.append({
            "path": relative, "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw),
            "stored_sha256": hashlib.sha256(stored).hexdigest(), "stored_bytes": len(stored),
        })
    inventory = {"source": (report.get("provenance") or {}).get("source_sha"), "artifacts": artifacts}
    (destination / "inventory.json").write_text(json.dumps(inventory, indent=2) + "\n", encoding="utf-8")
    print(f"archived {len(artifacts)} files into {destination}")
    return 0


def totals(report: dict) -> dict:
    rows = report["suites"]
    statuses: dict[str, int] = {}
    for row in rows:
        statuses[row["status"]] = statuses.get(row["status"], 0) + 1
    executed = sum((row.get("counts") or {}).get("executed_passes", 0) for row in rows)
    executed += sum(campaign.get("counts", {}).get("executed_passes", 0)
                    for row in rows for campaign in row.get("campaigns", []))
    return {
        "suites": len(rows), "statuses": statuses, "executed_passes": executed,
        "failed_suites": sorted(row["id"] for row in rows if row["status"] not in ("pass", "census")),
        "builds_failed": sorted(f"{build['package']}{'+' + ','.join(build['features']) if build['features'] else ''}"
                                for build in report["builds"] if build["status"] != "pass"),
    }


def verdict(report: dict, mode: str, skip_gates: bool) -> str:
    if mode == "census":
        return "census" if not report["errors"] else "fail"
    complete = len(report["suites"]) == len(report["selected"])
    suites_green = complete and all(row["status"] == "pass" for row in report["suites"])
    gates_green = not skip_gates and set(report["stages"]) == {key for key, *_ in GATE_STAGES} \
        and all(stage["status"] == "pass" for stage in report["stages"].values())
    if report["errors"] or not suites_green:
        return "fail"
    if mode == "only" or skip_gates:
        return "partial-pass"
    return "pass" if gates_green else "fail"


if __name__ == "__main__":
    raise SystemExit(main())
