#!/usr/bin/env python3
"""Parse captured libtest results without treating runtime SKIPs as passes.

Both supported protocols must use --show-output. Stable output is attributed by
libtest's named stdout sections; nightly JSON attaches stdout to each test event.
Suite rollups are checked against named results, never trusted on their own.
This measures observed test outcomes, not formal proof or silent branch coverage.
"""

from __future__ import annotations

import json
import math
import os
import re
import shlex
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable


SHARD_SCHEMA = "trust-cg.test-matrix-shard.v2"
REPORT_SCHEMA = "trust-cg.test-matrix.v2"
OUTCOMES = ("pass", "fail", "skipped", "timeout", "incomplete")
# New producers use SKIP explicitly. Keep recognizing the former proof-campaign
# opt-out spelling so retained captures cannot gain false proof-test credit.
SKIP = re.compile(
    r"^\s*(?:SKIP(?=[:\s])|[A-Za-z_][A-Za-z_0-9:]*: "
    r"external-solver campaign not requested; "
    r"set TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 to run\s*$|"
    r"external certificate campaign not requested; "
    r"set TRUST_CG_RUN_EXTERNAL_CERT_TESTS=1 with explicit "
    r"AY_SOLVER_PATH and TCG_EXTERNAL_CLEAN_CHECKER paths to run\s*$)"
)
ROLLUP = re.compile(
    r"^test result: \S+\. (\d+) passed; (\d+) failed; (\d+) ignored; "
    r"(\d+) measured; (\d+) filtered out;(?: finished in .*)?$"
)
TEST_RESULT = re.compile(r"^test (.+) \.\.\. (ok|FAILED|ignored)(?:, .*| <.*>)?$")
STDOUT_HEADER = re.compile(r"^---- (.+) stdout ----$")
TIMEOUT_MARKERS = (
    "[cargo] ERROR: Command timed out",
    "[trust-cg-timeout] ERROR: Command timed out",
    "run_with_timeout: command exceeded ",
)


def classify_result(result: dict, rc: int) -> str:
    """Keep process failure, missing evidence, and observed test failures distinct."""
    if result["timeout_detected"] or rc == 124:
        return "timeout"
    if result["failed"]:
        return "fail"
    if (rc != 0 or result["parse_problems"] or result["incomplete_suites"]
            or result["unclassified_passes"] or result["unattributed_skips"]
            or result["runtime_skip_reporting"] != "captured"):
        return "incomplete"
    if not result["libtest_passed"] or result["runtime_skipped"] or result["ignored"]:
        return "skipped"
    return "pass"


@dataclass
class Suite:
    label: str
    doc: bool
    declared: int | None
    events: dict[str, str] = field(default_factory=dict)
    started: set[str] = field(default_factory=set)
    skips: dict[str, list[str]] = field(default_factory=dict)
    filtered: int = 0
    complete: bool = False

    def counts(self) -> Counter:
        return Counter(self.events.values())

    def add_output(self, name: str, output: str) -> None:
        for line in output.splitlines():
            if SKIP.match(line):
                messages = self.skips.setdefault(name, [])
                if line.strip() not in messages:
                    messages.append(line.strip())


def parse_log(lines: Iterable[str], *, mode: str, rc: int, capture_available: bool) -> dict:
    if mode not in {"plain", "json"}:
        raise ValueError(f"unsupported libtest output mode: {mode}")
    suites: list[Suite] = []
    current: Suite | None = None
    owner: str | None = None
    next_label = "libtest"
    next_doc = False
    problems: list[str] = []
    unattributed_skips: list[str] = []
    timed_out = rc == 124

    def begin(declared: int | None) -> None:
        nonlocal current, owner
        if current is not None:
            problems.append(f"suite without rollup: {current.label}")
        current = Suite(next_label, next_doc, declared)
        suites.append(current)
        owner = None

    def event(name: str, outcome: str) -> None:
        if current is None or not name:
            problems.append("test result without an identified suite/test")
            return
        if name in current.events:
            problems.append(f"duplicate result: {current.label} / {name}")
            return
        current.events[name] = outcome
        current.started.discard(name)

    def finish(counts: tuple[int, int, int, int, int], *, captured: bool) -> bool:
        nonlocal current, owner
        if current is None:
            if not captured:
                problems.append("suite rollup without suite start")
            return False
        passed, failed, ignored, measured, filtered = counts
        observed = current.counts()
        expected = (observed["ok"], observed["failed"], observed["ignored"])
        consistent = (
            (passed, failed, ignored) == expected
            and measured == 0
            and not current.started
            and (current.declared is None or sum(expected) == current.declared)
        )
        if not consistent:
            # A captured diagnostic may literally contain a fake libtest
            # rollup. It cannot override the separately observed named events.
            if not captured:
                problems.append(f"suite rollup disagrees with named results: {current.label}")
            return False
        current.filtered = filtered
        current.complete = True
        current = None
        owner = None
        return True

    for raw in lines:
        line = raw.strip()
        if not (mode == "json" and line.startswith("{")) and (
            any(marker in line for marker in TIMEOUT_MARKERS)
            or ("timed out after" in line and "killing process group" in line)
        ):
            # Do not interpret a captured negative-control diagnostic as the
            # wrapper's own timeout. A real timeout also supplies rc=124.
            if owner is None:
                timed_out = True

        if mode == "plain":
            header = STDOUT_HEADER.fullmatch(line)
            if current is not None and header and header[1] in current.events:
                owner = header[1]
                continue
            rollup = ROLLUP.fullmatch(line)
            if rollup and finish(tuple(map(int, rollup.groups())), captured=owner is not None):
                continue
            if owner is not None:
                current.add_output(owner, raw)
                continue
        if current is None and line.startswith(("Running ", "Doc-tests ")):
            next_label = line
            next_doc = line.startswith("Doc-tests ")
            continue
        if mode == "plain":
            start = re.fullmatch(r"running (\d+) tests?", line)
            if start:
                begin(int(start[1]))
                continue
            result = TEST_RESULT.fullmatch(line)
            if result:
                event(result[1], {"ok": "ok", "FAILED": "failed", "ignored": "ignored"}[result[2]])
                continue
            if SKIP.match(line):
                unattributed_skips.append(line)
            continue

        if not line.startswith("{"):
            if SKIP.match(line):
                unattributed_skips.append(line)
            continue
        try:
            obj = json.loads(line)
        except (ValueError, TypeError):
            problems.append("malformed libtest JSON line")
            continue
        if not isinstance(obj, dict):
            problems.append("libtest JSON event is not an object")
            continue
        kind, outcome = obj.get("type"), obj.get("event")
        if kind == "suite":
            if outcome == "started":
                declared = obj.get("test_count")
                if type(declared) is not int or declared < 0:
                    problems.append("suite started without a valid test_count")
                    declared = None
                begin(declared)
            elif outcome in {"ok", "failed"}:
                values = [obj.get(key, 0) for key in ("passed", "failed", "ignored", "measured", "filtered_out")]
                if any(type(value) is not int or value < 0 for value in values):
                    problems.append("invalid suite counter")
                else:
                    finish(tuple(values), captured=False)
        elif kind == "test":
            name = obj.get("name")
            if not isinstance(name, str) or not name or current is None:
                problems.append("test event without an identified suite/test")
                continue
            if outcome == "started":
                if name in current.started or name in current.events:
                    problems.append(f"duplicate test start: {name}")
                current.started.add(name)
            elif outcome in {"ok", "failed", "ignored"}:
                event(name, outcome)
                output = obj.get("stdout", "")
                if not isinstance(output, str):
                    problems.append(f"non-string captured stdout: {name}")
                else:
                    current.add_output(name, output)

    incomplete_suites = sum(not suite.complete for suite in suites)
    if incomplete_suites:
        problems.append(f"{incomplete_suites} incomplete suite(s); named partial results retained")
    if unattributed_skips:
        problems.append("runtime SKIP output could not be attributed to a test")
    if not capture_available:
        problems.append("successful-test output unavailable; --show-output capture is required")
    observed = Counter(outcome for suite in suites for outcome in suite.events.values())
    runtime_skips = []
    runtime_skipped = 0
    for index, suite in enumerate(suites):
        for name, messages in sorted(suite.skips.items()):
            outcome = suite.events[name]
            runtime_skips.append({
                "suite": suite.label, "suite_index": index, "test": name,
                "libtest_status": outcome, "messages": messages,
            })
            # A failed test stays failed even when an optional subcheck skipped.
            runtime_skipped += outcome == "ok"
    raw_passed = observed["ok"]
    # Stable libtest postpones successful stdout until the suite ends. If it
    # dies first, a completed `ok` event may still hide an unprinted SKIP. JSON
    # supplies stdout with each completed test event and can retain those passes.
    unclassified = sum(
        outcome == "ok" and name not in suite.skips
        for suite in suites
        if not capture_available or (mode == "plain" and not suite.complete)
        for name, outcome in suite.events.items()
    )
    passed = raw_passed - runtime_skipped - unclassified
    result = {
        "passed": passed, "libtest_passed": raw_passed,
        "unclassified_passes": unclassified,
        "failed": observed["failed"], "ignored": observed["ignored"],
        "doc_ignored": sum(s.counts()["ignored"] for s in suites if s.doc),
        "test_ignored": sum(s.counts()["ignored"] for s in suites if not s.doc),
        "filtered": sum(s.filtered for s in suites),
        "suites": len(suites), "incomplete_suites": incomplete_suites,
        "runtime_skipped": runtime_skipped, "runtime_skip_details": runtime_skips,
        "unattributed_skips": unattributed_skips,
        "runtime_skip_reporting": (
            "unavailable" if not capture_available else
            "partial" if mode == "plain" and incomplete_suites else "captured"
        ),
        "timeout_detected": timed_out,
        "parse_problems": problems,
    }
    result["status"] = classify_result(result, rc)
    return result


def check_cargo_gate(args: list[str]) -> int:
    """Validate a complete named soundness gate using captured stable output.

    The caller must run Cargo with ``-- --show-output``. Unlike a deliberately
    filtered matrix shard, a whole-target gate must execute every discovered
    case. The explicit --allow-filtered policy is reserved for library filters;
    all capture, skip and positive-pass requirements still apply.
    Process errors, incomplete capture, ignored cases and runtime SKIPs all
    return nonzero; a successful rollup alone cannot establish a pass.
    """
    allow_filtered = len(args) == 3 and args[2] == "--allow-filtered"
    if len(args) > 2 and args[2] not in ("--allow-filtered", "--require-unfiltered"):
        raise ValueError("unknown Cargo gate option")
    log_path, rc_text = args[:2]
    rc = int(rc_text)
    with open(log_path, encoding="utf-8", errors="replace") as handle:
        result = parse_log(
            handle, mode="plain", rc=rc,
            capture_available=os.environ.get("RUST_TEST_NOCAPTURE", "0") == "0",
        )
    if result["filtered"] and not allow_filtered:
        result["parse_problems"].append("named gate filtered out discovered tests")
        result["status"] = classify_result(result, rc)
    print(
        f'{result["status"]}: rc={rc}; {result["passed"]} captured passes; '
        f'{result["failed"]} failed; {result["ignored"]} ignored; '
        f'{result["runtime_skipped"]} runtime SKIPs; {result["filtered"]} filtered; '
        f'{result["suites"]} suites; {result["incomplete_suites"]} incomplete suites'
    )
    for problem in result["parse_problems"]:
        print(problem)
    for skip in result["runtime_skip_details"]:
        print(f'runtime SKIP in {skip["test"]}: {"; ".join(skip["messages"])}')
    return 0 if result["status"] == "pass" else 1


def feature_set(cargo_args: str) -> list[str]:
    args = shlex.split(cargo_args)
    features = []
    for index, arg in enumerate(args):
        value = None
        if arg == "--features" and index + 1 < len(args):
            value = args[index + 1]
        elif arg.startswith("--features="):
            value = arg.split("=", 1)[1]
        if value:
            features.extend(value.replace(",", " ").split())
    return sorted(set(features))


def input_identifiers(crate: str, shard: str, cargo_args: str) -> dict:
    args = shlex.split(cargo_args)
    selectors, test_targets = [], []
    for index, arg in enumerate(args):
        if arg in {"--lib", "--tests", "--doc", "--all-targets"}:
            selectors.append(arg)
        elif arg == "--test" and index + 1 < len(args):
            test_targets.append(args[index + 1])
        elif arg.startswith("--test="):
            test_targets.append(arg.split("=", 1)[1])
    return {"crate": crate, "shard": shard, "selectors": selectors, "test_targets": test_targets}


def parse_shard(args: list[str]) -> dict:
    (crate, shard, log_path, elapsed, rc, notes, cargo_args, _post_args, command,
     timeout, timeout_policy, combined_log, mode) = args
    elapsed_seconds = float(elapsed)
    if not math.isfinite(elapsed_seconds) or elapsed_seconds < 0:
        raise ValueError("invalid shard elapsed time")
    command_args = shlex.split(command)
    capture = (
        "--show-output" in command_args and "--nocapture" not in command_args
        and os.environ.get("RUST_TEST_NOCAPTURE", "0") == "0"
    )
    with open(log_path, encoding="utf-8", errors="replace") as handle:
        result = parse_log(handle, mode=mode, rc=int(rc), capture_available=capture)
    return {
        "schema": SHARD_SCHEMA, "crate": crate, "shard": shard, **result,
        "time_s": round(elapsed_seconds, 3), "rc": int(rc),
        "timeout_policy": timeout_policy, "timeout_budget_sec": int(timeout),
        "libtest_output": mode, "command": command,
        "feature_set": feature_set(cargo_args),
        "input_identifiers": input_identifiers(crate, shard, cargo_args),
        "combined_log": combined_log or None,
        "notes": "; ".join(filter(None, [notes, *result["parse_problems"]])),
    }


# landing_checks.sh exit status for each recorded bench-stage result. A stage
# that did not run has no status, and only a green stage is qualifying.
BENCH_STAGE_RESULTS = {
    "green": 0, "red": 1, "inconclusive": 2, "missing-evidence": 3, "error": None,
}
BENCH_STAGE_MODES = {
    "auto": set(BENCH_STAGE_RESULTS),
    # The runner stops before reporting when a required stage is not green.
    "required": {"green"},
    "skipped": {"skipped-non-qualifying"},
    "targeted": {"not-run"},
}


def bench_stage(mode: str, result: str, rc_text: str) -> dict:
    """Validate the matrix's bench-stage marker; never promote a non-green stage."""
    if mode not in BENCH_STAGE_MODES or result not in BENCH_STAGE_MODES[mode]:
        raise ValueError(f"invalid bench stage marker: mode={mode!r} result={result!r}")
    if result in BENCH_STAGE_RESULTS:
        if not re.fullmatch(r"0|[1-9][0-9]{0,2}", rc_text):
            raise ValueError("a bench stage that ran needs its landing_checks.sh exit status")
        rc = int(rc_text)
        expected = BENCH_STAGE_RESULTS[result]
        if expected is None:
            # "error" names every status landing_checks.sh does not define.
            mismatched = rc in BENCH_STAGE_RESULTS.values()
        else:
            mismatched = rc != expected
        if mismatched:
            raise ValueError(f"bench stage result {result!r} disagrees with exit status {rc}")
    elif rc_text:
        raise ValueError("a bench stage that did not run cannot have an exit status")
    else:
        rc = None
    return {"mode": mode, "result": result, "landing_checks_rc": rc, "qualifying": result == "green"}


def aggregate(args: list[str]) -> dict:
    (shards_path, out_path, date, commit, short, rustc, expected,
     proof_mode, proof_result, bench_mode, bench_result, bench_rc) = args
    bench = bench_stage(bench_mode, bench_result, bench_rc)
    with open(shards_path, encoding="utf-8") as handle:
        shards = [json.loads(line) for line in handle if line.strip()]
    if not shards or any(not isinstance(row, dict) for row in shards):
        raise ValueError("expected at least one shard object")
    if len(shards) != int(expected):
        raise ValueError(f"parsed {len(shards)} shards, expected {expected}")
    identities = [(row.get("crate"), row.get("shard")) for row in shards]
    if any(not crate or not shard for crate, shard in identities) or len(set(identities)) != len(shards):
        raise ValueError("missing or duplicate shard identity")
    if any(row.get("schema") != SHARD_SCHEMA or row.get("status") not in OUTCOMES for row in shards):
        raise ValueError("unrecognized shard schema/status; cannot promote legacy counts")
    counters = (
        "passed", "libtest_passed", "unclassified_passes", "failed", "ignored",
        "doc_ignored", "test_ignored", "filtered", "suites", "incomplete_suites",
        "runtime_skipped",
    )
    for row in shards:
        if any(type(row.get(key)) is not int or row[key] < 0 for key in counters):
            raise ValueError("invalid shard counter")
        if row["passed"] + row["runtime_skipped"] + row["unclassified_passes"] != row["libtest_passed"]:
            raise ValueError("inconsistent raw/qualified pass counters")
        if row["ignored"] != row["doc_ignored"] + row["test_ignored"]:
            raise ValueError("inconsistent ignored-test counters")
        if row["incomplete_suites"] > row["suites"]:
            raise ValueError("more incomplete suites than observed suites")
        if (type(row.get("time_s")) not in {int, float}
                or not math.isfinite(row["time_s"]) or row["time_s"] < 0):
            raise ValueError("invalid shard elapsed time")
        if type(row.get("rc")) is not int or type(row.get("timeout_detected")) is not bool:
            raise ValueError("invalid shard process result")
        if row.get("runtime_skip_reporting") not in {"captured", "partial", "unavailable"}:
            raise ValueError("unrecognized runtime skip reporting")
        for key in ("parse_problems", "unattributed_skips"):
            if not isinstance(row.get(key), list) or any(not isinstance(item, str) for item in row[key]):
                raise ValueError(f"invalid {key}")
        if row["status"] != classify_result(row, row["rc"]):
            raise ValueError("shard status disagrees with its observed results")
    totals = {key: sum(row[key] for row in shards) for key in counters}
    totals["outcome_counts"] = {status: sum(row["status"] == status for row in shards) for status in OUTCOMES}
    totals["time_s"] = round(sum(row["time_s"] for row in shards), 3)
    report = {
        "schema": REPORT_SCHEMA, "date": date, "commit": commit,
        "commit_short": short, "rustc": rustc,
        "counting": "Named libtest results; passed excludes observed runtime SKIPs and unavailable capture. Counts are invocations, not unique tests or proof obligations.",
        "proof_gate": {"mode": proof_mode, "result": proof_result},
        "bench_stage": bench,
        "shards": shards, "totals": totals,
    }
    # A malformed input or interrupted write must not destroy the last report.
    destination = Path(out_path)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=destination.parent,
                                         prefix=f".{destination.name}.", delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(json.dumps(report, indent=2, allow_nan=False) + "\n")
        if destination.exists():
            temporary.chmod(destination.stat().st_mode & 0o777)
        os.replace(temporary, destination)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return report


def main(args: list[str]) -> int:
    try:
        if args and args[0] == "check-cargo-gate" and len(args) in (3, 4):
            return check_cargo_gate(args[1:])
        elif args and args[0] == "parse-shard" and len(args) == 14:
            print(json.dumps(parse_shard(args[1:])))
        elif args and args[0] == "aggregate" and len(args) == 13:
            report = aggregate(args[1:])
            print(f"Wrote {args[2]}")
            print(json.dumps(report["totals"], indent=2))
        else:
            raise ValueError(
                "usage: matrix_results.py check-cargo-gate <log> <rc> [--allow-filtered] | "
                "parse-shard <13 fields> | aggregate <12 fields>"
            )
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"matrix result error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
