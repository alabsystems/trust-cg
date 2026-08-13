#!/usr/bin/env python3
"""Helpers for the baseline-aware panic-family Clippy gate.

Subcommands are intentionally narrow because `check_panic_clippy.sh` owns the
Clippy invocation:

* ``list-packages`` reads Cargo metadata on stdin and emits sorted workspace
  package names, excluding the policy-exempt verifier crate.
* ``summarize`` reads Cargo JSONL logs plus their ``.status`` files, accepts
  panic-family diagnostics up to the deterministic per-file source baseline,
  and rejects count increases or unrelated compiler errors.

Exit 0 means the ratchet held, 1 means a source/compilation regression, and 2
means the gate itself was malformed or incompletely wired.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
import unittest
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


PANIC_LINTS = frozenset(
    {
        "clippy::unwrap_used",
        "clippy::expect_used",
        "clippy::panic",
        "clippy::unreachable",
        "clippy::todo",
    }
)
EXCLUDED_PACKAGES = frozenset({"trust-cg-verify"})


class ToolingError(RuntimeError):
    pass


@dataclass(frozen=True, order=True)
class LintDiagnostic:
    file: str
    line: int
    column: int
    code: str
    message: str
    package: str


@dataclass(frozen=True)
class CompileError:
    package: str
    code: str
    message: str


@dataclass
class PackageLog:
    package: str
    status: int
    lints: list[LintDiagnostic]
    compile_errors: list[CompileError]
    unrelated_notes: int
    non_json_lines: list[str]


def workspace_packages(metadata: dict[str, object]) -> list[str]:
    members = set(metadata.get("workspace_members", []))
    packages: list[str] = []
    for raw in metadata.get("packages", []):
        if not isinstance(raw, dict):
            continue
        package_id = raw.get("id")
        name = raw.get("name")
        if package_id in members and isinstance(name, str) and name not in EXCLUDED_PACKAGES:
            packages.append(name)
    return sorted(set(packages))


def command_list_packages() -> int:
    try:
        metadata = json.load(sys.stdin)
    except (OSError, json.JSONDecodeError) as error:
        raise ToolingError(f"cannot parse Cargo metadata from stdin: {error}") from error
    if not isinstance(metadata, dict):
        raise ToolingError("Cargo metadata must be a JSON object")
    packages = workspace_packages(metadata)
    if not packages:
        raise ToolingError("Cargo metadata contains no in-scope workspace packages")
    for package in packages:
        print(package)
    return 0


def normalize_source_path(file_name: str, repo_root: Path) -> str:
    if not file_name:
        return "<unknown>"
    candidate = Path(file_name)
    if candidate.is_absolute():
        try:
            return candidate.resolve(strict=False).relative_to(repo_root.resolve()).as_posix()
        except ValueError:
            return candidate.as_posix()
    normalized = Path(os.path.normpath(file_name)).as_posix()
    if normalized.startswith("./"):
        normalized = normalized[2:]
    return normalized


def _primary_span(message: dict[str, object]) -> dict[str, object] | None:
    spans = message.get("spans", [])
    if not isinstance(spans, list):
        return None
    for span in spans:
        if isinstance(span, dict) and span.get("is_primary"):
            return span
    return next((span for span in spans if isinstance(span, dict)), None)


def parse_compiler_message(
    record: dict[str, object], package: str, repo_root: Path
) -> tuple[LintDiagnostic | None, CompileError | None, bool]:
    if record.get("reason") != "compiler-message":
        return None, None, False
    message = record.get("message")
    if not isinstance(message, dict):
        return None, None, False
    code_record = message.get("code")
    code = code_record.get("code", "") if isinstance(code_record, dict) else ""
    level = str(message.get("level", ""))
    text = str(message.get("message", ""))

    if code in PANIC_LINTS:
        span = _primary_span(message)
        file_name = str(span.get("file_name", "<unknown>")) if span else "<unknown>"
        line = int(span.get("line_start", 0)) if span else 0
        column = int(span.get("column_start", 0)) if span else 0
        return (
            LintDiagnostic(
                file=normalize_source_path(file_name, repo_root),
                line=line,
                column=column,
                code=code,
                message=text,
                package=package,
            ),
            None,
            False,
        )
    if level == "error":
        return None, CompileError(package, code or "rustc", text), False
    return None, None, level in {"warning", "note", "help"}


def read_package_log(log_path: Path, repo_root: Path) -> PackageLog:
    status_path = Path(str(log_path) + ".status")
    if not status_path.is_file():
        raise ToolingError(f"missing Clippy status file: {status_path}")
    try:
        status = int(status_path.read_text(encoding="utf-8").strip())
    except (OSError, ValueError) as error:
        raise ToolingError(f"invalid Clippy status file {status_path}: {error}") from error

    package = log_path.name.removesuffix(".jsonl")
    lints: dict[tuple[str, int, int, str], LintDiagnostic] = {}
    compile_errors: set[CompileError] = set()
    unrelated_notes = 0
    non_json_lines: list[str] = []
    try:
        lines = log_path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError as error:
        raise ToolingError(f"cannot read Clippy log {log_path}: {error}") from error

    for line in lines:
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            if line.strip():
                non_json_lines.append(line.strip())
            continue
        if not isinstance(record, dict):
            continue
        lint, compile_error, note = parse_compiler_message(record, package, repo_root)
        if lint is not None:
            lints[(lint.file, lint.line, lint.column, lint.code)] = lint
        if compile_error is not None:
            compile_errors.add(compile_error)
        unrelated_notes += int(note)

    # A deny-level panic lint makes rustc/cargo return nonzero by design.  A
    # nonzero status with neither one of those diagnostics nor a structured
    # compiler error means the command itself failed before rustc could report
    # a useful result (bad toolchain, Cargo resolution failure, signal, etc.).
    if status != 0 and not lints and not compile_errors:
        tail = "\n".join(non_json_lines[-8:])
        detail = f"\n{tail}" if tail else ""
        raise ToolingError(
            f"Clippy package {package!r} exited {status} without structured diagnostics{detail}"
        )

    return PackageLog(
        package=package,
        status=status,
        lints=sorted(lints.values()),
        compile_errors=sorted(compile_errors, key=lambda item: (item.package, item.code, item.message)),
        unrelated_notes=unrelated_notes,
        non_json_lines=non_json_lines,
    )


def load_baseline(path: Path) -> dict[str, int]:
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ToolingError(f"cannot parse panic baseline {path}: {error}") from error
    if not isinstance(document, dict) or not isinstance(document.get("per_file"), dict):
        raise ToolingError(f"panic baseline {path} has no per_file object")
    per_file: dict[str, int] = {}
    for file, count in document["per_file"].items():
        if not isinstance(file, str) or not isinstance(count, int) or count < 0:
            raise ToolingError(f"panic baseline {path} has invalid entry {file!r}: {count!r}")
        per_file[file] = count
    return per_file


def lint_regressions(
    diagnostics: Iterable[LintDiagnostic], baseline: dict[str, int]
) -> list[tuple[str, int, int]]:
    current = Counter(diagnostic.file for diagnostic in diagnostics)
    regressions = []
    for file, count in sorted(current.items()):
        accepted = baseline.get(file, 0)
        if count > accepted:
            regressions.append((file, accepted, count))
    return regressions


def summarize(baseline_path: Path, log_dir: Path, repo_root: Path) -> int:
    baseline = load_baseline(baseline_path)
    log_paths = sorted(log_dir.glob("*.jsonl"))
    if not log_paths:
        raise ToolingError(f"no Clippy JSONL logs found in {log_dir}")
    package_logs = [read_package_log(path, repo_root) for path in log_paths]
    diagnostic_map = {
        (diagnostic.file, diagnostic.line, diagnostic.column, diagnostic.code): diagnostic
        for log in package_logs
        for diagnostic in log.lints
    }
    diagnostics = sorted(diagnostic_map.values())
    compile_errors = [error for log in package_logs for error in log.compile_errors]
    regressions = lint_regressions(diagnostics, baseline)

    if compile_errors:
        print("panic-clippy FAILED: unrelated compiler errors prevented a valid lint census.")
        for error in compile_errors:
            print(f"  {error.package}: {error.code}: {error.message}")
    if regressions:
        print("panic-clippy FAILED: production panic-family diagnostics increased.")
        print(f"  {'file':<68} {'base':>6} {'cur':>6} {'delta':>6}")
        for file, accepted, current in regressions:
            print(f"  {file:<68} {accepted:>6} {current:>6} {current - accepted:>+6}")
            for diagnostic in diagnostics:
                if diagnostic.file == file:
                    print(
                        f"    {diagnostic.line}:{diagnostic.column} "
                        f"{diagnostic.code}: {diagnostic.message}"
                    )

    if compile_errors or regressions:
        return 1

    nonzero_packages = sum(log.status != 0 for log in package_logs)
    notes = sum(log.unrelated_notes for log in package_logs)
    print(
        "panic-clippy OK: "
        f"{len(diagnostics)} accepted diagnostics across {len(package_logs)} packages "
        f"({nonzero_packages} deny-level Clippy exits; {notes} unrelated notes)."
    )
    return 0


class SummarizerSelfTests(unittest.TestCase):
    def test_workspace_package_selection_is_sorted_and_excludes_verify(self) -> None:
        metadata = {
            "workspace_members": ["b 0.1", "verify 0.1", "a 0.1"],
            "packages": [
                {"id": "b 0.1", "name": "b"},
                {"id": "verify 0.1", "name": "trust-cg-verify"},
                {"id": "a 0.1", "name": "a"},
                {"id": "external 1.0", "name": "external"},
            ],
        }
        self.assertEqual(workspace_packages(metadata), ["a", "b"])

    def test_lint_comparison_is_per_file(self) -> None:
        diagnostics = [
            LintDiagnostic("crates/a/src/lib.rs", 1, 1, "clippy::panic", "a", "a"),
            LintDiagnostic("crates/a/src/lib.rs", 2, 1, "clippy::todo", "b", "a"),
            LintDiagnostic("crates/b/src/lib.rs", 1, 1, "clippy::panic", "c", "b"),
        ]
        self.assertEqual(
            lint_regressions(diagnostics, {"crates/a/src/lib.rs": 1, "crates/b/src/lib.rs": 1}),
            [("crates/a/src/lib.rs", 1, 2)],
        )

    def test_parses_primary_panic_lint_span(self) -> None:
        record = {
            "reason": "compiler-message",
            "message": {
                "code": {"code": "clippy::unwrap_used"},
                "level": "error",
                "message": "used unwrap",
                "spans": [
                    {
                        "file_name": "crates/a/src/lib.rs",
                        "line_start": 4,
                        "column_start": 9,
                        "is_primary": True,
                    }
                ],
            },
        }
        lint, error, note = parse_compiler_message(record, "a", Path("/repo"))
        self.assertIsNone(error)
        self.assertFalse(note)
        self.assertEqual(lint.file if lint else None, "crates/a/src/lib.rs")
        self.assertEqual(lint.line if lint else None, 4)

    def test_non_panic_error_is_a_compile_failure(self) -> None:
        record = {
            "reason": "compiler-message",
            "message": {
                "code": {"code": "E0308"},
                "level": "error",
                "message": "mismatched types",
                "spans": [],
            },
        }
        lint, error, note = parse_compiler_message(record, "a", Path("/repo"))
        self.assertIsNone(lint)
        self.assertEqual(error.code if error else None, "E0308")
        self.assertFalse(note)

    def test_end_to_end_accepts_a_baselined_deny_exit(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline = root / "baseline.json"
            logs = root / "logs"
            logs.mkdir()
            baseline.write_text(
                json.dumps({"per_file": {"crates/a/src/lib.rs": 1}}), encoding="utf-8"
            )
            record = {
                "reason": "compiler-message",
                "message": {
                    "code": {"code": "clippy::panic"},
                    "level": "error",
                    "message": "panic macro",
                    "spans": [
                        {
                            "file_name": "crates/a/src/lib.rs",
                            "line_start": 1,
                            "column_start": 1,
                            "is_primary": True,
                        }
                    ],
                },
            }
            duplicate = json.loads(json.dumps(record))
            duplicate["message"]["message"] = "same site rendered by another target"
            (logs / "a.jsonl").write_text(
                json.dumps(record) + "\n" + json.dumps(duplicate) + "\n",
                encoding="utf-8",
            )
            (logs / "a.jsonl.status").write_text("1\n", encoding="utf-8")
            self.assertEqual(summarize(baseline, logs, root), 0)


def run_self_tests() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(SummarizerSelfTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("list-packages", help="read Cargo metadata JSON from stdin")
    summarize_parser = subparsers.add_parser("summarize", help="summarize Clippy JSONL logs")
    summarize_parser.add_argument("baseline", type=Path)
    summarize_parser.add_argument("log_dir", type=Path)
    summarize_parser.add_argument("repo_root", type=Path)
    subparsers.add_parser("self-test", help="run helper unit tests")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.command == "list-packages":
            return command_list_packages()
        if args.command == "summarize":
            return summarize(args.baseline, args.log_dir, args.repo_root.resolve())
        if args.command == "self-test":
            return run_self_tests()
        raise ToolingError(f"unknown command: {args.command}")
    except ToolingError as error:
        print(f"check_panic_clippy: tooling error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
