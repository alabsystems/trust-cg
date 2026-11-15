"""Exercise run_with_timeout.py's resident-set ceiling without a Linux host.

The real /proc walk is covered on Linux by scripts/test_run_with_timeout.sh;
these tests pin the parser against a synthetic process table and the
supervision loop against an injected probe, so every breach, refusal and
receipt path runs on any host.
"""

from __future__ import annotations

import argparse
import contextlib
import importlib.util
import io
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("run_with_timeout", ROOT / "scripts" / "run_with_timeout.py")
assert SPEC is not None and SPEC.loader is not None
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)

GIB = 1024 ** 3


def arguments(*argv: str) -> argparse.Namespace:
    return RUNNER.parse_args(list(argv))


def run_captured(args: argparse.Namespace, probe=None) -> tuple[int, str]:
    stderr = io.StringIO()
    with contextlib.redirect_stderr(stderr):
        code = RUNNER.run(args, rss_probe=probe)
    return code, stderr.getvalue()


def receipt(stderr: str) -> dict[str, str]:
    lines = [line for line in stderr.splitlines() if line.startswith(RUNNER.RSS_RECEIPT + " ")]
    if len(lines) != 1:
        raise AssertionError(f"expected exactly one RSS receipt, saw {lines!r}")
    return dict(field.split("=", 1) for field in lines[0][len(RUNNER.RSS_RECEIPT) + 1:].split())


def write_process(root: Path, pid: int, command: str, group: int, resident_pages: int | None) -> None:
    directory = root / str(pid)
    directory.mkdir()
    # Field 5 is the process group; the command name may itself contain
    # spaces and parentheses, so the parser must split after the LAST ')'.
    (directory / "stat").write_text(f"{pid} ({command}) S 1 {group} {group} 0 -1 4194560 0\n")
    if resident_pages is not None:
        (directory / "statm").write_text(f"1000 {resident_pages} 10 1 0 50 0\n")


class ProcessGroupResidentSetTests(unittest.TestCase):
    def test_sums_only_members_of_the_requested_group(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            write_process(root, 4100, "cargo", 4100, 300)
            write_process(root, 4101, "rustc (x) ) y", 4100, 200)
            write_process(root, 4102, "unrelated", 999, 1_000_000)
            write_process(root, 4103, "exited-before-statm", 4100, None)
            (root / "self").mkdir()
            (root / "meminfo").write_text("not a process\n")
            observed = RUNNER.process_group_rss_bytes(4100, proc_root=str(root), page_size=4096)
        self.assertEqual(observed, 500 * 4096)

    def test_empty_group_is_zero_but_an_unreadable_table_is_unmeasurable(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            write_process(root, 10, "other", 10, 7)
            self.assertEqual(RUNNER.process_group_rss_bytes(4100, proc_root=str(root), page_size=4096), 0)
            empty = root / "empty"
            empty.mkdir()
            self.assertIsNone(RUNNER.process_group_rss_bytes(4100, proc_root=str(empty), page_size=4096))
            self.assertIsNone(RUNNER.process_group_rss_bytes(
                4100, proc_root=str(root / "absent"), page_size=4096,
            ))


class ResidentSetCeilingTests(unittest.TestCase):
    def test_ceiling_values_must_be_positive_and_finite(self):
        for value in ("0", "-1", "nan", "inf", "sixteen"):
            with self.subTest(value=value), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit):
                    arguments("--max-rss-gib", value, "5", "true")
        self.assertEqual(arguments("--max-rss-gib", "16", "5", "true").max_rss_gib, 16.0)
        self.assertIsNone(arguments("5", "true").max_rss_gib)

    def test_unsupported_host_refuses_before_launch(self):
        with tempfile.TemporaryDirectory() as temp:
            marker = Path(temp) / "ran"
            args = arguments("--max-rss-gib", "4", "5", sys.executable, "-c",
                             f"open({str(marker)!r}, 'w').close()")
            with mock.patch.object(RUNNER, "rss_supervision_support", return_value=None):
                code, stderr = run_captured(args)
            self.assertEqual(code, RUNNER.LAUNCH_ERROR_EXIT)
            self.assertIn("is unsupported on", stderr)
            self.assertFalse(marker.exists(), "an unsupported ceiling must not run the command")
            self.assertNotIn(RUNNER.RSS_RECEIPT, stderr)

    def test_within_ceiling_preserves_status_and_records_receipt(self):
        args = arguments("--max-rss-gib", "2", "10", sys.executable, "-c",
                         "import sys, time; time.sleep(0.3); sys.exit(7)")
        code, stderr = run_captured(args, probe=lambda group: GIB // 2)
        self.assertEqual(code, 7)
        fields = receipt(stderr)
        self.assertEqual(fields["outcome"], "within")
        self.assertEqual(fields["ceiling_gib"], "2")
        self.assertEqual(fields["peak_mib"], "512")
        self.assertGreaterEqual(int(fields["samples"]), 1)

    def test_breach_kills_the_group_without_waiting_for_the_timeout(self):
        args = arguments("--grace-seconds", "30", "--max-rss-gib", "1", "60",
                         sys.executable, "-c", "import time; time.sleep(60)")
        started = time.monotonic()
        code, stderr = run_captured(args, probe=lambda group: 3 * GIB)
        self.assertLess(time.monotonic() - started, 20, "breach waited for the grace or timeout")
        self.assertEqual(code, RUNNER.RSS_LIMIT_EXIT)
        self.assertIn("resident set exceeded 1 GiB (3072 MiB)", stderr)
        self.assertEqual(receipt(stderr)["outcome"], "exceeded")

    def test_unmeasurable_or_failing_probe_cannot_leave_the_ceiling_unenforced(self):
        def broken(group: int) -> int:
            raise PermissionError("proc hidden")

        for name, probe in (("none", lambda group: None), ("raises", broken)):
            with self.subTest(probe=name), mock.patch.object(RUNNER, "RSS_UNMEASURABLE_SECONDS", 0.3):
                args = arguments("--max-rss-gib", "1", "60",
                                 sys.executable, "-c", "import time; time.sleep(60)")
                started = time.monotonic()
                code, stderr = run_captured(args, probe=probe)
                self.assertLess(time.monotonic() - started, 20)
                self.assertEqual(code, RUNNER.RSS_LIMIT_EXIT)
                self.assertIn("cannot be upheld", stderr)
                fields = receipt(stderr)
                self.assertEqual(fields["outcome"], "unmeasurable")
                self.assertEqual(fields["samples"], "0")

    def test_timeout_still_wins_and_keeps_the_receipt(self):
        args = arguments("--grace-seconds", "0.1", "--max-rss-gib", "4", "0.3",
                         sys.executable, "-c", "import time; time.sleep(60)")
        code, stderr = run_captured(args, probe=lambda group: 1)
        self.assertEqual(code, RUNNER.TIMEOUT_EXIT)
        self.assertIn("command exceeded 0.3s", stderr)
        self.assertEqual(receipt(stderr)["outcome"], "within")

    def test_no_ceiling_means_no_probe_and_no_receipt(self):
        args = arguments("5", sys.executable, "-c", "pass")
        code, stderr = run_captured(args, probe=mock.Mock(side_effect=AssertionError("probed")))
        self.assertEqual(code, 0)
        self.assertNotIn(RUNNER.RSS_RECEIPT, stderr)


if __name__ == "__main__":
    unittest.main()
