# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Named guard receipts and rollback controls; no compiler or remote is run."""

from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
import io
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
import sys
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import bump_trust_ir_pin as bump  # noqa: E402
from rust_guard_transcript import (  # noqa: E402
    validate_exact_rust_test_transcript,
    validate_rust_test_transcript,
)
import test_bump_trust_ir_pin as fixture  # noqa: E402


def receipt(names=("alpha", "beta")):
    return (f"running {len(names)} tests\n"
            + "".join(f"test {name} ... ok\n" for name in names)
            + f"test result: ok. {len(names)} passed; 0 failed; 0 ignored; "
            "0 measured; 0 filtered out; finished in 0.01s\n")


def invalid_receipts(names):
    valid = receipt(names)
    first = names[0]
    return {
        "empty": "",
        "zero": receipt(()),
        "missing-name": valid.replace(f"test {first} ... ok\n", ""),
        "wrong-name": valid.replace(f"test {first} ...", f"test other::{first} ..."),
        "duplicate-name": valid.replace(f"test {first} ... ok\n",
                                        f"test {first} ... ok\ntest {first} ... ok\n"),
        "ignored": valid.replace(f"test {first} ... ok", f"test {first} ... ignored"),
        "failed": valid.replace(f"test {first} ... ok", f"test {first} ... FAILED"),
        "nonzero-failed": valid.replace("0 failed;", "1 failed;"),
        "nonzero-ignored": valid.replace("0 ignored;", "1 ignored;"),
        "measured": valid.replace("0 measured;", "1 measured;"),
        "filtered": valid.replace("0 filtered out;", "1 filtered out;"),
        "bad-count": valid.replace(f"{len(names)} passed;", "999 passed;"),
        "bad-start": valid.replace(f"running {len(names)} tests", "running malformed tests"),
        "bad-summary": valid.replace("test result: ok.", "test result: malformed."),
        "malformed-status": valid.replace(f"test {first} ... ok", f"test {first} .. ok"),
        "indented-record": valid.replace(f"test {first} ... ok", f" test {first} ... ok"),
        "no-end": valid[:valid.index("test result:")],
        "truncated-status": valid.replace(f"test {first} ... ok", f"test {first} ..."),
        "status-before-start": "ok\n" + valid,
        "extra-suite": valid + valid,
        "extra-start": f"running {len(names)} tests\n" + valid,
        "error": "error: compiler guard failed\n" + valid,
        "skip": "SKIP: guard unavailable\n" + valid,
        "trailing-error": valid + "error: guard failed after result\n",
    }


class ExactTranscriptTests(unittest.TestCase):
    def test_one_named_execution_accounts_for_every_filtered_peer(self):
        for total in [1, 5, 72]:
            text = receipt(("module::alpha",)).replace(
                "0 filtered out", f"{total - 1} filtered out"
            )
            self.assertEqual(validate_exact_rust_test_transcript(text, "module::alpha", total), 1)
            pending = text.replace("test module::alpha ... ok", "test module::alpha ... diagnostic\nok")
            self.assertEqual(validate_exact_rust_test_transcript(pending, "module::alpha", total), 1)

    def test_exact_execution_rejects_vacuous_wrong_or_incomplete_receipts(self):
        for label, text in invalid_receipts(("alpha",)).items():
            with self.subTest(label=label), self.assertRaises(ValueError):
                validate_exact_rust_test_transcript(text, "alpha", 1)
        for total in [0, -1, True, "5", None]:
            with self.subTest(total=total), self.assertRaises(ValueError):
                validate_exact_rust_test_transcript(receipt(("alpha",)), "alpha", total)
        for name in ["", "--skip", "two names", None]:
            with self.subTest(name=name), self.assertRaises(ValueError):
                validate_exact_rust_test_transcript(receipt(("alpha",)), name, 1)

    def test_filtered_execution_does_not_weaken_full_guard_receipts(self):
        text = receipt(("alpha",)).replace("0 filtered out", "4 filtered out")
        self.assertEqual(validate_exact_rust_test_transcript(text, "alpha", 5), 1)
        with self.assertRaises(ValueError):
            validate_rust_test_transcript(text, ("alpha",))
        for total in [1, 4, 6]:
            with self.subTest(total=total), self.assertRaises(ValueError):
                validate_exact_rust_test_transcript(text, "alpha", total)


class TranscriptTests(unittest.TestCase):
    def test_valid_exact_nonvacuous_counts(self):
        for names in [("alpha",), ("alpha", "beta"), ("module::alpha", "module::beta")]:
            with self.subTest(names=names):
                self.assertEqual(validate_rust_test_transcript(receipt(names), names), len(names))
                self.assertEqual(validate_rust_test_transcript(
                    receipt(tuple(reversed(names))).replace("\n", "\r\n"), names), len(names))

    def test_nocapture_diagnostics_need_the_pending_names_own_ok(self):
        valid = receipt().replace("test alpha ... ok\n",
                                  "test alpha ... first diagnostic\nsecond diagnostic\nok\n")
        self.assertEqual(validate_rust_test_transcript(valid, ("alpha", "beta")), 2)
        valid = valid.replace("first diagnostic", "")
        self.assertEqual(validate_rust_test_transcript(valid, ("alpha", "beta")), 2)
        for status in ["FAILED", "ignored", "ignored, unavailable", ""]:
            with self.subTest(status=status), self.assertRaises(ValueError):
                validate_rust_test_transcript(valid.replace("\nok\n", f"\n{status}\n"),
                                              ("alpha", "beta"))

    def test_every_incomplete_vacuous_non_green_or_malformed_receipt_refuses(self):
        for label, text in invalid_receipts(("alpha", "beta")).items():
            with self.subTest(label=label), self.assertRaises(ValueError):
                validate_rust_test_transcript(text, ("alpha", "beta"))

    def test_malformed_input_and_rosters_are_typed(self):
        for text in [None, b"\xff", 0, {}, []]:
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "not text"):
                validate_rust_test_transcript(text, ("alpha",))
        for names in [None, [], (), ("alpha", "alpha"), (None,), ([],), ("",)]:
            with self.subTest(names=names), self.assertRaisesRegex(ValueError, "expected-name"):
                validate_rust_test_transcript(receipt(), names)

    def test_reviewed_rosters_match_all_current_guard_functions(self):
        root = Path(bump.__file__).resolve().parents[1]
        guards = {("trust-cg-test", "dependency_authority"): bump.GUARD}
        guards.update({(package, target): relative
                       for relative, package, target in bump.INVENTORY_GUARDS})
        guards.update({(package, target): relative
                       for relative, package, target, _ in bump.FIXTURE_GUARDS})
        guards[("trust-cg-codegen", "must_refuse_corpus")] = bump.CORPUS_GUARD
        # One roster per guard the transaction runs, in its run order.
        self.assertEqual(list(guards), list(bump.GUARD_TEST_NAMES))
        self.assertEqual({key: len(names) for key, names in bump.GUARD_TEST_NAMES.items()},
                         {("trust-cg-test", "dependency_authority"): 4,
                          ("trust-cg-verify", "fsym_layout"): 9,
                          ("trust-cg-verify", "fsym_ub_map"): 21,
                          ("trust-cg-lower", "trust_ir_construct_inventory"): 13,
                          ("trust-cg-codegen", "trust_ir_corpus_roundtrip"): 4,
                          ("trust-cg-codegen", "trust_ir_binary_container"): 20,
                          ("trust-cg-cli", "trust_ir_binary_container"): 6,
                          ("trust-cg-codegen", "must_refuse_corpus"): 5})
        for key, relative in guards.items():
            with self.subTest(guard=key):
                package, target = key
                self.assertEqual(relative, f"crates/{package}/tests/{target}.rs")
                source = (root / relative).read_text()
                observed = re.findall(r"#\[test\]\s*fn ([A-Za-z_0-9]+)\(", source)
                self.assertCountEqual(observed, bump.GUARD_TEST_NAMES[key])
                # Every test is a plain #[test]: no other attribute could hide one.
                self.assertEqual(source.count("#[test]"), len(observed))

    def test_a_fixture_guard_run_missing_any_one_of_its_tests_is_refused(self):
        for _, package, target, _ in bump.FIXTURE_GUARDS:
            names = bump.GUARD_TEST_NAMES[package, target]
            self.assertEqual(validate_rust_test_transcript(receipt(names), names), len(names))
            for missing in names:
                with self.subTest(guard=(package, target), missing=missing):
                    rest = tuple(name for name in names if name != missing)
                    # A shorter, otherwise all-green run (the test was deleted
                    # or filtered away), the full receipt without its line, and
                    # a shorter run whose counts claim the full roster.
                    for text in [receipt(rest),
                                 receipt(names).replace(f"test {missing} ... ok\n", ""),
                                 receipt(rest)
                                 .replace(f"running {len(rest)} tests", f"running {len(names)} tests")
                                 .replace(f"{len(rest)} passed;", f"{len(names)} passed;")]:
                        with self.assertRaises(ValueError):
                            validate_rust_test_transcript(text, names)

    def test_one_packages_container_receipt_is_never_the_others(self):
        codegen = bump.GUARD_TEST_NAMES["trust-cg-codegen", "trust_ir_binary_container"]
        cli = bump.GUARD_TEST_NAMES["trust-cg-cli", "trust_ir_binary_container"]
        self.assertTrue(set(codegen) & set(cli))
        for text, names in [(receipt(cli), codegen), (receipt(codegen), cli)]:
            with self.subTest(names=len(names)), self.assertRaises(ValueError):
                validate_rust_test_transcript(text, names)


class GuardCommandsTests(unittest.TestCase):
    def test_selected_targo_stdout_is_retained_before_named_credit(self):
        commands = bump.Commands(Path("/synthetic/root"), Path("/chosen/targo"))
        commands._test_guard_transport = Mock(return_value="legacy")
        args = ["--unverified", "test", "--locked", "-p", "example",
                "--test", "authority"]
        child = Mock(returncode=0)
        child.communicate.return_value = (receipt(), None)
        output = io.StringIO()
        with patch.object(subprocess, "Popen", return_value=child) as popen, redirect_stdout(output):
            commands.rust_guard(args, ("alpha", "beta"))
        self.assertEqual(output.getvalue(), receipt())
        self.assertEqual(popen.call_args.args[0], ["/chosen/targo", *args, "--", "--test-threads=1"])
        self.assertEqual(popen.call_args.kwargs["stdout"], subprocess.PIPE)
        self.assertEqual(popen.call_args.kwargs["cwd"], commands.root)
        self.assertNotIn("stderr", popen.call_args.kwargs)

    def test_child_failure_never_credits_a_green_receipt_and_keeps_raw_stdout(self):
        commands = bump.Commands(Path("/synthetic/root"), Path("/chosen/targo"))
        commands._test_guard_transport = Mock(return_value="legacy")
        child = Mock(returncode=101)
        child.communicate.return_value = (receipt(), None)
        output = io.StringIO()
        with patch.object(subprocess, "Popen", return_value=child), redirect_stdout(output):
            with self.assertRaisesRegex(bump.Refusal, r"command failed \(101\)"):
                commands.rust_guard(["--unverified", "test"], ("alpha", "beta"))
        self.assertEqual(output.getvalue(), receipt())

    def test_malformed_text_and_decode_failure_are_typed_refusals(self):
        commands = bump.Commands(Path("/synthetic/root"), Path("/chosen/targo"))
        commands._test_guard_transport = Mock(return_value="legacy")
        with patch.object(commands, "run", return_value=None):
            with self.assertRaisesRegex(bump.Refusal, "not text"):
                commands.rust_guard(["--unverified", "test"], ("alpha",))
        error = UnicodeDecodeError("utf-8", b"\xff", 0, 1, "invalid byte")
        with patch.object(commands, "run", side_effect=error):
            with self.assertRaisesRegex(bump.Refusal, "could not be decoded"):
                commands.rust_guard(["--unverified", "test"], ("alpha",))


class GuardTransportTests(unittest.TestCase):
    def test_explicit_ordinary_executes_the_exact_guard_without_worker_discovery(self):
        commands = bump.Commands(Path("/synthetic/root"), Path("/chosen/targo"),
                                 guard_admission="ordinary")
        args = ["--unverified", "test", "--locked", "-p", "pkg", "--test", "guard"]
        with patch.object(commands, "run", return_value=receipt()) as run, \
                redirect_stdout(io.StringIO()):
            commands.rust_guard(args, ("alpha", "beta"))
        run.assert_called_once_with([
            "/chosen/targo", "--unverified", "test", "--config", "build.test-jobs=1", *args[2:]],
            cwd=commands.root, capture=True, env={"RUST_TEST_THREADS": "1"})

    def test_explicit_ordinary_refusal_never_retries_another_interface(self):
        commands = bump.Commands(Path("/synthetic/root"), Path("/chosen/targo"),
                                 guard_admission="ordinary")
        with patch.object(commands, "run", side_effect=bump.Refusal("ordinary admission refused")) as run:
            with self.assertRaisesRegex(bump.Refusal, "ordinary admission refused"):
                commands.rust_guard(["--unverified", "test"], ("alpha", "beta"))
        self.assertEqual(run.call_count, 1)

    def test_explicit_fixed_profile_uses_its_api_and_the_same_owned_serial_config(self):
        commands = bump.Commands(Path("/synthetic/root"), Path("/chosen/targo"),
                                 guard_admission="original-fixed-v1")
        args = ["--unverified", "test", "--locked", "-p", "pkg", "--test", "guard"]
        fixed = (0, '{"version":1,"fixed_admission":"original-fixed-v1"}', "")
        with patch.object(commands, "run", side_effect=[fixed, receipt()]) as run, \
                redirect_stdout(io.StringIO()):
            commands.rust_guard(args, ("alpha", "beta"))
        self.assertEqual([call.args[0] for call in run.call_args_list], [
            ["/chosen/targo", "--resource-capabilities", "--fixed-admission-v1"],
            ["/chosen/targo", "--unverified", "test", "--config", "build.test-jobs=1", *args[2:]],
        ])

    def test_explicit_fixed_refusal_never_retries_worker_or_legacy(self):
        positive = '{"version":1,"fixed_admission":"original-fixed-v1"}'
        replies = [
            (0, '{"version":1,"fixed_admission":null}', ""),
            (0, '{"version":true,"fixed_admission":"original-fixed-v1"}', ""),
            (0, '{"version":2,"fixed_admission":"original-fixed-v1"}', ""),
            (0, '{"version":1,"fixed_admission":"other"}', ""),
            (0, '{"version":1,"fixed_admission":"original-fixed-v1","extra":true}', ""),
            (0, '{"version":3,"cpu_workers":true,"supports_invocation":true}', ""),
            (0, 'not JSON', positive), (0, "", positive),
            (1, positive, "fixed admission refused"),
            (1, "", "error: unexpected argument '--resource-capabilities' found\nUsage: targo"),
        ]
        for reply in replies:
            commands = bump.Commands(Path("/synthetic/root"), Path("/chosen/targo"),
                                     guard_admission="original-fixed-v1")
            with self.subTest(reply=reply), patch.object(commands, "run", return_value=reply) as run:
                with self.assertRaises(bump.Refusal):
                    commands.rust_guard(["--unverified", "test"], ("alpha", "beta"))
                self.assertEqual(run.call_count, 1)

    def commands(self):
        return bump.Commands(Path("/synthetic/root"), Path("/chosen/targo"))

    def test_native_exact_invocation_uses_its_owned_serial_config(self):
        commands = self.commands()
        args = ["--unverified", "test", "--locked", "-p", "pkg", "--test", "guard"]
        for version in (2, 3):
            reply = (0, f'{{"version":{version},"cpu_workers":true,"supports_invocation":true}}', "")
            with self.subTest(version=version), patch.object(commands, "run", return_value=reply) as run:
                self.assertEqual(commands._test_guard_transport(args), "native")
            argv = run.call_args.args[0]
            self.assertEqual(argv, ["/chosen/targo", "--resource-capabilities", "--",
                                   "--unverified", "test", "--config", "build.test-jobs=1", *args[2:]])
            self.assertTrue(run.call_args.kwargs["capture_status"])

    def test_native_warning_stays_separate_and_visible(self):
        commands = self.commands()
        warning = "warning: UNVERIFIED: `targo test` emits no proof claim\n"
        child = Mock(returncode=0)
        child.communicate.return_value = (
            '{"version":3,"cpu_workers":true,"supports_invocation":true}\n', warning)
        diagnostics = io.StringIO()
        with patch.object(subprocess, "Popen", return_value=child) as popen, \
                redirect_stderr(diagnostics):
            self.assertEqual(commands._test_guard_transport(["--unverified", "test"]), "native")
        self.assertEqual(popen.call_args.kwargs["stdout"], subprocess.PIPE)
        self.assertEqual(popen.call_args.kwargs["stderr"], subprocess.PIPE)
        self.assertEqual(diagnostics.getvalue(), warning)

    def test_diagnostics_cannot_supply_or_override_capability_json(self):
        positive = '{"version":3,"cpu_workers":true,"supports_invocation":true}'
        negative = '{"version":3,"cpu_workers":false,"supports_invocation":false}'
        for reply in [(0, "", positive), (0, "not JSON", positive),
                      (0, negative, positive), (1, positive, "native admission refused")]:
            commands = self.commands()
            with self.subTest(reply=reply), patch.object(commands, "run", return_value=reply) as run:
                with self.assertRaises(bump.Refusal):
                    commands._test_guard_transport(["--unverified", "test"])
                self.assertEqual(run.call_count, 1)

    def test_actual_separate_pipe_warning_does_not_poison_native_json(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            targo = root / "targo"
            code = ("import sys\n"
                    "sys.stderr.write('warning: explicit unverified test lane\\n')\n"
                    "print('{\"version\":3,\"cpu_workers\":true,\"supports_invocation\":true}')\n")
            targo.write_text("#!/bin/sh\nexec " + shlex.join([sys.executable, "-c", code]) + ' "$@"\n')
            targo.chmod(0o755)
            commands = bump.Commands(root, targo)
            diagnostic = io.StringIO()
            with patch.object(bump.sys, "stderr", diagnostic):
                self.assertEqual(commands._test_guard_transport(["--unverified", "test"]), "native")
            self.assertEqual(diagnostic.getvalue(), "warning: explicit unverified test lane\n")

    def test_incomplete_channel_response_is_not_a_capability(self):
        commands = self.commands()
        for reply in [(0, '{"version":3,"cpu_workers":true,"supports_invocation":true}'),
                      (0, "{}", None), (False, "{}", ""), (0, "{}", b"warning")]:
            with self.subTest(reply=reply), patch.object(commands, "run", return_value=reply):
                with self.assertRaises(bump.Refusal):
                    commands._test_guard_transport(["--unverified", "test"])

    def test_modern_refusal_malformed_or_unknown_capability_never_falls_back(self):
        for reply in [
            (0, '{"version":3,"cpu_workers":false,"supports_invocation":false}', ""),
            (0, '{"version":1,"cpu_workers":true,"supports_invocation":true}', ""),
            (0, '{"version":4,"cpu_workers":true,"supports_invocation":true}', ""),
            (0, '{"version":2,"cpu_workers":false,"supports_invocation":true}', ""),
            (0, '{"version":2,"cpu_workers":true,"supports_invocation":false}', ""),
            (0, '{"version":2,"cpu_workers":1,"supports_invocation":true}', ""),
            (0, '{"version":true,"cpu_workers":true,"supports_invocation":true}', ""),
            (0, 'not JSON', ""), (0, '[]', ""), (1, "", 'native admission refused'),
            (1, "", "error: unexpected argument '--different-flag' found\nUsage: targo"),
        ]:
            commands = self.commands()
            with self.subTest(reply=reply), patch.object(commands, "run", return_value=reply) as run:
                with self.assertRaises(bump.Refusal):
                    commands._test_guard_transport(["--unverified", "test"])
                self.assertEqual(run.call_count, 1)

    def test_only_missing_protocol_plus_branded_legacy_frontend_selects_legacy(self):
        missing = (1, "", "error: unexpected argument '--resource-capabilities' found\nUsage: targo [OPTIONS]")
        commands = self.commands()
        with patch.object(commands, "run", side_effect=[missing, "targo 1.101.0-dev\n"]) as run:
            self.assertEqual(commands._test_guard_transport(["--unverified", "test"]), "legacy")
        self.assertEqual(run.call_args.args[0], ["/chosen/targo", "--unverified", "--version"])
        commands = self.commands()
        with patch.object(commands, "run", side_effect=[missing, "cargo 1.101.0\n"]):
            with self.assertRaisesRegex(bump.Refusal, "branded"):
                commands._test_guard_transport(["--unverified", "test"])

    def test_native_execution_gets_no_manual_harness_override(self):
        commands = self.commands()
        args = ["--unverified", "test", "--locked"]
        with patch.object(commands, "_test_guard_transport", return_value="native"), \
                patch.object(commands, "run", return_value=receipt()) as run, \
                redirect_stdout(io.StringIO()):
            commands.rust_guard(args, ("alpha", "beta"))
        self.assertEqual(run.call_args.args[0], ["/chosen/targo", "--unverified", "test",
                                                "--config", "build.test-jobs=1", "--locked"])

    def test_capability_child_keeps_normal_interruption_cleanup(self):
        commands = self.commands()
        child = Mock(pid=424242)
        child.communicate.side_effect = KeyboardInterrupt()
        with patch.object(subprocess, "Popen", return_value=child), \
                patch.object(bump.os, "killpg") as kill:
            with self.assertRaises(KeyboardInterrupt):
                commands._test_guard_transport(["--unverified", "test"])
        kill.assert_called_once_with(child.pid, bump.signal.SIGTERM)
        child.wait.assert_called_once_with(timeout=5)


class TransactionReceiptTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixture.TransactionTests("runTest")
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)

    def invoke_with_guard_reply(self, selected, reply):
        commands = fixture.SyntheticCommands(self.fixture.root)
        original_run = commands.run

        def run(argv, **kwargs):
            output = original_run(argv, **kwargs)
            if "--test" in argv and (argv[argv.index("-p") + 1],
                                     argv[argv.index("--test") + 1]) == selected:
                if isinstance(reply, BaseException):
                    raise reply
                return reply
            return output

        commands.run = run
        self.fixture.commands = commands
        self.fixture.invoke()

    def test_all_eight_exact_receipts_close_the_transaction_with_unchanged_argv(self):
        self.fixture.test_success_binds_all_seven_files_and_exact_frontend_lanes()
        guards = [call for call in self.fixture.commands.calls if "--test" in call[0]]
        self.assertEqual(len(guards), 8)
        self.assertTrue(all(call[2] for call in guards))
        self.assertEqual([(call[0][call[0].index("-p") + 1], call[0][call[0].index("--test") + 1])
                          for call in guards],
                         [("trust-cg-test", "dependency_authority"),
                          ("trust-cg-verify", "fsym_layout"),
                          ("trust-cg-verify", "fsym_ub_map"),
                          ("trust-cg-lower", "trust_ir_construct_inventory"),
                          ("trust-cg-codegen", "trust_ir_corpus_roundtrip"),
                          ("trust-cg-codegen", "trust_ir_binary_container"),
                          ("trust-cg-cli", "trust_ir_binary_container"),
                          ("trust-cg-codegen", "must_refuse_corpus")])

    def test_every_invalid_receipt_at_every_guard_restores_all_eight_files_and_modes(self):
        for target, names in bump.GUARD_TEST_NAMES.items():
            for label, text in invalid_receipts(names).items():
                with self.subTest(target=target, label=label):
                    with self.assertRaisesRegex(bump.Refusal, "transcript refused"):
                        self.invoke_with_guard_reply(target, text)
                    self.fixture.assert_restored()
                    self.assertIn("restored all eight original files and modes", self.fixture.output.getvalue())
                    self.assertNotIn("Updated TrustIR", self.fixture.output.getvalue())

    def test_a_fixture_guard_receipt_missing_one_test_rolls_the_move_back(self):
        for _, package, target, update in bump.FIXTURE_GUARDS:
            names = bump.GUARD_TEST_NAMES[package, target]
            for missing in names:
                with self.subTest(guard=(package, target), missing=missing):
                    self.fixture.output = io.StringIO()
                    rest = receipt(tuple(name for name in names if name != missing))
                    with self.assertRaisesRegex(bump.Refusal, "transcript refused") as raised:
                        self.invoke_with_guard_reply((package, target), rest)
                    self.assertIn(f"{package} --test {target} is red at the target", str(raised.exception))
                    self.assertIn(f"update {update}", str(raised.exception))
                    self.fixture.assert_restored()
                    self.assertNotIn("Updated TrustIR", self.fixture.output.getvalue())
                    calls = [call[0] for call in self.fixture.commands.calls if "--test" in call[0]]
                    self.assertNotIn("must_refuse_corpus", calls[-1])

    def test_the_cli_receipt_is_not_credited_for_the_codegen_container_guard(self):
        cli = receipt(bump.GUARD_TEST_NAMES["trust-cg-cli", "trust_ir_binary_container"])
        with self.assertRaisesRegex(bump.Refusal, "transcript refused"):
            self.invoke_with_guard_reply(("trust-cg-codegen", "trust_ir_binary_container"), cli)
        self.fixture.assert_restored()

    def test_child_and_decode_failures_at_every_guard_restore_all_eight_files_and_modes(self):
        for target in bump.GUARD_TEST_NAMES:
            for failure in [bump.Refusal("synthetic guard child failed"),
                            UnicodeDecodeError("utf-8", b"\xff", 0, 1, "invalid byte")]:
                with self.subTest(target=target, failure=type(failure).__name__):
                    with self.assertRaises(bump.Refusal):
                        self.invoke_with_guard_reply(target, failure)
                    self.fixture.assert_restored()
                    self.assertNotIn("Updated TrustIR", self.fixture.output.getvalue())

    def test_guard_source_byte_checks_still_refuse_after_valid_named_receipts(self):
        guards = [(bump.GUARD, 9),
                  (bump.INVENTORY_GUARDS[0][0], 10),
                  (bump.INVENTORY_GUARDS[1][0], 11),
                  (bump.FIXTURE_GUARDS[0][0], 12),
                  (bump.FIXTURE_GUARDS[1][0], 13),
                  (bump.FIXTURE_GUARDS[2][0], 14),
                  (bump.CORPUS_GUARD, 15)]
        for relative, selected_step in guards:
            with self.subTest(relative=relative):
                path = self.fixture.root / relative
                original = path.read_bytes()
                commands = fixture.SyntheticCommands(self.fixture.root)

                def mutate(step, root):
                    if step == selected_step:
                        (root / relative).write_bytes(original + b"// changed during guard\n")

                commands.mutate = mutate
                self.fixture.commands = commands
                with self.assertRaisesRegex(bump.Refusal, "guard changed"):
                    self.fixture.invoke()
                self.fixture.assert_restored()
                path.write_bytes(original)


if __name__ == "__main__":
    unittest.main()
