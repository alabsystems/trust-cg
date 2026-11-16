"""Ordinary subprocess/receipt/rollback controls; no real compiler or remote."""

from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import bump_trust_ir_pin as bump
import test_bump_trust_ir_pin as fixture
from test_bump_trust_ir_pin_transcript import receipt


ARGS = ["--unverified", "test", "--locked", "-p", "trust-cg-test",
        "--test", "dependency_authority"]
CONFIGURED = [*ARGS[:2], "--config", "build.test-jobs=1", *ARGS[2:]]


class OrdinaryProcessTests(unittest.TestCase):
    def frontend(self, root, text, code=0, checks=""):
        """A real child process checks transport, not compiler or SDK custody."""
        program = root / "targo"
        program.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            f"with open({str(root / 'calls.jsonl')!r}, 'a') as out:\n"
            "    out.write(json.dumps(sys.argv[1:]) + '\\n')\n"
            f"assert sys.argv[1:] == {CONFIGURED!r}, sys.argv\n"
            "assert os.environ['RUST_TEST_THREADS'] == '1'\n"
            + checks
            + f"sys.stdout.write({text!r})\n"
            + f"sys.exit({code})\n"
        )
        program.chmod(0o755)
        return program

    @unittest.skipUnless(os.name == "posix", "POSIX descriptor inheritance")
    def test_real_ordinary_child_keeps_parent_cpu_and_only_advertised_fds(self):
        read_fd, write_fd = os.pipe()
        try:
            with tempfile.TemporaryDirectory() as temporary, tempfile.TemporaryFile() as unrelated:
                root = Path(temporary)
                os.set_inheritable(unrelated.fileno(), True)
                os.write(write_fd, b"q")
                checks = (
                    "assert os.environ['CARGO_BUILD_JOBS'] == '17'\n"
                    f"assert os.environ['TRUST_CPU_IMPLICIT_FD'] == {str(read_fd)!r}\n"
                    f"assert os.read({read_fd}, 1) == b'q'\n"
                    f"os.fstat({write_fd})\n"
                    "import errno\n"
                    "try:\n"
                    f"    os.fstat({unrelated.fileno()})\n"
                    "except OSError as error:\n"
                    "    assert error.errno == errno.EBADF\n"
                    "else:\n"
                    "    raise AssertionError('unadvertised descriptor inherited')\n"
                )
                program = self.frontend(root, receipt(), checks=checks)
                commands = bump.Commands(root, program, guard_admission="ordinary")
                # These are synthetic transport advertisements. The native
                # scheduler still owns actual CPU/SDK admission in live use.
                environment = {
                    "RUST_TEST_THREADS": "99", "CARGO_BUILD_JOBS": "17",
                    "TRUST_CPU_IMPLICIT_FD": str(read_fd),
                    "CARGO_MAKEFLAGS": f"--jobserver-auth={read_fd},{write_fd}",
                }
                before = dict(os.environ)
                with patch.dict(os.environ, environment), redirect_stdout(io.StringIO()):
                    commands.rust_guard(ARGS, ("alpha", "beta"))
                    self.assertEqual(os.environ["RUST_TEST_THREADS"], "99")
                    self.assertEqual(os.environ["CARGO_BUILD_JOBS"], "17")
                self.assertEqual(dict(os.environ), before)
                self.assertEqual((root / "calls.jsonl").read_text().splitlines(),
                                 [json.dumps(CONFIGURED)])
        finally:
            os.close(read_fd)
            os.close(write_fd)

    def test_real_ordinary_child_refusal_or_vacuity_never_reprobes(self):
        names = ("alpha", "beta")
        invalid = [
            (receipt(), 101),
            (receipt(()), 0),
            (receipt(("alpha",)), 0),
            (receipt().replace("test alpha ... ok", "test alpha ... ignored"), 0),
            (receipt().replace("0 filtered out", "1 filtered out"), 0),
        ]
        for text, code in invalid:
            with self.subTest(code=code, text=text), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                program = self.frontend(root, text, code)
                commands = bump.Commands(root, program, guard_admission="ordinary")
                with redirect_stdout(io.StringIO()), self.assertRaises(bump.Refusal):
                    commands.rust_guard(ARGS, names)
                self.assertEqual((root / "calls.jsonl").read_text().splitlines(),
                                 [json.dumps(CONFIGURED)])

    def test_default_native_false_remains_a_refusal_without_ordinary_execution(self):
        commands = bump.Commands(Path("/synthetic/root"), Path("/chosen/targo"))
        self.assertEqual(commands.guard_admission, "native-worker")
        commands.run = Mock(return_value=(
            0, '{"version":3,"cpu_workers":false,"supports_invocation":false}', ""))
        with self.assertRaisesRegex(bump.Refusal, "does not admit.*no legacy fallback"):
            commands.rust_guard(ARGS, ("alpha", "beta"))
        commands.run.assert_called_once()
        self.assertEqual(commands.run.call_args.args[0],
                         ["/chosen/targo", "--resource-capabilities", "--", *CONFIGURED])
        self.assertNotIn("env", commands.run.call_args.kwargs)


class OrdinaryTransactionTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixture.TransactionTests("runTest")
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)

    def invoke(self, selected=None, reply=None):
        commands = fixture.SyntheticCommands(self.fixture.root)
        commands.guard_admission = "ordinary"
        # The inherited fixture forces legacy; bind the actual owner method
        # so these controls exercise ordinary selection and argv construction.
        commands._test_guard_transport = bump.Commands._test_guard_transport.__get__(commands)
        original = commands.run

        def run(argv, **kwargs):
            self.assertNotIn("--resource-capabilities", argv)
            output = original(argv, **kwargs)
            if "--test" in argv:
                key = (argv[argv.index("-p") + 1], argv[argv.index("--test") + 1])
                if key == selected:
                    if isinstance(reply, BaseException):
                        raise reply
                    return reply
            return output

        commands.run = run
        self.fixture.commands = commands
        self.fixture.invoke()
        return commands

    def test_all_eight_original_guards_execute_with_exact_names_and_serial_env(self):
        commands = self.invoke()
        calls = [call[0] for call in commands.calls if "--test" in call[0]]
        self.assertEqual(len(calls), 8)
        self.assertEqual([(a[a.index("-p") + 1], a[a.index("--test") + 1]) for a in calls],
                         list(bump.GUARD_TEST_NAMES))
        self.assertTrue(all(a[1:6] == ["--unverified", "test", "--config", "build.test-jobs=1",
                                      "--locked"] for a in calls))
        self.assertTrue(all("--" not in a and "--test-threads=1" not in a for a in calls))
        self.assertEqual(commands.guard_environments, [{"RUST_TEST_THREADS": "1"}] * 8)
        self.assertEqual(sum(map(len, bump.GUARD_TEST_NAMES.values())), 82)
        self.assertEqual(commands.frontend_count, fixture.FRONTEND_STEPS)

    def test_each_guard_refusal_missing_test_or_vacuity_restores_every_owned_file(self):
        for key, names in bump.GUARD_TEST_NAMES.items():
            for reply in [receipt(()), receipt(names[1:]),
                          bump.Refusal("original normal execution admission refused")]:
                with self.subTest(key=key, reply=type(reply).__name__):
                    self.fixture.output = io.StringIO()
                    with self.assertRaises(bump.Refusal):
                        self.invoke(key, reply)
                    self.fixture.assert_restored()
                    self.assertIn("restored all eight original files and modes",
                                  self.fixture.output.getvalue())
                    self.assertNotIn("Updated TrustIR", self.fixture.output.getvalue())

    def test_ordinary_interruption_preserves_the_original_transaction_rollback(self):
        for key in bump.GUARD_TEST_NAMES:
            with self.subTest(key=key), self.assertRaises(KeyboardInterrupt):
                self.invoke(key, KeyboardInterrupt())
            self.fixture.assert_restored()


if __name__ == "__main__":
    unittest.main()
