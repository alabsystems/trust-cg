"""scripts/trust_cargo.sh: what targo and the test executables receive.

A fake Trust package (`bin/targo`, `bin/trustc`) records targo's environment
and arguments, so these tests read exactly what the wrapper hands over.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_cargo.sh"

FAKE_TARGO = f"#!{sys.executable}\n" + r'''import json, os, sys
if sys.argv[1:2] == ["--unverified"] and sys.argv[2:3] and sys.argv[2] in {
    "tippy", "fmt", "fetch", "metadata", "help", "version", "tree",
    "locate-project", "generate-lockfile", "update", "clean", "rm", "trust",
}:
    print("error: `--unverified` is valid only for a Targo compilation command", file=sys.stderr)
    sys.exit(64)
with open(os.environ["FAKE_TARGO_LOG"], "w") as log:
    json.dump({"argv": sys.argv[1:], "env": dict(os.environ)}, log)
sys.exit(int(os.environ.get("FAKE_TARGO_STATUS", "0")))
'''

FAKE_TRUSTC = f"#!{sys.executable}\n" + r'''import os, sys
from pathlib import Path
package = Path(sys.argv[0]).resolve().parent.parent
for name in os.environ:
    if name.startswith(("TRUST_CG_", "TCG_")):
        print(f"environment variable `{name}` is an untracked Trust control", file=sys.stderr)
        sys.exit(1)
if sys.argv[1:] == ["-vV"]:
    print("rustc 1.99.0-dev (trustc 0.1.0)")
    print("host: " + os.environ.get("FAKE_HOST", "aarch64-apple-darwin"))
    sys.exit(0)
if sys.argv[1:] == ["--print", "sysroot"]:
    print(package)
    sys.exit(0)
sys.exit(64)
'''


class TrustCargoTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.package = Path(self.tmp.name).resolve() / "overlay"
        (self.package / "bin").mkdir(parents=True)
        for name, text in (("targo", FAKE_TARGO), ("trustc", FAKE_TRUSTC)):
            path = self.package / "bin" / name
            path.write_text(text)
            path.chmod(0o755)
        self.log = Path(self.tmp.name) / "targo.json"

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def run_wrapper(self, *arguments: str, expected_status: int = 0, **extra: str) -> dict:
        env = {
            key: value for key, value in os.environ.items()
            if not key.startswith(("TRUST_CG_", "TCG_", "TOOLCHAIN_AY_"))
        }
        env.update(TRUST_TARGO=str(self.package / "bin" / "targo"), FAKE_TARGO_LOG=str(self.log))
        env.update(extra)
        result = subprocess.run(
            ["bash", str(SCRIPT), *arguments], env=env, capture_output=True, text=True, check=False
        )
        self.assertEqual(result.returncode, expected_status, result.stderr)
        return json.loads(self.log.read_text())

    def test_targo_gets_the_selected_sysroot_for_the_ay_record(self) -> None:
        call = self.run_wrapper("check", "-p", "trust-cg-verify")
        self.assertEqual(call["env"]["TOOLCHAIN_AY_EXPECTED_SYSROOT"], str(self.package))
        self.assertEqual(call["argv"], ["--unverified", "check", "-p", "trust-cg-verify"])

    def test_tippy_selects_its_own_lane_and_preserves_strict_lint_arguments(self) -> None:
        arguments = [
            "--locked", "-p", "trust-cg-verify", "--lib", "--tests",
            "--no-deps", "--keep-going", "--message-format", "short", "--", "-D", "warnings",
        ]
        call = self.run_wrapper(
            "tippy", *arguments,
            TRUST_CG_RUN_FORMAL_PROOF_TESTS="1",
            TCG_TEST_CONTROL="unchanged",
            RUSTUP_TOOLCHAIN="unrelated",
        )
        self.assertEqual(call["argv"], ["tippy", *arguments])
        self.assertNotIn("TRUST_CG_RUN_FORMAL_PROOF_TESTS", call["env"])
        self.assertNotIn("TCG_TEST_CONTROL", call["env"])
        self.assertNotIn("RUSTUP_TOOLCHAIN", call["env"])
        self.assertEqual(call["env"]["TOOLCHAIN_AY_EXPECTED_SYSROOT"], str(self.package))

    def test_compilation_verbs_keep_the_explicit_unverified_lane(self) -> None:
        # The public native Targo transport set and its built-in aliases.
        for verb in (
            "build", "check", "fix", "clippy", "miri", "test", "run", "bench",
            "doc", "rustc", "rustdoc", "install", "package", "publish",
            "b", "c", "d", "r", "t",
        ):
            with self.subTest(verb=verb):
                call = self.run_wrapper(verb, "--locked", "-p", "trust-cg-verify")
                self.assertEqual(
                    call["argv"], ["--unverified", verb, "--locked", "-p", "trust-cg-verify"]
                )

    def test_noncompiling_and_tool_commands_receive_no_invented_lane(self) -> None:
        for verb, arguments in (
            ("fetch", ["--locked", "--offline"]),
            ("metadata", ["--locked", "--offline", "--no-deps", "--format-version", "1"]),
            ("fmt", ["--all", "--", "--check"]),
            ("help", ["build"]),
            ("version", ["--verbose"]),
            ("tree", ["--locked", "--offline", "--edges", "normal"]),
            ("locate-project", ["--workspace", "--message-format", "json"]),
            ("generate-lockfile", ["--offline"]),
            ("update", ["--locked", "--offline"]),
            ("clean", ["--release"]),
            ("rm", ["obsolete-dependency"]),
            ("trust", ["check", "--locked"]),
        ):
            with self.subTest(verb=verb):
                call = self.run_wrapper(
                    verb, *arguments, TCG_TEST_CONTROL="preserve for executables only",
                    RUSTUP_TOOLCHAIN="unrelated",
                )
                self.assertEqual(call["argv"], [verb, *arguments])
                self.assertNotIn("TCG_TEST_CONTROL", call["env"])
                self.assertNotIn("RUSTUP_TOOLCHAIN", call["env"])
                self.assertEqual(call["env"]["TOOLCHAIN_AY_EXPECTED_SYSROOT"], str(self.package))

    def test_unknown_commands_delegate_unchanged_and_preserve_native_failure(self) -> None:
        arguments = ["--locked", "--", "build", "--unverified"]
        call = self.run_wrapper(
            "future-command", *arguments, expected_status=42, FAKE_TARGO_STATUS="42",
        )
        self.assertEqual(call["argv"], ["future-command", *arguments])

    def test_explicit_user_authority_is_not_stripped_to_make_fetch_succeed(self) -> None:
        arguments = ["--unverified", "--locked", "--offline"]
        call = self.run_wrapper(
            "fetch", *arguments, expected_status=64, FAKE_TARGO_STATUS="64",
        )
        self.assertEqual(call["argv"], ["fetch", *arguments])

    def test_builtin_execution_aliases_keep_their_controls_and_payload(self) -> None:
        for verb in ("t", "r"):
            with self.subTest(verb=verb):
                call = self.run_wrapper(
                    verb, "--locked", "--", "--unverified", "argument with spaces",
                    TCG_TEST_CONTROL="value with spaces",
                )
                self.assertEqual(call["argv"][:2], ["--unverified", verb])
                self.assertEqual(
                    call["argv"][-4:], ["--locked", "--", "--unverified", "argument with spaces"]
                )
                self.assertNotIn("TCG_TEST_CONTROL", call["env"])
                config = call["argv"][call["argv"].index("--config") + 1]
                runner = json.loads(config.split("=", 1)[1])
                self.assertIn("TCG_TEST_CONTROL=value with spaces", runner)

    def test_controls_reach_the_tests_through_the_runner_not_targo(self) -> None:
        call = self.run_wrapper(
            "test", "-p", "trust-cg-verify",
            TRUST_CG_PROOF_IDENTITY_OUT="/tmp/identity.jsonl",
        )
        self.assertNotIn("TRUST_CG_PROOF_IDENTITY_OUT", call["env"])
        self.assertEqual(call["argv"][:2], ["--unverified", "test"])
        self.assertEqual(call["env"]["TOOLCHAIN_AY_EXPECTED_SYSROOT"], str(self.package))
        config = call["argv"][call["argv"].index("--config") + 1]
        self.assertTrue(config.startswith("target.aarch64-apple-darwin.runner="), config)
        runner = json.loads(config.split("=", 1)[1])
        lib = f"{self.package}/lib"
        host_lib = f"{self.package}/lib/rustlib/aarch64-apple-darwin/lib"
        home_lib = f"{os.environ['HOME']}/lib:" if os.environ.get("HOME") else ""
        self.assertEqual(
            runner,
            [
                "/usr/bin/env",
                f"DYLD_FALLBACK_LIBRARY_PATH={lib}:{host_lib}:{home_lib}/usr/local/lib:/usr/lib",
                "TRUST_CG_PROOF_IDENTITY_OUT=/tmp/identity.jsonl",
            ],
        )

    def test_a_linux_runner_carries_no_dyld_path(self) -> None:
        # dyld's SIP stripping is macOS-only; elsewhere the runner is unchanged.
        call = self.run_wrapper(
            "test", "-p", "trust-cg-verify",
            TRUST_CG_PROOF_IDENTITY_OUT="/tmp/identity.jsonl",
            FAKE_HOST="aarch64-unknown-linux-gnu",
        )
        config = call["argv"][call["argv"].index("--config") + 1]
        self.assertTrue(config.startswith("target.aarch64-unknown-linux-gnu.runner="), config)
        runner = json.loads(config.split("=", 1)[1])
        self.assertEqual(runner, ["/usr/bin/env", "TRUST_CG_PROOF_IDENTITY_OUT=/tmp/identity.jsonl"])

    def test_no_controls_means_no_runner(self) -> None:
        call = self.run_wrapper("test", "-p", "trust-cg-verify")
        self.assertNotIn("--config", call["argv"])


if __name__ == "__main__":
    unittest.main()
