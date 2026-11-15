from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import pwd
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "cargo_config_audit.py"
SPEC = importlib.util.spec_from_file_location("cargo_config_audit", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)
COMMITTED = b"[build]\njobs = 2\n[env]\nRUST_MIN_STACK = { value = \"16777216\", force = false }\n"
# The Targo whose config model InstalledTargoTests pins: the harness's resolved
# package (python_unit_tests exports it as BRIDGE_PROBE_TARGO), else PATH.
INSTALLED_TARGO = os.environ.get("BRIDGE_PROBE_TARGO") or shutil.which("targo")


class CargoConfigAuditTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.checkout = self.root / "work" / "repo"
        self.checkout.mkdir(parents=True)
        self.home = self.root / "home"
        self.home.mkdir()
        self.environment = {"HOME": str(self.home), "PATH": "/usr/bin"}

    def write(self, path: Path, text: str) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def problems(self, text: str, name: str = "config.toml") -> list[str]:
        path = self.write(self.home / ".cargo" / name, text)
        record = AUDIT.audit(self.checkout, self.environment)
        return [problem.removeprefix(f"{path}: ") for problem in record["problems"]]

    def test_every_file_cargo_reads_is_found_in_search_order(self):
        paths = [
            self.write(self.checkout / ".cargo" / "config.toml", "[net]\nretry = 2\n"),
            self.write(self.root / "work" / ".cargo" / "config", "[term]\nverbose = false\n"),
            self.write(self.root / ".cargo" / "config.toml", "[http]\ntimeout = 30\n"),
            self.write(self.home / ".cargo" / "config.toml", "[net]\noffline = true\n"),
        ]
        found = AUDIT.config_files(self.checkout, self.environment)
        self.assertEqual([entry["path"] for entry in found], paths)
        self.assertEqual([entry["origin"] for entry in found], ["ancestor"] * 3 + ["home"])
        record = AUDIT.audit(self.checkout, self.environment)
        self.assertEqual([entry["path"] for entry in record["files"]], [str(path) for path in paths])
        self.assertTrue(all(len(entry["sha256"]) == 64 for entry in record["files"]))
        self.assertEqual(record["problems"], [])

    def test_cargo_home_comes_from_the_environment_before_home(self):
        injected = self.root / "injected-home"
        self.write(injected / "config", "[env]\nPROPTEST_CASES = \"0\"\n")
        record = AUDIT.audit(self.checkout, {**self.environment, "CARGO_HOME": str(injected)})
        self.assertEqual(record["problems"], [f"{injected / 'config'}: [env]"])
        self.assertEqual(AUDIT.audit(self.checkout, self.environment)["problems"], [])

    def test_cargo_home_resolves_as_cargo_does_not_against_pythons_cwd(self):
        # A relative CARGO_HOME is relative to the directory Cargo starts in.
        injected = self.write(self.checkout / "relative-home" / "config.toml", "[alias]\nt = \"check\"\n")
        environment = {**self.environment, "CARGO_HOME": "relative-home"}
        record = AUDIT.audit(self.checkout, environment)
        self.assertEqual(record["cargo_home"], str(self.checkout / "relative-home"))
        self.assertEqual(record["problems"], [f"{injected}: [alias]"])
        # An empty HOME is the password-database home, as for Rust's home_dir.
        account = Path(pwd.getpwuid(os.getuid()).pw_dir)
        for environment in ({"HOME": "", "PATH": "/usr/bin"}, {"PATH": "/usr/bin"}):
            self.assertEqual(AUDIT.cargo_home(environment, self.checkout), account / ".cargo")
        # A relative HOME is relative to the directory Cargo starts in too.
        self.assertEqual(AUDIT.cargo_home({"HOME": "h"}, self.checkout), self.checkout / "h" / ".cargo")

    def test_keys_that_change_the_build_or_the_tests_are_problems(self):
        for text, expected in (
            ('[env]\nPROPTEST_CASES = { value = "0", force = true }\n', ["[env]"]),
            ('[build]\nrustflags = ["-Coverflow-checks=off", "-Cdebug-assertions=off"]\n', ["[build] rustflags"]),
            ('[build]\nrustc-wrapper = "sccache"\n', ["[build] rustc-wrapper"]),
            ('[build]\ntarget = "x86_64-unknown-linux-gnu"\n', ["[build] target"]),
            ('[profile.dev]\noverflow-checks = false\n', ["[profile]"]),
            ('[alias]\ntest = "check"\n', ["[alias]"]),
            ('[target.aarch64-unknown-linux-gnu]\nrunner = "valgrind"\n', ["[target]"]),
            ('[unstable]\nbuild-std = ["std"]\n', ["[unstable]"]),
            ('[patch.crates-io]\nlibc = { path = "/x" }\n', ["[patch]"]),
            ('[source.crates-io]\nreplace-with = "vendored"\n', ["[source]"]),
            ('include = "other.toml"\n', ["include"]),
            ('[some-future-table]\nkey = 1\n', ["[some-future-table]"]),
            # `quiet` makes libtest print dots, hiding the probe lines.
            ('[term]\nquiet = true\n', ["[term] quiet"]),
            ('[term]\nsome-future-key = 1\n', ["[term] some-future-key"]),
            ("this is not toml = = \n", None),
        ):
            with self.subTest(text=text):
                found = self.problems(text)
                if expected is None:
                    self.assertEqual(len(found), 1)
                    self.assertTrue(found[0].startswith("cannot be parsed"), found)
                else:
                    self.assertEqual(found, expected)

    def test_documented_allowlist_passes(self):
        text = (
            "[build]\njobs = 4\ntarget-dir = \"/t\"\nincremental = false\n"
            "[net]\ngit-fetch-with-cli = true\noffline = true\n"
            "[http]\ntimeout = 30\n[term]\ncolor = \"never\"\nverbose = true\n"
            "[term.progress]\nwhen = \"never\"\n"
            "[registries.example]\nindex = \"sparse+https://example.invalid/\"\n"
            "[install]\nroot = \"/opt\"\n[cache]\nauto-clean-frequency = \"never\"\n"
        )
        self.assertEqual(self.problems(text), [])

    def test_a_config_path_that_is_not_a_regular_file_is_refused_unread(self):
        target = self.write(self.root / "elsewhere.toml", "[net]\nretry = 2\n")
        directory = self.checkout / ".cargo"
        directory.mkdir()
        cases = {
            "fifo": lambda path: os.mkfifo(path),
            "symlink to a file": lambda path: path.symlink_to(target),
            "symlink to stdin": lambda path: path.symlink_to("/dev/stdin"),
            "directory": lambda path: path.mkdir(),
        }
        for label, make in cases.items():
            for name in AUDIT.CONFIG_NAMES:
                with self.subTest(label=label, name=name):
                    path = directory / name
                    make(path)
                    try:
                        # A FIFO without a writer would block a reader; the
                        # audit never opens a path it did not lstat as regular.
                        record = AUDIT.audit(self.checkout, self.environment)
                    finally:
                        if path.is_dir() and not path.is_symlink():
                            path.rmdir()
                        else:
                            path.unlink()
                    self.assertEqual(len(record["problems"]), 1, record["problems"])
                    problem = record["problems"][0]
                    self.assertTrue(problem.startswith(f"{path}: "), problem)
                    self.assertTrue("symbolic link" in problem or "not a regular file" in problem, problem)
                    self.assertNotIn("sha256", record["files"][0])

    def test_reading_never_blocks_on_a_fifo_swapped_in(self):
        fifo = self.root / "swapped"
        os.mkfifo(fifo)
        with self.assertRaises(OSError):
            AUDIT.read_regular(fifo)
        link = self.root / "link"
        link.symlink_to(self.write(self.root / "real.toml", ""))
        with self.assertRaises(OSError):
            AUDIT.read_regular(link)

    def test_config_and_config_toml_together_are_refused_and_config_alone_is_audited(self):
        directory = self.checkout / ".cargo"
        self.write(directory / "config.toml", "[net]\nretry = 2\n")
        self.write(directory / "config", "[net]\nretry = 3\n")
        record = AUDIT.audit(self.checkout, self.environment)
        self.assertEqual(len(record["problems"]), 2)
        self.assertTrue(all("Cargo reads only `config`" in problem for problem in record["problems"]))
        (directory / "config.toml").unlink()
        self.write(directory / "config", "[env]\nPROPTEST_CASES = \"0\"\n")
        self.assertEqual(AUDIT.audit(self.checkout, self.environment)["problems"], [f"{directory / 'config'}: [env]"])

    def test_the_committed_repository_config_is_exempt_only_while_unmodified(self):
        path = self.checkout / ".cargo" / "config.toml"
        path.parent.mkdir(parents=True)
        path.write_bytes(COMMITTED)
        record = AUDIT.audit(self.checkout, self.environment, COMMITTED)
        self.assertEqual(record["problems"], [])
        self.assertEqual(record["files"][0]["exempt"], "the repository's committed config")
        path.write_bytes(COMMITTED + b"[env.PROPTEST_CASES]\nvalue = \"0\"\nforce = true\n")
        record = AUDIT.audit(self.checkout, self.environment, COMMITTED)
        self.assertTrue(record["files"][0]["modified_from_committed"])
        self.assertEqual(record["problems"], [f"{path}: [env]"])

    def test_a_worktree_nested_in_a_checkout_of_the_same_config_is_accepted(self):
        # The outer checkout's committed config is byte-identical to this one's.
        outer = self.root / "work"
        nested = outer / "nested" / "worktree"
        for checkout in (outer, nested):
            (checkout / ".cargo").mkdir(parents=True)
            (checkout / ".cargo" / "config.toml").write_bytes(COMMITTED)
        record = AUDIT.audit(nested, self.environment, COMMITTED)
        self.assertEqual(record["problems"], [])
        self.assertEqual(
            [entry.get("exempt") for entry in record["files"]],
            ["the repository's committed config", "byte-identical to the repository's committed config"],
        )
        # A different outer config is still audited, and a byte-identical copy
        # in Cargo's home (not the ancestor walk) is not exempt.
        (outer / ".cargo" / "config.toml").write_bytes(COMMITTED.replace(b"jobs = 2", b"jobs = 3"))
        self.assertEqual(AUDIT.audit(nested, self.environment, COMMITTED)["problems"],
                         [f"{outer / '.cargo' / 'config.toml'}: [env]"])
        (outer / ".cargo" / "config.toml").unlink()
        self.write(self.home / ".cargo" / "config.toml", COMMITTED.decode())
        self.assertEqual(AUDIT.audit(nested, self.environment, COMMITTED)["problems"],
                         [f"{self.home / '.cargo' / 'config.toml'}: [env]"])

    def test_cargo_config_variables_follow_the_allowlist(self):
        environment = {
            **self.environment,
            "CARGO_HOME": str(self.home / ".cargo"), "CARGO_TARGET_DIR": "/t", "CARGO_BUILD_JOBS": "4",
            "CARGO_NET_OFFLINE": "true", "CARGO_HTTP_TIMEOUT": "30", "CARGO_TERM_COLOR": "never",
            "CARGO_TERM_VERBOSE": "true", "CARGO_TERM_PROGRESS_WHEN": "never",
            "CARGO_INCREMENTAL": "0", "CARGO_REGISTRIES_CRATES_IO_PROTOCOL": "sparse",
            "CARGO_BUILD_RUSTFLAGS": "-Coverflow-checks=off", "CARGO_ENCODED_RUSTFLAGS": "-Cpanic=abort",
            "CARGO_PROFILE_DEV_OVERFLOW_CHECKS": "false", "CARGO_ALIAS_TEST": "check",
            "CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER": "valgrind", "CARGO_UNSTABLE_BUILD_STD": "std",
            "CARGO_BUILD_RUSTC_WRAPPER": "sccache", "CARGO_SOMETHING_NEW": "1", "CARGO_TERM_QUIET": "true",
        }
        self.assertEqual(AUDIT.environment_problems(environment), [
            "CARGO_ALIAS_TEST", "CARGO_BUILD_RUSTC_WRAPPER", "CARGO_BUILD_RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS",
            "CARGO_PROFILE_DEV_OVERFLOW_CHECKS", "CARGO_SOMETHING_NEW",
            "CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER", "CARGO_TERM_QUIET", "CARGO_UNSTABLE_BUILD_STD",
        ])
        record = AUDIT.audit(self.checkout, environment)
        self.assertEqual(len(record["problems"]), 9)
        self.assertEqual(record["environment"]["CARGO_TARGET_DIR"], "/t")
        self.assertEqual(record["environment_prefixes"], ["CARGO_"])

    def test_variables_cargo_sets_for_its_children_are_recorded_not_refused(self):
        environment = {
            **self.environment, "CARGO_MANIFEST_DIR": "/x", "CARGO_PKG_NAME": "x", "CARGO_MAKEFLAGS": "-j",
            "CARGO_CFG_TARGET_OS": "linux", "CARGO_FEATURE_STD": "1", "CARGO_BIN_EXE_x": "/x",
            "CARGO_TARGET_TMPDIR": "/tmp", "CARGO_PRIMARY_PACKAGE": "1",
        }
        record = AUDIT.audit(self.checkout, environment)
        self.assertEqual(record["problems"], [])
        self.assertEqual(record["child_variables"], sorted(set(environment) - set(self.environment)))
        self.assertTrue(all(AUDIT.child_variable(name) for name in record["child_variables"]))
        self.assertFalse(AUDIT.child_variable("CARGO_TARGET_DIR"))
        self.assertFalse(AUDIT.child_variable("CARGO_ENCODED_RUSTFLAGS"))

    def test_targo_config_variables_are_audited_like_cargo_ones(self):
        self.assertEqual(AUDIT.environment_prefixes("cargo"), ("CARGO_",))
        self.assertEqual(AUDIT.environment_prefixes("/opt/trust/bin/targo"), ("CARGO_", "TARGO_"))
        environment = {
            **self.environment,
            "TARGO_BUILD_RUSTFLAGS": "--cfg x", "TARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUSTFLAGS": "--cfg x",
            "TARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER": "/x", "TARGO_PROFILE_DEV_OVERFLOW_CHECKS": "false",
            "TARGO_ENCODED_RUSTFLAGS": "--cfg\x1fx", "TARGO_ALIAS_TEST": "check", "TARGO_VERIFY": "0",
            "TARGO_TARGET_DIR": "/t", "TARGO_NET_OFFLINE": "true", "TARGO_TERM_QUIET": "true",
            "TARGO_HOME": "/h", "TARGO_PKG_NAME": "x", "TRUST_BUILD_RUSTFLAGS": "--cfg x",
        }
        refused = [
            "TARGO_ALIAS_TEST", "TARGO_BUILD_RUSTFLAGS", "TARGO_ENCODED_RUSTFLAGS",
            "TARGO_PROFILE_DEV_OVERFLOW_CHECKS", "TARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER",
            "TARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUSTFLAGS", "TARGO_TERM_QUIET", "TARGO_VERIFY",
        ]
        self.assertEqual(AUDIT.environment_problems(environment, AUDIT.environment_prefixes("targo")), refused)
        record = AUDIT.audit(self.checkout, environment, tool="targo")
        self.assertEqual(record["environment_prefixes"], ["CARGO_", "TARGO_"])
        self.assertEqual(len(record["problems"]), len(refused))
        self.assertEqual(record["child_variables"], ["TARGO_PKG_NAME"])
        # Stock Cargo reads none of them.
        self.assertEqual(AUDIT.audit(self.checkout, environment)["problems"], [])

    def test_a_trust_cargo_beside_its_targo_reads_targo_variables_too(self):
        package = self.root / "trust" / "bin"
        package.mkdir(parents=True)
        (package / "targo").write_bytes(b"")
        os.link(package / "targo", package / "cargo")
        self.assertEqual(AUDIT.environment_prefixes(package / "cargo"), ("CARGO_", "TARGO_"))
        stock = self.root / "stock" / "bin"
        stock.mkdir(parents=True)
        (stock / "cargo").write_bytes(b"")
        (stock / "targo").write_bytes(b"")
        self.assertEqual(AUDIT.environment_prefixes(stock / "cargo"), ("CARGO_",))

    def test_changes_name_every_differing_path_and_the_environment(self):
        path = self.write(self.home / ".cargo" / "config.toml", "[net]\nretry = 2\n")
        before = AUDIT.audit(self.checkout, self.environment)
        self.assertEqual(AUDIT.changes(before, AUDIT.audit(self.checkout, self.environment)), [])
        path.write_text("[net]\nretry = 3\n")
        self.assertEqual(len(AUDIT.changes(before, AUDIT.audit(self.checkout, self.environment))), 1)
        path.unlink()
        os.mkfifo(path)
        self.assertEqual(len(AUDIT.changes(before, AUDIT.audit(self.checkout, self.environment))), 1)
        moved = AUDIT.audit(self.checkout, {**self.environment, "CARGO_TERM_COLOR": "never"})
        self.assertIn("environment changed", AUDIT.changes(before, moved))

    def test_this_checkouts_committed_config_is_exempt(self):
        committed = AUDIT.committed_config(ROOT)
        self.assertEqual(committed, (ROOT / ".cargo" / "config.toml").read_bytes())
        self.assertIsNone(AUDIT.committed_config(ROOT, git="/nonexistent/git"))


@unittest.skipUnless(INSTALLED_TARGO, "no BRIDGE_PROBE_TARGO and no targo on PATH")
class InstalledTargoTests(unittest.TestCase):
    """Pins the audit's model of the installed Targo: it maps TARGO_<KEY> and
    CARGO_<KEY> onto config keys, and reads no `.targo/` directory and no
    TARGO_HOME. An `[alias]` shows whether a source was read without
    compiling anything."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.targo = INSTALLED_TARGO
        self.environment = {
            key: value for key, value in os.environ.items()
            if not key.startswith(("CARGO_", "TARGO_", "RUSTUP_")) or key in ("CARGO_HOME", "RUSTUP_HOME")
        }

    def alias_runs(self, cwd: Path, **extra: str) -> bool:
        result = subprocess.run(
            [self.targo, "zz-audit-probe"], cwd=cwd, env={**self.environment, **extra},
            capture_output=True, text=True, timeout=60, check=False,
        )
        if "no such command" in result.stderr:
            return False
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout.startswith("targo "), result.stdout)
        return True

    def alias_file(self, path: Path) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('[alias]\nzz-audit-probe = "version"\n')
        return path.parent

    def test_the_prefixes_and_locations_targo_reads(self):
        self.assertFalse(self.alias_runs(self.root))
        self.assertTrue(self.alias_runs(self.root, TARGO_ALIAS_ZZ_AUDIT_PROBE="version"))
        self.assertTrue(self.alias_runs(self.root, CARGO_ALIAS_ZZ_AUDIT_PROBE="version"))
        self.assertEqual(AUDIT.environment_prefixes(self.targo), ("CARGO_", "TARGO_"))
        cargo_directory = self.root / "cargo-dir"
        self.alias_file(cargo_directory / ".cargo" / "config.toml")
        self.assertTrue(self.alias_runs(cargo_directory))
        targo_directory = self.root / "targo-dir"
        self.alias_file(targo_directory / ".targo" / "config.toml")
        self.assertFalse(self.alias_runs(targo_directory))
        home = self.alias_file(self.root / "home" / "config.toml")
        self.assertFalse(self.alias_runs(self.root, TARGO_HOME=str(home)))
        self.assertTrue(self.alias_runs(self.root, CARGO_HOME=str(home)))


if __name__ == "__main__":
    unittest.main()
