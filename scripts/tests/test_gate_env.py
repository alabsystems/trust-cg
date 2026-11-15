#!/usr/bin/env python3
"""Regression tests for scripts/gate_env.sh against fake tool directories.

Every compiler, package manager, solver, checker and Lean install here is a
small shell script in a temporary HOME. No real toolchain is executed, nothing
is built, and no network access is attempted. Run with
`python3 -m unittest scripts/tests/test_gate_env.py` or
`python3 scripts/tests/test_gate_env.py`.
"""

from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parent))
import atpkg_prelude_fixture as SHIMS  # noqa: E402
import soundness_fixture  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
GATE_ENV = ROOT / "scripts" / "gate_env.sh"
BASH = shutil.which("bash") or "/bin/bash"
ZSH = shutil.which("zsh")
DIGESTS = ROOT / "reports" / "2026-09-10-soundness-prerequisites" / "publisher-digests.json"
PIN_VERSION = "0.26.0"
PIN_REV = "a" * 40
COMMIT = "0123456789abcdef0123456789abcdef01234567"


def rust_pin() -> str:
    return re.search(r'^channel\s*=\s*"([^"]+)"', (ROOT / "rust-toolchain.toml").read_text(), re.M).group(1)


def lean_pin() -> str:
    return (ROOT / "formal" / "lean" / "lean-toolchain").read_text().strip()


def lean_dir_name(pin: str) -> str:
    return pin.replace("/", "--").replace(":", "---")


def write_script(path: Path, body: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("#!/bin/sh\n" + body)
    path.chmod(0o755)
    return path


def fake_compiler(path: Path, *, release: str, host: str = "aarch64-apple-darwin",
                  binary: str = "rustc", commit: str = COMMIT, sysroot: Path | None = None,
                  trust: bool = False) -> Path:
    lines = [f"rustc {release} (fake)", f"binary: {binary}", f"commit-hash: {commit}",
             "commit-date: 2026-09-17", f"host: {host}", f"release: {release}", "LLVM version: 22.1.2"]
    printed = " ".join(f"'{line}'" for line in lines)
    # Measured Trust behaviour: any exported TRUST_CG_* / TCG_* variable makes
    # every invocation but -vV exit 1 as an untracked codegen control.
    refusal = """if [ "$1" != -vV ]; then
  case "$(export -p)" in
    *" TRUST_CG_"*|*" TCG_"*) echo 'error: environment variable is an untracked Trust semantic/codegen control' >&2
      exit 1 ;;
  esac
fi
""" if trust else ""
    return write_script(path, refusal + f"""case "$1" in
  -vV) printf '%s\\n' {printed} ;;
  -V|--version) printf '%s\\n' 'rustc {release} (fake)' ;;
  --print) printf '%s\\n' '{sysroot or path.parent.parent}' ;;
  *) exit 64 ;;
esac
""")


def write_targo(path: Path, *, upstream: bool = False) -> Path:
    # targo accepts `--unverified --version`; upstream cargo under its name does not.
    if upstream:
        return write_script(path, """case "$1" in
  --unverified) echo "error: unexpected argument '--unverified' found" >&2; exit 1 ;;
esac
printf '%s\\n' 'cargo 1.99.0-dev (fake)'
""")
    return write_script(path, """case "$*" in
  "--unverified --version") printf '%s\\n' 'targo 1.99.0-dev (0123456 2026-09-17) (targo 0.1.0)' ;;
  *) exit 0 ;;
esac
""")


def fake_ay(path: Path, version: str, commit: str = COMMIT) -> Path:
    return write_script(path, f"""printf '%s\\n' 'ay {version}+build.1.{commit}@2026-09-18T00:00:00Z' \\
  'build.version={version}' 'build.increment=1' 'build.commit={commit}'
""")


def managed_prefix(home: Path) -> Path:
    if sys.platform == "darwin":
        return home / "Library" / "Application Support" / "aterm" / "pkg"
    return home / ".local" / "share" / "aterm" / "pkg"


def store_tool(prefix: Path, package: str, build: str, tool: str, body_writer) -> Path:
    binary = prefix / "store" / package / build / "bin" / tool
    body_writer(binary)
    current = prefix / "store" / package / "current"
    if not current.exists():
        current.symlink_to(prefix / "store" / package / build)
    return binary


class Fixture:
    """A healthy host: the Trust pin, one coherent Trust package on PATH, managed ay/clean, Lean."""

    def __init__(self, directory: Path):
        self.directory = directory
        self.repo = directory / "repo"
        self.home = directory / "home"
        self.sysbin = directory / "sysbin"
        self.cargo_bin = self.home / ".cargo" / "bin"
        self.seal = directory / "trust-seal"
        self.marker = directory / "network-install-attempted"
        (self.repo / "scripts").mkdir(parents=True)
        shutil.copy2(GATE_ENV, self.repo / "scripts" / "gate_env.sh")
        shutil.copy2(ROOT / "scripts" / "trust_toolchain.py", self.repo / "scripts" / "trust_toolchain.py")
        shutil.copy2(ROOT / "rust-toolchain.toml", self.repo / "rust-toolchain.toml")
        (self.repo / "formal" / "lean").mkdir(parents=True)
        (self.repo / "formal" / "lean" / "lean-toolchain").write_text(lean_pin() + "\n")
        report = self.repo / "reports" / "2026-09-10-soundness-prerequisites"
        report.mkdir(parents=True)
        shutil.copy2(DIGESTS, report / "publisher-digests.json")
        self.write_ay_pin(f'ay-pb = {{ version = "{PIN_VERSION}", git = "https://example.invalid/ay.git", '
                          f'rev = "{PIN_REV}", default-features = false, optional = true }}\n')

        self.sysbin.mkdir()
        for name in ("dirname", "uname", "awk"):
            found = shutil.which(name)
            if found:
                (self.sysbin / name).symlink_to(found)
        (self.sysbin / "python3").symlink_to(sys.executable)

        self.write_rustup(self.seal / "bin" / "rustc")

        fake_compiler(self.seal / "bin" / "rustc", release="1.99.0-dev", sysroot=self.seal, trust=True)
        fake_compiler(self.seal / "bin" / "trustc", release="1.99.0-dev", binary="trustc", sysroot=self.seal,
                      trust=True)
        write_targo(self.seal / "bin" / "targo")
        fake_ay(self.seal / "bin" / "ay", PIN_VERSION)

        self.prefix = managed_prefix(self.home)
        store_tool(self.prefix, "ay", "100", "ay", lambda p: fake_ay(p, PIN_VERSION))
        store_tool(self.prefix, "clean", "200", "clean",
                   lambda p: write_script(p, "printf '%s\\n' 'clean 0.9.0'\n"))

        pin = lean_pin()
        version = pin.rsplit(":v", 1)[1]
        self.lean_version = version
        write_script(self.home / ".elan" / "toolchains" / lean_dir_name(pin) / "bin" / "lean",
                     f"printf '%s\\n' 'Lean (version {version}, fake, Release)'\n")
        write_script(self.home / ".elan" / "bin" / "lake", f": > '{self.marker}'\nexit 70\n")

        # rustup (for the `trust` link lane) is found through the caller's PATH:
        # the prelude no longer puts ~/.cargo/bin first.
        self.path = [str(self.sysbin), str(self.seal / "bin"), str(self.cargo_bin)]
        self.env_extra: dict[str, str] = {}

    def write_ay_pin(self, line: str) -> None:
        manifest = self.repo / "crates" / "trust-cg-regalloc" / "Cargo.toml"
        manifest.parent.mkdir(parents=True, exist_ok=True)
        manifest.write_text("[dependencies]\n" + line)

    def write_rustup(self, trust_rustc: Path | None) -> None:
        answer = (f"printf '%s\\n' '{trust_rustc}'; exit 0" if trust_rustc
                  else "echo \"error: toolchain 'trust' is not installed\" >&2; exit 1")
        write_script(self.cargo_bin / "rustup", f"""case "$1 $2" in
  "which --toolchain") {answer} ;;
  "show active-toolchain") printf '%s\\n' 'fixture-toolchain (overridden by fixture)' ;;
  *) exit 64 ;;
esac
""")

    def write_aterm(self, answers: dict[str, Path]) -> None:
        arms = "".join(
            f"  {tool}) printf '%s\\n' '{tool} → {self.prefix}/bin/{tool} → {path} — managed 1 — pinned by index 1' ;;\n"
            for tool, path in answers.items())
        write_script(self.directory / "atermbin" / "aterm", f"""[ "$1 $2" = "pkg which" ] || exit 64
case "$3" in
{arms}  *) printf '%s\\n' "atpkg: $3 is not installed"; exit 1 ;;
esac
""")
        self.path.insert(0, str(self.directory / "atermbin"))

    def environment(self) -> dict[str, str]:
        env = {"HOME": str(self.home), "PATH": ":".join(self.path), "LC_ALL": "C.UTF-8",
               "PYTHONIOENCODING": "utf-8"}
        env.update(self.env_extra)
        return env

    def check(self, *arguments: str, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [BASH, str(self.repo / "scripts" / "gate_env.sh"), *arguments], env=self.environment(),
            capture_output=True, text=True, encoding="utf-8", timeout=120, check=False,
            cwd=None if cwd is None else str(cwd),
        )


def findings(result: subprocess.CompletedProcess[str], kind: str) -> set[str]:
    return set(re.findall(rf"^gate_env: {kind} (GATE_ENV_[A-Z0-9_]+):", result.stdout, re.M))


class GateEnvCheckTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="trust-cg-gate-env-")
        self.addCleanup(temporary.cleanup)
        self.fixture = Fixture(Path(temporary.name))

    def assertPasses(self, result: subprocess.CompletedProcess[str]) -> None:
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(findings(result, "FAIL"), set(), result.stdout)
        self.assertIn("gate_env: RESULT PASS", result.stdout)

    def assertFailsWith(self, result: subprocess.CompletedProcess[str], *codes: str) -> None:
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertTrue(set(codes) <= findings(result, "FAIL"), result.stdout)
        self.assertIn("gate_env: RESULT FAIL", result.stdout)

    # ---- positive control ------------------------------------------------
    def test_healthy_host_passes_and_records_identities(self) -> None:
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertEqual(findings(result, "WARN"), set(), result.stdout)
        home = self.fixture.home
        self.assertIn(f"PATH head: {home}/.elan/bin | {self.fixture.sysbin} | {self.fixture.seal}/bin", result.stdout)
        self.assertIn("PASS rust-toolchain.toml channel trust", result.stdout)
        self.assertIn("PASS PATH targo is targo: targo 1.99.0-dev", result.stdout)
        self.assertIn("PASS trustc host aarch64-apple-darwin", result.stdout)
        self.assertRegex(result.stdout, r"managed ay: .*/store/ay/100/bin/ay \(via store layout under .*\): "
                                        r"not consulted by trust-cg; not executed")
        self.assertRegex(result.stdout, r"managed clean: .*/store/clean/200/bin/clean .*: clean 0\.9\.0")
        self.assertIn(f"one toolchain: {os.path.realpath(self.fixture.seal)}", result.stdout)
        self.assertIn(f"PASS effective Trust toolchain ay {PIN_VERSION} matches the ay-pb pin", result.stdout)
        self.assertIn(f"Lean (version {self.fixture.lean_version}, fake, Release)", result.stdout)
        # The elan proxy is never executed: it could start a network install.
        self.assertFalse(self.fixture.marker.exists())

    def test_the_check_imports_nothing_from_its_working_directory(self) -> None:
        # OD-XHOST-GATE-CWD-20261025 (the X-HOST-P13 sixth closure audit's
        # probe_gate_env_cwd.sh): the check's `python3 -` put its working
        # directory first on sys.path, so a json.py, hashlib.py or
        # datetime.py another user could write there ran as this user, and
        # soundness_check.sh started it in its caller's directory. It now runs
        # with -I: started in a 0777 directory holding the three 0666 marker
        # modules it passes exactly as the healthy host does and imports none.
        caller = self.fixture.directory / "caller-cwd"
        caller.mkdir()
        os.chmod(caller, 0o777)
        marker = self.fixture.directory / "planted-modules.log"
        soundness_fixture.plant_marker_modules(caller, marker)
        probe = subprocess.run([sys.executable, "-c", "import json, hashlib, datetime"], cwd=caller,
                               capture_output=True, text=True, timeout=60, check=False)
        self.assertEqual(probe.returncode, 0, probe.stderr)
        self.assertEqual(len(marker.read_text().splitlines()), 3, "the markers' positive control imports all three")
        marker.unlink()
        result = self.fixture.check(cwd=caller)
        self.assertPasses(result)
        self.assertEqual(findings(result, "WARN"), set(), result.stdout)
        self.assertFalse(marker.exists(), marker.read_text() if marker.exists() else "")

        def report(text: str) -> str:
            return re.sub(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ", "<now>", text)

        self.assertEqual(report(result.stdout), report(self.fixture.check(cwd=self.fixture.repo).stdout),
                         "the same report as from the checkout")

    def test_the_check_runs_the_python3_resolved_before_the_prelude(self) -> None:
        # Repair round 3 of OD-XHOST-GATE-CWD-20261025: the check found its
        # python3 by name after its own prelude had put $HOME/.elan/bin first
        # on PATH, so a python3 there ran the check (and, started by the
        # soundness gate, was not the interpreter the gate's host trust
        # boundary had judged as its own). It is now resolved once, before
        # the prelude: the gate's pinned SOUNDNESS_PYTHON3 when set, else the
        # one PATH finds. A logging python3 in ~/.elan/bin never runs; the
        # positive control shows a lookup after the prelude finds it.
        planted_log = self.fixture.directory / "elan-python3.log"
        planted = write_script(self.fixture.home / ".elan" / "bin" / "python3",
                               f'echo "elan python3 ran: $*" >> \'{planted_log}\'\nexec \'{sys.executable}\' "$@"\n')
        after_prelude = ":".join([str(self.fixture.home / ".elan" / "bin"), *self.fixture.path])
        self.assertEqual(shutil.which("python3", path=after_prelude), str(planted), "the positive control")
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertFalse(planted_log.exists(), planted_log.read_text() if planted_log.exists() else "")
        # The gate's pin, when set, is the interpreter the check runs.
        pinned_log = self.fixture.directory / "pinned-python3.log"
        pinned_dir = self.fixture.directory / "pinned-bin"
        pinned = write_script(pinned_dir / "python3",
                              f'echo "pinned python3 ran: $*" >> \'{pinned_log}\'\nexec \'{sys.executable}\' "$@"\n')
        self.fixture.env_extra["SOUNDNESS_PYTHON3"] = str(pinned)
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertEqual(len(pinned_log.read_text().splitlines()), 1, pinned_log.read_text())
        self.assertFalse(planted_log.exists(), planted_log.read_text() if planted_log.exists() else "")
        # One that is not an absolute path to an executable file fails closed.
        for value in ("python3", str(pinned_dir / "missing")):
            with self.subTest(pin=value):
                self.fixture.env_extra["SOUNDNESS_PYTHON3"] = value
                result = self.fixture.check()
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("gate_env: FAIL GATE_ENV_PYTHON_MISSING", result.stderr)
                self.assertFalse(planted_log.exists())

    def test_bare_rustc_and_cargo_on_path_are_not_consulted(self) -> None:
        # The gates run the Trust package's targo; a stock rustc/cargo (or an
        # atpkg reroute stub) earlier on PATH changes nothing.
        decoy = self.fixture.directory / "decoy"
        ran = self.fixture.directory / "decoy-ran"
        write_script(decoy / "rustc", f": > '{ran}'\nexit 127\n")
        write_script(decoy / "cargo", f": > '{ran}'\nexit 127\n")
        self.fixture.path.insert(0, str(decoy))
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertFalse(ran.exists())

    # ---- Trust toolchain contract ---------------------------------------
    def test_non_aarch64_host_fails(self) -> None:
        fake_compiler(self.fixture.seal / "bin" / "trustc", release="1.99.0-dev", binary="trustc",
                      host="x86_64-apple-darwin", sysroot=self.fixture.seal, trust=True)
        fake_compiler(self.fixture.seal / "bin" / "rustc", release="1.99.0-dev",
                      host="x86_64-apple-darwin", sysroot=self.fixture.seal, trust=True)
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_HOST_NOT_AARCH64")

    def test_linux_aarch64_host_is_accepted(self) -> None:
        for name, binary in (("trustc", "trustc"), ("rustc", "rustc")):
            fake_compiler(self.fixture.seal / "bin" / name, release="1.99.0-dev", binary=binary,
                          host="aarch64-unknown-linux-gnu", sysroot=self.fixture.seal, trust=True)
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertIn("PASS trustc host aarch64-unknown-linux-gnu", result.stdout)

    def test_x86_64_host_is_accepted_only_when_the_gate_allows_it(self) -> None:
        # The soundness gate passes --allow-x86_64-host on a native x86-64 leg
        # host; without it the aarch64 contract stands.
        for host in ("x86_64-unknown-linux-gnu", "x86_64-apple-darwin"):
            with self.subTest(host=host):
                for name, binary in (("trustc", "trustc"), ("rustc", "rustc")):
                    fake_compiler(self.fixture.seal / "bin" / name, release="1.99.0-dev", binary=binary,
                                  host=host, sysroot=self.fixture.seal, trust=True)
                self.assertFailsWith(self.fixture.check(), "GATE_ENV_HOST_NOT_AARCH64")
                result = self.fixture.check("--allow-x86_64-host")
                self.assertPasses(result)
                self.assertIn(f"PASS trustc host {host}", result.stdout)

    def test_upstream_cargo_under_the_targo_name_fails(self) -> None:
        write_targo(self.fixture.seal / "bin" / "targo", upstream=True)
        result = self.fixture.check()
        self.assertFailsWith(result, "GATE_ENV_TARGO_NOT_TARGO")
        self.assertIn("unexpected argument '--unverified'", result.stdout)

    def test_missing_targo_fails(self) -> None:
        (self.fixture.seal / "bin" / "targo").unlink()
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_TARGO_MISSING")

    def test_unbranded_or_unstamped_trustc_fails(self) -> None:
        self.fixture.write_rustup(None)
        fake_compiler(self.fixture.seal / "bin" / "trustc", release="1.99.0-dev", binary="trustc",
                      commit="unknown", sysroot=self.fixture.seal, trust=True)
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_TRUST_UNSTAMPED")
        fake_compiler(self.fixture.seal / "bin" / "trustc", release="1.99.0-dev", binary="rustc",
                      sysroot=self.fixture.seal, trust=True)
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_TRUST_UNSTAMPED")

    def test_rust_toolchain_pin_drift_fails(self) -> None:
        (self.fixture.repo / "rust-toolchain.toml").write_text('[toolchain]\nchannel = "1.97.1"\n')
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_RUST_PIN_DRIFT")
        (self.fixture.repo / "rust-toolchain.toml").write_text("[toolchain]\n")
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_RUST_PIN_UNREADABLE")

    def test_atpkg_launcher_shims_are_followed_to_their_package(self) -> None:
        shims = self.fixture.directory / "atpkg-bin"
        for tool in ("trustc", "targo"):
            write_script(shims / tool, f"# atpkg shim\nexec '{self.fixture.seal / 'bin' / tool}' \"$@\"\n")
        self.fixture.path.remove(str(self.fixture.seal / "bin"))
        self.fixture.path.insert(1, str(shims))
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertIn(f"one toolchain: {os.path.realpath(self.fixture.seal)}", result.stdout)

    def test_targo_discriminator_runs_the_package_file_never_the_launcher_shim(self) -> None:
        # The gates run the package targo. A shim whose prelude the resolver
        # reads but never runs (DR-ATPKG-PRELUDE-SHIM-20261015) must not answer
        # for it: here the package file is upstream cargo under the name targo,
        # and the prelude claims otherwise.
        write_targo(self.fixture.seal / "bin" / "targo", upstream=True)
        shims = self.fixture.directory / "atpkg-bin"
        log = self.fixture.directory / "shim-calls.log"
        SHIMS.lying_shim(shims / "trustc", self.fixture.seal / "bin" / "trustc", log)
        SHIMS.lying_shim(shims / "targo", self.fixture.seal / "bin" / "targo", log,
                         {"--unverified --version": "targo 1.99.0-dev (forged by a prelude)"})
        self.fixture.path.remove(str(self.fixture.seal / "bin"))
        self.fixture.path.insert(1, str(shims))
        result = self.fixture.check()
        self.assertFailsWith(result, "GATE_ENV_TARGO_NOT_TARGO")
        self.assertIn("unexpected argument '--unverified'", result.stdout)
        self.assertNotIn("forged by a prelude", result.stdout)
        self.assertEqual(SHIMS.logged(log), [], "gate_env executed a PATH launcher shim")

    # ---- Trust toolchain divergence -------------------------------------
    def divergent(self) -> Path:
        recon = self.fixture.directory / "trust-recon"
        fake_compiler(recon / "bin" / "rustc", release="1.99.0-dev", commit="unknown", sysroot=recon, trust=True)
        fake_ay(recon / "bin" / "ay", "0.22.0")
        self.fixture.write_rustup(recon / "bin" / "rustc")
        return recon

    def test_divergent_trust_toolchains_are_refused_by_name(self) -> None:
        recon = self.divergent()
        result = self.fixture.check()
        self.assertFailsWith(result, "GATE_ENV_TRUST_TOOLCHAINS_DIVERGENT")
        self.assertIn(f"rustup `trust` -> {os.path.realpath(recon)} (commit-hash unknown)", result.stdout)
        self.assertIn(f"PATH/managed trustc -> {os.path.realpath(self.fixture.seal)} (commit-hash {COMMIT})",
                      result.stdout)
        self.assertIn("TRUST_CG_TOOLCHAIN_LANE=rustup|path", result.stdout)
        # The rustup bundle's ay is reported against the pin too.
        self.assertIn("GATE_ENV_BUNDLE_AY_PIN_MISMATCH", findings(result, "WARN"))

    def test_explicit_lane_selection_accepts_divergence_with_a_recorded_warning(self) -> None:
        self.divergent()
        self.fixture.env_extra["TRUST_CG_TOOLCHAIN_LANE"] = "path"
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertIn("GATE_ENV_TRUST_LANE_OVERRIDE", findings(result, "WARN"))
        self.assertNotIn("GATE_ENV_TRUST_UNSTAMPED", findings(result, "WARN"))
        # The selector is itself a variable Trust compilers refuse; the sysroots
        # are still measured (probed without it) and the hazard is named.
        self.assertIn("GATE_ENV_TRUST_ENV_CONTROLS", findings(result, "WARN"))
        self.assertIn(f"selects {os.path.realpath(self.fixture.seal)} despite", result.stdout)

        # Selecting the unstamped rustup lane is recorded, but the gates require
        # a branded 40-hex trustc, so it fails.
        self.fixture.env_extra["TRUST_CG_TOOLCHAIN_LANE"] = "rustup"
        result = self.fixture.check()
        self.assertFailsWith(result, "GATE_ENV_TRUST_UNSTAMPED")
        self.assertIn("GATE_ENV_TRUST_LANE_OVERRIDE", findings(result, "WARN"))
        self.assertIn("do not honour this selection", result.stdout)

    def test_trust_identities_are_probed_without_refused_environment_controls(self) -> None:
        self.fixture.env_extra.update(TCG_DECODE_CHECK="warn", TRUST_CG_RUN_FORMAL_PROOF_TESTS="1")
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertIn("GATE_ENV_TRUST_ENV_CONTROLS", findings(result, "WARN"))
        self.assertIn("TCG_DECODE_CHECK, TRUST_CG_RUN_FORMAL_PROOF_TESTS set here", result.stdout)
        self.assertIn(f"one toolchain: {os.path.realpath(self.fixture.seal)}", result.stdout)

    def test_unmeasurable_trust_identity_fails_closed_instead_of_guessing(self) -> None:
        # A launcher whose sysroot query fails must not be assigned the
        # launcher's grandparent directory as a guessed sysroot.
        launcher_dir = self.fixture.directory / "pkg" / "bin"
        write_script(launcher_dir / "trustc", """case "$1" in
  -vV) printf '%s\\n' 'rustc 1.99.0-dev (fake)' 'binary: trustc' 'commit-hash: unknown' ;;
  *) echo 'error: sysroot unavailable' >&2; exit 1 ;;
esac
""")
        write_targo(launcher_dir / "targo")
        self.fixture.path.remove(str(self.fixture.seal / "bin"))
        self.fixture.path.append(str(launcher_dir))
        result = self.fixture.check()
        self.assertFailsWith(result, "GATE_ENV_TRUST_IDENTITY_UNKNOWN")
        self.assertIn("--print sysroot failed: error: sysroot unavailable", result.stdout)
        self.assertNotIn(f"sysroot {os.path.realpath(launcher_dir.parent)};", result.stdout)

    def test_invalid_or_unavailable_lane_selection_fails(self) -> None:
        self.fixture.env_extra["TRUST_CG_TOOLCHAIN_LANE"] = "stock"
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_TRUST_LANE_INVALID")
        self.fixture.write_rustup(None)
        self.fixture.env_extra["TRUST_CG_TOOLCHAIN_LANE"] = "rustup"
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_TRUST_LANE_UNAVAILABLE")

    def test_managed_trust_package_stands_in_for_an_absent_path_trustc(self) -> None:
        recon = self.divergent()
        self.fixture.path.remove(str(self.fixture.seal / "bin"))
        store_tool(self.fixture.prefix, "trust", "300", "trustc",
                   lambda p: fake_compiler(p, release="1.99.0-dev", binary="trustc", trust=True,
                                           sysroot=self.fixture.prefix / "store" / "trust" / "300"))
        result = self.fixture.check()
        self.assertFailsWith(result, "GATE_ENV_TRUST_TOOLCHAINS_DIVERGENT", "GATE_ENV_TRUSTC_NOT_ON_PATH")
        self.assertIn("NOT on PATH", result.stdout)
        self.assertIn(os.path.realpath(recon), result.stdout)

    def test_path_trustc_and_targo_from_different_packages_fail(self) -> None:
        other = self.fixture.directory / "other"
        write_targo(other / "targo")
        (self.fixture.seal / "bin" / "targo").unlink()
        self.fixture.path.append(str(other))
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_TRUST_PATH_SPLIT")

    def test_no_trust_toolchain_fails_without_a_stock_fallback(self) -> None:
        self.fixture.write_rustup(None)
        self.fixture.path.remove(str(self.fixture.seal / "bin"))
        result = self.fixture.check()
        self.assertFailsWith(result, "GATE_ENV_TRUST_TOOLCHAIN_ABSENT")
        self.assertIn("no stock fallback", result.stdout)

    def test_a_rustup_copy_carrying_the_same_compiler_is_one_toolchain(self) -> None:
        # aterm's rustup `trust` link is a copied tree of the store package; the
        # same commit and byte-identical bin/trustc, bin/rustc, bin/ay, lib/ and
        # libexec/ make it one compiler even though its bin/cargo differs.
        copy = self.fixture.directory / "rustup-copy"
        shutil.copytree(self.fixture.seal, copy, symlinks=True)
        # One trustc and one rustc byte stream in both trees: each derives its
        # sysroot from $0, as the real (hard-linked) atpkg driver does.
        def body(binary: str) -> str:
            return f"""case "$1" in
  -vV) printf '%s\\n' 'rustc 1.99.0-dev (fake)' 'binary: {binary}' 'commit-hash: {COMMIT}' \\
         'commit-date: 2026-09-17' 'host: aarch64-apple-darwin' 'release: 1.99.0-dev' \\
         'LLVM version: 22.1.2' ;;
  -V|--version) printf '%s\\n' 'rustc 1.99.0-dev (fake)' ;;
  --print) cd "$(dirname "$0")/.." && pwd -P ;;
  *) exit 64 ;;
esac
"""
        for tree in (self.fixture.seal, copy):
            write_script(tree / "bin" / "trustc", body("trustc"))
            write_script(tree / "bin" / "rustc", body("rustc"))
            (tree / "lib").mkdir(exist_ok=True)
            (tree / "lib" / "librustc_driver-fixture.dylib").write_bytes(b"driver")
        write_script(copy / "bin" / "cargo", "exit 0\n")
        self.fixture.write_rustup(copy / "bin" / "rustc")
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertIn("carries the same compiler as the PATH/managed package", result.stdout)
        self.assertIn("their other bin/ tools differ", result.stdout)
        # Different compiler bytes under the same commit stay divergent: the
        # driver library, the rustc a rustup-proxied build runs, or the bin/ay
        # trust-cg-verify admits.
        for relative, content in (
            ("lib/librustc_driver-fixture.dylib", None),
            ("bin/rustc", body("rustc") + "# another build\n"),
            ("bin/ay", "exit 0\n"),
        ):
            with self.subTest(relative=relative):
                target = copy / relative
                original = target.read_bytes()
                if content is None:
                    target.write_bytes(b"another driver")
                else:
                    write_script(target, content)
                self.assertFailsWith(self.fixture.check(), "GATE_ENV_TRUST_TOOLCHAINS_DIVERGENT")
                target.write_bytes(original)

    # ---- managed tools and AY coherence ---------------------------------
    def test_aterm_pkg_which_is_preferred_and_only_store_paths_are_trusted(self) -> None:
        custom = self.fixture.directory / "custom-prefix"
        ay = store_tool(custom, "ay", "7", "ay", lambda p: fake_ay(p, PIN_VERSION))
        launcher = write_script(custom / "bin" / "clean", "exit 0\n")
        self.fixture.write_aterm({"ay": ay, "clean": launcher})
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertIn(f"managed ay: {os.path.realpath(ay)} (via aterm pkg which ay)", result.stdout)
        # A launcher outside store/<package>/<version>/bin is never an identity;
        # the store layout answers instead.
        self.assertIn("`aterm pkg which clean` named no store executable", result.stdout)
        self.assertRegex(result.stdout, r"managed clean: .*/store/clean/200/bin/clean \(via store layout")

    def test_atpkg_bin_names_the_managed_prefix(self) -> None:
        custom = self.fixture.directory / "custom-prefix"
        store_tool(custom, "ay", "7", "ay", lambda p: fake_ay(p, PIN_VERSION))
        (custom / "bin").mkdir()
        self.fixture.env_extra["ATPKG_BIN"] = str(custom / "bin")
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertIn(f"(via store layout under {custom})", result.stdout)

    def test_managed_ay_is_never_executed_or_the_effective_solver(self) -> None:
        # trust-cg never consults aterm's managed ay (ay_identity.rs), so a
        # stale one is no finding and is never run.
        ran = self.fixture.directory / "managed-ay-was-executed"
        shutil.rmtree(self.fixture.prefix / "store" / "ay")
        store_tool(self.fixture.prefix, "ay", "8256", "ay",
                   lambda p: write_script(p, f": > '{ran}'\nprintf '%s\\n' 'ay 0.13.0'\n"))
        result = self.fixture.check("--require-ay-pin")
        self.assertPasses(result)
        self.assertEqual(findings(result, "WARN"), set(), result.stdout)
        self.assertFalse(ran.exists())
        self.assertIn(f"PASS effective Trust toolchain ay {PIN_VERSION} matches the ay-pb pin", result.stdout)

        shutil.rmtree(self.fixture.prefix / "store" / "ay")
        result = self.fixture.check("--require-ay-pin")
        self.assertPasses(result)
        self.assertNotIn("GATE_ENV_MANAGED_TOOL_ABSENT", findings(result, "WARN"))

    def test_stale_toolchain_ay_warns_loudly_and_never_switches_solvers(self) -> None:
        fake_ay(self.fixture.seal / "bin" / "ay", "0.13.0")
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertIn("GATE_ENV_AY_PIN_MISMATCH", findings(result, "WARN"))
        self.assertIn("GATE_ENV_AY_PIN_MISMATCH", result.stderr)
        self.assertIn("!" * 72, result.stderr)
        self.assertIn("gate_env does NOT switch solvers", result.stdout)
        self.assertIn(f"pins ay-pb {PIN_VERSION} (rev {PIN_REV})", result.stdout)

        strict = self.fixture.check("--require-ay-pin")
        self.assertFailsWith(strict, "GATE_ENV_AY_PIN_MISMATCH")

    def test_ay_solver_path_is_admitted_only_as_a_byte_copy_of_the_toolchain_ay(self) -> None:
        toolchain_ay = self.fixture.seal / "bin" / "ay"
        copy = self.fixture.directory / "explicit" / "ay"
        copy.parent.mkdir(parents=True)
        shutil.copy2(toolchain_ay, copy)
        self.fixture.env_extra["AY_SOLVER_PATH"] = str(copy)
        result = self.fixture.check("--require-ay-pin")
        self.assertPasses(result)
        self.assertIn(f"PASS AY_SOLVER_PATH {copy} is a byte copy of {os.path.realpath(toolchain_ay)}",
                      result.stdout)

        # Same version banner, different bytes: refused, and never executed.
        ran = self.fixture.directory / "decoy-was-executed"
        decoy = write_script(self.fixture.directory / "decoy" / "ay",
                             f": > '{ran}'\nprintf '%s\\n' 'ay {PIN_VERSION}+build.1.{COMMIT}@2026-09-18T00:00:00Z' "
                             f"'build.version={PIN_VERSION}' 'build.increment=1' 'build.commit={COMMIT}'\n")
        self.fixture.env_extra["AY_SOLVER_PATH"] = str(decoy)
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_AY_OVERRIDE_REFUSED")
        self.assertFalse(ran.exists())

        # No PATH lookup: a relative name is refused even when it is executable here.
        self.fixture.env_extra["AY_SOLVER_PATH"] = "ay"
        result = subprocess.run(
            [BASH, str(self.fixture.repo / "scripts" / "gate_env.sh")], env=self.fixture.environment(),
            cwd=str(self.fixture.seal / "bin"), capture_output=True, text=True, encoding="utf-8",
            timeout=120, check=False,
        )
        self.assertFailsWith(result, "GATE_ENV_AY_OVERRIDE_REFUSED")

        self.fixture.env_extra["AY_SOLVER_PATH"] = str(self.fixture.directory / "missing-ay")
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_OVERRIDE_NOT_EXECUTABLE")

    def test_unknown_or_absent_effective_solver_fails_only_when_required(self) -> None:
        write_script(self.fixture.seal / "bin" / "ay", "exit 3\n")
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertIn("GATE_ENV_AY_VERSION_UNKNOWN", findings(result, "WARN"))
        self.assertFailsWith(self.fixture.check("--require-ay-pin"), "GATE_ENV_AY_VERSION_UNKNOWN")

        # A managed ay is no substitute for an absent toolchain ay.
        (self.fixture.seal / "bin" / "ay").unlink()
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertFailsWith(self.fixture.check("--require-ay-pin"), "GATE_ENV_AY_UNRESOLVED")

    def test_unreadable_ay_pin_fails_closed(self) -> None:
        self.fixture.write_ay_pin('ay-sat = { version = "0.26.0" }\n')
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_AY_PIN_UNREADABLE")
        line = f'ay-pb = {{ version = "{PIN_VERSION}", rev = "{PIN_REV}" }}\n'
        self.fixture.write_ay_pin(line + line)
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_AY_PIN_UNREADABLE")
        self.fixture.write_ay_pin(f'ay-pb = {{ version = "{PIN_VERSION}", branch = "main" }}\n')
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_AY_PIN_UNREADABLE")

    def test_the_committed_regalloc_manifest_is_parseable(self) -> None:
        manifest = self.fixture.repo / "crates" / "trust-cg-regalloc" / "Cargo.toml"
        shutil.copy2(ROOT / "crates" / "trust-cg-regalloc" / "Cargo.toml", manifest)
        match = re.search(r'^ay-pb = \{[^}\n]*version = "([^"]+)"[^}\n]*rev = "([0-9a-f]{40})"',
                          manifest.read_text(), re.M)
        self.assertIsNotNone(match)
        result = self.fixture.check()
        self.assertIn(f"INFO ay-pb pin: {match.group(1)} at rev {match.group(2)}", result.stdout)
        self.assertNotIn("GATE_ENV_AY_PIN_UNREADABLE", findings(result, "FAIL"))

    def test_invalid_checker_override_fails(self) -> None:
        self.fixture.env_extra["TCG_EXTERNAL_CLEAN_CHECKER"] = str(self.fixture.directory)
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_OVERRIDE_NOT_EXECUTABLE")

    # ---- Lean ------------------------------------------------------------
    def test_absent_lean_toolchain_fails_with_the_recorded_recipe(self) -> None:
        shutil.rmtree(self.fixture.home / ".elan" / "toolchains" / lean_dir_name(lean_pin()))
        write_script(self.fixture.home / ".elan" / "toolchains" / "leanprover--lean4---v4.30.0" / "bin" / "lean",
                     "exit 0\n")
        result = self.fixture.check()
        self.assertFailsWith(result, "GATE_ENV_LEAN_TOOLCHAIN_ABSENT")
        self.assertIn("installed: leanprover--lean4---v4.30.0", result.stdout)
        self.assertIn(f"elan toolchain install {lean_pin()}", result.stdout)
        self.assertIn("reports/2026-09-10-soundness-prerequisites/README.md", result.stdout)
        import json
        lean = json.loads(DIGESTS.read_text())["lean"]
        if sys.platform == "darwin" and lean["tag_name"] == "v" + self.fixture.lean_version:
            self.assertIn(lean["sha256"], result.stdout)
            self.assertIn(lean["url"], result.stdout)
            self.assertIn("shasum -a 256 -c -", result.stdout)
        else:
            self.assertIn("obtain and record a publisher digest", result.stdout)
        self.assertFalse(self.fixture.marker.exists())

    def test_recipe_refuses_a_digest_recorded_for_another_version(self) -> None:
        pin = "leanprover/lean4:v9.9.9"
        (self.fixture.repo / "formal" / "lean" / "lean-toolchain").write_text(pin + "\n")
        result = self.fixture.check()
        self.assertFailsWith(result, "GATE_ENV_LEAN_TOOLCHAIN_ABSENT")
        self.assertIn("obtain and record a publisher digest", result.stdout)
        self.assertNotIn("shasum -a 256 -c -", result.stdout)

    def test_unreadable_lean_pin_fails(self) -> None:
        (self.fixture.repo / "formal" / "lean" / "lean-toolchain").write_text("stable\n")
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_LEAN_PIN_UNREADABLE")

    def test_non_proxy_lake_must_report_the_pinned_lean(self) -> None:
        (self.fixture.home / ".elan" / "bin" / "lake").unlink()
        vendored = self.fixture.directory / "vendored-lean" / "bin"
        write_script(vendored / "lake", "printf '%s\\n' 'Lake version 5.0.0-src (Lean version 4.0.0)'\n")
        self.fixture.path.append(str(vendored))
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_LEAN_VERSION_MISMATCH")
        write_script(vendored / "lake",
                     f"printf '%s\\n' 'Lake version 5.0.0-src (Lean version {self.fixture.lean_version})'\n")
        result = self.fixture.check()
        self.assertPasses(result)
        self.assertIn(f"PASS lake {vendored}/lake", result.stdout)

    def test_missing_or_rerouted_lake_fails(self) -> None:
        (self.fixture.home / ".elan" / "bin" / "lake").unlink()
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_LAKE_MISSING")
        reroute = self.fixture.directory / "reroute"
        reroute.mkdir()
        (reroute / ".atpkg-reroute-dir").touch()
        write_script(reroute / "lake", "exit 0\n")
        self.fixture.path.insert(0, str(reroute))
        self.assertFailsWith(self.fixture.check(), "GATE_ENV_LAKE_REROUTED")

    # ---- command line -----------------------------------------------------
    def test_usage_errors_and_help(self) -> None:
        result = self.fixture.check("--bogus")
        self.assertEqual(result.returncode, 2)
        self.assertIn("unknown option: --bogus", result.stderr)
        result = self.fixture.check("--help")
        self.assertEqual(result.returncode, 0)
        self.assertIn("GATE_ENV_TRUST_TOOLCHAINS_DIVERGENT", result.stdout)
        self.assertNotIn("RESULT", result.stdout)

    def test_with_managed_bin_places_the_managed_launchers_after_lean(self) -> None:
        (self.fixture.prefix / "bin").mkdir(parents=True)
        result = self.fixture.check("--with-managed-bin")
        self.assertPasses(result)
        home = self.fixture.home
        self.assertIn(f"PATH head: {home}/.elan/bin | {self.fixture.prefix}/bin | {self.fixture.sysbin}",
                      result.stdout)

    def test_trust_cg_dir_selects_the_checked_repository(self) -> None:
        other = self.fixture.directory / "elsewhere"
        shutil.copytree(self.fixture.repo, other)
        (other / "rust-toolchain.toml").write_text('[toolchain]\nchannel = "1.97.1"\n')
        self.fixture.env_extra["TRUST_CG_DIR"] = str(other)
        result = self.fixture.check()
        self.assertIn(f"repository: {other}", result.stdout)
        self.assertFailsWith(result, "GATE_ENV_RUST_PIN_DRIFT")


class GateEnvSourceTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="trust-cg-gate-env-source-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.home = self.directory / "home"
        self.cargo_bin = self.home / ".cargo" / "bin"
        self.cargo_bin.mkdir(parents=True)

    def source(self, shell: str, snippet: str, path: str, **extra: str) -> subprocess.CompletedProcess[str]:
        env = {"HOME": str(self.home), "PATH": path, "GATE_ENV": str(GATE_ENV), **extra}
        argv = [shell, "--noprofile", "--norc", "-c", snippet] if shell == BASH else [shell, "-f", "-c", snippet]
        return subprocess.run(argv, env=env, capture_output=True, text=True, timeout=30, check=False)

    def test_sourcing_leaves_path_alone_without_options(self) -> None:
        # No stock rustup proxies are put first any more: the Rust toolchain
        # is the Trust package already on PATH.
        cargo = str(self.cargo_bin)
        result = self.source(BASH, 'source "$GATE_ENV" && printf "%s" "$PATH"', f"/usr/bin::/bin:{cargo}:/sbin")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, f"/usr/bin::/bin:{cargo}:/sbin")
        self.assertEqual(result.stderr, "")

    def test_sourcing_runs_no_check_and_never_fails_on_host_state(self) -> None:
        # No rustc, no Lean, no managed tools: sourcing must still succeed silently.
        result = self.source(BASH, 'source "$GATE_ENV"; echo "rc=$?"', "/usr/bin:/bin")
        self.assertEqual(result.stdout, "rc=0\n")
        self.assertNotIn("gate_env:", result.stdout + result.stderr)

    def test_sourcing_ignores_and_preserves_caller_arguments_under_strict_options(self) -> None:
        snippet = ('set -euo pipefail; set -- --bogus positional; source "$GATE_ENV"; '
                   'printf "%s|%s|%s\\n" "$#" "$1" "${PATH%%:*}"')
        result = self.source(BASH, snippet, "/usr/bin:/bin")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "2|--bogus|/usr/bin\n")

    def test_empty_path_gains_no_current_directory_entry(self) -> None:
        snippet = 'PATH=; source "$GATE_ENV"; gate_env_prelude --with-lean; printf "%s" "$PATH"'
        result = self.source(BASH, snippet, "/usr/bin:/bin")
        self.assertEqual(result.stdout, str(self.home / ".elan" / "bin"))

    def test_prelude_options_order_lean_and_managed_bin(self) -> None:
        managed = self.directory / "atpkg" / "bin"
        managed.mkdir(parents=True)
        elan = str(self.home / ".elan" / "bin")
        snippet = ('source "$GATE_ENV" && gate_env_prelude --with-lean --with-managed-bin && '
                   'printf "%s" "$PATH"')
        result = self.source(BASH, snippet, f"/usr/bin:{managed}:{elan}:/bin", ATPKG_BIN=str(managed))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, f"{elan}:{managed}:/usr/bin:/bin")

    def test_prelude_rejects_unknown_options_and_unset_home(self) -> None:
        result = self.source(BASH, 'source "$GATE_ENV"; gate_env_prelude --bogus; echo "rc=$?"', "/usr/bin:/bin")
        self.assertIn("rc=2", result.stdout)
        self.assertIn("unknown prelude option: --bogus", result.stderr)
        env = {"PATH": "/usr/bin:/bin", "GATE_ENV": str(GATE_ENV)}
        snippet = 'source "$GATE_ENV"; echo "rc=$?"; gate_env_prelude --with-lean; echo "rc=$?"'
        result = subprocess.run([BASH, "--noprofile", "--norc", "-c", snippet],
                                env=env, capture_output=True, text=True, timeout=30, check=False)
        # Without options the prelude needs no HOME; Lean's ~/.elan/bin does.
        self.assertEqual(result.stdout, "rc=0\nrc=1\n")
        self.assertIn("HOME is unset", result.stderr)

    @unittest.skipUnless(ZSH, "zsh is not installed")
    def test_zsh_can_source_the_prelude(self) -> None:
        cargo = str(self.cargo_bin)
        result = self.source(ZSH, 'source "$GATE_ENV" && gate_env_prelude --with-lean && print -rn -- "$PATH"',
                             f"/usr/bin:{cargo}:/bin")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, f"{self.home}/.elan/bin:/usr/bin:{cargo}:/bin")


class GateConsumerTests(unittest.TestCase):
    """The soundness gate uses this prelude; no gate exports stock rustup proxies."""

    CONSUMERS = ("soundness_check.sh",)
    NO_PROXY_EXPORT = ("soundness_check.sh", "compile_time_canary.sh", "compile_determinism_sentinel.sh")

    def test_consumers_source_the_prelude_and_keep_no_private_proxy_export(self) -> None:
        for name in self.CONSUMERS:
            with self.subTest(script=name):
                text = (ROOT / "scripts" / name).read_text()
                self.assertRegex(text, r'(?m)^[^#\n]*source "\$.*/gate_env\.sh"')
        for name in self.NO_PROXY_EXPORT:
            with self.subTest(script=name):
                text = (ROOT / "scripts" / name).read_text()
                self.assertNotRegex(text, r'export PATH="\$\{?HOME\}?/\.cargo/bin')

    def soundness_fixture(self) -> tuple[Path, dict[str, str]]:
        temporary = tempfile.TemporaryDirectory(prefix="trust-cg-gate-env-soundness-")
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        scripts = directory / "cg" / "scripts"
        scripts.mkdir(parents=True)
        for name in ("soundness_check.sh", "gate_env.sh", "run_with_timeout.py", "matrix_results.py",
                     "trust_cargo.sh", "trust_toolchain.py"):
            shutil.copy2(ROOT / "scripts" / name, scripts / name)
        home = directory / "home"
        seen = directory / "path-seen"
        package = directory / "package" / "bin"
        write_script(package / "trustc", "printf '%s\\n' 'binary: trustc' 'host: aarch64-apple-darwin'\n")
        write_script(package / "targo", f"""printf '%s\\n' "$PATH" >> '{seen}'
shift  # --unverified
case "$1" in
  build) mkdir -p "$CARGO_TARGET_DIR/release"; : > "$CARGO_TARGET_DIR/release/clean"
         chmod +x "$CARGO_TARGET_DIR/release/clean" ;;
  test) printf '%s\\n' 'running 1 test' 'test micro_diversity_is_nonvacuous ... ok' \\
          'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;' ;;
esac
""")
        clean = directory / "clean"
        clean.mkdir()
        sysbin = directory / "sysbin"
        sysbin.mkdir()
        (sysbin / "python3").symlink_to(sys.executable)
        env = {"HOME": str(home), "CLEAN_DIR": str(clean), "TMPDIR": str(directory),
               "PATH": f"{sysbin}:/usr/bin:/bin", "SEEN": str(seen), "TRUST_TARGO": str(package / "targo")}
        return scripts, env

    def test_soundness_gate_runs_cargo_under_the_shared_prelude(self) -> None:
        scripts, env = self.soundness_fixture()
        result = subprocess.run([BASH, str(scripts / "soundness_check.sh"), "--self-test-clean-cargo-command"],
                                env=env, capture_output=True, text=True, timeout=120, check=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        paths = Path(env["SEEN"]).read_text().splitlines()
        self.assertEqual(len(paths), 2, paths)
        home = env["HOME"]
        for path in paths:
            entries = path.split(":")
            self.assertEqual(entries[0], f"{home}/.elan/bin")
            self.assertNotIn(f"{home}/.cargo/bin", entries)

    def test_soundness_gate_refuses_to_run_without_the_prelude(self) -> None:
        scripts, env = self.soundness_fixture()
        (scripts / "gate_env.sh").unlink()
        result = subprocess.run([BASH, str(scripts / "soundness_check.sh"), "--self-test-clean-cargo-command"],
                                env=env, capture_output=True, text=True, timeout=120, check=False)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("cannot apply the scripts/gate_env.sh PATH prelude", result.stderr)
        self.assertFalse(Path(env["SEEN"]).exists())


if __name__ == "__main__":
    unittest.main()
