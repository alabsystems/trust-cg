"""scripts/assemble_trust_overlay.py: what an overlay binds, and every refusal."""

from __future__ import annotations

import hashlib
import importlib.util
import io
import json
import os
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "assemble_trust_overlay.py"
SPEC = importlib.util.spec_from_file_location("assemble_trust_overlay_under_test", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
ASSEMBLE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ASSEMBLE)

# `trustc` prints its own sysroot (the directory above its bin/), as the pack's does.
FAKE_TRUSTC = f"#!{sys.executable}\n" + r'''import os, sys
from pathlib import Path
if sys.argv[1:] == ["--print", "sysroot"]:
    print(os.environ.get("FAKE_SYSROOT_ANSWER") or Path(sys.argv[0]).absolute().parent.parent)
elif sys.argv[1:] == ["-vV"]:
    print("rustc 1.99.0-dev (321aaeda7 2026-09-17) (trustc 0.1.0)")
    print("binary: trustc")
    print("commit-hash: " + "3" * 40)
    print("host: aarch64-apple-darwin")
else:
    sys.exit(64)
'''

# The compiler a wrapper sysroot's `bin/trustc` runs: it honours `--sysroot`.
WRAPPED_TRUSTC = f"#!{sys.executable}\n" + r'''import os, sys
from pathlib import Path
args = sys.argv[1:]
sysroot = Path(sys.argv[0]).absolute().parent.parent
if args[:1] == ["--sysroot"]:
    sysroot, args = args[1], args[2:]
if args == ["--print", "sysroot"]:
    print(os.environ.get("FAKE_SYSROOT_ANSWER") or sysroot)
elif args == ["-vV"]:
    print("rustc 1.99.0-dev (3d7768caf 2026-08-21) (trustc 0.1.0)")
    print("binary: trustc")
    print("commit-hash: " + "6" * 40)
    print("host: x86_64-apple-darwin")
else:
    sys.exit(64)
'''


def wrapper_script(compiler: Path, sysroot_line: str, extra: str = "") -> str:
    """A wrapper like the x86_64 Darwin stage0-sysroot's `bin/trustc`."""
    return (
        "#!/bin/sh\n"
        "# The pack trustc pointed at the stage0-sysroot.\n"
        f"trustc='{compiler}'\n"
        f"{sysroot_line}\n"
        f"{extra}"
        'for arg in "$@"; do\n'
        '    case "$arg" in\n'
        '        --sysroot|--sysroot=*) exec "$trustc" "$@" ;;\n'
        "    esac\n"
        "done\n"
        'exec "$trustc" --sysroot "$sysroot" "$@"\n'
    )


CAPABLE = (
    "External certificate verification: PASSED\n  Type: Alethe SMT proof\n"
    "  Proof status: fully verified\n"
)
NO_CARCARA = "Error: proof_verification_failed: carcara-verify feature required for tier 1 verification\n"


def clean_script(transcript: str, code: int) -> str:
    return (
        "#!/bin/sh\n"
        'if [ "$1" = --version ]; then echo "clean 0.9.0"; exit 0; fi\n'
        f"cat <<'EOF'\n{transcript}EOF\nexit {code}\n"
    )


def executable(path: Path, text: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    path.chmod(0o755)
    return path


def git(checkout: Path, *arguments: str) -> str:
    return subprocess.run(
        ["git", "-C", str(checkout), *arguments],
        check=True,
        capture_output=True,
        text=True,
        env={**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
             "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"},
    ).stdout.strip()


def repository(path: Path, commits: int) -> list[str]:
    path.mkdir(parents=True)
    git(path, "init", "-q")
    shas = []
    for index in range(commits):
        (path / "file.txt").write_text(f"{path.name} {index}\n")
        git(path, "add", "file.txt")
        git(path, "commit", "-q", "-m", f"c{index}")
        shas.append(git(path, "rev-parse", "HEAD"))
    return shas


def ay_banner(commit: str, increment: int | str) -> str:
    stamp = f"0.27.0+build.{increment}.{commit}@2026-09-29T02:54:35Z"
    return (
        f"ay {stamp}\nbuild.version=0.27.0\nbuild.increment={increment}\n"
        f"build.commit={commit}\nbuild.stamp={stamp}\n"
    )


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class AssembleTrustOverlayTests(unittest.TestCase):
    def setUp(self) -> None:
        self.scratch = tempfile.TemporaryDirectory()
        self.root = Path(self.scratch.name).resolve()
        self.pack = self.root / "store" / "trust" / "9192"
        executable(self.pack / "bin" / "trustc", FAKE_TRUSTC)
        executable(self.pack / "bin" / "targo", "#!/bin/sh\nexit 0\n")
        executable(self.pack / "bin" / "ay", "#!/bin/sh\necho pack ay\n")
        executable(self.pack / "bin" / "clean", "#!/bin/sh\necho pack clean\n")
        (self.pack / "lib" / "rustlib").mkdir(parents=True)
        self.ay_shas = repository(self.root / "ay-src", 3)
        self.clean_shas = repository(self.root / "clean-src", 2)
        self.ay = executable(self.root / "built" / "ay", "#!/bin/sh\ncat <<'EOF'\n"
                             + ay_banner(self.ay_shas[-1], 3) + "EOF\n")
        self.clean = executable(self.root / "built" / "clean", clean_script(CAPABLE, 0))
        self.out = self.root / "overlays" / "trust9192+ay3"
        self.out.parent.mkdir()
        os.environ.pop("FAKE_SYSROOT_ANSWER", None)

    def tearDown(self) -> None:
        os.environ.pop("FAKE_SYSROOT_ANSWER", None)
        self.scratch.cleanup()

    def assemble(self, *extra: str, ay: Path | None = None, clean: Path | None = None) -> tuple[int, str]:
        argv = [
            "--pack", str(self.pack),
            "--ay", str(ay or self.ay), "--ay-src", str(self.root / "ay-src"),
            "--clean", str(clean or self.clean), "--clean-src", str(self.root / "clean-src"),
            "--out", str(self.out), *extra,
        ]
        stdout, stderr = io.StringIO(), io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            code = ASSEMBLE.main(argv)
        return code, stdout.getvalue() + stderr.getvalue()

    def assert_refused(self, needle: str, *extra: str, **inputs: Path) -> None:
        code, output = self.assemble(*extra, **inputs)
        self.assertEqual(code, 2, output)
        self.assertIn("refused", output)
        self.assertIn(needle, output)
        self.assertFalse(self.out.exists(), "a refusal leaves nothing at --out")
        self.assertEqual([p.name for p in self.out.parent.iterdir()], [], "no partial clone is left")

    def test_assembles_a_clone_whose_manifest_binds_both_binaries(self) -> None:
        code, output = self.assemble(
            "--require-ay-ancestor", self.ay_shas[0],
            "--require-clean-ancestor", self.clean_shas[0],
            "--ay-build-command", "targo --unverified build --release -p ay",
        )
        self.assertEqual(code, 0, output)
        for role, source in (("ay", self.ay), ("clean", self.clean)):
            target = self.out / "bin" / role
            self.assertFalse(target.is_symlink())
            self.assertEqual(target.read_bytes(), source.read_bytes())
        self.assertEqual((self.out / "bin" / "trustc").read_bytes(), (self.pack / "bin" / "trustc").read_bytes())
        self.assertEqual(self.out.stat().st_mode & 0o777, 0o700)
        # The installed pack is untouched.
        self.assertEqual((self.pack / "bin" / "ay").read_text(), "#!/bin/sh\necho pack ay\n")
        manifest = json.loads((self.out / "overlay.json").read_text())
        self.assertEqual(manifest["schema"], "trust-cg.trust-overlay.v1")
        self.assertIs(manifest["not_a_published_pack"], True)
        self.assertEqual(manifest["signatures"], [])
        self.assertEqual(manifest["pack"]["store_id"], "9192")
        self.assertEqual(manifest["pack"]["trustc"]["commit-hash"], "3" * 40)
        self.assertEqual(manifest["ay"]["sha256"], sha256(self.ay))
        self.assertEqual(manifest["ay"]["commit"], self.ay_shas[-1])
        self.assertEqual(manifest["ay"]["increment"], "3")
        self.assertEqual(manifest["ay"]["source"]["required_ancestors"], [self.ay_shas[0]])
        self.assertEqual(manifest["ay"]["build_command"], "targo --unverified build --release -p ay")
        self.assertEqual(manifest["clean"]["sha256"], sha256(self.clean))
        self.assertEqual(manifest["clean"]["control_probe"], "fully verified")
        self.assertEqual(manifest["clean"]["source"]["commit"], self.clean_shas[-1])
        self.assertIn("asserted", manifest["clean"]["source"]["binding"])
        self.assertTrue((self.out / "OVERLAY-README.txt").is_file())
        self.assertIn(sha256(self.out / "overlay.json"), output)

    def test_refuses_an_existing_out_directory(self) -> None:
        self.out.mkdir()
        code, output = self.assemble()
        self.assertEqual(code, 2)
        self.assertIn("already exists", output)

    def test_refuses_an_unnumbered_archive_build(self) -> None:
        ay = executable(self.root / "archive" / "ay", "#!/bin/sh\ncat <<'EOF'\n"
                        + ay_banner(self.ay_shas[-1], 0) + "EOF\n")
        self.assert_refused("unnumbered build", ay=ay)

    def test_refuses_an_unknown_or_dirty_commit(self) -> None:
        for commit, needle in (("unknown", "not a 40-character"), (self.ay_shas[-1] + "-dirty", "DIRTY")):
            with self.subTest(commit=commit):
                ay = executable(self.root / "other" / "ay", "#!/bin/sh\ncat <<'EOF'\n"
                                + ay_banner(commit, 3) + "EOF\n")
                self.assert_refused(needle, ay=ay)

    def test_refuses_a_build_number_that_is_not_the_commit_count(self) -> None:
        ay = executable(self.root / "other" / "ay", "#!/bin/sh\ncat <<'EOF'\n"
                        + ay_banner(self.ay_shas[-1], 99) + "EOF\n")
        self.assert_refused("rev-list --count", ay=ay)

    def test_refuses_a_banner_from_another_commit(self) -> None:
        ay = executable(self.root / "other" / "ay", "#!/bin/sh\ncat <<'EOF'\n"
                        + ay_banner(self.ay_shas[0], 1) + "EOF\n")
        self.assert_refused("is not --ay-src HEAD", ay=ay)

    def test_refuses_a_modified_source_checkout(self) -> None:
        (self.root / "clean-src" / "file.txt").write_text("edited\n")
        self.assert_refused("tracked modifications")

    def test_refuses_a_missing_required_ancestor(self) -> None:
        self.assert_refused("does not contain required commit", "--require-ay-ancestor", self.clean_shas[0])

    def test_refuses_a_clean_that_fails_the_control_probe(self) -> None:
        clean = executable(self.root / "packclean" / "clean", clean_script(NO_CARCARA, 1))
        self.assert_refused("carcara-verify", clean=clean)
        holey = executable(self.root / "holey" / "clean", clean_script(CAPABLE + "Proof status: holey\n", 0))
        self.assert_refused("control proof", clean=holey)

    def test_refuses_a_pack_without_a_compiler(self) -> None:
        (self.pack / "bin" / "trustc").unlink()
        self.assert_refused("bin/trustc")

    def test_refuses_a_symlinked_input(self) -> None:
        link = self.root / "link-ay"
        link.symlink_to(self.ay)
        self.assert_refused("symlink", ay=link)

    def test_refuses_and_removes_an_overlay_whose_compiler_names_another_sysroot(self) -> None:
        os.environ["FAKE_SYSROOT_ANSWER"] = str(self.pack)
        self.assert_refused("not the overlay")

    def test_refuses_an_overlay_as_the_pack(self) -> None:
        code, output = self.assemble()
        self.assertEqual(code, 0, output)
        self.pack, first = self.out, self.out
        self.out = self.root / "overlays" / "second"
        code, output = self.assemble()
        self.assertEqual(code, 2, output)
        self.assertIn("itself an overlay", output)
        self.assertTrue(first.is_dir())

    def test_an_installed_pack_overlay_records_its_kind_and_no_wrapper(self) -> None:
        code, output = self.assemble()
        self.assertEqual(code, 0, output)
        manifest = json.loads((self.out / "overlay.json").read_text())
        self.assertEqual(manifest["pack"]["kind"], "installed")
        self.assertNotIn("wrapper", manifest["pack"])


class AssembleWrapperSysrootOverlayTests(unittest.TestCase):
    """`--pack-kind wrapper-sysroot`: the bridge's sysroot, whose `bin/trustc`
    is a shell wrapper with a hard-coded `--sysroot`, with no targo and no
    `bin/clean`."""

    tearDown = AssembleTrustOverlayTests.tearDown
    assemble = AssembleTrustOverlayTests.assemble

    def setUp(self) -> None:
        AssembleTrustOverlayTests.setUp(self)  # type: ignore[arg-type]
        self.compiler = executable(self.root / "pack6808" / "bin" / "trustc", WRAPPED_TRUSTC)
        self.pack = self.root / "build" / "stage0-sysroot"
        self.wrapper_text = wrapper_script(self.compiler, f"sysroot='{self.pack}'")
        executable(self.pack / "bin" / "trustc", self.wrapper_text)
        executable(self.pack / "bin" / "ay", "#!/bin/sh\necho stage1 ay\n")
        (self.pack / "lib" / "rustlib").mkdir(parents=True)
        self.out = self.root / "overlays" / "bridge+ay3"

    def wrapper_assemble(self) -> tuple[int, str]:
        return self.assemble("--pack-kind", "wrapper-sysroot")

    def assert_wrapper_refused(self, needle: str) -> None:
        code, output = self.wrapper_assemble()
        self.assertEqual(code, 2, output)
        self.assertIn("refused", output)
        self.assertIn(needle, output)
        self.assertFalse(self.out.exists(), "a refusal leaves nothing at --out")
        self.assertEqual([p.name for p in self.out.parent.iterdir()], [], "no partial clone is left")

    def test_assembles_a_wrapper_overlay_whose_compiler_names_the_overlay(self) -> None:
        code, output = self.wrapper_assemble()
        self.assertEqual(code, 0, output)
        self.assertIn(f"RUSTC={self.out}/bin/trustc", output)
        # The wrapper now names the overlay, and so does the compiler it runs.
        rewritten = (self.out / "bin" / "trustc").read_text()
        self.assertIn(f"sysroot={self.out}\n", rewritten)
        self.assertNotIn(str(self.pack), rewritten)
        self.assertEqual(rewritten.replace(f"sysroot={self.out}", f"sysroot='{self.pack}'"), self.wrapper_text)
        answer = subprocess.run(
            [str(self.out / "bin" / "trustc"), "--print", "sysroot"],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
        self.assertEqual(Path(answer), self.out)
        # bin/ay replaced; bin/clean, absent from the wrapper sysroot, added.
        for role, source in (("ay", self.ay), ("clean", self.clean)):
            self.assertEqual((self.out / "bin" / role).read_bytes(), source.read_bytes())
        # The wrapper sysroot itself is untouched.
        self.assertEqual((self.pack / "bin" / "trustc").read_text(), self.wrapper_text)
        self.assertEqual((self.pack / "bin" / "ay").read_text(), "#!/bin/sh\necho stage1 ay\n")
        self.assertFalse((self.pack / "bin" / "clean").exists())
        manifest = json.loads((self.out / "overlay.json").read_text())
        self.assertEqual(manifest["pack"]["kind"], "wrapper-sysroot")
        self.assertEqual(manifest["pack"]["trustc"]["commit-hash"], "6" * 40)
        wrapper = manifest["pack"]["wrapper"]
        self.assertEqual(wrapper["original_sha256"], hashlib.sha256(self.wrapper_text.encode()).hexdigest())
        self.assertEqual(wrapper["sha256"], sha256(self.out / "bin" / "trustc"))
        self.assertEqual(wrapper["sysroot_assignment"], {"original": str(self.pack), "overlay": str(self.out)})
        self.assertEqual(manifest["ay"]["sha256"], sha256(self.ay))
        self.assertEqual(manifest["clean"]["sha256"], sha256(self.clean))

    def test_the_installed_kind_still_requires_a_targo(self) -> None:
        code, output = self.assemble()
        self.assertEqual(code, 2, output)
        self.assertIn("bin/targo", output)
        self.assertFalse(self.out.exists())

    def test_refuses_a_wrapper_sysroot_without_rustlib(self) -> None:
        (self.pack / "lib" / "rustlib").rmdir()
        self.assert_wrapper_refused("lib/rustlib")

    def test_refuses_a_compiler_binary_as_the_wrapper(self) -> None:
        (self.pack / "bin" / "trustc").write_bytes(b"\xcf\xfa\xed\xfe\x07\x00\x00\x01\xff")
        self.assert_wrapper_refused("not a text wrapper")

    def test_refuses_a_wrapper_with_no_or_two_sysroot_assignments(self) -> None:
        for line, extra in (("# no assignment", ""), (f"sysroot='{self.pack}'", f"sysroot='{self.pack}'\n")):
            with self.subTest(line=line, extra=extra):
                executable(self.pack / "bin" / "trustc", wrapper_script(self.compiler, line, extra))
                self.assert_wrapper_refused("`sysroot=` assignments")

    def test_refuses_a_wrapper_that_assigns_another_sysroot(self) -> None:
        other = self.root / "elsewhere"
        executable(self.pack / "bin" / "trustc", wrapper_script(self.compiler, f"sysroot='{other}'"))
        self.assert_wrapper_refused("not the wrapper sysroot itself")

    def test_refuses_a_wrapper_that_names_the_sysroot_elsewhere(self) -> None:
        extra = f"export LIBRARY_PATH='{self.pack}/lib'\n"
        executable(self.pack / "bin" / "trustc", wrapper_script(self.compiler, f"sysroot='{self.pack}'", extra))
        self.assert_wrapper_refused("outside its `sysroot=` assignment")

    def test_refuses_a_symlinked_wrapper(self) -> None:
        real = executable(self.root / "real-wrapper" / "trustc", self.wrapper_text)
        (self.pack / "bin" / "trustc").unlink()
        (self.pack / "bin" / "trustc").symlink_to(real)
        self.assert_wrapper_refused("symlink")

    def test_refuses_a_wrapper_overlay_whose_compiler_names_another_sysroot(self) -> None:
        os.environ["FAKE_SYSROOT_ANSWER"] = str(self.pack)
        self.assert_wrapper_refused("not the overlay")


if __name__ == "__main__":
    unittest.main()
