"""Resolve the Trust compiler pack the rustc bridge pins, and refuse the rest."""

from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import shlex
import sys
import tempfile
import time
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "trust_toolchain.py"
SPEC = importlib.util.spec_from_file_location("trust_toolchain_under_test", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
TOOLCHAIN = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TOOLCHAIN)

COMMIT = "3" * 40
# Match the certificate gate's shell/Python fixture trampoline: a managed
# interpreter may live under Application Support, which a shebang splits.
FAKE_TOOL = ("#!/bin/sh\n" + "'''exec' " + shlex.quote(sys.executable)
             + ' "$0" "$@"\n' + "' '''\n") + r'''import os
from pathlib import Path
import sys

mode = os.environ.get("FAKE_TRUST_MODE", "")
name = Path(sys.argv[0]).name
arguments = sys.argv[1:]
package = Path(sys.argv[0]).resolve().parent.parent
if name == "targo":
    if arguments == ["--version"]:
        print("cargo 1.99.0-dev" if mode == "targo-is-cargo" else "targo 1.99.0-dev (3333333 2026-09-17) (targo 0.1.0)")
        sys.exit(0)
    if arguments[:3] == ["--unverified", "rustc", "--offline"]:
        assert arguments[-3:] == ["--lib", "--", "--print=sysroot"]
        compiler = next(arguments[i+1].split("=", 1)[1] for i in range(len(arguments)-1)
                        if arguments[i] == "--config" and arguments[i+1].startswith("build.rustc="))
        import json, subprocess
        sys.exit(subprocess.call([json.loads(compiler), "--print=sysroot"]))
    sys.exit(64)
if arguments == ["-vV"]:
    if mode == "probe-fails":
        print("broken compiler", file=sys.stderr)
        sys.exit(9)
    print("rustc 1.99.0-dev (333333333 2026-09-17) (trustc 0.1.0)")
    print("binary: " + ("rustc" if mode == "unbranded" else name))
    if mode == "unknown-commit":
        print("commit-hash: unknown")
    elif mode == "duplicate-commit":
        print("commit-hash: " + "3" * 40)
        print("commit-hash: " + "4" * 40)
    else:
        print("commit-hash: " + "3" * 40)
    print("commit-date: 2026-09-17")
    if mode != "no-host":
        print("host: aarch64-unknown-linux-gnu")
    print("release: 1.99.0-dev")
    sys.exit(0)
if arguments == ["--print=sysroot"]:
    print(os.environ["FAKE_OTHER_SYSROOT"] if mode == "wrong-sysroot" else package)
    sys.exit(0)
sys.exit(64)
'''

# aterm's atpkg `targo` launcher since aterm 8d02fb9be (crates/atpkg/src/
# build_cache.rs: the atpkg shim header, `SH_BLOCK`, then the exec line),
# copied from an installed launcher with its store path replaced by @TARGET@.
# Its `targo-tippy` twin differs only in `__atb_t=tippy`.
BUILD_DIR_SHIM = (
    ROOT / "scripts" / "tests" / "fixtures" / "atpkg_launcher_shim" / "targo-build-dir.in"
).read_text(encoding="utf-8")


def write_pin(root: Path, channel: str | None) -> Path:
    pin = root / "rust-toolchain.toml"
    body = "[toolchain]\n" + (f'channel = "{channel}"\n' if channel is not None else "")
    pin.write_text("# fixture\n" + body)
    return pin


def make_package(root: Path, *, private=None, host="aarch64-unknown-linux-gnu",
                 targo=True, alias=False) -> Path:
    bindir = root / "bin"
    bindir.mkdir(parents=True)
    names = ["trustc"] + (["targo"] if targo else [])
    for name in names:
        tool = bindir / name
        tool.write_text(FAKE_TOOL)
        tool.chmod(0o755)
    if alias:
        os.link(bindir / "trustc", bindir / "rustc")
    libdir = root / "lib" / "rustlib" / host / "lib"
    libdir.mkdir(parents=True)
    for component in (private if private is not None else ("rustc_middle", "rustc_codegen_ssa")):
        (libdir / f"lib{component}-fixture.rmeta").touch()
    return bindir / "trustc"


class TargetArgumentTests(unittest.TestCase):
    def test_native_target_keeps_implicit_host_configuration(self):
        self.assertEqual(TOOLCHAIN.target_arguments({"host": "aarch64-apple-darwin"},
                                                   "aarch64-apple-darwin"), [])

    def test_cross_target_is_forwarded(self):
        self.assertEqual(TOOLCHAIN.target_arguments({"host": "aarch64-apple-darwin"},
                                                   "x86_64-unknown-linux-gnu"),
                         ["--target", "x86_64-unknown-linux-gnu"])

    def test_missing_identity_or_target_cannot_be_measured(self):
        for host, target in [(None, "aarch64-apple-darwin"), ("", "aarch64-apple-darwin"),
                             ("aarch64-apple-darwin", "")]:
            with self.subTest(host=host, target=target), self.assertRaises(TOOLCHAIN.ToolchainError):
                TOOLCHAIN.target_arguments({"host": host}, target)


class TrustToolchainResolutionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="trust-cg-toolchain-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.pin = write_pin(self.root, "trust")
        self.package = self.root / "pkg"
        self.compiler = make_package(self.package)
        self.environment = dict(os.environ)
        self.environment.pop("FAKE_TRUST_MODE", None)
        self.addCleanup(self.restore_environment)

    def restore_environment(self):
        os.environ.clear()
        os.environ.update(self.environment)

    def resolve(self, driver=None, *, mode="", path=None, pin=None, purpose="bridge"):
        os.environ["FAKE_TRUST_MODE"] = mode
        return TOOLCHAIN.resolve(
            driver, pin=pin or self.pin,
            path=str(self.package / "bin") if path is None else path,
            purpose=purpose,
        )

    def refused(self, message, **kwargs):
        with self.assertRaises(TOOLCHAIN.ToolchainError) as caught:
            self.resolve(**kwargs)
        self.assertIn(message, str(caught.exception))
        return str(caught.exception)

    # ---- positive controls ----
    def test_path_pair_resolves_one_identified_package_in_the_unverified_lane(self):
        record = self.resolve()
        self.assertEqual(record["schema"], TOOLCHAIN.SCHEMA)
        self.assertEqual(record["selection"], "path")
        self.assertEqual(record["compiler"], str(self.compiler))
        self.assertEqual(record["targo"], str(self.package / "bin" / "targo"))
        self.assertEqual(record["sysroot"], str(self.package))
        self.assertEqual(record["commit"], COMMIT)
        self.assertEqual(record["host"], "aarch64-unknown-linux-gnu")
        self.assertEqual(record["bridge_pin"]["channel"], "trust")
        self.assertEqual(record["lane"], "unverified")
        self.assertIn("no Trust-verified compilation claim", record["lane_label"])
        self.assertEqual(record["compiler_flags"], ["-Ztrust-verify=off"])
        self.assertEqual(record["build_command"], [record["targo"], "--unverified"])
        self.assertTrue(record["targo_version"].startswith("targo "))

    def test_identity_queries_keep_the_bounded_native_argv(self):
        calls = []

        def probe(arguments):
            calls.append(arguments)
            return TOOLCHAIN._probe(arguments)

        record = TOOLCHAIN.resolve(path=str(self.package / "bin"), pin=self.pin, runner=probe)
        self.assertEqual(record["sysroot"], str(self.package))
        scheduled = [c for c in calls if c[:3] == [str(self.package / "bin/targo"), "--unverified", "rustc"]]
        self.assertEqual(len(scheduled), 1)
        self.assertEqual(scheduled[0][-3:], ["--lib", "--", "--print=sysroot"])
        self.assertIn("build.rustc=" + json.dumps(str(self.compiler)), scheduled[0])
        self.assertNotIn([str(self.compiler), "--print", "sysroot"], calls)

    def test_explicit_driver_resolves_without_path_and_canonicalizes_links(self):
        link = self.root / "links" / "trustc"
        link.parent.mkdir()
        link.symlink_to(self.compiler)
        record = self.resolve(str(link), path="")
        self.assertEqual(record["selection"], "explicit-driver")
        self.assertEqual(record["requested_driver"], str(link))
        self.assertEqual(record["compiler"], str(self.compiler))
        self.assertEqual(record["targo"], str(self.package / "bin" / "targo"))

    def test_command_line_prints_each_requested_field(self):
        environment = dict(os.environ, PATH=str(self.package / "bin") + os.pathsep + "/usr/bin:/bin")
        environment.pop("FAKE_TRUST_MODE", None)
        # The CLI reads the repository pin, which must be the committed trust pin.
        self.assertEqual(TOOLCHAIN.require_trust_pin(), "trust")
        for field, expected in (("compiler", str(self.compiler)), ("sysroot", str(self.package)),
                                ("commit", COMMIT), ("targo", str(self.package / "bin" / "targo"))):
            with self.subTest(field=field):
                result = subprocess.run([sys.executable, str(SCRIPT), "--print", field], env=environment,
                                        capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), expected)
        result = subprocess.run([sys.executable, str(SCRIPT)], env=environment,
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["lane"], "unverified")
        result = subprocess.run([sys.executable, str(SCRIPT), "--print", "summary"], env=environment,
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(COMMIT, result.stdout)
        self.assertIn("unverified", result.stdout)

    def test_command_line_failure_is_a_distinct_nonzero_status(self):
        environment = dict(os.environ, PATH="/usr/bin:/bin")
        result = subprocess.run([sys.executable, str(SCRIPT), "--print", "compiler"], env=environment,
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(result.stdout, "")
        self.assertIn("missing from PATH: trustc", result.stderr)

    # ---- the bridge pin ----
    def test_retired_nightly_and_other_pins_are_refused_before_any_probe(self):
        for channel, message in (("nightly-2026-04-20", "retired stock nightly lane"),
                                 ("nightly-2026-09-01", "must be channel = \"trust\""),
                                 ("1.97.1", "must be channel = \"trust\""),
                                 (None, "found None")):
            with self.subTest(channel=channel):
                directory = self.root / f"pin-{channel}"
                directory.mkdir()
                pin = write_pin(directory, channel)
                self.refused(message, pin=pin, mode="probe-fails")

    def test_missing_or_tableless_pin_is_refused(self):
        self.refused("cannot read the bridge toolchain pin", pin=self.root / "absent.toml")
        tableless = self.root / "tableless.toml"
        tableless.write_text('channel = "trust"\n')
        self.refused("no [toolchain] table", pin=tableless)

    def test_python_without_tomllib_reads_the_same_pin(self):
        self.assertEqual(TOOLCHAIN._toolchain_table('[toolchain]\nchannel = "trust" # c\n')["channel"], "trust")
        self.assertEqual(TOOLCHAIN.require_trust_pin(ROOT / TOOLCHAIN.PIN_RELATIVE), "trust")

    # ---- package coherence ----
    def test_missing_path_tools_are_refused(self):
        self.refused("missing from PATH: trustc", path=str(self.root))
        (self.package / "bin" / "targo").unlink()
        self.refused("missing from PATH: targo")

    def test_path_pair_from_two_packages_is_refused(self):
        other = make_package(self.root / "other")
        mixed = self.root / "mixed"
        mixed.mkdir()
        (mixed / "trustc").symlink_to(self.compiler)
        (mixed / "targo").symlink_to(other.parent / "targo")
        self.refused("same installed package", path=str(mixed))

    def write_shims(self, directory, bodies):
        directory.mkdir()
        for name, body in bodies.items():
            shim = directory / name
            shim.write_text(body)
            shim.chmod(0o755)
        return directory

    def atpkg_shim(self, target):
        return f"#!/bin/sh\n# atpkg shim\nexec '{target}' \"$@\"\n"

    def test_atpkg_launcher_shims_resolve_to_the_package_they_exec(self):
        shims = self.write_shims(self.root / "shims", {
            name: self.atpkg_shim(self.package / "bin" / name) for name in ("trustc", "targo")
        })
        record = self.resolve(path=str(shims))
        self.assertEqual(record["selection"], "path-launcher")
        self.assertEqual(record["compiler"], str(self.compiler))
        self.assertEqual(record["targo"], str(self.package / "bin" / "targo"))
        self.assertEqual(record["sysroot"], str(self.package))
        self.assertEqual(record["launchers"], {
            "trustc": str(shims / "trustc"), "targo": str(shims / "targo"),
        })

    def build_dir_shim(self, target):
        return BUILD_DIR_SHIM.replace("@TARGET@", str(target))

    def admission_shim(self, target, *, helper="/Applications/aterm.app/Contents/MacOS/atpkg"):
        # atpkg/src/build_cache_registered.rs::shim_hop, without an optional
        # alternate routing branch: the static target is the final exec's.
        tail = f"exec '{target}' \"$@\"\n"
        prefix = self.build_dir_shim(target).removesuffix(tail)
        return prefix + (
            f"__atb_p='{target}'\n"
            "__atb_h=-\n"
            'if [ -n "$__atb" ]; then if [ -n "$__atb_D" ] && [ -n "$__atb_e" ]; then __atb_h=env; else __atb_h=config; fi; fi\n'
            f'[ -x \'{helper}\' ] && exec \'{helper}\' __build_admit --shim targo "$__atb_h" "$__atb_p" "$@"\n'
            "printf '%s\\n' 'atpkg: the cache registrar is unavailable; run aterm pkg repair; no build started' >&2\n"
            "exit 75\n"
        ) + tail

    def test_build_admission_shim_resolves_without_running_the_hop(self):
        targo = self.package / "bin" / "targo"
        marker = self.root / "shim-ran"
        helper = self.root / "atpkg"
        helper.write_text(f"#!/bin/sh\n: > '{marker}'\nexit 1\n")
        helper.chmod(0o755)
        shims = self.write_shims(self.root / "admission", {
            "trustc": self.atpkg_shim(self.compiler),
            "targo": self.admission_shim(targo, helper=str(helper)),
        })
        record = self.resolve(path=str(shims))
        self.assertEqual(record["selection"], "path-launcher")
        self.assertEqual(record["targo"], str(targo))
        self.assertEqual(record["build_command"], [str(targo), "--unverified"])
        self.assertFalse(marker.exists())

    def test_malformed_build_admission_hops_are_refused(self):
        targo = self.package / "bin" / "targo"
        body = self.admission_shim(targo)
        bodies = {
            "target-mismatch": body.replace(f"__atb_p='{targo}'", "__atb_p='/other/targo'"),
            "helper-mismatch": body.replace("&& exec '/Applications/aterm.app/Contents/MacOS/atpkg'", "&& exec '/other/atpkg'"),
            "relative-helper": body.replace("/Applications/aterm.app/Contents/MacOS/atpkg", "relative/atpkg"),
            "wrong-protocol": body.replace("__build_admit --shim", "unknown --shim"),
            "wrong-tool": body.replace("--shim targo", "--shim trustc"),
            "dropped-arguments": body.replace('"$__atb_p" "$@"', '"$__atb_p"'),
            "no-refusal": body.replace("exit 75\n", ""),
            "changed-refusal": body.replace("exit 75\n", "exit 0\n"),
            "extra-exec": body.replace("__atb_p=", "exec '/bin/false'\n__atb_p=", 1),
            "route-after-target": body.replace("__atb_h=-\n", "__atb_p='/other/targo'\n__atb_h=-\n"),
        }
        for label, candidate in bodies.items():
            with self.subTest(label=label):
                shims = self.write_shims(self.root / label, {
                    "trustc": self.atpkg_shim(self.compiler), "targo": candidate,
                })
                self.assertIsNone(TOOLCHAIN.launcher_target(shims / "targo"))
                self.refused("both be atpkg launcher shims", path=str(shims))

    def test_aterm_build_dir_shim_and_other_preludes_are_followed_to_the_package(self):
        targo = self.package / "bin" / "targo"
        tippy = self.build_dir_shim(targo).replace("\n__atb_t=\n", "\n__atb_t=tippy\n", 1)
        self.assertNotEqual(tippy, self.build_dir_shim(targo))
        pairs = {
            # The installed mix: a one-line trustc shim beside the build-dir targo.
            "one-line-trustc": {
                "trustc": self.atpkg_shim(self.compiler), "targo": self.build_dir_shim(targo),
            },
            "build-dir-both": {
                name: self.build_dir_shim(self.package / "bin" / name) for name in ("trustc", "targo")
            },
            "targo-tippy-twin": {"trustc": self.atpkg_shim(self.compiler), "targo": tippy},
            "export-prelude": {
                name: f"#!/bin/sh\nexport X=1\nexec '{self.package / 'bin' / name}' \"$@\"\n"
                for name in ("trustc", "targo")
            },
        }
        for label, bodies in pairs.items():
            with self.subTest(label=label):
                shims = self.write_shims(self.root / label, bodies)
                self.assertEqual(TOOLCHAIN.launcher_target(shims / "targo"), targo)
                record = self.resolve(path=str(shims))
                self.assertEqual(record["selection"], "path-launcher")
                self.assertEqual(record["compiler"], str(self.compiler))
                self.assertEqual(record["targo"], str(targo))
                self.assertEqual(record["build_command"], [str(targo), "--unverified"])
                self.assertEqual(record["launchers"], {
                    "trustc": str(shims / "trustc"), "targo": str(shims / "targo"),
                })

    def test_resolution_reads_a_launcher_shim_and_never_runs_it(self):
        # A prelude runs only when the shim itself is executed; following the
        # shim must not execute it, so the prelude cannot affect the selection.
        marker = self.root / "prelude-ran"
        shims = self.write_shims(self.root / "marking-shims", {
            name: f"#!/bin/sh\n: > '{marker}'\nexec '{self.package / 'bin' / name}' \"$@\"\n"
            for name in ("trustc", "targo")
        })
        record = self.resolve(path=str(shims))
        self.assertEqual(record["compiler"], str(self.compiler))
        self.assertFalse(marker.exists())

    def test_launcher_shim_size_cap(self):
        targo = self.package / "bin" / "targo"
        plain = self.build_dir_shim(targo)
        admitted = self.admission_shim(targo)
        self.assertLess(len(plain.encode()), TOOLCHAIN.PLAIN_LAUNCHER_SHIM_MAX_BYTES)
        self.assertLess(len(admitted.encode()), TOOLCHAIN.PLAIN_LAUNCHER_SHIM_MAX_BYTES)

        def padded_before(body, marker, size):
            head, tail = body.rsplit(marker, 1)
            padding = size - len(body.encode()) - 2
            self.assertGreaterEqual(padding, 0)
            result = head + "#" + "x" * padding + "\n" + marker + tail
            self.assertEqual(len(result.encode()), size)
            return result

        # A generic prelude gets no more room than the original bounded rule.
        for size, expected in ((TOOLCHAIN.PLAIN_LAUNCHER_SHIM_MAX_BYTES, targo),
                               (TOOLCHAIN.PLAIN_LAUNCHER_SHIM_MAX_BYTES + 1, None)):
            with self.subTest(shape="plain", size=size):
                body = padded_before(plain, "exec '", size)
                shim = self.root / f"plain-{size}"
                shim.write_text(body)
                self.assertEqual(TOOLCHAIN.launcher_target(shim), expected)

        # The maintained registered-build launcher measured 18,001 bytes. Its
        # exact admission tail earns only the separate 24 KiB absolute bound.
        for size, expected in ((18_001, targo), (TOOLCHAIN.LAUNCHER_SHIM_MAX_BYTES, targo),
                               (TOOLCHAIN.LAUNCHER_SHIM_MAX_BYTES + 1, None)):
            with self.subTest(shape="build-admission", size=size):
                body = padded_before(admitted, "__atb_p=", size)
                shim = self.root / f"admitted-{size}"
                shim.write_text(body)
                self.assertEqual(TOOLCHAIN.launcher_target(shim), expected)

        malformed = padded_before(admitted, "__atb_p=", 18_001).replace(
            "__build_admit --shim targo", "__build_admit --shim trustc"
        )
        shim = self.root / "malformed-admission-18001"
        shim.write_text(malformed)
        self.assertIsNone(TOOLCHAIN.launcher_target(shim))

    def test_shapes_that_are_not_an_atpkg_launcher_shim_are_refused(self):
        targo = self.package / "bin" / "targo"
        tail = f"exec '{targo}' \"$@\"\n"
        build_dir = self.build_dir_shim(targo)
        prelude = build_dir[: -len(tail)]
        self.assertTrue(build_dir.endswith(tail))
        bodies = {
            # A second exec anywhere, in any form.
            "second-exec-before": prelude + "exec '/bin/false' \"$@\"\n" + tail,
            "conditional-exec": prelude + f"[ -n \"$X\" ] && exec '{targo}' \"$@\"\n" + tail,
            "redirecting-exec": "#!/bin/sh\nexec 2>/dev/null\n" + tail,
            "exec-in-function": f"#!/bin/sh\nf() {{ exec '{targo}' \"$@\"; }}\n" + tail,
            "exec-twice": "#!/bin/sh\n" + tail + tail,
            "exec-in-inline-comment": "#!/bin/sh\nexport X=1 # exec\n" + tail,
            # The exec is not the last command.
            "exec-not-last": prelude + tail + "exit 0\n",
            "continued-by-and": "#!/bin/sh\ntrue &&\n" + tail,
            "continued-by-or": "#!/bin/sh\nfalse ||\n# comment\n" + tail,
            "continued-by-pipe": "#!/bin/sh\nprintf x |\n" + tail,
            "continued-by-backslash": "#!/bin/sh\necho \\\n" + tail,
            "here-document": "#!/bin/sh\ncat <<EOF\n" + tail,
            # The target is not one quoted absolute file given "$@".
            "relative-target": "#!/bin/sh\nexec 'pkg/bin/targo' \"$@\"\n",
            "unquoted-target": f"#!/bin/sh\nexec {targo} \"$@\"\n",
            "double-quoted-target": f"#!/bin/sh\nexec \"{targo}\" \"$@\"\n",
            "arguments-dropped": f"#!/bin/sh\nexec '{targo}'\n",
            "arguments-changed": f"#!/bin/sh\nexec '{targo}' \"$@\" --extra\n",
            # Not a #!/bin/sh file.
            "bash": "#!/bin/bash\n" + build_dir.split("\n", 1)[1],
            "env-sh": "#!/usr/bin/env sh\n" + tail,
            "no-interpreter": build_dir.split("\n", 1)[1],
            "empty": "",
        }
        for label, body in bodies.items():
            with self.subTest(label=label):
                shims = self.write_shims(self.root / label, {
                    "trustc": self.atpkg_shim(self.compiler), "targo": body,
                })
                self.assertIsNone(TOOLCHAIN.launcher_target(shims / "targo"))
                self.refused("both be atpkg launcher shims", path=str(shims))

    def test_build_dir_shim_keeps_the_pair_and_package_rules(self):
        targo = self.package / "bin" / "targo"
        half = self.write_shims(self.root / "half-build-dir", {
            "trustc": FAKE_TOOL, "targo": self.build_dir_shim(targo),
        })
        self.refused("both be atpkg launcher shims", path=str(half))
        other = make_package(self.root / "other")
        mixed = self.write_shims(self.root / "mixed-build-dir", {
            "trustc": self.atpkg_shim(self.compiler),
            "targo": self.build_dir_shim(other.parent / "targo"),
        })
        self.refused("must exec one installed package", path=str(mixed))
        foreign = self.write_shims(self.root / "foreign-build-dir", {
            "trustc": self.atpkg_shim(self.root / "absent" / "trustc"),
            "targo": self.build_dir_shim(self.root / "absent" / "targo"),
        })
        self.refused("behind the PATH launcher shim does not exist", path=str(foreign))
        # A target that exists but is no package (no host libraries) is refused
        # by the package rules, exactly as for a file named directly.
        loose = self.root / "loose" / "bin"
        loose.mkdir(parents=True)
        for name in ("trustc", "targo"):
            (loose / name).write_text(FAKE_TOOL)
            (loose / name).chmod(0o755)
        outside = self.write_shims(self.root / "outside-build-dir", {
            "trustc": self.atpkg_shim(loose / "trustc"),
            "targo": self.build_dir_shim(loose / "targo"),
        })
        self.refused("lacks host target libraries", path=str(outside))

    def test_other_launchers_are_not_a_package_and_name_the_real_driver(self):
        bodies = {
            "exec-not-last": {
                name: f"#!/bin/sh\nexec '{self.package / 'bin' / name}' \"$@\"\nexit 3\n"
                for name in ("trustc", "targo")
            },
            "bash": {
                name: f"#!/bin/bash\nexec '{self.package / 'bin' / name}' \"$@\"\n"
                for name in ("trustc", "targo")
            },
        }
        for label, shim_bodies in bodies.items():
            with self.subTest(label=label):
                shims = self.write_shims(self.root / label, shim_bodies)
                message = self.refused("package mismatch", path=str(shims))
                self.assertIn(f"--driver {self.compiler}", message)
        # A relative exec target is not the atpkg shape either; the wrapper is
        # probed as-is and refused.
        relative = self.write_shims(self.root / "relative-target", {
            name: f"#!/bin/sh\nexec 'pkg/bin/{name}' \"$@\"\n" for name in ("trustc", "targo")
        })
        with self.assertRaises(TOOLCHAIN.ToolchainError):
            self.resolve(path=str(relative))
        self.assertIsNone(TOOLCHAIN.launcher_target(relative / "trustc"))

    def test_launchers_must_both_exec_one_package(self):
        other = make_package(self.root / "other")
        mixed = self.write_shims(self.root / "mixed-shims", {
            "trustc": self.atpkg_shim(self.compiler),
            "targo": self.atpkg_shim(other.parent / "targo"),
        })
        self.refused("must exec one installed package", path=str(mixed))
        half = self.write_shims(self.root / "half-shim", {
            "trustc": self.atpkg_shim(self.compiler), "targo": FAKE_TOOL,
        })
        self.refused("both be atpkg launcher shims", path=str(half))
        foreign = self.write_shims(self.root / "foreign-shims", {
            name: self.atpkg_shim(self.root / "absent" / name) for name in ("trustc", "targo")
        })
        self.refused("behind the PATH launcher shim does not exist", path=str(foreign))

    def test_explicit_driver_needs_targo_in_the_same_package(self):
        lonely = make_package(self.root / "lonely", targo=False)
        self.refused("Trust build tool beside --driver", driver=str(lonely), path="")

    def test_unbranded_or_misnamed_drivers_are_refused(self):
        aliased = make_package(self.root / "aliased", alias=True)
        self.refused("branded trustc driver, not rustc", driver=str(aliased.parent / "rustc"), path="")
        self.refused("binary: trustc", mode="unbranded")

    def test_commit_identity_is_required(self):
        self.refused("40-hex commit identity (commit-hash: unknown)", mode="unknown-commit")
        self.refused("40-hex commit identity (commit-hash: None)", mode="duplicate-commit")

    def test_host_identity_is_required(self):
        self.refused("exactly one host triple", mode="no-host")

    def test_foreign_sysroot_is_refused(self):
        os.environ["FAKE_OTHER_SYSROOT"] = str(self.root)
        self.refused("package mismatch", mode="wrong-sysroot")

    def test_private_crates_and_host_libraries_are_required(self):
        missing = make_package(self.root / "no-private", private=("rustc_middle",))
        self.refused("private crate missing: rustc_codegen_ssa", driver=str(missing), path="")
        foreign = make_package(self.root / "foreign-host", host="x86_64-unknown-linux-gnu")
        self.refused("lacks host target libraries", driver=str(foreign), path="")

    def test_workspace_purpose_waives_only_the_private_crates(self):
        # A package without rustc-dev (the cross-built x86_64-apple-darwin pack)
        # serves the root workspace, its formatter and its linter, never the bridge.
        bare = make_package(self.root / "no-rustc-dev", private=())
        self.refused("private crate missing: rustc_middle", driver=str(bare), path="")
        record = self.resolve(driver=str(bare), path="", purpose="workspace")
        self.assertEqual(record["purpose"], "workspace")
        self.assertEqual(record["private_crates"], [])
        self.assertEqual(record["compiler"], str(bare))
        self.assertEqual(self.resolve()["private_crates"], ["rustc_middle", "rustc_codegen_ssa"])
        # Every other package rule still holds for the workspace purpose.
        foreign = make_package(self.root / "foreign-host-ws", host="x86_64-unknown-linux-gnu")
        self.refused("lacks host target libraries", driver=str(foreign), path="", purpose="workspace")
        self.refused("40-hex commit identity (commit-hash: unknown)", mode="unknown-commit", purpose="workspace")
        self.refused("unknown purpose 'fmt'", purpose="fmt")

    def test_command_line_takes_the_workspace_purpose(self):
        bare = make_package(self.root / "cli-no-rustc-dev", private=())
        environment = dict(os.environ, PATH=str(bare.parent) + os.pathsep + "/usr/bin:/bin")
        environment.pop("FAKE_TRUST_MODE", None)
        refused = subprocess.run([sys.executable, str(SCRIPT), "--print", "targo"], env=environment,
                                 capture_output=True, text=True, timeout=30)
        self.assertEqual(refused.returncode, 2)
        self.assertIn("private crate missing", refused.stderr)
        result = subprocess.run([sys.executable, str(SCRIPT), "--purpose", "workspace", "--print", "targo"],
                                env=environment, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), str(bare.parent / "targo"))

    def test_failed_probe_and_wrong_build_tool_are_refused(self):
        self.refused("exited 9", mode="probe-fails")
        self.refused("did not identify as targo", mode="targo-is-cargo")

    def test_non_executable_driver_is_refused(self):
        self.compiler.chmod(0o644)
        self.refused("not an executable file", driver=str(self.compiler), path="")


class CompilerIdentityTests(unittest.TestCase):
    """compiler_digest / same_compiler, and the probe environment."""

    def tree(self, base: Path, name: str) -> Path:
        root = base / name
        for relative, content in (
            ("bin/trustc", b"driver"), ("bin/rustc", b"driver"), ("bin/ay", b"ay"),
            ("bin/cargo", name.encode()), ("lib/librustc_driver.dylib", b"lib"),
            ("libexec/helper", b"helper"),
        ):
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
        return root

    def test_a_copied_tree_is_one_compiler_until_a_digested_file_differs(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            first, second = self.tree(base, "store"), self.tree(base, "rustup-copy")
            # bin/cargo differs and a rustdoc alias exists in one tree only.
            (second / "bin" / "rustdoc").write_bytes(b"rustdoc")
            self.assertTrue(TOOLCHAIN.same_compiler(first, COMMIT, second, COMMIT))
            self.assertFalse(TOOLCHAIN.same_compiler(first, COMMIT, second, "4" * 40))
            self.assertFalse(TOOLCHAIN.same_compiler(first, "unknown", second, "unknown"))
            for relative in ("bin/trustc", "bin/rustc", "bin/ay", "lib/librustc_driver.dylib",
                             "libexec/helper"):
                with self.subTest(relative=relative):
                    path = second / relative
                    original = path.read_bytes()
                    path.write_bytes(original + b"-other")
                    self.assertFalse(TOOLCHAIN.same_compiler(first, COMMIT, second, COMMIT))
                    path.unlink()
                    self.assertFalse(TOOLCHAIN.same_compiler(first, COMMIT, second, COMMIT))
                    path.write_bytes(original)
            self.assertTrue(TOOLCHAIN.same_compiler(first, COMMIT, second, COMMIT))

    def test_copied_trees_with_identical_unbound_symlinks_are_refused(self):
        # Link text is identical while referents differ; hashing only the link
        # must not authenticate two different compilers as one copied tree.
        for relative in ("bin", "lib", "libexec", "bin/trustc", "bin/rustc", "bin/ay",
                         "lib/librustc_driver.dylib", "lib/nested", "lib/dangling"):
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as temporary:
                base = Path(temporary)
                first, second = self.tree(base, "store"), self.tree(base, "rustup-copy")
                for root, content in ((first, b"first"), (second, b"second")):
                    path = root / relative
                    target = path.with_name(path.name + "-referent")
                    if path.exists():
                        path.rename(target)
                    elif relative.endswith("nested"):
                        target.mkdir()
                    if target.is_dir():
                        (target / "different-library").write_bytes(content)
                    elif not relative.endswith("dangling"):
                        target.write_bytes(content)
                    path.symlink_to(target.name)
                self.assertFalse(TOOLCHAIN.same_compiler(first, COMMIT, second, COMMIT))

    def test_copied_trees_with_shared_external_library_link_are_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            first, second = self.tree(base, "store"), self.tree(base, "rustup-copy")
            external = base / "external-library"
            external.write_bytes(b"not a member of either authenticated tree")
            for root in (first, second):
                (root / "lib" / "external").symlink_to(external)
            self.assertFalse(TOOLCHAIN.same_compiler(first, COMMIT, second, COMMIT))

    def test_scheduled_sysroot_blocks_wrapper_substitution_and_preserves_custody(self):
        captured = {}
        custody = {"BUILD_SLOT_CPU_PROTOCOL": "synthetic-original-protocol",
                   "CARGO_MAKEFLAGS": "synthetic-broken-advertisement",
                   "ATERM_SDK_LEASE_V3": "synthetic-original-lease",
                   "ATERM_WORKLOAD_CPU_FDS_V1": "synthetic-original-cpu"}
        hostile = {"RUSTC": "/foreign/compiler", "RUSTC_WRAPPER": "/foreign/wrapper",
                   "RUSTC_WORKSPACE_WRAPPER": "/foreign/workspace-wrapper",
                   "CARGO_BUILD_RUSTC_WRAPPER": "/foreign/config-wrapper",
                   "RUSTFLAGS": "--sysroot=/foreign", "CARGO_TARGET_DIR": "/foreign/target"}

        def observe(command, **kwargs):
            captured.update(command=command, **kwargs)
            root = kwargs["cwd"]
            self.assertEqual((root / "src/lib.rs").read_bytes(), b"")
            manifest = (root / "Cargo.toml").read_text()
            self.assertIn("[workspace]", manifest)
            self.assertNotIn("dependencies", manifest)
            self.assertNotIn("build=", manifest)
            return "/selected\n"

        with mock.patch.dict(os.environ, dict(custody, **hostile)), \
                mock.patch.object(TOOLCHAIN, "_probe", side_effect=observe):
            self.assertEqual(TOOLCHAIN.scheduled_sysroot_query(
                Path("/selected/bin/trustc"), Path("/selected/bin/targo"), TOOLCHAIN._probe), "/selected\n")
        env = captured["environment"]
        for key, value in custody.items():
            self.assertEqual(env[key], value)
        self.assertEqual(env["RUSTC"], "/selected/bin/trustc")
        for key in set(hostile) - {"RUSTC"}:
            self.assertNotIn(key, env)
        self.assertIn('build.rustc-wrapper=""', captured["command"])
        self.assertIn('build.rustc-workspace-wrapper=""', captured["command"])
        self.assertEqual(captured["command"][-3:], ["--lib", "--", "--print=sysroot"])

    def test_probe_environment_drops_only_the_controls_trustc_refuses(self):
        source = {"PATH": "/bin", "TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1", "TCG_SOLVER_PATH": "/ay",
                  "TRUST_NO_VERIFY": "1", "XTRUST_CG_KEEP": "1"}
        self.assertEqual(
            TOOLCHAIN.without_untracked_controls(source),
            {"PATH": "/bin", "TRUST_NO_VERIFY": "1", "XTRUST_CG_KEEP": "1"},
        )

    def test_scheduled_query_timeout_stops_its_actual_descendant(self):
        with tempfile.TemporaryDirectory(prefix="trust-cg-query-timeout-") as temporary:
            root = Path(temporary)
            ready, delayed = root / "ready", root / "delayed"
            worker = ("from pathlib import Path; import time; "
                      f"Path({str(ready)!r}).write_text('started'); "
                      f"time.sleep(2); Path({str(delayed)!r}).write_text('escaped')")
            parent = ("import subprocess,time; "
                      f"subprocess.Popen({[sys.executable, '-c', worker]!r}); time.sleep(30)")
            with mock.patch.object(TOOLCHAIN, "PROBE_TIMEOUT_SECONDS", 1), \
                    self.assertRaises(TOOLCHAIN.ToolchainError):
                TOOLCHAIN._probe([sys.executable, "-c", parent],
                                 environment=dict(os.environ), cwd=root, subtree=True)
            self.assertTrue(ready.is_file(), "the actual descendant must have started")
            time.sleep(2.2)
            self.assertFalse(delayed.exists(), "timed-out descendant survived its owned group cleanup")


if __name__ == "__main__":
    unittest.main()
