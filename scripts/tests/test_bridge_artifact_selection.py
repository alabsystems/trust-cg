"""Actual Cargo layout/selector tests, not Trust compiler differentials.

Run with the installed Trust package on PATH (`trustc`/`targo`; the bridge
and this stand-in for it pin `channel = "trust"`, owner directive 2026-09-28).
Each lane builds a tiny ordinary
Rust dylib and compiles the actual two bridge test sources, then executes only
their artifact selectors and the selection refusal controls. Compiler/proof
tests imported from those files are explicitly excluded, never called passed.
"""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "scripts/tests/fixtures/bridge_artifact_selection"
SUBJECTS = [
    ROOT / "crates/rustc-codegen-trust-cg/tests/dyn_fat_leaf_differential.rs",
    ROOT / "crates/rustc-codegen-trust-cg/tests/boolean_knob_value_grammar.rs",
    ROOT / "crates/rustc-codegen-trust-cg/tests/support/backend_artifact.rs",
    ROOT / "crates/rustc-codegen-trust-cg/tests/support/toolchain.rs",
    *sorted(path for path in FIXTURE.rglob("*") if path.is_file()),
]


def source_identity():
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in SUBJECTS}


class BridgeArtifactSelectionTests(unittest.TestCase):
    def test_actual_cargo_profile_and_target_layouts(self):
        # BRIDGE_ARTIFACT_SELECTION_ARTIFACTS names a directory to keep the
        # records (and the Cargo target) in; otherwise both go to a temporary
        # directory removed when the test ends, passed or failed.
        named = os.environ.get("BRIDGE_ARTIFACT_SELECTION_ARTIFACTS")
        if named:
            artifacts = Path(named).resolve()
        else:
            scratch = tempfile.TemporaryDirectory(prefix="tcg-artifact-selection-")
            self.addCleanup(scratch.cleanup)
            artifacts = Path(scratch.name).resolve()
        artifacts.mkdir(parents=True, exist_ok=True)
        target = Path(os.environ.get("CARGO_TARGET_DIR", str(artifacts / "target"))).resolve()
        before = source_identity()
        version = subprocess.check_output(["trustc", "-vV"], cwd=ROOT, text=True, timeout=20)
        host = next(line.removeprefix("host: ") for line in version.splitlines()
                    if line.startswith("host: "))
        lanes = [("debug", []), ("release", ["--release"]),
                 ("custom-profile", ["--profile", "artifact-contract"]),
                 ("explicit-host-target", ["--target", host])]
        records = []
        for name, options in lanes:
            with self.subTest(lane=name):
                base = ["targo", "--unverified", "test", "--locked", "--offline", "-j2",
                           "--manifest-path", str(FIXTURE / "Cargo.toml"),
                           "--target-dir", str(target), "--test", "selection", *options]
                build_command = [*base, "--no-run", "--message-format=json-render-diagnostics"]
                build = subprocess.run(build_command, cwd=ROOT, text=True, capture_output=True,
                                       timeout=180)
                (artifacts / f"{name}.build.stdout").write_text(build.stdout)
                (artifacts / f"{name}.build.stderr").write_text(build.stderr)
                self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
                messages = [json.loads(line) for line in build.stdout.splitlines()
                            if line.startswith("{")]
                libraries = [Path(path) for message in messages
                             if message.get("reason") == "compiler-artifact"
                             and message.get("target", {}).get("name") == "rustc_codegen_trust_cg"
                             and "dylib" in message.get("target", {}).get("crate_types", [])
                             for path in message.get("filenames", [])
                             if Path(path).suffix in (".dylib", ".so", ".dll")]
                self.assertEqual(len(libraries), 1, libraries)
                library = libraries[0].resolve(strict=True)
                environment = dict(os.environ, BRIDGE_ARTIFACT_EXPECTED_LIBRARY=str(library))
                command = [*base,
                           "--", "--nocapture", "--test-threads=1",
                           "--skip", "fat_leaf::fat_pointer_memory_leaves_match_llvm",
                           "--skip", "boolean_knob::a_boolean_knob_reads_its_value_and_not_its_presence"]
                result = subprocess.run(command, cwd=ROOT, env=environment, text=True, capture_output=True,
                                        timeout=180)
                (artifacts / f"{name}.stdout").write_text(result.stdout)
                (artifacts / f"{name}.stderr").write_text(result.stderr)
                records.append({"lane": name, "build_command": build_command,
                                "library": str(library), "library_sha256": hashlib.sha256(library.read_bytes()).hexdigest(),
                                "command": command, "exit": result.returncode})
                (artifacts / "records.json").write_text(json.dumps(records, indent=2) + "\n")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                count = 12 if os.name == "posix" else 11
                self.assertIn(f"{count} passed; 0 failed; 0 ignored; 0 measured; 2 filtered out",
                              result.stdout)
        after = source_identity()
        (artifacts / "source-before.json").write_text(json.dumps(before, indent=2) + "\n")
        (artifacts / "source-after.json").write_text(json.dumps(after, indent=2) + "\n")
        (artifacts / "compiler.txt").write_text(version)
        self.assertEqual(after, before, "artifact-selection source changed during qualification")
        print(f"BRIDGE_ARTIFACT_SELECTION lanes={len(records)} artifacts={artifacts}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
