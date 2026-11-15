#!/usr/bin/env python3
"""Pure source controls for the bounded full-state diagnostic runner.

No compiler/benchmark is launched by these tests. Native kernel agreement and
actual tool qualification are separate requirements.
"""

import argparse
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import full_output as output
import run_full_output as runner


class FullOutputControls(unittest.TestCase):
    def test_original_denominator_and_unsupported_rows_remain(self):
        manifest = output.load_manifest(HERE)
        rows = output.empty_accounting(manifest)
        self.assertEqual(len(rows), 18)
        self.assertEqual(set(rows), set(manifest))
        self.assertEqual(output.counts(rows), {
            "original_denominator": 18, "supported_count": 3, "unsupported_count": 15,
            "full_output_agreement_count": 0, "incomplete_count": 3, "mismatch_count": 0,
        })
        for stem in output.SUPPORTED:
            rows[stem]["verdict"] = "FULL_OUTPUT_AGREEMENT"
        self.assertEqual(output.counts(rows)["original_denominator"], 18)
        self.assertEqual(output.counts(rows)["unsupported_count"], 15)
        self.assertNotIn("MATCH", {row["verdict"] for row in rows.values()})

    def test_every_supported_renderer_preserves_actual_kernel_and_iterations(self):
        for stem, spec in output.SUPPORTED.items():
            for language, folder, suffix, boundary in (
                ("rust", "progs", ".rs", "fn main() {"),
                ("c", "progs_c", ".c", "int main(void) {"),
            ):
                data = (HERE / folder / (stem + suffix)).read_bytes()
                rendered = output.render_validation(stem, language, data).decode()
                original_body = data.decode().split(boundary, 1)[1].split(spec[language + "_stop"], 1)[0]
                observed_body = rendered.split(boundary, 1)[1].split("    oracle_output(", 1)[0]
                self.assertEqual(original_body, observed_body)
                self.assertIn("TCG-BENCH-OUTPUT-V1 " + stem, rendered)
                self.assertIn("u6=", rendered)
                self.assertEqual(data, (HERE / folder / (stem + suffix)).read_bytes())
                with self.assertRaises(output.OutputError):
                    output.render_validation(stem, language, data + b"\n")

    def test_manifest_or_membership_mutation_is_not_a_new_denominator(self):
        with tempfile.TemporaryDirectory() as temporary:
            here = Path(temporary)
            (here / "progs").mkdir()
            original = (HERE / "progs" / "manifest.json").read_bytes()
            (here / "progs" / "manifest.json").write_bytes(original + b"\n")
            with self.assertRaises(output.OutputError):
                output.load_manifest(here)
            (here / "progs" / "manifest.json").write_bytes(original)
            with self.assertRaises(output.OutputError):
                output.load_manifest(here)

    def test_high_bits_and_every_unsigned_transport_field_are_exact(self):
        for stem in output.SUPPORTED:
            fields = output.SUPPORTED[stem]["fields"]
            state = tuple(output.TRANSPORT[-1 - index] for index in range(len(fields)))
            residue = output.checksum(stem, state) % 126
            stdout = output.output_bytes(stem, state)
            self.assertEqual(output.decode_output(stem, stdout, b"", residue, residue), state)
            for index, value in enumerate(output.TRANSPORT):
                old = f"u{index}={value:016x}".encode()
                changed = f"u{index}={value ^ (1 << 63):016x}".encode()
                with self.assertRaises(output.OutputError):
                    output.decode_output(stem, stdout.replace(old, changed), b"", residue, residue)

    def test_stdout_cannot_drop_round_reorder_or_duplicate_fields(self):
        stem, state = "p1_xorshift", (0x8000000000000000, 41)
        stdout = output.output_bytes(stem, state)
        for wrong in (
            stdout[:-1], stdout + stdout, b"noise\n" + stdout,
            stdout.replace(b"x=8000000000000000", b"x=80000000"),
            stdout.replace(b"acc=0000000000000029", b"acc=41"),
            stdout.replace(b"acc=0000000000000029", b"acc=000000000000002A"),
            stdout.replace(b" x=8000000000000000 acc=0000000000000029",
                           b" acc=0000000000000029 x=8000000000000000"),
            stdout.replace(b"\n", b"\r\n"), stdout.replace(b" ", b"\t", 1),
        ):
            with self.assertRaises(output.OutputError):
                output.decode_output(stem, wrong, b"", 41, 41)
        with self.assertRaises(output.OutputError):
            output.decode_output(stem, stdout, b"warning", 41, 41)
        for wrong_exit in (0, 42, 127, -9, None, True):
            with self.assertRaises(output.OutputError):
                output.decode_output(stem, stdout, b"", wrong_exit, 41)

    def test_same_exit_residue_wrong_full_value_refuses_agreement(self):
        original, wrong = (9, 41), (9, 167)
        for state in (original, wrong):
            self.assertEqual(output.checksum("p1_xorshift", state) % 126, 41)
            self.assertEqual(output.decode_output("p1_xorshift", output.output_bytes("p1_xorshift", state),
                                                 b"", 41, 41), state)
        self.assertFalse(output.compare_lanes({"llvm": [original] * 3, "clang": [original] * 3,
                                              "bridge": [wrong] * 3}))

    def test_xor_collision_and_nonreturned_state_are_observed_separately(self):
        original, permuted = (1, 2, 3), (2, 1, 3)
        self.assertEqual(output.checksum("p5_struct_acc", original),
                         output.checksum("p5_struct_acc", permuted))
        self.assertFalse(output.compare_lanes({"llvm": [original] * 3, "clang": [original] * 3,
                                              "bridge": [permuted] * 3}))
        first, different_rng_state = (9, 41), (10, 41)
        self.assertFalse(output.compare_lanes({"llvm": [first] * 3, "clang": [first] * 3,
                                              "bridge": [different_rng_state] * 3}))

    def test_missing_lane_or_repeat_and_nondeterministic_state_refuse(self):
        state = (9, 41)
        positive = {lane: [state] * 3 for lane in runner.LANES}
        self.assertTrue(output.compare_lanes(positive))
        self.assertFalse(output.compare_lanes({"llvm": [state] * 3, "bridge": [state] * 3}))
        short = dict(positive, clang=[state] * 2)
        self.assertFalse(output.compare_lanes(short))
        nondeterministic = dict(positive, bridge=[state, (9, 167), state])
        self.assertFalse(output.compare_lanes(nondeterministic))

    def test_compile_and_launch_timeouts_stay_incomplete(self):
        with mock.patch.object(runner.subprocess, "run", side_effect=
                               subprocess.TimeoutExpired(["unused"], 1, output=b"partial")):
            result = runner.capture(["unused"], 1)
        self.assertEqual(result["status"], "TIMEOUT")
        self.assertIsNone(result["returncode"])
        self.assertEqual(result["stdout"], b"partial")
        with mock.patch.object(runner.subprocess, "run", side_effect=OSError("unavailable")):
            self.assertEqual(runner.capture(["unused"], 1)["status"], "EXECUTION_UNAVAILABLE")

    def test_real_lane_commands_keep_default_backend_proof_policy(self):
        tools = {"target": "aarch64-apple-darwin", "clang": "/clang",
                 "dylib": "/backend", "driver": {"compiler": "/trustc",
                                                       "compiler_flags": ["-Ztrust-verify=off"]}}
        llvm = runner.compiler_command(tools, "llvm", Path("kernel.rs"), Path("llvm"))
        bridge = runner.compiler_command(tools, "bridge", Path("kernel.rs"), Path("bridge"))
        clang = runner.compiler_command(tools, "clang", Path("kernel.c"), Path("clang"))
        self.assertEqual(llvm[0], "/trustc")
        self.assertEqual(bridge[0], "/trustc")
        self.assertIn("-Zcodegen-backend=/backend", bridge)
        self.assertNotIn("--target", llvm)
        self.assertNotIn("--target", bridge)
        self.assertNotIn("no-proof-certs", " ".join(bridge))
        self.assertNotIn("-march=native", clang)
        self.assertIn("--target=aarch64-apple-darwin", clang)
        self.assertNotEqual(runner.SCHEMA, "trust-cg-bench-v2")

    def test_bridge_refusal_keeps_other_lanes_and_all_original_rows(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            tools = {"target": "aarch64-apple-darwin", "clang": "/clang", "dylib": "/backend",
                     "driver": {"compiler": "/trustc", "compiler_flags": ["-Ztrust-verify=off"]}}
            rows = output.empty_accounting(output.load_manifest(HERE))
            commands = []

            def stand_in(command, timeout, env=None):
                commands.append(command)
                if "-o" in command:
                    if any(arg.startswith("-Zcodegen-backend=") for arg in command):
                        return {"status": "EXITED", "returncode": 1, "stdout": b"",
                                "stderr": b"error: [TCG-PROOF-465] production refusal control"}
                    Path(command[command.index("-o") + 1]).write_bytes(b"test-only binary identity")
                    return {"status": "EXITED", "returncode": 0, "stdout": b"", "stderr": b""}
                return {"status": "EXITED", "returncode": 41,
                        "stdout": output.output_bytes("p1_xorshift", (9, 41)), "stderr": b""}

            args = argparse.Namespace(repeat=3, compile_timeout=1, run_timeout=1)
            with mock.patch.object(runner, "capture", side_effect=stand_in), \
                 mock.patch.object(runner, "tools_unchanged", return_value=True):
                runner.check_kernel(HERE, directory, "p1_xorshift", rows["p1_xorshift"], tools, args)
            row = rows["p1_xorshift"]
            self.assertEqual(row["verdict"], "INCOMPLETE")
            self.assertEqual(set(row["lanes"]), set(runner.LANES))
            self.assertEqual(row["lanes"]["bridge"]["compile"]["returncode"], 1)
            self.assertEqual(len(row["lanes"]["llvm"]["runs"]), 3)
            self.assertEqual(len(row["lanes"]["clang"]["runs"]), 3)
            self.assertEqual(output.counts(rows)["original_denominator"], 18)

    def test_observed_state_disagreement_survives_an_incomplete_lane(self):
        for disagreement in ("repeat", "lanes", "partial"):
            with self.subTest(disagreement=disagreement), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                tools = {"target": "aarch64-apple-darwin", "clang": "/clang",
                         "dylib": "/backend", "driver": {"compiler": "/trustc",
                         "compiler_flags": ["-Ztrust-verify=off"]}}
                rows = output.empty_accounting(output.load_manifest(HERE))
                repeats = {"llvm": 0, "clang": 0}

                def observe(command, timeout, env=None):
                    if "-o" in command:
                        if any(arg.startswith("-Zcodegen-backend=") for arg in command):
                            return {"status": "EXITED", "returncode": 1,
                                    "stdout": b"", "stderr": b"backend refusal"}
                        Path(command[command.index("-o") + 1]).write_bytes(b"test-only identity")
                        return {"status": "EXITED", "returncode": 0, "stdout": b"", "stderr": b""}
                    lane = "clang" if str(command[0]).endswith("_clang") else "llvm"
                    repeat = repeats[lane]
                    repeats[lane] += 1
                    if disagreement == "partial" and lane == "llvm" and repeat == 2:
                        return {"status": "TIMEOUT", "returncode": None, "stdout": b"", "stderr": b""}
                    different = ((disagreement == "lanes" and lane == "clang")
                                 or (disagreement != "lanes" and lane == "llvm" and repeat == 1))
                    return {"status": "EXITED", "returncode": 41, "stderr": b"",
                            "stdout": output.output_bytes("p1_xorshift", (10 if different else 9, 41))}

                args = argparse.Namespace(repeat=3, compile_timeout=1, run_timeout=1)
                with mock.patch.object(runner, "capture", side_effect=observe), \
                     mock.patch.object(runner, "tools_unchanged", return_value=True):
                    runner.check_kernel(HERE, directory, "p1_xorshift", rows["p1_xorshift"], tools, args)
                self.assertEqual(rows["p1_xorshift"]["verdict"], "MISMATCH")
                self.assertEqual(rows["p1_xorshift"]["lanes"]["bridge"]["compile"]["returncode"], 1)

    def test_admitted_mismatch_survives_later_artifact_mutation(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            tools = {"target": "aarch64-apple-darwin", "clang": "/clang",
                     "dylib": "/backend", "driver": {"compiler": "/trustc",
                     "compiler_flags": []}}
            row = output.empty_accounting(output.load_manifest(HERE))["p1_xorshift"]
            executions = 0

            def observe(command, timeout, env=None):
                nonlocal executions
                if "-o" in command:
                    Path(command[command.index("-o") + 1]).write_bytes(b"test identity")
                    return {"status": "EXITED", "returncode": 0, "stdout": b"", "stderr": b""}
                executions += 1
                if executions == 3:
                    Path(command[0]).write_bytes(b"changed identity")
                return {"status": "EXITED", "returncode": 41, "stderr": b"",
                        "stdout": output.output_bytes("p1_xorshift", (executions, 41))}

            args = argparse.Namespace(repeat=3, compile_timeout=1, run_timeout=1)
            with mock.patch.object(runner, "capture", side_effect=observe), \
                 mock.patch.object(runner, "tools_unchanged", return_value=True):
                with self.assertRaises(output.OutputError):
                    runner.check_kernel(HERE, directory, "p1_xorshift", row, tools, args)
            self.assertEqual(row["verdict"], "MISMATCH")
            self.assertIn("differ", row["reason"])
            self.assertNotIn("state_hex", row["lanes"]["llvm"]["runs"][2])

    def test_main_preserves_mismatch_when_kernel_check_is_interrupted(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "captures"

            def interrupted(here, directory, stem, row, tools, args):
                row.update(verdict="MISMATCH", reason="admitted output differs")
                raise output.OutputError("later artifact mutation")

            with mock.patch.object(runner, "resolve_tools", return_value={}), \
                 mock.patch.object(runner, "check_kernel", side_effect=interrupted):
                result = runner.main(["--repo", str(HERE.parent.parent), "--clang", "/clang",
                                      "--output-dir", str(directory)])
            report = json.loads((directory / "full-output-results.json").read_text())
            self.assertEqual(result, 1)
            self.assertEqual(report["counts"]["mismatch_count"], 3)
            for stem in output.SUPPORTED:
                self.assertEqual(report["programs"][stem]["reason"], "admitted output differs")
                self.assertEqual(report["programs"][stem]["interruption_reason"],
                                 "later artifact mutation")

    def test_changed_binary_or_validation_source_has_no_observation_credit(self):
        for mutation in ("binary", "compiled_source", "running_source"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                tools = {"target": "aarch64-apple-darwin", "clang": "/clang", "dylib": "/backend",
                         "driver": {"compiler": "/trustc", "compiler_flags": ["-Ztrust-verify=off"]}}
                rows = output.empty_accounting(output.load_manifest(HERE))

                def mutate_identity(command, timeout, env=None):
                    source = directory / "p1_xorshift_validation.rs"
                    if "-o" in command:
                        Path(command[command.index("-o") + 1]).write_bytes(b"original test-only identity")
                        if mutation == "compiled_source":
                            source.write_bytes(source.read_bytes() + b"\n")
                        return {"status": "EXITED", "returncode": 0, "stdout": b"", "stderr": b""}
                    if mutation == "binary":
                        Path(command[0]).write_bytes(b"different test-only identity")
                    else:
                        source.write_bytes(source.read_bytes() + b"\n")
                    return {"status": "EXITED", "returncode": 41,
                            "stdout": output.output_bytes("p1_xorshift", (9, 41)), "stderr": b""}

                args = argparse.Namespace(repeat=3, compile_timeout=1, run_timeout=1)
                with mock.patch.object(runner, "capture", side_effect=mutate_identity), \
                     mock.patch.object(runner, "tools_unchanged", return_value=True):
                    with self.assertRaises(output.OutputError):
                        runner.check_kernel(HERE, directory, "p1_xorshift", rows["p1_xorshift"], tools, args)
                row = rows["p1_xorshift"]
                self.assertEqual(row["verdict"], "INCOMPLETE")
                self.assertEqual(row["lanes"]["llvm"]["status"], "INCOMPLETE")
                self.assertEqual(row["lanes"]["bridge"]["status"], "NOT_RUN")
                self.assertNotIn("state_hex", row["lanes"]["llvm"]["runs"][0]
                                 if row["lanes"]["llvm"]["runs"] else {})


if __name__ == "__main__":
    unittest.main()
