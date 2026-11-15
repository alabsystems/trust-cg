from __future__ import annotations

import ast
import copy
import hashlib
import importlib.util
import json
import os
import re
from pathlib import Path
import signal
import stat
import subprocess
import sys
import shlex
import tempfile
import time
import unittest
from unittest import mock


# The selected interpreter can live below "Application Support". A kernel
# shebang splits such a path; this shell/Python header execs the exact quoted
# interpreter and preserves the fixture argv. Python sees the exec as a string.
PYTHON_FIXTURE_HEADER = (
    "#!/bin/sh\n'''exec' " + shlex.quote(sys.executable) + ' "$0" "$@"\n' + "' '''\n"
)

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check_linux_aarch64_bridge.py"
SPEC = importlib.util.spec_from_file_location("linux_aarch64_bridge_gate", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)
SHA = hashlib.sha256(b"built backend").hexdigest()
# Every required step of a complete run, in order; "xback" is the cross-backend
# ABI runner (a stand-in here that writes a synthetic, verdict-checked report).
FULL_CALLS = ["build", "test-build", "test", "tls-test", "unwind-test", "panic-test", "trap-test", "zst-test",
              "static-test", "heap-test", "coroutine-test", "xback"]
XBACK_TESTS = ROOT / "scripts/tests/test_linux_aarch64_xback.py"

# Orchestration and cancellation fixtures exercise the gate's process control,
# not installed proof-tool discovery, control proofs or executable hashing.
# The resolver's positive and negative controls live in its dedicated tests.
PINNED_PROOF_TOOLS = {
    "ay": {
        "resolved": "/fixture/ay",
        "route": "env-override:AY_SOLVER_PATH",
        "pinned": True,
        "sha256": "1" * 64,
        "bytes": 7,
    },
    "clean": {
        "resolved": "/fixture/clean",
        "route": "env-override:TCG_EXTERNAL_CLEAN_CHECKER",
        "pinned": True,
        "sha256": "2" * 64,
        "bytes": 7,
    },
}


def execution_record():
    # Intentionally independent of the runner's required inventory: deleting a
    # production obligation must not silently delete its positive test control.
    families = {
        "aliased_f32_read": (17, 238), "aliased_f32_write": (17, 238),
        "aliased_f64_read": (17, 238), "aliased_f64_write": (17, 238),
        "local_cell_read": (17, 238), "local_cell_read_f32": (17, 238),
        "projected_cell_result": (17, 357),
        "repeated_cell_f32": (17, 680), "repeated_cell_f64": (17, 680),
        "repeated_cell_u64": (17, 680),
        "branch_loop_cell_f32": (102, 3808), "branch_loop_cell_f64": (102, 3808),
        "zst_sibling_cell": (4001, 4001),
    }
    return {
        "target": GATE.HOST, "opt_levels": [0, 1, 2, 3],
        "executions": 8, "calls": 9728, "checks": 151936,
        "matrix_calls": 9216, "matrix_checks": 149376,
        "mutation_calls": 512, "mutation_checks": 2560, "refusals": 20,
        "projected_cell_controls": 4, "projected_cell_refusals": 0,
        "projected_cell_native_executions": 8, "projected_cell_native_calls": 136,
        "projected_cell_native_checks": 2856, "backend_sha256": SHA,
        "scalar_cell": {
            "schema": 1,
            "native": [
                {"family": family, "compiler": compiler, "opt_level": opt, "calls": calls, "checks": checks}
                for family, (calls, checks) in families.items() for compiler in ("cg", "llvm") for opt in range(4)
            ],
            "unsupported": [
                {"name": name, "opt_level": opt, "cg_refusals": 1, "llvm_objects": 1}
                for name in (
                    "mixed_return", "projected_borrow", "overaligned_cell",
                    "packed_cell", "hfa_middle_borrow",
                )
                for opt in range(4)
            ],
        },
    }


def transcript(marker=None, *, passed=2, ignored=0, filtered=0, skip=""):
    if marker is None:
        marker = GATE.MARKER + json.dumps(execution_record()) + "\n"
    return (
        f"running {passed + ignored} tests\n{skip}{marker}"
        f"test result: ok. {passed} passed; 0 failed; {ignored} ignored; "
        f"0 measured; {filtered} filtered out; finished in 0.01s\n"
    )


def tls_execution_record(model="general-dynamic-tlsdesc"):
    # Independent of the runner's inventory, like execution_record(). Both
    # compilers' objects carry the same access model, as the runner requires.
    sequences = {
        "general-dynamic-tlsdesc": [
            "R_AARCH64_TLSDESC_ADD_LO12", "R_AARCH64_TLSDESC_ADR_PAGE21",
            "R_AARCH64_TLSDESC_CALL", "R_AARCH64_TLSDESC_LD64_LO12",
        ],
        "initial-exec": ["R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21", "R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC"],
        "local-exec": ["R_AARCH64_TLSLE_ADD_TPREL_HI12", "R_AARCH64_TLSLE_ADD_TPREL_LO12_NC"],
    }
    lanes = []
    for opt in range(4):
        lanes.append({
            "compiler": "cg", "opt_level": opt, "runs": 5, "passes": 5, "tls_definers": 1,
            "linked_objects": 2, "excluded_objects": 1, "abort_stubs": 0,
            "tls_relocations": sequences[model], "definition_section": ".tdata",
            "accessor_objects": 1, "access_model": model, "access_sequences": 3,
        })
        lanes.append({
            "compiler": "llvm", "opt_level": opt, "runs": 5, "passes": 5, "tls_definers": 1,
            "linked_objects": 1, "excluded_objects": 0, "abort_stubs": 3 if opt == 0 else 0,
            "tls_relocations": list(sequences[model]),
        })
    return {
        "schema": 1, "target": GATE.HOST, "opt_levels": [0, 1, 2, 3], "runs_per_lane": 5,
        "lanes": lanes,
        "shared_storage_controls": [
            {"compiler": compiler, "opt_level": opt, "exit_code": 3}
            for opt in range(4) for compiler in ("cg", "llvm")
        ],
        "unsupported": [
            {"name": "link_section", "opt_level": opt, "cg_refusals": 1, "cg_item_definitions": 0,
             "cg_leftover_objects": 1, "llvm_objects": 1}
            for opt in range(4)
        ],
        "backend_sha256": SHA,
    }


def tls_transcript(marker=None, **kwargs):
    if marker is None:
        marker = GATE.TLS_MARKER + json.dumps(tls_execution_record()) + "\n"
    return transcript(marker, **kwargs)


def unwind_execution_record():
    # Independent of the runner's inventory, like execution_record().
    fixtures = {
        "box_across_unwind": ("ay_may_unwind", 0, 1),
        "guards_across_unwind": ("ay_unwind_if", 4, 2),
        "nested_unwind": ("guards_across_unwind", 1, 1),
    }
    lanes = []
    for opt in range(4):
        for compiler in ("cg", "llvm"):
            # LLVM removes the never-read boxes above O0 (3 frees per run).
            elided = 3 if compiler == "llvm" and opt > 0 else 0
            row = {
                "compiler": compiler, "opt_level": opt, "runs": 3, "passes": 3, "calls": 15,
                "panics": 9, "caught": 9, "drop_events": 30, "box_frees": (7 - elided) * 3,
                "elided_box_frees": elided,
                "linked_objects": 10 if compiler == "cg" else 1,
                "excluded_objects": 1 if compiler == "cg" else 0,
            }
            if compiler == "cg":
                row.update(eh_functions=3, personality="rust_eh_personality", resume_calls=3)
            lanes.append(row)
    return {
        "schema": 1, "target": GATE.HOST, "opt_levels": [0, 1, 2, 3], "runs_per_lane": 3,
        "mir_cleanup_functions": 3, "lanes": lanes,
        "missing_landing_pad_controls": [
            {"function": function, "callee": callee, "opt_level": opt, "lsda_rows": 3,
             "landing_pad": 64, "mutated_rows": 1, "exit_code": 0, "lost_drops": drops,
             "lost_frees": frees}
            for opt in range(4) for function, (callee, drops, frees) in fixtures.items()
        ],
        "unsupported": [
            {"name": "disable_unwind", "opt_level": opt, "cg_refusals": 1, "refused_functions": 3,
             "fixture_definitions": 0}
            for opt in range(4)
        ],
        "backend_sha256": SHA,
    }


def unwind_transcript(marker=None, **kwargs):
    if marker is None:
        marker = GATE.UNWIND_MARKER + json.dumps(unwind_execution_record()) + "\n"
    return transcript(marker, **kwargs)


def zst_execution_record():
    # Independent counts and inventory: deleting a production obligation must
    # fail these controls rather than shrink their expected native matrix.
    return {
        "schema": 1, "target": "aarch64-unknown-linux-gnu", "comparisons": 8,
        "backend_sha256": SHA, "compiler_sha256": "3" * 64,
        "certificates": "off", "frontend_verify": "off",
        "lanes": [
            {"compiler": compiler, "panic": panic, "opt_level": opt,
             "executions": 1, "driver_checks": 57, "layout_checks": 16, "callback_checks": 10, "address_observations": 40}
            for compiler in ("cg", "llvm") for panic in ("abort", "unwind") for opt in range(4)
        ],
    }


def zst_transcript(record=None, **kwargs):
    if record is None:
        record = zst_execution_record()
    marker = (
        "TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs\n" * 8
        + "TCG_NATIVE_RUNTIME_TEST NativeRun scalar_zst_field_matches_llvm certificates=off frontend_verify=off\n"
        + GATE.ZST_MARKER + json.dumps(record) + "\n"
    )
    return transcript(marker, passed=1, **kwargs)


def model_digest(fixture):
    return hashlib.sha256(f"model of {fixture}".encode()).hexdigest()


def runtime_lanes(table):
    # table: fixture -> (compilers, levels, ending); independent of the runner's.
    return [
        {"fixture": fixture, "compiler": compiler, "opt_level": opt, "runs": 3, "passes": 3,
         "ending": ending, "stdout_sha256": model_digest(fixture)}
        for fixture, (compilers, levels, ending) in table.items()
        for opt in levels for compiler in compilers
    ]


def runtime_record(table, **extra):
    return {
        "schema": 1, "target": GATE.HOST, "opt_levels": [0, 1, 2, 3], "certificates": "off",
        "frontend_verify": "off", "backend_sha256": SHA, "runs_per_lane": 3,
        "lanes": runtime_lanes(table), "model_sha256": {fixture: model_digest(fixture) for fixture in table},
        **extra,
    }


STATIC_TABLE = {
    "immutable": (("cg", "llvm"), range(4), "exit:0"),
    "readonly_store": (("cg", "llvm"), range(4), "signal:11"),
    "mutable": (("cg", "llvm"), range(4), "exit:0"),
    "overaligned": (("cg", "llvm"), range(4), "exit:0"),
    "misaligned_exclusive": (("cg", "llvm"), range(4), "signal:7"),
    "externs": (("cg", "llvm"), range(4), "exit:0"),
    "layout": (("cg", "llvm"), range(4), "exit:0"),
    "out_of_bounds": (("cg", "llvm"), range(4), "signal:6"),
}
STATIC_STORAGE = {
    **{name: "ReadOnly" for name in ("AY_STATIC_N", "AY_STATIC_BYTES", "AY_STATIC_W", "AY_LINE", "AY_PAD_C",
                                     "AY_BIG", "AY_ZERO_CONST", "AY_TARGET", "AY_TABLE")},
    **{name: "Data" for name in ("AY_STATIC_MUT", "AY_PAD_A", "AY_PAD_B", "AY_WIDE_A", "AY_WIDE_B", "AY_WIDE_C")},
    "AY_ZERO_WORDS": "Bss",
    **{name: "Relocated" for name in ("AY_REFS", "AY_GREETING", "AY_PRIMES", "AY_OPS", "AY_SELF_REF")},
}
HEAP_TABLE = {
    "hooked": (("cg",), range(4), "exit:0"),
    "hooked_per_function": (("cg",), range(1), "exit:0"),
    "indirect": (("cg",), range(4), "exit:0"),
    "archive_c1": (("cg", "llvm"), range(4), "exit:0"),
    "archive_c4": (("cg", "llvm"), range(4), "exit:0"),
    "events": (("cg", "llvm"), range(4), "exit:0"),
    "refused": (("llvm",), range(4), "exit:0"),
}
COROUTINE_TABLE = {
    "sequence": (("cg", "llvm"), range(4), "exit:0"),
    "resume_after_complete": (("cg", "llvm"), range(4), "signal:6"),
    "shapes": (("cg", "llvm"), range(4), "exit:0"),
    "refused": (("llvm",), range(4), "exit:0"),
}


def refusal_controls(name, rows):
    return [{"name": name, "opt_level": opt, "cg_refusals": 1, "refusal_rows": rows, "cg_definitions": 0,
             "llvm_runs": 3} for opt in range(4)]


def static_execution_record():
    objects = [{"compiler": compiler, "opt_level": opt, "statics": 21, "pointer_relocations": 12,
                "extern_imports": 2, "abort_stubs": 2, "storage": dict(STATIC_STORAGE)}
               for opt in range(4) for compiler in ("cg", "llvm")]
    return runtime_record(STATIC_TABLE, objects=objects)


def heap_execution_record():
    return runtime_record(
        HEAP_TABLE,
        partitions=[{"opt_level": 0, "batched_objects": 2, "per_function_objects": 14,
                     "per_function_shared_entry_object": False}],
        refusal_controls=refusal_controls("refused_drop_glue", 2),
    )


def coroutine_execution_record():
    return runtime_record(
        COROUTINE_TABLE,
        mir={"coroutine_frame": True, "set_discriminant": True, "yield_terminators": 0},
        refused_lanes=[], refusal_controls=refusal_controls("refused_coroutines", 3),
    )


RUNTIME_KNOBS = {
    "static": ["TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs"] * 20,
    "heap": ["TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs"] * 2
    + ["TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs batch-cgu=0"]
    + ["TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs"] * 22,
    "coroutine": ["TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs"] * 16,
}


def runtime_marker(which):
    return {"static": GATE.STATIC_MARKER, "heap": GATE.HEAP_MARKER, "coroutine": GATE.COROUTINE_MARKER}[which]


def runtime_record_of(which):
    return {"static": static_execution_record, "heap": heap_execution_record,
            "coroutine": coroutine_execution_record}[which]()


def runtime_transcript(which, record=None, *, knobs=None, **kwargs):
    if record is None:
        record = runtime_record_of(which)
    if knobs is None:
        knobs = RUNTIME_KNOBS[which]
    marker = "".join(line + "\n" for line in knobs) + runtime_marker(which) + json.dumps(record) + "\n"
    return transcript(marker, passed=kwargs.pop("passed", 3), **kwargs)


def rust_string_literal(source, prefix, anchor=None):
    """The source text of the ordinary string literal `prefix` opens (it ends in
    the opening quote), as written, searching from `anchor` when given."""
    start = source.index(prefix, source.index(anchor) if anchor else 0) + len(prefix)
    at = start
    while source[at] != '"':
        at += 2 if source[at] == "\\" else 1
    return source[start:at]


def rust_item(source, header):
    """The text of the top-level item that `header` opens, through its closing brace."""
    start = source.index("\n" + header) + 1
    return source[start:source.index("\n}\n", start) + 3]


def literal_value(source, name):
    """The value of a `const NAME: &str = "...";` Rust string literal, as written."""
    prefix = f"const {name}: &str = "
    start = source.index(prefix) + len(prefix)
    return source[start:source.index('";\n', start)]


def extract_literal(source, name):
    """Decode these fixtures' raw strings or ASCII escaped string literals."""
    prefix = f"const {name}: &str = "
    start = source.index(prefix) + len(prefix)
    if source.startswith('r#"', start):
        return source[start + 3:source.index('"#;', start)]
    end = source.index('";\n', start) + 1
    # Rust elides whitespace following an escaped physical newline. Python's
    # literal evaluator alone would retain the next line's indentation.
    literal = re.sub(r"\\\n[ \t\r\n]*", "", source[start:end])
    return ast.literal_eval(literal)


def portable_transcript(name, *, native=4):
    marker = "TCG_DARWIN_BRIDGE_POSITIVE"
    if name == "panic":
        records = [
            ("panic_abort_runs_the_hook_with_the_real_location_like_llvm", "native-run",
             "panic-hook rows: 49/49 matched LLVM"),
            ("panic_hook_observes_preceding_stores_abort_and_unwind_like_llvm", "native-run",
             "PRE_PANIC_EFFECTS matched=24 strategies=abort,unwind opts=0,2,3"),
        ]
    else:
        records = [
            ("range_inclusive_rev_reductions_never_trap_aarch64", "native-run",
             "EXECUTABLE_TRAP_STUB_RANGE refusals=0 llvm_native=6 cg_native=6"),
            ("dead_std_iterator_body_fails_closed_aarch64", "expected-refusal",
             "EXECUTABLE_TRAP_STUB_DEAD_ITER rows=4 llvm_native=4 cg_native=0 cg_refused=4"),
            ("generator_source_take_reductions_never_trap_aarch64", "native-run",
             "EXECUTABLE_TRAP_STUB_GENERATOR_TAKE rows=4 llvm_native=4 cg_native=4 cg_refused=0"),
            ("dyn_heap_glue_drop_fails_closed_aarch64", "native-run" if native else "expected-refusal",
             f"EXECUTABLE_TRAP_STUB_DYN rows=4 llvm_native=4 cg_native={native} cg_refused={4-native}"),
            ("library_trap_stub_reached_by_local_code_fails_closed_aarch64", "expected-refusal",
             "LIBRARY_TRAP_STUB_REACHED refused=4 compiled=5"),
        ]
    lines = [f"running {len(records)} tests", *[f"test {test} ... ok" for test, _, _ in records], "",
             "successes:"]
    for test, kind, summary in records:
        lines += [f"---- {test} stdout ----", "TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs",
                  summary, f"{marker} kind={kind} certs=off test={test}", ""]
    lines += ["successes:", *[f"    {test}" for test, _, _ in records],
              f"test result: ok. {len(records)} passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; "
              "finished in 0.01s"]
    return "\n".join(lines) + "\n"


class LinuxAarch64BridgeGateTests(unittest.TestCase):
    def test_native_target_keeps_build_compiler_binding_and_bounded_artifact_contract(self):
        source = (GATE.MANIFEST.parent / "tests" / f"{GATE.TARGET}.rs").read_text()
        self.assertIn('#[path = "support/toolchain.rs"]', source)
        # A runtime Linux target must not silently choose a second compiler via
        # rustup or PATH after the runner built and hashed its backend.
        for tool in ("rustup", "rustc", "trustc", "cargo", "targo"):
            self.assertNotIn(f'Command::new("{tool}")', source)
        self.assertIn('toolchain_support::rustc_driver_command().arg("-vV")', source)
        # Without the runner pair, the library Cargo built for this test build,
        # hashed; never a nested build into the shared target directory.
        self.assertIn("let path = backend_artifact_support::current_test_backend();", source)
        self.assertNotIn("backend_build_command", source)
        self.assertNotIn("cargo_target_dir", source)
        self.assertEqual(source.count('toolchain_support::rustc_command_with_edition("2024")'), 1)
        # Seven compile sites, each through the edition-bound helper: the four
        # before LA-11, the LA-11 owner and controls tests, and the lane's
        # required zst_sibling_cell positive.
        self.assertEqual(source.count('let mut command = rustc_command();'), 7)
        self.assertNotIn('"--edition=', source)
        helper = (GATE.MANIFEST.parent / "tests/support/toolchain.rs").read_text()
        self.assertIn('rustc_command_with_edition("2021")', helper)
        self.assertIn('cmd.arg(format!("--edition={edition}"));', helper)
        self.assertIn('cmd.arg("-Ztrust-verify=off")', helper)
        self.assertIn('bounded.args(["--kill-after=5", &seconds.to_string()])', source)
        self.assertIn('assert_eq!(actual, expected, "runner\'s fresh backend identity changed")', source)

    def test_tls_target_keeps_the_mandatory_host_backend_binding_and_proof_knob(self):
        self.assertEqual(GATE.REQUIRED_TARGETS, (GATE.TARGET, GATE.TLS_TARGET, GATE.UNWIND_TARGET, GATE.PANIC_TARGET, GATE.TRAP_TARGET, GATE.ZST_TARGET,
                                                 GATE.STATIC_TARGET, GATE.HEAP_TARGET, GATE.COROUTINE_TARGET))
        source = (GATE.MANIFEST.parent / "tests" / f"{GATE.TLS_TARGET}.rs").read_text()
        self.assertIn(
            '#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]', source)
        self.assertIn('#[path = "support/toolchain.rs"]', source)
        for tool in ("rustup", "rustc", "trustc", "cargo", "targo"):
            self.assertNotIn(f'Command::new("{tool}")', source)
        # Mandatory on its host: the only early return is the knob-option skip.
        self.assertNotIn("host_is_", source)
        self.assertNotIn("target_std_available", source)
        self.assertEqual(source.count("return;"), 1)
        self.assertIn('toolchain_support::skip_without_backend_knobs("tls_thread_local_linux")', source)
        self.assertIn('toolchain_support::rustc_driver_command().arg("-vV")', source)
        # Without the runner pair, the library Cargo built for this test build,
        # hashed; never a nested build into the shared target directory.
        self.assertIn("let path = backend_artifact_support::current_test_backend();", source)
        self.assertNotIn("backend_build_command", source)
        self.assertNotIn("cargo_target_dir", source)
        self.assertIn('assert_eq!(actual, expected, "runner\'s fresh backend identity changed")', source)
        # Never a cached library: no candidate list, no debug/release dylib probing.
        self.assertNotIn("candidates", source)
        self.assertNotIn(".dylib", source)
        self.assertEqual(source.count('toolchain_support::backend_knobs_arg(&["no-proof-certs"])'), 1)
        self.assertNotIn('.env("TCG_', source)
        self.assertEqual(source.count("let mut command = rustc_command();"), 1)
        self.assertEqual(source.count("toolchain_support::rustc_command()"), 1)
        self.assertIn('bounded.args(["--kill-after=5", &seconds.to_string()])', source)
        for field in ("TLS_MARKER", "MARKER", "UNWIND_MARKER"):
            self.assertTrue(getattr(GATE, field).endswith(" "))
        # trustc refuses every TCG_* variable; the runner's test-only backend
        # pair must not reach any compiler child (the knob-option probe, the
        # sysroot query, every compile), or the target would skip or fail.
        # Every child starts from rustc_driver_command, which drops the pair.
        helper = (GATE.MANIFEST.parent / "tests/support/toolchain.rs").read_text()
        self.assertIn('pub const RUNNER_TEST_ONLY_ENV: [&str; 2] = '
                      '["TCG_TEST_BACKEND_PATH", "TCG_TEST_BACKEND_SHA256"];', helper)
        driver = helper[helper.index("pub fn rustc_driver_command"):]
        driver = driver[:driver.index("\n}\n")]
        self.assertIn("let mut command = Command::new(BUILD_COMPILER);", driver)
        self.assertIn("for name in RUNNER_TEST_ONLY_ENV {\n        command.env_remove(name);", driver)
        self.assertEqual(helper.count("Command::new(BUILD_COMPILER)"), 1)
        probe = helper[helper.index("pub fn backend_knobs_supported"):]
        probe = probe[:probe.index("\n}\n")]
        self.assertIn('rustc_driver_command().arg("-Zhelp")', probe)
        for name in ("rustc_command_with_edition", "target_std_available"):
            body = helper[helper.index(f"pub fn {name}"):]
            self.assertIn("rustc_driver_command()", body[:body.index("\n}\n")])
        self.assertIn(f'"\\n{GATE.TLS_MARKER}{{{{', source)

    def test_tls_target_keeps_the_darwin_crate_and_driver(self):
        linux = (GATE.MANIFEST.parent / "tests" / f"{GATE.TLS_TARGET}.rs").read_text()
        darwin = (GATE.MANIFEST.parent / "tests" / "tls_thread_local_aarch64.rs").read_text()
        # Darwin exercises cross-object TLS with a descriptor and an accessor
        # crate. Linux exercises the same definition and function bodies in one
        # crate. Remove only the accessor's duplicate header and explicit import
        # before comparing every guest line. Only indentation is ignored;
        # the quoted literals are pinned independently below.
        descriptor = extract_literal(darwin, "TLS_DESCRIPTOR_CRATE").strip("\n")
        accessor = extract_literal(darwin, "TLS_ACCESSOR_CRATE").lstrip("\n")
        accessor_prefix = ('#![crate_type = "staticlib"]\n#![feature(thread_local)]\n\n'
                           'unsafe extern "C" {\n    #[thread_local]\n    static mut X: i32;\n}\n\n')
        self.assertTrue(accessor.startswith(accessor_prefix), accessor)
        combined = descriptor + "\n\n" + accessor[len(accessor_prefix):]
        def guest_lines(text):
            # These guests contain only the crate type and two C ABI strings.
            # Pin them so ignoring source indentation cannot hide changed data
            # inside a future multiline Rust string literal.
            self.assertEqual(re.findall(r'"[^"]*"', text),
                             ['"staticlib"', '"C"', '"C"'])
            return [line.lstrip(" \t") for line in text.splitlines()]
        self.assertEqual(guest_lines(extract_literal(linux, "TLS_CRATE")), guest_lines(combined))
        self.assertEqual(extract_literal(linux, "DRIVER"), extract_literal(darwin, "DRIVER"))
        self.assertIn("tls_thread_local_linux.rs", darwin)

    def test_unwind_target_keeps_the_mandatory_host_backend_binding_and_proof_knobs(self):
        source = (GATE.MANIFEST.parent / "tests" / f"{GATE.UNWIND_TARGET}.rs").read_text()
        self.assertIn(
            '#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]', source)
        self.assertIn('#[path = "support/toolchain.rs"]', source)
        for tool in ("rustup", "rustc", "trustc", "cargo", "targo"):
            self.assertNotIn(f'Command::new("{tool}")', source)
        # Mandatory on its host: the only early return is the knob-option skip.
        self.assertNotIn("host_is_", source)
        self.assertNotIn("target_std_available", source)
        self.assertEqual(source.count("return;"), 1)
        self.assertIn('toolchain_support::skip_without_backend_knobs("unwind_cleanup_linux")', source)
        self.assertIn('toolchain_support::rustc_driver_command().arg("-vV")', source)
        # Without the runner pair, the library Cargo built for this test build,
        # hashed; never a nested build into the shared target directory.
        self.assertIn("let path = backend_artifact_support::current_test_backend();", source)
        self.assertNotIn("backend_build_command", source)
        self.assertNotIn("cargo_target_dir", source)
        self.assertIn('assert_eq!(actual, expected, "runner\'s fresh backend identity changed")', source)
        self.assertNotIn("candidates", source)
        self.assertNotIn(".dylib", source)
        # Every bridge compile passes the proof knob through the one tracked
        # option; only the refusal control adds the `disable-unwind` opt-out.
        self.assertEqual(source.count("toolchain_support::backend_knobs_arg("), 1)
        self.assertIn("command.arg(toolchain_support::backend_knobs_arg(knobs));", source)
        self.assertEqual(source.count('let knobs: &[&str] = &["no-proof-certs"];'), 1)
        self.assertEqual(source.count('let knobs: &[&str] = &["no-proof-certs", "disable-unwind"];'), 1)
        self.assertNotIn('.env("TCG_', source)
        self.assertEqual(source.count("let mut command = rustc_command();"), 1)
        self.assertEqual(source.count("toolchain_support::rustc_command()"), 1)
        self.assertIn('bounded.args(["--kill-after=5", &seconds.to_string()])', source)
        self.assertIn(f'"\\n{GATE.UNWIND_MARKER}{{{{', source)
        # A passing run removes its artifacts unless explicitly retained.
        self.assertIn(
            'std::fs::remove_dir_all(&artifacts).expect("remove the artifacts of a passing run")', source)
        self.assertIn('const KEEP_ARTIFACTS: &str = "UNWIND_CLEANUP_LINUX_KEEP_ARTIFACTS";', source)
        # The fixture inventory the runner requires is the one the test runs.
        for function, (callee, _, _) in GATE.UNWIND_FIXTURES.items():
            self.assertIn(f'("{function}", "{callee}")', source)

    def test_unwind_target_keeps_the_darwin_crates(self):
        linux = (GATE.MANIFEST.parent / "tests" / f"{GATE.UNWIND_TARGET}.rs").read_text()
        darwin = (GATE.MANIFEST.parent / "tests" / "unwind_cleanup_aarch64.rs").read_text()
        for linux_name, darwin_name in (("DARWIN_UNWIND_CRATE", "UNWIND_CRATE"),
                                        ("DARWIN_PANICKER_CRATE", "PANICKER_CRATE")):
            with self.subTest(name=darwin_name):
                self.assertEqual(literal_value(linux, linux_name), literal_value(darwin, darwin_name))
        self.assertIn('format!("{DARWIN_UNWIND_CRATE}{UNWIND_EXTENSION}")', linux)
        self.assertIn('format!("{DARWIN_PANICKER_CRATE}{PANICKER_EXTENSION}")', linux)
        self.assertIn("unwind_cleanup_linux.rs", darwin)

    def test_runtime_twin_targets_keep_the_mandatory_host_backend_binding_and_proof_knob(self):
        tests = GATE.MANIFEST.parent / "tests"
        harness = (tests / "support/linux_runtime_twin.rs").read_text()
        for target, marker in ((GATE.STATIC_TARGET, GATE.STATIC_MARKER), (GATE.HEAP_TARGET, GATE.HEAP_MARKER),
                               (GATE.COROUTINE_TARGET, GATE.COROUTINE_MARKER)):
            with self.subTest(target=target):
                source = (tests / f"{target}.rs").read_text()
                self.assertIn(
                    '#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]', source)
                self.assertIn('#[path = "support/linux_runtime_twin.rs"]\nmod twin;', source)
                for tool in ("rustup", "rustc", "trustc", "cargo", "targo"):
                    self.assertNotIn(f'Command::new("{tool}")', source)
                # Mandatory on its host: a missing prerequisite FAILS, never skips.
                self.assertIn(f'twin::require_knobs("{target}");', source)
                self.assertNotIn("skip_without_backend_knobs", source)
                self.assertNotIn("host_is_", source)
                self.assertNotIn("target_std_available", source)
                self.assertEqual(source.count("return;"), 0)
                self.assertIn("twin::require_host(&root);", source)
                self.assertIn("let (backend, digest) = twin::backend();", source)
                self.assertNotIn('.env("TCG_', source)
                self.assertNotIn("toolchain_support::rustc_command()", source)
                self.assertNotIn("backend_knobs_arg", source)
                self.assertIn(f'const MARKER: &str = "{marker.strip()}";', source)
                self.assertIn("twin::print_marker(", source)
                self.assertIn("artifacts.finish();", source)
                # Its own Darwin original points back at it.
                darwin = target.replace("_linux", "_aarch64")
                self.assertIn(f"{target}.rs", (tests / f"{darwin}.rs").read_text())
        # The one harness: fail-not-skip knob check, the runner's exact
        # backend binding, the shared compiler constructor, and the knob trace.
        knobs = harness[harness.index("pub fn require_knobs"):]
        knobs = knobs[:knobs.index("\n}\n")]
        self.assertIn("toolchain_support::backend_knobs_supported()", knobs)
        self.assertIn("assert!(", knobs)
        self.assertNotIn("return", knobs)
        self.assertIn("let path = backend_artifact_support::current_test_backend();", harness)
        self.assertIn('assert_eq!(actual, expected, "runner\'s fresh backend identity changed")', harness)
        self.assertIn('pub const NO_PROOF_CERTS: &[&str] = &["no-proof-certs"];', harness)
        self.assertEqual(harness.count("toolchain_support::backend_knobs_arg("), 1)
        self.assertEqual(harness.count("toolchain_support::rustc_command()"), 1)
        self.assertIn('bounded.args(["--kill-after=5", &seconds.to_string()])', harness)
        self.assertIn('object.insert("certificates".into(), serde_json::json!("off"));', harness)
        self.assertIn('object.insert("frontend_verify".into(), serde_json::json!("off"));', harness)
        # The only other knob any twin passes: the per-function partition.
        heap = (tests / f"{GATE.HEAP_TARGET}.rs").read_text()
        self.assertEqual(heap.count('knobs: &["no-proof-certs", "batch-cgu=0"]'), 1)
        for target in (GATE.STATIC_TARGET, GATE.COROUTINE_TARGET):
            self.assertNotIn("knobs: &[", (tests / f"{target}.rs").read_text())

    def test_runtime_twins_keep_the_darwin_crates_and_drivers(self):
        tests = GATE.MANIFEST.parent / "tests"
        static_linux = (tests / f"{GATE.STATIC_TARGET}.rs").read_text()
        static_darwin = (tests / "static_data_aarch64.rs").read_text()
        heap_linux = (tests / f"{GATE.HEAP_TARGET}.rs").read_text()
        heap_darwin = (tests / "drop_heap_aarch64.rs").read_text()
        coroutine_linux = (tests / f"{GATE.COROUTINE_TARGET}.rs").read_text()
        coroutine_darwin = (tests / "coroutine_generator_aarch64.rs").read_text()
        mutable = "fn mutable_static_is_shared_writable_and_link_runs_aarch64("
        aligned = "fn over_aligned_statics_land_aligned_and_survive_a_16_byte_atomic_aarch64("
        externs = "fn statics_pointing_at_extern_statics_link_and_run_aarch64("
        indirect = "fn address_taken_box_new_links_runs_without_reachable_trap_aarch64("
        for linux, name, darwin, anchor, prefix in (
            (static_linux, "STATIC_CRATE", static_darwin, None, 'const STATIC_CRATE: &str = "'),
            (static_linux, "DRIVER_C", static_darwin, None, 'const DRIVER_C: &str = "'),
            (static_linux, "MUTABLE_CRATE", static_darwin, mutable, 'let src = "'),
            (static_linux, "MUTABLE_DRIVER", static_darwin, mutable, 'let driver = "'),
            (static_linux, "OVERALIGNED_CRATE", static_darwin, aligned, 'const SRC: &str = "'),
            (static_linux, "OVERALIGNED_DRIVER", static_darwin, aligned, 'const DRIVER: &str = "'),
            (static_linux, "EXTERN_CRATE", static_darwin, externs, 'let src = "'),
            (static_linux, "EXTERN_DRIVER", static_darwin, externs, 'let driver = "'),
            (heap_linux, "DROP_CRATE", heap_darwin, None, 'const DROP_CRATE: &str = "'),
            (heap_linux, "INDIRECT_CRATE", heap_darwin, indirect, 'let src = "'),
            (heap_linux, "ARCHIVE_DRIVER", heap_darwin, None, 'const ARCHIVE_DRIVER: &str = "'),
            (coroutine_linux, "GEN_CRATE", coroutine_darwin, None, 'const GEN_CRATE: &str = "'),
            (coroutine_linux, "DRIVER_C", coroutine_darwin, None, 'const DRIVER_C: &str = "'),
        ):
            with self.subTest(name=name):
                self.assertEqual(rust_string_literal(linux, f'const {name}: &str = "'),
                                 rust_string_literal(darwin, prefix, anchor))
        # The hooked drivers are the Darwin builders, verbatim.
        for header in ("struct RdlSymbols {", "fn alloc_error_handler_definition(", "fn build_driver(",
                       "fn build_indirect_box_driver("):
            with self.subTest(item=header):
                self.assertEqual(rust_item(heap_linux, header), rust_item(heap_darwin, header))

    def test_pin_requires_exactly_trust(self):
        with tempfile.TemporaryDirectory() as temp:
            pin = Path(temp) / "rust-toolchain.toml"
            for channel in ("stable", "nightly", "nightly-2026-04-20", "1.97.1", "trust; true"):
                pin.write_text(f'[toolchain]\nchannel = "{channel}"\n')
                with self.subTest(channel=channel), self.assertRaises(ValueError):
                    GATE.pinned_toolchain(pin)
            pin.write_text('[toolchain]\nchannel = "trust"\n')
            self.assertEqual(GATE.pinned_toolchain(pin), "trust")

    def test_trust_lane_uses_branded_tools_and_preserves_artifact_rejections(self):
        code, report, calls, _ = self.fixture_run(channel="trust")
        self.assertEqual(code, 0, report)
        self.assertEqual(calls, FULL_CALLS)
        for mode in ("buildfail", "missing_artifact", "changed_snapshot", "missing_marker"):
            with self.subTest(mode=mode):
                code, report, _, _ = self.fixture_run(mode, channel="trust")
                self.assertEqual(code, 1, report)
                self.assertEqual(report["status"], "fail")

    def test_trust_preflight_binds_installed_pair_identity_and_private_components(self):
        with tempfile.TemporaryDirectory() as temp:
            package = Path(temp).resolve()
            target_lib = package / "lib/rustlib" / GATE.HOST / "lib"
            bindir = package / "bin"
            bindir.mkdir()
            for name in ("trustc", "targo"):
                (bindir / name).write_text("fixture executable")
                (bindir / name).chmod(0o755)
            paths = {name: str(bindir / name) for name in ("trustc", "targo")}
            calls = []
            binary, sysroot = "trustc", str(package)
            def probe(command):
                calls.append(command)
                self.assertNotIn("rustup", " ".join(command))
                if command[-1] == "-vV":
                    return f"rustc 1.99.0-dev (trustc)\nbinary: {binary}\ncommit-hash: {'a' * 40}\nhost: {GATE.HOST}\n"
                if command[-2:] == ["--print", "sysroot"]:
                    return sysroot
                return "fixture version"
            with mock.patch.object(GATE, "pinned_toolchain", return_value="trust"), \
                    mock.patch.object(GATE.sys, "platform", "linux"), \
                    mock.patch.object(GATE.shutil, "which", side_effect=lambda name: paths.get(name, f"/fixture/{name}")), \
                    mock.patch.object(GATE.SHARED, "probe", side_effect=probe), \
                    mock.patch.object(GATE.SHARED, "source_provenance", return_value={}), \
                    mock.patch.dict(os.environ, {}, clear=True):
                with self.assertRaisesRegex(RuntimeError, "lacks native target libraries"):
                    GATE.preflight(package / "cache")
                target_lib.mkdir(parents=True)
                with self.assertRaisesRegex(RuntimeError, "private crate missing"):
                    GATE.preflight(package / "cache")
                for name in ("rustc_middle", "rustc_codegen_ssa"):
                    (target_lib / f"lib{name}-fixture.rlib").touch()
                provenance = GATE.preflight(package / "cache")
                self.assertEqual(provenance["compiler_path"], str(bindir / "trustc"))
                self.assertEqual(provenance["compiler_commit"], "a" * 40)
                self.assertEqual(provenance["sysroot"], str(package))
                self.assertEqual(provenance["compiler_command"], [str(bindir / "trustc")])
                self.assertEqual(provenance["build_command"], [str(bindir / "targo"), "--unverified"])
                self.assertEqual(provenance["lane"], "unverified")
                self.assertIsNone(provenance["installed_components"])
                self.assertFalse(any("component" in command for command in calls))
                binary = "rustc"
                with self.assertRaisesRegex(RuntimeError, "branded trustc"):
                    GATE.preflight(package / "cache")
                binary = "trustc"
                paths["targo"] = None
                with self.assertRaisesRegex(RuntimeError, "required tool is missing: targo"):
                    GATE.preflight(package / "cache")
                paths["targo"] = str(package / "other/targo")
                Path(paths["targo"]).parent.mkdir()
                Path(paths["targo"]).write_text("other pack")
                Path(paths["targo"]).chmod(0o755)
                with self.assertRaisesRegex(RuntimeError, "same installed package"):
                    GATE.preflight(package / "cache")
                paths["targo"] = str(bindir / "targo")
                sysroot = str(package / "other")
                with self.assertRaisesRegex(RuntimeError, "compiler/sysroot package mismatch"):
                    GATE.preflight(package / "cache")

    def test_native_marker_is_bound_nonempty_and_covers_all_optimization_levels(self):
        self.assertEqual(GATE.classify_native(0, transcript(), SHA)["status"], "pass")
        good = json.loads(transcript().splitlines()[1][len(GATE.MARKER):])
        cases = ["", GATE.MARKER + "not json\n", GATE.MARKER + "[]\n"]
        for key, value in (
            ("target", "aarch64-apple-darwin"), ("opt_levels", [0, 3]),
            ("opt_levels", [False, True, 2, 3]), ("opt_levels", [0.0, 1, 2, 3]),
            ("executions", 0), ("executions", 7), ("checks", 0), ("executions", True),
            ("calls", 0), ("calls", True), ("calls", 1.5),
            ("refusals", 0), ("refusals", 16), ("refusals", 24), ("refusals", 32), ("refusals", True),
            ("refusals", 20.0),
            ("projected_cell_controls", 3), ("projected_cell_controls", True), ("projected_cell_controls", 4.0),
            ("projected_cell_refusals", 4), ("projected_cell_refusals", False),
            ("projected_cell_native_executions", 4), ("projected_cell_native_calls", 7),
            ("projected_cell_native_checks", 39),
            ("matrix_calls", 9215), ("matrix_checks", 149375),
            ("mutation_calls", 511), ("mutation_checks", 2559),
            ("calls", 9729), ("checks", 151937),
            ("checks", 1.5), ("backend_sha256", "0" * 64),
        ):
            cases.append(GATE.MARKER + json.dumps({**good, key: value}) + "\n")
        cases.append((GATE.MARKER + json.dumps(good) + "\n") * 2)
        for marker in cases:
            with self.subTest(marker=marker):
                self.assertEqual(GATE.classify_native(0, transcript(marker), SHA)["status"], "fail")
        for text in (transcript(passed=0), transcript(ignored=1), transcript(filtered=1), transcript(skip="SKIP native\n")):
            self.assertEqual(GATE.classify_native(0, text, SHA)["status"], "fail")
        self.assertEqual(GATE.classify_native(7, transcript(), SHA)["status"], "fail")

    def test_scalar_cell_schema_requires_every_named_native_family_and_twin_tier(self):
        good = execution_record()
        self.assertEqual(len(good["scalar_cell"]["native"]), 104)
        cases = []
        for value in (None, [], {}, {"schema": True}, {"schema": 1.0}, {"schema": 0}):
            cases.append({**good, "scalar_cell": value})
        for field in ("native", "unsupported"):
            for value in (None, {}, [], [None]):
                mutated = copy.deepcopy(good)
                mutated["scalar_cell"][field] = value
                cases.append(mutated)
        for family in {row["family"] for row in good["scalar_cell"]["native"]}:
            mutated = copy.deepcopy(good)
            mutated["scalar_cell"]["native"] = [
                row for row in mutated["scalar_cell"]["native"] if row["family"] != family
            ]
            cases.append(mutated)
        for compiler in ("cg", "llvm"):
            for opt in range(4):
                mutated = copy.deepcopy(good)
                mutated["scalar_cell"]["native"] = [
                    row for row in mutated["scalar_cell"]["native"]
                    if (row["compiler"], row["opt_level"]) != (compiler, opt)
                ]
                cases.append(mutated)
        for key, value in (
            ("family", "unknown_cell"), ("family", []), ("compiler", "clang"), ("compiler", True),
            ("opt_level", True), ("opt_level", 0.0), ("opt_level", "0"), ("opt_level", 4),
            ("calls", 0), ("calls", True), ("calls", 1.0),
            ("checks", 0), ("checks", True), ("checks", 5.0), ("refusals", 1),
        ):
            mutated = copy.deepcopy(good)
            mutated["scalar_cell"]["native"][0][key] = value
            cases.append(mutated)
        duplicate = copy.deepcopy(good)
        duplicate["scalar_cell"]["native"][1] = duplicate["scalar_cell"]["native"][0].copy()
        cases.append(duplicate)
        extra = copy.deepcopy(good)
        extra["scalar_cell"]["native"].append(extra["scalar_cell"]["native"][0].copy())
        cases.append(extra)
        for index, execution in enumerate(cases):
            with self.subTest(case=index):
                marker = GATE.MARKER + json.dumps(execution) + "\n"
                self.assertEqual(GATE.classify_native(0, transcript(marker), SHA)["status"], "fail")

    def test_scalar_cell_retained_refusals_require_exact_names_tiers_and_llvm_controls(self):
        good = execution_record()
        cases = []
        self.assertEqual(len(good["scalar_cell"]["unsupported"]), 20)
        for index in range(20):
            mutated = copy.deepcopy(good)
            mutated["scalar_cell"]["unsupported"].pop(index)
            cases.append(mutated)
        for key, value in (
            ("name", "aliased_f32_read"), ("name", "zst_sibling_cell"), ("name", []), ("opt_level", True),
            ("opt_level", 0.0), ("opt_level", "0"), ("opt_level", 4),
            ("cg_refusals", 0), ("cg_refusals", 2), ("cg_refusals", True), ("cg_refusals", 1.0),
            ("llvm_objects", 0), ("llvm_objects", 2), ("llvm_objects", True), ("llvm_objects", 1.0),
        ):
            mutated = copy.deepcopy(good)
            mutated["scalar_cell"]["unsupported"][0][key] = value
            cases.append(mutated)
        duplicate = copy.deepcopy(good)
        duplicate["scalar_cell"]["unsupported"][1] = duplicate["scalar_cell"]["unsupported"][0].copy()
        cases.append(duplicate)
        extra = copy.deepcopy(good)
        extra["scalar_cell"]["unsupported"].append(extra["scalar_cell"]["unsupported"][0].copy())
        cases.append(extra)
        for index, execution in enumerate(cases):
            with self.subTest(case=index):
                marker = GATE.MARKER + json.dumps(execution) + "\n"
                self.assertEqual(GATE.classify_native(0, transcript(marker), SHA)["status"], "fail")

    def test_zst_sibling_cell_is_a_required_native_positive_not_a_refusal(self):
        # Ruling LD-93 (b): the pre-ruling marker,
        # with zst_sibling_cell as a retained refusal and no native lanes, fails.
        old = execution_record()
        old["scalar_cell"]["native"] = [
            row for row in old["scalar_cell"]["native"] if row["family"] != "zst_sibling_cell"
        ]
        old["scalar_cell"]["unsupported"] += [
            {"name": "zst_sibling_cell", "opt_level": opt, "cg_refusals": 1, "llvm_objects": 1}
            for opt in range(4)
        ]
        old["refusals"] = 24
        verdict = GATE.classify_native(0, transcript(GATE.MARKER + json.dumps(old) + "\n"), SHA)
        self.assertEqual(verdict["status"], "fail")
        errors = "\n".join(verdict["errors"])
        self.assertIn("missing required scalar-cell native lanes", errors)
        self.assertIn("unexpected or duplicate scalar-cell unsupported control: ('zst_sibling_cell', 0)", errors)
        for opt in range(4):
            for compiler in ("cg", "llvm"):
                with self.subTest(compiler=compiler, opt=opt):
                    mutated = execution_record()
                    mutated["scalar_cell"]["native"] = [
                        row for row in mutated["scalar_cell"]["native"]
                        if (row["family"], row["compiler"], row["opt_level"]) != ("zst_sibling_cell", compiler, opt)
                    ]
                    marker = GATE.MARKER + json.dumps(mutated) + "\n"
                    self.assertEqual(GATE.classify_native(0, transcript(marker), SHA)["status"], "fail")

    def test_scalar_cell_counter_shrinking_cannot_launder_named_native_coverage(self):
        good = execution_record()
        native = good["scalar_cell"]["native"]
        self.assertEqual(sum(row["calls"] for row in native), 35000)
        self.assertEqual(sum(row["checks"] for row in native), 123536)
        # Every family, compiler and tier must retain each independent floor.
        # Keep the projected summary self-consistent so it cannot be the reason
        # these otherwise complete, positive-count native markers are rejected.
        for index, row in enumerate(native):
            for counter in ("calls", "checks"):
                with self.subTest(family=row["family"], compiler=row["compiler"], opt=row["opt_level"], counter=counter):
                    mutated = copy.deepcopy(good)
                    mutated["scalar_cell"]["native"][index][counter] -= 1
                    if row["family"] == "projected_cell_result":
                        mutated[f"projected_cell_native_{counter}"] -= 1
                    marker = GATE.MARKER + json.dumps(mutated) + "\n"
                    verdict = GATE.classify_native(0, transcript(marker), SHA)
                    self.assertEqual(verdict["status"], "fail")
                    self.assertTrue(any(f"{counter} floor" in error for error in verdict["errors"]), verdict)
        expanded = copy.deepcopy(good)
        for row in expanded["scalar_cell"]["native"]:
            row["calls"] += 1
            row["checks"] += 1
        expanded["projected_cell_native_calls"] += 8
        expanded["projected_cell_native_checks"] += 8
        marker = GATE.MARKER + json.dumps(expanded) + "\n"
        self.assertEqual(GATE.classify_native(0, transcript(marker), SHA)["status"], "pass")

    def test_tls_marker_requires_every_lane_control_and_refusal(self):
        good = tls_execution_record()
        self.assertEqual(GATE.classify_tls_native(0, tls_transcript(), SHA)["status"], "pass")
        for model in ("initial-exec", "local-exec"):
            other = GATE.TLS_MARKER + json.dumps(tls_execution_record(model)) + "\n"
            self.assertEqual(GATE.classify_tls_native(0, tls_transcript(other), SHA)["status"], "pass")
        # The CG objects must use the LLVM twin's access model at every level.
        for opt in range(4):
            diverged = copy.deepcopy(good)
            initial = tls_execution_record("initial-exec")
            diverged["lanes"][2 * opt] = initial["lanes"][2 * opt]
            marker = GATE.TLS_MARKER + json.dumps(diverged) + "\n"
            verdict = GATE.classify_tls_native(0, tls_transcript(marker), SHA)
            self.assertEqual(verdict["status"], "fail")
            self.assertIn(f"CG TLS relocations must match the LLVM twin's access model: O{opt}",
                          verdict["errors"])
        expanded = copy.deepcopy(good)
        expanded["runs_per_lane"] = 6
        for row in expanded["lanes"]:
            row["runs"] = row["passes"] = 6
        marker = GATE.TLS_MARKER + json.dumps(expanded) + "\n"
        self.assertEqual(GATE.classify_tls_native(0, tls_transcript(marker), SHA)["status"], "pass")

        cases = []
        for key, value in (
            ("schema", 0), ("schema", True), ("schema", 1.0), ("target", "aarch64-apple-darwin"),
            ("opt_levels", [0, 3]), ("opt_levels", [False, True, 2, 3]), ("runs_per_lane", 4),
            ("runs_per_lane", True), ("backend_sha256", "0" * 64), ("lanes", None),
            ("shared_storage_controls", {}), ("unsupported", None),
        ):
            cases.append({**good, key: value})
        for field in ("lanes", "shared_storage_controls", "unsupported"):
            for index in range(len(good[field])):
                mutated = copy.deepcopy(good)
                mutated[field].pop(index)
                cases.append(mutated)
            duplicate = copy.deepcopy(good)
            duplicate[field].append(copy.deepcopy(duplicate[field][0]))
            cases.append(duplicate)
        cg, llvm = 0, 1
        for index, key, value in (
            (cg, "runs", 4), (cg, "passes", 4), (cg, "runs", True), (cg, "tls_definers", 0),
            (cg, "tls_definers", 2), (cg, "linked_objects", 0), (cg, "abort_stubs", -1),
            (cg, "access_model", "general-dynamic"), (cg, "access_model", None),
            (cg, "access_model", "local-exec"), (cg, "tls_relocations", []),
            (cg, "tls_relocations", tls_execution_record("initial-exec")["lanes"][cg]["tls_relocations"]),
            (cg, "tls_relocations", good["lanes"][cg]["tls_relocations"][:1]),
            (cg, "tls_relocations", [*good["lanes"][cg]["tls_relocations"], "R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21"]),
            (cg, "definition_section", ".data"), (cg, "accessor_objects", 0),
            (cg, "access_sequences", 1), (cg, "access_sequences", True),
            (llvm, "tls_relocations", tls_execution_record("local-exec")["lanes"][llvm]["tls_relocations"]),
            (cg, "compiler", "clang"), (cg, "opt_level", 4), (cg, "opt_level", 0.0),
            (llvm, "runs", 4), (llvm, "passes", 0), (llvm, "tls_definers", 0),
            (llvm, "tls_relocations", []), (llvm, "tls_relocations", ["abs"]),
            (llvm, "access_model", "initial-exec"),
        ):
            mutated = copy.deepcopy(good)
            mutated["lanes"][index][key] = value
            cases.append(mutated)
        for index, key in ((cg, "definition_section"), (llvm, "abort_stubs")):
            mutated = copy.deepcopy(good)
            del mutated["lanes"][index][key]
            cases.append(mutated)
        for key, value in (("exit_code", 0), ("exit_code", 4), ("exit_code", True),
                           ("compiler", "gcc"), ("opt_level", 4)):
            mutated = copy.deepcopy(good)
            mutated["shared_storage_controls"][0][key] = value
            cases.append(mutated)
        for key, value in (("cg_refusals", 0), ("cg_refusals", True), ("cg_item_definitions", 1),
                           ("llvm_objects", 0), ("cg_leftover_objects", -1), ("name", "other"),
                           ("opt_level", 4)):
            mutated = copy.deepcopy(good)
            mutated["unsupported"][0][key] = value
            cases.append(mutated)
        for index, execution in enumerate(cases):
            with self.subTest(case=index):
                marker = GATE.TLS_MARKER + json.dumps(execution) + "\n"
                self.assertEqual(GATE.classify_tls_native(0, tls_transcript(marker), SHA)["status"], "fail")
        for text in ("", GATE.TLS_MARKER + "not json\n", GATE.TLS_MARKER + "[]\n",
                     (GATE.TLS_MARKER + json.dumps(good) + "\n") * 2,
                     GATE.MARKER + json.dumps(good) + "\n"):
            with self.subTest(marker=text[:40]):
                self.assertEqual(GATE.classify_tls_native(0, tls_transcript(text), SHA)["status"], "fail")
        for text in (tls_transcript(passed=0), tls_transcript(ignored=1), tls_transcript(filtered=1),
                     tls_transcript(skip="skipped: no ELF TLS\n")):
            self.assertEqual(GATE.classify_tls_native(0, text, SHA)["status"], "fail")
        self.assertEqual(GATE.classify_tls_native(101, tls_transcript(), SHA)["status"], "fail")
        # Neither marker satisfies the other target's classifier.
        self.assertEqual(GATE.classify_native(0, tls_transcript(), SHA)["status"], "fail")

    def test_unwind_marker_requires_every_lane_control_and_refusal(self):
        good = unwind_execution_record()
        self.assertEqual(GATE.classify_unwind_native(0, unwind_transcript(), SHA)["status"], "pass")
        expanded = copy.deepcopy(good)
        expanded["runs_per_lane"] = 4
        for row in expanded["lanes"]:
            row["runs"] = row["passes"] = 4
            for name, per_run in (("calls", 5), ("panics", 3), ("caught", 3), ("drop_events", 10),
                                  ("box_frees", 7 - row["elided_box_frees"])):
                row[name] = per_run * 4
        marker = GATE.UNWIND_MARKER + json.dumps(expanded) + "\n"
        self.assertEqual(GATE.classify_unwind_native(0, unwind_transcript(marker), SHA)["status"], "pass")

        cases = []
        for key, value in (
            ("schema", 0), ("schema", True), ("target", "aarch64-apple-darwin"), ("opt_levels", [0, 3]),
            ("opt_levels", [False, True, 2, 3]), ("runs_per_lane", 2), ("runs_per_lane", True),
            ("backend_sha256", "0" * 64), ("mir_cleanup_functions", 2), ("mir_cleanup_functions", True),
            ("lanes", None), ("missing_landing_pad_controls", {}), ("unsupported", None),
        ):
            cases.append({**good, key: value})
        for field in ("lanes", "missing_landing_pad_controls", "unsupported"):
            for index in range(len(good[field])):
                mutated = copy.deepcopy(good)
                mutated[field].pop(index)
                cases.append(mutated)
            duplicate = copy.deepcopy(good)
            duplicate[field].append(copy.deepcopy(duplicate[field][0]))
            cases.append(duplicate)
        cg, llvm = 0, 1
        for index, key, value in (
            (cg, "runs", 2), (cg, "passes", 2), (cg, "runs", True), (cg, "calls", 14), (cg, "panics", 8),
            (cg, "caught", 6), (cg, "drop_events", 27), (cg, "box_frees", 18), (cg, "calls", 15.0),
            (cg, "linked_objects", 0), (cg, "excluded_objects", 2), (cg, "eh_functions", 2),
            (cg, "personality", "__gxx_personality_v0"), (cg, "resume_calls", 2), (cg, "resume_calls", True),
            (cg, "compiler", "clang"), (cg, "opt_level", 4), (cg, "opt_level", 0.0),
            (llvm, "passes", 0), (llvm, "drop_events", 0), (llvm, "box_frees", 20),
            (llvm, "eh_functions", 3),
            # A bridge lane never omits a modelled free; LLVM omits at most the elidable ones.
            (cg, "elided_box_frees", 1), (cg, "elided_box_frees", True), (llvm + 2, "box_frees", 21),
            (llvm + 2, "elided_box_frees", 4), (llvm + 2, "elided_box_frees", -1),
        ):
            mutated = copy.deepcopy(good)
            mutated["lanes"][index][key] = value
            cases.append(mutated)
        # Rows 1 and 3 are the LLVM O0 and O1 lanes; the classifier accepts
        # either elision count only with the matching free total.
        self.assertEqual(good["lanes"][llvm]["elided_box_frees"], 0)
        self.assertEqual(good["lanes"][llvm + 2]["elided_box_frees"], 3)
        consistent = copy.deepcopy(good)
        consistent["lanes"][llvm].update(elided_box_frees=1, box_frees=18)
        marker = GATE.UNWIND_MARKER + json.dumps(consistent) + "\n"
        self.assertEqual(GATE.classify_unwind_native(0, unwind_transcript(marker), SHA)["status"], "pass")
        for key in ("resume_calls", "box_frees"):
            mutated = copy.deepcopy(good)
            del mutated["lanes"][cg][key]
            cases.append(mutated)
        for key, value in (
            ("function", "other"), ("callee", "ay_may_unwind"), ("opt_level", 4),
            ("mutated_rows", 2), ("mutated_rows", 0), ("landing_pad", 0), ("landing_pad", True),
            ("lsda_rows", 1), ("exit_code", 134), ("exit_code", None), ("lost_drops", 1),
            ("lost_frees", 0), ("lost_frees", True),
        ):
            mutated = copy.deepcopy(good)
            # Row 1 is guards_across_unwind at O0: 4 drops and 2 frees lost.
            mutated["missing_landing_pad_controls"][1][key] = value
            cases.append(mutated)
        mutated = copy.deepcopy(good)
        del mutated["missing_landing_pad_controls"][0]["lost_frees"]
        cases.append(mutated)
        for key, value in (("cg_refusals", 0), ("cg_refusals", True), ("refused_functions", 2),
                           ("fixture_definitions", 1), ("name", "other"), ("opt_level", 4)):
            mutated = copy.deepcopy(good)
            mutated["unsupported"][0][key] = value
            cases.append(mutated)
        for index, execution in enumerate(cases):
            with self.subTest(case=index):
                marker = GATE.UNWIND_MARKER + json.dumps(execution) + "\n"
                self.assertEqual(GATE.classify_unwind_native(0, unwind_transcript(marker), SHA)["status"], "fail")
        for text in ("", GATE.UNWIND_MARKER + "not json\n", GATE.UNWIND_MARKER + "[]\n",
                     (GATE.UNWIND_MARKER + json.dumps(good) + "\n") * 2,
                     GATE.TLS_MARKER + json.dumps(good) + "\n"):
            with self.subTest(marker=text[:40]):
                self.assertEqual(GATE.classify_unwind_native(0, unwind_transcript(text), SHA)["status"], "fail")
        for text in (unwind_transcript(passed=0), unwind_transcript(ignored=1), unwind_transcript(filtered=1),
                     unwind_transcript(skip="skipped: no unwinder\n")):
            self.assertEqual(GATE.classify_unwind_native(0, text, SHA)["status"], "fail")
        self.assertEqual(GATE.classify_unwind_native(101, unwind_transcript(), SHA)["status"], "fail")
        # No marker satisfies another target's classifier.
        self.assertEqual(GATE.classify_native(0, unwind_transcript(), SHA)["status"], "fail")
        self.assertEqual(GATE.classify_tls_native(0, unwind_transcript(), SHA)["status"], "fail")
        self.assertEqual(GATE.classify_unwind_native(0, tls_transcript(), SHA)["status"], "fail")

    def test_runtime_twin_markers_require_every_lane_control_and_refusal(self):
        classifiers = {"static": GATE.classify_static_native, "heap": GATE.classify_heap_native,
                       "coroutine": GATE.classify_coroutine_native}
        for which, classify in classifiers.items():
            with self.subTest(target=which):
                good = runtime_record_of(which)
                self.assertEqual(classify(0, runtime_transcript(which), SHA)["status"], "pass",
                                 classify(0, runtime_transcript(which), SHA)["errors"])
                cases = []
                for key, value in (
                    ("schema", 0), ("schema", True), ("target", "aarch64-apple-darwin"), ("opt_levels", [0, 3]),
                    ("opt_levels", [False, True, 2, 3]), ("backend_sha256", "0" * 64), ("certificates", "on"),
                    ("frontend_verify", "on"), ("runs_per_lane", 2), ("runs_per_lane", True), ("lanes", None),
                    ("model_sha256", {}),
                ):
                    cases.append({**good, key: value})
                for index in (0, len(good["lanes"]) - 1):
                    mutated = copy.deepcopy(good)
                    mutated["lanes"].pop(index)
                    cases.append(mutated)
                duplicate = copy.deepcopy(good)
                duplicate["lanes"].append(copy.deepcopy(duplicate["lanes"][0]))
                cases.append(duplicate)
                for key, value in (("ending", "exit:1"), ("ending", "signal:6"), ("stdout_sha256", "0" * 64),
                                   ("runs", 2), ("passes", 2), ("compiler", "clang"), ("opt_level", 4),
                                   ("opt_level", 0.0), ("fixture", "other")):
                    mutated = copy.deepcopy(good)
                    mutated["lanes"][1][key] = value
                    cases.append(mutated)
                mutated = copy.deepcopy(good)
                mutated["lanes"][0]["refusals"] = 1
                cases.append(mutated)
                # A model digest that does not match: every lane of that fixture fails.
                mutated = copy.deepcopy(good)
                first = good["lanes"][0]["fixture"]
                mutated["model_sha256"][first] = "1" * 64
                cases.append(mutated)
                if which == "static":
                    for key, value in (("pointer_relocations", 11), ("extern_imports", 1), ("statics", 20),
                                       ("abort_stubs", -1)):
                        mutated = copy.deepcopy(good)
                        mutated["objects"][0][key] = value
                        cases.append(mutated)
                    mutated = copy.deepcopy(good)
                    mutated["objects"].pop()
                    cases.append(mutated)
                    # Equal class counts, but CG and LLVM disagree on two statics.
                    mutated = copy.deepcopy(good)
                    mutated["objects"][0]["storage"].update(AY_STATIC_N="Data", AY_STATIC_MUT="ReadOnly")
                    cases.append(mutated)
                    mutated = copy.deepcopy(good)
                    for row in mutated["objects"]:
                        row["storage"]["AY_ZERO_WORDS"] = "Data"
                    cases.append(mutated)
                if which == "heap":
                    for key, value in (("per_function_shared_entry_object", True), ("per_function_objects", 2),
                                       ("opt_level", 1)):
                        mutated = copy.deepcopy(good)
                        mutated["partitions"][0][key] = value
                        cases.append(mutated)
                    cases.append({**good, "partitions": []})
                if which == "coroutine":
                    cases.append({**good, "refused_lanes": [{"fixture": "sequence", "compiler": "cg",
                                                            "opt_level": 2, "rows": "- ay_gen_seq: refused"}]})
                    cases.append({**good, "refused_lanes": None})
                    cases.append({**good, "mir": {**good["mir"], "yield_terminators": 1}})
                if which in ("heap", "coroutine"):
                    for key, value in (("cg_refusals", 0), ("refusal_rows", 1), ("cg_definitions", 1),
                                       ("name", "other"), ("llvm_runs", 0), ("opt_level", 4)):
                        mutated = copy.deepcopy(good)
                        mutated["refusal_controls"][0][key] = value
                        cases.append(mutated)
                    mutated = copy.deepcopy(good)
                    mutated["refusal_controls"].pop()
                    cases.append(mutated)
                for index, execution in enumerate(cases):
                    with self.subTest(case=index):
                        self.assertEqual(classify(0, runtime_transcript(which, execution), SHA)["status"], "fail")
                knobs = RUNTIME_KNOBS[which]
                for text in (
                    runtime_transcript(which, knobs=knobs[:-1]),
                    runtime_transcript(which, knobs=[*knobs, "TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs"]),
                    runtime_transcript(which, knobs=[*knobs[:-1], "TCG_BRIDGE_BACKEND_KNOBS knobs="]),
                    runtime_transcript(which, passed=2), runtime_transcript(which, passed=4),
                    runtime_transcript(which, ignored=1), runtime_transcript(which, filtered=1),
                    runtime_transcript(which, skip="skipped: no native host\n"),
                    runtime_transcript(which) + runtime_marker(which) + json.dumps(good) + "\n",
                    transcript(runtime_marker(which) + "not json\n", passed=3),
                    tls_transcript(passed=3),
                ):
                    self.assertEqual(classify(0, text, SHA)["status"], "fail")
                self.assertEqual(classify(101, runtime_transcript(which), SHA)["status"], "fail")
                # No runtime twin's marker satisfies another target's classifier.
                for other, other_classify in classifiers.items():
                    if other != which:
                        self.assertEqual(other_classify(0, runtime_transcript(which), SHA)["status"], "fail")
                self.assertEqual(GATE.classify_tls_native(0, runtime_transcript(which), SHA)["status"], "fail")

    def test_portable_targets_require_complete_positive_native_evidence(self):
        for name, classify in (("panic", GATE.classify_panic_native), ("trap", GATE.classify_trap_native)):
            with self.subTest(name=name):
                text = portable_transcript(name)
                self.assertEqual(classify(0, text, SHA)["status"], "pass")
                self.assertEqual(classify(0, text.replace("TCG_DARWIN_BRIDGE_POSITIVE", "missing"), SHA)["status"], "fail")
                self.assertEqual(classify(0, text.replace("knobs=no-proof-certs", "knobs="), SHA)["status"], "fail")
                passed = text.count(" ... ok")
                self.assertEqual(classify(0, text.replace(f"{passed} passed", f"{passed - 1} passed"), SHA)["status"],
                                 "fail")
        # Both -O0 dyn-heap rows must run natively; the -O2 rows may refuse.
        for native in range(5):
            verdict = GATE.classify_trap_native(0, portable_transcript("trap", native=native), SHA)
            self.assertEqual(verdict["status"], "pass" if native >= 2 else "fail", verdict)
            self.assertEqual(verdict["guarded_execution"]["cg_native"], native)

    def test_scalar_zst_native_requires_every_lane_and_counter(self):
        control = zst_execution_record()
        self.assertEqual(GATE.classify_zst_native(0, zst_transcript(control), SHA)["status"], "pass")
        mutations = []
        for field, value in (("schema", True), ("target", "aarch64-apple-darwin"),
                             ("comparisons", 7), ("backend_sha256", "0" * 64),
                             ("compiler_sha256", ""), ("certificates", "on"),
                             ("frontend_verify", "on")):
            row = copy.deepcopy(control); row[field] = value; mutations.append(row)
        for field, value in (("executions", 0), ("driver_checks", 56), ("layout_checks", 15),
                             ("callback_checks", 0), ("address_observations", 0), ("opt_level", True), ("compiler", "refused")):
            row = copy.deepcopy(control); row["lanes"][0][field] = value; mutations.append(row)
        row = copy.deepcopy(control); row["lanes"].pop(); mutations.append(row)
        row = copy.deepcopy(control); row["lanes"][0] = row["lanes"][1]; mutations.append(row)
        row = copy.deepcopy(control); row["lanes"][0]["refusals"] = 1; mutations.append(row)
        for row in mutations:
            with self.subTest(row=row):
                self.assertEqual(GATE.classify_zst_native(0, zst_transcript(row), SHA)["status"], "fail")
        text = zst_transcript()
        malformed = [
            text.replace("knobs=no-proof-certs", "knobs=disable-unwind", 1),
            text.replace("NativeRun scalar_zst_field_matches_llvm", "Compiled scalar_zst_field_matches_llvm"),
            text.replace("running 1 tests", "running 0 tests").replace("1 passed", "0 passed"),
            text.replace("0 filtered out", "1 filtered out"),
            text + GATE.ZST_MARKER + json.dumps(control) + "\n",
            zst_transcript(skip="SKIP native unavailable\n"),
            transcript(GATE.ZST_MARKER + "[]\n", passed=1),
        ]
        for altered in malformed:
            self.assertEqual(GATE.classify_zst_native(0, altered, SHA)["status"], "fail")
        self.assertEqual(GATE.classify_zst_native(1, text, SHA)["status"], "fail")

    # Default bound for runs meant to FINISH; the timeout test passes timeout=1 against a 60 s sleep (F-164).
    def fixture_run(self, mode="pass", fingerprints=None, *, timeout=60, channel="trust"):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp).resolve()
            target_dir = directory / "cache"
            backend = target_dir / "release" / GATE.BACKEND_NAME
            backend.parent.mkdir(parents=True)
            backend.write_bytes(b"old preexisting backend")
            calls = directory / "calls"
            fixture = directory / ("targo-fixture" if channel == "trust" else "rustup-fixture")
            tool_args = ["--unverified"] if channel == "trust" else ["run", channel, "cargo"]
            native = target_dir / "release/deps" / (GATE.TARGET + "-fixture")
            tls_native = target_dir / "release/deps" / (GATE.TLS_TARGET + "-fixture")
            unwind_native = target_dir / "release/deps" / (GATE.UNWIND_TARGET + "-fixture")
            panic_native = target_dir / "release/deps" / (GATE.PANIC_TARGET + "-fixture")
            trap_native = target_dir / "release/deps" / (GATE.TRAP_TARGET + "-fixture")
            zst_native = target_dir / "release/deps" / (GATE.ZST_TARGET + "-fixture")
            runtime_natives = {
                "static": target_dir / "release/deps" / (GATE.STATIC_TARGET + "-fixture"),
                "heap": target_dir / "release/deps" / (GATE.HEAP_TARGET + "-fixture"),
                "coroutine": target_dir / "release/deps" / (GATE.COROUTINE_TARGET + "-fixture"),
            }
            runtime_names = {"static": GATE.STATIC_TARGET, "heap": GATE.HEAP_TARGET,
                             "coroutine": GATE.COROUTINE_TARGET}
            natives = {"hfa": native, "tls": tls_native, "unwind": unwind_native,
                       "panic": panic_native, "trap": trap_native, "zst": zst_native, **runtime_natives}
            native_sources = {
                which: (
                    PYTHON_FIXTURE_HEADER + "import os, runpy, sys\n"
                    "os.environ['FAKE_PORTABLE_EXE'] = __file__\n"
                    f"sys.argv = [{str(fixture)!r}, '--native', {which!r}]\n"
                    f"runpy.run_path({str(fixture)!r}, run_name='__main__')\n"
                )
                for which in natives
            }
            fixture.write_text(
                PYTHON_FIXTURE_HEADER +
                "import hashlib, json, os, sys, time\n"
                "from pathlib import Path\n"
                f"mode = {mode!r}\n"
                f"backend = Path({str(backend)!r})\n"
                f"calls = Path({str(calls)!r})\n"
                "if sys.argv[1:2] == ['--native']:\n"
                "    action = 'native'\n"
                "    which = sys.argv[2]\n"
                "else:\n"
                f"    assert sys.argv[1:{1 + len(tool_args)}] == {tool_args!r}\n"
                f"    if {channel == 'trust'!r}: assert os.environ['RUSTC'] == {str(directory / 'trustc-fixture')!r}\n"
                f"    action = sys.argv[{1 + len(tool_args)}]\n"
                "    assert '--release' in sys.argv and '--locked' in sys.argv\n"
                "    assert Path(sys.argv[sys.argv.index('--target-dir') + 1]) == backend.parent.parent\n"
                "    assert not any(key.startswith('TCG_') for key in os.environ)\n"
                "native_label = {'hfa': 'test', 'tls': 'tls-test', 'unwind': 'unwind-test', 'panic': 'panic-test', 'trap': 'trap-test', 'zst': 'zst-test',\n"
                "                'static': 'static-test', 'heap': 'heap-test', 'coroutine': 'coroutine-test'}\n"
                "label = {'native': native_label[which] if action == 'native' else 'test', 'test': 'test-build'}\n"
                "with calls.open('a') as out: out.write(label.get(action, action) + '\\n')\n"
                "assert Path(os.environ['CARGO_TARGET_DIR']) == backend.parent.parent\n"
                "if action == 'build':\n"
                "    if mode == 'timeout': time.sleep(60)\n"
                "    if mode == 'buildfail': raise SystemExit(9)\n"
                "    assert '--message-format=json-render-diagnostics' in sys.argv\n"
                "    if mode != 'missing_backend': backend.write_bytes(b'built backend')\n"
                "    else: backend.unlink()\n"
                "    if mode != 'missing_artifact':\n"
                "        print(json.dumps({'reason':'compiler-artifact',\n"
                f"            'manifest_path':{str(GATE.MANIFEST)!r},\n"
                "            'target':{'name':'rustc_codegen_trust_cg','kind':['dylib']},\n"
                "            'filenames':[str(backend) + ('.wrong' if mode == 'wrong_artifact' else '')],\n"
                "            'fresh':False}))\n"
                "    print(json.dumps({'reason':'build-finished','success':mode != 'unfinished'}))\n"
                "elif action == 'test':\n"
                "    tests = [sys.argv[i + 1] for i, value in enumerate(sys.argv) if value == '--test']\n"
                f"    assert tests == {list(GATE.REQUIRED_TARGETS)!r}, tests\n"
                "    assert '--no-run' in sys.argv and '--message-format=json-render-diagnostics' in sys.argv\n"
                "    if mode == 'test_build_fail': raise SystemExit(8)\n"
                f"    for path, text in (({str(tls_native)!r}, {native_sources['tls']!r}),\n"
                f"                       ({str(unwind_native)!r}, {native_sources['unwind']!r}),\n"
                f"                       ({str(native)!r}, {native_sources['hfa']!r}),\n"
                f"                       ({str(panic_native)!r}, {native_sources['panic']!r}),\n"
                f"                       ({str(trap_native)!r}, {native_sources['trap']!r}),\n"
                f"                       ({str(zst_native)!r}, {native_sources['zst']!r}),\n"
                + "".join(f"                       ({str(runtime_natives[which])!r}, {native_sources[which]!r}),\n"
                          for which in runtime_natives)
                + "                       ):\n"
                "        Path(path).parent.mkdir(parents=True, exist_ok=True)\n"
                "        Path(path).write_text(text)\n"
                "        Path(path).chmod(0o700)\n"
                f"    native = Path({str(native)!r})\n"
                f"    tls_artifact = {{'reason':'compiler-artifact', 'manifest_path':{str(GATE.MANIFEST)!r},\n"
                f"        'target':{{'name':{GATE.TLS_TARGET!r}, 'kind':['test']}}, 'profile':{{'test':True}},\n"
                f"        'filenames':[{str(tls_native)!r}], 'executable':{str(tls_native)!r}, 'fresh':False}}\n"
                "    if mode != 'missing_tls_test_artifact': print(json.dumps(tls_artifact))\n"
                f"    unwind_artifact = {{'reason':'compiler-artifact', 'manifest_path':{str(GATE.MANIFEST)!r},\n"
                f"        'target':{{'name':{GATE.UNWIND_TARGET!r}, 'kind':['test']}}, 'profile':{{'test':True}},\n"
                f"        'filenames':[{str(unwind_native)!r}], 'executable':{str(unwind_native)!r}, 'fresh':False}}\n"
                "    if mode != 'missing_unwind_test_artifact': print(json.dumps(unwind_artifact))\n"
                f"    for name, path in (({GATE.PANIC_TARGET!r}, {str(panic_native)!r}), ({GATE.TRAP_TARGET!r}, {str(trap_native)!r}), ({GATE.ZST_TARGET!r}, {str(zst_native)!r}),\n"
                + "".join(f"                       ({runtime_names[which]!r}, {str(runtime_natives[which])!r}),\n"
                          for which in runtime_natives)
                + "                       ):\n"
                f"        if name == {GATE.ZST_TARGET!r} and mode == 'missing_zst_test_artifact': continue\n"
                f"        if name == {GATE.STATIC_TARGET!r} and mode == 'missing_static_test_artifact': continue\n"
                f"        if name == {GATE.HEAP_TARGET!r} and mode == 'missing_heap_test_artifact': continue\n"
                f"        if name == {GATE.COROUTINE_TARGET!r} and mode == 'missing_coroutine_test_artifact': continue\n"
                "        print(json.dumps({'reason':'compiler-artifact',\n"
                f"            'manifest_path':{str(GATE.MANIFEST)!r}, 'target':{{'name':name, 'kind':['test']}},\n"
                "            'profile':{'test':True}, 'filenames':[path], 'executable':path, 'fresh':False}))\n"
                f"    artifact = {{'reason':'compiler-artifact', 'manifest_path':{str(GATE.MANIFEST)!r},\n"
                f"        'target':{{'name':{GATE.TARGET!r}, 'kind':['test']}}, 'profile':{{'test':True}},\n"
                "        'filenames':[str(native)], 'executable':str(native), 'fresh':False}\n"
                "    if mode == 'wrong_test_artifact': artifact['target']['name'] = 'other_test'\n"
                "    if mode == 'wrong_test_profile': artifact['profile']['test'] = False\n"
                "    if mode == 'missing_test_executable': artifact['executable'] = None\n"
                "    if mode == 'wrong_test_path': artifact['executable'] = str(backend)\n"
                "    if mode == 'test_symlink':\n"
                "        native.unlink()\n"
                "        native.symlink_to(__file__)\n"
                "    if mode != 'missing_test_artifact': print(json.dumps(artifact))\n"
                "    if mode == 'duplicate_test_artifact': print(json.dumps(artifact))\n"
                "    print(json.dumps({'reason':'build-finished','success':mode != 'test_unfinished'}))\n"
                # Model Cargo's test-graph rebuild before the native fixture
                # opens the backend supplied by the runner.
                "    if mode == 'changed_backend': backend.write_bytes(b'changed during test')\n"
                "elif action == 'native':\n"
                "    if which != 'hfa' and mode.startswith(which + '_'): mode = mode[len(which) + 1:]\n"
                "    elif which != 'hfa': mode = 'pass'\n"
                f"    if mode == 'changed_test_executable': Path({ {key: str(path) for key, path in natives.items()}!r}[which]).write_text('changed during execution')\n"
                "    snapshot = Path(os.environ['TCG_TEST_BACKEND_PATH'])\n"
                f"    assert snapshot == Path({str(directory / 'report' / GATE.BACKEND_NAME)!r})\n"
                "    assert snapshot != backend and snapshot.stat().st_ino != backend.stat().st_ino\n"
                "    assert snapshot.stat().st_mode & 0o777 == 0o444\n"
                "    assert snapshot.stat().st_nlink == 1 and not snapshot.is_symlink()\n"
                "    assert snapshot.read_bytes() == b'built backend'\n"
                "    assert os.environ['TCG_TEST_BACKEND_SHA256'] == hashlib.sha256(snapshot.read_bytes()).hexdigest()\n"
                "    if mode == 'changed_snapshot':\n"
                "        snapshot.chmod(0o600)\n"
                "        snapshot.write_bytes(b'tampered during test')\n"
                "        snapshot.chmod(0o444)\n"
                "    if mode == 'replaced_snapshot':\n"
                "        replacement = snapshot.with_suffix('.replacement')\n"
                "        replacement.write_bytes(b'built backend')\n"
                "        replacement.chmod(0o444)\n"
                "        replacement.replace(snapshot)\n"
                "    if mode == 'symlink_snapshot':\n"
                "        snapshot.unlink()\n"
                "        snapshot.symlink_to(backend)\n"
                "    if which in ('panic', 'trap', 'zst'):\n"
                "        selected = Path(os.environ['FAKE_PORTABLE_EXE']).parent / 'librustc_codegen_trust_cg.so'\n"
                "        assert selected.parent.name == 'deps' and selected != backend and selected != snapshot\n"
                "        assert selected.read_bytes() == snapshot.read_bytes() == b'built backend'\n"
                "        assert selected.stat().st_ino != snapshot.stat().st_ino\n"
                f"    text = {{'hfa': {transcript()!r}, 'tls': {tls_transcript()!r}, 'unwind': {unwind_transcript()!r}, 'panic': {portable_transcript('panic')!r}, 'trap': {portable_transcript('trap')!r}, 'zst': {zst_transcript()!r},\n"
                f"            'static': {runtime_transcript('static')!r}, 'heap': {runtime_transcript('heap')!r}, 'coroutine': {runtime_transcript('coroutine')!r}}}[which]\n"
                f"    runtime_records = {{which: {{'static': {static_execution_record()!r}, 'heap': {heap_execution_record()!r}, 'coroutine': {coroutine_execution_record()!r}}}[which] for which in ('static', 'heap', 'coroutine')}}\n"
                f"    runtime_knobs = {RUNTIME_KNOBS!r}\n"
                f"    runtime_markers = {{'static': {GATE.STATIC_MARKER!r}, 'heap': {GATE.HEAP_MARKER!r}, 'coroutine': {GATE.COROUTINE_MARKER!r}}}\n"
                "    if which in runtime_records and mode in ('missing_runtime_lane', 'runtime_refused', 'runtime_certs_on', 'runtime_wrong_digest'):\n"
                "        execution = runtime_records[which]\n"
                "        if mode == 'missing_runtime_lane': execution['lanes'].pop()\n"
                "        if mode == 'runtime_certs_on': execution['certificates'] = 'on'\n"
                "        if mode == 'runtime_wrong_digest': execution['lanes'][0]['stdout_sha256'] = '0' * 64\n"
                "        if mode == 'runtime_refused':\n"
                "            execution['refused_lanes'] = [{'fixture': 'sequence', 'compiler': 'cg', 'opt_level': 2, 'rows': '- ay_gen_seq: [TCG-A64-SWITCH-BIND]'}]\n"
                "            execution['lanes'] = [row for row in execution['lanes'] if (row['fixture'], row['compiler'], row['opt_level']) != ('sequence', 'cg', 2)]\n"
                "        text = 'running 3 tests\\n' + ''.join(line + '\\n' for line in runtime_knobs[which]) + runtime_markers[which] + json.dumps(execution) + '\\ntest result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\\n'\n"
                f"    if mode == 'missing_marker': text = {transcript('')!r}\n"
                f"    if mode == 'skipped': text = {transcript(skip='SKIP native execution unavailable' + chr(10))!r}\n"
                f"    if mode == 'zero_suite': text = {transcript(passed=0)!r}\n"
                "    if mode in ('missing_control', 'pad_lost_nothing'):\n"
                f"        execution = {unwind_execution_record()!r}\n"
                "        if mode == 'missing_control': execution['missing_landing_pad_controls'].pop()\n"
                "        if mode == 'pad_lost_nothing': execution['missing_landing_pad_controls'][0]['lost_frees'] = 0\n"
                f"        text = 'running 2 tests\\n' + {GATE.UNWIND_MARKER!r} + json.dumps(execution) + '\\ntest result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\\n'\n"
                "    if mode in ('missing_lane', 'refusal_as_native'):\n"
                f"        execution = {tls_execution_record()!r}\n"
                "        if mode == 'missing_lane': execution['lanes'].pop()\n"
                "        if mode == 'refusal_as_native': execution['unsupported'][0]['cg_refusals'] = 0\n"
                f"        text = 'running 2 tests\\n' + {GATE.TLS_MARKER!r} + json.dumps(execution) + '\\ntest result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\\n'\n"
                "    if mode in ('missing_native_family', 'missing_llvm_tier', 'unsupported_as_native', 'shrunken_native_counters'):\n"
                f"        execution = {execution_record()!r}\n"
                "        native = execution['scalar_cell']['native']\n"
                "        if mode == 'missing_native_family':\n"
                "            execution['scalar_cell']['native'] = [row for row in native if row['family'] != 'local_cell_read']\n"
                "        if mode == 'missing_llvm_tier':\n"
                "            execution['scalar_cell']['native'] = [row for row in native if not (row['compiler'] == 'llvm' and row['opt_level'] == 3)]\n"
                "        if mode == 'unsupported_as_native':\n"
                "            native[0]['calls'] = 0\n"
                "            native[0]['checks'] = 0\n"
                "            native[0]['refusals'] = 1\n"
                "        if mode == 'shrunken_native_counters': native[0]['calls'] -= 1\n"
                f"        text = 'running 2 tests\\n' + {GATE.MARKER!r} + json.dumps(execution) + '\\ntest result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\\n'\n"
                "    print(text)\n"
                "    if mode == 'testfail': raise SystemExit(7)\n"
                "else: raise AssertionError(action)\n"
            )
            fixture.chmod(0o700)
            xback = directory / "xback-fixture"
            xback.write_text(
                PYTHON_FIXTURE_HEADER +
                "import hashlib, importlib.util, json, sys\n"
                "from pathlib import Path\n"
                "args = sys.argv[1:]\n"
                "def value(flag): return args[args.index(flag) + 1]\n"
                f"mode = {mode!r}\n"
                f"with Path({str(calls)!r}).open('a') as out: out.write('xback\\n')\n"
                f"spec = importlib.util.spec_from_file_location('xback_tests', {str(XBACK_TESTS)!r})\n"
                "module = importlib.util.module_from_spec(spec)\n"
                "spec.loader.exec_module(module)\n"
                "backend = Path(value('--backend'))\n"
                f"assert backend == Path({str(directory / 'report' / GATE.BACKEND_NAME)!r})\n"
                "assert hashlib.sha256(backend.read_bytes()).hexdigest() == value('--backend-sha256')\n"
                f"assert value('--trustc') == {str(directory / 'trustc-fixture')!r}\n"
                "report = module.synthetic_report(value('--backend-sha256'), value('--trustc'))\n"
                "if mode == 'xback_wrong_hash': report['backend']['sha256'] = '0' * 64\n"
                "if mode == 'xback_wrong_compiler': report['compiler']['path'] = '/other/trustc'\n"
                "if mode == 'xback_mismatch':\n"
                "    row = next(row for row in report['cells'] if row['outcome'] == 'match')\n"
                "    row.update(outcome='mismatch', reason='exit 7 vs oracle 0')\n"
                "    report['status'] = 'fail'\n"
                "if mode == 'xback_status_only': report['status'] = 'fail'\n"
                "if mode == 'xback_superseded_wrong':\n"
                "    row = dict(next(row for row in report['cells'] if row['outcome'] == 'match'))\n"
                "    row.update(outcome='mismatch', reason='exit 7 vs oracle 0', superseded=True)\n"
                "    report['cells'].append({'group_attempt': row})\n"
                "if mode == 'xback_unlisted_decline':\n"
                "    row = next(row for row in report['cells'] if row['outcome'] == 'match' and row['callee'] == 'tcg')\n"
                "    row.update(outcome='decline', decline={'side': 'callee', 'tags': ['[TCG-ARG-ABI]'],\n"
                "               'message': 'fixture', 'functions': []})\n"
                "out = Path(value('--out'))\n"
                "out.mkdir()\n"
                "if mode != 'xback_missing_report': (out / 'report.json').write_text(json.dumps(report))\n"
                "raise SystemExit(1 if mode in ('xback_mismatch', 'xback_status_only') else 0)\n"
            )
            xback.chmod(0o700)
            provenance = {
                "source_fingerprint": "same", "source_sha": "fixture-current-source",
                "toolchain": channel, "target_dir": str(target_dir),
                "compiler_path": str(directory / "trustc-fixture"),
                "tools": {"git": "fixture-git", "rustup": str(fixture), "targo": str(fixture), "env": "/usr/bin/env"},
            }
            snapshots = [{"source_fingerprint": value} for value in (fingerprints or ["same", "same", "same"])]
            output = directory / "report"
            with mock.patch.object(GATE, "preflight", return_value=provenance), \
                    mock.patch.object(GATE, "XBACK_RUNNER", xback), \
                    mock.patch.object(GATE.SHARED, "proof_tool_identities", return_value=copy.deepcopy(PINNED_PROOF_TOOLS)):
                with mock.patch.object(GATE.SHARED, "source_provenance", side_effect=snapshots):
                    code = GATE.main([
                        "--out", str(output), "--target-dir", str(target_dir),
                        "--timeout-seconds", str(timeout),
                    ])
            report = json.loads((output / "report.json").read_text())
            logs = {path.name: path.read_text() for path in output.glob("*.log")}
            return code, report, calls.read_text().splitlines(), logs

    def test_real_build_then_complete_native_process_and_exact_backend_contract(self):
        code, report, calls, logs = self.fixture_run()
        self.assertEqual(code, 0, report)
        self.assertEqual(calls, FULL_CALLS)
        self.assertEqual(report["status"], "pass")
        self.assertEqual(report["required_targets"], [GATE.TARGET, GATE.TLS_TARGET, GATE.UNWIND_TARGET, GATE.PANIC_TARGET, GATE.TRAP_TARGET, GATE.ZST_TARGET,
                                                     GATE.STATIC_TARGET, GATE.HEAP_TARGET, GATE.COROUTINE_TARGET])
        self.assertEqual(report["target_status"],
                         {target: "pass" for target in GATE.REQUIRED_TARGETS} | {GATE.XBACK_KEY: "pass"})
        self.assertEqual(report["unwind_test"]["counts"]["passed"], 2)
        self.assertEqual(len(report["unwind_test"]["execution"]["lanes"]), 8)
        self.assertEqual(len(report["unwind_test"]["execution"]["missing_landing_pad_controls"]), 12)
        self.assertEqual(report["unwind_test"]["execution"]["backend_sha256"], SHA)
        self.assertEqual(report["backend_snapshot"], report["backend_snapshot_before_unwind_test"])
        self.assertEqual(report["backend_snapshot"], report["backend_snapshot_after_unwind_test"])
        self.assertEqual(report["tls_test"]["counts"]["passed"], 2)
        self.assertEqual(len(report["tls_test"]["execution"]["lanes"]), 8)
        self.assertEqual(report["tls_test"]["execution"]["backend_sha256"], SHA)
        self.assertEqual(report["backend_snapshot"], report["backend_snapshot_before_tls_test"])
        self.assertEqual(report["backend_snapshot"], report["backend_snapshot_after_tls_test"])
        self.assertEqual(set(report["test_build"]["executable_identities"]), set(GATE.REQUIRED_TARGETS))
        self.assertNotEqual(report["backend_before_build"], report["backend_after_build"])
        self.assertEqual(report["backend_after_build"]["sha256"], SHA)
        self.assertEqual(report["backend_after_build"], report["backend_after_test"])
        self.assertFalse(report["cache_backend_changed_during_test"])
        self.assertEqual(report["backend_snapshot"]["sha256"], SHA)
        self.assertEqual(report["backend_snapshot"]["size"], report["backend_after_build"]["size"])
        self.assertNotEqual(report["backend_snapshot"]["stat"]["inode"], report["backend_after_build"]["stat"]["inode"])
        self.assertEqual(report["backend_snapshot"], report["backend_snapshot_before_test"])
        self.assertEqual(report["backend_snapshot"], report["backend_snapshot_after_test"])
        self.assertEqual(report["test"]["counts"]["passed"], 2)
        self.assertEqual(report["test"]["execution"]["executions"], 8)
        self.assertEqual(set(logs), {"build.log", "test-build.log", "native.log", "tls-native.log",
                                    "unwind-native.log", "panic-hook-native.log", "executable-trap-native.log",
                                    "scalar-zst-field-native.log", "static-data-native.log", "drop-heap-native.log",
                                    "coroutine-native.log", "cross-backend-abi.log"})
        for step in ("build", "test", "tls_test", "unwind_test"):
            self.assertEqual(len(report[step]["log_sha256"]), 64)

    def test_cross_backend_abi_step_is_required_and_rederives_its_verdict(self):
        code, report, calls, _ = self.fixture_run()
        self.assertEqual(code, 0, report)
        self.assertEqual(report[GATE.XBACK_KEY]["status"], "pass")
        listed = {(row["suite"], row["case"], row["side"]) for row in report[GATE.XBACK_KEY]["declines"]}
        self.assertEqual(listed, set(GATE.xback_gate().EXPECTED_DECLINES))
        self.assertEqual(report["target_status"][GATE.XBACK_KEY], "pass")
        for mode, text in (("xback_mismatch", "WRONG VALUE"), ("xback_status_only", "status is 'fail'"),
                           ("xback_superseded_wrong", "superseded group attempt"),
                           ("xback_wrong_hash", "qualified backend hash"),
                           ("xback_wrong_compiler", "another compiler"),
                           ("xback_unlisted_decline", "unlisted decline"),
                           ("xback_missing_report", "unreadable")):
            with self.subTest(mode=mode):
                code, report, calls, _ = self.fixture_run(mode)
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, FULL_CALLS)
                self.assertEqual(report["status"], "fail")
                self.assertEqual(report["target_status"][GATE.XBACK_KEY], "fail")
                self.assertTrue(any(text in error for error in report[GATE.XBACK_KEY]["errors"]),
                                report[GATE.XBACK_KEY]["errors"])
                # The native targets are unaffected by the cross-backend verdict.
                self.assertEqual({key: value for key, value in report["target_status"].items()
                                  if key != GATE.XBACK_KEY},
                                 {target: "pass" for target in GATE.REQUIRED_TARGETS})

    def test_preexisting_backend_cannot_launder_failed_or_unidentified_build(self):
        for mode in ("buildfail", "missing_artifact", "wrong_artifact", "unfinished", "missing_backend"):
            with self.subTest(mode=mode):
                code, report, calls, _ = self.fixture_run(mode)
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, ["build"])
                self.assertNotIn("test", report)
                self.assertNotIn("backend_snapshot", report)
                self.assertIsNotNone(report["backend_before_build"])

    def test_failed_or_ambiguous_test_build_never_executes_native_binary(self):
        for mode in ("test_build_fail", "missing_test_artifact", "wrong_test_artifact",
                     "duplicate_test_artifact", "test_unfinished", "wrong_test_profile",
                     "missing_test_executable", "wrong_test_path", "missing_tls_test_artifact",
                     "missing_unwind_test_artifact", "missing_zst_test_artifact",
                     "missing_static_test_artifact", "missing_heap_test_artifact",
                     "missing_coroutine_test_artifact"):
            with self.subTest(mode=mode):
                code, report, calls, _ = self.fixture_run(mode, channel="trust")
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, ["build", "test-build"])
                self.assertEqual(report["test_build"]["status"], "fail")
                self.assertNotIn("test", report)

    def test_test_executable_identity_cannot_be_substituted(self):
        for mode, calls in (("test_symlink", ["build", "test-build"]),
                            ("changed_test_executable", ["build", "test-build", "test"])):
            with self.subTest(mode=mode):
                code, report, observed, _ = self.fixture_run(mode, channel="trust")
                self.assertEqual(code, 1, report)
                self.assertEqual(observed, calls)
                self.assertTrue(report["errors"], report)

    def test_real_native_failure_skip_zero_or_absent_marker_cannot_pass(self):
        for mode in ("testfail", "skipped", "zero_suite", "missing_marker"):
            with self.subTest(mode=mode):
                code, report, calls, _ = self.fixture_run(mode)
                self.assertEqual(code, 1, report)
                # A failing ABI target never skips the independent TLS and unwind targets.
                self.assertEqual(calls, FULL_CALLS)
                self.assertEqual(report["tls_test"]["status"], "pass")
                self.assertEqual(report["unwind_test"]["status"], "pass")
                self.assertEqual(report["target_status"][GATE.TARGET], "fail")
                self.assertEqual(report["status"], "fail")

    def test_real_tls_native_failure_skip_or_missing_obligation_cannot_pass(self):
        for mode in ("tls_testfail", "tls_skipped", "tls_zero_suite", "tls_missing_marker",
                     "tls_missing_lane", "tls_refusal_as_native"):
            with self.subTest(mode=mode):
                code, report, calls, _ = self.fixture_run(mode)
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, FULL_CALLS)
                self.assertEqual(report["test"]["status"], "pass")
                self.assertEqual(report["tls_test"]["status"], "fail")
                self.assertEqual(report["target_status"],
                                 {target: "fail" if target == GATE.TLS_TARGET else "pass"
                                  for target in GATE.REQUIRED_TARGETS} | {GATE.XBACK_KEY: "pass"})
                self.assertEqual(report["status"], "fail")

    def test_real_unwind_native_failure_skip_or_missing_obligation_cannot_pass(self):
        for mode in ("unwind_testfail", "unwind_skipped", "unwind_zero_suite", "unwind_missing_marker",
                     "unwind_missing_control", "unwind_pad_lost_nothing"):
            with self.subTest(mode=mode):
                code, report, calls, _ = self.fixture_run(mode)
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, FULL_CALLS)
                self.assertEqual(report["test"]["status"], "pass")
                self.assertEqual(report["tls_test"]["status"], "pass")
                self.assertEqual(report["unwind_test"]["status"], "fail")
                self.assertEqual(report["target_status"],
                                 {target: "fail" if target == GATE.UNWIND_TARGET else "pass"
                                  for target in GATE.REQUIRED_TARGETS} | {GATE.XBACK_KEY: "pass"})
                self.assertEqual(report["status"], "fail")

    def test_real_runtime_twin_failure_skip_or_missing_obligation_cannot_pass(self):
        for which, target in (("static", GATE.STATIC_TARGET), ("heap", GATE.HEAP_TARGET),
                              ("coroutine", GATE.COROUTINE_TARGET)):
            modes = ["testfail", "skipped", "zero_suite", "missing_marker", "missing_runtime_lane",
                     "runtime_certs_on", "runtime_wrong_digest"]
            if which == "coroutine":
                modes.append("runtime_refused")
            for mode in modes:
                with self.subTest(target=which, mode=mode):
                    code, report, calls, _ = self.fixture_run(f"{which}_{mode}")
                    self.assertEqual(code, 1, report)
                    self.assertEqual(calls, FULL_CALLS)
                    self.assertEqual(report["target_status"],
                                     {name: "fail" if name == target else "pass"
                                      for name in GATE.REQUIRED_TARGETS} | {GATE.XBACK_KEY: "pass"})
                    self.assertEqual(report["status"], "fail")
        code, report, _, _ = self.fixture_run("coroutine_runtime_refused")
        self.assertTrue(any("refused a required coroutine lane" in error
                            for error in report["coroutine_test"]["errors"]), report["coroutine_test"]["errors"])

    def test_real_scalar_zst_failure_skip_zero_or_absent_marker_cannot_pass(self):
        for mode in ("zst_testfail", "zst_skipped", "zst_zero_suite", "zst_missing_marker"):
            with self.subTest(mode=mode):
                code, report, calls, _ = self.fixture_run(mode)
                self.assertEqual(code, 1, report)
                self.assertEqual(calls[-1], "xback")
                self.assertEqual(report["zst_test"]["status"], "fail")
                self.assertEqual(report["target_status"],
                                 {target: "fail" if target == GATE.ZST_TARGET else "pass"
                                  for target in GATE.REQUIRED_TARGETS} | {GATE.XBACK_KEY: "pass"})

    def test_unwind_snapshot_or_executable_tampering_rejects_otherwise_passing_run(self):
        for mode in ("unwind_changed_snapshot", "unwind_replaced_snapshot", "unwind_changed_test_executable"):
            with self.subTest(mode=mode):
                code, report, calls, _ = self.fixture_run(mode, channel="trust")
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, ["build", "test-build", "test", "tls-test", "unwind-test"])
                self.assertEqual(report["unwind_test"]["status"], "pass")
                self.assertEqual(report["status"], "fail")
                self.assertTrue(report["errors"], report)

    def test_tls_snapshot_or_executable_tampering_rejects_otherwise_passing_run(self):
        for mode in ("tls_changed_snapshot", "tls_replaced_snapshot", "tls_changed_test_executable"):
            with self.subTest(mode=mode):
                code, report, calls, _ = self.fixture_run(mode, channel="trust")
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, ["build", "test-build", "test", "tls-test"])
                self.assertEqual(report["tls_test"]["status"], "pass")
                self.assertEqual(report["status"], "fail")
                self.assertTrue(report["errors"], report)

    def test_real_cargo_test_cache_change_preserves_exact_snapshot_execution(self):
        code, report, calls, _ = self.fixture_run("changed_backend")
        self.assertEqual(code, 0, report)
        self.assertEqual(calls, FULL_CALLS)
        self.assertTrue(report["cache_backend_changed_during_test"])
        self.assertNotEqual(report["backend_after_build"]["sha256"], report["backend_after_test"]["sha256"])
        self.assertEqual(report["backend_snapshot"]["sha256"], SHA)
        self.assertEqual(report["backend_snapshot"], report["backend_snapshot_before_test"])
        self.assertEqual(report["backend_snapshot"], report["backend_snapshot_after_test"])
        self.assertEqual(report["test"]["execution"]["backend_sha256"], SHA)

    def test_real_native_process_cannot_substitute_missing_family_twin_or_refusal(self):
        for mode in ("missing_native_family", "missing_llvm_tier", "unsupported_as_native", "shrunken_native_counters"):
            with self.subTest(mode=mode):
                code, report, calls, _ = self.fixture_run(mode)
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, FULL_CALLS)
                self.assertEqual(report["test"]["counts"]["passed"], 2)
                self.assertEqual(report["test"]["status"], "fail")
                self.assertEqual(report["status"], "fail")

    def test_real_snapshot_tampering_rejects_otherwise_passing_native_process(self):
        for mode in ("changed_snapshot", "replaced_snapshot", "symlink_snapshot"):
            with self.subTest(mode=mode):
                code, report, calls, _ = self.fixture_run(mode)
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, ["build", "test-build", "test"])
                self.assertEqual(report["test"]["status"], "pass")
                self.assertEqual(report["status"], "fail")
                self.assertTrue(report["errors"], report)

    def test_source_change_after_build_prevents_test_and_after_test_rejects_result(self):
        for fingerprints, expected_calls in ((["changed"], ["build"]), (["same", "changed"], ["build", "test-build"]),
                                              (["same", "same", "changed"], FULL_CALLS)):
            code, report, calls, _ = self.fixture_run(fingerprints=fingerprints)
            self.assertEqual(code, 1, report)
            self.assertEqual(calls, expected_calls)
            self.assertIn("source changed", report["errors"][0])

    def test_build_timeout_is_bounded_and_does_not_reuse_old_backend(self):
        code, report, calls, logs = self.fixture_run("timeout", timeout=1)
        self.assertEqual(code, 1)
        self.assertEqual(calls, ["build"])
        self.assertEqual(report["build"]["returncode"], 124)
        self.assertIn("command exceeded", logs["build.log"])

    def test_list_does_not_probe_build_or_create_output(self):
        with mock.patch.object(GATE, "preflight", side_effect=AssertionError("probed")):
            with mock.patch.object(GATE.tempfile, "mkdtemp", side_effect=AssertionError("wrote")):
                self.assertEqual(GATE.main(["--list"]), 0)

    def test_existing_evidence_is_preserved_and_preflight_failures_retained(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            marker = directory / "report.json"
            marker.write_text("preserve")
            self.assertEqual(GATE.main(["--out", temp]), 1)
            self.assertEqual(marker.read_text(), "preserve")
            output = directory / "new"
            with mock.patch.object(GATE, "preflight", side_effect=RuntimeError("missing pinned compiler")):
                self.assertEqual(GATE.main(["--out", str(output)]), 1)
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "fail")
            self.assertEqual(report["errors"], ["missing pinned compiler"])

    def test_backend_identity_refuses_empty_and_symlink_artifacts(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "backend"
            path.write_bytes(b"")
            with self.assertRaisesRegex(RuntimeError, "empty"):
                GATE.backend_identity(path)
            link = Path(temp) / "link"
            link.symlink_to(path)
            with self.assertRaisesRegex(RuntimeError, "symlink"):
                GATE.backend_identity(link)

    def test_snapshot_exclusively_creates_read_only_independent_regular_file(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            backend = directory / "backend"
            backend.write_bytes(b"built backend")
            expected = GATE.backend_identity(backend)
            snapshot = directory / "snapshot"
            observed = GATE.snapshot_backend(backend, snapshot, expected)
            self.assertEqual(observed["sha256"], expected["sha256"])
            self.assertEqual(observed["size"], expected["size"])
            self.assertEqual(stat.S_IMODE(snapshot.stat().st_mode), 0o444)
            self.assertNotEqual(snapshot.stat().st_ino, backend.stat().st_ino)
            for name, kind in (("existing", "file"), ("symlink", "symlink"), ("hardlink", "hardlink")):
                destination = directory / name
                if kind == "file":
                    destination.write_bytes(b"preserve existing evidence")
                elif kind == "symlink":
                    destination.symlink_to(backend)
                else:
                    os.link(backend, destination)
                # Creating a hard link changes the source ctime/link count;
                # use its current identity to isolate exclusive-create refusal.
                current = GATE.backend_identity(backend)
                content = destination.read_bytes()
                with self.subTest(kind=kind), self.assertRaises(FileExistsError):
                    GATE.snapshot_backend(backend, destination, current)
                self.assertEqual(destination.read_bytes(), content)

    def test_snapshot_refuses_source_change_before_or_during_copy(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            backend = directory / "backend"
            backend.write_bytes(b"built backend")
            expected = GATE.backend_identity(backend)
            backend.write_bytes(b"changed before copy")
            with self.assertRaisesRegex(RuntimeError, "changed before"):
                GATE.snapshot_backend(backend, directory / "before", expected)
            self.assertFalse((directory / "before").exists())
            backend.write_bytes(b"built backend")
            expected = GATE.backend_identity(backend)
            # This real write occurs after the last copied byte, before the
            # source fd/path is rechecked. Matching copied bytes cannot hide it.
            original_fsync = os.fsync
            def change_source(fd):
                original_fsync(fd)
                backend.write_bytes(b"changed during copy")
            with mock.patch.object(GATE.os, "fsync", side_effect=change_source):
                with self.assertRaisesRegex(RuntimeError, "changed during"):
                    GATE.snapshot_backend(backend, directory / "during", expected)
            self.assertEqual((directory / "during").read_bytes(), b"built backend")

    def test_preflight_rejects_inherited_backend_or_proof_or_compiler_override(self):
        for name in (
            "TCG_TEST_BACKEND_PATH", "TCG_TEST_BACKEND_SHA256", "TCG_NO_PROOF_CERTS",
            "RUSTC", "CARGO_BUILD_TARGET", "TCG_OPT_LEVEL", "TRUST_CG_DISABLE_PASSES",
            "TRUST_CG_DISABLE_CFGSIMPLIFY_SUBPASSES", "TCG_DATAFLOW_INTEGRITY",
        ):
            with self.subTest(name=name), mock.patch.dict(os.environ, {name: ""}, clear=True):
                with mock.patch.object(GATE.shutil, "which", side_effect=lambda tool: "/fixture/" + tool):
                    with self.assertRaisesRegex(RuntimeError, "rejects ambient"):
                        GATE.preflight(Path("/fixture/cache"))

    @unittest.skipUnless(sys.platform == "linux", "Linux process-group cancellation control")
    def test_cancelling_bridge_build_reaps_signal_resistant_child_and_retains_failure(self):
        for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            with self.subTest(signal=signum), tempfile.TemporaryDirectory() as temp:
                directory = Path(temp)
                ready = directory / "ready"
                output = directory / "result"
                fixture = directory / "blocked-build"
                fixture.write_text(
                    PYTHON_FIXTURE_HEADER +
                    "import os, signal, time\nfrom pathlib import Path\n"
                    "for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):\n"
                    "    signal.signal(signum, signal.SIG_IGN)\n"
                    f"Path({str(ready)!r}).write_text(str(os.getpid()))\n"
                    "time.sleep(60)\n"
                )
                fixture.chmod(0o700)
                runner = (
                    "import runpy, sys; from unittest import mock; "
                    f"gate=runpy.run_path({str(SCRIPT)!r}); "
                    "main=gate['main']; "
                    f"main.__globals__['preflight']=lambda _: {{'source_fingerprint':'same', "
                    "'toolchain':'trust', "
                    f"'compiler_path':{str(directory / 'trustc-fixture')!r}, "
                    f"'tools':{{'env':'/usr/bin/env','targo':{str(fixture)!r},'git':'fixture'}}}}; "
                    "shared=gate['SHARED']; original=shared.run_target; "
                    f"shared.proof_tool_identities=lambda: {PINNED_PROOF_TOOLS!r}; "
                    "shared.run_target=lambda *a, **k: original(*a, **k, grace_seconds=0.05); "
                    "shared.source_provenance=lambda _: {'source_fingerprint':'same'}; "
                    f"sys.exit(main(['--out',{str(output)!r},'--target-dir',{str(directory / 'cache')!r},'--timeout-seconds','60']))"
                )
                supervisor = subprocess.Popen(
                    [sys.executable, "-c", runner], stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, text=True, start_new_session=True,
                )
                child = None
                try:
                    deadline = time.monotonic() + 5
                    while not ready.exists() and time.monotonic() < deadline:
                        time.sleep(0.02)
                    self.assertTrue(ready.exists(), "build never reached its signal-ready state")
                    child = int(ready.read_text())
                    supervisor.send_signal(signum)
                    stdout, stderr = supervisor.communicate(timeout=5)
                    self.assertEqual(supervisor.returncode, 1, (stdout, stderr))
                    report = json.loads((output / "report.json").read_text())
                    self.assertEqual(report["status"], "fail")
                    self.assertEqual(report["build"]["interrupted_signal"], signum)
                    self.assertNotIn("test", report)
                    self.assertFalse(Path(f"/proc/{child}").exists(), "build survived cancellation")
                finally:
                    if supervisor.poll() is None:
                        supervisor.kill()
                        supervisor.communicate(timeout=5)
                    if child is not None and Path(f"/proc/{child}").exists():
                        os.killpg(child, signal.SIGKILL)


if __name__ == "__main__":
    unittest.main()
