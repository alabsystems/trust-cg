"""Tests for scripts/check_aarch64_aot_arithmetic.py with a fake CLI, solver and checker.

The fakes reproduce the exported file layout of the archived 2026-09-17
qualification (object, lowering and trust-proof-cert sidecars, one Arithmetic
and one FrameLayout query per case, nine distinct queries overall) so the
runner's denominator, classification and corruption-control accounting can be
exercised without a trust-cg build, AY or Clean.

The fake objects and executables are not ELF, so matrix runs inject
`fake_binder` for the linked-image step. The real `bind_linked_image` is tested
separately on minimal ELF64 files built here and on the 48 object/executable
pairs archived by the 2026-09-20 Linux run.
"""

from __future__ import annotations

import contextlib
import gzip
import importlib.util
import io
import json
import os
from pathlib import Path
import stat
import struct
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "check_aarch64_aot_arithmetic.py"
SPEC = importlib.util.spec_from_file_location("check_aarch64_aot_arithmetic", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
sys.modules["check_aarch64_aot_arithmetic"] = GATE
SPEC.loader.exec_module(GATE)
# Real CLI exports from reports/perf/2026-09-17-arithmetic-aot-export/records/,
# moved byte for byte; scripts/tests/fixtures/aarch64_aot_arithmetic/README.md.
FIXTURES = ROOT / "scripts/tests/fixtures/aarch64_aot_arithmetic"
ARCHIVE = FIXTURES / "export"
# The 2026-09-20 Linux run retained every case's certified object and linked PIE.
LINKED_ARCHIVE = FIXTURES / "linked-cases"
LINUX = ("linux", "aarch64")
DARWIN = ("darwin", "arm64")


FAKE_CLI = r'''
import hashlib, json, os, sys, time
from pathlib import Path

MAGIC = {"aarch64-unknown-linux-gnu": b"\x7fELF", "aarch64-apple-darwin": b"\xcf\xfa\xed\xfe"}
FRAME_NAME = "Source-bound AArch64 leaf: FP/LR frame memory and writeback"
FRAME_QUERY = "(set-logic QF_BV)\n(declare-const fp (_ BitVec 64))\n(assert (not (= fp fp)))\n(check-sat)\n"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def cert(category, name):
    return {"category": category, "function": "calculate", "hash": 1, "proof_name": name,
            "result": "verified", "solver": "ay", "strength": "Formal", "timestamp": 0, "verified": True}


def ay_identity(env):
    """The AY identity rule, as the real CLI's --print-ay-identity applies it.

    The fixture writes the "compiled-in" record next to this script; a missing
    record is a stock build that records no AY. Nothing is executed. Like the
    real rule it places the admitted bytes in a private content-addressed copy
    under the user cache (0700 directories, 0500 file) and reports it as
    exec_path.
    """
    base = {"schema": "trust-cg.ay-identity.v2"}
    if env.get("FAKE_CLI_IDENTITY_UNSUPPORTED") == "1":
        print("error: unexpected argument '--print-ay-identity' found", file=sys.stderr)
        return 2
    record = Path(__file__).with_name("trust-cg-recorded-ay.sha256")
    value = env.get("AY_SOLVER_PATH")
    if not record.is_file():
        refusal = ("TCG-AY-IDENTITY-UNRECORDED", "the build recorded no toolchain AY identity")
    elif value is None or not os.path.isabs(value):
        refusal = ("TCG-AY-IDENTITY-OVERRIDE-NOT-ABSOLUTE", "AY_SOLVER_PATH is not absolute")
    elif not (os.path.isfile(value) and os.access(value, os.X_OK)):
        refusal = ("TCG-AY-IDENTITY-OVERRIDE-MISSING", "AY_SOLVER_PATH names no executable file")
    else:
        digest = sha(Path(value).read_bytes())
        expected = record.read_text().strip()
        if digest == expected:
            reported = env.get("FAKE_CLI_REPORT_AY_SHA256") or digest
            # The one user-cache rule (private_fs::user_cache_base): only an
            # absolute XDG_CACHE_HOME counts.
            xdg = env.get("XDG_CACHE_HOME") or ""
            cache = xdg if os.path.isabs(xdg) else os.path.join(env["HOME"], ".cache")
            directory = Path(cache, "trust-cg", "ay-exec", digest)
            # Like the real rule, every directory it creates is 0700.
            if not os.path.isdir(cache):
                Path(cache).mkdir(mode=0o700, parents=True)
                Path(cache).chmod(0o700)
            for part in (directory.parent.parent, directory.parent, directory):
                part.mkdir(mode=0o700, parents=True, exist_ok=True)
                part.chmod(0o700)
            copy = directory / "ay"
            if not copy.exists():
                copy.write_bytes(Path(value).read_bytes())
                copy.chmod(0o500)
            exec_path = env.get("FAKE_CLI_REPORT_EXEC_PATH") or str(copy)
            print(json.dumps({**base, "admitted": True, "path": value, "exec_path": exec_path,
                              "sha256": reported, "route": "override-pinned-ay",
                              "recorded": {"sha256": expected}}))
            return 0
        refusal = ("TCG-AY-IDENTITY-MISMATCH", "AY_SOLVER_PATH digests to " + digest + ", recorded " + expected)
    print(json.dumps({**base, "admitted": False, "code": refusal[0], "detail": "[%s] %s" % refusal}))
    return 1


def main():
    args = sys.argv[1:]
    if args == ["--version"]:
        print("trust-cg 0.0.0-fake")
        return 0
    env = os.environ
    if args == ["--print-ay-identity"]:
        return ay_identity(env)
    for name in sorted(env):
        if name.startswith(("TCG_", "TRUST_CG_", "AY_")) and name not in ("AY_SOLVER_PATH", "TCG_EXTERNAL_CLEAN_CHECKER"):
            print("trust-cg: error: ambient " + name + " reached the compiler", file=sys.stderr)
            return 3
    if not (os.path.isabs(env.get("AY_SOLVER_PATH", "")) and os.path.isabs(env.get("TCG_EXTERNAL_CLEAN_CHECKER", ""))):
        print("trust-cg: error: proof authority is not pinned", file=sys.stderr)
        return 3
    assert args[0] == "--format=text" and "-c" in args, args
    target = args[args.index("--target") + 1]
    level = [arg for arg in args if arg.startswith("-O")][0][2:]
    source = Path(args[args.index("-c") + 1])
    proofs = Path(args[args.index("--emit-proofs") + 1])
    obj = Path(args[args.index("-o") + 1])
    case = source.stem + "-O" + level
    if env.get("FAKE_CLI_SLEEP") == case:
        time.sleep(60)
    if env.get("FAKE_CLI_REFUSE_TARGET") == target:
        print("--- proof certificates ---\n  Source-bound AArch64 affine ALU: AddRR [UNVERIFIED]\n--- end proofs ---", file=sys.stderr)
        print("trust-cg: error: proof promotion rejected for 'calculate': fake " + target + " refusal writing "
              + str(obj), file=sys.stderr)
        return 1
    ty, shape = source.stem.split("-")
    width = 32 if ty.endswith("32") else 64
    kind = {"add": "AddRR", "sub": "SubRR"}.get(shape) or ("AddRR" if level == "0" else "LslRI")
    expression = {"add": "(bvadd x y)", "sub": "(bvsub x y)"}.get(shape) or (
        "(bvadd x x)" if level == "0" else "(bvshl x (_ bv1 %d))" % width)
    query = ("(set-logic QF_BV)\n(declare-const x (_ BitVec %d))\n(declare-const y (_ BitVec %d))\n"
             "(assert (not (= %s %s)))\n(check-sat)\n") % (width, width, expression, expression)
    if env.get("FAKE_CLI_QUERY_SALT") == "1":
        query = "; " + case + "\n" + query
    raw_object = MAGIC[target] + b" fake object " + case.encode() + b" " + target.encode()
    if env.get("FAKE_CLI_NO_OBJECT") != case:
        obj.write_bytes(raw_object)
    trust_ir_hash = sha(source.read_bytes() + (level.encode() if env.get("FAKE_CLI_SOURCE_DRIFT") == source.stem else b""))
    object_hash = "0" * 64 if env.get("FAKE_CLI_BAD_HASH") == case else sha(raw_object)
    alu_name = "Source-bound AArch64 affine ALU: %s i%d" % (kind, width)
    rules = []
    for name, check in ((FRAME_NAME, "regalloc"), (alu_name, "instruction_lowering")):
        rules.append({"rule_name": name, "check_kind": check,
                      "result": {"status": "proved", "strength": {"kind": "smt_unsat"}, "solver": "ay_cli", "time_ms": 1},
                      "obligation_hash": "00", "proof_hash": "11"})
    lower = {"schema": "trust-cg.lowering_certificate.v1", "function": "calculate", "target": target,
             "trust_ir_hash": trust_ir_hash, "machine_code_hash": object_hash,
             "compiler_config_hash": sha(b"config " + level.encode()), "rule_proofs": rules,
             "overall_strength": {"kind": "smt_unsat"}, "result": "verified"}
    formula = json.dumps({key: lower[key] for key in (
        "function", "target", "trust_ir_hash", "machine_code_hash", "compiler_config_hash", "rule_proofs")})
    trust = {"version": 2, "function": "calculate", "function_hash": trust_ir_hash,
             "vc_snapshot": {"formula_json": formula},
             "vc_hash": list(hashlib.sha256(("lowering_equivalence:" + formula).encode()).digest()),
             "chain": {"steps": [{"step_type": "CodegenLowering", "input_hash": trust_ir_hash, "output_hash": object_hash}]}}
    for directory in ("Arithmetic", "FrameLayout", "covered_elsewhere"):
        (proofs / directory).mkdir(parents=True, exist_ok=True)
    if env.get("FAKE_CLI_DROP_LOWERING") != case:
        (proofs / "calculate.lowering.json").write_text(json.dumps(lower, indent=2))
    (proofs / "calculate.trust-proof-cert.json").write_text(json.dumps(trust))
    alu = proofs / "Arithmetic" / ("Source-bound_AArch64_affine_ALU__%s_i%d--%s" % (kind, width, sha(query.encode())))
    alu.with_suffix(".smt2").write_text(query)
    alu.with_suffix(".cert").write_text(json.dumps(cert("Arithmetic", alu_name)))
    frame = proofs / "FrameLayout" / "Source-bound_AArch64_leaf__FP_LR_frame_memory_and_writeback"
    frame.with_suffix(".smt2").write_text(FRAME_QUERY)
    frame.with_suffix(".cert").write_text(json.dumps(cert("Frame Layout", FRAME_NAME)))
    (proofs / "covered_elsewhere" / "covered_elsewhere_instruction_0.cert").write_text(json.dumps(
        {"category": "covered_elsewhere", "result": "eval-only", "verified": True}))
    print("trust-cg: compiled 1 function(s) -> " + str(obj), file=sys.stderr)
    return 0


sys.exit(main())
'''

FAKE_AY = r'''
import hashlib, os, sys
from pathlib import Path


def selects(name, text):
    marker = os.environ.get(name)
    return bool(marker) and marker in text


args = sys.argv[1:]
if args == ["--version"]:
    print("ay 0.0.0-fake")
    sys.exit(0)
assert "--strict-proofs" in args and args[args.index("--proof-format") + 1] == "alethe", args
query = Path(args[args.index("-smt2") + 1])
proof = Path(args[args.index("--proof") + 1])
text = query.read_text()
if selects("FAKE_AY_SAT", text):
    print("sat")
    sys.exit(0)
if selects("FAKE_AY_NO_PROOF", text):
    print("unsat")
    sys.exit(0)
digest = hashlib.sha256(query.read_bytes()).hexdigest()
# "(cl )" is still an empty clause for the fake checker, but the recorded
# "(cl)" -> "(cl false)" mutation cannot be applied to it.
empty = "(cl )" if selects("FAKE_AY_SPACED_EMPTY", text) else "(cl)"
proof.write_text("; problem %s\n(assume h1 (not false))\n(step t1 %s :rule resolution :premises (h1))\n" % (digest, empty))
print("unsat")
'''

FAKE_CLEAN = r'''
import hashlib, json, os, re, sys
from pathlib import Path


def selects(name, text):
    marker = os.environ.get(name)
    return bool(marker) and marker in text


args = sys.argv[1:]
if args == ["--version"]:
    print("clean 0.0.0-fake")
    sys.exit(0)
assert args[:2] == ["cert", "verify-external"] and args[3:] == ["--verbose"], args
packet = json.loads(Path(args[2]).read_text())
problem = packet["problem"]
proof = packet["proof"]
digest = hashlib.sha256(problem.encode()).hexdigest()
valid = (packet.get("type") == "alethe_certificate" and packet.get("version") == "1.0"
         and ("; problem " + digest) in proof and ":rule hole" not in proof
         and re.search(r"\(cl\s*\)", proof) is not None)
if selects("FAKE_CLEAN_ACCEPT_ALL", problem):
    valid = True
if selects("FAKE_CLEAN_REJECT_ALL", problem):
    valid = False
if selects("FAKE_CLEAN_CRASH_ON_CONTROLS", problem) and not valid:
    sys.exit(2)
if valid:
    print("External certificate verification: PASSED\n  Proof status: fully verified")
    sys.exit(0)
print("External certificate verification: FAILED")
print("Error: proof_verification_failed: fake rejection", file=sys.stderr)
sys.exit(1)
'''

# Native stubs are created once and linked into place: macOS scans every new
# executable on first launch, which would dominate a 48-case fixture run.
FAKE_CC = r'''#!/bin/sh
if [ "$1" = "--version" ]; then echo "fake cc 1.0"; exit 0; fi
out=""; obj=""; compile_only=""
while [ $# -gt 0 ]; do
  case "$1" in
    -o) out="$2"; shift 2 ;;
    -c) compile_only=1; shift ;;
    *.o) obj="$1"; shift ;;
    *) shift ;;
  esac
done
if [ -n "$compile_only" ]; then
  if [ -n "$FAKE_CC_FOREIGN_FAIL" ]; then echo "cc: error: fake foreign compile failure" >&2; exit 1; fi
  echo "fake foreign calculate object" > "$out"; exit 0
fi
name=$(basename "$obj" .o)
stubs=$(dirname "$0")
if [ "$FAKE_CC_FAIL" = "$name" ]; then echo "ld: error: undefined symbol: calculate" >&2; exit 1; fi
if [ "$name" = "foreign-calculate" ] || [ "$FAKE_IMAGE_FOREIGN" = "$name" ]; then
  ln -s "$stubs/native-foreign" "$out"
elif [ "$FAKE_NATIVE_WRONG" = "$name" ]; then
  ln -s "$stubs/native-wrong" "$out"
elif [ "$FAKE_NATIVE_SLEEP" = "$name" ]; then
  ln -s "$stubs/native-sleep" "$out"
else
  ln -s "$stubs/native-ok" "$out"
fi
'''
NATIVE_STUBS = {
    "native-ok": '#!/bin/sh\necho "ARITHMETIC_AOT_NATIVE calls=144"\n',
    "native-wrong": '#!/bin/sh\necho "ARITHMETIC_AOT_NATIVE calls=143"\nexit 1\n',
    "native-sleep": "#!/bin/sh\nexec sleep 30\n",
    # Runs like native-ok but is a different image: what a foreign link produces.
    "native-foreign": '#!/bin/sh\n# foreign\necho "ARITHMETIC_AOT_NATIVE calls=144"\n',
}
BOUND_STUBS = {NATIVE_STUBS[name].encode() for name in ("native-ok", "native-wrong", "native-sleep")}


def fake_binder(object_bytes, image_bytes, target):
    """Stand-in for bind_linked_image over the fakes' non-ELF files.

    A fake object binds to an unmodified stub other than native-foreign. The
    stub's first word stands for the function and its second for the FDE
    pc_begin field, so the runner's two in-place patches and its foreign link
    must all be refused, exactly as the real check refuses them.
    """
    if b" fake object " not in object_bytes:
        raise GATE.LinkedImageFailure(GATE.LINKED_IMAGE_UNSUPPORTED, "not a fake object")
    if image_bytes not in BOUND_STUBS:
        raise GATE.LinkedImageFailure(GATE.LINKED_IMAGE_MISMATCH, "image is not an unmodified bound stub")
    return {"status": "bound", "image_sha256": GATE.sha256_bytes(image_bytes), "function_file_offset": 0,
            "function_size": 4, "relocation_effects": [{"field_file_offset": 4, "status": "checked"}]}


def executable(path: Path, text: str) -> Path:
    path.write_text(text)
    path.chmod(path.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    return path


def python_tool(directory: Path, name: str, source: str, reexec: bool = False) -> Path:
    script = directory / f"{name}_impl.py"
    script.write_text(textwrap.dedent(source))
    prelude = 'if [ -z "$FAKE_REEXECED" ]; then FAKE_REEXECED=1 exec "$0" "$@"; fi\n' if reexec else ""
    return executable(directory / name, f'#!/bin/sh\n{prelude}exec "{sys.executable}" -S -E "{script}" "$@"\n')


def direct_executor(command, *, cwd, env, timeout_seconds, log_stem):
    """Mirror run_with_timeout's contract in-process so fixture runs stay fast."""
    stdout_path = log_stem.parent / (log_stem.name + ".stdout.log")
    stderr_path = log_stem.parent / (log_stem.name + ".stderr.log")
    started = time.monotonic()
    with stdout_path.open("xb") as stdout, stderr_path.open("xb") as stderr:
        try:
            returncode = subprocess.run(
                list(command), cwd=cwd, env=dict(env), stdout=stdout, stderr=stderr,
                stdin=subprocess.DEVNULL, timeout=timeout_seconds, check=False,
            ).returncode
        except subprocess.TimeoutExpired:
            stderr.write(f"{GATE.TIMEOUT_LINE} {timeout_seconds:g}s (test executor)\n".encode())
            returncode = GATE.TIMEOUT_EXIT
    return GATE.finish_execution(command, returncode, stdout_path, stderr_path, started, timeout_seconds)


def clean_provenance():
    return {"dirty": False, "source_fingerprint": "f" * 64, "source_sha": "0" * 40}


class Fixture:
    def __init__(self, directory: Path):
        self.directory = directory
        self.bin = directory / "bin"
        self.bin.mkdir()
        self.home = directory / "home"
        # Private whatever the umask, as a real home is: the runner starts the
        # private AY copy below it only when no other user can rename an entry
        # along its canonical path (the real CLI would refuse it otherwise).
        self.home.mkdir(mode=0o700)
        self.home.chmod(0o700)
        self.cli = python_tool(self.bin, "trust-cg", FAKE_CLI)
        # Like the real AY, the fake re-executes itself by its own path at
        # startup before it answers.
        self.ay = python_tool(self.bin, "fake-ay", FAKE_AY, reexec=True)
        # The fake CLI's "compiled-in" AY identity record: the fake AY's bytes.
        self.ay_record = self.bin / "trust-cg-recorded-ay.sha256"
        self.ay_record.write_text(GATE.sha256_file(self.ay) + "\n")
        self.clean = python_tool(self.bin, "fake-clean", FAKE_CLEAN)
        self.cc = executable(self.bin / "cc", FAKE_CC)
        for name, text in NATIVE_STUBS.items():
            executable(self.bin / name, text)
        self.runs = 0

    def environ(self, **extra):
        environ = {
            "PATH": f"{self.bin}{os.pathsep}/usr/bin{os.pathsep}/bin", "HOME": str(self.home),
            "AY_SOLVER_PATH": str(self.ay), "TCG_EXTERNAL_CLEAN_CHECKER": str(self.clean),
        }
        environ.update(extra)
        return environ

    def options(self, **overrides):
        self.runs += 1
        out = self.directory / f"out-{self.runs}"
        out.mkdir()
        # Classification tests need every step to FINISH; a timeout here turns the deliberately
        # mismatching native case into `native-timeout` and the query-dependent checker case into a
        # checker timeout, so the assertion measures the machine's load rather than the classifier
        # (F-164: red on origin/main itself at load 34, and at load 10-49 on a branch). The one test
        # that exercises timeouts passes its own small bounds explicitly and is unaffected.
        values = dict(out=out, trust_cg=self.cli, cc="cc", compile_timeout=300.0, link_timeout=300.0,
                      native_timeout=300.0, solver_timeout=300.0, checker_timeout=300.0)
        values.update(overrides)
        return GATE.Options(**values)

    def run(self, host=LINUX, environ=None, provenance=clean_provenance, executor=direct_executor,
            binder=fake_binder, **overrides):
        options = self.options(**overrides)
        with contextlib.redirect_stdout(io.StringIO()):
            report = GATE.run_matrix(
                options, self.environ() if environ is None else environ,
                executor=executor, host=host, provenance=provenance, binder=binder,
            )
        stored = json.loads((options.out / "report.json").read_text())
        assert stored == json.loads(json.dumps(report)), "the retained report must equal the returned one"
        return report


def cases_by_name(report):
    return {row["name"]: row for row in report["cases"]}


class DenominatorAndInventoryTests(unittest.TestCase):
    def test_denominator_is_the_exact_48_case_product(self):
        cases = GATE.required_cases()
        self.assertEqual(GATE.TYPES, ("i32", "u32", "i64", "u64"))
        self.assertEqual(GATE.SHAPES, ("add", "sub", "double"))
        self.assertEqual(GATE.OPT_LEVELS, (0, 1, 2, 3))
        self.assertEqual((GATE.REQUIRED_CASES, GATE.CALLS_PER_CASE, GATE.REQUIRED_CALLS), (48, 144, 6912))
        self.assertEqual(GATE.EXPECTED_DISTINCT_QUERIES, 9)
        self.assertEqual(GATE.CORRUPTION_CONTROLS, ("hole", "no-empty-clause", "opposite-premise"))
        self.assertEqual(len(cases), 48)
        self.assertEqual(len({case.name for case in cases}), 48)
        self.assertEqual(GATE.denominator_errors(cases), [])
        # The archived native run executed exactly these case names in this order.
        archived = gzip.decompress((ARCHIVE / "harness/run-aot-arithmetic-native-first.log.gz").read_bytes()).decode()
        self.assertEqual([line.split()[0] for line in archived.splitlines()], [case.name for case in cases])

    def test_denominator_errors_reject_dropped_duplicated_and_foreign_cases(self):
        cases = list(GATE.required_cases())
        self.assertIn("missing cases", " ".join(GATE.denominator_errors(cases[:-1])))
        self.assertIn("duplicate cases", " ".join(GATE.denominator_errors(cases[:-1] + [cases[0]])))
        foreign = cases[:-1] + [GATE.Case("i16", "add", 0)]
        errors = " ".join(GATE.denominator_errors(foreign))
        self.assertIn("outside the denominator", errors)
        self.assertIn("missing cases", errors)
        with mock.patch.object(GATE, "OPT_LEVELS", (0, 1, 2)):
            self.assertIn("does not equal 48 cases", " ".join(GATE.denominator_errors(GATE.required_cases())))

    def test_generated_inputs_are_byte_identical_to_the_archived_harness(self):
        native = ARCHIVE / "aot-arithmetic-native-first"
        for ty in GATE.TYPES:
            for shape in GATE.SHAPES:
                with self.subTest(ty=ty, shape=shape):
                    self.assertEqual(
                        GATE.trust_ir_source(ty, shape).encode(),
                        gzip.decompress((native / f"{ty}-{shape}.trust_ir.gz").read_bytes()),
                    )
                    self.assertEqual(
                        GATE.oracle_source(ty, shape).encode(),
                        gzip.decompress((native / f"{ty}-{shape}.c.gz").read_bytes()),
                    )
        self.assertIn(GATE.NATIVE_MARKER, GATE.oracle_source("u64", "sub"))

    def test_corruption_controls_reproduce_the_archived_certificate_packets(self):
        independent = ARCHIVE / "aot-arithmetic-independent-first"
        for index in range(GATE.EXPECTED_DISTINCT_QUERIES):
            name = f"alu-{index:02d}"
            with self.subTest(query=name):
                original_bytes = gzip.decompress((independent / f"{name}-original.json.gz").read_bytes())
                original = json.loads(original_bytes)
                self.assertEqual(GATE.packet_bytes(original), original_bytes)
                controls = GATE.corruption_controls(original)
                self.assertEqual([label for label, _ in controls], list(GATE.CORRUPTION_CONTROLS))
                for label, value in controls:
                    self.assertIsNotNone(value, label)
                    self.assertEqual(
                        GATE.packet_bytes(value),
                        gzip.decompress((independent / f"{name}-{label}.json.gz").read_bytes()),
                        label,
                    )

    def test_unconstructible_controls_are_marked_not_silently_passed(self):
        certificate = {"type": "alethe_certificate", "version": "1.0",
                       "problem": "(assert a)\n(assert b)\n", "proof": "(step t1 (cl false) :rule hole)"}
        self.assertEqual([value for _, value in GATE.corruption_controls(certificate)], [None, None, None])
        self.assertIsNone(GATE.opposite_premise("(check-sat)\n"))
        self.assertIsNone(GATE.opposite_premise("(assert (unbalanced"))
        self.assertEqual(GATE.opposite_premise("(assert (= a b))\n"), "(assert (not (= a b)))\n")


class ArchivedArtifactAuditTests(unittest.TestCase):
    """The ported audit accepts every archived real CLI export and rejects its mutations."""

    NATIVE = ARCHIVE / "aot-arithmetic-native-first"

    def materialize(self, name: str, destination: Path) -> tuple:
        proofs = destination / "proofs"
        for packed in sorted((self.NATIVE / f"{name}-proofs").rglob("*.gz")):
            target = proofs / packed.relative_to(self.NATIVE / f"{name}-proofs").with_suffix("")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(gzip.decompress(packed.read_bytes()))
        obj = destination / f"{name}.o"
        obj.write_bytes(gzip.decompress((self.NATIVE / f"{name}.o.gz").read_bytes()))
        return proofs, obj

    def test_every_archived_case_passes_the_ported_audit(self):
        queries = set()
        identities = {}
        with tempfile.TemporaryDirectory() as temp:
            for case in GATE.required_cases():
                with self.subTest(case=case.name):
                    proofs, obj = self.materialize(case.name, Path(temp) / case.name)
                    audit = GATE.audit_case(proofs, obj, "aarch64-unknown-linux-gnu")
                    self.assertEqual(sorted(row["category"] for row in audit["queries"]), ["Arithmetic", "FrameLayout"])
                    queries.update(row["sha256"] for row in audit["queries"])
                    identities.setdefault(case.stem, set()).add(audit["trust_ir_hash"])
        self.assertEqual(len(queries), GATE.EXPECTED_DISTINCT_QUERIES)
        self.assertEqual({stem: len(values) for stem, values in identities.items()},
                         {f"{ty}-{shape}": 1 for ty in GATE.TYPES for shape in GATE.SHAPES})

    def test_mutated_archived_exports_are_rejected_with_named_classes(self):
        def mutate_json(path: Path, change) -> None:
            value = json.loads(path.read_text())
            change(value)
            path.write_text(json.dumps(value))

        def set_key(key, value):
            return lambda document: document.__setitem__(key, value)

        def undomained_vc_hash(document) -> None:
            # The first archived audit draft's mistake: hashing without "lowering_equivalence:".
            formula = document["vc_snapshot"]["formula_json"].encode()
            document["vc_hash"] = list(bytes.fromhex(GATE.sha256_bytes(formula)))

        mutations = {
            "object byte": (GATE.SIDECAR_MISMATCH, lambda p, o: o.write_bytes(
                o.read_bytes()[:-1] + bytes([o.read_bytes()[-1] ^ 0xFF]))),
            "wrong target": (GATE.SIDECAR_MISMATCH, None),
            "missing lowering": (GATE.CERTIFICATE_MISSING, lambda p, o: (p / "calculate.lowering.json").unlink()),
            "missing trust cert": (GATE.CERTIFICATE_MISSING,
                                   lambda p, o: (p / "calculate.trust-proof-cert.json").unlink()),
            "missing object": (GATE.OBJECT_MISSING, lambda p, o: o.unlink()),
            "vc hash without domain": (GATE.SIDECAR_MISMATCH, lambda p, o: mutate_json(
                p / "calculate.trust-proof-cert.json", undomained_vc_hash)),
            "statistical rule": (GATE.SIDECAR_MISMATCH, lambda p, o: mutate_json(
                p / "calculate.lowering.json",
                lambda d: d["rule_proofs"][1]["result"].__setitem__("strength", {"kind": "statistical"}))),
            "unverified audit record": (GATE.SIDECAR_MISMATCH, lambda p, o: mutate_json(
                next((p / "covered_elsewhere").glob("*.cert")), set_key("verified", False))),
            "query renamed": (GATE.SIDECAR_MISMATCH, lambda p, o: [
                path.rename(path.with_name(path.name.replace(path.name.split("--", 1)[1].split(".")[0], "0" * 64)))
                for path in list((p / "Arithmetic").iterdir())]),
            "query metadata missing": (GATE.CERTIFICATE_MISSING, lambda p, o: [
                path.unlink() for path in (p / "Arithmetic").glob("*.cert")]),
            "missing arithmetic query": (GATE.SIDECAR_MISMATCH, lambda p, o: [
                path.unlink() for path in (p / "Arithmetic").glob("*.smt2")]),
            "non-formal query metadata": (GATE.SIDECAR_MISMATCH, lambda p, o: mutate_json(
                next((p / "FrameLayout").glob("*.cert")), set_key("strength", "Statistical"))),
            # A valid theorem that is not the one the sidecar records as proved.
            "query names another rule": (GATE.SIDECAR_MISMATCH, lambda p, o: mutate_json(
                next((p / "Arithmetic").glob("*.cert")),
                set_key("proof_name", "Source-bound AArch64 affine ALU: AddRR i64"))),
            "query for another function": (GATE.SIDECAR_MISMATCH, lambda p, o: mutate_json(
                next((p / "FrameLayout").glob("*.cert")), set_key("function", "other"))),
        }
        with tempfile.TemporaryDirectory() as temp:
            for label, (failure_class, mutate) in mutations.items():
                with self.subTest(mutation=label):
                    proofs, obj = self.materialize("i64-double-O2", Path(temp) / label.replace(" ", "-"))
                    target = "aarch64-unknown-linux-gnu"
                    if mutate is None:
                        target = "aarch64-apple-darwin"
                    else:
                        mutate(proofs, obj)
                    with self.assertRaises(GATE.AuditFailure) as caught:
                        GATE.audit_case(proofs, obj, target)
                    self.assertEqual(caught.exception.failure_class, failure_class, caught.exception.detail)


# ---------------------------------------------------------------------------
# Minimal ELF64 AArch64 fixtures for the linked-image check
# ---------------------------------------------------------------------------

ELF_LINUX = "aarch64-unknown-linux-gnu"
LEAF = (0xA9BF7BFD, 0x910003FD, 0x0B010000, 0xA8C17BFD, 0xD65F03C0)  # stp, mov x29, add, ldp, ret
CIE_PROGRAM = bytes([0x0C, 0x1F, 0x00])  # DW_CFA_def_cfa sp, 0
FDE_PROGRAM = bytes([0x41, 0x0E, 0x10, 0x9D, 0x02, 0x9E, 0x01, 0x41, 0x0C, 0x1D, 0x10])
GLOBAL_FUNC, LOCAL_FUNC, LOCAL_SECTION = 0x12, 0x02, 0x03
TEXT_VA, HDR_VA, EH_FRAME_VA, FUNCTION_VA = 0x100, 0x180, 0x200, 0x108


def uleb(value: int) -> bytes:
    out = bytearray()
    while True:
        byte, value = value & 0x7F, value >> 7
        out.append(byte | (0x80 if value else 0))
        if not value:
            return bytes(out)


def sleb(value: int) -> bytes:
    out = bytearray()
    while True:
        byte, value = value & 0x7F, value >> 7
        if (value == 0 and not byte & 0x40) or (value == -1 and byte & 0x40):
            out.append(byte)
            return bytes(out)
        out.append(byte | 0x80)


def words(values) -> bytes:
    return b"".join(struct.pack("<I", value) for value in values)


def cie_record(padding: int) -> bytes:
    body = (struct.pack("<I", 0) + b"\x01zR\x00" + uleb(4) + sleb(-8) + bytes([30]) + uleb(1) + bytes([0x1B])
            + CIE_PROGRAM + bytes(padding))
    return struct.pack("<I", len(body)) + body


def fde_record(offset: int, pc_begin: int, pc_range: int, program: bytes, padding: int) -> bytes:
    body = struct.pack("<Iii", offset + 4, pc_begin, pc_range) + uleb(0) + program + bytes(padding)
    return struct.pack("<I", len(body)) + body


def symbol_table(rows) -> tuple:
    strings, table = bytearray(b"\0"), bytearray(24)
    for name, info, shndx, value, size in rows:
        offset = 0
        if name:
            offset = len(strings)
            strings += name.encode() + b"\0"
        table += struct.pack("<IBBHQQ", offset, info, 0, shndx, value, size)
    return bytes(table), bytes(strings)


def elf_file(e_type: int, sections: list, segments=(), machine: int = 183) -> bytes:
    """Lay out an ELF64 LE file: header, program headers, sections, .shstrtab, section headers."""
    names = bytearray(b"\0")
    name_offsets = []
    for section in sections + [{"name": ".shstrtab"}]:
        name_offsets.append(len(names))
        names += section["name"].encode() + b"\0"
    blob = bytearray(64 + 56 * len(segments))
    offsets = []
    for section in sections:
        offset = section.get("offset", (len(blob) + 7) & ~7)
        assert offset >= len(blob), "fixture sections overlap"
        blob += bytes(offset - len(blob)) + section["data"]
        offsets.append(offset)
    names_offset = len(blob)
    blob += names
    shoff = (len(blob) + 7) & ~7
    blob += bytes(shoff - len(blob)) + bytes(64)
    for index, section in enumerate(sections):
        blob += struct.pack("<IIQQQQIIQQ", name_offsets[index], section["type"], section.get("flags", 0),
                            section.get("addr", 0), offsets[index], len(section["data"]), section.get("link", 0),
                            section.get("info", 0), 8, section.get("entsize", 0))
    blob += struct.pack("<IIQQQQIIQQ", name_offsets[-1], 3, 0, 0, names_offset, len(names), 0, 0, 1, 0)
    shnum = len(sections) + 2
    blob[0:64] = (b"\x7fELF" + bytes([2, 1, 1]) + bytes(9) + struct.pack(
        "<HHIQQQIHHHHHH", e_type, machine, 1, 0, 64 if segments else 0, shoff, 0, 64, 56 if segments else 0,
        len(segments), 64, shnum, shnum - 1))
    for index, (p_type, flags, offset, vaddr, size) in enumerate(segments):
        blob[64 + 56 * index:120 + 56 * index] = struct.pack("<IIQQQQQQ", p_type, flags, offset, vaddr, vaddr,
                                                             size, size, 0x10000)
    return bytes(blob)


def minimal_object(code=LEAF, *, text_relocation=False, trailing_text=b"", fde_range=None, machine=183) -> bytes:
    """What trust-cg emits for the leaf: one global function filling .text, one PREL32 FDE."""
    text = words(code) + trailing_text
    cie = cie_record(4)
    eh_frame = cie + fde_record(len(cie), 0, 4 * len(code) if fde_range is None else fde_range, FDE_PROGRAM, 4)
    table, strings = symbol_table([("", LOCAL_SECTION, 1, 0, 0), ("calculate", GLOBAL_FUNC, 1, 0, 4 * len(code))])
    sections = [
        {"name": ".text", "type": 1, "flags": 0x6, "data": text},
        {"name": ".eh_frame", "type": 1, "flags": 0x2, "data": eh_frame},
        {"name": ".rela.eh_frame", "type": 4, "flags": 0x40, "link": 4, "info": 2, "entsize": 24,
         "data": struct.pack("<QQq", len(cie) + 8, (1 << 32) | GATE.R_AARCH64_PREL32, 0)},
        {"name": ".symtab", "type": 2, "link": 5, "info": 2, "entsize": 24, "data": table},
        {"name": ".strtab", "type": 3, "data": strings},
    ]
    if text_relocation:
        sections.append({"name": ".rela.text", "type": 4, "flags": 0x40, "link": 4, "info": 1, "entsize": 24,
                         "data": struct.pack("<QQq", 8, (1 << 32) | 283, 0)})
    return elf_file(1, sections, machine=machine)


def minimal_image(code=LEAF, *, symbol_size=None, duplicate=False, flags=5, pc_begin_delta=0, fde_range=None,
                  program=FDE_PROGRAM, header=True, header_delta=0, symtab=True, machine=183) -> bytes:
    """A PIE-shaped ET_DYN: other code, then the function at FUNCTION_VA, with linker-trimmed CFI."""
    text = words((GATE.AARCH64_NOP, 0xD65F03C0)) + words(code)
    cie = cie_record(0)
    other_offset = len(cie)
    other = fde_record(other_offset, TEXT_VA - (EH_FRAME_VA + other_offset + 8), 8, b"", 3)
    fde_offset = other_offset + len(other)
    eh_frame = cie + other + fde_record(
        fde_offset, FUNCTION_VA - (EH_FRAME_VA + fde_offset + 8) + pc_begin_delta,
        4 * len(code) if fde_range is None else fde_range, program, 0) + bytes(4)
    entries = [(TEXT_VA, EH_FRAME_VA + other_offset), (FUNCTION_VA, EH_FRAME_VA + fde_offset + header_delta)]
    hdr = struct.pack("<BBBBiI", 1, 0x1B, 0x03, 0x3B, EH_FRAME_VA - (HDR_VA + 4), len(entries)) + b"".join(
        struct.pack("<ii", location - HDR_VA, fde - HDR_VA) for location, fde in entries)
    rows = [("", LOCAL_SECTION, 1, TEXT_VA, 0),
            ("calculate", GLOBAL_FUNC, 1, FUNCTION_VA, 4 * len(code) if symbol_size is None else symbol_size)]
    if duplicate:
        rows.append(("calculate", LOCAL_FUNC, 1, TEXT_VA, 4 * len(code)))
    table, strings = symbol_table(rows)
    sections = [{"name": ".text", "type": 1, "flags": 0x6, "addr": TEXT_VA, "offset": TEXT_VA, "data": text}]
    if header:
        sections.append({"name": ".eh_frame_hdr", "type": 1, "flags": 0x2, "addr": HDR_VA, "offset": HDR_VA,
                         "data": hdr})
    sections.append({"name": ".eh_frame", "type": 1, "flags": 0x2, "addr": EH_FRAME_VA, "offset": EH_FRAME_VA,
                     "data": eh_frame})
    if symtab:
        strtab_index = len(sections) + 2
        sections += [{"name": ".symtab", "type": 2, "link": strtab_index, "info": 2, "entsize": 24, "data": table},
                     {"name": ".strtab", "type": 3, "data": strings}]
    end = EH_FRAME_VA + len(eh_frame)
    return elf_file(3, sections, [(1, flags, 0, 0, end)], machine=machine)


class LinkedImageFixtureTests(unittest.TestCase):
    """bind_linked_image on minimal ELF64 files whose every field the test controls."""

    def refused(self, failure_class, object_bytes=None, image_bytes=None, target=ELF_LINUX):
        with self.assertRaises(GATE.LinkedImageFailure) as caught:
            GATE.bind_linked_image(object_bytes or minimal_object(), image_bytes or minimal_image(), target)
        self.assertEqual(caught.exception.failure_class, failure_class, caught.exception.detail)
        return caught.exception.detail

    def test_minimal_pair_binds_with_its_link_time_address_and_prel32_effect(self):
        image = minimal_image()
        record = GATE.bind_linked_image(minimal_object(), image, ELF_LINUX)
        self.assertEqual(record["status"], "bound")
        self.assertEqual(record["image_sha256"], GATE.sha256_bytes(image))
        self.assertEqual((record["image_type"], record["function_va"], record["function_file_offset"],
                          record["function_size"], record["function_words"], record["function_section"]),
                         ("ET_DYN", FUNCTION_VA, FUNCTION_VA, 20, 5, ".text"))
        self.assertEqual(record["object_text_sha256"], GATE.sha256_bytes(words(LEAF)))
        self.assertEqual(record["linked_function_sha256"], record["object_text_sha256"])
        self.assertEqual(record["object_relocations"], {"total": 1, "text": 0, "by_section": {".eh_frame": 1}})
        self.assertEqual(record["load_segment"]["flags"], "R-X")
        (effect,) = record["relocation_effects"]
        self.assertEqual((effect["type"], effect["symbol"], effect["addend"], effect["status"], effect["resolves_to"],
                          effect["pc_range"]), ("R_AARCH64_PREL32", ".text", 0, "checked", FUNCTION_VA, 20))
        field = effect["field_file_offset"]
        self.assertEqual(effect["field_va"], field)  # the fixture maps file offsets 1:1
        self.assertEqual(field + struct.unpack_from("<i", image, field)[0], FUNCTION_VA)
        self.assertEqual(record["eh_frame_hdr"], {"status": "checked", "entries": 2, "entry_index": 1,
                                                  "fde_va": effect["fde_va"]})
        self.assertTrue(record["unchecked"])

    def test_every_single_word_patch_is_refused_at_its_word(self):
        image = minimal_image()
        for index in range(len(LEAF)):
            with self.subTest(word=index):
                site = FUNCTION_VA + 4 * index
                patched = image[:site] + struct.pack("<I", GATE.AARCH64_BRK_0) + image[site + 4:]
                detail = self.refused(GATE.LINKED_IMAGE_MISMATCH, image_bytes=patched)
                self.assertIn(f"1 of 5 instruction word(s) of linked 'calculate' differ", detail)
                self.assertIn(f"first at word {index} (VA {site:#x}", detail)

    def test_the_runner_patches_are_refused_and_record_their_sites(self):
        image = minimal_image()
        record = GATE.bind_linked_image(minimal_object(), image, ELF_LINUX)
        patches = GATE.linked_image_patches(image, record)
        self.assertEqual([label for label, _, _ in patches], list(GATE.LINKED_IMAGE_CONTROLS[:2]))
        (word_label, word_image, word_info), (fde_label, fde_image, fde_info) = patches
        self.assertEqual((word_info["file_offset"], word_info["original_word"], word_info["patched_word"]),
                         (FUNCTION_VA + 16, LEAF[-1], GATE.AARCH64_NOP))
        self.assertIn("first at word 4", self.refused(GATE.LINKED_IMAGE_MISMATCH, image_bytes=word_image))
        self.assertEqual(fde_info["file_offset"], record["relocation_effects"][0]["field_file_offset"])
        self.assertEqual((fde_info["patched_word"] - fde_info["original_word"]) % (1 << 32), 4)
        self.assertIn("0 linked FDEs resolve pc_begin", self.refused(GATE.LINKED_IMAGE_MISMATCH, image_bytes=fde_image))
        # A function that is already a NOP is patched to BRK #0, never to itself.
        nop_image = minimal_image(LEAF[:-1] + (GATE.AARCH64_NOP,))
        nop_record = GATE.bind_linked_image(minimal_object(LEAF[:-1] + (GATE.AARCH64_NOP,)), nop_image, ELF_LINUX)
        self.assertEqual(GATE.linked_image_patches(nop_image, nop_record)[0][2]["patched_word"], GATE.AARCH64_BRK_0)
        # A record without sites yields unconstructible patches, not silent passes.
        self.assertEqual([patched for _, patched, _ in GATE.linked_image_patches(image, {})], [None, None])

    def test_linked_image_defects_are_mismatches(self):
        cases = {
            "differing word": (minimal_image(LEAF[:2] + (0x4B010000,) + LEAF[3:]), "first at word 2"),
            "resized symbol": (minimal_image(symbol_size=16), "is 16 bytes; the certified .text is 20 bytes"),
            "duplicate definition": (minimal_image(duplicate=True), "defines 'calculate' 2 times"),
            "stripped image": (minimal_image(symtab=False), "0 .symtab sections"),
            "non-executable segment": (minimal_image(flags=4), "is not executable"),
            "moved FDE pc_begin": (minimal_image(pc_begin_delta=-4), "0 linked FDEs resolve pc_begin"),
            "FDE range": (minimal_image(fde_range=16), "differs from the certified object's CIE/FDE"),
            "FDE program": (minimal_image(program=FDE_PROGRAM[:-1] + b"\x11"), "differs from the certified object"),
            "eh_frame_hdr entry": (minimal_image(header_delta=4), ".eh_frame_hdr has 1 search entries"),
            "truncated": (minimal_image()[:FUNCTION_VA + 8], "outside the"),
            "other machine": (minimal_image(machine=62), "is not AArch64"),
            "not ELF": (b"#!/bin/sh\nexit 0\n", "not an ELF file"),
        }
        for label, (image, expected) in cases.items():
            with self.subTest(defect=label):
                self.assertIn(expected, self.refused(GATE.LINKED_IMAGE_MISMATCH, image_bytes=image))

    def test_absent_eh_frame_hdr_is_recorded_not_assumed(self):
        record = GATE.bind_linked_image(minimal_object(), minimal_image(header=False), ELF_LINUX)
        self.assertEqual(record["eh_frame_hdr"], {"status": "absent"})
        self.assertEqual(record["relocation_effects"][0]["status"], "checked")

    def test_objects_outside_the_model_are_unsupported(self):
        cases = {
            "text relocation": (minimal_object(text_relocation=True), "patch the certified .text"),
            "function is not the whole .text": (minimal_object(trailing_text=bytes(4)), "is not the whole"),
            "FDE does not cover the function": (minimal_object(fde_range=16), "does not cover exactly"),
            "other machine": (minimal_object(machine=62), "is not AArch64"),
            "fake object": (b"\x7fELF fake object", "shorter than an ELF64 header"),
        }
        for label, (obj, expected) in cases.items():
            with self.subTest(object=label):
                self.assertIn(expected, self.refused(GATE.LINKED_IMAGE_UNSUPPORTED, object_bytes=obj))

    def test_mach_o_targets_are_unsupported_not_skipped(self):
        detail = self.refused(GATE.LINKED_IMAGE_UNSUPPORTED, target="aarch64-apple-darwin")
        self.assertIn("parses ELF64 only", detail)


class ArchivedLinkedImageTests(unittest.TestCase):
    """The check over the 48 real object/PIE pairs retained by the 2026-09-20 Linux run (c45c4d3f)."""

    @classmethod
    def setUpClass(cls):
        cls.pairs = {}
        for case in GATE.required_cases():
            directory = LINKED_ARCHIVE / case.name
            cls.pairs[case.name] = (gzip.decompress((directory / f"{case.name}.o.gz").read_bytes()),
                                    gzip.decompress((directory / f"{case.name}.gz").read_bytes()))

    def test_every_archived_pie_carries_its_certified_function(self):
        for case in GATE.required_cases():
            with self.subTest(case=case.name):
                obj, image = self.pairs[case.name]
                record = GATE.bind_linked_image(obj, image, ELF_LINUX)
                # O0 keeps the FP/LR frame around a 32-bit (8 words) or 64-bit (6 words) body.
                size = 20 if case.opt_level else (32 if case.type.endswith("32") else 24)
                self.assertEqual((record["image_type"], record["function_va"], record["function_size"]),
                                 ("ET_DYN", 0x958, size))
                self.assertEqual(record["object_relocations"], {"total": 1, "text": 0, "by_section": {".eh_frame": 1}})
                self.assertEqual(record["relocation_effects"][0]["resolves_to"], 0x958)
                self.assertEqual(record["eh_frame_hdr"]["status"], "checked")
                for label, patched, _ in GATE.linked_image_patches(image, record):
                    with self.assertRaises(GATE.LinkedImageFailure, msg=label) as caught:
                        GATE.bind_linked_image(obj, patched, ELF_LINUX)
                    self.assertEqual(caught.exception.failure_class, GATE.LINKED_IMAGE_MISMATCH, label)

    def test_a_swapped_certified_object_is_refused_unless_the_objects_are_identical(self):
        # Every other case at the same optimization level: 12 x 11 x 4 swaps.
        refused = identical = 0
        for case in GATE.required_cases():
            for other in GATE.required_cases():
                if other.opt_level != case.opt_level or other == case:
                    continue
                obj = self.pairs[case.name][0]
                image = self.pairs[other.name][1]
                if obj == self.pairs[other.name][0]:
                    # Byte-identical objects share one machine_code_hash: not a swap.
                    GATE.bind_linked_image(obj, image, ELF_LINUX)
                    identical += 1
                    continue
                with self.assertRaises(GATE.LinkedImageFailure, msg=f"{case.name} <- {other.name}") as caught:
                    GATE.bind_linked_image(obj, image, ELF_LINUX)
                self.assertEqual(caught.exception.failure_class, GATE.LINKED_IMAGE_MISMATCH)
                refused += 1
        self.assertEqual(refused + identical, 528)
        self.assertGreater(refused, 0)


class PathParameterizationTests(unittest.TestCase):
    def test_runner_names_no_host_local_paths(self):
        text = SCRIPT.read_text()
        for fragment in ("/home/", "/Users/", "ayates", "/tmp/", "trust-cg-soundness"):
            self.assertNotIn(fragment, text)

    def test_commands_are_built_only_from_parameterized_paths(self):
        case = GATE.Case("u32", "double", 2)
        command = GATE.compile_command(Path("/x/cli"), "aarch64-apple-darwin", case, Path("/o/in.trust_ir"),
                                       Path("/o/proofs"), Path("/o/obj.o"))
        self.assertEqual(command, ["/x/cli", "--format=text", "--permit-unlicensed", "--target", "aarch64-apple-darwin", "-O2", "-c",
                                   "/o/in.trust_ir", "--emit-proofs", "/o/proofs", "-o", "/o/obj.o"])
        self.assertEqual(GATE.link_command(Path("/c/cc"), Path("/o/d.c"), Path("/o/o.o"), Path("/o/e")),
                         ["/c/cc", "-O2", "-std=c11", "-Wall", "-Wextra", "-Werror", "/o/d.c", "/o/o.o", "-o", "/o/e"])
        self.assertEqual(GATE.solver_command(Path("/a/ay"), Path("/q.smt2"), Path("/p.alethe")),
                         ["/a/ay", "--memory", "8192", "-smt2", "/q.smt2", "--strict-proofs", "--proof",
                          "/p.alethe", "--proof-format", "alethe"])
        self.assertEqual(GATE.checker_command(Path("/c/clean"), Path("/k.json")),
                         ["/c/clean", "cert", "verify-external", "/k.json", "--verbose"])

    def test_default_cli_path_and_overrides(self):
        parser = GATE.build_parser()
        defaults = parser.parse_args([])
        self.assertEqual(defaults.trust_cg, ROOT / "target" / "release" / "trust-cg")
        self.assertEqual(defaults.cc, "cc")
        self.assertIsNone(defaults.out)
        chosen = parser.parse_args(["--trust-cg", "/opt/cg/trust-cg", "--cc", "clang", "--out", "/o",
                                    "--compile-timeout-seconds", "7"])
        self.assertEqual((chosen.trust_cg, chosen.cc, chosen.out, chosen.compile_timeout_seconds),
                         (Path("/opt/cg/trust-cg"), "clang", Path("/o"), 7.0))
        for bad in (["--compile-timeout-seconds", "0"], ["--max-rss-gib", "-1"], ["--trust"]):
            with self.assertRaises(SystemExit):
                with mock.patch("sys.stderr"):
                    parser.parse_args(bad)

    def test_output_directory_must_be_new_and_outside_the_tree(self):
        with self.assertRaises(OSError):
            GATE.prepare_output(ROOT / "scripts" / "aot-arithmetic-out")
        self.assertFalse((ROOT / "scripts" / "aot-arithmetic-out").exists())
        with tempfile.TemporaryDirectory() as temp:
            existing = Path(temp) / "existing"
            existing.mkdir()
            with self.assertRaises(FileExistsError):
                GATE.prepare_output(existing)
            created = GATE.prepare_output(Path(temp) / "new")
            self.assertTrue(created.is_dir())
            self.assertEqual(stat.S_IMODE(created.stat().st_mode), 0o700)

    def test_host_targets(self):
        self.assertEqual(GATE.host_target("linux", "aarch64")[1], "aarch64-unknown-linux-gnu")
        self.assertEqual(GATE.host_target("linux2", "aarch64")[1], "aarch64-unknown-linux-gnu")
        self.assertEqual(GATE.host_target("darwin", "arm64")[1], "aarch64-apple-darwin")
        for key in (("linux", "x86_64"), ("darwin", "x86_64"), ("win32", "ARM64"), ("freebsd", "arm64")):
            self.assertIsNone(GATE.host_target(*key)[1], key)


class ToolDiscoveryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.fixture = Fixture(Path(self.temp.name))

    def tearDown(self):
        self.temp.cleanup()

    def resolve(self, environ, trust_cg=None):
        return GATE.resolve_tools(trust_cg or self.fixture.cli, "cc", environ, "linux", "aarch64-unknown-linux-gnu")

    def test_explicit_overrides_are_pinned(self):
        tools, errors = self.resolve(self.fixture.environ())
        self.assertEqual(errors, [])
        self.assertEqual(tools["ay"]["route"], "env-override:AY_SOLVER_PATH")
        self.assertEqual(tools["clean"]["route"], "env-override:TCG_EXTERNAL_CLEAN_CHECKER")
        self.assertEqual(tools["ay"]["sha256"], GATE.sha256_file(self.fixture.ay))
        self.assertEqual(tools["cc"]["resolved"], str(self.fixture.cc.resolve()))
        self.assertEqual(tools["trust_cg"]["resolved"], str(self.fixture.cli.resolve()))

    def test_managed_clean_and_toolchain_ay_are_pinned(self):
        prefix = Path(self.temp.name) / "pkg"
        for tool, source in (("ay", self.fixture.ay), ("clean", self.fixture.clean)):
            target = prefix / "store" / tool / "7" / "bin"
            target.mkdir(parents=True)
            executable(target / tool, source.read_text())
            (prefix / "store" / tool / "current").symlink_to("7")
        (prefix / "bin").mkdir()
        environ = {"PATH": f"{prefix / 'bin'}{os.pathsep}{self.fixture.bin}", "HOME": str(self.fixture.home)}
        # A managed ay is never consulted (crates/trust-cg-verify/src/ay_identity.rs).
        tools, errors = self.resolve(environ)
        self.assertNotIn("ay", tools)
        self.assertEqual(errors, ["ay: no pinned executable (absolute AY_SOLVER_PATH or the build toolchain's "
                                  "bin/ay); the independent replay cannot run"])
        self.assertEqual(tools["clean"]["route"], "aterm-packaged")
        self.assertEqual(tools["clean"]["resolved"], str((prefix / "store/clean/7/bin/clean").resolve()))
        # The build compiler's sysroot bin/ay is the automatic AY route.
        sysroot = Path(self.temp.name) / "trust-sysroot"
        (sysroot / "bin").mkdir(parents=True)
        (Path(self.temp.name) / "compiler").mkdir()
        executable(sysroot / "bin" / "ay", self.fixture.ay.read_text())
        rustc = executable(Path(self.temp.name) / "compiler" / "rustc", f"#!/bin/sh\necho '{sysroot}'\n")
        tools, errors = self.resolve({**environ, "RUSTC": str(rustc)})
        self.assertEqual(errors, [])
        self.assertEqual(tools["ay"]["route"], "toolchain-sysroot")
        self.assertEqual(tools["ay"]["resolved"], str((sysroot / "bin" / "ay").resolve()))

    def test_unpinned_missing_and_invalid_tools_are_refused(self):
        executable(self.fixture.bin / "ay", "#!/bin/sh\necho unsat\n")
        executable(self.fixture.bin / "clean", "#!/bin/sh\nexit 0\n")
        environ = {"PATH": str(self.fixture.bin), "HOME": str(self.fixture.home)}
        tools, errors = self.resolve(environ)
        self.assertNotIn("ay", tools)
        self.assertNotIn("clean", tools)
        # A bare `ay` on PATH is never consulted.
        self.assertTrue(any(error.startswith("ay: no pinned executable") for error in errors), errors)
        self.assertTrue(any(error.startswith("clean: no pinned executable") for error in errors), errors)
        environ.update(AY_SOLVER_PATH="relative/ay", TCG_EXTERNAL_CLEAN_CHECKER=str(self.fixture.bin / "absent"))
        tools, errors = self.resolve(environ, trust_cg=self.fixture.directory / "no-such-cli")
        self.assertEqual(set(tools), {"cc"})
        self.assertEqual(len(errors), 3, errors)
        self.assertIn("trust-cg CLI unavailable", errors[0])

    def test_child_environment_strips_ambient_knobs_and_pins_tools(self):
        env, removed = GATE.child_environment(
            {"PATH": "/bin", "TCG_REFINE_SOLVER": "0", "TRUST_CG_X": "1", "AY_SOLVER_PATH": "/old",
             "TCG_NO_ELF_REPARSE": "1", "KEEP": "yes"}, "/new/ay", "/new/clean")
        self.assertEqual(removed, ["AY_SOLVER_PATH", "TCG_NO_ELF_REPARSE", "TCG_REFINE_SOLVER", "TRUST_CG_X"])
        self.assertEqual(env, {"PATH": "/bin", "KEEP": "yes", "AY_SOLVER_PATH": "/new/ay",
                               "TCG_EXTERNAL_CLEAN_CHECKER": "/new/clean"})

    def test_identity_drift_is_reported(self):
        before = {"ay": {"sha256": "a", "resolved": "/x"}, "clean": {"sha256": "b", "resolved": "/y"}}
        self.assertEqual(GATE.identity_drift(before, before), [])
        drift = GATE.identity_drift(before, {"ay": {"sha256": "c", "resolved": "/x"}})
        self.assertEqual(len(drift), 2)


class ClassificationTests(unittest.TestCase):
    def test_refusal_signature_keeps_refusal_lines_and_elides_the_output_directory(self):
        out = Path("/scratch/run")
        signature = GATE.refusal_signature(
            "--- proof certificates ---\n", "note: fine\ntrust-cg: error: proof promotion rejected: x /scratch/run/a.o\n",
            out)
        self.assertEqual(signature, "trust-cg: error: proof promotion rejected: x <out>/a.o")
        self.assertEqual(GATE.refusal_signature("", "", out), "no diagnostic output")
        self.assertEqual(GATE.refusal_signature("a\nb\n", "", out), "a\nb")

    def test_observed_darwin_refusal_keeps_its_exact_reason(self):
        # Verbatim stderr of an installed trust-cg package compiling i32-add at O0 for
        # aarch64-apple-darwin with --emit-proofs (probe on 2026-09-18; not a runner run).
        out = Path("/scratch/aot")
        stderr = (
            "trust-cg: error: compilation of '/scratch/aot/inputs/i32-add.trust_ir' failed: proof promotion "
            "rejected for target Aarch64: non_verified proof entry statistical_validation_instruction_0 in "
            "calculate: 1 instruction(s) were validated only by bounded statistical sampling; proof-carrying "
            "promotion requires Formal or Exhaustive evidence\n"
        )
        signature = GATE.refusal_signature("", stderr, out)
        self.assertEqual(signature, stderr.strip().replace("/scratch/aot", "<out>"))
        self.assertIn("statistical_validation_instruction_0", signature)

    def test_runner_statuses_are_attributed_only_with_their_marker(self):
        self.assertTrue(GATE.classify_execution(124, "run_with_timeout: command exceeded 1s: x")["timed_out"])
        self.assertFalse(GATE.classify_execution(124, "the program itself exited 124")["timed_out"])
        self.assertTrue(GATE.classify_execution(122, "run_with_timeout: resident set exceeded 1 GiB")["resource_limited"])
        self.assertTrue(GATE.classify_execution(127, "run_with_timeout: command not found: x")["launch_error"])
        self.assertEqual(set(GATE.classify_execution(0, "").values()), {False})

    def test_bounded_executor_uses_the_shared_process_group_runner(self):
        executor = GATE.BoundedExecutor(grace_seconds=0.05)
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            ok = executor([sys.executable, "-c", "import sys; print('out'); print('err', file=sys.stderr); sys.exit(3)"],
                          cwd=directory, env=os.environ, timeout_seconds=20, log_stem=directory / "ok")
            self.assertEqual((ok["returncode"], ok["timed_out"], ok["stdout_text"].strip()), (3, False, "out"))
            self.assertEqual((directory / "ok.stderr.log").read_text().strip(), "err")
            self.assertEqual(ok["bounded_command"][1], str(GATE.TIMEOUT_RUNNER))
            slow = executor([sys.executable, "-c", "import time; time.sleep(30)"], cwd=directory, env=os.environ,
                            timeout_seconds=0.5, log_stem=directory / "slow")
            self.assertTrue(slow["timed_out"], slow)
            self.assertEqual(GATE.step_failure(slow, GATE.COMPILE_TIMEOUT), GATE.COMPILE_TIMEOUT)
            self.assertNotIn("stdout_text", GATE.public_execution(slow))
            with self.assertRaises(FileExistsError):
                executor(["true"], cwd=directory, env=os.environ, timeout_seconds=5, log_stem=directory / "ok")


class MatrixTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.fixture = Fixture(Path(self.temp.name))

    def tearDown(self):
        self.temp.cleanup()

    def assert_all_cases_failed(self, report, failure_class):
        self.assertEqual(report["status"], "fail")
        self.assertEqual(len(report["cases"]), 48)
        self.assertEqual({row["failure"]["class"] for row in report["cases"]}, {failure_class})
        self.assertEqual(report["summary"]["failure_classes"], {failure_class: 48})
        self.assertEqual(report["summary"]["passed_cases"], 0)

    def test_complete_matrix_passes_through_main_with_every_control(self):
        environ = self.fixture.environ(TCG_REFINE_SOLVER="0", TRUST_CG_RUN_FORMAL_PROOF_TESTS="1", AY_JOBS="9")
        out = Path(self.temp.name) / "main-out"
        with mock.patch("sys.stdout"), mock.patch("sys.stderr"):
            code = GATE.main(["--trust-cg", str(self.fixture.cli), "--out", str(out)], environ=environ,
                             executor=direct_executor, host=LINUX, binder=fake_binder)
        self.assertEqual(code, 0)
        report = json.loads((out / "report.json").read_text())
        self.assertEqual(report["status"], "pass", report["errors"])
        self.assertEqual(report["schema"], GATE.SCHEMA)
        self.assertEqual(report["host"]["target"], "aarch64-unknown-linux-gnu")
        summary = report["summary"]
        self.assertEqual((summary["passed_cases"], summary["native_calls"]), (48, 6912))
        self.assertEqual((summary["distinct_queries"], summary["originals_accepted"], summary["corruptions_rejected"]),
                         (9, 9, 27))
        self.assertEqual(summary["failure_classes"], {})
        # Source fingerprints come from the real repository tree, before and after.
        self.assertEqual(report["provenance"]["source_root"], str(ROOT))
        self.assertEqual(len(report["provenance"]["source_fingerprint"]), 64)
        self.assertEqual(report["final_source"]["source_fingerprint"], report["provenance"]["source_fingerprint"])
        self.assertEqual(report["environment"]["removed"],
                         ["AY_JOBS", "AY_SOLVER_PATH", "TCG_EXTERNAL_CLEAN_CHECKER", "TCG_REFINE_SOLVER",
                          "TRUST_CG_RUN_FORMAL_PROOF_TESTS"])
        self.assertEqual(report["environment"]["pinned"]["AY_SOLVER_PATH"], str(self.fixture.ay.resolve()))
        self.assertEqual(report["tools"]["trust_cg"]["sha256"], GATE.sha256_file(self.fixture.cli))
        self.assertEqual(report["tools"], report["tools_after"])
        # 24 TrustIR/oracle pairs plus the foreign-object control's C source.
        self.assertEqual(len(report["inputs"]), 25)
        self.assertEqual(report["inputs"][-1]["path"], "inputs/foreign-calculate.c")
        for row in report["inputs"]:
            self.assertEqual(GATE.sha256_file(out / row["path"]), row["sha256"])
        self.assertEqual(report["linked_image_foreign"]["object_sha256"],
                         GATE.sha256_file(out / "inputs" / "foreign-calculate.o"))
        self.assertEqual((summary["linked_images_bound"], summary["linked_image_controls_refused"],
                          summary["required_linked_image_controls"]), (48, 144, 144))
        for case in report["cases"]:
            record = case["linked_image"]
            self.assertEqual(record["status"], "bound", case["name"])
            self.assertEqual([control["control"] for control in record["controls"]], list(GATE.LINKED_IMAGE_CONTROLS))
            for control in record["controls"]:
                self.assertEqual((control["constructed"], control["refused"], control["observed_class"],
                                  control["passed"]), (True, True, GATE.LINKED_IMAGE_MISMATCH, True), control)
        row = cases_by_name(report)["u64-double-O3"]
        self.assertEqual((row["status"], row["calls"], len(row["queries"])), ("pass", 144, 2))
        for step in ("compile", "link", "native"):
            record = row["steps"][step]
            log = out / "cases" / "u64-double-O3" / record["stdout_log"]
            self.assertEqual(GATE.sha256_file(log), record["stdout_sha256"])
        self.assertTrue((out / "cases" / "u64-double-O3" / "proofs" / "calculate.lowering.json").is_file())
        for query in report["replay"]["queries"]:
            self.assertEqual(query["status"], "pass")
            self.assertEqual([cert["variant"] for cert in query["certificates"]],
                             ["original", *GATE.CORRUPTION_CONTROLS])
            self.assertEqual([cert["accepted"] for cert in query["certificates"]], [True, False, False, False])
        frame = [query for query in report["replay"]["queries"] if len(query["cases"]) == 48]
        self.assertEqual(len(frame), 1)

    def test_darwin_export_refusal_is_a_named_failure_on_every_case(self):
        report = self.fixture.run(host=DARWIN, environ=self.fixture.environ(FAKE_CLI_REFUSE_TARGET="aarch64-apple-darwin"))
        self.assert_all_cases_failed(report, GATE.EXPORT_REFUSED)
        self.assertEqual(report["host"]["target"], "aarch64-apple-darwin")
        refusals = report["summary"]["refusals"]
        self.assertEqual(len(refusals), 48)  # each signature names its own elided object path
        self.assertTrue(all(refusal["signature"].startswith(
            "Source-bound AArch64 affine ALU: AddRR [UNVERIFIED]\ntrust-cg: error: proof promotion rejected")
            for refusal in refusals), refusals[0])
        self.assertIn("<out>/cases/i32-add-O0/i32-add-O0.o", cases_by_name(report)["i32-add-O0"]["refusal"])
        self.assertEqual(report["summary"]["distinct_queries"], 0)
        self.assertTrue(any("exported 0 distinct queries" in error for error in report["errors"]))
        command = cases_by_name(report)["u32-sub-O1"]["steps"]["compile"]["command"]
        self.assertEqual(command[command.index("--target") + 1], "aarch64-apple-darwin")

    def test_case_faults_are_classified_without_masking_other_cases(self):
        environ = self.fixture.environ(
            FAKE_CLI_DROP_LOWERING="i32-add-O1", FAKE_CLI_BAD_HASH="i32-sub-O2", FAKE_CLI_NO_OBJECT="u32-add-O0",
            FAKE_CC_FAIL="u32-double-O3", FAKE_NATIVE_WRONG="i64-add-O2", FAKE_CLI_SLEEP="i64-sub-O0",
            FAKE_NATIVE_SLEEP="u64-add-O1", FAKE_CLI_SOURCE_DRIFT="u64-sub",
        )
        fingerprints = iter(["a" * 64, "b" * 64])
        changing = lambda: {"dirty": False, "source_fingerprint": next(fingerprints)}  # noqa: E731
        # The same bound must be SHORT enough that the sleeping fakes (60 s CLI, 30 s native) time out and
        # LONG enough that the other cases finish: at 2 s the deliberately-wrong native case itself timed
        # out on this machine even at load 5 (F-164), turning NATIVE_MISMATCH into NATIVE_TIMEOUT. 10 s keeps
        # a 3x margin under the shortest sleep.
        report = self.fixture.run(environ=environ, provenance=changing, compile_timeout=10.0, native_timeout=10.0)
        expected = {
            "i32-add-O1": GATE.CERTIFICATE_MISSING, "i32-sub-O2": GATE.SIDECAR_MISMATCH,
            "u32-add-O0": GATE.OBJECT_MISSING, "u32-double-O3": GATE.LINK_FAILED,
            "i64-add-O2": GATE.NATIVE_MISMATCH, "i64-sub-O0": GATE.COMPILE_TIMEOUT,
            "u64-add-O1": GATE.NATIVE_TIMEOUT,
        }
        # One changed TrustIR identity fails every optimization level of its group.
        expected.update({f"u64-sub-O{level}": GATE.SOURCE_IDENTITY_MISMATCH for level in range(4)})
        rows = cases_by_name(report)
        for name, row in rows.items():
            if name in expected:
                self.assertEqual(row["failure"]["class"], expected[name], row["failure"])
            else:
                self.assertEqual((row["status"], row["failure"], row["calls"]), ("pass", None, 144), name)
        for name in ("i32-add-O1", "i32-sub-O2", "u32-add-O0", "u32-double-O3", "i64-add-O2", "i64-sub-O0"):
            self.assertEqual(rows[name]["calls"], 0, name)
        self.assertIn("machine_code_hash", rows["i32-sub-O2"]["failure"]["detail"])
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["summary"]["passed_cases"], 48 - len(expected))
        self.assertIn("source changed while the matrix was running", report["errors"])
        # Cases that exported still contribute their queries; the replay itself passes.
        self.assertEqual((report["summary"]["distinct_queries"], report["summary"]["corruptions_rejected"]), (9, 27))

    def test_solver_faults_fail_exactly_the_cases_that_depend_on_the_query(self):
        report = self.fixture.run(environ=self.fixture.environ(
            FAKE_AY_SAT="bvsub", FAKE_AY_NO_PROOF="bvshl", FAKE_AY_SPACED_EMPTY="bvadd x x"))
        rows = cases_by_name(report)
        for row in rows.values():
            if row["shape"] == "sub":
                expected = GATE.SOLVER_REFUSED
            elif row["shape"] == "double":
                expected = GATE.CONTROL_NOT_CONSTRUCTED if row["opt_level"] == 0 else GATE.PROOF_MISSING
            else:
                expected = None
            self.assertEqual(row["failure"] and row["failure"]["class"], expected, row["name"])
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["summary"]["passed_cases"], 16)
        self.assertEqual(report["summary"]["failure_classes"], {
            GATE.CONTROL_NOT_CONSTRUCTED: 4, GATE.PROOF_MISSING: 12, GATE.SOLVER_REFUSED: 16})
        spaced = [query for query in report["replay"]["queries"] if query["failure"]
                  and query["failure"]["class"] == GATE.CONTROL_NOT_CONSTRUCTED]
        self.assertEqual(len(spaced), 2)
        for query in spaced:
            self.assertEqual([(cert["variant"], cert["passed"]) for cert in query["certificates"]],
                             [("original", True), ("hole", True), ("no-empty-clause", False),
                              ("opposite-premise", True)])
        self.assertEqual(report["summary"]["originals_accepted"], 5)

    def test_checker_faults_fail_exactly_the_cases_that_depend_on_the_query(self):
        report = self.fixture.run(environ=self.fixture.environ(
            FAKE_CLEAN_ACCEPT_ALL="bvsub", FAKE_CLEAN_CRASH_ON_CONTROLS="bvshl", FAKE_CLEAN_REJECT_ALL="bvadd x x"))
        rows = cases_by_name(report)
        for row in rows.values():
            if row["shape"] == "sub":
                expected = GATE.CHECKER_ACCEPTED_CORRUPTION
            elif row["shape"] == "double":
                expected = GATE.CHECKER_REJECTED_ORIGINAL if row["opt_level"] == 0 else GATE.CHECKER_CONTROL_ERROR
            else:
                expected = None
            self.assertEqual(row["failure"] and row["failure"]["class"], expected, row["name"])
            self.assertEqual(row["calls"], 144)
        self.assertEqual(report["status"], "fail")
        summary = report["summary"]
        self.assertEqual(summary["native_calls"], 6912)
        self.assertEqual(summary["passed_cases"], 16)
        # Originals: add x2, frame, sub x2 (whose corruptions are also accepted) and shl x2.
        # Rejections: three each for add x2 and frame, plus the doubling-O0 controls that the
        # rejecting checker refuses with its verdict; the accepted and crashed ones never count.
        self.assertEqual((summary["originals_accepted"], summary["corruptions_rejected"]), (7, 15))

    def test_changed_query_inventory_fails_the_replay_denominator(self):
        report = self.fixture.run(environ=self.fixture.environ(FAKE_CLI_QUERY_SALT="1"))
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["summary"]["distinct_queries"], 49)
        self.assertEqual(report["summary"]["passed_cases"], 48)
        self.assertTrue(any("exported 49 distinct queries" in error for error in report["errors"]))

    def test_unavailable_tools_fail_every_case_without_running(self):
        report = self.fixture.run(trust_cg=self.fixture.directory / "missing-cli")
        self.assert_all_cases_failed(report, GATE.TOOL_UNAVAILABLE)
        self.assertEqual(report["cases"][0]["steps"], {})
        self.assertFalse((self.fixture.directory / f"out-{self.fixture.runs}" / "cases").exists())
        report = self.fixture.run(environ={"PATH": str(self.fixture.bin), "HOME": str(self.fixture.home)})
        self.assert_all_cases_failed(report, GATE.TOOL_UNAVAILABLE)

    def decoy_ay(self):
        """A script that prints a fake AY banner and `unsat`, and logs every execution."""
        marker = self.fixture.directory / "decoy-ay.executed"
        text = f'#!/bin/sh\necho "$@" >> "{marker}"\necho "ay 0.0.0-fake"\necho unsat\n'
        return text, marker

    def assert_refused_before_any_ay_ran(self, report, code):
        self.assert_all_cases_failed(report, GATE.AY_NOT_ADMITTED)
        self.assertEqual(report["replay"]["queries"], [])
        self.assertEqual(report["cases"][0]["steps"], {})
        self.assertFalse((self.fixture.directory / f"out-{self.fixture.runs}" / "cases").exists())
        self.assertFalse((self.fixture.directory / f"out-{self.fixture.runs}" / "replay").exists())
        if code is not None:
            self.assertEqual(report["ay_admission"]["report"]["code"], code)
            self.assertFalse(report["ay_admission"]["report"]["admitted"])

    def test_the_cli_under_test_admits_the_resolved_ay_before_anything_runs(self):
        report = self.fixture.run()
        self.assertEqual(report["status"], "pass", report["errors"])
        admission = report["ay_admission"]
        self.assertEqual(admission["returncode"], 0)
        self.assertEqual(admission["report"]["sha256"], GATE.sha256_file(self.fixture.ay))
        self.assertEqual(admission["report"]["path"], str(self.fixture.ay.resolve()))
        # Every replay started the private copy, never the admitted path.
        copy = Path(admission["report"]["exec_path"])
        self.assertEqual(copy.parent.name, admission["report"]["sha256"])
        self.assertEqual(copy.stat().st_mode & 0o7777, 0o500)
        self.assertEqual(copy.parent.stat().st_mode & 0o7777, 0o700)
        self.assertEqual(GATE.sha256_file(copy), GATE.sha256_file(self.fixture.ay))
        self.assertEqual(admission["exec_stamp"][1], copy.stat().st_ino)
        # Started by the canonical path admission judged.
        self.assertEqual(admission["exec_canonical"], os.path.realpath(copy))
        self.assertEqual(len(report["replay"]["queries"]), 9)
        for query in report["replay"]["queries"]:
            self.assertEqual(query["solver"]["command"][0], admission["exec_canonical"], query["name"])

    def test_an_ay_the_cli_does_not_admit_never_runs(self):
        # A banner-faking script named by an absolute AY_SOLVER_PATH resolves
        # through a pinned route; only the CLI's record can refuse it.
        text, marker = self.decoy_ay()
        decoy = executable(self.fixture.bin / "decoy-ay", text)
        report = self.fixture.run(environ=self.fixture.environ(AY_SOLVER_PATH=str(decoy)))
        self.assertEqual(report["tools"]["ay"]["route"], "env-override:AY_SOLVER_PATH")
        self.assert_refused_before_any_ay_ran(report, "TCG-AY-IDENTITY-MISMATCH")
        self.assertTrue(any("refuses AY" in error and "TCG-AY-IDENTITY-MISMATCH" in error
                            for error in report["errors"]), report["errors"])
        self.assertFalse(marker.exists(), "the refused AY was executed")

    def test_a_cli_that_records_no_ay_admits_none(self):
        # A stock-toolchain build of the CLI records no AY.
        self.fixture.ay_record.unlink()
        report = self.fixture.run()
        self.assert_refused_before_any_ay_ran(report, "TCG-AY-IDENTITY-UNRECORDED")

    def test_a_cli_that_cannot_report_its_ay_identity_admits_none(self):
        report = self.fixture.run(environ=self.fixture.environ(FAKE_CLI_IDENTITY_UNSUPPORTED="1"))
        self.assert_refused_before_any_ay_ran(report, None)
        self.assertEqual(report["ay_admission"]["returncode"], 2)
        self.assertTrue(any("without an identity report" in error for error in report["errors"]), report["errors"])

    def test_admission_must_name_the_resolved_ay_bytes(self):
        report = self.fixture.run(environ=self.fixture.environ(FAKE_CLI_REPORT_AY_SHA256="0" * 64))
        self.assert_refused_before_any_ay_ran(report, None)
        self.assertTrue(report["ay_admission"]["report"]["admitted"])
        self.assertTrue(any("admitted sha256" in error for error in report["errors"]), report["errors"])

    def test_an_ay_replaced_after_admission_is_not_executed(self):
        text, marker = self.decoy_ay()
        replaced = []

        def replacing_executor(command, **kwargs):
            # Swap the admitted file's bytes after admission, during the cases.
            if not replaced and Path(command[0]).name == "trust-cg":
                self.fixture.ay.write_text(text)
                replaced.append(True)
            return direct_executor(command, **kwargs)

        report = self.fixture.run(executor=replacing_executor)
        self.assertEqual(replaced, [True])
        self.assertEqual(len(report["replay"]["queries"]), 9)
        for query in report["replay"]["queries"]:
            self.assertEqual(query["failure"]["class"], GATE.AY_NOT_ADMITTED, query["name"])
            self.assertNotIn("solver", query)
        self.assertEqual(report["summary"]["failure_classes"], {GATE.AY_NOT_ADMITTED: 48})
        self.assertIn("ay executable identity changed during the run", report["errors"])
        self.assertFalse(marker.exists(), "an AY whose bytes changed after admission was executed")

    def test_replacing_the_admitted_ay_as_the_replay_starts_never_runs_the_replacement(self):
        # The measured attack on 288ac2d2c: AY re-executes itself by the path
        # it was started from, so a file swapped in at the admitted path after
        # admission and re-digest, as the solver starts, ran instead. The
        # replay starts the private copy, so its re-exec lands on the copy.
        text, marker = self.decoy_ay()
        swaps = []

        def swapping_executor(command, **kwargs):
            if "-smt2" in command:
                staged = self.fixture.bin / "fake-ay.decoy"
                executable(staged, text)
                os.replace(staged, self.fixture.ay)
                swaps.append(command[0])
            return direct_executor(command, **kwargs)

        report = self.fixture.run(executor=swapping_executor)
        self.assertFalse(marker.exists(), "a file swapped in after admission was executed")
        # The swap lands after the pre-start checks of the first solver run:
        # that run's re-exec still lands on the admitted bytes and answers.
        first, *rest = report["replay"]["queries"]
        self.assertEqual(swaps, [first["solver"]["command"][0]])
        self.assertEqual(first["failure"], None, first)
        self.assertNotEqual(first["solver"]["command"][0], str(self.fixture.ay))
        # Every later run sees the admitted file changed and starts nothing.
        self.assertEqual(len(rest), 8)
        for query in rest:
            self.assertEqual(query["failure"]["class"], GATE.AY_NOT_ADMITTED, query["name"])
            self.assertNotIn("solver", query)
        # The run still reports that the admitted file changed under it.
        self.assertIn("ay executable identity changed during the run", report["errors"])

    def test_a_private_copy_that_is_not_private_or_not_the_admitted_bytes_never_runs(self):
        text, marker = self.decoy_ay()
        exec_directory = self.fixture.home / ".cache" / "trust-cg" / "ay-exec" / GATE.sha256_file(self.fixture.ay)
        copy = exec_directory / "ay"
        tampers = {
            "replaced": lambda: (copy.chmod(0o700), copy.write_text(text), copy.chmod(0o500)),
            "writable": lambda: copy.chmod(0o700),
            "group-directory": lambda: exec_directory.chmod(0o750),
        }
        for label, tamper in tampers.items():
            with self.subTest(label):
                tampered = []

                def tampering_executor(command, **kwargs):
                    if not tampered and Path(command[0]).name == "trust-cg" and "--print-ay-identity" not in command:
                        tamper()
                        tampered.append(True)
                    return direct_executor(command, **kwargs)

                report = self.fixture.run(executor=tampering_executor)
                self.assertEqual(tampered, [True])
                self.assertEqual(len(report["replay"]["queries"]), 9)
                for query in report["replay"]["queries"]:
                    self.assertEqual(query["failure"]["class"], GATE.AY_NOT_ADMITTED, query["name"])
                    self.assertNotIn("solver", query)
                self.assertFalse(marker.exists(), "a tampered private copy was executed")
                exec_directory.chmod(0o700)
                copy.chmod(0o700)
                copy.unlink()

    def test_admission_must_name_a_private_copy_of_the_admitted_bytes(self):
        text, marker = self.decoy_ay()
        elsewhere = self.fixture.directory / "public-ay"
        executable(elsewhere, text)
        for exec_path in (str(elsewhere), "relative-ay", str(self.fixture.ay)):
            with self.subTest(exec_path):
                report = self.fixture.run(environ=self.fixture.environ(FAKE_CLI_REPORT_EXEC_PATH=exec_path))
                self.assert_refused_before_any_ay_ran(report, None)
                self.assertTrue(any("private" in error for error in report["errors"]), report["errors"])
        self.assertFalse(marker.exists())

    def test_a_private_copy_named_through_a_link_others_can_repoint_is_started_by_its_canonical_path(self):
        """X-HOST-P13 third closure audit: a path checked by its canonical
        ancestry and then started by its own spelling runs whatever a symlink
        in a directory others can write points to at the start. Here the CLI
        names the private copy as `<shared 0777>/link/<sha256>/ay`, the link
        standing for its `ay-exec` directory (the copy's own 0700 directory is
        real, so a check of the file and its parent passes through it), and
        another user re-points the link at a decoy tree as the first solver
        run starts. Admission resolves the copy once and every run starts its
        canonical path, so the decoy never runs."""
        text, marker = self.decoy_ay()
        exec_directory = self.fixture.home / ".cache" / "trust-cg" / "ay-exec" / GATE.sha256_file(self.fixture.ay)
        shared = self.fixture.directory / "shared"
        shared.mkdir()
        shared.chmod(0o777)
        link = shared / "link"
        link.symlink_to(exec_directory.parent)
        decoy_directory = self.fixture.directory / "decoy"
        decoy_directory.mkdir()
        decoy_directory.chmod(0o700)
        (decoy_directory / exec_directory.name).mkdir(mode=0o700)
        (decoy_directory / exec_directory.name).chmod(0o700)
        executable(decoy_directory / exec_directory.name / "ay", text).chmod(0o500)
        swaps = []

        def repointing_executor(command, **kwargs):
            if "-smt2" in command and not swaps:
                staged = shared / "staged"
                staged.symlink_to(decoy_directory)
                os.replace(staged, link)
                swaps.append(command[0])
            return direct_executor(command, **kwargs)

        aliased = link / exec_directory.name / "ay"
        report = self.fixture.run(environ=self.fixture.environ(FAKE_CLI_REPORT_EXEC_PATH=str(aliased)),
                                  executor=repointing_executor)
        canonical = os.path.realpath(exec_directory / "ay")
        self.assertEqual(report["ay_admission"]["report"]["exec_path"], str(aliased))
        self.assertEqual(report["ay_admission"]["exec_canonical"], canonical)
        self.assertEqual(swaps, [canonical], "the link was re-pointed as the first solver run started")
        self.assertFalse(marker.exists(), "the decoy behind the re-pointed link was executed")
        self.assertEqual(report["status"], "pass", report["errors"])
        for query in report["replay"]["queries"]:
            self.assertEqual(query["solver"]["command"][0], canonical, query["name"])

    def test_a_private_copy_below_a_directory_others_can_write_is_refused(self):
        """The copy itself in a real directory below `<shared 0777>`: the
        canonical ancestry fails the private-cache rule and nothing runs."""
        shared = self.fixture.directory / "shared"
        shared.mkdir()
        shared.chmod(0o777)
        report = self.fixture.run(environ=self.fixture.environ(XDG_CACHE_HOME=str(shared / "xdg")))
        self.assert_refused_before_any_ay_ran(report, None)
        self.assertTrue(any("is not one only this user can change" in error and "not a trusted directory ancestor"
                            in error for error in report["errors"]), report["errors"])

    def test_the_replay_runs_no_ay_without_the_clis_admission(self):
        # The replay itself refuses: a caller that resolves tools and calls it
        # directly, skipping run_matrix's admission, still executes no AY.
        text, marker = self.decoy_ay()
        decoy = executable(self.fixture.bin / "decoy-ay", text)
        environ = self.fixture.environ(AY_SOLVER_PATH=str(decoy))
        tools, errors = GATE.resolve_tools(self.fixture.cli, "cc", environ, "linux", "aarch64-unknown-linux-gnu")
        self.assertEqual(errors, [])
        out = self.fixture.directory / "direct-replay"
        out.mkdir()
        query = out / "q.smt2"
        query.write_text("(check-sat)\n")
        env, _ = GATE.child_environment(environ, tools["ay"]["resolved"], tools["clean"]["resolved"])
        report = {"replay": {"queries": []}}
        context = {"out": out, "options": self.fixture.options(), "executor": direct_executor, "env": env,
                   "tools": tools, "exported_queries": [("case", query)], "report_path": out / "report.json"}
        results = GATE.run_replay(context, report)
        self.assertEqual([row["failure"]["class"] for row in results.values()], [GATE.AY_NOT_ADMITTED])
        self.assertFalse(marker.exists(), "the replay executed an AY nobody admitted")

    def test_unsupported_host_fails_every_case(self):
        report = self.fixture.run(host=("linux", "x86_64"))
        self.assert_all_cases_failed(report, GATE.UNSUPPORTED_HOST)
        self.assertIsNone(report["host"]["target"])

    def test_require_clean_refuses_a_dirty_tree(self):
        dirty = lambda: {"dirty": True, "source_fingerprint": "e" * 64, "git_status": [" M x"]}  # noqa: E731
        report = self.fixture.run(provenance=dirty, require_clean=True)
        self.assert_all_cases_failed(report, GATE.SOURCE_NOT_CLEAN)
        report = self.fixture.run(provenance=dirty, trust_cg=self.fixture.directory / "missing-cli")
        self.assertFalse(report["clean_source"])
        self.assertEqual(report["provenance"]["git_status"], [" M x"])

    def test_linked_image_faults_are_named_without_masking_other_cases(self):
        def accepting(object_bytes, image_bytes, target):
            # i64-double-O2's check accepts any image, so each of its three negatives must fail it.
            if b" i64-double-O2 " in object_bytes:
                return {"status": "bound", "image_sha256": GATE.sha256_bytes(image_bytes), "function_file_offset": 0,
                        "function_size": 4, "relocation_effects": [{"field_file_offset": 4, "status": "checked"}]}
            return fake_binder(object_bytes, image_bytes, target)

        swapped = []

        def swapping_executor(command, **kwargs):
            result = direct_executor(command, **kwargs)
            exe = Path(command[0])
            if exe.name == "u32-add-O3" and exe.is_symlink():
                # The file executed is replaced after its binding and run.
                exe.unlink()
                exe.symlink_to(self.fixture.bin / "native-foreign")
                swapped.append(exe)
            return result

        report = self.fixture.run(environ=self.fixture.environ(FAKE_IMAGE_FOREIGN="i32-sub-O1"), binder=accepting,
                                  executor=swapping_executor)
        rows = cases_by_name(report)
        expected = {"i32-sub-O1": GATE.LINKED_IMAGE_MISMATCH, "i64-double-O2": GATE.LINKED_IMAGE_CONTROL_FAILED,
                    "u32-add-O3": GATE.LINKED_IMAGE_MISMATCH}
        self.assertEqual(len(swapped), 1)
        for name, row in rows.items():
            self.assertEqual(row["failure"] and row["failure"]["class"], expected.get(name), name)
        self.assertEqual(rows["i32-sub-O1"]["linked_image"]["status"], "refused")
        self.assertNotIn("native", rows["i32-sub-O1"]["steps"])
        self.assertEqual(rows["i32-sub-O1"]["calls"], 0)
        accepted = rows["i64-double-O2"]["linked_image"]["controls"]
        self.assertEqual([(control["control"], control["refused"], control["passed"]) for control in accepted],
                         [(label, False, False) for label in GATE.LINKED_IMAGE_CONTROLS])
        self.assertIn("is not the bound image", rows["u32-add-O3"]["failure"]["detail"])
        summary = report["summary"]
        self.assertEqual((summary["passed_cases"], summary["linked_images_bound"],
                          summary["linked_image_controls_refused"]), (45, 47, 138))
        self.assertEqual(report["status"], "fail")

    def test_unconstructible_linked_image_controls_fail_their_cases(self):
        report = self.fixture.run(environ=self.fixture.environ(FAKE_CC_FOREIGN_FAIL="1"))
        self.assert_all_cases_failed(report, GATE.CONTROL_NOT_CONSTRUCTED)
        self.assertTrue(any("foreign-object control could not be compiled" in error for error in report["errors"]))
        self.assertEqual(report["summary"]["linked_image_controls_refused"], 96)

        def siteless(object_bytes, image_bytes, target):
            record = fake_binder(object_bytes, image_bytes, target)
            return {"status": record["status"], "image_sha256": record["image_sha256"]}

        report = self.fixture.run(binder=siteless)
        self.assert_all_cases_failed(report, GATE.CONTROL_NOT_CONSTRUCTED)
        self.assertEqual(report["summary"]["linked_image_controls_refused"], 48)

    def test_the_default_binder_refuses_non_elf_objects(self):
        # The real check is the default: the fakes' objects are not ELF, so nothing binds.
        report = self.fixture.run(binder=None)
        self.assert_all_cases_failed(report, GATE.LINKED_IMAGE_UNSUPPORTED)
        self.assertEqual(report["summary"]["native_calls"], 0)
        self.assertIn("shorter than an ELF64 header", report["cases"][0]["failure"]["detail"])

    def test_resident_set_ceiling_is_refused_where_unsupported(self):
        unsupported = mock.Mock()
        unsupported.rss_supervision_support.return_value = None
        with mock.patch.object(GATE.SHARED, "timeout_runner_module", return_value=unsupported):
            report = self.fixture.run(max_rss_gib=4.0, executor=GATE.BoundedExecutor(0.05, 4.0))
        self.assert_all_cases_failed(report, GATE.RESOURCE_SUPERVISION_UNSUPPORTED)
        self.assertEqual(report["controls"]["rss_supervision"], "unsupported")


if __name__ == "__main__":
    unittest.main()
