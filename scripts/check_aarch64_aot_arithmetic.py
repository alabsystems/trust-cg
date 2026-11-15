#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Run the required 48-case AArch64 arithmetic AOT export matrix on this host.

This is the maintained form of the archived native, sidecar-audit and
independent-replay harness described in
reports/perf/2026-09-17-arithmetic-aot-export/README.md. Every case of the fixed
denominator -- I32/U32/I64/U64 x ADD/SUB/doubling x O0-O3 -- must:

1. compile its generated TrustIR text with the trust-cg CLI and --emit-proofs
   for the host target, publishing an object and its proof sidecars;
2. pass the ported sidecar audit: the lowering and trust-proof-cert sidecars
   bind the actual object bytes, one TrustIR identity per type/shape, the
   documented lowering-equivalence VC hash domain, and exactly one Arithmetic
   and one FrameLayout query whose metadata is verified Formal AY evidence
   naming one of the lowering sidecar's proved rules;
3. link with the host C compiler against the recorded C oracle driver;
4. bind the linked executable to the audited object: parse both ELF64 files
   with the standard library, locate the certified function by its .symtab
   symbol (the executable is a PIE, so its address is link-time), map it
   through its executable PT_LOAD segment and require its words to equal the
   object's .text word for word; the object's one .eh_frame R_AARCH64_PREL32
   must resolve, in the linked .eh_frame, to exactly one FDE whose pc_begin is
   that address and whose CIE/FDE bytes match the object's (modulo trailing
   DW_CFA_nop padding), and a present .eh_frame_hdr must index that FDE. The
   same check must refuse three negatives per case: the image with its last
   function word patched, with the FDE pc_begin word patched, and the oracle
   linked against a foreign object defining a different `calculate`;
5. execute natively, match the wrapping-arithmetic oracle (144 calls) and
   confirm the executed file is still the bound image.

Every distinct exported SMT query is then re-solved by AY with an Alethe proof,
and the independent Clean checker must accept the original certificate and
reject the three recorded corruption controls (hole rule, removed empty clause,
opposite premise). A refusal, timeout, missing object or certificate, sidecar
mismatch, link or oracle failure, linked image that does not carry the
certified bytes (or that the check cannot model, such as a Mach-O image),
accepted linked-image negative, solver refusal, checker rejection of an
original, checker acceptance of a corruption, or an unconstructible control is
a named failure. Nothing is skipped: an unsupported host or an unavailable tool
fails every case of the denominator with that named class.

Supported hosts are aarch64-unknown-linux-gnu and aarch64-apple-darwin. The CLI
is compiled for the host target. The runner records whatever the CLI does:
a Darwin export refusal is reported verbatim under `export-refused`. The
linked-image binding reads ELF only, so a Darwin case that did export and link
would fail `linked-image-unsupported` rather than pass unbound.

AY and Clean are named exactly as the verifier names them
(scripts/release_gate_summary.py): AY is an absolute AY_SOLVER_PATH, else the
build toolchain's `<sysroot>/bin/ay`; Clean is an explicit
TCG_EXTERNAL_CLEAN_CHECKER / TCG_CLEAN_CHECKER override, then aterm's managed
package store. Unpinned routes are refused. A named route is not an admitted
AY: the AY identity rule (crates/trust-cg-verify/src/ay_identity.rs) admits an
AY only when the SHA-256 of its bytes equals the digest recorded when
trust-cg-verify was built, and that record is compiled into the CLI. Before any
case runs, this runner asks the CLI under test (`trust-cg --print-ay-identity`,
which executes no AY) to apply that rule to the resolved AY, and runs the
matrix only when the CLI admits exactly those bytes; otherwise every case fails
`ay-not-admitted` and no AY is executed. AY re-executes itself by its own path
at startup (its kernel memory governor), so the replay never starts the
admitted path: it starts the private, content-addressed copy the CLI placed the
admitted bytes in (`exec_path`: a `0500` file owned by this user, one link, in
a `0700` directory owned by this user), resolved once to its canonical path,
whose every ancestor must be renamable by nobody else (scripts/private_cache.py
`require_private`), and started only by that canonical path; before every solver run it
re-checks that copy's ownership, modes and file state and re-digests it,
refusing one that is no longer the admitted bytes. The resolved executables are passed to the CLI as explicit
overrides, so the compiler's own pre-publication replay and this runner's
independent replay use the same admitted identity. Ambient TCG_*, TRUST_CG_*
and AY_* variables are removed from every child.

This is testing evidence for a bounded leaf. The linked-image step is the
runner's own byte comparison, not a certificate over the linked image, and it
does not examine the rest of the image, dynamic relocations or the loader. It
does not establish that the trust-cg binary was built from the recorded source,
a complete source-to-byte proof, Trust-verified compilation, platform
completion or release readiness.
Build the CLI from the recorded revision before relying on a report, with a
Trust toolchain whose sysroot ships `bin/ay` (for example `targo --unverified
build --release --locked -p trust-cg-cli --bin trust-cg`). A build by a
toolchain whose sysroot ships no AY (any stock toolchain) records none, so its
CLI admits none and every case fails `ay-not-admitted`.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import struct
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from typing import Callable, Dict, List, Mapping, Optional, Sequence, Tuple


ROOT = Path(__file__).resolve().parents[1]
TIMEOUT_RUNNER = ROOT / "scripts" / "run_with_timeout.py"
TOOL_RESOLVER = ROOT / "scripts" / "release_gate_summary.py"
LINUX_FLOOR = ROOT / "scripts" / "check_linux_aarch64.py"
DEFAULT_TRUST_CG = ROOT / "target" / "release" / "trust-cg"
ARCHIVED_QUALIFICATION = "reports/perf/2026-09-17-arithmetic-aot-export"

# v2 adds the per-case linked-image binding and its three negatives.
SCHEMA = "trust-cg-aarch64-aot-arithmetic-v2"
SCOPE = (
    "bounded leaf arithmetic AOT export matrix on this host: CLI export, sidecar audit, runner-parsed "
    "byte identity of the certified function and its .eh_frame PREL32 effect in the linked executable, "
    "native C-oracle execution and independent AY/Clean replay of every exported query; not a "
    "certificate over the linked image, binary-to-source correspondence, complete source-to-byte proof, "
    "Trust-verified compilation, platform completion or release readiness"
)

# The exact denominator. Changing any of these changes the claim the README
# makes, so the unit tests pin them and denominator_errors() rechecks them.
TYPES = ("i32", "u32", "i64", "u64")
SHAPES = ("add", "sub", "double")
OPT_LEVELS = (0, 1, 2, 3)
REQUIRED_CASES = 48
CALLS_PER_CASE = 144
REQUIRED_CALLS = 6912
# The recorded qualification exported nine distinct query byte sequences
# (eight operand-specific arithmetic theorems plus the shared leaf frame).
# Any other count changes the replay denominator and must be requalified.
EXPECTED_DISTINCT_QUERIES = 9
CORRUPTION_CONTROLS = ("hole", "no-empty-clause", "opposite-premise")
NATIVE_MARKER = f"ARITHMETIC_AOT_NATIVE calls={CALLS_PER_CASE}"
FUNCTION = "calculate"
SOLVER_MEMORY_MB = 8192

HOST_TARGETS = {
    ("linux", "aarch64"): "aarch64-unknown-linux-gnu",
    ("darwin", "arm64"): "aarch64-apple-darwin",
}
OBJECT_MAGIC = {
    "aarch64-unknown-linux-gnu": b"\x7fELF",
    "aarch64-apple-darwin": b"\xcf\xfa\xed\xfe",
}
# Only these variables are removed from ambient child environments; the
# resolved proof tools are then injected as explicit overrides.
STRIPPED_PREFIXES = ("TCG_", "TRUST_CG_", "AY_")

# run_with_timeout.py exit statuses and the stderr lines that attribute them.
RSS_LIMIT_EXIT = 122
TIMEOUT_EXIT = 124
LAUNCH_ERROR_EXITS = (125, 126, 127)
TIMEOUT_LINE = "run_with_timeout: command exceeded"
RSS_LINE = "run_with_timeout: resident set"

# Named failure classes. A case passes only when none applies.
UNSUPPORTED_HOST = "unsupported-host"
TOOL_UNAVAILABLE = "tool-unavailable"
SOURCE_NOT_CLEAN = "source-not-clean"
RESOURCE_SUPERVISION_UNSUPPORTED = "resource-supervision-unsupported"
INTERRUPTED = "interrupted"
INCOMPLETE = "incomplete"
EXPORT_REFUSED = "export-refused"
COMPILE_TIMEOUT = "compile-timeout"
LAUNCH_FAILED = "launch-failed"
RESOURCE_LIMIT = "resource-limit"
OBJECT_MISSING = "object-missing"
CERTIFICATE_MISSING = "certificate-missing"
SIDECAR_MISMATCH = "sidecar-mismatch"
SOURCE_IDENTITY_MISMATCH = "source-identity-mismatch"
LINK_FAILED = "link-failed"
LINK_TIMEOUT = "link-timeout"
NATIVE_MISMATCH = "native-mismatch"
NATIVE_TIMEOUT = "native-timeout"
SOLVER_REFUSED = "solver-refused"
SOLVER_TIMEOUT = "solver-timeout"
PROOF_MISSING = "proof-missing"
CONTROL_NOT_CONSTRUCTED = "control-not-constructed"
CHECKER_REJECTED_ORIGINAL = "checker-rejected-original"
CHECKER_ACCEPTED_CORRUPTION = "checker-accepted-corruption"
CHECKER_CONTROL_ERROR = "checker-control-error"
CHECKER_TIMEOUT = "checker-timeout"
# The linked executable does not demonstrably carry the certified function
# bytes and unwind entry (unparseable image, missing/duplicate/resized symbol,
# differing words, unresolved FDE or .eh_frame_hdr entry).
LINKED_IMAGE_MISMATCH = "linked-image-mismatch"
# The certified object or target is outside what the linked-image check
# models (a non-ELF target such as Mach-O, relocations against .text, an
# unmodelled relocation site or unwind encoding); the binding is not shown.
LINKED_IMAGE_UNSUPPORTED = "linked-image-unsupported"
# A linked-image negative control was accepted or refused for another reason.
LINKED_IMAGE_CONTROL_FAILED = "linked-image-control-failed"
# The CLI under test does not admit the resolved AY under the AY identity rule
# (or cannot be asked), or the AY's bytes changed after admission. No AY runs.
AY_NOT_ADMITTED = "ay-not-admitted"
FAILURE_CLASSES = (
    UNSUPPORTED_HOST, TOOL_UNAVAILABLE, AY_NOT_ADMITTED, SOURCE_NOT_CLEAN, RESOURCE_SUPERVISION_UNSUPPORTED,
    INTERRUPTED, INCOMPLETE, EXPORT_REFUSED, COMPILE_TIMEOUT, LAUNCH_FAILED, RESOURCE_LIMIT, OBJECT_MISSING,
    CERTIFICATE_MISSING, SIDECAR_MISMATCH, SOURCE_IDENTITY_MISMATCH, LINK_FAILED, LINK_TIMEOUT,
    NATIVE_MISMATCH, NATIVE_TIMEOUT, SOLVER_REFUSED, SOLVER_TIMEOUT, PROOF_MISSING,
    CONTROL_NOT_CONSTRUCTED, CHECKER_REJECTED_ORIGINAL, CHECKER_ACCEPTED_CORRUPTION,
    CHECKER_CONTROL_ERROR, CHECKER_TIMEOUT, LINKED_IMAGE_MISMATCH, LINKED_IMAGE_UNSUPPORTED,
    LINKED_IMAGE_CONTROL_FAILED,
)
# Lines that carry a refusal: diagnostics plus the CLI's [UNVERIFIED] proof rows.
REFUSAL_LINE = re.compile(
    r"\b(?:error|rejected|refus\w*|cannot|unsupported|unavailable|unverified)\b", re.IGNORECASE
)


def load_helper(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None or not path.is_file():
        raise RuntimeError(f"required helper is missing: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# Share the Linux floor's source-content fingerprint, report writer and
# resident-set receipt parser, and the release gate's proof-tool resolver.
SHARED = load_helper("_aot_arithmetic_linux_shared", LINUX_FLOOR)
RESOLVER = load_helper("_aot_arithmetic_tool_resolver", TOOL_RESOLVER)
# The private-cache rule the repository's scripts share (`require_private`:
# the canonical path, every canonical ancestor renamable by nobody else).
PRIVATE_CACHE = load_helper("_aot_arithmetic_private_cache", ROOT / "scripts" / "private_cache.py")
write_report = SHARED.write_report
positive_seconds = SHARED.positive_seconds
positive_gib = SHARED.positive_gib


@dataclasses.dataclass(frozen=True)
class Case:
    type: str
    shape: str
    opt_level: int

    @property
    def name(self) -> str:
        return f"{self.type}-{self.shape}-O{self.opt_level}"

    @property
    def stem(self) -> str:
        return f"{self.type}-{self.shape}"


def required_cases() -> Tuple[Case, ...]:
    return tuple(Case(ty, shape, level) for ty in TYPES for shape in SHAPES for level in OPT_LEVELS)


def denominator_errors(cases: Sequence[Case]) -> List[str]:
    """Reject any case list that is not exactly the required product."""
    errors = []
    expected = [(ty, shape, level) for ty in TYPES for shape in SHAPES for level in OPT_LEVELS]
    observed = [(case.type, case.shape, case.opt_level) for case in cases]
    if len(expected) != REQUIRED_CASES or REQUIRED_CASES * CALLS_PER_CASE != REQUIRED_CALLS:
        errors.append("the declared type/shape/optimization product does not equal 48 cases and 6,912 calls")
    if len(observed) != REQUIRED_CASES:
        errors.append(f"expected {REQUIRED_CASES} cases, observed {len(observed)}")
    duplicates = sorted({row for row in observed if observed.count(row) > 1})
    if duplicates:
        errors.append(f"duplicate cases: {duplicates}")
    missing = sorted(set(expected) - set(observed))
    if missing:
        errors.append(f"missing cases: {missing}")
    extra = sorted(set(observed) - set(expected))
    if extra:
        errors.append(f"cases outside the denominator: {extra}")
    return errors


def trust_ir_source(ty: str, shape: str) -> str:
    """Byte-identical to the archived native harness's TrustIR input."""
    rhs = "%0" if shape == "double" else "%1"
    op = "sub" if shape == "sub" else "add"
    return (
        f'; TrustIr text format v1\nmodule "aot_arithmetic"\nfuncty.0 = ({ty}, {ty}) -> ({ty})\n'
        f'fn @calculate(functy.0) {{\nbb0(%0: {ty}, %1: {ty}):\n    %2 = {op} {ty} %0, {rhs}\n'
        f'    ret %2\n}}\n'
    )


def oracle_source(ty: str, shape: str) -> str:
    """Byte-identical to the archived native harness's C oracle driver."""
    width = int(ty[1:])
    ct = ("int" if ty[0] == "i" else "uint") + str(width) + "_t"
    ut = "uint" + str(width) + "_t"
    expression = {"add": "a+b", "sub": "a-b", "double": "a+a"}[shape]
    return f'''#include <stdint.h>
#include <stdio.h>
extern {ct} calculate({ct}, {ct});
int main(void){{
uint64_t values[]={{0,1,2,4095,4096,UINT32_MAX,UINT64_C(1)<<31,UINT64_C(1)<<32,INT64_MAX,UINT64_C(1)<<63,UINT64_MAX-1,UINT64_MAX}};
for(unsigned i=0;i<12;i++)for(unsigned j=0;j<12;j++){{
uint64_t a=({ut})values[i], b=({ut})values[j];
{ut} actual=({ut})calculate(({ct})a,({ct})b), expected=({ut})({expression});
if(actual!=expected)return 1;
}}
puts("ARITHMETIC_AOT_NATIVE calls=144");return 0;
}}
'''


def compile_command(trust_cg: Path, target: str, case: Case, source: Path, proofs: Path, obj: Path) -> List[str]:
    return [
        str(trust_cg), "--format=text", "--permit-unlicensed", "--target", target, f"-O{case.opt_level}", "-c", str(source),
        "--emit-proofs", str(proofs), "-o", str(obj),
    ]


def link_command(cc: Path, oracle: Path, obj: Path, exe: Path) -> List[str]:
    return [str(cc), "-O2", "-std=c11", "-Wall", "-Wextra", "-Werror", str(oracle), str(obj), "-o", str(exe)]


def solver_command(ay: Path, query: Path, proof: Path) -> List[str]:
    return [
        str(ay), "--memory", str(SOLVER_MEMORY_MB), "-smt2", str(query), "--strict-proofs",
        "--proof", str(proof), "--proof-format", "alethe",
    ]


def checker_command(clean: Path, packet: Path) -> List[str]:
    return [str(clean), "cert", "verify-external", str(packet), "--verbose"]


def host_target(system: Optional[str] = None, machine: Optional[str] = None) -> Tuple[Tuple[str, str], Optional[str]]:
    system = sys.platform if system is None else system
    if system.startswith("linux"):
        system = "linux"
    machine = platform.machine() if machine is None else machine
    return (system, machine), HOST_TARGETS.get((system, machine))


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def child_environment(environ: Mapping[str, str], ay: Optional[str], clean: Optional[str]) -> Tuple[Dict[str, str], List[str]]:
    """Remove ambient proof/compiler knobs, then pin the resolved proof tools."""
    removed = sorted(name for name in environ if name.startswith(STRIPPED_PREFIXES))
    env = {name: value for name, value in environ.items() if not name.startswith(STRIPPED_PREFIXES)}
    if ay is not None:
        env["AY_SOLVER_PATH"] = ay
    if clean is not None:
        env["TCG_EXTERNAL_CLEAN_CHECKER"] = clean
    return env, removed


# ---------------------------------------------------------------------------
# Bounded execution
# ---------------------------------------------------------------------------

def classify_execution(returncode: int, stderr: str) -> Dict[str, bool]:
    """Attribute the shared runner's own exit statuses by their stderr lines."""
    return {
        "timed_out": returncode == TIMEOUT_EXIT and TIMEOUT_LINE in stderr,
        "resource_limited": returncode == RSS_LIMIT_EXIT and RSS_LINE in stderr,
        "launch_error": returncode in LAUNCH_ERROR_EXITS and "run_with_timeout:" in stderr,
    }


class BoundedExecutor:
    """Run each command through scripts/run_with_timeout.py in its own process group."""

    def __init__(self, grace_seconds: float = 5.0, max_rss_gib: Optional[float] = None):
        self.grace_seconds = grace_seconds
        self.max_rss_gib = max_rss_gib

    def __call__(self, command: Sequence[str], *, cwd: Path, env: Mapping[str, str],
                 timeout_seconds: float, log_stem: Path) -> dict:
        ceiling = [] if self.max_rss_gib is None else ["--max-rss-gib", repr(self.max_rss_gib)]
        bounded = [
            sys.executable, str(TIMEOUT_RUNNER), "--grace-seconds", str(self.grace_seconds),
            *ceiling, str(timeout_seconds), *command,
        ]
        stdout_path = log_stem.parent / (log_stem.name + ".stdout.log")
        stderr_path = log_stem.parent / (log_stem.name + ".stderr.log")
        started = time.monotonic()
        process = None
        interrupted = None

        def forward(signum: int, _frame: object) -> None:
            nonlocal interrupted
            if interrupted is None:
                interrupted = signum
            if process is not None:
                try:
                    process.send_signal(signum)
                except ProcessLookupError:
                    pass

        previous = {}
        with stdout_path.open("xb") as stdout, stderr_path.open("xb") as stderr:
            try:
                for signum in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
                    previous[signum] = signal.signal(signum, forward)
                process = subprocess.Popen(
                    bounded, cwd=cwd, env=dict(env), stdout=stdout, stderr=stderr,
                    stdin=subprocess.DEVNULL, start_new_session=True,
                )
                if interrupted is not None:
                    forward(interrupted, None)
                returncode = process.wait()
            except OSError as error:
                stderr.write(f"aot arithmetic runner launch error: {error}\n".encode())
                returncode = LAUNCH_ERROR_EXITS[0]
            finally:
                for signum, handler in previous.items():
                    signal.signal(signum, handler)
        result = finish_execution(command, returncode, stdout_path, stderr_path, started, timeout_seconds)
        result["bounded_command"] = bounded
        result["interrupted_signal"] = interrupted
        if self.max_rss_gib is not None:
            receipt, errors = SHARED.rss_receipt(result["stderr_text"], self.max_rss_gib)
            result["rss"] = receipt
            if errors:
                result["resource_limited"] = True
                result["resource_errors"] = errors
        return result


def finish_execution(command: Sequence[str], returncode: int, stdout_path: Path, stderr_path: Path,
                     started: float, timeout_seconds: float) -> dict:
    stdout_bytes = stdout_path.read_bytes()
    stderr_bytes = stderr_path.read_bytes()
    stderr_text = stderr_bytes.decode("utf-8", errors="replace")
    return {
        "command": list(command), "returncode": returncode, "timeout_seconds": timeout_seconds,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "stdout_log": stdout_path.name, "stderr_log": stderr_path.name,
        "stdout_sha256": sha256_bytes(stdout_bytes), "stderr_sha256": sha256_bytes(stderr_bytes),
        "stdout_text": stdout_bytes.decode("utf-8", errors="replace"), "stderr_text": stderr_text,
        "interrupted_signal": None, **classify_execution(returncode, stderr_text),
    }


def public_execution(result: dict) -> dict:
    """The retained record; transcripts live in their hashed log files."""
    return {key: value for key, value in result.items() if key not in ("stdout_text", "stderr_text")}


# ---------------------------------------------------------------------------
# Sidecar audit (ported from audit-aot-arithmetic-sidecars-second.py)
# ---------------------------------------------------------------------------

class AuditFailure(Exception):
    def __init__(self, failure_class: str, detail: str):
        super().__init__(detail)
        self.failure_class = failure_class
        self.detail = detail


def _load_json(path: Path, label: str) -> dict:
    if not path.is_file():
        raise AuditFailure(CERTIFICATE_MISSING, f"{label} is missing: {path.name}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, ValueError) as error:
        raise AuditFailure(SIDECAR_MISMATCH, f"{label} is not valid JSON: {error}") from error
    if not isinstance(value, dict):
        raise AuditFailure(SIDECAR_MISMATCH, f"{label} is not a JSON object")
    return value


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise AuditFailure(SIDECAR_MISMATCH, detail)


def audit_case(proofs: Path, obj: Path, target: str) -> dict:
    """Check one case's exported object and sidecars; raise AuditFailure."""
    if not obj.is_file() or obj.stat().st_size == 0:
        raise AuditFailure(OBJECT_MISSING, f"compiler exited 0 without publishing {obj.name}")
    raw_object = obj.read_bytes()
    magic = OBJECT_MAGIC[target]
    _require(raw_object.startswith(magic), f"object is not a {target} object (magic {raw_object[:4].hex()})")
    digest = sha256_bytes(raw_object)
    if not proofs.is_dir():
        raise AuditFailure(CERTIFICATE_MISSING, "compiler exited 0 without publishing its proof directory")
    lower = _load_json(proofs / f"{FUNCTION}.lowering.json", "lowering sidecar")
    trust = _load_json(proofs / f"{FUNCTION}.trust-proof-cert.json", "trust-proof-cert sidecar")
    queries = sorted(proofs.glob("**/*.smt2"))
    if not queries:
        raise AuditFailure(CERTIFICATE_MISSING, "no exported SMT query")
    try:
        _require(lower.get("schema") == "trust-cg.lowering_certificate.v1", "lowering schema differs")
        _require(lower.get("function") == FUNCTION, "lowering function differs")
        _require(lower.get("target") == target, f"lowering target {lower.get('target')!r} is not {target}")
        _require(lower.get("machine_code_hash") == digest, "lowering machine_code_hash does not bind the object bytes")
        _require(lower.get("result") == "verified", "lowering result is not verified")
        _require(lower.get("overall_strength") == {"kind": "smt_unsat"}, "lowering overall strength is not smt_unsat")
        rules = lower.get("rule_proofs")
        _require(isinstance(rules, list) and len(rules) == 2, "lowering must carry exactly two rule proofs")
        for rule in rules:
            result = rule.get("result", {})
            _require(
                result.get("status") == "proved" and result.get("strength") == {"kind": "smt_unsat"}
                and result.get("solver") == "ay_cli",
                f"rule {rule.get('rule_name')!r} is not a proved AY smt_unsat result",
            )
        kinds = {rule.get("check_kind") for rule in rules}
        _require({"instruction_lowering", "regalloc"} <= kinds, "lowering lacks instruction_lowering or regalloc rules")
        _require(trust.get("version") == 2 and trust.get("function") == FUNCTION, "trust-proof-cert identity differs")
        _require(trust.get("function_hash") == lower.get("trust_ir_hash"), "trust-proof-cert function_hash differs")
        formula = trust.get("vc_snapshot", {}).get("formula_json")
        _require(isinstance(formula, str), "trust-proof-cert has no vc_snapshot.formula_json")
        snapshot = json.loads(formula)
        for key in ("function", "target", "trust_ir_hash", "machine_code_hash", "compiler_config_hash", "rule_proofs"):
            _require(snapshot.get(key) == lower.get(key), f"vc_snapshot {key} differs from the lowering sidecar")
        vc_hash = trust.get("vc_hash")
        _require(
            isinstance(vc_hash, list) and bytes(vc_hash).hex()
            == sha256_bytes(("lowering_equivalence:" + formula).encode("utf-8")),
            "vc_hash is not the lowering-equivalence domain hash of its snapshot",
        )
        steps = trust.get("chain", {}).get("steps") or [{}]
        step = steps[-1]
        _require(
            step.get("step_type") == "CodegenLowering" and step.get("output_hash") == digest
            and step.get("input_hash") == lower.get("trust_ir_hash"),
            "final CodegenLowering chain step does not bind TrustIR input and object output",
        )
    except (TypeError, ValueError, AttributeError) as error:
        raise AuditFailure(SIDECAR_MISMATCH, f"malformed sidecar field: {error}") from error
    rows = []
    categories = []
    for query in queries:
        raw = query.read_bytes()
        meta = _load_json(query.with_suffix(".cert"), f"metadata for {query.name}")
        _require(
            meta.get("result") == "verified" and meta.get("verified") is True
            and meta.get("strength") == "Formal" and meta.get("solver") == "ay",
            f"{query.name} metadata is not verified Formal AY evidence",
        )
        _require(meta.get("function") == FUNCTION, f"{query.name} metadata names function {meta.get('function')!r}")
        if "--" in query.stem:
            _require(query.stem.rsplit("--", 1)[1] == sha256_bytes(raw), f"{query.name} name does not hash its query")
        category = query.parent.name if query.parent != proofs else ""
        categories.append(category)
        rows.append({
            "path": str(query.relative_to(proofs)), "category": category, "sha256": sha256_bytes(raw),
            "proof_name": meta.get("proof_name"),
        })
    _require(
        sorted(categories) == ["Arithmetic", "FrameLayout"],
        f"expected exactly one Arithmetic and one FrameLayout query, observed {sorted(categories)}",
    )
    # Each exported query must be the one the sidecar records as proved: the
    # CLI writes the same rule name into the lowering row and the query record.
    proof_names = [row["proof_name"] for row in rows]
    rule_names = [rule.get("rule_name") for rule in rules]
    _require(
        all(isinstance(name, str) for name in proof_names + rule_names)
        and sorted(proof_names) == sorted(rule_names),
        f"exported query records {sorted(map(str, proof_names))} do not name the lowering sidecar's "
        f"proved rules {sorted(map(str, rule_names))}",
    )
    for cert in sorted(proofs.glob("**/*.cert")):
        meta = _load_json(cert, f"record {cert.name}")
        _require(meta.get("verified") is True, f"{cert.relative_to(proofs)} is not verified")
    return {
        "object_sha256": digest, "trust_ir_hash": lower.get("trust_ir_hash"),
        "compiler_config_hash": lower.get("compiler_config_hash"), "queries": rows,
    }


# ---------------------------------------------------------------------------
# Linked-image binding (ELF64 little-endian AArch64)
# ---------------------------------------------------------------------------
#
# The sidecar audit binds the certificate to the object bytes through
# machine_code_hash. This step checks that the executable cc produced from that
# object still carries them: the certified function's words at its link-time
# address, and the linked effect of the object's one .eh_frame R_AARCH64_PREL32
# (the FDE pc_begin of the function). It is a byte comparison of the runner's
# own parse, not a certificate over the linked image. Everything else in the
# image (other code, dynamic relocations, loader behaviour, CFI semantics) is
# outside it.

class LinkedImageFailure(Exception):
    def __init__(self, failure_class: str, detail: str):
        super().__init__(detail)
        self.failure_class = failure_class
        self.detail = detail


class ElfError(ValueError):
    """A structural defect: the file is not the ELF this check can read."""


class ElfUnsupported(ElfError):
    """A well-formed construct the check does not model."""


EM_AARCH64 = 183
ET_REL, ET_EXEC, ET_DYN = 1, 2, 3
SHT_PROGBITS, SHT_SYMTAB, SHT_RELA, SHT_NOBITS, SHT_REL = 1, 2, 4, 8, 9
SHF_ALLOC, SHF_EXECINSTR = 0x2, 0x4
SHN_UNDEF, SHN_LORESERVE = 0, 0xFF00
PT_LOAD = 1
PF_X, PF_W, PF_R = 1, 2, 4
STT_FUNC, STT_SECTION = 2, 3
STB_GLOBAL = 1
R_AARCH64_PREL32 = 261
DW_EH_PE_PCREL_SDATA4 = 0x1B
DW_EH_PE_UDATA4 = 0x03
DW_EH_PE_DATAREL_SDATA4 = 0x3B
AARCH64_NOP = 0xD503201F
AARCH64_BRK_0 = 0xD4200000
ADDRESS_MASK = (1 << 64) - 1
# Per-case negatives: each must be refused as linked-image-mismatch.
LINKED_IMAGE_CONTROLS = ("patched-function-word", "patched-fde-pc-begin", "foreign-object")
LINKED_IMAGE_UNCHECKED = (
    "CFI program semantics: the function's CIE/FDE bytes are compared modulo trailing DW_CFA_nop padding",
    "image bytes outside the certified function, its FDE and its .eh_frame_hdr entry",
    "dynamic relocations, symbol resolution by the loader, memory permissions at run time",
)


def _unpack(fmt: str, data: bytes, offset: int, what: str) -> tuple:
    size = struct.calcsize(fmt)
    if offset < 0 or offset + size > len(data):
        raise ElfError(f"{what} at offset {offset:#x} lies outside the {len(data)}-byte file")
    return struct.unpack_from(fmt, data, offset)


def _slice(data: bytes, offset: int, size: int, what: str) -> bytes:
    if offset < 0 or size < 0 or offset + size > len(data):
        raise ElfError(f"{what} [{offset:#x}, +{size:#x}) lies outside the {len(data)}-byte range")
    return data[offset:offset + size]


def _cstring(data: bytes, offset: int, what: str) -> str:
    if offset < 0 or offset >= len(data):
        raise ElfError(f"{what} string offset {offset:#x} is outside its table")
    end = data.find(b"\0", offset)
    if end < 0:
        raise ElfError(f"{what} string at {offset:#x} is not NUL-terminated")
    return data[offset:end].decode("utf-8", errors="replace")


def _uleb(data: bytes, offset: int, end: int) -> Tuple[int, int]:
    value = shift = 0
    while True:
        if offset >= end:
            raise ElfError("truncated ULEB128 in .eh_frame")
        byte = data[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        shift += 7
        if not byte & 0x80:
            return value, offset


def _sleb(data: bytes, offset: int, end: int) -> Tuple[int, int]:
    value = shift = 0
    while True:
        if offset >= end:
            raise ElfError("truncated SLEB128 in .eh_frame")
        byte = data[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        shift += 7
        if not byte & 0x80:
            if byte & 0x40:
                value -= 1 << shift
            return value, offset


@dataclasses.dataclass(frozen=True)
class ElfSection:
    index: int
    name: str
    type: int
    flags: int
    addr: int
    offset: int
    size: int
    link: int
    info: int
    entsize: int


@dataclasses.dataclass(frozen=True)
class ElfSymbol:
    index: int
    name: str
    info: int
    shndx: int
    value: int
    size: int

    @property
    def kind(self) -> int:
        return self.info & 0xF

    @property
    def binding(self) -> int:
        return self.info >> 4


@dataclasses.dataclass(frozen=True)
class ElfSegment:
    type: int
    flags: int
    offset: int
    vaddr: int
    filesz: int
    memsz: int


class ElfFile:
    """The ELF64 little-endian AArch64 subset this check reads, bounds-checked."""

    def __init__(self, data: bytes, label: str):
        self.data = data
        self.label = label
        if data[:4] != b"\x7fELF":
            raise ElfUnsupported(f"{label} is not an ELF file (magic {data[:4].hex() or 'empty'})")
        if len(data) < 64:
            raise ElfError(f"{label} is shorter than an ELF64 header")
        if data[4] != 2 or data[5] != 1:
            raise ElfUnsupported(f"{label} is not ELF64 little-endian (class {data[4]}, data {data[5]})")
        (self.type, self.machine, _version, _entry, phoff, shoff, _flags, _ehsize, phentsize, phnum,
         shentsize, shnum, shstrndx) = _unpack("<HHIQQQIHHHHHH", data, 16, f"{label} header")
        if self.machine != EM_AARCH64:
            raise ElfUnsupported(f"{label} machine {self.machine} is not AArch64 ({EM_AARCH64})")
        if shnum == 0 or shstrndx >= shnum:
            raise ElfUnsupported(f"{label} uses extended or absent section numbering")
        if shentsize != 64 or (phnum and phentsize != 56):
            raise ElfError(f"{label} header entry sizes {shentsize}/{phentsize} are not ELF64's 64/56")
        raw = []
        for index in range(shnum):
            raw.append(_unpack("<IIQQQQIIQQ", data, shoff + index * 64, f"{label} section header {index}"))
        names = raw[shstrndx]
        name_table = _slice(data, names[4], names[5], f"{label} section-name table")
        self.sections = [
            ElfSection(index, _cstring(name_table, row[0], f"{label} section name"), row[1], row[2], row[3],
                       row[4], row[5], row[6], row[7], row[9])
            for index, row in enumerate(raw)
        ]
        self.segments = []
        for index in range(phnum):
            p_type, flags, offset, vaddr, _paddr, filesz, memsz, _align = _unpack(
                "<IIQQQQQQ", data, phoff + index * 56, f"{label} program header {index}")
            self.segments.append(ElfSegment(p_type, flags, offset, vaddr, filesz, memsz))

    def section_bytes(self, section: ElfSection) -> bytes:
        if section.type == SHT_NOBITS:
            return b""
        return _slice(self.data, section.offset, section.size, f"{self.label} section {section.name}")

    def named(self, name: str) -> List[ElfSection]:
        return [section for section in self.sections if section.name == name]

    def symbols(self) -> List[ElfSymbol]:
        tables = [section for section in self.sections if section.type == SHT_SYMTAB]
        if len(tables) != 1:
            raise ElfError(f"{self.label} has {len(tables)} .symtab sections; the function is located by .symtab")
        table = tables[0]
        if table.entsize != 24 or table.size % 24 or table.link >= len(self.sections):
            raise ElfError(f"{self.label} .symtab has entry size {table.entsize} / link {table.link}")
        strings = self.section_bytes(self.sections[table.link])
        data = self.section_bytes(table)
        rows = []
        for index in range(table.size // 24):
            name, info, _other, shndx, value, size = struct.unpack_from("<IBBHQQ", data, index * 24)
            rows.append(ElfSymbol(index, _cstring(strings, name, f"{self.label} symbol name") if name else "",
                                  info, shndx, value, size))
        return rows


def _defined(elf: ElfFile, function: str) -> List[ElfSymbol]:
    return [symbol for symbol in elf.symbols() if symbol.name == function and symbol.shndx != SHN_UNDEF]


def _pointer_size(encoding: int) -> Optional[int]:
    return {0x00: 8, 0x02: 2, 0x03: 4, 0x04: 8, 0x0A: 2, 0x0B: 4, 0x0C: 8}.get(encoding & 0x0F)


def parse_eh_frame(data: bytes, base: int) -> Tuple[Dict[int, dict], List[dict]]:
    """CIEs by section offset and FDEs in order; `base` is the section's address."""
    cies: Dict[int, dict] = {}
    fdes: List[dict] = []
    offset = 0
    while offset + 4 <= len(data):
        (length,) = struct.unpack_from("<I", data, offset)
        if length == 0:
            break
        if length == 0xFFFFFFFF:
            raise ElfUnsupported("64-bit DWARF .eh_frame records are not modelled")
        end = offset + 4 + length
        if length < 4 or end > len(data):
            raise ElfError(f".eh_frame record at {offset:#x} overruns the section")
        (ident,) = struct.unpack_from("<I", data, offset + 4)
        if ident == 0:
            cies[offset] = _parse_cie(data, offset, end)
        else:
            cie = cies.get(offset + 4 - ident)
            if cie is None:
                raise ElfError(f".eh_frame FDE at {offset:#x} names no preceding CIE")
            fdes.append(_parse_fde(data, offset, end, cie, base))
        offset = end
    return cies, fdes


def _parse_cie(data: bytes, offset: int, end: int) -> dict:
    version = _slice(data, offset + 8, 1, "CIE version")[0]
    if version not in (1, 3):
        raise ElfUnsupported(f"CIE at {offset:#x} has version {version}")
    terminator = data.find(b"\0", offset + 9, end)
    if terminator < 0:
        raise ElfError(f"CIE at {offset:#x} has an unterminated augmentation string")
    augmentation = data[offset + 9:terminator].decode("ascii", errors="replace")
    cursor = terminator + 1
    code_align, cursor = _uleb(data, cursor, end)
    data_align, cursor = _sleb(data, cursor, end)
    if version == 1:
        return_column = _slice(data, cursor, 1, "CIE return column")[0]
        cursor += 1
    else:
        return_column, cursor = _uleb(data, cursor, end)
    fde_encoding = 0x00
    augmentation_data = b""
    if augmentation.startswith("z"):
        length, cursor = _uleb(data, cursor, end)
        augmentation_data = _slice(data, cursor, length, "CIE augmentation data")
        cursor += length
        position = 0
        for letter in augmentation[1:]:
            if letter == "R":
                fde_encoding = _slice(augmentation_data, position, 1, "CIE R encoding")[0]
                position += 1
            elif letter == "L":
                position += 1
            elif letter == "P":
                encoding = _slice(augmentation_data, position, 1, "CIE P encoding")[0]
                size = _pointer_size(encoding)
                if size is None:
                    raise ElfUnsupported(f"CIE at {offset:#x} personality encoding {encoding:#x} is not modelled")
                position += 1 + size
            elif letter not in ("S", "B", "G"):
                raise ElfUnsupported(f"CIE at {offset:#x} augmentation {augmentation!r} is not modelled")
    elif augmentation:
        raise ElfUnsupported(f"CIE at {offset:#x} augmentation {augmentation!r} is not modelled")
    return {
        "offset": offset, "version": version, "augmentation": augmentation, "code_align": code_align,
        "data_align": data_align, "return_column": return_column, "fde_encoding": fde_encoding,
        "augmentation_data": augmentation_data, "instructions": data[cursor:end],
    }


def _parse_fde(data: bytes, offset: int, end: int, cie: dict, base: int) -> dict:
    if cie["fde_encoding"] != DW_EH_PE_PCREL_SDATA4:
        raise ElfUnsupported(f"FDE at {offset:#x} pointer encoding {cie['fde_encoding']:#x} is not "
                             f"pcrel|sdata4 ({DW_EH_PE_PCREL_SDATA4:#x})")
    field = offset + 8
    stored, pc_range = _unpack("<ii", data, field, f"FDE at {offset:#x} address range")
    cursor = field + 8
    if cie["augmentation"].startswith("z"):
        length, cursor = _uleb(data, cursor, end)
        cursor += length
    if pc_range < 0 or cursor > end:
        raise ElfError(f"FDE at {offset:#x} is malformed")
    return {
        "offset": offset, "cie": cie, "pc_begin_field": field, "stored": stored,
        "pc_begin": (base + field + stored) & ADDRESS_MASK, "pc_range": pc_range,
        "instructions": data[cursor:end],
    }


def _cfi_equal(left: dict, right: dict) -> bool:
    """CIE and FDE programs equal modulo the trailing DW_CFA_nop padding a linker trims."""
    keys = ("version", "augmentation", "code_align", "data_align", "return_column", "fde_encoding",
            "augmentation_data")
    return (all(left["cie"][key] == right["cie"][key] for key in keys)
            and left["cie"]["instructions"].rstrip(b"\0") == right["cie"]["instructions"].rstrip(b"\0")
            and left["instructions"].rstrip(b"\0") == right["instructions"].rstrip(b"\0"))


def certified_object_model(data: bytes, function: str = FUNCTION) -> dict:
    """The certified function's bytes and relocation sites; raise ElfError outside the model."""
    obj = ElfFile(data, "certified object")
    if obj.type != ET_REL:
        raise ElfUnsupported(f"certified object type {obj.type} is not ET_REL")
    symbols = _defined(obj, function)
    if len(symbols) != 1:
        raise ElfError(f"certified object defines {function!r} {len(symbols)} times")
    symbol = symbols[0]
    if (symbol.kind != STT_FUNC or symbol.binding != STB_GLOBAL
            or symbol.shndx >= min(SHN_LORESERVE, len(obj.sections))):
        raise ElfUnsupported(f"certified {function!r} is not a global function in a regular section")
    text = obj.sections[symbol.shndx]
    if text.name != ".text" or text.type != SHT_PROGBITS or text.flags & (SHF_ALLOC | SHF_EXECINSTR) != (
            SHF_ALLOC | SHF_EXECINSTR):
        raise ElfUnsupported(f"certified {function!r} is in {text.name!r}, not an executable .text")
    if symbol.value != 0 or symbol.size != text.size or symbol.size == 0 or symbol.size % 4:
        raise ElfUnsupported(f"certified {function!r} [{symbol.value:#x}, +{symbol.size:#x}) is not the whole "
                             f"{text.size:#x}-byte .text in whole instruction words")
    other = [section.name for section in obj.sections
             if section.flags & SHF_EXECINSTR and section.size and section.index != text.index]
    if other:
        raise ElfUnsupported(f"certified object has other executable sections {other}")
    symbols_by_index = {row.index: row for row in obj.symbols()}
    relocations = []
    for section in obj.sections:
        if section.type == SHT_REL:
            raise ElfUnsupported(f"certified object has SHT_REL section {section.name}; only RELA is modelled")
        if section.type != SHT_RELA:
            continue
        if section.entsize != 24 or section.size % 24 or section.info >= len(obj.sections):
            raise ElfError(f"relocation section {section.name} is malformed")
        target = obj.sections[section.info]
        rows = obj.section_bytes(section)
        for index in range(section.size // 24):
            offset, info, addend = struct.unpack_from("<QQq", rows, index * 24)
            referenced = symbols_by_index.get(info >> 32)
            if referenced is None:
                raise ElfError(f"relocation in {section.name} names symbol {info >> 32} outside .symtab")
            # A section symbol has no name of its own; report its section's.
            label = referenced.name or (
                obj.sections[referenced.shndx].name if referenced.shndx < len(obj.sections) else "")
            relocations.append({
                "section": target.name, "section_index": target.index, "type": info & 0xFFFFFFFF,
                "offset": offset, "symbol": label, "symbol_shndx": referenced.shndx,
                "symbol_value": referenced.value, "addend": addend,
            })
    text_relocations = [row for row in relocations if row["section_index"] == text.index]
    if text_relocations:
        raise ElfUnsupported(f"{len(text_relocations)} relocation(s) patch the certified .text; relocated "
                             "function bodies are not modelled by a byte comparison")
    eh_frames = obj.named(".eh_frame")
    fdes: Dict[int, dict] = {}
    if eh_frames:
        _, parsed = parse_eh_frame(obj.section_bytes(eh_frames[0]), 0)
        fdes = {fde["pc_begin_field"]: fde for fde in parsed}
    for row in relocations:
        if row["section"] != ".eh_frame" or row["type"] != R_AARCH64_PREL32:
            raise ElfUnsupported(f"relocation type {row['type']} against {row['section']} is not the modelled "
                                 f".eh_frame R_AARCH64_PREL32")
        if row["symbol_shndx"] != text.index:
            raise ElfUnsupported(f".eh_frame relocation at {row['offset']:#x} does not reference the certified .text")
        fde = fdes.get(row["offset"])
        if fde is None:
            raise ElfUnsupported(f".eh_frame relocation at {row['offset']:#x} is not an FDE pc_begin field")
        if row["symbol_value"] + row["addend"] != symbol.value or fde["pc_range"] != symbol.size:
            raise ElfUnsupported(f"the FDE at .eh_frame+{fde['offset']:#x} does not cover exactly {function!r}")
        row["fde"] = fde
    by_section: Dict[str, int] = {}
    for row in relocations:
        by_section[row["section"]] = by_section.get(row["section"], 0) + 1
    return {"text": obj.section_bytes(text), "symbol": symbol, "relocations": relocations,
            "relocation_counts": {"total": len(relocations), "text": 0, "by_section": by_section}}


def _check_eh_frame_hdr(image: ElfFile, eh_frame: ElfSection, function_va: int, fde_va: int) -> dict:
    headers = image.named(".eh_frame_hdr")
    if not headers:
        return {"status": "absent"}
    header = headers[0]
    data = image.section_bytes(header)
    version, frame_encoding, count_encoding, table_encoding = _unpack("<BBBB", data, 0, ".eh_frame_hdr")
    if (version, frame_encoding, count_encoding, table_encoding) != (
            1, DW_EH_PE_PCREL_SDATA4, DW_EH_PE_UDATA4, DW_EH_PE_DATAREL_SDATA4):
        raise ElfUnsupported(f".eh_frame_hdr version/encodings {version}/{frame_encoding:#x}/{count_encoding:#x}/"
                             f"{table_encoding:#x} are not modelled")
    frame_pointer, count = _unpack("<iI", data, 4, ".eh_frame_hdr pointers")
    if (header.addr + 4 + frame_pointer) & ADDRESS_MASK != eh_frame.addr:
        raise ElfError(".eh_frame_hdr does not point at .eh_frame")
    _slice(data, 12, 8 * count, ".eh_frame_hdr search table")
    entries = [
        (index, *((header.addr + value) & ADDRESS_MASK for value in struct.unpack_from("<ii", data, 12 + 8 * index)))
        for index in range(count)
    ]
    matches = [row for row in entries if row[1] == function_va]
    if len(matches) != 1 or matches[0][2] != fde_va:
        raise ElfError(f".eh_frame_hdr has {len(matches)} search entries for {function_va:#x}"
                       + (f" pointing at {matches[0][2]:#x}, not the FDE at {fde_va:#x}" if len(matches) == 1 else ""))
    return {"status": "checked", "entries": count, "entry_index": matches[0][0], "fde_va": fde_va}


def _linked_function(image: ElfFile, function: str, size: int) -> dict:
    if image.type not in (ET_EXEC, ET_DYN):
        raise ElfError(f"linked image type {image.type} is not an executable (ET_EXEC/ET_DYN)")
    symbols = _defined(image, function)
    if len(symbols) != 1:
        raise ElfError(f"linked image defines {function!r} {len(symbols)} times in .symtab")
    symbol = symbols[0]
    if symbol.kind != STT_FUNC or symbol.shndx >= min(SHN_LORESERVE, len(image.sections)):
        raise ElfError(f"linked {function!r} is not a function in a regular section")
    if symbol.size != size:
        raise ElfError(f"linked {function!r} is {symbol.size} bytes; the certified .text is {size} bytes")
    section = image.sections[symbol.shndx]
    va = symbol.value
    if (section.type != SHT_PROGBITS or section.flags & (SHF_ALLOC | SHF_EXECINSTR) != (SHF_ALLOC | SHF_EXECINSTR)
            or not section.addr <= va or va + size > section.addr + section.size):
        raise ElfError(f"linked {function!r} at {va:#x} is not inside an executable PROGBITS section "
                       f"({section.name!r})")
    loads = [segment for segment in image.segments
             if segment.type == PT_LOAD and segment.vaddr <= va and va + size <= segment.vaddr + segment.filesz]
    if len(loads) != 1:
        raise ElfError(f"{len(loads)} PT_LOAD segments map linked {function!r} at {va:#x}")
    segment = loads[0]
    if not segment.flags & PF_X:
        raise ElfError(f"the PT_LOAD segment mapping {va:#x} is not executable")
    offset = segment.offset + (va - segment.vaddr)
    if offset != section.offset + (va - section.addr):
        raise ElfError(f"section and segment file offsets of {va:#x} disagree")
    return {"symbol": symbol, "section": section, "segment": segment, "va": va, "offset": offset,
            "bytes": _slice(image.data, offset, size, f"linked {function!r}")}


def bind_linked_image(object_bytes: bytes, image_bytes: bytes, target: str, function: str = FUNCTION) -> dict:
    """Show that the linked image carries the certified function; raise LinkedImageFailure."""
    if OBJECT_MAGIC.get(target) != b"\x7fELF":
        raise LinkedImageFailure(LINKED_IMAGE_UNSUPPORTED, f"linked-image binding parses ELF64 only; the {target} "
                                                           "image is not checked")
    try:
        model = certified_object_model(object_bytes, function)
    except ElfError as error:
        raise LinkedImageFailure(LINKED_IMAGE_UNSUPPORTED, f"certified object: {error}") from error
    text = model["text"]
    try:
        image = ElfFile(image_bytes, "linked image")
    except ElfError as error:
        # An image that is not an ELF64 AArch64 file cannot carry the certified words.
        raise LinkedImageFailure(LINKED_IMAGE_MISMATCH, f"linked image: {error}") from error
    try:
        linked = _linked_function(image, function, len(text))
        words = len(text) // 4
        differing = [index for index in range(words)
                     if text[4 * index:4 * index + 4] != linked["bytes"][4 * index:4 * index + 4]]
        if differing:
            first = differing[0]
            raise LinkedImageFailure(LINKED_IMAGE_MISMATCH, (
                f"{len(differing)} of {words} instruction word(s) of linked {function!r} differ from the certified "
                f"object; first at word {first} (VA {linked['va'] + 4 * first:#x}, file offset "
                f"{linked['offset'] + 4 * first:#x}): linked "
                f"{struct.unpack_from('<I', linked['bytes'], 4 * first)[0]:#010x}, certified "
                f"{struct.unpack_from('<I', text, 4 * first)[0]:#010x}"))
        placement = linked["va"] - model["symbol"].value
        effects = []
        hdr: dict = {"status": "absent"}
        if model["relocations"]:
            frames = image.named(".eh_frame")
            if len(frames) != 1:
                raise ElfError(f"linked image has {len(frames)} .eh_frame sections")
            eh_frame = frames[0]
            _, fdes = parse_eh_frame(image.section_bytes(eh_frame), eh_frame.addr)
            for row in model["relocations"]:
                expected = (placement + row["symbol_value"] + row["addend"]) & ADDRESS_MASK
                matches = [fde for fde in fdes if fde["pc_begin"] == expected]
                if len(matches) != 1:
                    raise ElfError(f"{len(matches)} linked FDEs resolve pc_begin to {function!r} at {expected:#x}; the "
                                   f"certified R_AARCH64_PREL32 at .eh_frame+{row['offset']:#x} requires exactly one")
                fde = matches[0]
                if fde["pc_range"] != row["fde"]["pc_range"] or not _cfi_equal(fde, row["fde"]):
                    raise ElfError(f"the linked FDE for {function!r} at .eh_frame+{fde['offset']:#x} differs from the "
                                   "certified object's CIE/FDE")
                effects.append({
                    "section": row["section"], "type": "R_AARCH64_PREL32", "offset": row["offset"],
                    "symbol": row["symbol"], "addend": row["addend"], "site": "FDE pc_begin", "status": "checked",
                    "field_va": eh_frame.addr + fde["pc_begin_field"],
                    "field_file_offset": eh_frame.offset + fde["pc_begin_field"],
                    "stored_word": fde["stored"] & 0xFFFFFFFF, "resolves_to": fde["pc_begin"],
                    "fde_va": eh_frame.addr + fde["offset"], "pc_range": fde["pc_range"], "cfi_matches_object": True,
                })
            hdr = _check_eh_frame_hdr(image, eh_frame, linked["va"], effects[0]["fde_va"])
    except ElfUnsupported as error:
        raise LinkedImageFailure(LINKED_IMAGE_UNSUPPORTED, f"linked image: {error}") from error
    except ElfError as error:
        raise LinkedImageFailure(LINKED_IMAGE_MISMATCH, f"linked image: {error}") from error
    segment = linked["segment"]
    return {
        "status": "bound", "container": "ELF64 little-endian AArch64",
        "image_sha256": sha256_bytes(image_bytes), "image_bytes": len(image_bytes),
        "image_type": {ET_EXEC: "ET_EXEC", ET_DYN: "ET_DYN"}[image.type],
        "function": function, "function_va": linked["va"], "function_file_offset": linked["offset"],
        "function_size": len(text), "function_words": len(text) // 4, "function_section": linked["section"].name,
        "load_segment": {
            "vaddr": segment.vaddr, "offset": segment.offset, "filesz": segment.filesz,
            "flags": "".join(flag if segment.flags & bit else "-"
                             for flag, bit in (("R", PF_R), ("W", PF_W), ("X", PF_X))),
        },
        "object_text_sha256": sha256_bytes(text), "linked_function_sha256": sha256_bytes(linked["bytes"]),
        "object_relocations": model["relocation_counts"], "relocation_effects": effects, "eh_frame_hdr": hdr,
        "unchecked": list(LINKED_IMAGE_UNCHECKED),
    }


def linked_image_patches(image_bytes: bytes, record: dict) -> List[Tuple[str, Optional[bytes], dict]]:
    """The two in-place negatives; None marks a patch the record gives no site for."""
    rows: List[Tuple[str, Optional[bytes], dict]] = []
    offset, size = record.get("function_file_offset"), record.get("function_size")
    if (isinstance(offset, int) and isinstance(size, int) and size >= 4 and 0 <= offset
            and offset + size <= len(image_bytes)):
        site = offset + size - 4
        (word,) = struct.unpack_from("<I", image_bytes, site)
        patched = AARCH64_NOP if word != AARCH64_NOP else AARCH64_BRK_0
        rows.append(("patched-function-word",
                     image_bytes[:site] + struct.pack("<I", patched) + image_bytes[site + 4:],
                     {"file_offset": site, "original_word": word, "patched_word": patched}))
    else:
        rows.append(("patched-function-word", None, {}))
    effects = record.get("relocation_effects") or []
    field = effects[0].get("field_file_offset") if effects else None
    if isinstance(field, int) and 0 <= field and field + 4 <= len(image_bytes):
        (stored,) = struct.unpack_from("<i", image_bytes, field)
        patched = (stored + 4 + (1 << 31)) % (1 << 32) - (1 << 31)
        rows.append(("patched-fde-pc-begin",
                     image_bytes[:field] + struct.pack("<i", patched) + image_bytes[field + 4:],
                     {"file_offset": field, "original_word": stored & 0xFFFFFFFF,
                      "patched_word": patched & 0xFFFFFFFF}))
    else:
        rows.append(("patched-fde-pc-begin", None, {}))
    return rows


def foreign_object_source() -> str:
    """A same-named C definition whose code differs from every certified case."""
    return '''#include <stdint.h>
/* Foreign definition of the certified symbol for the linked-image control. */
uint64_t calculate(uint64_t a, uint64_t b);
uint64_t calculate(uint64_t a, uint64_t b){return (a ^ b) * UINT64_C(0x9e3779b97f4a7c15);}
'''


def refusal_signature(stdout: str, stderr: str, out: Path) -> str:
    """The CLI's refusal lines with this run's output directory elided."""
    text = stderr + "\n" + stdout
    for prefix in sorted({str(out), str(out.resolve())}, key=len, reverse=True):
        text = text.replace(prefix, "<out>")
    lines = [line.strip()[:400] for line in text.splitlines() if REFUSAL_LINE.search(line)]
    if not lines:
        lines = [line.strip()[:400] for line in text.splitlines() if line.strip()][-5:]
    return "\n".join(lines[:12]) or "no diagnostic output"


# ---------------------------------------------------------------------------
# Independent replay (ported from replay-aot-arithmetic-first.py)
# ---------------------------------------------------------------------------

def opposite_premise(query: str) -> Optional[str]:
    if query.count("(assert ") != 1:
        return None
    start = query.index("(assert ") + len("(assert ")
    depth = 0
    for index in range(start, len(query)):
        if query[index] == "(":
            depth += 1
        elif query[index] == ")":
            if depth == 0:
                return query[:start] + "(not " + query[start:index] + ")" + query[index:]
            depth -= 1
    return None


def corruption_controls(certificate: dict) -> List[Tuple[str, Optional[dict]]]:
    """The three recorded controls; None marks a control that cannot be built."""
    proof = certificate["proof"]
    hole = dict(certificate, proof=re.sub(r":rule\s+[^\s)]+", ":rule hole", proof, count=1))
    empty = dict(certificate, proof=proof.replace("(cl)", "(cl false)"))
    opposite = opposite_premise(certificate["problem"])
    rows = [
        ("hole", hole),
        ("no-empty-clause", empty),
        ("opposite-premise", None if opposite is None else dict(certificate, problem=opposite)),
    ]
    return [(label, value if value is not None and value != certificate else None) for label, value in rows]


def packet_bytes(certificate: dict) -> bytes:
    return (json.dumps(certificate) + "\n").encode("utf-8")


# ---------------------------------------------------------------------------
# Tool identities
# ---------------------------------------------------------------------------

def version_probe(path: Path, env: Mapping[str, str]) -> dict:
    try:
        result = subprocess.run(
            [str(path), "--version"], capture_output=True, text=True, timeout=20,
            check=False, env=dict(env), stdin=subprocess.DEVNULL,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return {"returncode": None, "error": str(error)}
    return {"returncode": result.returncode, "stdout": result.stdout[-2000:], "stderr": result.stderr[-2000:]}


def executable_identity(path: Path) -> dict:
    resolved = path.resolve(strict=True)
    if not resolved.is_file() or not os.access(resolved, os.X_OK):
        raise OSError(f"{path} is not an executable file")
    # Commands run from per-case directories, so a relative spelling is made absolute.
    return {"path": str(path.absolute()), "resolved": str(resolved), "sha256": sha256_file(resolved),
            "size": resolved.stat().st_size}


def resolve_tools(trust_cg: Path, cc: str, environ: Mapping[str, str], system: str,
                  target: str) -> Tuple[dict, List[str]]:
    tools: dict = {}
    errors: List[str] = []
    try:
        tools["trust_cg"] = executable_identity(trust_cg)
    except OSError as error:
        errors.append(f"trust-cg CLI unavailable at {trust_cg}: {error} (build it or pass --trust-cg)")
    cc_path = Path(cc) if os.sep in cc else None
    if cc_path is None:
        found = shutil.which(cc, path=environ.get("PATH", ""))
        cc_path = Path(found) if found else None
    try:
        if cc_path is None:
            raise OSError(f"{cc!r} is not on PATH")
        tools["cc"] = executable_identity(cc_path)
    except OSError as error:
        errors.append(f"host C compiler unavailable: {error}")
    for tool in ("ay", "clean"):
        try:
            found = RESOLVER.resolve_tool(tool, target, dict(environ), system)
        except RESOLVER.ResolveError as error:
            errors.append(f"{tool}: {error}")
            continue
        if found is None:
            errors.append(
                f"{tool}: no pinned executable ("
                + ("absolute AY_SOLVER_PATH or the build toolchain's bin/ay" if tool == "ay"
                   else "explicit override or aterm managed package store")
                + "); "
                "the independent replay cannot run"
            )
            continue
        path, route = found
        if RESOLVER.route_pinning(route) != "pinned":
            errors.append(f"{tool}: only the unpinned route {route} resolves ({path}); refusing it")
            continue
        try:
            tools[tool] = {**executable_identity(path), "route": route}
        except OSError as error:
            errors.append(f"{tool}: {error}")
    return tools, errors


AY_IDENTITY_SCHEMA = "trust-cg.ay-identity.v2"


def ay_admission(trust_cg: str, ay: dict, env: Mapping[str, str]) -> Tuple[Optional[dict], List[str]]:
    """Ask the CLI under test whether it admits exactly the resolved AY's bytes.

    The digest the AY identity rule compares against is compiled into the CLI,
    so only the CLI can answer. `--print-ay-identity` applies the rule to the
    child environment (whose AY_SOLVER_PATH is the resolved AY) and executes no
    AY. Admission requires the CLI's admitted path and digest to be the resolved
    file and the digest this runner computed from its bytes.
    """
    try:
        result = subprocess.run(
            [trust_cg, "--print-ay-identity"], capture_output=True, text=True, timeout=60,
            check=False, env=dict(env), stdin=subprocess.DEVNULL,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return None, [f"trust-cg --print-ay-identity could not run: {error}"]
    record: dict = {"returncode": result.returncode, "stderr": result.stderr[-2000:]}
    try:
        answer = json.loads(result.stdout)
    except ValueError:
        record["stdout"] = result.stdout[-2000:]
        return record, [f"trust-cg --print-ay-identity exited {result.returncode} without an identity report "
                        "(a CLI that predates the AY identity rule cannot admit an AY)"]
    record["report"] = answer
    if not isinstance(answer, dict) or answer.get("schema") != AY_IDENTITY_SCHEMA:
        return record, [f"trust-cg --print-ay-identity answered an unknown schema: {result.stdout.strip()[:200]!r}"]
    if answer.get("admitted") is not True or result.returncode != 0:
        return record, [f"the CLI under test refuses AY {ay['resolved']}: "
                        f"{answer.get('detail') or answer.get('code') or 'no reason given'}"]
    problems = []
    admitted_path = answer.get("path")
    if not isinstance(admitted_path, str) or os.path.realpath(admitted_path) != ay["resolved"]:
        problems.append(f"the CLI admitted {admitted_path!r}, not the resolved AY {ay['resolved']}")
    if answer.get("sha256") != ay["sha256"]:
        problems.append(f"the CLI admitted sha256 {answer.get('sha256')!r}, but the resolved AY's bytes "
                        f"digest to {ay['sha256']}")
    exec_path = answer.get("exec_path")
    if not isinstance(exec_path, str) or not os.path.isabs(exec_path):
        problems.append(f"the CLI named no absolute private copy to start (exec_path {exec_path!r})")
    elif not problems:
        # Resolved once and judged by its canonical path (every canonical
        # ancestor renamable by nobody else), which is then the only path
        # checked again and started (`exec_canonical`): a name that runs
        # through a symlink in a directory others can write could be
        # re-pointed between a check and a start.
        try:
            canonical = PRIVATE_CACHE.require_private(exec_path)
        except OSError as error:
            problems.append(f"the private AY copy {exec_path} is not one only this user can change: "
                            f"{error.strerror or error}")
        else:
            record["exec_canonical"] = canonical
            stamp, copy_problems = private_copy_state(Path(canonical), ay["sha256"])
            problems.extend(copy_problems)
            if stamp is not None:
                record["exec_stamp"] = list(stamp)
    return record, problems


def private_copy_state(path: Path, sha256: str) -> Tuple[Optional[Tuple[int, ...]], List[str]]:
    """Check the private copy an admitted AY is started from.

    It must be a regular file (not a symlink) owned by this user with mode
    exactly 0500 and one link, in a directory owned by this user with mode
    exactly 0700, and its bytes must digest to the admitted sha256. Returns the
    file state its digest is bound to (device, inode, size, mtime, ctime).
    """
    problems: List[str] = []
    try:
        info = os.lstat(path)
        parent = os.lstat(path.parent)
    except OSError as error:
        return None, [f"private AY copy {path} cannot be inspected: {error}"]
    uid = os.geteuid()
    if not stat_is_regular(info.st_mode):
        problems.append(f"private AY copy {path} is not a regular file")
    if info.st_uid != uid or (info.st_mode & 0o7777) != 0o500 or info.st_nlink != 1:
        problems.append(f"private AY copy {path} is not a 0500 single-link file owned by uid {uid} "
                        f"(uid {info.st_uid}, mode {info.st_mode & 0o7777:04o}, links {info.st_nlink})")
    if not stat_is_directory(parent.st_mode) or parent.st_uid != uid or (parent.st_mode & 0o7777) != 0o700:
        problems.append(f"private AY copy directory {path.parent} is not a 0700 directory owned by uid {uid} "
                        f"(uid {parent.st_uid}, mode {parent.st_mode & 0o7777:04o})")
    if problems:
        return None, problems
    stamp = (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)
    try:
        current = sha256_file(path)
        after = os.lstat(path)
    except OSError as error:
        return None, [f"private AY copy {path} cannot be digested: {error}"]
    if (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns) != stamp:
        return None, [f"private AY copy {path} changed while it was digested"]
    if current != sha256:
        return None, [f"private AY copy {path} digests to {current}, not the admitted sha256 {sha256}"]
    return stamp, []


def stat_is_regular(mode: int) -> bool:
    return (mode & 0o170000) == 0o100000


def stat_is_directory(mode: int) -> bool:
    return (mode & 0o170000) == 0o040000


def identity_drift(before: dict, after: dict) -> List[str]:
    drift = []
    for name, row in before.items():
        later = after.get(name)
        if later is None or later.get("sha256") != row.get("sha256") or later.get("resolved") != row.get("resolved"):
            drift.append(f"{name} executable identity changed during the run")
    return drift


# ---------------------------------------------------------------------------
# The matrix
# ---------------------------------------------------------------------------

@dataclasses.dataclass
class Options:
    out: Path
    trust_cg: Path = DEFAULT_TRUST_CG
    cc: str = "cc"
    require_clean: bool = False
    max_rss_gib: Optional[float] = None
    compile_timeout: float = 120.0
    link_timeout: float = 120.0
    native_timeout: float = 120.0
    solver_timeout: float = 180.0
    checker_timeout: float = 180.0
    grace_seconds: float = 5.0


Executor = Callable[..., dict]
# (object bytes, image bytes, target) -> binding record; raises LinkedImageFailure.
Binder = Callable[[bytes, bytes, str], dict]


def case_row(case: Case) -> dict:
    return {
        "name": case.name, "type": case.type, "shape": case.shape, "opt_level": case.opt_level,
        "status": "not-run", "failure": None, "errors": [], "steps": {}, "calls": 0,
        "object_sha256": None, "trust_ir_hash": None, "queries": [], "linked_image": None,
    }


def fail(row: dict, failure_class: str, detail: str) -> None:
    assert failure_class in FAILURE_CLASSES, failure_class
    row["status"] = "fail"
    row["errors"].append({"class": failure_class, "detail": detail})
    if row["failure"] is None:
        row["failure"] = {"class": failure_class, "detail": detail}


def step_failure(result: dict, timeout_class: str) -> Optional[str]:
    if result.get("interrupted_signal") is not None:
        # Cancellation stops the whole run; the unrun remainder is reported.
        raise KeyboardInterrupt
    if result["timed_out"]:
        return timeout_class
    if result["resource_limited"]:
        return RESOURCE_LIMIT
    if result["launch_error"]:
        return LAUNCH_FAILED
    return None


def run_case(case: Case, row: dict, context: dict) -> None:
    out: Path = context["out"]
    options: Options = context["options"]
    executor: Executor = context["executor"]
    env = context["env"]
    target = context["target"]
    directory = out / "cases" / case.name
    directory.mkdir(parents=True)
    source = out / "inputs" / f"{case.stem}.trust_ir"
    oracle = out / "inputs" / f"{case.stem}.c"
    obj = directory / f"{case.name}.o"
    proofs = directory / "proofs"
    exe = directory / case.name

    compiled = executor(
        compile_command(Path(context["tools"]["trust_cg"]["path"]), target, case, source, proofs, obj),
        cwd=directory, env=env, timeout_seconds=options.compile_timeout, log_stem=directory / "compile",
    )
    row["steps"]["compile"] = public_execution(compiled)
    row["object_published"] = obj.exists()
    row["proofs_published"] = proofs.exists()
    early = step_failure(compiled, COMPILE_TIMEOUT)
    if early is not None:
        fail(row, early, f"compile: {early} (exit {compiled['returncode']})")
        return
    if compiled["returncode"] != 0:
        signature = refusal_signature(compiled["stdout_text"], compiled["stderr_text"], out)
        row["refusal"] = signature
        fail(row, EXPORT_REFUSED, f"trust-cg exited {compiled['returncode']} for {target}: {signature}")
        return
    queries = sorted(proofs.glob("**/*.smt2")) if proofs.is_dir() else []
    row["queries"] = [sha256_file(path) for path in queries]
    context["exported_queries"].extend((case.name, path) for path in queries)
    try:
        audit = audit_case(proofs, obj, target)
    except AuditFailure as failure:
        fail(row, failure.failure_class, failure.detail)
        return
    row["object_sha256"] = audit["object_sha256"]
    row["trust_ir_hash"] = audit["trust_ir_hash"]
    row["audit"] = audit

    linked = executor(
        link_command(Path(context["tools"]["cc"]["path"]), oracle, obj, exe),
        cwd=directory, env=env, timeout_seconds=options.link_timeout, log_stem=directory / "link",
    )
    row["steps"]["link"] = public_execution(linked)
    early = step_failure(linked, LINK_TIMEOUT)
    if early is not None:
        fail(row, early, f"link: {early} (exit {linked['returncode']})")
        return
    if linked["returncode"] != 0 or not exe.is_file():
        fail(row, LINK_FAILED, f"host C compiler exited {linked['returncode']}: "
             f"{refusal_signature(linked['stdout_text'], linked['stderr_text'], out)}")
        return
    if not bind_case_image(case, row, context, obj, exe, oracle, directory):
        return

    native = executor(
        [str(exe)], cwd=directory, env=env, timeout_seconds=options.native_timeout,
        log_stem=directory / "native",
    )
    row["steps"]["native"] = public_execution(native)
    early = step_failure(native, NATIVE_TIMEOUT)
    if early is not None:
        fail(row, early, f"native: {early} (exit {native['returncode']})")
        return
    if native["returncode"] != 0 or native["stdout_text"].strip() != NATIVE_MARKER:
        fail(row, NATIVE_MISMATCH, f"oracle driver exited {native['returncode']} with "
             f"{native['stdout_text'].strip()[:200]!r}; expected {NATIVE_MARKER!r}")
        return
    executed = sha256_file(exe)
    if executed != row["linked_image"]["image_sha256"]:
        fail(row, LINKED_IMAGE_MISMATCH, f"the executed image {executed} is not the bound image "
             f"{row['linked_image']['image_sha256']}")
        return
    row["calls"] = CALLS_PER_CASE
    row["status"] = "native-pass"


def bind_case_image(case: Case, row: dict, context: dict, obj: Path, exe: Path, oracle: Path,
                    directory: Path) -> bool:
    """Bind the linked image to the audited object and require its three negatives to be refused."""
    binder: Binder = context["binder"]
    target = context["target"]
    object_bytes = obj.read_bytes()
    if sha256_bytes(object_bytes) != row["object_sha256"]:
        fail(row, SIDECAR_MISMATCH, "the object changed after its sidecar audit; machine_code_hash no longer binds it")
        return False
    image_bytes = exe.read_bytes()
    try:
        record = binder(object_bytes, image_bytes, target)
    except LinkedImageFailure as failure:
        row["linked_image"] = {"status": "refused", "image_sha256": sha256_bytes(image_bytes),
                               "failure": {"class": failure.failure_class, "detail": failure.detail}}
        fail(row, failure.failure_class, failure.detail)
        return False
    record = dict(record, controls=[])
    row["linked_image"] = record
    candidates = [(label, patched, dict(info, source="in-place patch of the bound image"))
                  for label, patched, info in linked_image_patches(image_bytes, record)]
    candidates.append(("foreign-object", *foreign_image(case, context, oracle, directory)))
    for label, patched, info in candidates:
        control = {"control": label, "expected_class": LINKED_IMAGE_MISMATCH, **info,
                   "constructed": patched is not None, "refused": None, "passed": False}
        record["controls"].append(control)
        if patched is None:
            fail(row, CONTROL_NOT_CONSTRUCTED, f"linked-image {label}: {info.get('reason', 'no patch site')}")
            continue
        control["image_sha256"] = sha256_bytes(patched)
        if patched == image_bytes:
            control["constructed"] = False
            fail(row, CONTROL_NOT_CONSTRUCTED, f"linked-image {label}: the control equals the bound image")
            continue
        try:
            binder(object_bytes, patched, target)
        except LinkedImageFailure as failure:
            control.update(refused=True, observed_class=failure.failure_class, detail=failure.detail)
        else:
            control.update(refused=False, observed_class=None, detail="accepted")
        control["passed"] = control["observed_class"] == LINKED_IMAGE_MISMATCH
        if not control["passed"]:
            observed = f"{control['observed_class']}: {control['detail']}" if control["refused"] else "acceptance"
            fail(row, LINKED_IMAGE_CONTROL_FAILED,
                 f"linked-image {label}: expected {LINKED_IMAGE_MISMATCH}, observed {observed}")
    return row["failure"] is None


def foreign_image(case: Case, context: dict, oracle: Path, directory: Path) -> Tuple[Optional[bytes], dict]:
    """Link the recorded oracle against the run's foreign `calculate` object."""
    foreign = context.get("foreign_object")
    if foreign is None:
        return None, {"reason": "the foreign object was not built (see report errors)"}
    options: Options = context["options"]
    exe = directory / f"{case.name}-foreign"
    linked = context["executor"](
        link_command(Path(context["tools"]["cc"]["path"]), oracle, foreign, exe),
        cwd=directory, env=context["env"], timeout_seconds=options.link_timeout, log_stem=directory / "foreign-link",
    )
    info = {"source": f"oracle linked with {foreign.relative_to(context['out'])}",
            "foreign_object_sha256": sha256_file(foreign), "link": public_execution(linked)}
    early = step_failure(linked, LINK_TIMEOUT)
    if early is not None or linked["returncode"] != 0 or not exe.is_file():
        info["reason"] = f"foreign link {early or 'failed'} (exit {linked['returncode']})"
        return None, info
    return exe.read_bytes(), info


def build_foreign_object(context: dict, report: dict) -> None:
    """Compile the same-named foreign definition once; its absence fails every bound case's control."""
    out: Path = context["out"]
    options: Options = context["options"]
    source = out / "inputs" / "foreign-calculate.c"
    obj = out / "inputs" / "foreign-calculate.o"
    compiled = context["executor"](
        [context["tools"]["cc"]["path"], "-O2", "-std=c11", "-Wall", "-Wextra", "-Werror", "-c", str(source),
         "-o", str(obj)],
        cwd=out / "inputs", env=context["env"], timeout_seconds=options.link_timeout,
        log_stem=out / "inputs" / "foreign-calculate-compile",
    )
    entry = {"source": str(source.relative_to(out)), "compile": public_execution(compiled)}
    report["linked_image_foreign"] = entry
    early = step_failure(compiled, LINK_TIMEOUT)
    if early is not None or compiled["returncode"] != 0 or not obj.is_file():
        report["errors"].append(f"the foreign-object control could not be compiled ({early or 'exit'} "
                                f"{compiled['returncode']}); every bound case fails its foreign-object control")
        return
    entry["object"] = str(obj.relative_to(out))
    entry["object_sha256"] = sha256_file(obj)
    context["foreign_object"] = obj


def check_source_identities(rows: Sequence[dict]) -> None:
    """Every optimization level of one type/shape must compile the same TrustIR."""
    groups: Dict[str, set] = {}
    for row in rows:
        if row["trust_ir_hash"] is not None:
            groups.setdefault(f"{row['type']}-{row['shape']}", set()).add(row["trust_ir_hash"])
    for row in rows:
        identities = groups.get(f"{row['type']}-{row['shape']}", set())
        if row["trust_ir_hash"] is not None and len(identities) > 1:
            fail(row, SOURCE_IDENTITY_MISMATCH,
                 f"{len(identities)} TrustIR identities across the optimization levels of {row['type']}-{row['shape']}")


def run_replay(context: dict, report: dict) -> Dict[str, dict]:
    """Re-solve every distinct exported query and check the four certificates."""
    out: Path = context["out"]
    options: Options = context["options"]
    executor: Executor = context["executor"]
    env = context["env"]
    # The AY that runs is the file the CLI under test admitted, by its bytes.
    # Only ay_admission() sets this; without it no AY is executed.
    admitted: Optional[dict] = context.get("ay_admitted")
    clean = Path(context["tools"]["clean"]["path"])
    distinct: Dict[str, dict] = {}
    for case_name, path in context["exported_queries"]:
        raw = path.read_bytes()
        entry = distinct.setdefault(sha256_bytes(raw), {"bytes": raw, "cases": [], "paths": []})
        entry["cases"].append(case_name)
        entry["paths"].append(str(path.relative_to(out)))
    directory = out / "replay"
    directory.mkdir()
    results: Dict[str, dict] = {}
    for index, digest in enumerate(sorted(distinct)):
        entry = distinct[digest]
        name = f"query-{index:02d}"
        query = directory / f"{name}.smt2"
        query.write_bytes(entry["bytes"])
        proof = directory / f"{name}.alethe"
        row = {
            "name": name, "query_sha256": digest, "cases": entry["cases"], "exported_paths": entry["paths"],
            "status": "fail", "failure": None, "errors": [], "certificates": [],
        }
        report["replay"]["queries"].append(row)
        results[digest] = row
        if admitted is None:
            fail(row, AY_NOT_ADMITTED, "the CLI under test admitted no AY; no AY is executed")
            write_report(context["report_path"], report)
            continue
        # Started from the private copy of the admitted bytes, never from the
        # admitted path: AY re-executes itself by the path it was started from.
        # The admitted file itself must also still be the admitted bytes, as
        # the compiler's own launcher requires (TCG-AY-IDENTITY-CHANGED).
        try:
            current = sha256_file(Path(admitted["path"]))
        except OSError as error:
            current = f"unreadable ({error})"
        if current != admitted["sha256"]:
            fail(row, AY_NOT_ADMITTED,
                 f"AY {admitted['path']} now digests to {current}, not the admitted sha256 "
                 f"{admitted['sha256']}; not executed")
            write_report(context["report_path"], report)
            continue
        ay = Path(admitted["exec_path"])
        stamp, copy_problems = private_copy_state(ay, admitted["sha256"])
        if not copy_problems and stamp != admitted["exec_stamp"]:
            copy_problems = [f"private AY copy {ay} was replaced or modified since admission"]
        if copy_problems:
            fail(row, AY_NOT_ADMITTED, "; ".join(copy_problems) + "; not executed")
            write_report(context["report_path"], report)
            continue
        solved = executor(solver_command(ay, query, proof), cwd=directory, env=env,
                          timeout_seconds=options.solver_timeout, log_stem=directory / f"{name}-ay")
        row["solver"] = public_execution(solved)
        early = step_failure(solved, SOLVER_TIMEOUT)
        if early is not None:
            fail(row, early, f"AY: {early} (exit {solved['returncode']})")
            write_report(context["report_path"], report)
            continue
        lines = [line.strip() for line in solved["stdout_text"].splitlines()]
        if solved["returncode"] != 0 or "unsat" not in lines:
            fail(row, SOLVER_REFUSED, f"AY exited {solved['returncode']} without an unsat verdict")
            write_report(context["report_path"], report)
            continue
        if not proof.is_file() or proof.stat().st_size == 0:
            fail(row, PROOF_MISSING, "AY reported unsat without writing its Alethe proof")
            write_report(context["report_path"], report)
            continue
        certificate = {
            "type": "alethe_certificate", "version": "1.0",
            "problem": entry["bytes"].decode("utf-8"), "proof": proof.read_text(encoding="utf-8"),
        }
        row["proof_sha256"] = sha256_file(proof)
        variants: List[Tuple[str, Optional[dict], bool]] = [("original", certificate, True)]
        variants += [(label, value, False) for label, value in corruption_controls(certificate)]
        for label, value, expected in variants:
            record = {"variant": label, "expected_accept": expected, "accepted": None, "passed": False}
            row["certificates"].append(record)
            if value is None:
                fail(row, CONTROL_NOT_CONSTRUCTED, f"{label}: the recorded mutation leaves the certificate unchanged")
                continue
            packet = directory / f"{name}-{label}.json"
            data = packet_bytes(value)
            packet.write_bytes(data)
            record["certificate_sha256"] = sha256_bytes(data)
            checked = executor(checker_command(clean, packet), cwd=directory, env=env,
                               timeout_seconds=options.checker_timeout, log_stem=directory / f"{name}-{label}")
            record["execution"] = public_execution(checked)
            early = step_failure(checked, CHECKER_TIMEOUT)
            if early is not None:
                fail(row, early, f"Clean {label}: {early} (exit {checked['returncode']})")
                continue
            accepted = checked["returncode"] == 0 and "fully verified" in (checked["stdout_text"] + checked["stderr_text"])
            record["accepted"] = accepted
            if expected and not accepted:
                fail(row, CHECKER_REJECTED_ORIGINAL, f"Clean exited {checked['returncode']} on the original certificate")
            elif not expected and accepted:
                fail(row, CHECKER_ACCEPTED_CORRUPTION, f"Clean accepted the {label} corruption")
            elif not expected and checked["returncode"] != 1:
                fail(row, CHECKER_CONTROL_ERROR,
                     f"Clean exited {checked['returncode']} on {label}; a rejection must be its verdict (exit 1)")
            else:
                record["passed"] = True
        if row["failure"] is None:
            row["status"] = "pass"
        write_report(context["report_path"], report)
    return results


def summarize(report: dict) -> None:
    cases = report["cases"]
    classes: Dict[str, int] = {}
    refusals: Dict[str, List[str]] = {}
    for row in cases:
        if row["failure"] is not None:
            classes[row["failure"]["class"]] = classes.get(row["failure"]["class"], 0) + 1
        if row.get("refusal"):
            refusals.setdefault(row["refusal"], []).append(row["name"])
    queries = report["replay"]["queries"]
    originals = sum(
        1 for row in queries for cert in row["certificates"] if cert["variant"] == "original" and cert["accepted"]
    )
    rejected = sum(
        1 for row in queries for cert in row["certificates"] if cert["variant"] != "original" and cert["passed"]
    )
    report["summary"] = {
        "required_cases": REQUIRED_CASES, "recorded_cases": len(cases),
        "passed_cases": sum(row["status"] == "pass" for row in cases),
        "failed_cases": sum(row["status"] != "pass" for row in cases),
        "native_calls": sum(row["calls"] for row in cases), "required_calls": REQUIRED_CALLS,
        "linked_images_bound": sum((row.get("linked_image") or {}).get("status") == "bound" for row in cases),
        "linked_image_controls_refused": sum(
            control["passed"] for row in cases for control in (row.get("linked_image") or {}).get("controls", [])),
        "required_linked_image_controls": REQUIRED_CASES * len(LINKED_IMAGE_CONTROLS),
        "distinct_queries": len(queries), "expected_distinct_queries": EXPECTED_DISTINCT_QUERIES,
        "originals_accepted": originals, "corruptions_rejected": rejected,
        "required_corruptions_rejected": len(queries) * len(CORRUPTION_CONTROLS),
        "failure_classes": dict(sorted(classes.items())),
        "refusals": [
            {"signature": signature, "count": len(names), "cases": names}
            for signature, names in sorted(refusals.items(), key=lambda item: (-len(item[1]), item[0]))
        ],
    }


def fail_unrun(report: dict, failure_class: str, detail: str) -> None:
    """Fail every case that has not reached a verdict; none is dropped."""
    for row in report["cases"]:
        if row["status"] not in ("pass", "fail"):
            fail(row, failure_class, f"not completed: {detail}")


def run_matrix(options: Options, environ: Optional[Mapping[str, str]] = None, *,
               executor: Optional[Executor] = None, host: Optional[Tuple[str, str]] = None,
               provenance: Optional[Callable[[], dict]] = None, binder: Optional[Binder] = None) -> dict:
    """Run the matrix into options.out (created here) and return the report."""
    environ = dict(os.environ if environ is None else environ)
    out = options.out
    report_path = out / "report.json"
    cases = required_cases()
    key, target = host_target(*(host or (None, None)))
    report = {
        "schema": SCHEMA, "scope": SCOPE, "started_utc": utc_now(), "status": "incomplete",
        "host": {"system": key[0], "machine": key[1], "target": target},
        "reference": {
            "archived_qualification": ARCHIVED_QUALIFICATION,
        },
        "denominator": {
            "types": list(TYPES), "shapes": list(SHAPES), "opt_levels": list(OPT_LEVELS),
            "required_cases": REQUIRED_CASES, "calls_per_case": CALLS_PER_CASE,
            "required_calls": REQUIRED_CALLS, "expected_distinct_queries": EXPECTED_DISTINCT_QUERIES,
            "corruption_controls": list(CORRUPTION_CONTROLS), "native_marker": NATIVE_MARKER,
            "linked_image_controls": list(LINKED_IMAGE_CONTROLS),
            "required_linked_image_controls": REQUIRED_CASES * len(LINKED_IMAGE_CONTROLS),
        },
        "controls": {
            "require_clean": options.require_clean, "max_rss_gib": options.max_rss_gib,
            "timeouts_seconds": {
                "compile": options.compile_timeout, "link": options.link_timeout,
                "native": options.native_timeout, "solver": options.solver_timeout,
                "checker": options.checker_timeout,
            },
            "solver_memory_mb": SOLVER_MEMORY_MB,
        },
        "cases": [case_row(case) for case in cases],
        "ay_admission": None, "replay": {"queries": []}, "inputs": [], "errors": [],
    }
    write_report(report_path, report)
    denominator = denominator_errors(cases)
    if denominator:
        report["errors"].extend(denominator)
    executor = executor or BoundedExecutor(options.grace_seconds, options.max_rss_gib)
    context: dict = {"out": out, "options": options, "executor": executor, "target": target,
                     "exported_queries": [], "report_path": report_path, "binder": binder or bind_linked_image}
    try:
        if target is None:
            detail = f"no supported AArch64 export target for {key[0]}/{key[1]}; supported: " + ", ".join(
                f"{system}/{machine}" for system, machine in HOST_TARGETS)
            report["errors"].append(detail)
            fail_unrun(report, UNSUPPORTED_HOST, detail)
            return finish(report, report_path)
        if provenance is None:
            git = shutil.which("git", path=environ.get("PATH", ""))
            if git is None:
                raise RuntimeError("git is required to fingerprint the source tree")
            provenance = lambda: SHARED.source_provenance(git)  # noqa: E731
        report["provenance"] = provenance()
        write_report(report_path, report)
        if options.require_clean and report["provenance"].get("dirty") is not False:
            detail = "--require-clean: the source tree has tracked edits or untracked non-ignored files"
            report["errors"].append(detail)
            fail_unrun(report, SOURCE_NOT_CLEAN, detail)
            return finish(report, report_path)
        if options.max_rss_gib is not None and isinstance(executor, BoundedExecutor):
            support = SHARED.timeout_runner_module().rss_supervision_support()
            report["controls"]["rss_supervision"] = support or "unsupported"
            if support is None:
                detail = f"--max-rss-gib {options.max_rss_gib:g}: resident-set supervision is unsupported on this host"
                report["errors"].append(detail)
                fail_unrun(report, RESOURCE_SUPERVISION_UNSUPPORTED, detail)
                return finish(report, report_path)
        tools, errors = resolve_tools(options.trust_cg, options.cc, environ, key[0], target)
        report["tools"] = tools
        if errors:
            report["errors"].extend(errors)
            fail_unrun(report, TOOL_UNAVAILABLE, "; ".join(errors))
            return finish(report, report_path)
        env, removed = child_environment(environ, tools["ay"]["resolved"], tools["clean"]["resolved"])
        context["env"] = env
        context["tools"] = tools
        report["environment"] = {
            "removed": removed, "pinned": {"AY_SOLVER_PATH": tools["ay"]["resolved"],
                                           "TCG_EXTERNAL_CLEAN_CHECKER": tools["clean"]["resolved"]},
        }
        report["ay_admission"], admission_errors = ay_admission(tools["trust_cg"]["resolved"], tools["ay"], env)
        if admission_errors:
            report["errors"].extend(admission_errors)
            fail_unrun(report, AY_NOT_ADMITTED, "; ".join(admission_errors))
            return finish(report, report_path)
        context["ay_admitted"] = {
            "path": tools["ay"]["resolved"], "sha256": report["ay_admission"]["report"]["sha256"],
            # The canonical path admission judged, never the CLI's spelling.
            "exec_path": report["ay_admission"]["exec_canonical"],
            "exec_stamp": tuple(report["ay_admission"]["exec_stamp"]),
        }
        report["tool_versions"] = {
            name: version_probe(Path(tools[name]["resolved"]), env) for name in ("trust_cg", "cc")
        }
        inputs = out / "inputs"
        inputs.mkdir()
        for ty in TYPES:
            for shape in SHAPES:
                for suffix, text in ((".trust_ir", trust_ir_source(ty, shape)), (".c", oracle_source(ty, shape))):
                    path = inputs / f"{ty}-{shape}{suffix}"
                    path.write_text(text, encoding="utf-8")
                    report["inputs"].append({"path": str(path.relative_to(out)), "sha256": sha256_file(path)})
        foreign = inputs / "foreign-calculate.c"
        foreign.write_text(foreign_object_source(), encoding="utf-8")
        report["inputs"].append({"path": str(foreign.relative_to(out)), "sha256": sha256_file(foreign)})
        build_foreign_object(context, report)
        write_report(report_path, report)
        for case, row in zip(cases, report["cases"]):
            print(f"Running {case.name}", flush=True)
            run_case(case, row, context)
            write_report(report_path, report)
            status = "NATIVE-PASS" if row["failure"] is None else f"FAIL {row['failure']['class']}"
            print(f"{status}: {case.name}", flush=True)
        check_source_identities(report["cases"])
        results = run_replay(context, report)
        if len(results) != EXPECTED_DISTINCT_QUERIES:
            report["errors"].append(
                f"exported {len(results)} distinct queries; the recorded replay denominator is "
                f"{EXPECTED_DISTINCT_QUERIES}. A changed query inventory must be requalified, not accepted"
            )
        for row in report["cases"]:
            for digest in row["queries"]:
                replay = results.get(digest)
                if replay is None:
                    fail(row, INCOMPLETE, f"exported query {digest} has no independent replay")
                elif replay["failure"] is not None:
                    fail(row, replay["failure"]["class"], f"{replay['name']}: {replay['failure']['detail']}")
            if row["status"] == "native-pass" and row["failure"] is None:
                row["status"] = "pass"
        report["tools_after"], after_errors = resolve_tools(options.trust_cg, options.cc, environ, key[0], target)
        report["errors"].extend(after_errors)
        report["errors"].extend(identity_drift(tools, report["tools_after"]))
        report["final_source"] = provenance()
        if report["final_source"].get("source_fingerprint") != report["provenance"].get("source_fingerprint"):
            report["errors"].append("source changed while the matrix was running")
    except KeyboardInterrupt:
        report["errors"].append("interrupted; the required case inventory is incomplete")
        fail_unrun(report, INTERRUPTED, "run interrupted")
    except (OSError, RuntimeError, subprocess.SubprocessError, UnicodeError, ValueError) as error:
        report["errors"].append(f"runner error: {error}")
        fail_unrun(report, INCOMPLETE, f"runner error: {error}")
    return finish(report, report_path)


def finish(report: dict, report_path: Path) -> dict:
    for row in report["cases"]:
        if row["status"] not in ("pass", "fail"):
            fail(row, INCOMPLETE, "case did not complete every required step")
    summarize(report)
    summary = report["summary"]
    report["status"] = "pass" if (
        not report["errors"]
        and not denominator_errors([Case(r["type"], r["shape"], r["opt_level"]) for r in report["cases"]])
        and summary["passed_cases"] == REQUIRED_CASES
        and summary["native_calls"] == REQUIRED_CALLS
        and summary["linked_images_bound"] == REQUIRED_CASES
        and summary["linked_image_controls_refused"] == REQUIRED_CASES * len(LINKED_IMAGE_CONTROLS)
        and summary["distinct_queries"] == EXPECTED_DISTINCT_QUERIES
        and summary["originals_accepted"] == EXPECTED_DISTINCT_QUERIES
        and summary["corruptions_rejected"] == EXPECTED_DISTINCT_QUERIES * len(CORRUPTION_CONTROLS)
        and all(row["status"] == "pass" for row in report["replay"]["queries"])
    ) else "fail"
    report["clean_source"] = report.get("provenance", {}).get("dirty") is False
    report["finished_utc"] = utc_now()
    write_report(report_path, report)
    return report


def prepare_output(requested: Optional[Path]) -> Path:
    if requested is None:
        output = Path(tempfile.mkdtemp(prefix="trust-cg-aot-arithmetic-"))
    else:
        output = requested.absolute()
        if output.resolve().is_relative_to(ROOT.resolve()):
            raise OSError("output must be outside the source tree so logs cannot change source provenance")
        output.mkdir(mode=0o700)
    if output.resolve().is_relative_to(ROOT.resolve()):
        raise OSError("output must be outside the source tree so logs cannot change source provenance")
    return output


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0], allow_abbrev=False)
    parser.add_argument("--list", action="store_true", help="print the 48 required cases without executing")
    parser.add_argument("--trust-cg", type=Path, default=DEFAULT_TRUST_CG,
                        help="trust-cg CLI executable (default: target/release/trust-cg in this checkout)")
    parser.add_argument("--cc", default="cc", help="host C compiler for the oracle driver (default: cc on PATH)")
    parser.add_argument("--out", type=Path,
                        help="new output directory outside the source tree; existing paths are rejected")
    parser.add_argument("--require-clean", action="store_true",
                        help="refuse to run unless git status --porcelain is empty")
    parser.add_argument("--max-rss-gib", type=positive_gib, metavar="GIB",
                        help="process-group resident-set ceiling for every command (Linux /proc only; fails elsewhere)")
    for stage, default in (("compile", 120), ("link", 120), ("native", 120), ("solver", 180), ("checker", 180)):
        parser.add_argument(f"--{stage}-timeout-seconds", type=positive_seconds, default=float(default),
                            help=f"bound for each {stage} command (default: {default})")
    return parser


def main(argv: Optional[Sequence[str]] = None, *, environ: Optional[Mapping[str, str]] = None,
         executor: Optional[Executor] = None, host: Optional[Tuple[str, str]] = None,
         provenance: Optional[Callable[[], dict]] = None, binder: Optional[Binder] = None) -> int:
    args = build_parser().parse_args(argv)
    if args.list:
        for case in required_cases():
            print(case.name)
        return 0
    try:
        output = prepare_output(args.out)
    except OSError as error:
        print(f"arithmetic AOT matrix: output directory error: {error}", file=sys.stderr)
        return 1
    print(f"arithmetic AOT matrix logs: {output}", flush=True)
    options = Options(
        out=output, trust_cg=args.trust_cg.absolute(), cc=args.cc, require_clean=args.require_clean,
        max_rss_gib=args.max_rss_gib, compile_timeout=args.compile_timeout_seconds,
        link_timeout=args.link_timeout_seconds, native_timeout=args.native_timeout_seconds,
        solver_timeout=args.solver_timeout_seconds, checker_timeout=args.checker_timeout_seconds,
    )
    report = run_matrix(options, environ, executor=executor, host=host, provenance=provenance, binder=binder)
    summary = report["summary"]
    print(
        f"arithmetic AOT matrix: {report['status'].upper()} ({summary['passed_cases']}/{REQUIRED_CASES} cases, "
        f"{summary['native_calls']}/{REQUIRED_CALLS} calls, {summary['linked_images_bound']} linked images bound, "
        f"{summary['linked_image_controls_refused']} linked-image negatives refused, "
        f"{summary['originals_accepted']} originals accepted, "
        f"{summary['corruptions_rejected']} corruptions rejected) {output / 'report.json'}"
    )
    for failure_class, count in summary["failure_classes"].items():
        print(f"  {failure_class}: {count} case(s)", file=sys.stderr)
    for refusal in summary["refusals"]:
        print(f"  refusal on {refusal['count']} case(s):\n    " + refusal["signature"].replace("\n", "\n    "),
              file=sys.stderr)
    for error in report["errors"]:
        print(error, file=sys.stderr)
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
