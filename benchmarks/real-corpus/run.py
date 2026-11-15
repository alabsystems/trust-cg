#!/usr/bin/env python3
"""benchmarks/real-corpus/run.py — the versioned larger corpus, measured proofs-on (L14-P7).

Why this exists
---------------
The beat-llvm corpus is 18 programs of tens of lines. A compiler meant to
replace LLVM, and to compile the whole Trust toolchain, cannot be described by
them (ledger L14-P7). This harness measures a larger, versioned corpus
(manifest.json): real-program guests, real crates.io library crates from the
Trust toolchain's own dependency graph, the `core` library at the installed
Trust compiler's own revision, and synthetic scale ladders. Every manifested
row is reported, intent-to-treat: a refusal, a timeout, a crash, an unavailable
input and a baseline failure are all rows that stay in the denominator.

Lanes per row
-------------
  llvm        : the pinned Trust compiler with its own LLVM backend, the row's
                opt level, N measured compiles.
  bridge      : the same compiler with -Zcodegen-backend=<trust-cg backend> and
                NO backend knob: the production configuration (proof
                certificates, solver and certificate store on; the host's
                warm cache, as beat-llvm's warm lane). One unmeasured warmup
                compile, a retry when it fails (beat-llvm's BENCH-8 rule), then
                N measured compiles when it succeeds. This is the evidence lane.
  diagnostic  : (--diagnostic-lane) the bridge with -Ztrust-ir-cg-args=no-proof-certs.
                It measures what the backend emits with its proof gate off. It
                is never evidence and never counts toward completion.

Runnable rows (bins) whose bridge compile succeeds are run: one warmup per lane,
then N interleaved rounds; every bridge exit status must equal the LLVM lane's
(a disagreement is a MISMATCH, P0, exit 1). The exit-status oracle is
probabilistic: the guests fold a checksum into a status below 256.

Outcomes (the `bridge` lane's, which decides completion)
-------------------------------------------------------
  MATCH              compiled N+1 times, and every run's status equals LLVM's
  COMPILED           compiled N+1 times, each writing a readable object; the row
                     has no execution oracle (a library)
  MISMATCH           compiled, but a run's status differs from LLVM's (P0)
  INCOMPLETE         fail-closed twice with a named [TCG-...] refusal
  NONDET-FAILCLOSED  the attempts disagree (one compiled, one refused)
  TIMEOUT            a compile exceeded the row's timeout (killed)
  ERROR              the compile crashed (ICE, panic) or failed without a named
                     refusal, a library compile exited 0 without writing a
                     readable object, or the harness itself faulted on the row
  BASELINE-FAILED    the LLVM lane could not compile or run the input (or its
                     library compile wrote no readable object): the input is
                     invalid under this driver, the bridge is not attempted
  UNAVAILABLE        the input is not on this host (crate archive, Trust checkout)
  INVALID-INPUT      the input on this host does not match the manifest's digest

Completion rate = (MATCH + COMPILED) / every manifested row. A library row
whose LLVM object holds 0 code bytes is VACUOUS (`vacuous: true`): it gives the
backend no code to judge, so the aggregates also report the completions with
code (completed and not vacuous) over every manifested row, and a vacuous row
has no code-bytes ratio. Ratios (compile wall, instructions retired, CPU, peak
RSS, runtime, emitted code bytes) are computed only for completed rows and
aggregated fail-closed: an aggregate is null unless every completed row has the
value.

Measurement
-----------
Every compile and run is wrapped in `/usr/bin/time -l` (Darwin) or `-v`
(Linux). Wall time is the harness's own monotonic clock around the wrapped
command. Peak RSS is the largest single process in the tree (rusage of the
reaped children). User and system CPU include every waited-for descendant (the
linker, solver and checker processes). Darwin's "instructions retired" and
"cycles elapsed" are the compiler (or program) process ITSELF, not its
children: the bridge runs inside trustc, the AY solver and Clean checker run as
children and are excluded, as is the linker. Those two counters are
load-robust; wall time is reported with the load average.

Eligibility (all must hold, or `ineligible_reasons` names each failure)
-----------------------------------------------------------------------
clean tree (no tracked edits) at a full revision; the manifest is the
repository's committed benchmarks/real-corpus/manifest.json at HEAD; a backend
no older than its build inputs that loaded in every bridge compile; no
TCG_*/TRUST_CG_* variable; the 1-minute load at or below ncpu/2 at the start
and the end of the run and of every row (threshold not overridden); no runaway
process; the whole manifest (no --only/--kinds subset); N >= 3 compiles and
N >= 5 runs; every input available and matching its digest; every row
classified; no MISMATCH; a runnable independent proof checker and no DEGRADED
bridge compile. An eligible run is
evidence for this corpus only; it feeds no ratchet (the ledger's ratchet is the
18-program contract corpus).

Usage
-----
    python3 benchmarks/real-corpus/run.py --out-dir DIR [--diagnostic-lane]
    python3 benchmarks/real-corpus/run.py --list
    python3 benchmarks/real-corpus/run.py --check-manifest     # in-repo digests, no compile
    python3 benchmarks/real-corpus/run.py --only 'crate/*' --out-dir DIR

Path arguments (--repo, --manifest, --dylib, --out-dir, --work-dir,
--trust-checkout, --cargo-home, and a --driver given as a path) are made
absolute before anything runs: the compiler runs inside each lane's output
directory, where a relative backend path would not load.

Exit: 0 measured (whatever the completion rate), 1 MISMATCH in any lane,
2 tooling/environment error (unresolvable driver, missing or stale backend,
manifest invalid, loaded machine without --allow-loaded).
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import importlib.util
import io
import json
import math
import os
import platform
import re
import shutil
import signal
import statistics
import subprocess
import sys
import tarfile
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
MANIFEST_REL = "benchmarks/real-corpus/manifest.json"
MANIFEST = REPO / MANIFEST_REL
SCHEMA = "trust-cg-real-corpus-results-v1"
MANIFEST_SCHEMA = "trust-cg-real-corpus-manifest-v1"


def _load(name, relative):
    spec = importlib.util.spec_from_file_location(name, REPO / relative)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


TRUST_TOOLCHAIN = _load("trust_cg_trust_toolchain", "scripts/trust_toolchain.py")
BRIDGE_BACKEND = _load("trust_cg_bridge_backend", "scripts/bridge_backend.py")
# beat-llvm's harness: provenance helpers (tool versions, OS, runaway detection,
# proof-checker record, the DEGRADED banner) are shared, not re-implemented.
sys.path.insert(0, str(REPO / "benchmarks" / "beat-llvm"))
BEAT = _load("trust_cg_beat_llvm_run", "benchmarks/beat-llvm/run.py")
SCALE_GATE = _load("trust_cg_scale_gate", "benchmarks/beat-llvm/scale_gate.py")
SCALING_GEN = _load("trust_cg_compile_scaling_gen", "benchmarks/compile-scaling/gen.py")
import emitted_size  # noqa: E402  (benchmarks/beat-llvm, on sys.path above)
import hostinfo  # noqa: E402

KINDS = ("real-program", "real-crate", "trust-sysroot", "scale-ladder")
OUTCOMES = ("MATCH", "COMPILED", "MISMATCH", "INCOMPLETE", "NONDET-FAILCLOSED", "TIMEOUT",
            "ERROR", "BASELINE-FAILED", "UNAVAILABLE", "INVALID-INPUT")
COMPLETED = ("MATCH", "COMPILED")
DIAGNOSTIC_KNOB = "no-proof-certs"
TIME_BIN = "/usr/bin/time"
TCG_CODE = re.compile(r"\[TCG-[A-Z0-9]+(?:-[A-Z0-9]+)*\]")
# A compiler crash, even one that also printed a named refusal, is an ERROR row.
ICE_MARKERS = ("internal compiler error", "panicked at")
# rustc's own words when -Zcodegen-backend cannot be loaded (rustc_interface
# util.rs): every such compile is an ERROR row and the run is not evidence.
BACKEND_LOAD_MARKERS = ("couldn't load codegen backend", "could not canonicalize codegen backend",
                        "symbol lookup in the codegen backend failed")


# ---------------------------------------------------------------- manifest --

class ManifestError(ValueError):
    pass


def load_manifest(path=MANIFEST):
    data = json.loads(Path(path).read_text())
    problems = validate_manifest(data)
    if problems:
        raise ManifestError("; ".join(problems))
    return data


def manifest_digest(path=MANIFEST):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


ROW_FIELDS = {"id", "kind", "crate_type", "source"}


def validate_manifest(data):
    """Every structural problem with a manifest (empty when it is well formed)."""
    problems = []
    if data.get("schema") != MANIFEST_SCHEMA:
        problems.append(f"schema is {data.get('schema')!r}, expected {MANIFEST_SCHEMA!r}")
    if not re.fullmatch(r"\d+\.\d+\.\d+", str(data.get("version", ""))):
        problems.append("version must be MAJOR.MINOR.PATCH")
    defaults = data.get("defaults") or {}
    for key in ("opt_level", "panic", "timeout_s", "n_compile", "n_run"):
        if key not in defaults:
            problems.append(f"defaults.{key} missing")
    seen = set()
    for index, row in enumerate(data.get("rows") or []):
        where = f"rows[{index}]"
        missing = ROW_FIELDS - set(row)
        if missing:
            problems.append(f"{where} lacks {sorted(missing)}")
            continue
        if row["id"] in seen:
            problems.append(f"{where} duplicates id {row['id']!r}")
        seen.add(row["id"])
        if row["kind"] not in KINDS:
            problems.append(f"{where} kind {row['kind']!r} not in {KINDS}")
        if row["crate_type"] not in ("bin", "lib"):
            problems.append(f"{where} crate_type must be bin or lib")
        if row.get("run") and row["crate_type"] != "bin":
            problems.append(f"{where} only a bin row can run")
        source = row["source"]
        kind = source.get("type")
        need = {
            "corpus-guest": ("file", "guest", "sha256"),
            "generator": ("generator", "sha256"),
            "crates-io": ("name", "version", "sha256"),
            "trust-git": ("revision", "path", "tree", "root"),
        }.get(kind)
        if need is None:
            problems.append(f"{where} source type {kind!r} unknown")
            continue
        for key in need:
            if not source.get(key):
                problems.append(f"{where} source lacks {key}")
        if kind == "generator" and source.get("generator") not in ("scale_gate", "compile-scaling"):
            problems.append(f"{where} generator {source.get('generator')!r} unknown")
    if not data.get("rows"):
        problems.append("no rows")
    return problems


def row_setting(manifest, row, key):
    return row.get(key, (manifest.get("defaults") or {}).get(key))


# ------------------------------------------------------------ in-repo sources --

GUEST_RE = re.compile(r'name:\s*"(?P<name>[^"]+)",.*?src:\s*r#"(?P<src>.*?)"#', re.S)


def corpus_guests(path):
    """{guest name: source text} from the bridge's shared real-program corpus
    (the Rust raw string's exact value)."""
    return {m.group("name"): m.group("src") for m in GUEST_RE.finditer(Path(path).read_text())}


def generated_source(source):
    """The text a generator row compiles."""
    if source["generator"] == "scale_gate":
        sizes = dict(SCALE_GATE.SIZES)
        if source.get("size") not in sizes:
            raise ManifestError(f"scale_gate size {source.get('size')!r} not in {sorted(sizes)}")
        return SCALE_GATE.generate(sizes[source["size"]])
    shape = SCALING_GEN.SHAPES.get(source.get("shape"))
    if shape is None or not isinstance(source.get("n"), int):
        raise ManifestError(f"compile-scaling shape {source.get('shape')!r}/{source.get('n')!r}")
    return shape(source["n"])


def sha256_text(text):
    return hashlib.sha256(text.encode()).hexdigest()


def in_repo_text(row, repo=REPO):
    """(text, None) for an in-repo row, or (None, problem)."""
    source = row["source"]
    if source["type"] == "corpus-guest":
        guests = corpus_guests(repo / source["file"])
        if source["guest"] not in guests:
            return None, f"guest {source['guest']!r} not in {source['file']}"
        return guests[source["guest"]], None
    if source["type"] == "generator":
        return generated_source(source), None
    return None, "not an in-repo source"


def check_in_repo_digests(manifest, repo=REPO):
    """Problems for every in-repo row whose source no longer has the manifest's
    digest: a changed guest or generator is a new corpus version."""
    problems = []
    for row in manifest["rows"]:
        if row["source"]["type"] not in ("corpus-guest", "generator"):
            continue
        text, problem = in_repo_text(row, repo)
        if problem:
            problems.append(f"{row['id']}: {problem}")
        elif sha256_text(text) != row["source"]["sha256"]:
            problems.append(f"{row['id']}: source digest {sha256_text(text)[:16]} != manifest "
                            f"{row['source']['sha256'][:16]} (bump the manifest version)")
    return problems


# -------------------------------------------------------------- crate inputs --

def registry_archive(cargo_home, name, version):
    """The crates.io archive in the local Cargo registry cache, or None."""
    cache = Path(cargo_home) / "registry" / "cache"
    if not cache.is_dir():
        return None
    for index in sorted(cache.iterdir()):
        candidate = index / f"{name}-{version}.crate"
        if candidate.is_file():
            return candidate
    return None


def safe_extract(archive_bytes, dest):
    """Extract a .crate (gzip tar) refusing absolute, parent and link members."""
    with tarfile.open(fileobj=io.BytesIO(archive_bytes), mode="r:gz") as tar:
        for member in tar.getmembers():
            name = member.name
            if name.startswith("/") or ".." in Path(name).parts:
                raise ManifestError(f"unsafe archive member {name!r}")
            if not (member.isfile() or member.isdir()):
                raise ManifestError(f"archive member {name!r} is not a file or directory")
        tar.extractall(dest, filter="data") if hasattr(tarfile, "data_filter") else tar.extractall(dest)


def feature_closure(features_table, requested, default_features, optional_deps):
    """The enabled feature set Cargo would compute for a crate built with no
    dependency: `requested` plus `default` (when on), closed over the table.
    A feature that enables an optional dependency (`dep:x`, or the implicit
    feature of an optional dependency) is refused: this corpus compiles each
    crate alone. `x?/f` and `x/f` entries name dependency features and are
    ignored when `x` is not enabled."""
    pending = list(requested) + (["default"] if default_features and "default" in features_table else [])
    enabled = set()
    while pending:
        feature = pending.pop()
        if feature in enabled:
            continue
        if feature.startswith("dep:") or (feature in optional_deps and feature not in features_table):
            raise ManifestError(f"feature {feature!r} enables an optional dependency")
        if "/" in feature:
            dep = feature.split("/", 1)[0].rstrip("?")
            if feature.split("/", 1)[0].endswith("?") or dep in optional_deps:
                continue
            raise ManifestError(f"feature {feature!r} names a dependency")
        if feature not in features_table:
            raise ManifestError(f"feature {feature!r} is not declared")
        enabled.add(feature)
        pending.extend(features_table[feature])
    return sorted(enabled - {"default"})


def crate_plan(crate_dir, source):
    """How to compile an extracted crate as one rustc invocation, or raise
    ManifestError naming why it cannot be (a build script, a required
    dependency, an undeclared feature, an edition the manifest disagrees with)."""
    import tomllib  # Python 3.11+; the harness's documented interpreter is Homebrew 3.14

    toml = tomllib.loads((crate_dir / "Cargo.toml").read_text())
    package = toml.get("package") or {}
    if package.get("build") or (package.get("build") is None and (crate_dir / "build.rs").is_file()):
        raise ManifestError("crate has a build script")
    deps = dict(toml.get("dependencies") or {})
    for table_key, table in (toml.get("target") or {}).items():
        if "windows" in table_key:
            continue  # target-gated dependencies that never apply on these hosts
        deps.update(table.get("dependencies") or {})
    optional = {name for name, spec in deps.items() if isinstance(spec, dict) and spec.get("optional")}
    required = sorted(set(deps) - optional)
    if required:
        raise ManifestError(f"crate requires dependencies {required}")
    edition = str(package.get("edition", "2015"))
    if source.get("edition") and source["edition"] != edition:
        raise ManifestError(f"manifest edition {source['edition']} != Cargo.toml {edition}")
    lib = toml.get("lib") or {}
    root = crate_dir / lib.get("path", "src/lib.rs")
    crate_name = lib.get("name", package.get("name", "")).replace("-", "_")
    features = feature_closure(toml.get("features") or {}, source.get("features") or [],
                               source.get("default_features", True), optional)
    return {"root": root, "edition": edition, "crate_name": crate_name, "features": features,
            "cfg": [arg for f in features for arg in ("--cfg", f'feature="{f}"')]}


def line_count(paths):
    total = 0
    for path in paths:
        try:
            total += len(Path(path).read_text(errors="replace").splitlines())
        except OSError:
            pass
    return total


# ------------------------------------------------------------------ sampling --

DARWIN_TIME = {
    "maxrss_bytes": re.compile(r"^\s*(\d+)\s+maximum resident set size\s*$", re.M),
    "instructions": re.compile(r"^\s*(\d+)\s+instructions retired\s*$", re.M),
    "cycles": re.compile(r"^\s*(\d+)\s+cycles elapsed\s*$", re.M),
    "footprint_bytes": re.compile(r"^\s*(\d+)\s+peak memory footprint\s*$", re.M),
}
DARWIN_TIMES = re.compile(r"^\s*([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys\s*$", re.M)
GNU_TIME = {
    "maxrss_kib": re.compile(r"Maximum resident set size \(kbytes\):\s*(\d+)"),
    "user_s": re.compile(r"User time \(seconds\):\s*([\d.]+)"),
    "sys_s": re.compile(r"System time \(seconds\):\s*([\d.]+)"),
}
# The first line of /usr/bin/time's own report; everything before it is the
# command's stderr.
REPORT_START = re.compile(r"^\s*[\d.]+ real\s+[\d.]+ user|^\tCommand being timed:|"
                          r"^Command (?:exited with non-zero status|terminated by signal)", re.M)


def parse_time_report(text, platform_name=None):
    """(command stderr, metrics) from a /usr/bin/time -l/-v stderr blob."""
    platform_name = platform_name or sys.platform
    match = REPORT_START.search(text)
    own = text[:match.start()] if match else text
    report = text[match.start():] if match else ""
    metrics = {}
    if platform_name == "darwin":
        for key, pattern in DARWIN_TIME.items():
            found = pattern.findall(report)
            metrics[key] = int(found[-1]) if found else None
        times = DARWIN_TIMES.findall(report)
        if times:
            metrics["user_s"], metrics["sys_s"] = float(times[-1][1]), float(times[-1][2])
    else:
        rss = GNU_TIME["maxrss_kib"].search(report)
        metrics["maxrss_bytes"] = int(rss.group(1)) * 1024 if rss else None
        for key in ("user_s", "sys_s"):
            found = GNU_TIME[key].search(report)
            metrics[key] = float(found.group(1)) if found else None
        metrics["instructions"] = metrics["cycles"] = metrics["footprint_bytes"] = None
    return own, metrics


def time_wrapper():
    if os.path.isfile(TIME_BIN) and os.access(TIME_BIN, os.X_OK):
        return [TIME_BIN, "-l" if sys.platform == "darwin" else "-v"]
    return []


def measure(cmd, env, timeout, cwd=None):
    """Run `cmd` once under /usr/bin/time and return a sample record. A
    timeout kills the whole process group (the compiler and its solver and
    checker children)."""
    wrapper = time_wrapper()
    started = time.monotonic()
    proc = subprocess.Popen([*wrapper, *cmd], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            env=env, cwd=cwd, start_new_session=True)
    timed_out = False
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = proc.communicate()
    wall = time.monotonic() - started
    text = err.decode(errors="replace")
    own, metrics = parse_time_report(text) if wrapper else (text, {})
    return {
        "returncode": proc.returncode,
        "timed_out": timed_out,
        "wall_s": round(wall, 6),
        "user_s": metrics.get("user_s"),
        "sys_s": metrics.get("sys_s"),
        "maxrss_bytes": metrics.get("maxrss_bytes"),
        "instructions": metrics.get("instructions"),
        "cycles": metrics.get("cycles"),
        "footprint_bytes": metrics.get("footprint_bytes"),
        "stderr": own,
        "stdout_bytes": len(out),
    }


def tcg_codes(stderr):
    return sorted(set(TCG_CODE.findall(stderr or "")))


def classify_failure(sample):
    """The outcome a failed compile sample stands for."""
    if sample["timed_out"]:
        return "TIMEOUT"
    stderr = sample.get("stderr") or ""
    if any(marker in stderr for marker in ICE_MARKERS):
        return "ERROR"
    if tcg_codes(stderr):
        return "INCOMPLETE"
    return "ERROR"


def first_error_line(stderr):
    lines = [l for l in (stderr or "").splitlines() if l.startswith("error")]
    return (lines[0] if lines else (stderr or "").strip()[-300:])[:300]


def object_problem(sample):
    """Why a library compile that exited 0 has no usable object, or None.

    `--emit=obj` asks for an object: a compile that exits 0 and writes none (or
    one whose code sections cannot be read) has not delivered the row, and a
    library row has no execution oracle that would catch it otherwise."""
    if sample.get("code_bytes") is not None:
        return None
    if sample.get("objects") == 0:
        return "the compile exited 0 but wrote no object"
    if sample.get("objects"):
        return "the compile wrote an object whose code sections could not be read"
    return "the compile exited 0 without a readable object"


def backend_load_failed(stderr):
    return any(marker in (stderr or "") for marker in BACKEND_LOAD_MARKERS)


# ---------------------------------------------------------------- statistics --

def median(values):
    values = [v for v in values if v is not None]
    return statistics.median(values) if values else None


def ratio(numerator, denominator):
    if numerator is None or denominator is None or denominator <= 0 or numerator <= 0:
        return None
    return numerator / denominator


def geomean(values):
    if not values or any(v is None or v <= 0 for v in values):
        return None
    return math.exp(sum(math.log(v) for v in values) / len(values))


def lane_summary(samples):
    """Medians of the measured samples of one lane."""
    def med(key):
        return median([s.get(key) for s in samples])
    cpu = [s["user_s"] + s["sys_s"] for s in samples
           if s.get("user_s") is not None and s.get("sys_s") is not None]
    return {"n": len(samples), "wall_s": med("wall_s"), "cpu_s": median(cpu),
            "maxrss_bytes": med("maxrss_bytes"), "instructions": med("instructions"),
            "cycles": med("cycles"), "footprint_bytes": med("footprint_bytes")}


def code_bytes(directory):
    """Code bytes of every object a lib compile wrote into `directory`:
    `__text` (Mach-O) or `.text*` (ELF) sections."""
    total, objects = 0, 0
    for obj in sorted(Path(directory).glob("*.o")):
        data = obj.read_bytes()
        try:
            if data[:4] == b"\xcf\xfa\xed\xfe":
                sections = _macho_object_sections(data)
            else:
                sections = emitted_size._elf_sections(data)
        except Exception:  # noqa: BLE001 — an unreadable object is a missing reading
            return None
        objects += 1
        total += sum(len(content) for _, name, content in sections
                     if name == "__text" or name.startswith(".text"))
    return total if objects else None


def _macho_object_sections(data):
    """(segment, section, bytes) of a relocatable Mach-O object (one unnamed
    segment whose sections carry their own segment names)."""
    import struct
    magic, _, _, _, ncmds, _, _, _ = struct.unpack_from("<IiiIIIII", data, 0)
    offset, out = 32, []
    for _ in range(ncmds):
        cmd, cmdsize = struct.unpack_from("<II", data, offset)
        if cmd == 0x19:
            nsects = struct.unpack_from("<I", data, offset + 64)[0]
            at = offset + 72
            for _ in range(nsects):
                sectname = data[at:at + 16].rstrip(b"\0").decode()
                segname = data[at + 16:at + 32].rstrip(b"\0").decode()
                size, fileoff = struct.unpack_from("<QI", data, at + 40)
                flags = struct.unpack_from("<I", data, at + 64)[0]
                if (flags & 0xFF) not in (0x1, 0xC, 0x12) and size:
                    out.append((segname, sectname, data[fileoff:fileoff + size]))
                at += 80
        offset += cmdsize
    return out


# ------------------------------------------------------------------- harness --

def manifest_binding(repo, manifest_path):
    """Whether `manifest_path` is `repo`'s committed MANIFEST_REL at HEAD, byte
    for byte: only that manifest's run can be evidence for the corpus."""
    committed = Path(repo) / MANIFEST_REL
    shown = subprocess.run(["git", "-C", str(repo), "show", f"HEAD:{MANIFEST_REL}"], capture_output=True)
    head_sha = hashlib.sha256(shown.stdout).hexdigest() if shown.returncode == 0 else None
    same_path = Path(manifest_path).resolve() == committed.resolve()
    return {"committed_sha256": head_sha,
            "is_committed": bool(same_path and head_sha and manifest_digest(manifest_path) == head_sha)}


class Harness:
    def __init__(self, args):
        self.args = args
        self.repo = Path(args.repo).resolve()
        self.manifest_path = Path(args.manifest).resolve()
        self.manifest = load_manifest(self.manifest_path)
        self.driver = None
        self.env = TRUST_TOOLCHAIN.without_untracked_controls(os.environ)
        self.degraded = []
        self.backend_load_failures = []

    # -- selection --
    def selected_rows(self):
        rows = self.manifest["rows"]
        if self.args.kinds:
            rows = [r for r in rows if r["kind"] in self.args.kinds]
        if self.args.only:
            rows = [r for r in rows if any(fnmatch.fnmatch(r["id"], p) for p in self.args.only)]
        return rows

    def full_corpus(self):
        return not self.args.kinds and not self.args.only

    # -- provenance --
    def git(self, *a):
        r = subprocess.run(["git", "-C", str(self.repo), *a], capture_output=True, text=True)
        if r.returncode != 0:
            raise SystemExit(f"real-corpus: git {' '.join(a)} failed: {r.stderr.strip()}")
        return r.stdout

    def provenance(self, dylib, stale):
        porcelain = [l for l in self.git("status", "--porcelain").splitlines() if l.strip()]
        diff = subprocess.run(["git", "-C", str(self.repo), "diff", "HEAD"],
                              capture_output=True, text=True).stdout
        ncpu = os.cpu_count() or 1
        threshold = self.args.load_threshold if self.args.load_threshold is not None else ncpu / 2.0
        load = os.getloadavg()
        host = hostinfo.host_provenance()
        affinity = hostinfo.unpinned_record(hostinfo.core_topology())
        return {
            "schema": SCHEMA,
            "harness": "benchmarks/real-corpus/run.py",
            "timestamp_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "git_sha": self.git("rev-parse", "HEAD").strip(),
            "git_dirty": any(not l.startswith("??") for l in porcelain),
            "git_diff_sha256": hashlib.sha256(diff.encode()).hexdigest(),
            "untracked_count": sum(1 for l in porcelain if l.startswith("??")),
            "manifest": {"path": str(self.manifest_path.relative_to(self.repo))
                         if self.manifest_path.is_relative_to(self.repo) else str(self.manifest_path),
                         "sha256": manifest_digest(self.manifest_path),
                         "corpus": self.manifest.get("corpus"),
                         "version": self.manifest.get("version"),
                         **manifest_binding(self.repo, self.manifest_path)},
            "dylib_path": str(dylib),
            "dylib_sha256": BEAT.sha256_file(dylib),
            "dylib_mtime": datetime.fromtimestamp(dylib.stat().st_mtime, timezone.utc)
                .isoformat(timespec="seconds"),
            "dylib_stale_source": str(stale) if stale else None,
            "dylib_stale_override": bool(stale and self.args.allow_stale_dylib),
            "driver": {k: self.driver.get(k) for k in (
                "selection", "compiler", "targo", "sysroot", "host", "commit", "release",
                "version", "lane", "lane_label", "compiler_flags")},
            "target": self.target,
            "target_selection": self.target_selection,
            "host_arch": platform.machine(),
            **host,
            "affinity": affinity,
            "cc_version": BEAT._tool_version(["cc", "--version"]),
            "linker_version": BEAT._tool_version(["ld", "-v"]),
            "os": BEAT._os_description(),
            "python": sys.version.split()[0],
            "ncpu": ncpu,
            "load_threshold": round(threshold, 2),
            "load_threshold_overridden": self.args.load_threshold is not None,
            "loadavg_before": [round(v, 2) for v in load],
            "loadavg_after": None,
            "runaway_processes": BEAT.detect_runaways() or [],
            "tcg_env": {k: v for k, v in os.environ.items()
                        if k.startswith("TCG_") or k.startswith("TRUST_CG_")},
            "proof_checker": BEAT.proof_checker_record(self.env, self.driver.get("sysroot")),
            "sampler": {"wrapper": " ".join(time_wrapper()) or None,
                        "wall": "harness monotonic clock around the wrapped command",
                        "maxrss": "largest single process of the tree (rusage of reaped children)",
                        "cpu": "user+sys of the command and every waited-for descendant",
                        "instructions_cycles": "the compiler/program process itself (Darwin "
                                               "proc rusage), not its children"},
            "n_compile": self.args.n_compile,
            "n_run": self.args.n_run,
            "diagnostic_lane": bool(self.args.diagnostic_lane),
            "full_corpus": self.full_corpus(),
            "selection": {"only": self.args.only, "kinds": self.args.kinds},
            "cache": {"mode": "warm (the host's own trust-cg caches)",
                      "XDG_CACHE_HOME": os.environ.get("XDG_CACHE_HOME")},
            "cargo_home": str(self.cargo_home),
            "trust_checkout": str(self.args.trust_checkout) if self.args.trust_checkout else None,
        }

    # -- inputs --
    def materialize(self, row, work):
        """(plan, None) or (None, (outcome, reason)) for one row's input."""
        source = row["source"]
        kind = source["type"]
        row_dir = work / "src"
        row_dir.mkdir(parents=True, exist_ok=True)
        if kind in ("corpus-guest", "generator"):
            try:
                text, problem = in_repo_text(row, self.repo)
            except ManifestError as error:
                return None, ("INVALID-INPUT", str(error))
            if problem:
                return None, ("INVALID-INPUT", problem)
            digest = sha256_text(text)
            if digest != source["sha256"]:
                return None, ("INVALID-INPUT", f"source sha256 {digest} != manifest {source['sha256']}")
            stem = re.sub(r"[^A-Za-z0-9_]", "_", row["id"].split("/")[-1])
            if not stem[0].isalpha():
                stem = "r_" + stem
            path = row_dir / f"{stem}.rs"
            path.write_text(text)
            return {"root": path, "edition": row.get("edition", "2021"), "crate_name": None,
                    "cfg": [], "features": [], "lines": len(text.splitlines()),
                    "source_sha256": digest, "env": {}}, None
        if kind == "crates-io":
            archive = registry_archive(self.cargo_home, source["name"], source["version"])
            if archive is None:
                return None, ("UNAVAILABLE", f"{source['name']}-{source['version']}.crate not in "
                                             f"{self.cargo_home}/registry/cache")
            data = archive.read_bytes()
            digest = hashlib.sha256(data).hexdigest()
            if digest != source["sha256"]:
                return None, ("INVALID-INPUT", f"archive sha256 {digest} != manifest {source['sha256']}")
            try:
                safe_extract(data, row_dir)
                crate_dir = row_dir / f"{source['name']}-{source['version']}"
                plan = crate_plan(crate_dir, source)
            except (ManifestError, OSError, tarfile.TarError) as error:
                return None, ("INVALID-INPUT", str(error))
            plan.update(lines=line_count(crate_dir.rglob("*.rs")), source_sha256=digest, env={})
            return plan, None
        # trust-git: the driver's own library source at its revision.
        checkout = self.args.trust_checkout
        if not checkout or not (Path(checkout) / ".git").exists():
            return None, ("UNAVAILABLE", "no Trust checkout (--trust-checkout)")
        if (self.driver.get("commit") or "") != source["revision"]:
            return None, ("UNAVAILABLE", f"driver commit {self.driver.get('commit')} is not the "
                                         f"source revision {source['revision']}")
        tree = subprocess.run(["git", "-C", str(checkout), "rev-parse",
                               f"{source['revision']}:{source['path']}"],
                              capture_output=True, text=True)
        if tree.returncode != 0:
            return None, ("UNAVAILABLE", f"revision {source['revision']} not in the checkout")
        if tree.stdout.strip() != source["tree"]:
            return None, ("INVALID-INPUT", f"tree {tree.stdout.strip()} != manifest {source['tree']}")
        # `tree` pins the whole `path` tree; only `archive_paths` (default: `path`)
        # are extracted (core's `#[path]` modules live in sibling trees).
        paths = source.get("archive_paths") or [source["path"]]
        if any(not (p == source["path"] or p.startswith(source["path"] + "/")) for p in paths):
            return None, ("INVALID-INPUT", f"archive_paths {paths} outside {source['path']}")
        archive = subprocess.run(["git", "-C", str(checkout), "archive", "--format=tar",
                                  source["revision"], *paths], capture_output=True)
        if archive.returncode != 0:
            return None, ("UNAVAILABLE", archive.stderr.decode(errors="replace")[:300])
        with tarfile.open(fileobj=io.BytesIO(archive.stdout), mode="r:") as tar:
            tar.extractall(row_dir, filter="data") if hasattr(tarfile, "data_filter") else tar.extractall(row_dir)
        root = row_dir / source["path"] / source["root"]
        return {"root": root, "edition": row.get("edition", "2024"),
                "crate_name": row.get("crate_name"), "cfg": [], "features": [],
                "lines": line_count((row_dir / source["path"]).rglob("*.rs")),
                "source_sha256": source["tree"], "env": dict(row.get("env") or {})}, None

    # -- compiles --
    def compile_cmd(self, row, plan, lane, out):
        opt = str(row_setting(self.manifest, row, "opt_level"))
        cmd = [self.driver["compiler"], *self.driver["compiler_flags"]]
        if lane != "llvm":
            cmd.append(f"-Zcodegen-backend={self.dylib}")
            if lane == "diagnostic":
                cmd.append(f"-Ztrust-ir-cg-args={DIAGNOSTIC_KNOB}")
        cmd += [f"--edition={plan['edition']}", "--target", self.target,
                f"-Cpanic={row_setting(self.manifest, row, 'panic')}", f"-Copt-level={opt}",
                *row.get("rustc_flags", [])]
        if row["crate_type"] == "bin":
            cmd += ["--crate-type", "bin", "-o", str(out / "prog"), str(plan["root"])]
        else:
            cmd += ["--crate-type", "lib", "--emit=obj", "-Ccodegen-units=1", "--cap-lints", "allow"]
            if plan.get("crate_name"):
                cmd += ["--crate-name", plan["crate_name"]]
            cmd += [*plan["cfg"], "--out-dir", str(out), str(plan["root"])]
        return cmd

    def compile(self, row, plan, lane, out, timeout):
        if out.exists():
            shutil.rmtree(out)
        out.mkdir(parents=True)
        env = dict(self.env)
        env.update(plan.get("env") or {})
        sample = measure(self.compile_cmd(row, plan, lane, out), env, timeout, cwd=out)
        if lane != "llvm" and BEAT.DEGRADED_MARKER in sample["stderr"]:
            self.degraded.append(f"{row['id']}:{lane}")
        if lane != "llvm" and backend_load_failed(sample["stderr"]):
            self.backend_load_failures.append(f"{row['id']}:{lane}")
        if sample["returncode"] == 0 and not sample["timed_out"]:
            if row["crate_type"] == "lib":
                sample["objects"] = len(list(out.glob("*.o")))
                sample["code_bytes"] = code_bytes(out)
            else:
                prog = out / "prog"
                sample["binary_bytes"] = prog.stat().st_size if prog.is_file() else None
        return sample

    @staticmethod
    def slim(sample):
        """A retained sample: metrics and, for a failure, its diagnosis."""
        kept = {k: v for k, v in sample.items() if k != "stderr"}
        if sample["returncode"] != 0 or sample["timed_out"]:
            kept["tcg_codes"] = tcg_codes(sample["stderr"])
            kept["first_error"] = first_error_line(sample["stderr"])
            kept["stderr_sha256"] = sha256_text(sample["stderr"])
            kept["stderr_tail"] = sample["stderr"][-2000:]
        return kept

    def bridge_lane(self, row, plan, lane, work, timeout, n):
        """The warmup/retry/N protocol for a bridge lane: (outcome, record)."""
        out = work / lane
        attempts = [self.compile(row, plan, lane, out, timeout)]
        failed = attempts[0]["returncode"] != 0 or attempts[0]["timed_out"]
        if failed and not attempts[0]["timed_out"]:
            attempts.append(self.compile(row, plan, lane, out, timeout))
        record = {"attempts": [self.slim(a) for a in attempts], "samples": []}
        ok = [a["returncode"] == 0 and not a["timed_out"] for a in attempts]
        if not ok[-1]:
            if any(ok):
                return "NONDET-FAILCLOSED", record
            outcome = classify_failure(attempts[-1])
            record["tcg_codes"] = tcg_codes(attempts[-1]["stderr"])
            record["refusal_wall_s"] = attempts[-1]["wall_s"]
            record["refusal_instructions"] = attempts[-1]["instructions"]
            return outcome, record
        if not ok[0]:
            # Refused once, compiled on retry: never upgraded to a completion.
            return "NONDET-FAILCLOSED", record
        for _ in range(n):
            sample = self.compile(row, plan, lane, out, timeout)
            record["samples"].append(self.slim(sample))
            if sample["returncode"] != 0 or sample["timed_out"]:
                record["tcg_codes"] = tcg_codes(sample["stderr"])
                return "NONDET-FAILCLOSED", record
        record["summary"] = lane_summary(record["samples"])
        if row["crate_type"] == "lib":
            record["code_bytes"] = record["samples"][-1].get("code_bytes")
            problems = [object_problem(s) for s in [attempts[0], *record["samples"]]]
            problem = next((p for p in problems if p), None)
            if problem:
                # Exit 0 is not a completion when the requested object is missing.
                record["error"] = problem
                return "ERROR", record
        return None, record

    def run_lanes(self, row, binaries, n):
        """Interleaved runs of each lane's binary: (mismatch?, {lane: record})."""
        timeout = row.get("run_timeout_s", 300)
        records = {lane: {"warmup": None, "samples": []} for lane in binaries}
        for lane, path in binaries.items():
            records[lane]["warmup"] = self.slim(measure([str(path)], self.env, timeout))
        for _ in range(n):
            for lane, path in binaries.items():
                records[lane]["samples"].append(self.slim(measure([str(path)], self.env, timeout)))
        baseline = [s["returncode"] for s in records["llvm"]["samples"] + [records["llvm"]["warmup"]]]
        if len(set(baseline)) != 1 or records["llvm"]["warmup"]["timed_out"]:
            return None, records
        expected = baseline[0]
        mismatched = {}
        for lane, rec in records.items():
            statuses = [s["returncode"] for s in rec["samples"] + [rec["warmup"]]]
            timed = any(s["timed_out"] for s in rec["samples"] + [rec["warmup"]])
            rec["exit_status"] = sorted(set(statuses))
            rec["summary"] = lane_summary(rec["samples"])
            mismatched[lane] = timed or any(s != expected for s in statuses)
        records["expected_exit"] = expected
        return mismatched, records

    def bench_row(self, row):
        timeout = row_setting(self.manifest, row, "timeout_s") * self.args.timeout_scale
        n_compile, n_run = self.args.n_compile, self.args.n_run
        result = {"id": row["id"], "kind": row["kind"], "crate_type": row["crate_type"],
                  "opt_level": str(row_setting(self.manifest, row, "opt_level")),
                  "source": row["source"], "timeout_s": timeout,
                  "loadavg_start": [round(v, 2) for v in os.getloadavg()]}
        work = Path(tempfile.mkdtemp(prefix="row-", dir=self.work))
        try:
            plan, problem = self.materialize(row, work)
            if problem:
                result["outcome"], result["reason"] = problem
                if self.args.diagnostic_lane:
                    result["diagnostic_outcome"] = problem[0]
                return result
            result.update(lines=plan["lines"], source_sha256=plan["source_sha256"],
                          edition=plan["edition"], features=plan.get("features", []))
            # LLVM lane: the baseline. A failure invalidates the input.
            llvm_samples = []
            for _ in range(n_compile):
                sample = self.compile(row, plan, "llvm", work / "llvm", timeout)
                llvm_samples.append(self.slim(sample))
                failed = sample["returncode"] != 0 or sample["timed_out"]
                problem = None if failed or row["crate_type"] != "lib" else object_problem(sample)
                if failed or problem:
                    result["outcome"] = "BASELINE-FAILED"
                    result["reason"] = (f"LLVM lane: {problem}" if problem
                                        else first_error_line(sample["stderr"]))
                    result["lanes"] = {"llvm": {"samples": llvm_samples}}
                    if self.args.diagnostic_lane:
                        result["diagnostic_outcome"] = "BASELINE-FAILED"
                    return result
            lanes = {"llvm": {"samples": llvm_samples, "summary": lane_summary(llvm_samples)}}
            if row["crate_type"] == "lib":
                lanes["llvm"]["code_bytes"] = llvm_samples[-1].get("code_bytes")
                # No code in LLVM's object: nothing for the proof gate to judge.
                result["vacuous"] = lanes["llvm"]["code_bytes"] == 0
            outcomes = {}
            for lane in ("bridge", "diagnostic") if self.args.diagnostic_lane else ("bridge",):
                outcome, record = self.bridge_lane(row, plan, lane, work, timeout, n_compile)
                lanes[lane] = record
                outcomes[lane] = outcome
            runnable = row.get("run") and row["crate_type"] == "bin"
            binaries = {"llvm": work / "llvm" / "prog"}
            for lane, outcome in outcomes.items():
                if outcome is None and runnable:
                    binaries[lane] = work / lane / "prog"
            if runnable and len(binaries) > 1:
                mismatched, runs = self.run_lanes(row, binaries, n_run)
                result["runs"] = runs
                if mismatched is None:
                    result["outcome"] = "BASELINE-FAILED"
                    result["reason"] = "the LLVM lane's program did not exit consistently"
                    if self.args.diagnostic_lane:
                        result["diagnostic_outcome"] = "BASELINE-FAILED"
                    result["lanes"] = lanes
                    return result
                for lane in binaries:
                    if lane != "llvm":
                        outcomes[lane] = "MISMATCH" if mismatched[lane] else "MATCH"
            for lane, outcome in outcomes.items():
                if outcome is None:
                    outcomes[lane] = "MATCH" if runnable else "COMPILED"
            result["outcome"] = outcomes["bridge"]
            if lanes["bridge"].get("error"):
                result["reason"] = lanes["bridge"]["error"]
            if "diagnostic" in outcomes:
                result["diagnostic_outcome"] = outcomes["diagnostic"]
            result["lanes"] = lanes
            result["ratios"] = {lane: self.row_ratios(result, lane) for lane in outcomes
                                if outcomes[lane] in COMPLETED}
            if result["outcome"] in ("INCOMPLETE", "TIMEOUT", "ERROR"):
                result["refusal_cost_vs_llvm"] = ratio(lanes["bridge"].get("refusal_wall_s"),
                                                       lanes["llvm"]["summary"]["wall_s"])
            return result
        finally:
            result["loadavg_end"] = [round(v, 2) for v in os.getloadavg()]
            if not self.args.keep_work:
                shutil.rmtree(work, ignore_errors=True)

    @staticmethod
    def row_ratios(result, lane):
        mine, base = result["lanes"][lane]["summary"], result["lanes"]["llvm"]["summary"]
        out = {f"compile_{k}": ratio(mine.get(k), base.get(k))
               for k in ("wall_s", "cpu_s", "instructions", "maxrss_bytes")}
        if result["crate_type"] == "lib" and not result.get("vacuous"):
            out["code_bytes"] = ratio(result["lanes"][lane].get("code_bytes"),
                                      result["lanes"]["llvm"].get("code_bytes"))
        runs = result.get("runs") or {}
        if lane in runs and "summary" in runs[lane]:
            run_mine, run_base = runs[lane]["summary"], runs["llvm"]["summary"]
            for key in ("wall_s", "cycles", "instructions", "maxrss_bytes"):
                out[f"runtime_{key}"] = ratio(run_mine.get(key), run_base.get(key))
        return out

    # -- aggregates --
    @staticmethod
    def aggregates(rows, outcome_key, lane):
        total = len(rows)
        counts = {o: sum(1 for r in rows if r.get(outcome_key) == o) for o in OUTCOMES}
        completed = [r for r in rows if r.get(outcome_key) in COMPLETED]
        by_kind = {}
        for kind in KINDS:
            mine = [r for r in rows if r["kind"] == kind]
            if mine:
                done = sum(1 for r in mine if r.get(outcome_key) in COMPLETED)
                by_kind[kind] = {"rows": len(mine), "completed": done,
                                 "completion_pct": round(100.0 * done / len(mine), 1)}
        geo = {}
        keys = sorted({k for r in completed for k in (r.get("ratios") or {}).get(lane, {})})
        for key in keys:
            applicable = [r for r in completed
                          if key in (r.get("ratios") or {}).get(lane, {})]
            values = [r["ratios"][lane][key] for r in applicable]
            missing = [r["id"] for r, v in zip(applicable, values) if v is None]
            geo[key] = {"geomean": None if missing else geomean(values),
                        "rows": len(applicable), "missing": missing,
                        "worst": max(values) if values and not missing else None}
        codes = {}
        for r in rows:
            if r.get(outcome_key) in ("INCOMPLETE", "TIMEOUT", "ERROR", "NONDET-FAILCLOSED"):
                for code in (r.get("lanes") or {}).get(lane, {}).get("tcg_codes") or []:
                    codes[code] = codes.get(code, 0) + 1
        vacuous = [r["id"] for r in completed if r.get("vacuous")]
        with_code = len(completed) - len(vacuous)
        return {"lane": lane, "rows": total, "counts": counts,
                "completed": len(completed),
                "completion_pct": round(100.0 * len(completed) / total, 1) if total else None,
                "vacuous_completed": vacuous,
                "completed_with_code": with_code,
                "completion_with_code_pct": round(100.0 * with_code / total, 1) if total else None,
                # Fail-closed bookkeeping: every row must carry a known outcome.
                "unclassified": [r["id"] for r in rows if r.get(outcome_key) not in OUTCOMES],
                "by_kind": by_kind, "ratios": geo,
                "refused_rows_by_code": dict(sorted(codes.items(), key=lambda kv: -kv[1]))}

    def ineligible_reasons(self, prov, rows, aggregates=None):
        reasons = []
        if prov["git_dirty"]:
            reasons.append("source tree has tracked edits")
        if not (prov.get("manifest") or {}).get("is_committed"):
            reasons.append(f"manifest is not the committed {MANIFEST_REL} at HEAD")
        if prov["dylib_stale_override"]:
            reasons.append("stale bridge backend measured (--allow-stale-dylib)")
        if prov["tcg_env"]:
            reasons.append(f"TCG_*/TRUST_CG_* environment {sorted(prov['tcg_env'])}")
        thr = prov["load_threshold"]
        start, end = prov["loadavg_before"][0], (prov["loadavg_after"] or [None])[0]
        if start > thr or end is None or end > thr:
            reasons.append(f"machine LOADED (1-min load {start}->{end} vs threshold {thr})")
        if prov["load_threshold_overridden"]:
            reasons.append("--load-threshold overridden")
        # A long run is only as quiet as its loudest row: a refusal under load is
        # not a completeness datum (beat-llvm's BENCH-8 rule), nor is a timing.
        loaded = [r["id"] for r in rows
                  if max((r.get("loadavg_start") or [0])[0], (r.get("loadavg_end") or [0])[0]) > thr]
        if loaded:
            reasons.append(f"{len(loaded)} of {len(rows)} rows started or ended LOADED "
                           f"(1-min load above {thr})")
        if prov["runaway_processes"]:
            reasons.append("runaway processes on the host")
        if not prov["full_corpus"]:
            reasons.append("corpus subset (--only/--kinds)")
        if prov["n_compile"] < 3 or prov["n_run"] < 5:
            reasons.append(f"below N (compile {prov['n_compile']} < 3 or run {prov['n_run']} < 5)")
        missing = [r["id"] for r in rows if r.get("outcome") in ("UNAVAILABLE", "INVALID-INPUT")]
        if missing:
            reasons.append(f"{len(missing)} input(s) unavailable or not matching the manifest")
        if any(r.get(k) == "MISMATCH" for r in rows for k in ("outcome", "diagnostic_outcome")):
            reasons.append("MISMATCH rows")
        candidates = (prov.get("proof_checker") or {}).get("candidates") or []
        if not any(c.get("runs") for c in candidates):
            reasons.append("no independent proof checker (Clean) candidate runs")
        if self.degraded:
            reasons.append(f"verification DEGRADED in {len(self.degraded)} bridge compile(s)")
        if self.backend_load_failures:
            reasons.append(f"the bridge backend failed to load in {len(self.backend_load_failures)} "
                           "compile(s)")
        unclassified = sorted({i for a in (aggregates or {}).values() for i in a.get("unclassified", [])})
        if unclassified:
            reasons.append(f"{len(unclassified)} row(s) without a known outcome")
        return reasons

    # -- output --
    def markdown(self, res):
        p, agg = res["provenance"], res["aggregates"]
        lines = [f"# real-corpus {p['manifest']['corpus']} v{p['manifest']['version']} — "
                 f"`{p['git_sha'][:12]}`{' (dirty)' if p['git_dirty'] else ''}", "",
                 f"- {p['timestamp_utc']}  target `{p['target']}`  host {p.get('host_model')}  "
                 f"driver `{p['driver']['commit']}`  backend sha256 `{p['dylib_sha256'][:16]}…`",
                 f"- load {p['loadavg_before']} -> {p['loadavg_after']} (threshold "
                 f"{p['load_threshold']})  N compile {p['n_compile']} / run {p['n_run']}",
                 f"- evidence-eligible: **{res['eligible']}**"
                 + ("" if res["eligible"] else f" ({'; '.join(res['ineligible_reasons'])})"), ""]
        for name, a in agg.items():
            lines += [f"## {name} lane: {a['completed']} of {a['rows']} rows completed "
                      f"({a['completion_pct']}%), {a['completed_with_code']} with code "
                      f"({a['completion_with_code_pct']}%)", ""]
            if a["vacuous_completed"]:
                lines += ["Vacuous completions (LLVM's object holds no code): "
                          + ", ".join(f"`{i}`" for i in a["vacuous_completed"]), ""]
            lines += ["| outcome | rows |", "| --- | ---: |"]
            lines += [f"| {o} | {c} |" for o, c in a["counts"].items() if c]
            lines += ["", "| kind | rows | completed | % |", "| --- | ---: | ---: | ---: |"]
            lines += [f"| {k} | {v['rows']} | {v['completed']} | {v['completion_pct']} |"
                      for k, v in a["by_kind"].items()]
            if a["refused_rows_by_code"]:
                lines += ["", "Refused rows by named code: " + ", ".join(
                    f"`{c}` {n}" for c, n in a["refused_rows_by_code"].items())]
            if a["ratios"]:
                lines += ["", "| ratio vs LLVM (completed rows) | geomean | worst | rows |",
                          "| --- | ---: | ---: | ---: |"]
                lines += [f"| {k} | {fmt(v['geomean'])} | {fmt(v['worst'])} | {v['rows']} |"
                          for k, v in a["ratios"].items()]
            lines.append("")
        lines += ["## Rows", "",
                  "| row | kind | lines | LLVM compile s | bridge | bridge s (refusal or median) | "
                  "codes | diagnostic | diag compile x | diag runtime x |",
                  "| --- | --- | ---: | ---: | --- | ---: | --- | --- | ---: | ---: |"]
        for r in res["rows"]:
            lanes = r.get("lanes") or {}
            llvm = (lanes.get("llvm") or {}).get("summary") or {}
            bridge = lanes.get("bridge") or {}
            bs = (bridge.get("summary") or {}).get("wall_s") or bridge.get("refusal_wall_s")
            dr = (r.get("ratios") or {}).get("diagnostic") or {}
            lines.append(f"| {r['id']} | {r['kind']} | {r.get('lines', '')} | {fmt(llvm.get('wall_s'))} | "
                         f"{r['outcome']} | {fmt(bs)} | {' '.join(bridge.get('tcg_codes') or [])} | "
                         f"{r.get('diagnostic_outcome', '')} | {fmt(dr.get('compile_wall_s'))} | "
                         f"{fmt(dr.get('runtime_cycles'))} |")
        return "\n".join(lines) + "\n"

    def main(self):
        rows = self.selected_rows()
        if self.args.list:
            for row in rows:
                print(f"{row['id']:48} {row['kind']:14} {row['crate_type']:4} "
                      f"O{row_setting(self.manifest, row, 'opt_level')}")
            return 0
        if self.args.check_manifest:
            problems = check_in_repo_digests(self.manifest, self.repo)
            for problem in problems:
                print(f"real-corpus: {problem}")
            print(f"real-corpus: manifest {self.manifest.get('corpus')} v{self.manifest.get('version')}: "
                  f"{len(self.manifest['rows'])} rows, "
                  f"{'OK' if not problems else f'{len(problems)} problem(s)'}")
            return 0 if not problems else 2
        try:
            self.driver = TRUST_TOOLCHAIN.resolve(self.args.driver)
        except TRUST_TOOLCHAIN.ToolchainError as error:
            print(f"real-corpus: cannot resolve the pinned Trust compiler: {error}", file=sys.stderr)
            return 2
        self.target, self.target_selection = (
            (self.args.target, "explicit --target") if self.args.target
            else (self.driver.get("host"), "driver host"))
        if not self.target:
            print("real-corpus: the driver reported no host triple; pass --target", file=sys.stderr)
            return 2
        self.dylib = Path(self.args.dylib) if self.args.dylib else (
            BRIDGE_BACKEND.newest(self.repo) or BRIDGE_BACKEND.candidates(self.repo)[0])
        if not self.dylib.is_file():
            print(f"real-corpus: bridge backend missing: {self.dylib}", file=sys.stderr)
            return 2
        stale = BRIDGE_BACKEND.stale_source(self.repo, self.dylib)
        if stale is not None and not self.args.allow_stale_dylib:
            print(f"real-corpus: bridge backend is STALE ({stale} is newer); rebuild it or pass "
                  "--allow-stale-dylib (not evidence)", file=sys.stderr)
            return 2
        self.cargo_home = Path(self.args.cargo_home or os.environ.get("CARGO_HOME")
                               or Path.home() / ".cargo").absolute()
        self.degraded, self.backend_load_failures = [], []
        prov = self.provenance(self.dylib, stale)
        if prov["loadavg_before"][0] > prov["load_threshold"] and not self.args.allow_loaded:
            print(f"real-corpus: machine LOADED (1-min load {prov['loadavg_before'][0]} > "
                  f"{prov['load_threshold']}); wait, or pass --allow-loaded (not evidence)",
                  file=sys.stderr)
            return 2
        out_dir = Path(self.args.out_dir) if self.args.out_dir else HERE / "results"
        out_dir.mkdir(parents=True, exist_ok=True)
        work_parent = Path(self.args.work_dir) if self.args.work_dir else None
        if work_parent:
            work_parent.mkdir(parents=True, exist_ok=True)
        self.work = Path(tempfile.mkdtemp(prefix="tcg-real-corpus-", dir=work_parent))
        results = []
        try:
            for index, row in enumerate(rows, 1):
                print(f"[{index}/{len(rows)}] {row['id']} ...", end=" ", flush=True)
                try:
                    result = self.bench_row(row)
                except Exception as error:  # noqa: BLE001 — a harness fault is a row, never a lost run
                    result = {"id": row["id"], "kind": row["kind"], "crate_type": row["crate_type"],
                              "source": row["source"], "outcome": "ERROR",
                              "reason": f"harness exception: {type(error).__name__}: {error}"[:300],
                              "loadavg_start": [0.0], "loadavg_end": [round(os.getloadavg()[0], 2)]}
                    if self.args.diagnostic_lane:
                        result["diagnostic_outcome"] = "ERROR"
                results.append(result)
                note = result.get("reason") or " ".join(
                    ((result.get("lanes") or {}).get("bridge") or {}).get("tcg_codes") or [])
                diag = f" diagnostic={result['diagnostic_outcome']}" if "diagnostic_outcome" in result else ""
                print(f"{result['outcome']}{diag} {note}"[:240], flush=True)
        finally:
            if not self.args.keep_work:
                shutil.rmtree(self.work, ignore_errors=True)
        prov["loadavg_after"] = [round(v, 2) for v in os.getloadavg()]
        prov["proof_checker_degraded"] = self.degraded
        prov["backend_load_failures"] = self.backend_load_failures
        aggregates = {"bridge": self.aggregates(results, "outcome", "bridge")}
        if self.args.diagnostic_lane:
            aggregates["diagnostic"] = self.aggregates(results, "diagnostic_outcome", "diagnostic")
        reasons = self.ineligible_reasons(prov, results, aggregates)
        res = {"schema": SCHEMA, "provenance": prov, "aggregates": aggregates,
               "eligible": not reasons, "ineligible_reasons": reasons, "rows": results}
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        base = f"{prov['git_sha'][:12]}{'-dirty' if prov['git_dirty'] else ''}-{stamp}"
        jpath, mpath = out_dir / f"{base}.json", out_dir / f"{base}.md"
        jpath.write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
        mpath.write_text(self.markdown(res))
        a = aggregates["bridge"]
        print(f"\nreal-corpus: proofs-on (production) lane completed {a['completed']} of "
              f"{a['rows']} rows ({a['completion_pct']}%), {a['completed_with_code']} with code; "
              f"eligible={not reasons}")
        if self.args.diagnostic_lane:
            d = aggregates["diagnostic"]
            print(f"real-corpus: diagnostic (no-proof-certs, never evidence) lane completed "
                  f"{d['completed']} of {d['rows']} rows ({d['completion_pct']}%), "
                  f"{d['completed_with_code']} with code")
        for reason in reasons:
            print(f"  not evidence: {reason}")
        print(f"real-corpus: wrote {jpath}\nreal-corpus: wrote {mpath}")
        mismatch = any(r.get(k) == "MISMATCH" for r in results
                       for k in ("outcome", "diagnostic_outcome"))
        return 1 if mismatch else 0


def fmt(value, digits=3):
    if value is None:
        return "-"
    if isinstance(value, float):
        return f"{value:.{digits}f}"
    return str(value)


def parse_args(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=str(REPO))
    ap.add_argument("--manifest", default=str(MANIFEST))
    ap.add_argument("--driver", default=None, help="explicit Trust package trustc (default: PATH)")
    ap.add_argument("--dylib", default=None, help="bridge backend (default: the newest built one)")
    ap.add_argument("--target", default=None, help="target triple (default: the driver's host)")
    ap.add_argument("--out-dir", default=None, help="results directory (default: ./results)")
    ap.add_argument("--work-dir", default=None,
                    help="parent of the per-run scratch directory (removed at the end)")
    ap.add_argument("--keep-work", action="store_true", help="keep the scratch directory")
    ap.add_argument("--only", nargs="*", default=None, metavar="GLOB", help="row id globs (subset: not evidence)")
    ap.add_argument("--kinds", nargs="*", default=None, choices=KINDS, help="row kinds (subset: not evidence)")
    ap.add_argument("--diagnostic-lane", action="store_true",
                    help="also measure the no-proof-certs diagnostic lane (never evidence)")
    ap.add_argument("--n-compile", type=int, default=None, help="measured compiles per lane (manifest default)")
    ap.add_argument("--n-run", type=int, default=None, help="measured runs per lane (manifest default)")
    ap.add_argument("--timeout-scale", type=float, default=1.0, help="multiply every row timeout")
    ap.add_argument("--trust-checkout", default=None,
                    help="a Trust git checkout holding the driver's revision (for trust-sysroot rows)")
    ap.add_argument("--cargo-home", default=None, help="Cargo home holding the registry cache")
    ap.add_argument("--allow-loaded", action="store_true", help="measure on a loaded machine (not evidence)")
    ap.add_argument("--load-threshold", type=float, default=None, help="override ncpu/2 (not evidence)")
    ap.add_argument("--allow-stale-dylib", action="store_true", help="measure a stale backend (not evidence)")
    ap.add_argument("--list", action="store_true", help="list the selected rows and exit")
    ap.add_argument("--check-manifest", action="store_true",
                    help="validate the manifest and its in-repo source digests, compile nothing")
    args = ap.parse_args(argv)
    # The compiler runs with each lane's output directory as its working
    # directory, so every path handed to it, or kept in provenance, is absolute.
    for key in ("repo", "manifest", "dylib", "out_dir", "work_dir", "trust_checkout", "cargo_home"):
        if getattr(args, key):
            setattr(args, key, os.path.abspath(getattr(args, key)))
    if args.driver and os.sep in args.driver:
        args.driver = os.path.abspath(args.driver)
    return args


def main(argv=None):
    args = parse_args(argv)
    try:
        harness = Harness(args)
    except (ManifestError, json.JSONDecodeError, OSError) as error:
        print(f"real-corpus: manifest {args.manifest} is invalid: {error}", file=sys.stderr)
        return 2
    defaults = harness.manifest["defaults"]
    args.n_compile = args.n_compile if args.n_compile is not None else defaults["n_compile"]
    args.n_run = args.n_run if args.n_run is not None else defaults["n_run"]
    return harness.main()


if __name__ == "__main__":
    raise SystemExit(main())
