#!/usr/bin/env python3
"""benchmarks/wasm-vs-llvm/run.py — the wasm32 trust-cg vs rustc+LLVM harness.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0

Every program of progs/manifest.json is compiled for wasm32-unknown-unknown at
-C opt-level=2 three ways: rustc+LLVM (lane llvm_o2, baseline B1), rustc with
the trust-cg bridge as its codegen backend (lane tcg_o2), and, when a wasm-opt
is given, B1's module through `wasm-opt -O2 -g` (lane llvm_o2_wasmopt,
baseline B2, context only). All three link with the same wasm-ld against the
same sysroot. wasmtool.mjs then:

  - decodes each module (file and code-section bytes, static instructions,
    declared locals, static memory operations);
  - drives every scalar export over the deterministic grid on a fresh
    instance of each lane and compares every call with B1, traps included.
    A disagreement, a missing export, or a trust-cg module that does not
    compile, instantiate or return within its budget where B1 did makes the
    program a MISMATCH: stop-the-line, never ratchetable
    (scripts/check_perf_ratchet.py rejects the results). A +0/-0 difference
    is a disagreement unless the manifest lists the export under
    `soft_signed_zero` with a reason;
  - runs the workload (the grid calls on which B1 does not trap) once on an
    instrumented copy of each lane: executed instructions, memory operations,
    calls and loop-header entries, and the stack high-water (the lowest
    stack address written to __stack_pointer or touched by a memory access);
  - times the workload looped inside wasm in three node engine modes
    (default tiering, --no-liftoff, --liftoff-only): N interleaved samples
    per lane after warm-up, min and median recorded.

The harness never builds trust-cg or the bridge: --bridge names a built
backend dylib, whose SHA-256 and mtime are stamped, and which is checked
against the backend sources (scripts/bridge_backend.py).

Tools come from arguments or the documented environment, never from fixed
paths: --rustc (default: trustc on PATH), --bridge, --sysroot (default
$WASM32_SYSROOT, built by scripts/build_wasm32_sysroot.sh), --wasm-ld
(default $WASM_LD), --node (default: node on PATH), --wasm-opt (default
$WASM_OPT; without one the B2 lane is not measured and its context
aggregates are null).

A program that is not measured is INCOMPLETE with an `incomplete_kind`:
`refused` (the bridge refused it with a typed [TCG-*] diagnostic, a
fail-closed refusal), `compile_failed` (the bridge failed otherwise),
`b1_failed` (rustc+LLVM failed, or its module did not run) or `harness`. Only
`refused` is compatible with an evidence row.

The SHA-256 of the measuring code (this file, wasmtool.mjs and
contract/wasm_contract.py) is stamped as `measurement_sha256` and is part of
the ledger's comparison key, so a change to what or how the harness counts
never ratchets against numbers taken the old way.

Writes <out-dir>/<sha12>[-dirty]-<stamp>.json (schema trust-cg-wasm-bench-v2)
and a markdown summary beside it. The results enter ratchet/ledger.jsonl only
through `python3 scripts/check_perf_ratchet.py --append <results.json>`.

Exit: 0 results written; 2 tooling error (missing tool, corpus drift, a LOADED
machine without --allow-loaded).
"""

import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
sys.path.insert(0, str(HERE / "contract"))
sys.path.insert(0, str(REPO / "benchmarks" / "beat-llvm"))
import hostinfo  # noqa: E402
import wasm_contract as contract  # noqa: E402


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# The native harness's host probes (runaway detection, OS banner, tool
# versions), shared rather than copied.
BEAT_LLVM = _load("trust_cg_beat_llvm_run", REPO / "benchmarks" / "beat-llvm" / "run.py")
BRIDGE_BACKEND = _load("trust_cg_bridge_backend_wasm", REPO / "scripts" / "bridge_backend.py")

WASMTOOL = HERE / "wasmtool.mjs"
TARGET = contract.TARGET
OPT_LEVEL = "2"
COMPILE_TIMEOUT = 600
MEASURE_TIMEOUT = 600
TIME_TIMEOUT = 900
MODE_FLAGS = contract.load_contract()["engine_modes"]
PROOF_CERTIFICATES = ("none: the wasm32 lane emits no per-instruction proof certificates and refuses the "
                      "default proof-certificate gate ([TCG-PROOF-465]); it is compiled with "
                      "-Ztrust-ir-cg-args=no-proof-certs, and these rows say nothing about proofs")
REFUSAL = re.compile(r"\[(TCG-[A-Z0-9-]+)\]")


def die(msg):
    print(f"wasm-vs-llvm: {msg}", file=sys.stderr)
    sys.exit(2)


def sha256_file(path):
    return BEAT_LLVM.sha256_file(Path(path))


def first_line(cmd):
    return BEAT_LLVM._tool_version(cmd)


def tree_sha256(root):
    """Digest of every file under ROOT (relative path and content), so a
    sysroot is identified by what it holds, not by where it lives."""
    h = hashlib.sha256()
    for path in sorted(p for p in Path(root).rglob("*") if p.is_file()):
        h.update(str(path.relative_to(root)).encode() + b"\0" + sha256_file(path).encode() + b"\n")
    return h.hexdigest()


def resolve_tool(value, env_name, fallback, what, required=True):
    candidate = value or (os.environ.get(env_name) if env_name else None) or (shutil.which(fallback) if fallback else None)
    if not candidate:
        if required:
            die(f"no {what}: pass it as an argument" + (f" or set {env_name}" if env_name else ""))
        return None
    path = Path(candidate)
    if not path.exists():
        die(f"{what} does not exist: {path}")
    return str(path.resolve())


def check_corpus(manifest):
    """progs/*.rs and the manifest must agree file for file and byte for byte."""
    try:
        programs = json.loads(manifest.read_text(encoding="utf-8"))["programs"]
    except (OSError, ValueError, KeyError) as error:
        die(f"cannot read {manifest}: {error}")
    sources = {p.stem: p for p in (HERE / "progs").glob("*.rs")}
    if set(sources) != set(programs):
        die(f"corpus drift: files without a manifest row {sorted(set(sources) - set(programs))}, "
            f"rows without a file {sorted(set(programs) - set(sources))}")
    changed = [name for name, row in programs.items() if sha256_file(sources[name]) != row.get("sha256")]
    if changed:
        die(f"corpus drift: sources differ from their manifest sha256: {sorted(changed)}")
    problems = contract.manifest_problems(programs)
    if problems:
        die(f"malformed manifest: {problems}")
    return {name: sources[name] for name in sorted(programs)}, programs


class Harness:
    def __init__(self, args):
        self.args = args
        self.rustc = resolve_tool(args.rustc, None, "trustc", "rustc (--rustc)")
        self.bridge = resolve_tool(args.bridge, None, None, "bridge dylib (--bridge)")
        self.sysroot = resolve_tool(args.sysroot, "WASM32_SYSROOT", None, "wasm32 sysroot (--sysroot)")
        self.wasm_ld = resolve_tool(args.wasm_ld, "WASM_LD", None, "wasm-ld (--wasm-ld)")
        self.node = resolve_tool(args.node, None, "node", "node (--node)")
        self.wasm_opt = resolve_tool(args.wasm_opt, "WASM_OPT", None, "wasm-opt (--wasm-opt)", required=False)
        self.modes = args.modes or list(contract.MODES)
        unknown = [m for m in self.modes if m not in MODE_FLAGS]
        if unknown:
            die(f"unknown engine modes {unknown}; known: {sorted(MODE_FLAGS)}")
        # Compiles inherit no TCG_*/TRUST_* control: the bridge reads knobs from
        # -Ztrust-ir-cg-args only. What the environment holds is stamped.
        self.tcg_env = {k: v for k, v in os.environ.items() if k.startswith("TCG_") or k.startswith("TRUST_CG_")}

    def git(self, *args):
        result = subprocess.run(["git", "-C", str(REPO), *args], capture_output=True, text=True, check=False)
        if result.returncode != 0:
            die(f"git {' '.join(args)} failed: {result.stderr.strip()}")
        return result.stdout

    def common_flags(self):
        return ["-Ztrust-verify=off", "--edition", "2021", "--sysroot", self.sysroot, "--target", TARGET,
                "--crate-type", "cdylib", "-C", "panic=abort", "-C", f"linker={self.wasm_ld}",
                "-C", f"opt-level={OPT_LEVEL}"]

    def bridge_flags(self):
        return [f"-Zcodegen-backend={self.bridge}",
                *(f"-Ztrust-ir-cg-args={knob}" for knob in contract.REQUIRED_BRIDGE_CG_ARGS)]

    def provenance(self):
        sha = self.git("rev-parse", "HEAD").strip()
        lines = [line for line in self.git("status", "--porcelain").splitlines() if line.strip()]
        diff = self.git("diff", "HEAD")
        load1 = os.getloadavg()[0]
        ncpu = os.cpu_count() or 1
        threshold = self.args.load_threshold if self.args.load_threshold is not None else ncpu / 2.0
        stale = BRIDGE_BACKEND.stale_source(REPO, Path(self.bridge))
        engine = subprocess.run([self.node, "-p", "process.version + ' / V8 ' + process.versions.v8"],
                                capture_output=True, text=True, check=False).stdout.strip()
        rustc_vv = subprocess.run([self.rustc, "-vV"], capture_output=True, text=True, check=False).stdout
        host = hostinfo.host_provenance()
        return {
            "schema": contract.RESULTS_SCHEMA,
            "harness": "benchmarks/wasm-vs-llvm/run.py",
            "measurement_sha256": contract.measurement_sha256(),
            "measurement_files": list(contract.MEASUREMENT_FILES),
            "contract_version": contract.load_contract()["version"],
            "timestamp_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "git_sha": sha,
            "git_dirty": any(not line.startswith("??") for line in lines),
            "git_diff_sha256": hashlib.sha256(diff.encode()).hexdigest(),
            "untracked_count": sum(1 for line in lines if line.startswith("??")),
            "dylib_path": self.bridge,
            "dylib_sha256": sha256_file(self.bridge),
            "dylib_mtime": datetime.fromtimestamp(Path(self.bridge).stat().st_mtime, timezone.utc).isoformat(timespec="seconds"),
            "dylib_stale_source": BEAT_LLVM.repo_relative(stale, REPO) if stale else None,
            "rustc_path": self.rustc,
            "rustc_version": rustc_vv.splitlines()[0] if rustc_vv else "",
            "rustc_commit": next((line.split(": ", 1)[1] for line in rustc_vv.splitlines()
                                  if line.startswith("commit-hash: ")), ""),
            "rustc_flags": self.common_flags(),
            "bridge_cg_args": list(contract.REQUIRED_BRIDGE_CG_ARGS),
            "proof_certificates": PROOF_CERTIFICATES,
            "target": TARGET,
            "opt_level": OPT_LEVEL,
            "sysroot_path": self.sysroot,
            "sysroot_sha256": tree_sha256(Path(self.sysroot) / "lib" / "rustlib" / TARGET),
            "wasm_ld_path": self.wasm_ld,
            "wasm_ld_version": first_line([self.wasm_ld, "--version"]),
            "node_path": self.node,
            "engine": f"node {engine}",
            "engine_modes": {mode: MODE_FLAGS[mode] for mode in self.modes},
            "wasm_opt_path": self.wasm_opt,
            "wasm_opt_version": first_line([self.wasm_opt, "--version"]) if self.wasm_opt else None,
            "wasm_opt_flags": ["-O2", "-g"] if self.wasm_opt else None,
            "host_arch": platform.machine(),
            **host,
            "ncpu": ncpu,
            "os": BEAT_LLVM._os_description(),
            "tcg_env": self.tcg_env,
            "loadavg_before": round(load1, 2),
            "loadavg_after": None,
            "load_threshold": round(threshold, 2),
            "load_threshold_overridden": self.args.load_threshold is not None,
            "quiet": load1 <= threshold,
            "load_status": "QUIET" if load1 <= threshold else "LOADED",
            "runaway_processes": BEAT_LLVM.detect_runaways(),
            "n_run": self.args.n_run,
            "modes": list(self.modes),
            "target_ms": self.args.target_ms,
            "jobs": self.args.jobs,
            "aggregation": ("deterministic metrics: one reading per lane; timing: min (and median) of "
                            f"n_run={self.args.n_run} interleaved samples per lane per engine mode after "
                            "warm-up and calibration; per-program ratios trust-cg/B1, geomean or "
                            "corpus-total ratio per contract.json"),
            "corpus_manifest_sha256": contract.manifest_sha256(),
            "grid_sha256": None,  # filled from the first measurement
        }

    def compile(self, src, out, bridge):
        cmd = [self.rustc, *self.common_flags(), *(self.bridge_flags() if bridge else []), str(src), "-o", str(out)]
        t0 = time.perf_counter()
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=COMPILE_TIMEOUT, check=False)
        except subprocess.TimeoutExpired:
            return None, f"compile timed out after {COMPILE_TIMEOUT}s"
        elapsed = time.perf_counter() - t0
        if result.returncode != 0 or not out.is_file():
            codes = sorted(set(REFUSAL.findall(result.stderr)))
            lines = [line.strip() for line in result.stderr.splitlines() if line.strip().startswith(("- ", "error"))]
            return None, (f"refused {codes}: " if codes else "failed: ") + " | ".join(lines[:4])[:600]
        return elapsed, None

    def node_tool(self, flags, *args, timeout):
        cmd = [self.node, *flags, str(WASMTOOL), *args]
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, check=False)
        except subprocess.TimeoutExpired:
            return f"wasmtool {args[0]} timed out after {timeout}s"
        if result.returncode != 0:
            return f"wasmtool {args[0]} failed (exit {result.returncode}): {result.stderr.strip()[-600:]}"
        return None

    def build_and_measure(self, name, src, work, soft_zero=()):
        """Compiles every lane and runs the differential and deterministic
        measurements. Returns the program row (timing is added later)."""
        row = {"verdict": "INCOMPLETE", "incomplete_kind": "harness", "reason": None, "lanes": {}, "workload": None}

        def incomplete(kind, reason):
            row.update(incomplete_kind=kind, reason=reason)
            return row

        paths = {contract.B1: work / "b1.wasm", contract.TCG: work / "tcg.wasm"}
        b1_s, error = self.compile(src, paths[contract.B1], bridge=False)
        if error:
            return incomplete("b1_failed", f"rustc+LLVM (B1) {error}")
        tcg_s, error = self.compile(src, paths[contract.TCG], bridge=True)
        if error:
            return incomplete("refused" if error.startswith("refused") else "compile_failed", f"trust-cg {error}")
        if self.wasm_opt:
            paths[contract.B2] = work / "b2.wasm"
            result = subprocess.run([self.wasm_opt, "-O2", "-g", str(paths[contract.B1]), "-o", str(paths[contract.B2])],
                                    capture_output=True, text=True, timeout=COMPILE_TIMEOUT, check=False)
            if result.returncode != 0:
                row.setdefault("notes", []).append(f"wasm-opt failed: {result.stderr.strip()[:300]}")
                del paths[contract.B2]
        out = work / "measure.json"
        lanes = [arg for lane, path in paths.items() for arg in ("--lane", f"{lane}={path}")]
        soft = [arg for export in sorted(soft_zero) for arg in ("--soft-zero", export)]
        error = self.node_tool([], "measure", "--work", str(work), *lanes, *soft, "--out", str(out),
                               timeout=MEASURE_TIMEOUT)
        if error:
            return incomplete("harness", f"harness: {error}")
        measured = json.loads(out.read_text())
        if measured.get("oracle_failure"):
            return incomplete("b1_failed", f"rustc+LLVM (B1) module did not run: {measured['oracle_failure']}")
        row["grid_sha256"] = measured["grid_sha256"]
        row["exports"] = len(measured["exports"])
        row["skipped_exports"] = measured["skipped_exports"]
        row["checks"] = measured["checks"]
        row["workload"] = measured["workload"]
        for lane, record in measured["lanes"].items():
            record["compile_s"] = {contract.B1: b1_s, contract.TCG: tcg_s}.get(lane)
            record["bytes_sha256"] = sha256_file(paths[lane])
            row["lanes"][lane] = record
        verdict, reason = classify(row)
        if verdict == "INCOMPLETE":
            return incomplete("harness", reason)
        row.pop("incomplete_kind")
        row.update(verdict=verdict, reason=reason)
        return row

    def time_program(self, row, work):
        lanes = [contract.B1, contract.TCG]
        if contract.B2 in row["lanes"] and contract.b2_valid(row):
            lanes.append(contract.B2)
        for mode in self.modes:
            out = work / f"time_{mode}.json"
            args = ["time", "--work", str(work), *(a for lane in lanes for a in ("--lane", lane)),
                    "--n", str(self.args.n_run), "--target-ms", str(self.args.target_ms), "--out", str(out)]
            error = self.node_tool(MODE_FLAGS[mode], *args, timeout=TIME_TIMEOUT)
            timed = None if error else json.loads(out.read_text())
            if timed is not None and timed.get("error"):
                error = timed["error"]
            if error:
                row.setdefault("timing_errors", {})[mode] = error
                continue
            for lane in lanes:
                samples = timed["samples_ms"][lane]
                row["lanes"][lane].setdefault("timing", {})[mode] = {
                    "reps": timed["reps"], "samples_ms": samples, "min_ms": min(samples),
                    "median_ms": statistics.median(samples),
                    "first_call_ms": timed["first_call_ms"][lane]}

    def run(self):
        sources, manifest_rows = check_corpus(contract.MANIFEST)
        if self.args.progs:
            unknown = sorted(set(self.args.progs) - set(sources))
            if unknown:
                die(f"unknown programs: {unknown}")
            sources = {name: src for name, src in sources.items() if name in self.args.progs}
        prov = self.provenance()
        if not prov["quiet"]:
            msg = f"1-min load {prov['loadavg_before']} > threshold {prov['load_threshold']} (ncpu/2): machine is LOADED."
            if not self.args.allow_loaded:
                die(msg + " Refusing; --allow-loaded runs anyway and stamps the results LOADED (never evidence).")
            print(f"wasm-vs-llvm: WARNING: {msg} Stamping LOADED; results are not evidence.", file=sys.stderr)
        if prov["dylib_stale_source"]:
            print(f"wasm-vs-llvm: WARNING: {self.bridge} is older than {prov['dylib_stale_source']}; "
                  "results are not evidence.", file=sys.stderr)
        work_root = Path(tempfile.mkdtemp(prefix="wasm-vs-llvm-", dir=self.args.work_dir))
        programs = {}
        try:
            def phase1(item):
                name, src = item
                work = work_root / name
                work.mkdir()
                return name, self.build_and_measure(name, src, work,
                                                    soft_zero=manifest_rows[name].get("soft_signed_zero") or {})

            with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, self.args.jobs)) as pool:
                for done, (name, row) in enumerate(pool.map(phase1, sources.items()), 1):
                    programs[name] = row
                    print(f"wasm-vs-llvm: [{done}/{len(sources)}] {name}: {row['verdict']}"
                          + (f" ({row['reason'][:160]})" if row["reason"] else ""), file=sys.stderr)
            # Timing is sequential: one node process at a time.
            for name, row in programs.items():
                if row["verdict"] == "MATCH" and (row.get("workload") or {}).get("status") == "ok":
                    self.time_program(row, work_root / name)
                if not self.args.keep_work:
                    shutil.rmtree(work_root / name, ignore_errors=True)
        finally:
            if not self.args.keep_work:
                shutil.rmtree(work_root, ignore_errors=True)
        grids = {row.get("grid_sha256") for row in programs.values() if row.get("grid_sha256")}
        prov["grid_sha256"] = grids.pop() if len(grids) == 1 else None
        load_after = os.getloadavg()[0]
        prov["loadavg_after"] = round(load_after, 2)
        prov["quiet"] = prov["quiet"] and load_after <= prov["load_threshold"]
        prov["load_status"] = "QUIET" if prov["quiet"] else "LOADED"
        missing = contract.missing_provenance({**prov, "provenance_complete": True})
        prov["missing_required_provenance"] = missing
        prov["provenance_complete"] = not missing
        results = {"schema": contract.RESULTS_SCHEMA, "row_family": contract.ROW_FAMILY,
                   "provenance": prov, "programs": programs}
        results["aggregates"] = contract.table_aggregates(results)
        results["headline_eligible"] = True
        reasons = contract.evidence_problems(results)
        results["headline_eligible"] = not reasons
        results["ineligible_reasons"] = reasons
        results["gates_proposed"] = contract.gate_verdicts(results)
        out_dir = Path(self.args.out_dir) if self.args.out_dir else HERE / "results"
        out_dir.mkdir(parents=True, exist_ok=True)
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        base = f"{prov['git_sha'][:12]}{'-dirty' if prov['git_dirty'] else ''}-{stamp}"
        jpath, mpath = out_dir / f"{base}.json", out_dir / f"{base}.md"
        jpath.write_text(json.dumps(results, indent=1) + "\n")
        mpath.write_text(markdown(results) + "\n")
        print(f"wasm-vs-llvm: wrote {jpath} and {mpath.name} (evidence-eligible: {results['headline_eligible']})",
              file=sys.stderr)
        for reason in reasons:
            print(f"wasm-vs-llvm:   not evidence: {reason}", file=sys.stderr)
        print(jpath)
        return 0


def classify(row):
    """(verdict, reason) of a measured program row: MISMATCH when the trust-cg
    lane did not reproduce B1 (a grid disagreement, a missing export, a module
    that did not compile, instantiate or return within its budget, or a
    differing workload accumulator), INCOMPLETE when the harness could not
    decide, MATCH otherwise."""
    b1, tcg = row["lanes"].get(contract.B1) or {}, row["lanes"].get(contract.TCG) or {}
    diff = tcg.get("differential") or {}
    failure = diff.get("run_failure")
    if failure:
        at = f" at {failure['call']} after {failure['completed_calls']} calls" if failure.get("call") else ""
        return "MISMATCH", f"trust-cg module {failure['stage']} failure where B1 ran{at}: {str(failure.get('detail'))[:300]}"
    if diff.get("disagreements") or diff.get("missing_exports"):
        return "MISMATCH", (f"{diff.get('disagreements')} grid disagreements, missing exports "
                            f"{diff.get('missing_exports')}: {diff.get('first_disagreements', [])[:3]}")
    if diff.get("harness_fault"):
        return "INCOMPLETE", f"harness: {diff['harness_fault']}"
    if diff.get("disagreements") is None:
        return "INCOMPLETE", "harness: no differential for the trust-cg lane"
    if (row.get("workload") or {}).get("status") == "ok":
        errors = [f"{lane}: {record['loop_error']}" for lane, record in row["lanes"].items()
                  if lane in (contract.B1, contract.TCG) and record.get("loop_error")]
        if errors:
            return "INCOMPLETE", f"harness: no workload loop ({'; '.join(errors)})"
        if tcg.get("loop_acc") != b1.get("loop_acc") or tcg.get("loop_trap") != b1.get("loop_trap"):
            return "MISMATCH", (f"workload accumulator differs: B1 {b1.get('loop_acc')} (trap {b1.get('loop_trap')}) "
                                f"vs trust-cg {tcg.get('loop_acc')} (trap {tcg.get('loop_trap')})")
    return "MATCH", None


def fmt(value, digits=3):
    return "—" if value is None else (f"{value:.{digits}f}" if isinstance(value, float) else str(value))


def markdown(results):
    p, a = results["provenance"], results["aggregates"]
    lines = [
        f"# wasm-vs-llvm results — {p['git_sha'][:12]}{'-dirty' if p['git_dirty'] else ''} "
        f"({p['timestamp_utc']}, {p['host_arch']}, {p['load_status']})",
        "",
        "Generated by benchmarks/wasm-vs-llvm/run.py. Ratios are trust-cg / B1 (rustc+LLVM -C opt-level=2, "
        "no wasm-opt); B2 (B1 + wasm-opt -O2) is context. Evidence for the stamped revision and host only.",
        "",
        f"- evidence-eligible: **{results['headline_eligible']}**"
        + "".join(f"\n  - {r}" for r in results["ineligible_reasons"]),
        f"- bridge `{p['dylib_sha256'][:16]}` ({p['dylib_path']}), {p['rustc_version']}, {p['engine']}, "
        f"{p['wasm_ld_version']}, wasm-opt {p['wasm_opt_version']}",
        f"- coverage {fmt(a['coverage_pct'], 1)}% ({a['match_count']}/{a['total_programs']} MATCH, "
        f"{a['mismatch_count']} MISMATCH, {a['incomplete_count']} INCOMPLETE"
        + (f", not refusals: {a['incomplete_unrefused']}" if a["incomplete_unrefused"] else "") + "); "
        f"{a['workload_program_count']} programs with a workload; "
        f"{a['soft_signed_zero_total']} listed signed-zero differences; B2 measured on "
        f"{a['b2_program_count']} programs ({len(a['b2_excluded'])} disagreeing with B1, {a['b2_absent_count']} absent)",
        "",
        "| metric | trust-cg / B1 | trust-cg / B2 | B2 / B1 |",
        "|---|---|---|---|",
    ]
    for metric, _, how in contract.METRICS:
        b2 = (fmt(a.get(contract.metric_key(metric, contract.B2))), fmt(a.get(f"{contract.B2}_{metric}_{how}_vs_{contract.B1}"))) \
            if metric in contract.B2_METRICS else ("", "")
        lines.append(f"| {metric} ({how}) | {fmt(a.get(contract.metric_key(metric)))} | {b2[0]} | {b2[1]} |")
    lines += ["", "| program | verdict | file B1 | file tcg | dyn insns ratio | stack B1/tcg | turbofan ratio | note |",
              "|---|---|---|---|---|---|---|---|"]
    for name, row in sorted(results["programs"].items()):
        def r(metric):
            x, y = contract.reading(row, contract.TCG, metric), contract.reading(row, contract.B1, metric)
            return fmt(x / y) if x is not None and y else "—"
        stack = "/".join(fmt(contract.reading(row, lane, "stack_hwm")) for lane in (contract.B1, contract.TCG))
        lines.append(f"| {name} | {row['verdict']} | {fmt(contract.reading(row, contract.B1, 'file_bytes'))} "
                     f"| {fmt(contract.reading(row, contract.TCG, 'file_bytes'))} | {r('dyn_insns')} | {stack} "
                     f"| {r('time_turbofan')} | {(row.get('reason') or '')[:120]} |")
    return "\n".join(lines)


def parse_args(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0], allow_abbrev=False)
    ap.add_argument("--rustc", help="the Trust rustc driver (default: trustc on PATH)")
    ap.add_argument("--bridge", required=True, help="the built rustc_codegen_trust_cg backend dylib to measure")
    ap.add_argument("--sysroot", help="wasm32 sysroot (default: $WASM32_SYSROOT)")
    ap.add_argument("--wasm-ld", help="wasm-ld (default: $WASM_LD)")
    ap.add_argument("--node", help="node (default: node on PATH)")
    ap.add_argument("--wasm-opt", help="binaryen wasm-opt for the B2 context lane (default: $WASM_OPT; optional)")
    ap.add_argument("--progs", nargs="+", help="measure only these programs (a subset is never evidence)")
    ap.add_argument("--n-run", type=int, default=contract.N_RUN_MIN, help="timing samples per lane and mode (default 5)")
    ap.add_argument("--target-ms", type=float, default=20.0, help="calibrated duration of one timing sample (default 20)")
    ap.add_argument("--modes", nargs="+", help=f"engine modes (default: all of {list(contract.MODES)})")
    ap.add_argument("--jobs", type=int, default=1,
                    help="parallel compile+measure jobs (timing is always sequential; default 1)")
    ap.add_argument("--load-threshold", type=float, help="override the quiet threshold (ncpu/2); never evidence")
    ap.add_argument("--allow-loaded", action="store_true", help="run on a LOADED machine (results are not evidence)")
    ap.add_argument("--out-dir", help="results directory (default: benchmarks/wasm-vs-llvm/results, gitignored)")
    ap.add_argument("--work-dir", help="where per-program build outputs live while measured (default: the system temp dir)")
    ap.add_argument("--keep-work", action="store_true", help="keep the built modules (debugging)")
    return ap.parse_args(argv)


if __name__ == "__main__":
    sys.exit(Harness(parse_args()).run())
