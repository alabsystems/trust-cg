#!/usr/bin/env python3
"""benchmarks/wasm-vs-llvm/contract/wasm_contract.py — the one aggregation and
eligibility definition of the wasm32-vs-LLVM results, shared by the harness
(run.py, which stamps the aggregates) and the ledger ratchet
(scripts/wasm_perf_ratchet.py, which recomputes them and refuses a stamp that
disagrees).

Lanes: `llvm_o2` is B1 (rustc+LLVM, -C opt-level=2, no wasm-opt), `tcg_o2` the
trust-cg bridge at the same opt level, `llvm_o2_wasmopt` B2 (B1 through
binaryen wasm-opt -O2), context only. contract.json beside this file states
the baselines, metrics, eligibility and the PROPOSED gates in prose; the
definitions below are the executable form and a test keeps the two in step.

Aggregates are exact and fail-closed: over every program in a metric's scope
or null, never over the subset that happened to be measured. A metric that is
positive by construction aggregates as the geomean of per-program ratios; a
count that can be zero for LLVM (memory operations, calls, stack bytes,
declared locals) aggregates as the ratio of corpus totals, since a ratio with
a zero denominator is undefined.

`measurement_sha256` identifies the code that decides what is counted and how
(run.py, wasmtool.mjs and this file); the ledger compares rows only under the
same digest.
"""

import hashlib
import json
import math
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CONTRACT = HERE / "contract.json"
MANIFEST = HERE.parent / "progs" / "manifest.json"
sys.path.insert(0, str(HERE.parent.parent / "beat-llvm" / "contract"))
from check_gates import complete_geomean, gate_verdict, same_value  # noqa: E402

RESULTS_SCHEMA = "trust-cg-wasm-bench-v2"
ROW_FAMILY = "wasm32"
TARGET = "wasm32-unknown-unknown"
B1, TCG, B2 = "llvm_o2", "tcg_o2", "llvm_o2_wasmopt"
LANES = (B1, TCG, B2)
VERDICTS = ("MATCH", "MISMATCH", "INCOMPLETE")
# Why an INCOMPLETE program was not measured. Only `refused` (the bridge
# refused the program with a typed [TCG-*] diagnostic: fail-closed, not a
# defect of the output) is compatible with an evidence row.
INCOMPLETE_KINDS = ("refused", "compile_failed", "b1_failed", "harness")
# The measuring code, relative to benchmarks/wasm-vs-llvm.
MEASUREMENT_FILES = ("run.py", "wasmtool.mjs", "contract/wasm_contract.py")
MODES = ("default", "turbofan", "liftoff")
REQUIRED_BRIDGE_CG_ARGS = ["no-proof-certs"]
N_RUN_MIN = 5

# (metric, source, aggregation). source: static | dynamic | stack | timing.
METRICS = (
    ("file_bytes", "static", "geomean"),
    ("code_bytes", "static", "geomean"),
    ("static_insns", "static", "geomean"),
    ("declared_locals", "static", "total"),
    ("static_memops", "static", "total"),
    ("dyn_insns", "dynamic", "geomean"),
    ("dyn_memops", "dynamic", "total"),
    ("dyn_calls", "dynamic", "total"),
    ("stack_hwm", "stack", "total"),
    ("time_default", "timing", "geomean"),
    ("time_turbofan", "timing", "geomean"),
    ("time_liftoff", "timing", "geomean"),
)
METRIC = {name: (source, agg) for name, source, agg in METRICS}
DETERMINISTIC = tuple(name for name, source, _ in METRICS if source != "timing")
TIMING = tuple(name for name, source, _ in METRICS if source == "timing")
# Context metrics against B2, and B2 against B1.
B2_METRICS = ("file_bytes", "code_bytes", "dyn_insns", "time_turbofan")

MANDATORY_PROVENANCE = (
    "schema", "harness", "measurement_sha256", "contract_version", "timestamp_utc", "git_sha", "git_dirty",
    "git_diff_sha256", "untracked_count", "dylib_path", "dylib_sha256", "dylib_mtime",
    "rustc_path", "rustc_version", "rustc_flags", "bridge_cg_args", "target", "opt_level",
    "sysroot_path", "sysroot_sha256", "wasm_ld_path", "wasm_ld_version", "node_path", "engine",
    "wasm_opt_path", "wasm_opt_version", "host_arch", "host_model", "ncpu", "os", "tcg_env",
    "loadavg_before", "loadavg_after", "load_threshold", "quiet", "load_status", "n_run",
    "modes", "target_ms", "corpus_manifest_sha256", "grid_sha256",
    "proof_certificates", "provenance_complete",
)
# Mandatory, but legitimately empty or null: B2 is optional and a clean
# default environment is an empty object.
MAY_BE_EMPTY = {"wasm_opt_path", "wasm_opt_version", "tcg_env", "untracked_count", "git_dirty",
                "quiet", "provenance_complete", "loadavg_after"}


def metric_key(metric, base=B1):
    return f"wasm_{metric}_{METRIC[metric][1]}_vs_{base}"


def load_contract(path=None):
    return json.loads(Path(path or CONTRACT).read_text(encoding="utf-8"))


def corpus_programs(manifest=None):
    """The corpus's program names, sorted, or None if the manifest is unreadable."""
    try:
        programs = json.loads(Path(manifest or MANIFEST).read_text(encoding="utf-8"))["programs"]
    except (OSError, ValueError, KeyError, TypeError):
        return None
    return sorted(programs) if isinstance(programs, dict) else None


def measurement_sha256(root=None):
    """SHA-256 over MEASUREMENT_FILES (path and content digest of each)."""
    root = Path(root or HERE.parent)
    h = hashlib.sha256()
    for name in MEASUREMENT_FILES:
        h.update(name.encode() + b"\0" + hashlib.sha256((root / name).read_bytes()).hexdigest().encode() + b"\n")
    return h.hexdigest()


def manifest_problems(programs):
    """Malformed manifest rows: every row needs a sha256, and
    `soft_signed_zero`, when present, maps export names to non-empty reasons."""
    problems = []
    for name, row in sorted(programs.items()):
        if not isinstance(row, dict) or not isinstance(row.get("sha256"), str):
            problems.append(f"{name}: no sha256")
            continue
        soft = row.get("soft_signed_zero", {})
        if not isinstance(soft, dict) or not all(isinstance(k, str) and isinstance(v, str) and v.strip()
                                                 for k, v in soft.items()):
            problems.append(f"{name}: soft_signed_zero must map export names to reasons")
    return problems


def soft_zero_allowed(manifest=None):
    """{program: set of exports} whose +0/-0 differences the manifest allows."""
    try:
        programs = json.loads(Path(manifest or MANIFEST).read_text(encoding="utf-8"))["programs"]
    except (OSError, ValueError, KeyError, TypeError):
        return {}
    return {name: set((row or {}).get("soft_signed_zero") or {}) for name, row in programs.items()
            if isinstance(row, dict)}


def manifest_sha256(manifest=None):
    try:
        return hashlib.sha256(Path(manifest or MANIFEST).read_bytes()).hexdigest()
    except OSError:
        return None


def program_set_sha256(names):
    return hashlib.sha256("\n".join(sorted(names)).encode()).hexdigest()


def full_corpus(results, manifest=None):
    programs = results.get("programs") if isinstance(results, dict) else None
    corpus = corpus_programs(manifest)
    return isinstance(programs, dict) and corpus is not None and sorted(programs) == corpus


def _count(value):
    return type(value) is int and value >= 0


def _positive(value):
    return type(value) in (int, float) and math.isfinite(value) and value > 0


def _lane(row, lane):
    lanes = row.get("lanes") if isinstance(row, dict) else None
    record = lanes.get(lane) if isinstance(lanes, dict) else None
    return record if isinstance(record, dict) else None


def timing_samples(row, lane, mode):
    record = _lane(row, lane)
    timing = (record or {}).get("timing")
    entry = timing.get(mode) if isinstance(timing, dict) else None
    samples = entry.get("samples_ms") if isinstance(entry, dict) else None
    if not isinstance(samples, list) or not samples or not all(_positive(s) for s in samples):
        return None
    return samples


def reading(row, lane, metric):
    """One lane's reading of METRIC for one program, or None when absent or invalid."""
    source, _ = METRIC[metric]
    record = _lane(row, lane)
    if record is None:
        return None
    if source == "timing":
        samples = timing_samples(row, lane, metric[len("time_"):])
        return min(samples) if samples else None
    if source == "stack":
        value = (record.get("stack") or {}).get("stack_hwm") if isinstance(record.get("stack"), dict) else None
    else:
        block = record.get(source)
        value = block.get(metric) if isinstance(block, dict) else None
    return value if _count(value) else None


def workload_ok(row):
    workload = row.get("workload") if isinstance(row, dict) else None
    return isinstance(workload, dict) and workload.get("status") == "ok"


def b2_valid(row):
    """Whether this program's B2 module is usable as context: present and in
    agreement with B1 on the grid (and on the workload accumulator)."""
    record = _lane(row, B2)
    if record is None:
        return False
    diff = record.get("differential")
    if not isinstance(diff, dict) or diff.get("disagreements") != 0 or diff.get("missing_exports"):
        return False
    if workload_ok(row) and record.get("loop_acc") != (_lane(row, B1) or {}).get("loop_acc"):
        return False
    return True


def _soft_count(row):
    diff = (_lane(row, TCG) or {}).get("differential")
    value = diff.get("soft_signed_zero") if isinstance(diff, dict) else None
    return value if _count(value) else 0


def in_scope(row, metric):
    if not isinstance(row, dict) or row.get("verdict") != "MATCH":
        return False
    return METRIC[metric][0] == "static" or workload_ok(row)


def program_pairs(results, metric, lane=TCG, base=B1, scope=None):
    """{program: [lane reading, base reading]} over METRIC's scope (None for a
    missing reading), sorted by program name."""
    out = {}
    for name, row in sorted((results.get("programs") or {}).items()):
        if not in_scope(row, metric) or (scope is not None and not scope(row)):
            continue
        out[name] = [reading(row, lane, metric), reading(row, base, metric)]
    return out


def aggregate(pairs, how):
    """The aggregate of {program: [value, base]} pairs, or None (fail closed)
    when there is none or any pair is missing or unusable."""
    if not pairs or any(a is None or b is None for a, b in pairs.values()):
        return None
    if how == "geomean":
        if not all(_positive(a) and _positive(b) for a, b in pairs.values()):
            return None
        return complete_geomean([a / b for a, b in pairs.values()])
    if how == "total":
        top = sum(a for a, _ in pairs.values())
        bottom = sum(b for _, b in pairs.values())
        return top / bottom if bottom > 0 else None
    if how == "worst":
        if not all(_positive(a) and _positive(b) for a, b in pairs.values()):
            return None
        return max(a / b for a, b in pairs.values())
    raise ValueError(how)


def _median_pairs(results, mode):
    out = {}
    for name, row in sorted((results.get("programs") or {}).items()):
        if not in_scope(row, f"time_{mode}"):
            continue
        a, b = timing_samples(row, TCG, mode), timing_samples(row, B1, mode)
        out[name] = [statistics.median(a) if a else None, statistics.median(b) if b else None]
    return out


def _compile_pairs(results):
    out = {}
    for name, row in sorted((results.get("programs") or {}).items()):
        if in_scope(row, "file_bytes"):
            a, b = ((_lane(row, lane) or {}).get("compile_s") for lane in (TCG, B1))
            out[name] = [a if _positive(a) else None, b if _positive(b) else None]
    return out


def table_aggregates(results):
    """Every aggregate, recomputed from the per-program table."""
    programs = results.get("programs") if isinstance(results, dict) else None
    programs = programs if isinstance(programs, dict) else {}
    rows = list(programs.values())
    verdicts = [row.get("verdict") if isinstance(row, dict) else None for row in rows]
    total = len(rows)
    match = verdicts.count("MATCH")
    agg = {
        "total_programs": total,
        "match_count": match,
        "mismatch_count": verdicts.count("MISMATCH"),
        "incomplete_count": verdicts.count("INCOMPLETE"),
        "incomplete_unrefused": sorted(name for name, row in programs.items()
                                       if isinstance(row, dict) and row.get("verdict") == "INCOMPLETE"
                                       and row.get("incomplete_kind") != "refused"),
        "soft_signed_zero_total": sum(_soft_count(row) for row in rows
                                      if isinstance(row, dict) and row.get("verdict") == "MATCH"),
        "coverage_pct": 100.0 * match / total if total else 0.0,
        "workload_program_count": sum(1 for row in rows if in_scope(row, "dyn_insns")),
        "workload_excluded": sorted(name for name, row in programs.items()
                                    if in_scope(row, "file_bytes") and not workload_ok(row)),
    }
    missing = []
    for metric, _, how in METRICS:
        pairs = program_pairs(results, metric)
        missing += [f"{name}:{metric}" for name, (a, b) in pairs.items() if a is None or b is None]
        agg[metric_key(metric)] = aggregate(pairs, how)
    agg["readings_missing"] = sorted(missing)
    for mode in MODES:
        pairs = program_pairs(results, f"time_{mode}")
        agg[f"wasm_time_{mode}_worst_vs_{B1}"] = aggregate(pairs, "worst")
        agg[f"wasm_time_{mode}_median_geomean_vs_{B1}"] = aggregate(_median_pairs(results, mode), "geomean")
    agg[f"wasm_compile_geomean_vs_{B1}"] = aggregate(_compile_pairs(results), "geomean")

    def wins(metric, better):
        pairs = program_pairs(results, metric)
        if aggregate(pairs, METRIC[metric][1]) is None:
            return None
        return sum(1 for a, b in pairs.values() if better(a, b))

    agg["wasm_file_bytes_smaller_count"] = wins("file_bytes", lambda a, b: a < b)
    agg["wasm_time_turbofan_faster_count"] = wins("time_turbofan", lambda a, b: a < b)
    agg["wasm_stack_hwm_worse_count"] = wins("stack_hwm", lambda a, b: a > b)
    # B2 context: trust-cg against B2, and B2 against B1, over the programs
    # whose B2 module agrees with B1. Excluded: a B2 module that disagrees;
    # absent: no B2 module (no wasm-opt given, or wasm-opt failed).
    agg["b2_program_count"] = sum(1 for row in rows if in_scope(row, "file_bytes") and b2_valid(row))
    agg["b2_excluded"] = sorted(name for name, row in programs.items()
                                if in_scope(row, "file_bytes") and _lane(row, B2) is not None and not b2_valid(row))
    agg["b2_absent_count"] = sum(1 for row in rows if in_scope(row, "file_bytes") and _lane(row, B2) is None)
    for metric in B2_METRICS:
        how = METRIC[metric][1]
        agg[metric_key(metric, B2)] = aggregate(program_pairs(results, metric, TCG, B2, b2_valid), how)
        agg[f"{B2}_{metric}_{how}_vs_{B1}"] = aggregate(program_pairs(results, metric, B2, B1, b2_valid), how)
    agg["deterministic_complete"] = all(agg[metric_key(m)] is not None for m in DETERMINISTIC)
    agg["timing_complete"] = all(agg[metric_key(m)] is not None for m in TIMING)
    return agg


def table_issues(results):
    """Structural problems of the per-program table and stamps that disagree
    with their recomputation."""
    programs = results.get("programs")
    if not isinstance(programs, dict):
        return ["programs must be an object of per-program rows"]
    problems = []
    allowed = soft_zero_allowed()
    for name, row in sorted(programs.items()):
        if not isinstance(row, dict) or row.get("verdict") not in VERDICTS:
            problems.append(f"program {name}: verdict must be one of {list(VERDICTS)}")
        elif row["verdict"] == "INCOMPLETE" and row.get("incomplete_kind") not in INCOMPLETE_KINDS:
            problems.append(f"program {name}: an INCOMPLETE row needs an incomplete_kind in {list(INCOMPLETE_KINDS)}")
        elif row["verdict"] == "MATCH":
            if _lane(row, B1) is None or _lane(row, TCG) is None:
                problems.append(f"program {name}: a MATCH row needs the {B1} and {TCG} lanes")
                continue
            diff = _lane(row, TCG).get("differential")
            if not isinstance(diff, dict) or diff.get("disagreements") != 0 or diff.get("run_failure") \
                    or diff.get("missing_exports"):
                problems.append(f"program {name}: a MATCH row whose {TCG} differential is not clean")
                continue
            unlisted = sorted({case.get("export") for case in diff.get("soft_cases") or []
                               if isinstance(case, dict)} - allowed.get(name, set()))
            if unlisted or (_soft_count(row) and not allowed.get(name)):
                problems.append(f"program {name}: signed-zero differences allowed on exports {unlisted or '?'} "
                                "that the manifest does not list under soft_signed_zero")
    aggregates = results.get("aggregates")
    if not isinstance(aggregates, dict):
        return problems + ["aggregates must be an object"]
    expected = table_aggregates(results)
    for key, value in expected.items():
        if key not in aggregates:
            problems.append(f"aggregates.{key} is missing (recomputed {value!r})")
        elif not same_value(aggregates[key], value):
            problems.append(f"aggregates.{key} = {aggregates[key]!r} disagrees with its recomputation "
                            f"from the per-program table ({value!r})")
    return problems


def missing_provenance(provenance):
    """Mandatory provenance fields that are absent (or empty where a value is required)."""
    out = []
    for field in MANDATORY_PROVENANCE:
        if field not in provenance:
            out.append(field)
        elif field not in MAY_BE_EMPTY and provenance[field] in (None, "", [], {}):
            out.append(field)
    return out


def evidence_problems(results, manifest=None):
    """Every reason RESULTS are not evidence, recomputed from the results
    themselves (never from the headline stamp); empty means eligible."""
    if not isinstance(results, dict) or not isinstance(results.get("provenance"), dict):
        return ["no provenance"]
    p = results["provenance"]
    agg = table_aggregates(results)
    reasons = []
    if results.get("schema") != RESULTS_SCHEMA:
        reasons.append(f"schema {results.get('schema')!r} is not {RESULTS_SCHEMA}")
    if results.get("headline_eligible") is not True:
        reasons.append("headline_eligible is not stamped true")
    if p.get("quiet") is not True or p.get("load_status") != "QUIET":
        reasons.append(f"machine LOADED (1-min load {p.get('loadavg_before')}->{p.get('loadavg_after')} "
                       f"vs threshold {p.get('load_threshold')})")
    if p.get("load_threshold_overridden") is not False:
        reasons.append("--load-threshold overridden (or not stamped)")
    if p.get("runaway_processes"):
        reasons.append("runaway processes on the host")
    if p.get("git_dirty") is not False:
        reasons.append("source tree has tracked edits (or no git_dirty stamp)")
    if p.get("tcg_env") != {}:
        reasons.append(f"non-default TCG_*/TRUST_CG_* environment {p.get('tcg_env')!r}")
    if p.get("bridge_cg_args") != REQUIRED_BRIDGE_CG_ARGS:
        reasons.append(f"backend knobs {p.get('bridge_cg_args')!r} are not exactly {REQUIRED_BRIDGE_CG_ARGS}")
    if p.get("dylib_stale_source"):
        reasons.append(f"backend dylib older than its source {p.get('dylib_stale_source')}")
    if missing_provenance(p) or p.get("provenance_complete") is not True:
        reasons.append(f"incomplete provenance {missing_provenance(p)}")
    if p.get("target") != TARGET:
        reasons.append(f"target {p.get('target')!r} is not {TARGET}")
    if not full_corpus(results, manifest):
        reasons.append(f"program set is not the corpus of progs/manifest.json "
                       f"({len(results.get('programs') or {})} programs)")
    elif p.get("corpus_manifest_sha256") != manifest_sha256(manifest):
        reasons.append("corpus manifest digest differs from the committed manifest")
    if agg["mismatch_count"] != 0:
        reasons.append("MISMATCH rows")
    if agg["incomplete_unrefused"]:
        reasons.append(f"INCOMPLETE rows that are not typed refusals {agg['incomplete_unrefused'][:8]}")
    n_run = p.get("n_run")
    if type(n_run) is not int or n_run < N_RUN_MIN:
        reasons.append(f"timing samples per lane {n_run!r} < {N_RUN_MIN}")
    if sorted(p.get("modes") or []) != sorted(MODES):
        reasons.append(f"engine modes {p.get('modes')!r} are not {list(MODES)}")
    if not agg["deterministic_complete"]:
        reasons.append(f"deterministic readings incomplete ({agg['readings_missing'][:8]})")
    if not agg["timing_complete"]:
        reasons.append(f"timing readings incomplete ({agg['readings_missing'][:8]})")
    return reasons


def gate_verdicts(results, contract=None):
    """PROPOSED gate verdicts over the recomputed aggregates: True, False or
    None (unmeasured). Reported only; the ratchet never reads them."""
    contract = contract or load_contract()
    view = dict(results)
    view["aggregates"] = {**(results.get("aggregates") or {}), **table_aggregates(results)}
    return {name: gate_verdict(g["predicate"], view) for name, g in contract["gates"].items()}
