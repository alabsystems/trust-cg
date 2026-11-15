#!/usr/bin/env python3
"""Evaluate the gates.json predicates against a beat-llvm results JSON — no dependencies.

The predicates are written in a jq-compatible conjunction subset:
    .path.to.field OP literal [and .path OP literal ...]
where OP is one of == != <= >= < > and literal is a number, `null`, `true`, `false`,
or a double-quoted string. Missing or nonnumeric ordered operands fail closed;
unlike jq's total ordering, null can never satisfy a numeric threshold.

Aggregates: `count_aggregates`, `ratio_aggregates` (runtime/compile, from each
lane's raw samples) and `resource_aggregates` (linked and emitted-code size, and
peak RSS as the median of each lane's raw samples) are the one implementation
of the fail-closed, EXACT (unrounded) aggregation. run.py stamps
their result into the results JSON; this checker and
scripts/check_perf_ratchet.py recompute it from the per-program table and refuse
a stamp that disagrees (`table_issues`), and eligibility requires every MATCH
row's values (`evidence_eligible`). `gate_verdict` reports PASS, fail or
UNMEASURED (a null input) and is shared with the ratchet.

Usage: python3 check_gates.py <results.json> [gates.json]
Exit:  0 = all ELIGIBLE gates evaluated (verdicts printed; gates are goals, not ratchets —
           failing a parity gate is expected during the climb)
       2 = run is INELIGIBLE (LOADED/dirty/mismatch/gate-off/incomplete size or RSS)
           or input/predicate error
"""
import hashlib
import json
import math
import operator
import re
import statistics
import sys
from pathlib import Path

# The contract corpus (BENCH-3): progs/manifest.json beside this directory.
MANIFEST = Path(__file__).resolve().parent.parent / "progs" / "manifest.json"
# Stamped aggregates are recomputed here from the per-program table. Floats
# may differ in the last bits between platforms' libm (log/exp), so a stamp is
# accepted within this relative tolerance; anything larger is an edit.
STAMP_REL_TOL = 1e-12

TOKEN = re.compile(r'\s*(\.[A-Za-z_][A-Za-z0-9_.]*|==|!=|<=|>=|<|>|and\b|null\b|true\b|false\b|"[^"]*"|-?\d+(?:\.\d+)?)')
COMPARISONS = {"<=": operator.le, ">=": operator.ge, "<": operator.lt, ">": operator.gt}


def tokenize(pred):
    out, i = [], 0
    while i < len(pred):
        m = TOKEN.match(pred, i)
        if not m:
            if pred[i:].strip():
                raise ValueError(f"unparseable predicate at: {pred[i:]!r}")
            break
        out.append(m.group(1))
        i = m.end()
    return out


def literal(tok):
    if tok == "null":
        return None
    if tok == "true":
        return True
    if tok == "false":
        return False
    if tok.startswith('"'):
        return tok[1:-1]
    return float(tok) if "." in tok else int(tok)


def lookup(doc, path):
    cur = doc
    for part in path[1:].split("."):
        if not isinstance(cur, dict) or part not in cur:
            return None
        cur = cur[part]
    return cur


def evaluate(pred, doc):
    toks = tokenize(pred)
    # Each comparison has three tokens; conjunctions add four. Validate the
    # complete grammar before evaluating so an empty/truncated predicate cannot
    # turn a malformed contract into a successful gate.
    if not toks or len(toks) % 4 != 3:
        raise ValueError("expected a comparison, optionally followed by 'and' comparisons")
    result, i = True, 0
    while i < len(toks):
        lhs, op, rhs = toks[i], toks[i + 1], toks[i + 2]
        if op not in ("==", "!=", *COMPARISONS):
            raise ValueError(f"unsupported comparison operator: {op!r}")
        i += 3
        if i < len(toks):
            if toks[i] != "and":
                raise ValueError(f"only 'and' conjunctions supported, got {toks[i]!r}")
            i += 1
        l = lookup(doc, lhs) if lhs.startswith(".") else literal(lhs)
        r = lookup(doc, rhs) if rhs.startswith(".") else literal(rhs)
        if op == "==":
            ok = l == r and isinstance(l, bool) == isinstance(r, bool)
        elif op == "!=":
            ok = l != r or isinstance(l, bool) != isinstance(r, bool)
        else:
            # bool is a subclass of int in Python, but a true/false stamp is
            # never a measured ratio. JSON's nonstandard NaN/Infinity values
            # likewise must not satisfy a gate.
            numeric = all(type(v) in (int, float) and math.isfinite(v) for v in (l, r))
            ok = numeric and COMPARISONS[op](l, r)
        result = result and ok
    return result


def measurement_issues(aggregates):
    """Validate ratios and the intent-to-treat denominator before gate evaluation.

    Shared by the standalone gate checker and the performance ledger importer.
    Missing optional ratios represent unmeasured lanes; invalid ratios are errors.
    Coverage is the exact percentage; committed ledger rows condensed before
    aggregates were stamped exactly carry it rounded to one decimal, which is
    accepted as the legacy form.
    """
    if not isinstance(aggregates, dict):
        return ["aggregates must be an object"]
    problems = []
    count_fields = ("total_programs", "match_count", "incomplete_count", "mismatch_count")
    for field in count_fields:
        value = aggregates.get(field)
        if type(value) is not int or value < 0:
            problems.append(f"{field} must be a non-negative integer")
    coverage = aggregates.get("coverage_pct")
    if type(coverage) not in (int, float) or not math.isfinite(coverage) or not 0 <= coverage <= 100:
        problems.append("coverage_pct must be finite and between 0 and 100")
    elif all(type(aggregates.get(field)) is int and aggregates[field] >= 0 for field in count_fields):
        total = aggregates["total_programs"]
        if sum(aggregates[field] for field in count_fields[1:]) != total:
            problems.append("outcome counts do not sum to total_programs")
        expected = 100.0 * aggregates["match_count"] / total if total else 0.0
        if coverage != expected and coverage != round(expected, 1):
            problems.append("coverage_pct disagrees with match_count/total_programs")
    for field, value in aggregates.items():
        if "_vs_llvm_" in field and value is not None:
            if type(value) not in (int, float) or not math.isfinite(value) or value <= 0:
                problems.append(f"{field} must be a finite positive ratio or null")
    for field in RESOURCE_COUNT_KEYS:
        value = aggregates.get(field)
        if value is not None and (type(value) is not int or value < 0):
            problems.append(f"{field} must be a non-negative integer or null")
    return problems


def corpus_programs(manifest=None):
    """The contract corpus's program names, sorted, or None if unreadable."""
    try:
        programs = json.loads(Path(manifest or MANIFEST).read_text(encoding="utf-8"))["programs"]
    except (OSError, ValueError, KeyError, TypeError):
        return None
    return sorted(programs) if isinstance(programs, dict) else None


def program_set_sha256(names):
    """Digest of a program set (order-independent), for like-with-like comparison."""
    return hashlib.sha256("\n".join(sorted(names)).encode()).hexdigest()


def full_corpus(results, manifest=None):
    """Whether a results JSON measured exactly the contract corpus (not a
    `--progs` subset, nor a corpus with programs added or missing)."""
    programs = results.get("programs") if isinstance(results, dict) else None
    corpus = corpus_programs(manifest)
    return isinstance(programs, dict) and corpus is not None and sorted(programs) == corpus


def proof_checker_runs(provenance):
    """Whether the stamped independent-proof-checker record names a candidate
    that ran when the harness probed it (see run.py proof_checker_record)."""
    checker = provenance.get("proof_checker") if isinstance(provenance, dict) else None
    candidates = checker.get("candidates") if isinstance(checker, dict) else None
    return isinstance(candidates, list) and any(
        isinstance(c, dict) and c.get("runs") is True for c in candidates)


def rss_samples_meet_contract(programs, resources):
    """Whether every retained peak-RSS lane holds at least RSS_CONTRACT_N
    samples. Vacuously true with no MATCH row, which has no RSS reading
    (`rss_min_samples` is then null); otherwise `rss_min_samples` must be an
    int of at least the contract N."""
    matched = any(isinstance(row, dict) and row.get("verdict") == "MATCH"
                  for row in programs.values())
    minimum = resources.get("rss_min_samples")
    return not matched or (type(minimum) is int and minimum >= RSS_CONTRACT_N)


def evidence_eligible(results, eligibility):
    """Recheck recorded eligibility facts before allowing headline evidence.

    Size and peak RSS are gated metrics (gates.json version 2; emitted-code
    size and median-of-N RSS since version 3), so they are required data:
    every MATCH row must carry every resource reading, every RSS reading must
    be the median of at least RSS_CONTRACT_N samples, and the RSS sampler's
    calibration must hold; every MATCH row must also carry the raw samples its
    runtime and compile ratios come from. A run with no MATCH row has no
    reading to hold to the sample count (`rss_samples_meet_contract`): it is
    held to the provenance N only, as every earlier version held it, so a
    production-lane run that compiles nothing stays evidence of its 0%
    coverage. That is recomputed from the
    per-program table, never read from a stamp. The production proof
    lane also needs an independent proof checker the backend can run (a
    stamped candidate that ran when probed) that never reported DEGRADED
    verification, and no backend knob.

    Only a run of exactly the contract corpus (progs/manifest.json) can be
    evidence: a `--progs` subset is a diagnostic, never a baseline.

    Ineligibility only withholds EVIDENCE status. It never exempts a
    like-with-like row from the ledger ratchet's regression checks
    (scripts/check_perf_ratchet.py).
    """
    if not evaluate(eligibility, results):
        return False
    provenance = results.get("provenance", {})
    env = provenance.get("tcg_env")
    programs = results.get("programs")
    if not isinstance(programs, dict):
        return False
    resources = resource_aggregates(programs, rss_cross_check(results))
    ratios = ratio_aggregates(programs)
    return (
        isinstance(env, dict)
        and not any(key in env for key in ("TCG_NO_PROOF_CERTS", "TCG_NO_PROOF_CACHE"))
        and env.get("TCG_REFINE_SOLVER") != "0"
        and provenance.get("provenance_complete") is True
        and provenance.get("load_status") == "QUIET"
        and not provenance.get("load_threshold_overridden", False)
        and not provenance.get("dylib_stale_override", False)
        and not provenance.get("runaway_processes", [])
        # The production lane passes no backend knob and its independent proof
        # checker runs and is usable; a knob list, no runnable candidate or a
        # DEGRADED banner is a diagnostic lane. The knob list is what the
        # harness recorded passing: like every provenance field it is
        # self-reported, not attested.
        and not provenance.get("bridge_cg_args")
        and not provenance.get("proof_checker_degraded")
        and proof_checker_runs(provenance)
        and type(provenance.get("n_compile")) is int and provenance["n_compile"] >= 3
        and type(provenance.get("n_run")) is int and provenance["n_run"] >= 5
        and type(provenance.get("n_rss")) is int and provenance["n_rss"] >= RSS_CONTRACT_N
        and resources["resource_measurement_complete"] is True
        and rss_samples_meet_contract(programs, resources)
        and resources["rss_sampler_floor_bytes"] is not None
        and ratios["ratio_missing"] == {}
        and full_corpus(results)
    )


# ------------------------------------------------------------ aggregation
# The aggregates the gates read, computed ONCE, here, from the per-program
# table: run.py stamps them, and this checker and the ledger ratchet
# recompute them and refuse a stamp that disagrees. They are EXACT floats:
# rounding is for display only, because a gate compared on a rounded value is
# weaker than its threshold (a size geomean of 1.0000187 rounds to 1.0 and
# would pass "<= 1.00").
#
# Fail-closed: an aggregate over MATCH rows is computed only when EVERY
# covered MATCH row has its value; otherwise it is null and the rows lacking
# it are named (`ratio_missing`, `resource_missing`). Nothing is averaged over
# the subset that happened to be measured.


def _finite_positive(value):
    return type(value) in (int, float) and math.isfinite(value) and value > 0


def complete_geomean(values):
    """Geomean of EVERY value, or None when the list is empty or any value is
    missing, non-numeric or not strictly positive."""
    if not values or not all(_finite_positive(v) for v in values):
        return None
    return math.exp(sum(math.log(v) for v in values) / len(values))


def complete_max(values):
    """The largest of EVERY value, or None under complete_geomean's rule."""
    return max(values) if complete_geomean(values) is not None else None


def lane_median(record):
    """Exact median of one lane's raw timing samples (`times_s`), or None when
    the lane did not complete or any sample is missing or invalid."""
    if not isinstance(record, dict) or ("ok" in record and record["ok"] is not True):
        return None
    times = record.get("times_s")
    if not isinstance(times, list) or not times or not all(_finite_positive(t) for t in times):
        return None
    return statistics.median(times)


RATIO_METRICS = (
    ("runtime_vs_llvm_o3", ("run", "bridge"), ("run", "llvm_o3")),
    ("compile_warm_vs_llvm_o0", ("compile", "bridge_warm"), ("compile", "llvm_o0")),
    ("compile_warm_vs_llvm_o2", ("compile", "bridge_warm"), ("compile", "llvm_o2")),
    ("compile_warm_vs_llvm_o3", ("compile", "bridge_warm"), ("compile", "llvm_o3")),
)
COLD_METRICS = (
    ("compile_cold_vs_llvm_o0", ("compile", "bridge_cold"), ("compile", "llvm_o0")),
    ("compile_cold_vs_llvm_o2", ("compile", "bridge_cold"), ("compile", "llvm_o2")),
    ("compile_cold_vs_llvm_o3", ("compile", "bridge_cold"), ("compile", "llvm_o3")),
)
COUNT_AGGREGATE_KEYS = (
    "total_programs", "match_count", "incomplete_count", "mismatch_count",
    "nondet_failclosed_count", "nondet_candidate_count", "coverage_pct",
)
RATIO_AGGREGATE_KEYS = (
    "runtime_geomean_vs_llvm_o3", "runtime_worst_vs_llvm_o3",
    "scalar_runtime_geomean_vs_llvm_o3", "vectorizable_worst_runtime_vs_llvm_o3",
    "by_category",
    "compile_warm_geomean_vs_llvm_o0", "compile_warm_geomean_vs_llvm_o2",
    "compile_warm_geomean_vs_llvm_o3", "compile_cold_geomean_vs_llvm_o0",
    "compile_cold_geomean_vs_llvm_o2", "compile_cold_geomean_vs_llvm_o3",
    "ratio_missing",
)


def cold_requested(programs):
    """Whether the run measured the cold lane (--cold): any row carries it."""
    return any(isinstance(row, dict) and "bridge_cold" in (row.get("compile") or {})
               for row in programs.values())


def runtime_outcomes_match(row):
    """Both timing lanes completed with the same normal fixture checksum."""
    runs = row.get("run")
    if not isinstance(runs, dict):
        return False
    records = [runs.get(lane) for lane in ("llvm_o3", "bridge")]
    for record in records:
        if (not isinstance(record, dict)
                or type(record.get("exit")) is not int
                or not 0 <= record["exit"] < 126
                or "nondet_exit" not in record
                or record["nondet_exit"] is not None
                or record.get("error") is not None):
            return False
    return records[0]["exit"] == records[1]["exit"]


def program_ratios(row, cold=False):
    """A row's exact bridge/LLVM ratios from its lanes' raw samples (None when
    either lane lacks them)."""
    out = {}
    for metric, (num_table, num_lane), (den_table, den_lane) in RATIO_METRICS + (COLD_METRICS if cold else ()):
        if num_table == "run" and not runtime_outcomes_match(row):
            out[metric] = None
            continue
        numerator = lane_median((row.get(num_table) or {}).get(num_lane))
        denominator = lane_median((row.get(den_table) or {}).get(den_lane))
        out[metric] = numerator / denominator if numerator and denominator else None
    return out


def count_aggregates(programs):
    """Intent-to-treat outcome counts and the exact coverage percentage."""
    rows = [row for row in programs.values() if isinstance(row, dict)]
    total, match = len(programs), sum(1 for row in rows if row.get("verdict") == "MATCH")
    return {
        "total_programs": total,
        "match_count": match,
        "incomplete_count": sum(1 for row in rows if row.get("verdict") == "INCOMPLETE"),
        "mismatch_count": sum(1 for row in rows if row.get("verdict") == "MISMATCH"),
        "nondet_failclosed_count": sum(1 for row in rows if row.get("label") == "NONDET-FAILCLOSED"),
        "nondet_candidate_count": sum(1 for row in rows if row.get("label") == "NONDET-CANDIDATE"),
        "coverage_pct": 100.0 * match / total if total else 0.0,
    }


def ratio_aggregates(programs):
    """Runtime and compile aggregates over the MATCH rows, from raw samples."""
    rows = sorted((name, row) for name, row in programs.items()
                  if isinstance(row, dict) and row.get("verdict") == "MATCH")
    cold = cold_requested(programs)
    per = {name: program_ratios(row, cold) for name, row in rows}
    category = {name: row.get("category", "scalar") for name, row in rows}
    missing = {}

    def values(metric, names):
        absent = [name for name in names if per[name].get(metric) is None]
        if absent:
            missing[metric] = sorted(set(missing.get(metric, [])) | set(absent))
        return [per[name].get(metric) for name in names]

    names = [name for name, _ in rows]
    runtime = values("runtime_vs_llvm_o3", names)
    vectorizable = values("runtime_vs_llvm_o3", [n for n in names if category[n] == "vectorizable"])
    agg = {
        "runtime_geomean_vs_llvm_o3": complete_geomean(runtime),
        "runtime_worst_vs_llvm_o3": complete_max(runtime),
        "scalar_runtime_geomean_vs_llvm_o3": complete_geomean(
            values("runtime_vs_llvm_o3", [n for n in names if category[n] == "scalar"])),
        "vectorizable_worst_runtime_vs_llvm_o3": complete_max(vectorizable),
    }
    # Coverage per category — first-class intent-to-treat output.
    cats = {}
    for row in programs.values():
        if not isinstance(row, dict):
            continue
        c = cats.setdefault(row.get("category", "scalar"),
                            {"total": 0, "match": 0, "incomplete": 0, "mismatch": 0})
        c["total"] += 1
        key = {"MATCH": "match", "INCOMPLETE": "incomplete", "MISMATCH": "mismatch"}.get(row.get("verdict"))
        if key:
            c[key] += 1
    for cname, c in cats.items():
        c["coverage_pct"] = 100.0 * c["match"] / c["total"] if c["total"] else 0.0
        c["runtime_geomean_vs_llvm_o3"] = complete_geomean(
            values("runtime_vs_llvm_o3", [n for n in names if category[n] == cname]))
    agg["by_category"] = {k: cats[k] for k in sorted(cats)}
    for opt in ("0", "2", "3"):
        agg[f"compile_warm_geomean_vs_llvm_o{opt}"] = complete_geomean(
            values(f"compile_warm_vs_llvm_o{opt}", names))
        # The cold lane runs only under --cold; unrequested, its aggregates
        # are null (unmeasured) and its absence is not a missing value.
        agg[f"compile_cold_geomean_vs_llvm_o{opt}"] = (
            complete_geomean(values(f"compile_cold_vs_llvm_o{opt}", names)) if cold else None)
    agg["ratio_missing"] = missing
    return agg


# ------------------------------------------------------------------ resources
# Size and peak-RSS aggregation (gates.json version 2, revised by version 3).
#
# Size has two measures. `size_bytes` is the linked executable's file bytes,
# which include the shared standard library and so read about 1.000x
# (S1/S2). `emitted_size_bytes` is the emitted-code size (version 3, S3/S4):
# the linked image's code and read-only data bytes that the linker's own map
# attributes to the objects the compile produced (benchmarks/beat-llvm/
# emitted_size.py holds the definition).
#
# Peak RSS (version 3): every reading is the MEDIAN of an odd number of
# dedicated samples per lane (RSS_CONTRACT_N preregistered), recomputed here
# from the retained raw samples (`rss_samples`); a stamped per-program
# reading that disagrees with its samples is a table issue. A reading whose
# samples are not all valid is missing, never a median of the survivors.
#
# The per-process RSS sampler has a floor (metrics-contract.md "Size and
# memory"). The kernel reports max(the wrapper's own resident set, inherited
# across exec, and the program's peak), so every reading is at least the
# floor and a reading above it IS the program's peak.
#   * A comparison is RESOLVED when both readings are above
#     RSS_FLOOR_BOUND_FACTOR times the measured floor (the TY/TLC contract's
#     rule, section 8.3); only then is its ratio a measurement.
#   * A LOSS is conclusive wherever it sits: a bridge reading beyond the
#     program's parity band above both the LLVM reading and the floor is the
#     bridge's peak, and the LLVM reading can only overstate LLVM's peak. The
#     band is the contract's runtime rule applied to the RSS samples:
#     max(5%, RSS_SPREAD_FACTOR x the larger lane's relative sample spread).
#     The spread is the range over the median, so ONE outlier sample widens
#     the band although the median ignores it: a band that wide cannot
#     establish parity.
#   * A comparison is also NOISY, and so unresolved, when the larger lane's
#     relative spread exceeds RSS_SPREAD_MAX (the runtime lane's resolvability
#     cap, run.py RELIABLE_SPREAD_MAX). A noisy comparison still reports a
#     loss beyond its band, but it never counts as parity.
#   * R1 fails on any loss, passes only when EVERY matching program's
#     comparison is resolved (above the floor and not noisy) and none is a
#     loss, and is otherwise unmeasured (`program_rss_resolved_loss_count`
#     null): a program at the floor, or one whose samples disagree by more
#     than the cap, is not a measured parity.
RSS_FLOOR_BOUND_FACTOR = 2
# The contract's minimum parity band (Runtime: max(5%, 2 x relative spread)).
RSS_PARITY_BAND = 1.05
RSS_SPREAD_FACTOR = 2
# The largest relative sample spread at which a comparison is resolved.
RSS_SPREAD_MAX = 0.25
# Preregistered in gates.json version 3: peak RSS is the median of this many
# dedicated samples per lane (an odd number, so the median is a reading).
RSS_CONTRACT_N = 5
RESOURCE_LANES = (
    ("size_bytes", ("llvm_o3", "bridge")),
    ("emitted_size_bytes", ("llvm_o3", "bridge")),
    ("peak_rss_bytes", ("llvm_o3", "bridge")),
    ("compile_peak_rss_bytes", ("llvm_o2", "llvm_o3", "bridge")),
)
# The per-program RSS fields and the `rss_samples` table holding their samples.
RSS_SAMPLE_KIND = {"peak_rss_bytes": "program", "compile_peak_rss_bytes": "compiler"}
RESOURCE_AGGREGATE_KEYS = (
    "resource_measurement_complete", "resource_missing",
    "rss_sampler_floor_bytes", "rss_floor_bound_bytes",
    "size_geomean_vs_llvm_o3", "size_worst_vs_llvm_o3",
    "emitted_size_geomean_vs_llvm_o3", "emitted_size_worst_vs_llvm_o3",
    "rss_geomean_vs_llvm_o3",
    "compile_rss_geomean_vs_llvm_o2", "compile_rss_geomean_vs_llvm_o3",
    "program_rss_floor_bound_count", "program_rss_resolved_loss_count",
    "program_rss_resolved_losses", "compile_rss_floor_bound_count",
    "rss_min_samples", "program_rss_max_rel_spread", "compile_rss_max_rel_spread",
)
RESOURCE_COUNT_KEYS = ("program_rss_floor_bound_count", "program_rss_resolved_loss_count",
                       "compile_rss_floor_bound_count", "rss_min_samples")


def _positive_int(value):
    return type(value) is int and value > 0


def rss_cross_check(results):
    """The RSS sampler's calibration record stamped in provenance, or None."""
    provenance = results.get("provenance") if isinstance(results, dict) else None
    sampling = provenance.get("rss_sampling") if isinstance(provenance, dict) else None
    cross = sampling.get("cross_check") if isinstance(sampling, dict) else None
    return cross if isinstance(cross, dict) else None


def rss_sampler_floor(cross_check):
    """The sampler floor in bytes when the sampler's calibration holds, else None.

    Holds means: the floor probe produced a reading, the calibration allocation
    was covered, and `/usr/bin/time` agreed, or is recorded as absent
    (`time_wrapper_present: false`). A present `/usr/bin/time` whose output
    could not be used is a failed cross-check, not a missing one. A sampler
    that cannot be calibrated cannot qualify any RSS reading.
    """
    if not isinstance(cross_check, dict):
        return None
    floor = cross_check.get("sampler_floor_bytes")
    if not _positive_int(floor):
        return None
    if cross_check.get("rusage_covers_allocation") is not True:
        return None
    agree = cross_check.get("agree")
    if agree is not True and not (agree is None and cross_check.get("time_wrapper_present") is False):
        return None
    return floor


def rss_lane_samples(row, field, lane):
    """The raw readings (bytes) behind one lane's peak-RSS reading: the
    `bytes` of each retained sample record, or None without a sample list."""
    kind = RSS_SAMPLE_KIND[field]
    tables = row.get("rss_samples") if isinstance(row, dict) else None
    table = tables.get(kind) if isinstance(tables, dict) else None
    samples = table.get(lane) if isinstance(table, dict) else None
    if not isinstance(samples, list):
        return None
    return [sample.get("bytes") if isinstance(sample, dict) else None for sample in samples]


def sample_median(values):
    """The exact median of an ODD number of positive integer readings (itself
    a reading), or None when any sample is missing or invalid."""
    if not isinstance(values, list) or not values or len(values) % 2 == 0:
        return None
    if not all(_positive_int(value) for value in values):
        return None
    return statistics.median(values)


def relative_spread(values):
    """(max - min) / median of a sample list, or None when it has no median."""
    median = sample_median(values)
    return None if median is None else (max(values) - min(values)) / median


def resource_reading(row, field, lane):
    """One lane's reading of a resource metric, or None when it is missing:
    the median of its raw samples for peak RSS, the recorded bytes for size."""
    if field in RSS_SAMPLE_KIND:
        return sample_median(rss_lane_samples(row, field, lane))
    values = row.get(field) if isinstance(row, dict) else None
    value = values.get(lane) if isinstance(values, dict) else None
    return value if _positive_int(value) else None


def reading_issues(programs):
    """Stamped per-program RSS readings that disagree with the median of their
    own retained samples (an edited table, or another harness)."""
    issues = []
    for name, row in sorted(programs.items()):
        if not isinstance(row, dict) or row.get("verdict") != "MATCH":
            continue
        for field, lanes in RESOURCE_LANES:
            if field not in RSS_SAMPLE_KIND:
                continue
            stamped = row.get(field) if isinstance(row.get(field), dict) else {}
            for lane in lanes:
                expected = resource_reading(row, field, lane)
                if stamped.get(lane) != expected or type(stamped.get(lane)) is not type(expected):
                    issues.append(f"{name}.{field}.{lane} = {stamped.get(lane)!r} is not the median "
                                  f"of its samples ({expected!r})")
    return issues


def resource_aggregates(programs, cross_check):
    """Size and RSS aggregates over the MATCH rows of a results `programs` table."""
    rows = [(name, row) for name, row in sorted(programs.items())
            if isinstance(row, dict) and row.get("verdict") == "MATCH"]
    by_name = dict(rows)
    missing, readings, values = [], {}, {}
    for field, lanes in RESOURCE_LANES:
        complete = True
        for name, row in rows:
            for lane in lanes:
                reading = resource_reading(row, field, lane)
                values[(name, field, lane)] = reading
                if reading is None:
                    missing.append(f"{name}.{field}.{lane}")
                    complete = False
        readings[field] = complete
    floor = rss_sampler_floor(cross_check)
    bound = None if floor is None else RSS_FLOOR_BOUND_FACTOR * floor

    def value(name, field, lane):
        return values[(name, field, lane)]

    def ratios(field, lane, base):
        if not readings[field]:
            return None
        return [value(name, field, lane) / value(name, field, base) for name, _ in rows]

    def spread(name, field, lane):
        return relative_spread(rss_lane_samples(by_name[name], field, lane))

    size = ratios("size_bytes", "bridge", "llvm_o3")
    emitted = ratios("emitted_size_bytes", "bridge", "llvm_o3")
    program_rss = ratios("peak_rss_bytes", "bridge", "llvm_o3")
    compile_o2 = ratios("compile_peak_rss_bytes", "bridge", "llvm_o2")
    compile_o3 = ratios("compile_peak_rss_bytes", "bridge", "llvm_o3")
    # With no MATCH row nothing was measured: the counts stay null, so a gate
    # over them reads unmeasured instead of passing vacuously.
    floor_bound = losses = loss_count = compile_floor_bound = None
    if bound is not None and readings["peak_rss_bytes"] and rows:
        floor_bound, noisy, losses = 0, 0, []
        for name, _ in rows:
            llvm = value(name, "peak_rss_bytes", "llvm_o3")
            bridge = value(name, "peak_rss_bytes", "bridge")
            if llvm <= bound or bridge <= bound:
                floor_bound += 1
            noise = max(spread(name, "peak_rss_bytes", "llvm_o3"),
                        spread(name, "peak_rss_bytes", "bridge"))
            band = max(RSS_PARITY_BAND, 1 + RSS_SPREAD_FACTOR * noise)
            if bridge > band * max(llvm, floor):
                losses.append(name)
            elif noise > RSS_SPREAD_MAX:
                noisy += 1
        loss_count = (len(losses) if losses
                      else (0 if floor_bound == 0 and noisy == 0 else None))
    if bound is not None and readings["compile_peak_rss_bytes"] and rows:
        compile_floor_bound = sum(1 for name, _ in rows
                                  for lane in ("llvm_o2", "llvm_o3", "bridge")
                                  if value(name, "compile_peak_rss_bytes", lane) <= bound)
    rss_fields = [(field, lanes) for field, lanes in RESOURCE_LANES if field in RSS_SAMPLE_KIND]
    rss_complete = bool(rows) and all(readings[field] for field, _ in rss_fields)
    min_samples = (min(len(rss_lane_samples(row, field, lane)) for _, row in rows
                       for field, lanes in rss_fields for lane in lanes)
                   if rss_complete else None)

    def max_spread(field, lanes):
        if not rows or not readings[field]:
            return None
        return max(spread(name, field, lane) for name, _ in rows for lane in lanes)

    return {
        "resource_measurement_complete": not missing,
        "resource_missing": missing,
        "rss_sampler_floor_bytes": floor,
        "rss_floor_bound_bytes": bound,
        "size_geomean_vs_llvm_o3": complete_geomean(size or []),
        "size_worst_vs_llvm_o3": complete_max(size or []),
        "emitted_size_geomean_vs_llvm_o3": complete_geomean(emitted or []),
        "emitted_size_worst_vs_llvm_o3": complete_max(emitted or []),
        # A floor-bound comparison resolves nothing (gates version 4, ruling
        # OD-32): the program geomean is null unless the sampler is calibrated
        # and no MATCH program reads at or below the floor bound.
        "rss_geomean_vs_llvm_o3": (complete_geomean(program_rss or [])
                                   if floor_bound == 0 else None),
        "compile_rss_geomean_vs_llvm_o2": complete_geomean(compile_o2 or []),
        "compile_rss_geomean_vs_llvm_o3": complete_geomean(compile_o3 or []),
        "program_rss_floor_bound_count": floor_bound,
        "program_rss_resolved_loss_count": loss_count,
        "program_rss_resolved_losses": losses,
        "compile_rss_floor_bound_count": compile_floor_bound,
        "rss_min_samples": min_samples,
        "program_rss_max_rel_spread": max_spread("peak_rss_bytes", ("llvm_o3", "bridge")),
        "compile_rss_max_rel_spread": max_spread("compile_peak_rss_bytes",
                                                 ("llvm_o2", "llvm_o3", "bridge")),
    }


def table_aggregates(results):
    """Every gated aggregate, recomputed from a results JSON's per-program table."""
    programs = results["programs"]
    agg = count_aggregates(programs)
    agg.update(ratio_aggregates(programs))
    agg.update(resource_aggregates(programs, rss_cross_check(results)))
    return agg


TABLE_AGGREGATE_KEYS = COUNT_AGGREGATE_KEYS + RATIO_AGGREGATE_KEYS + RESOURCE_AGGREGATE_KEYS


# The aggregate each gates.json version's results first carry: a results JSON
# without it was written by an older harness under older aggregation rules.
CURRENT_AGGREGATE_MARKERS = (
    "resource_measurement_complete",  # version 2: exact, fail-closed, recomputed
    "emitted_size_geomean_vs_llvm_o3",  # version 3: emitted size, median-of-N RSS
)


def predates_table_aggregates(results):
    """A results JSON from before the current recomputed, fail-closed
    aggregates (gates.json version 3: emitted-code size and median-of-N peak
    RSS): its stamps cannot be checked against its table under today's rules."""
    aggregates = results.get("aggregates") if isinstance(results, dict) else None
    return isinstance(aggregates, dict) and any(
        marker not in aggregates for marker in CURRENT_AGGREGATE_MARKERS)


def table_issues(results):
    """Integrity of the stamped aggregates against the per-program table.

    The table must hold every counted program, and every stamped count,
    runtime/compile ratio aggregate and size/RSS aggregate must EQUAL its
    recomputation (the harness stamps the same function's output, so any
    difference is an edit or a different harness), as must every per-program
    peak-RSS reading the median of its own samples (`reading_issues`).
    Missing values are NOT an issue here (they null an aggregate and make a
    row ineligible); an aggregate that disagrees with its own table is.
    """
    if not isinstance(results, dict):
        return ["results must be an object"]
    programs, aggregates = results.get("programs"), results.get("aggregates")
    if not isinstance(programs, dict):
        return ["programs must be an object keyed by program (the per-program table)"]
    if not isinstance(aggregates, dict):
        return ["aggregates must be an object"]
    if predates_table_aggregates(results):
        return ["results predate the recomputed fail-closed aggregates of gates.json version 3 "
                f"(missing aggregates {[m for m in CURRENT_AGGREGATE_MARKERS if m not in aggregates]}); "
                "rerun the harness"]
    expected = table_aggregates(results)
    return reading_issues(programs) + [
        f"aggregates.{key} = {aggregates.get(key)!r} disagrees with its recomputation "
        f"from the per-program table ({expected[key]!r})"
        for key in TABLE_AGGREGATE_KEYS if not same_value(aggregates.get(key), expected[key])]


def same_value(stamped, expected):
    """Equality for a stamp and its recomputation: exact for everything but
    floats, which agree within STAMP_REL_TOL (a different libm may round
    log/exp differently); containers compare element by element. A bool never
    equals a number."""
    if isinstance(stamped, bool) or isinstance(expected, bool):
        return type(stamped) is type(expected) and stamped == expected
    if isinstance(stamped, (int, float)) and isinstance(expected, (int, float)):
        if isinstance(stamped, int) and isinstance(expected, int):
            return stamped == expected
        return (math.isfinite(stamped) and math.isfinite(expected)
                and math.isclose(stamped, expected, rel_tol=STAMP_REL_TOL, abs_tol=0.0))
    if isinstance(stamped, dict) and isinstance(expected, dict):
        return stamped.keys() == expected.keys() and all(
            same_value(stamped[key], expected[key]) for key in expected)
    if isinstance(stamped, list) and isinstance(expected, list):
        return len(stamped) == len(expected) and all(
            same_value(a, b) for a, b in zip(stamped, expected))
    return stamped == expected


# Kept for callers of the first version of this module.
resource_issues = table_issues


def recomputed_view(results):
    """RESULTS with every table aggregate replaced by its recomputation, so a
    gate reads the value the table implies, never a stamp that agreed with it
    only within STAMP_REL_TOL (such a stamp could otherwise flip a threshold
    such as S2's "<= 1.00"). Results without a usable table are returned as
    they are."""
    if (not isinstance(results, dict) or not isinstance(results.get("programs"), dict)
            or not isinstance(results.get("aggregates"), dict) or predates_table_aggregates(results)):
        return results
    view = dict(results)
    view["aggregates"] = {**results["aggregates"], **table_aggregates(results)}
    return view


def gate_verdict(predicate, results):
    """True (PASS), False (fail) or None (UNMEASURED: an aggregate the predicate
    reads is null or absent — a lane that was not run, or a fail-closed
    aggregate over incomplete data — which is never reported as a failure or
    a pass)."""
    fields = set(re.findall(r"\.aggregates\.([A-Za-z0-9_]+)", predicate))
    aggregates = results.get("aggregates") if isinstance(results, dict) else None
    aggregates = aggregates if isinstance(aggregates, dict) else {}
    if fields and any(aggregates.get(field) is None for field in fields):
        return None
    return bool(evaluate(predicate, results))


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    def unique_keys(pairs):
        keys = [key for key, _ in pairs]
        duplicates = sorted({key for key in keys if keys.count(key) > 1})
        if duplicates:
            raise ValueError(f"duplicate keys {duplicates} (a hidden second entry)")
        return dict(pairs)

    with open(sys.argv[1], encoding="utf-8") as source:
        results = json.load(source, object_pairs_hook=unique_keys)
    if not isinstance(results, dict):
        raise ValueError("results must be an object")
    gates_path = sys.argv[2] if len(sys.argv) > 2 else str(Path(__file__).parent / "gates.json")
    with open(gates_path, encoding="utf-8") as source:
        gates = json.load(source)
    problems = measurement_issues(results.get("aggregates")) or table_issues(results)
    if problems:
        raise ValueError("; ".join(problems))
    results = recomputed_view(results)
    if not evidence_eligible(results, gates["eligibility"]):
        p = results.get("provenance", {})
        print(f"INELIGIBLE run (load_status={p.get('load_status')}, dirty={p.get('git_dirty')}, "
              f"mismatches={results.get('aggregates', {}).get('mismatch_count')}, "
              f"headline_eligible={results.get('headline_eligible')}; harness reasons: "
              f"{'; '.join(results.get('ineligible_reasons') or []) or 'none stamped'}) "
              "— verdicts below are informational only:")
        eligible = False
    else:
        print("run is ELIGIBLE (quiet, clean tree, default gates, 0 MISMATCH)")
        eligible = True
    for name, g in gates["gates"].items():
        verdict = gate_verdict(g["predicate"], results)
        mark = {True: "PASS", False: "fail", None: "unmeasured"}[verdict]
        print(f"  {mark:<10}  {name}  — {g['description']}")
    sys.exit(0 if eligible else 2)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"check_gates: invalid input or predicate: {error}", file=sys.stderr)
        sys.exit(2)
