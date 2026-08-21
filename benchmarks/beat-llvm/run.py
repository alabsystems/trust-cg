#!/usr/bin/env python3
"""benchmarks/beat-llvm/run.py — THE authoritative dual-lane benchmark harness (BENCH-2).

Contract: metrics-contract.md (normative). Gate predicates:
benchmarks/beat-llvm/contract/gates.json. Any performance number cited in a
done-criterion must come from a results JSON emitted by this harness, with the
full provenance stamp. Numbers without stamps are not evidence.

Lanes per program:
  llvm_o0 / llvm_o2 / llvm_o3 : pinned nightly rustc, -Cpanic=abort, compile wall
                                (median-of-N); llvm_o3 also runs (runtime baseline).
  bridge                      : same rustc + -Zcodegen-backend=<trust-cg dylib>,
                                default env (certs+solver+cache ON), WARM lane
                                (1 unmeasured warmup compile populates the dde503a
                                verdict cache, then median-of-N measured compiles).
  bridge_cold (--cold)        : fresh empty TCG_PROOF_CACHE_DIR per measured compile.

Verdicts: MATCH (exit codes equal) | MISMATCH (P0 stop-the-line: quarantined,
exit 1) | INCOMPLETE (bridge fail-closed; stays in the coverage denominator).

Corpus: progs/manifest.json is the source of truth (category, pinned LLVM-lane
expected_exit, informational expected_bridge). Coverage% is a first-class output
(overall + per category, intent-to-treat: INCOMPLETE rows in the denominator).

BENCH-8 nondeterminism labeling: the ay solver deadline is wall-clock, so machine
load can flip a bridge compile from MATCH to fail-closed. A bridge-lane compile
failure is labeled NONDET-CANDIDATE and retried once:
  retry succeeds            -> label NONDET-FAILCLOSED (still INCOMPLETE, loud;
                               never upgraded to MATCH without a clean quiet pass)
  retry fails, quiet machine-> genuine INCOMPLETE (deterministic fail-closed)
  retry fails, LOADED       -> label NONDET-CANDIDATE (rejection under load is not
                               a valid completeness datum; rerun on a quiet machine)

Exit codes: 0 ok, 1 MISMATCH (or nondeterministic exit), 2 tooling/environment
(loaded machine without --allow-loaded, missing dylib, unresolvable git SHA,
LLVM-lane failure).
"""

import argparse
import hashlib
import shutil
import json
import math
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

SCHEMA = "trust-cg-bench-v1"
TOOLCHAIN = "nightly-2026-04-20"
HERE = Path(__file__).resolve().parent
REPO_DEFAULT = HERE.parent.parent
# Bridge dylib candidates, in preference order when mtimes tie. The CANONICAL
# build convention is
#   cd crates/rustc-codegen-trust-cg && CARGO_TARGET_DIR=target-bridge cargo build --release
# but several older recipes wrote elsewhere, so multiple stale copies coexist on
# a long-lived dev box (2026-07-25: five paths spanning four days). Defaulting to
# a fixed path silently measured a backend days older than the tree. Resolve to
# the NEWEST existing candidate instead, and stamp/verify freshness below.
DYLIB_CANDIDATES = (
    "crates/rustc-codegen-trust-cg/target-bridge/release/librustc_codegen_trust_cg.dylib",
    "target-bridge/release/librustc_codegen_trust_cg.dylib",
    "crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib",
)
DYLIB_REL = DYLIB_CANDIDATES[0]


def newest_dylib(repo):
    """Newest existing bridge dylib among the known build locations, else None."""
    found = [repo / rel for rel in DYLIB_CANDIDATES if (repo / rel).is_file()]
    return max(found, key=lambda p: p.stat().st_mtime) if found else None


def stale_backend_source(repo, dylib):
    """A backend source file newer than the dylib, or None if the dylib is current."""
    mtime = dylib.stat().st_mtime
    for src in (repo / "crates").rglob("*.rs"):
        path = str(src)
        if "/target" in path:
            continue
        # A crate's own TEST / BENCH / EXAMPLE sources are not compiled into the
        # cdylib the harness measures, so they cannot make it stale. Editing one
        # (which happens constantly while gating) previously blocked every
        # measurement with a FALSE staleness report, whose only workaround is
        # `--allow-stale-dylib` — the flag that stamps the row NOT EVIDENCE. The
        # guard must stay tight on things that DO affect the dylib and silent on
        # things that cannot, or it trains you to reach for the override.
        if any(f"/{d}/" in path for d in ("tests", "benches", "examples")):
            continue
        try:
            if src.stat().st_mtime > mtime:
                return src
        except OSError:
            continue
    return None

def _ps_time_to_seconds(s):
    """Parse ps ELAPSED/TIME fields: [[dd-]hh:]mm:ss."""
    s = s.strip()
    days = 0
    if "-" in s:
        d, _, s = s.partition("-")
        days = int(d)
    parts = [float(p) for p in s.split(":")]
    while len(parts) < 3:
        parts.insert(0, 0.0)
    return days * 86400 + parts[0] * 3600 + parts[1] * 60 + parts[2]


# Total CPU time is NOT the discriminator — on a box with 45 days of uptime the
# ordinary macOS daemons have each accumulated tens of CPU-hours, and a rule
# that flags them fires on every run and trains the reader to ignore it.
#
# DUTY CYCLE is the discriminator. A runaway busy-loop consumes ~100% of a core
# for its entire life; a daemon consumes a few percent:
#
#     leaked solver fixture   21019s CPU / 21220s elapsed = 99.1%
#     leaked bench binary    1552008s / 1580247s          = 98.2%
#     iTerm2                  351720s / 3956400s          =  8.9%
#     biomesyncd              230760s / 3956400s          =  5.8%
#
# So: sustained at least half a core for its whole lifetime, for at least half
# an hour, having burned at least 20 CPU-minutes.
#
# The elapsed floor is deliberately NOT generous. This check runs before the
# harness does any work of its own, and for a MEASUREMENT precondition a
# legitimate half-hour CPU hog invalidates the run exactly as thoroughly as an
# illegitimate one — so "is it supposed to be there?" is the wrong question.
# A one-hour floor let a leaked fixture that had only been spinning 59 minutes
# pass unreported.
RUNAWAY_CPU_SECONDS = 20 * 60
RUNAWAY_ELAPSED_SECONDS = 30 * 60
RUNAWAY_MIN_DUTY_CYCLE = 0.5


def detect_runaways():
    """Processes that have been burning CPU far too long to be legitimate work.

    Why this exists: `loadavg` alone is unactionable. On 2026-08-07 this box was
    reporting load 6-10 on four physical cores and the harness dutifully stamped
    every run `LOADED`, which reads as ambient contention. It was not ambient —
    two orphaned benchmark binaries leaked by a session on 2026-07-20 had each
    been spinning for **18 days** (~430 CPU-hours apiece), plus a leaked solver
    fixture. Half the machine had been stolen for weeks, and because the only
    signal was a load number that looks like normal contention, every runtime
    measurement taken in that window was quietly wrong rather than visibly
    failed — including a documented "noise floor" that was really the floor of a
    box at 50% capacity.

    A measurement-integrity defect that degrades results silently is worse than
    one that fails loudly, so this names the specific PIDs and makes the run
    ineligible as evidence.
    """
    try:
        out = subprocess.run(["ps", "-eo", "pid,etime,time,comm"],
                             capture_output=True, text=True, timeout=20)
    except Exception:
        return []
    me = os.getpid()
    found = []
    for line in (out.stdout or "").splitlines()[1:]:
        parts = line.split(None, 3)
        if len(parts) < 4:
            continue
        pid_s, elapsed_s, cpu_s, comm = parts
        try:
            pid, elapsed, cpu = int(pid_s), _ps_time_to_seconds(elapsed_s), _ps_time_to_seconds(cpu_s)
        except (ValueError, IndexError):
            continue
        if pid == me or cpu < RUNAWAY_CPU_SECONDS or elapsed < RUNAWAY_ELAPSED_SECONDS:
            continue
        duty = cpu / elapsed if elapsed > 0 else 0.0
        if duty < RUNAWAY_MIN_DUTY_CYCLE:
            continue
        found.append({"pid": pid, "comm": comm.strip(),
                      "elapsed_s": round(elapsed), "cpu_s": round(cpu),
                      "cpu_hours": round(cpu / 3600, 1), "duty_cycle": round(duty, 3)})
    found.sort(key=lambda r: -r["cpu_s"])
    return found


def _tool_version(cmd):
    """First line of a toolchain version banner, or "" if unavailable."""
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=20)
    except Exception:
        return ""
    text = (out.stdout or "") + (out.stderr or "")
    return text.strip().splitlines()[0].strip() if text.strip() else ""


def _os_description():
    """OS name + release, as the contract's Platform row requires."""
    try:
        out = subprocess.run(["uname", "-srm"], capture_output=True, text=True, timeout=10)
        if out.returncode == 0 and out.stdout.strip():
            return out.stdout.strip()
    except Exception:
        pass
    return f"{platform.system()} {platform.release()} {platform.machine()}".strip()


COMPILE_TIMEOUT = 900
RUN_TIMEOUT = 300


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# Thresholds for the non-gating `runtime_geomean_reliable_only` aggregate: a row
# counts as resolvable when the LLVM baseline runs at least this long AND
# neither lane's observed spread exceeds this fraction of its median.
RELIABLE_MIN_S = 0.05
RELIABLE_SPREAD_MAX = 0.25


def geomean(xs):
    xs = [x for x in xs if x is not None and x > 0]
    if not xs:
        return None
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def run(cmd, env=None, timeout=None, capture=True):
    return subprocess.run(cmd, capture_output=capture, text=True, env=env, timeout=timeout)


def parse_perf_stats(text):
    """Parse the `TCG_PERF_STATS ...` attribution lines the bridge emits under
    `TCG_PERF_STATS=1` (STEP 0) into a list of `{key: value}` dicts. Numeric
    values are coerced to int; everything else stays a string. Non-matching
    stderr lines are ignored. Inert when the flag is off (no lines emitted)."""
    rows = []
    prefix = "TCG_PERF_STATS "
    for line in text.splitlines():
        line = line.strip()
        if not line.startswith(prefix):
            continue
        kv = {}
        for tok in line[len(prefix):].split():
            if "=" not in tok:
                continue
            k, v = tok.split("=", 1)
            try:
                kv[k] = int(v)
            except ValueError:
                kv[k] = v
        if kv:
            rows.append(kv)
    return rows


class Harness:
    def __init__(self, args):
        self.args = args
        self.repo = Path(args.repo).resolve()
        self.env = dict(os.environ)
        self.env["PATH"] = os.path.expanduser("~/.cargo/bin") + ":" + self.env.get("PATH", "")
        self.env["MACOSX_DEPLOYMENT_TARGET"] = self.env.get("MACOSX_DEPLOYMENT_TARGET", "13.0")
        self.dylib = (Path(args.dylib) if args.dylib
                      else (newest_dylib(self.repo) or self.repo / DYLIB_REL))
        self.workdir = Path(tempfile.mkdtemp(prefix="beatllvm-"))
        self.rustc = self.resolve_rustc()
        self.manifest = self.load_manifest()
        self.load_threshold = None  # set in provenance()

    def manifest_digest(self):
        """SHA-256 of the corpus manifest — the contract's Corpus row."""
        mpath = HERE / "progs" / "manifest.json"
        try:
            return hashlib.sha256(mpath.read_bytes()).hexdigest()
        except OSError:
            return ""

    def load_manifest(self):
        """progs/manifest.json is the corpus source of truth (BENCH-3): every .rs must
        have a manifest row and vice versa — a drifted corpus is a tooling error."""
        mpath = HERE / "progs" / "manifest.json"
        try:
            manifest = json.load(open(mpath))["programs"]
        except (OSError, KeyError, json.JSONDecodeError) as e:
            self.die(2, f"corpus manifest unreadable: {mpath}: {e}")
        on_disk = {p.stem for p in (HERE / "progs").glob("*.rs")}
        missing_rows = on_disk - set(manifest)
        missing_files = set(manifest) - on_disk
        if missing_rows or missing_files:
            self.die(2, f"corpus/manifest drift: .rs without manifest row: {sorted(missing_rows)}; "
                        f"manifest row without .rs: {sorted(missing_files)} (update progs/manifest.json)")
        return manifest

    # ---------- provenance ----------
    def resolve_rustc(self):
        r = run(["rustup", "which", "--toolchain", TOOLCHAIN, "rustc"], env=self.env)
        if r.returncode != 0:
            self.die(2, f"cannot resolve rustc for {TOOLCHAIN}: {r.stderr.strip()}")
        return r.stdout.strip()

    def die(self, code, msg):
        print(f"beat-llvm: FATAL: {msg}", file=sys.stderr)
        sys.exit(code)

    def git(self, *a):
        r = run(["git", "-C", str(self.repo), *a])
        if r.returncode != 0:
            self.die(2, f"git {' '.join(a)} failed: {r.stderr.strip()} (fail-closed: no results without provenance)")
        return r.stdout

    def cache_dir(self):
        if "TCG_PROOF_CACHE_DIR" in os.environ:
            return Path(os.environ["TCG_PROOF_CACHE_DIR"])
        return Path(os.path.expanduser("~/.cache/trust-cg/proof-cache"))

    def cache_fingerprint(self):
        d = self.cache_dir()
        try:
            names = sorted(p.name for p in d.iterdir() if p.name.endswith(".verdict"))
        except OSError:
            names = []
        fp = hashlib.sha256("\n".join(names).encode()).hexdigest()
        return {"dir": str(d), "verdict_count": len(names), "fingerprint_sha256": fp}

    def provenance(self):
        sha = self.git("rev-parse", "HEAD").strip()
        porcelain = self.git("status", "--porcelain")
        lines = [l for l in porcelain.splitlines() if l.strip()]
        untracked = sum(1 for l in lines if l.startswith("??"))
        dirty = any(not l.startswith("??") for l in lines)
        diff = run(["git", "-C", str(self.repo), "diff", "HEAD"]).stdout
        if not self.dylib.is_file():
            self.die(2, f"bridge dylib missing: {self.dylib} (fail-closed: refusing to measure a phantom backend)")
        # A dylib older than the backend sources measures code that is not in the
        # tree. That is the same class of error as a missing dylib -- it yields
        # plausible numbers attributed to the wrong commit -- so fail closed too.
        stale_src = stale_backend_source(self.repo, self.dylib)
        if stale_src is not None and not self.args.allow_stale_dylib:
            self.die(2, f"bridge dylib is STALE: {self.dylib}\n"
                        f"  {stale_src} is newer. Rebuild:\n"
                        f"  (cd {self.repo}/crates/rustc-codegen-trust-cg && "
                        f"CARGO_TARGET_DIR=target-bridge cargo build --release)\n"
                        f"  Refusing (measuring a stale backend attributes results to the wrong tree). "
                        f"Use --allow-stale-dylib to override; the row is NOT evidence.")
        rustc_v = run([self.rustc, "--version"], env=self.env).stdout.strip()
        ncpu = os.cpu_count() or 1
        load1 = os.getloadavg()[0]
        thr = self.args.load_threshold if self.args.load_threshold is not None else ncpu / 2.0
        self.load_threshold = thr
        model = run(["sysctl", "-n", "hw.model"]).stdout.strip() or platform.node()
        runaways = detect_runaways()
        if runaways:
            print("beat-llvm: WARNING: runaway processes are stealing this box — "
                  "row is NOT evidence. Kill them and re-run:", file=sys.stderr)
            for r in runaways:
                print(f"  pid {r['pid']:>7}  {r['cpu_hours']:>7.1f} CPU-hours "
                      f"at {r['duty_cycle'] * 100:.0f}% duty  {r['comm']}", file=sys.stderr)
            print(f"  kill -9 {' '.join(str(r['pid']) for r in runaways)}", file=sys.stderr)
        tcg_env = {k: v for k, v in os.environ.items() if k.startswith("TCG_") or k.startswith("TRUST_CG_")}
        return {
            "schema": SCHEMA,
            "harness": "benchmarks/beat-llvm/run.py",
            "timestamp_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "git_sha": sha,
            "git_dirty": dirty,
            "git_diff_sha256": hashlib.sha256(diff.encode()).hexdigest(),
            "untracked_count": untracked,
            "dylib_path": str(self.dylib),
            "dylib_sha256": sha256_file(self.dylib),
            "dylib_mtime": datetime.fromtimestamp(self.dylib.stat().st_mtime, timezone.utc).isoformat(timespec="seconds"),
            "rustc_version": rustc_v,
            "rustc_path": self.rustc,
            "target": self.args.target,
            "host_arch": platform.machine(),
            "host_model": model,
            "ncpu": ncpu,
            "loadavg_before": round(load1, 2),
            "loadavg_after": None,  # filled at the end
            "load_threshold": round(thr, 2),
            # An operator-supplied --load-threshold can silently make ANY machine
            # look QUIET, which would mint a headline-eligible row on a loaded box.
            # Record the override so eligibility can refuse it; the contract's
            # quiet-machine precondition means ncpu/2, not "whatever was passed".
            "load_threshold_overridden": self.args.load_threshold is not None,
            # ---- metrics-contract.md "Required provenance" ----
            # The contract demands these and states plainly: "Missing required
            # data never defaults to an eligible result." Before this, the
            # harness could stamp headline_eligible: true while omitting the
            # build command, the C/linker toolchain, the OS, the aggregation
            # method and the corpus digest — i.e. publish a row the contract
            # would reject. `provenance_complete` below closes that.
            "dylib_build_command": (
                "cd crates/rustc-codegen-trust-cg && "
                "CARGO_TARGET_DIR=target-bridge cargo build --release"
            ),
            "cc_version": _tool_version(["cc", "--version"]),
            "cc_path": shutil.which("cc") or "",
            "linker_version": _tool_version(["ld", "-v"]),
            "os": _os_description(),
            "aggregation": f"median-of-N per program (compile N={self.args.n_compile}, "
                           f"run N={self.args.n_run} after {1} warmup); raw samples "
                           f"retained per program as times_s",
            "corpus_manifest_sha256": self.manifest_digest(),
            "dylib_stale_override": bool(self.args.allow_stale_dylib and stale_src is not None),
            "quiet": load1 <= thr,  # re-checked at the end
            "load_status": "QUIET" if load1 <= thr else "LOADED",
            # Named culprits, not just a load number — see detect_runaways().
            "runaway_processes": runaways,
            "tcg_env": tcg_env,
            "cache": {"mode": "warm", **self.cache_fingerprint(), "verdict_count_after": None},
            "n_compile": self.args.n_compile,
            "n_run": self.args.n_run,
            "warmup_runs": 1,
        }

    # ---------- lanes ----------
    def compile_cmd(self, src, out, opt, bridge):
        cmd = [self.rustc, "--edition=2021", "--crate-type", "bin",
               "--target", self.args.target, "-Cpanic=abort", f"-Copt-level={opt}",
               "-o", str(out), str(src)]
        if bridge:
            cmd.insert(1, f"-Zcodegen-backend={self.dylib}")
        return cmd

    def compile_once(self, src, out, opt, bridge, extra_env=None):
        env = dict(self.env)
        if extra_env:
            env.update(extra_env)
        t0 = time.monotonic()
        r = subprocess.run(self.compile_cmd(src, out, opt, bridge),
                           capture_output=True, text=True, env=env, timeout=COMPILE_TIMEOUT)
        dt = time.monotonic() - t0
        err = ""
        if r.returncode != 0:
            errl = [l for l in r.stderr.splitlines() if l.startswith("error")]
            err = (errl[0] if errl else r.stderr.strip()[-300:])[:300]
            # The captured message is the first `error` line, truncated. A
            # fail-closed caused by the ay solver's WALL-CLOCK deadline reports
            # "solver timeout" deeper in the failing-roots list, so it is lost by
            # that truncation — and it is precisely the signal that separates
            # "the box was busy" from "this shape is unsupported". Preserve it as
            # a compact marker so both the classifier below and a human reading
            # `err_first` can see it.
            if "solver timeout" in r.stderr or "solver deadline" in r.stderr:
                err = f"{err} [solver timeout]"
        return r.returncode == 0, round(dt, 3), err

    def compile_lane(self, src, out, opt, bridge, n, extra_env=None, warmup=False):
        rec = {"ok": False, "times_s": [], "median_s": None, "err": ""}
        if warmup:
            ok, _, err = self.compile_once(src, out, opt, bridge, extra_env)
            if not ok:
                rec["err"] = err
                return rec
        for _ in range(n):
            ok, dt, err = self.compile_once(src, out, opt, bridge, extra_env)
            if not ok:
                rec["err"] = err
                return rec
            rec["times_s"].append(dt)
        rec["ok"] = True
        rec["median_s"] = round(statistics.median(rec["times_s"]), 3)
        return rec

    def compile_cold(self, src, out, n):
        """True cold: fresh empty TCG_PROOF_CACHE_DIR per measured compile (store cost included)."""
        rec = {"ok": False, "times_s": [], "median_s": None, "err": ""}
        for _ in range(n):
            cold_dir = Path(tempfile.mkdtemp(prefix="beatllvm-coldcache-"))
            ok, dt, err = self.compile_once(src, out, 3, True, {"TCG_PROOF_CACHE_DIR": str(cold_dir)})
            shutil.rmtree(cold_dir, ignore_errors=True)
            if not ok:
                rec["err"] = err
                return rec
            rec["times_s"].append(dt)
        rec["ok"] = True
        rec["median_s"] = round(statistics.median(rec["times_s"]), 3)
        return rec

    def run_bin(self, path):
        t0 = time.monotonic()
        r = subprocess.run([str(path)], capture_output=True, timeout=RUN_TIMEOUT)
        return r.returncode, time.monotonic() - t0

    def runtime_lane(self, path, n):
        code0, _ = self.run_bin(path)  # warmup (unmeasured)
        times = []
        for _ in range(n):
            code, dt = self.run_bin(path)
            if code != code0:
                return {"exit": code0, "nondet_exit": code, "times_s": times, "median_s": None}
            # PRESERVE RAW SAMPLES (contract: "Preserve all raw samples and
            # report the median plus spread"). `round(dt, 3)` quantized every
            # sample to a MILLISECOND — one significant digit for this corpus's
            # shortest programs (v3_popcount's bridge lane runs ~2 ms) — so the
            # runtime metric could not resolve what it measured. Across five
            # headline rows whose binaries were BYTE-IDENTICAL the geomean read
            # 0.793 / 0.828 / 0.795 / 0.846 / 0.768, moved entirely by 2-40 ms
            # programs: h1_vec_push_sum's bridge lane reported 0.008 then 0.017
            # for the SAME machine code. `time.monotonic()` resolves
            # nanoseconds; keep microseconds.
            #
            # The METRIC is unchanged (median of the same N samples, plus
            # spread) — only the precision of the samples it is computed from.
            times.append(round(dt, 6))
        med = round(statistics.median(times), 6)
        spread = round((max(times) - min(times)) / med, 4) if med else None
        return {"exit": code0, "nondet_exit": None, "times_s": times, "median_s": med,
                "rel_spread": spread}

    def compile_peak_rss(self, src, out, opt, bridge, extra_env=None):
        """Peak RSS of the COMPILER PROCESS itself (bytes), via `/usr/bin/time -l`.

        The third axis of the superiority goal. `peak_rss` below measures the
        PRODUCED PROGRAM's memory; this measures what it costs to produce it —
        a distinct claim, and the one the harness previously could not make.

        Run ONCE per lane, deliberately OUTSIDE the timing loop: `/usr/bin/time`
        adds a fork+exec that would perturb the compile-time medians the whole
        contract is built on. Returns None when the wrapper or the compile fails,
        so a missing value is never silently read as zero.
        """
        env = dict(self.env)
        if extra_env:
            env.update(extra_env)
        cmd = ["/usr/bin/time", "-l"] + self.compile_cmd(src, out, opt, bridge)
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, env=env,
                               timeout=COMPILE_TIMEOUT)
        except (OSError, subprocess.TimeoutExpired):
            return None
        if r.returncode != 0:
            return None
        m = re.search(r"(\d+)\s+maximum resident set size", r.stderr)
        return int(m.group(1)) if m else None

    def peak_rss(self, path):
        try:
            r = subprocess.run(["/usr/bin/time", "-l", str(path)],
                               capture_output=True, text=True, timeout=RUN_TIMEOUT)
        except (OSError, subprocess.TimeoutExpired):
            return None
        m = re.search(r"(\d+)\s+maximum resident set size", r.stderr)
        return int(m.group(1)) if m else None

    # ---------- per program ----------
    def check_expected_exit(self, stem, lane_bin):
        """Pinned-exit oracle (BENCH-3): a silent LLVM-side change is a tooling error."""
        expected = self.manifest.get(stem, {}).get("expected_exit")
        if expected is None:
            return None
        code, _ = self.run_bin(lane_bin)
        if code != expected:
            self.die(2, f"{stem}: LLVM -O3 exit {code} != manifest expected_exit {expected} — "
                        f"the LLVM lane or the program changed silently (re-measure and update "
                        f"progs/manifest.json in an explicit commit)")
        return code

    def bench_program(self, src: Path):
        stem = src.stem
        print(f"== {stem}", flush=True)
        mrow = self.manifest.get(stem, {})
        row = {"source": str(src.relative_to(self.repo)),
               "category": mrow.get("category", "scalar"),
               "expected_bridge": mrow.get("expected_bridge"),
               "verdict": None, "reason": "", "label": None,
               "compile": {}, "run": {}, "size_bytes": {},
               "peak_rss_bytes": {}, "compile_peak_rss_bytes": {}, "ratios": {}}
        outs = {}
        # LLVM compile-time baselines -O0/-O2/-O3 (contract section 3)
        for opt in ("0", "2", "3"):
            out = self.workdir / f"{stem}_llvm_o{opt}"
            rec = self.compile_lane(src, out, opt, bridge=False, n=self.args.n_compile)
            if not rec["ok"]:
                self.die(2, f"LLVM lane failed to compile {stem} at -O{opt}: {rec['err']}")
            row["compile"][f"llvm_o{opt}"] = rec
            outs[f"llvm_o{opt}"] = out
        # pinned-exit oracle runs even when the bridge fails closed (full-corpus LLVM check)
        self.check_expected_exit(stem, outs["llvm_o3"])
        # Bridge WARM (default env; warmup populates the dde503a verdict cache)
        bout = self.workdir / f"{stem}_bridge"
        brec = self.compile_lane(src, bout, "3", bridge=True, n=self.args.n_compile, warmup=True)
        row["compile"]["bridge_warm"] = brec
        if self.args.cold:
            row["compile"]["bridge_cold"] = self.compile_cold(src, self.workdir / f"{stem}_bridge_cold",
                                                              self.args.n_compile)
        if not brec["ok"]:
            return self.bridge_failclosed_row(row, src, bout, brec)
        outs["bridge"] = bout
        if row["expected_bridge"] == "INCOMPLETE":
            print(f"   note: {stem} was expected-INCOMPLETE but now compiles — completeness "
                  f"improvement; update progs/manifest.json expected_bridge in an explicit commit",
                  flush=True)
        # sizes
        for lane in ("llvm_o3", "bridge"):
            row["size_bytes"][lane] = outs[lane].stat().st_size
        # runtime medians (warmup + N), llvm -O3 vs bridge
        for lane in ("llvm_o3", "bridge"):
            row["run"][lane] = self.runtime_lane(outs[lane], self.args.n_run)
            if row["run"][lane]["nondet_exit"] is not None:
                row["verdict"] = "MISMATCH"
                row["reason"] = f"nondeterministic exit code in lane {lane}"
                return row
        # peak RSS (dedicated run, not folded into timed medians)
        for lane in ("llvm_o3", "bridge"):
            row["peak_rss_bytes"][lane] = self.peak_rss(outs[lane])
        # COMPILER peak RSS — one extra compile per lane, outside the timing loop.
        row["compile_peak_rss_bytes"]["llvm_o2"] = self.compile_peak_rss(
            src, self.workdir / f"{stem}_rss_llvm_o2", "2", bridge=False)
        row["compile_peak_rss_bytes"]["llvm_o3"] = self.compile_peak_rss(
            src, self.workdir / f"{stem}_rss_llvm_o3", "3", bridge=False)
        row["compile_peak_rss_bytes"]["bridge"] = self.compile_peak_rss(
            src, self.workdir / f"{stem}_rss_bridge", "3", bridge=True)
        # differential oracle (exit codes; full-width checksum folded per contract section 6)
        le, be = row["run"]["llvm_o3"]["exit"], row["run"]["bridge"]["exit"]
        if le != be:
            row["verdict"] = "MISMATCH"
            row["reason"] = f"exit codes differ: llvm_o3={le} bridge={be}"
            return row
        row["verdict"] = "MATCH"
        # ratios (bridge / llvm)
        r = row["ratios"]
        lrt, brt = row["run"]["llvm_o3"]["median_s"], row["run"]["bridge"]["median_s"]
        r["runtime_vs_llvm_o3"] = round(brt / lrt, 3) if lrt else None
        for opt in ("0", "2", "3"):
            l = row["compile"][f"llvm_o{opt}"]["median_s"]
            r[f"compile_warm_vs_llvm_o{opt}"] = round(brec["median_s"] / l, 3) if l else None
            if self.args.cold and row["compile"].get("bridge_cold", {}).get("ok"):
                r[f"compile_cold_vs_llvm_o{opt}"] = round(row["compile"]["bridge_cold"]["median_s"] / l, 3) if l else None
        r["size_vs_llvm_o3"] = round(row["size_bytes"]["bridge"] / row["size_bytes"]["llvm_o3"], 3)
        lr, br = row["peak_rss_bytes"]["llvm_o3"], row["peak_rss_bytes"]["bridge"]
        r["rss_vs_llvm_o3"] = round(br / lr, 3) if (lr and br) else None
        crss = row["compile_peak_rss_bytes"]
        for opt in ("2", "3"):
            lc, bc = crss.get(f"llvm_o{opt}"), crss.get("bridge")
            r[f"compile_rss_vs_llvm_o{opt}"] = round(bc / lc, 3) if (lc and bc) else None
        return row

    def bridge_failclosed_row(self, row, src, bout, brec):
        """BENCH-8 retry-on-quiet labeling (contract section 7). The ay solver deadline is
        wall-clock (ay_bridge.rs `Instant::now() + timeout`), so load can flip a compile
        verdict from success to fail-closed. Every bridge fail-closed is a NONDET-CANDIDATE
        and is retried ONCE; only a quiet-machine rejection counts as a genuine
        (deterministic) INCOMPLETE. A row whose retry succeeds is labeled NONDET-FAILCLOSED
        and STAYS INCOMPLETE — never upgraded to MATCH without a clean quiet-machine pass."""
        err = brec["err"] or "bridge fail-closed (empty reason = possible ICE)"
        row["verdict"] = "INCOMPLETE"
        thr = self.load_threshold or ((os.cpu_count() or 1) / 2.0)
        load_at_fail = round(os.getloadavg()[0], 2)
        print(f"   bridge fail-closed (load {load_at_fail}, threshold {thr}) — "
              f"NONDET-CANDIDATE, retrying once…", flush=True)
        ok, _, retry_err = self.compile_once(src, bout, "3", bridge=True)
        load_at_retry = round(os.getloadavg()[0], 2)
        quiet_both = load_at_fail <= thr and load_at_retry <= thr
        # Retain BOTH error texts. Without them a NONDET-CANDIDATE row is
        # unfalsifiable after the fact: you cannot tell a load-induced solver flap
        # from a deterministic completeness gap wearing the same banner. Identical
        # texts are NOT on their own proof of determinism (a solver deadline on the
        # same function repeats its message), so this deliberately does not change
        # the label — it just makes the question answerable from the artifact, and
        # tells a reader which single program to recompile on a quiet box.
        # A SOLVER TIMEOUT is knowably load-sensitive: the ay deadline is
        # wall-clock, so a busy box expires it on an obligation a quiet box
        # discharges. That is a stronger signal than `err_identical`, which
        # cannot tell a repeated timeout from a real coverage gap — a timeout
        # reproduces its own message every time. Record it explicitly so a reader
        # (or a later triage pass) can separate "ran out of wall clock" from
        # "this shape is genuinely unsupported" without re-deriving it.
        both_err = f"{err}\n{retry_err or ''}"
        is_timeout = "solver timeout" in both_err or "solver deadline" in both_err
        row["nondet"] = {"loadavg_at_fail": load_at_fail, "loadavg_at_retry": load_at_retry,
                         "load_threshold": thr, "retry_ok": ok,
                         "err_first": err, "err_retry": retry_err or "",
                         "err_identical": (retry_err or "") == err,
                         "err_is_solver_timeout": is_timeout}
        # NOTE: do NOT assume any fail-closed banner is load-insensitive — the BENCH-8
        # sentinel observed a live [TCG-MIR-UNSUPPORTED] flap under load (2026-07-02,
        # 4 OK / 1 fail-closed on identical pinned source). Only the manifest's
        # expected-INCOMPLETE prior (a known completeness gap) or a quiet machine may
        # downgrade a rejection to a genuine INCOMPLETE datum.
        expected_inc = row.get("expected_bridge") == "INCOMPLETE"
        if ok:
            row["label"] = "NONDET-FAILCLOSED"
            row["reason"] = (f"NONDET-FAILCLOSED: bridge fail-closed then retry SUCCEEDED "
                             f"(load {load_at_fail}->{load_at_retry}); counted INCOMPLETE — "
                             f"needs a clean quiet-machine pass to count as MATCH. first error: {err}")
            print(f"   *** NONDET-FAILCLOSED: retry succeeded — load-sensitive solver verdict "
                  f"(ay wall-clock deadline class). Row stays INCOMPLETE. ***", flush=True)
        elif quiet_both or expected_inc:
            why = "quiet machine" if quiet_both else "expected-INCOMPLETE per manifest"
            row["reason"] = f"bridge fail-closed ({why}): {err}"
        else:
            row["label"] = "NONDET-CANDIDATE"
            if is_timeout:
                failure_detail = (
                    "; the failure is a SOLVER TIMEOUT (wall-clock deadline), which is "
                    "load-sensitive by construction — NOT evidence of a coverage gap"
                )
            elif (retry_err or "") == err:
                failure_detail = (
                    "; both attempts reported the IDENTICAL error, so a deterministic "
                    "completeness gap is the leading hypothesis"
                )
            else:
                failure_detail = ""
            row["reason"] = (f"NONDET-CANDIDATE: fail-closed twice under load "
                             f"(load {load_at_fail}->{load_at_retry} > {thr}); rejection under load "
                             f"is not a valid completeness datum — rerun on a quiet machine"
                             f"{failure_detail}. "
                             f"error: {retry_err or err}")
        return row

    # ---------- aggregation / emission ----------
    def aggregates(self, programs):
        match = {k: v for k, v in programs.items() if v["verdict"] == "MATCH"}
        agg = {
            "total_programs": len(programs),
            "match_count": len(match),
            "incomplete_count": sum(1 for v in programs.values() if v["verdict"] == "INCOMPLETE"),
            "mismatch_count": sum(1 for v in programs.values() if v["verdict"] == "MISMATCH"),
            # BENCH-8 labels: NONDET-FAILCLOSED = fail-closed whose immediate retry succeeded
            # (load-sensitive solver verdict, still INCOMPLETE); NONDET-CANDIDATE = fail-closed
            # twice under load (not a valid completeness datum; rerun quiet).
            "nondet_failclosed_count": sum(1 for v in programs.values() if v.get("label") == "NONDET-FAILCLOSED"),
            "nondet_candidate_count": sum(1 for v in programs.values() if v.get("label") == "NONDET-CANDIDATE"),
            "coverage_pct": round(100.0 * len(match) / len(programs), 1) if programs else 0.0,
        }
        agg["runtime_geomean_vs_llvm_o3"] = rnd(geomean([v["ratios"].get("runtime_vs_llvm_o3") for v in match.values()]))

        # ADDITIONAL, NON-GATING aggregate: the same geomean restricted to rows
        # whose measurement is actually resolvable.
        #
        # The full-corpus runtime geomean is dominated by programs that run for
        # a few milliseconds, where run-to-run variance swamps any real
        # difference. Measured on a quiet box (load 0.27), the SAME row reports:
        #
        #   all 18 programs                    0.843x
        #   rel_spread <= 0.25  (14 programs)  0.913x
        #   llvm median >= 50 ms (9 programs)  0.973x
        #
        # `v3_popcount` is the clearest case: ratio 0.245 off an LLVM lane whose
        # own rel_spread is 2.345 — the BASELINE varies by 234%, so that ratio
        # is not a measurement of anything, yet it alone moves the 18-program
        # geomean by roughly 7%.
        #
        # This does NOT replace or alter `runtime_geomean_vs_llvm_o3` (the gate
        # basis, contract section 10) — it is published beside it so a reader can
        # see how much of the headline rests on rows the harness itself reports
        # as unstable. `RELIABLE_SPREAD_MAX` and `RELIABLE_MIN_S` are the two
        # knobs; both are conservative.
        reliable = [
            v for v in match.values()
            if (v.get("run", {}).get("llvm_o3", {}).get("median_s") or 0) >= RELIABLE_MIN_S
            and max(
                v.get("run", {}).get("llvm_o3", {}).get("rel_spread") or 0.0,
                v.get("run", {}).get("bridge", {}).get("rel_spread") or 0.0,
            ) <= RELIABLE_SPREAD_MAX
        ]
        agg["runtime_geomean_reliable_only"] = rnd(
            geomean([v["ratios"].get("runtime_vs_llvm_o3") for v in reliable])
        )
        agg["runtime_reliable_program_count"] = len(reliable)
        agg["runtime_reliable_criteria"] = {
            "min_llvm_median_s": RELIABLE_MIN_S,
            "max_rel_spread": RELIABLE_SPREAD_MAX,
        }
        worst = [v["ratios"].get("runtime_vs_llvm_o3") for v in match.values() if v["ratios"].get("runtime_vs_llvm_o3")]
        agg["runtime_worst_vs_llvm_o3"] = max(worst) if worst else None
        # scalar-category geomean is the G1a basis (contract section 10) now that the corpus
        # spans categories; the full-corpus geomean above is the G1c/GATE-SB basis.
        agg["scalar_runtime_geomean_vs_llvm_o3"] = rnd(geomean(
            [v["ratios"].get("runtime_vs_llvm_o3") for v in match.values() if v.get("category") == "scalar"]))
        vec = [v["ratios"].get("runtime_vs_llvm_o3") for v in match.values()
               if v.get("category") == "vectorizable" and v["ratios"].get("runtime_vs_llvm_o3")]
        agg["vectorizable_worst_runtime_vs_llvm_o3"] = max(vec) if vec else None
        # coverage per category — first-class intent-to-treat output (contract section 7)
        cats = {}
        for v in programs.values():
            c = cats.setdefault(v.get("category", "scalar"),
                                {"total": 0, "match": 0, "incomplete": 0, "mismatch": 0})
            c["total"] += 1
            key = {"MATCH": "match", "INCOMPLETE": "incomplete", "MISMATCH": "mismatch"}.get(v["verdict"])
            if key:
                c[key] += 1
        for cname, c in cats.items():
            c["coverage_pct"] = round(100.0 * c["match"] / c["total"], 1) if c["total"] else 0.0
            c["runtime_geomean_vs_llvm_o3"] = rnd(geomean(
                [v["ratios"].get("runtime_vs_llvm_o3") for v in match.values() if v.get("category") == cname]))
        agg["by_category"] = {k: cats[k] for k in sorted(cats)}
        for opt in ("0", "2", "3"):
            agg[f"compile_warm_geomean_vs_llvm_o{opt}"] = rnd(geomean(
                [v["ratios"].get(f"compile_warm_vs_llvm_o{opt}") for v in match.values()]))
            agg[f"compile_cold_geomean_vs_llvm_o{opt}"] = rnd(geomean(
                [v["ratios"].get(f"compile_cold_vs_llvm_o{opt}") for v in match.values()]))
        agg["size_geomean_vs_llvm_o3"] = rnd(geomean([v["ratios"].get("size_vs_llvm_o3") for v in match.values()]))
        agg["rss_geomean_vs_llvm_o3"] = rnd(geomean([v["ratios"].get("rss_vs_llvm_o3") for v in match.values()]))
        for opt in ("2", "3"):
            agg[f"compile_rss_geomean_vs_llvm_o{opt}"] = rnd(geomean(
                [v["ratios"].get(f"compile_rss_vs_llvm_o{opt}") for v in match.values()]))
        return agg

    def markdown(self, res):
        p, a = res["provenance"], res["aggregates"]
        lines = [
            f"# beat-llvm results — {p['git_sha'][:12]}{'-dirty' if p['git_dirty'] else ''} "
            f"({p['timestamp_utc']}, {p['host_arch']}, {p['load_status']})",
            "",
            f"- dylib sha256 `{p['dylib_sha256'][:16]}…`  rustc `{p['rustc_version']}`  target `{p['target']}`",
            f"- load {p['loadavg_before']}→{p['loadavg_after']} (threshold {p['load_threshold']}, "
            f"quiet={p['quiet']})  cache: {p['cache']['mode']}, {p['cache']['verdict_count']}→"
            f"{p['cache']['verdict_count_after']} verdicts  N: compile={p['n_compile']} run={p['n_run']}",
            f"- TCG env: `{p['tcg_env'] or '{} (production defaults)'}`",
            f"- **headline-eligible: {res['headline_eligible']}**"
            + ("" if res["headline_eligible"] else "  (LOADED / runaway procs / dirty / non-default env or N — NOT evidence for gates)"),
            "",
            f"**coverage {a['coverage_pct']}% ({a['match_count']}/{a['total_programs']} MATCH, "
            f"{a['incomplete_count']} INCOMPLETE, {a['mismatch_count']} MISMATCH; "
            f"nondet: {a['nondet_failclosed_count']} NONDET-FAILCLOSED, "
            f"{a.get('nondet_candidate_count', 0)} NONDET-CANDIDATE)** — "
            f"runtime geomean vs LLVM -O3: **{a['runtime_geomean_vs_llvm_o3']}x** "
            f"[resolvable-rows-only: **{a.get('runtime_geomean_reliable_only')}x** over "
            f"{a.get('runtime_reliable_program_count')} programs with llvm median >= "
            f"{RELIABLE_MIN_S}s and rel_spread <= {RELIABLE_SPREAD_MAX}] "
            f"(scalar {a.get('scalar_runtime_geomean_vs_llvm_o3')}x, "
            f"worst {a['runtime_worst_vs_llvm_o3']}x); compile warm geomean vs -O2: "
            f"**{a['compile_warm_geomean_vs_llvm_o2']}x** (vs -O3: {a['compile_warm_geomean_vs_llvm_o3']}x)",
            "",
            "coverage by category (intent-to-treat — INCOMPLETE rows stay in the denominator):",
            "",
            "| category | coverage % | match/total | incomplete | runtime geomean x |",
            "|---|---|---|---|---|",
        ]
        for cname, c in a.get("by_category", {}).items():
            lines.append(f"| {cname} | {c['coverage_pct']}% | {c['match']}/{c['total']} "
                         f"| {c['incomplete']} | {c.get('runtime_geomean_vs_llvm_o3') or '—'} |")
        lines += [
            "",
            "| program | cat | verdict | run llvm-O3 (s) | run bridge (s) | runtime x | compile -O2 (s) | compile -O3 (s) | bridge warm (s) | warm x(-O2) | size x | rss x |",
            "|---|---|---|---|---|---|---|---|---|---|---|---|",
        ]
        for name, v in res["programs"].items():
            c, r, rt = v["compile"], v["ratios"], v["run"]
            def g(d, *ks):
                for k in ks:
                    d = d.get(k) if isinstance(d, dict) else None
                    if d is None:
                        return "—"
                # Display only: the JSON keeps microsecond precision (the
                # contract's "preserve all raw samples"), but a table of
                # 0.008341 is unreadable. 4 decimals = 0.1 ms, which is enough
                # to distinguish this corpus's short programs — the whole point
                # of preserving the samples in the first place.
                if isinstance(d, float):
                    return f"{d:.4f}".rstrip("0").rstrip(".") or "0"
                return d
            lines.append(
                f"| {name} | {v.get('category', 'scalar')} "
                f"| {v['verdict']}{' — ' + v['reason'] if v['verdict'] != 'MATCH' else ''} "
                f"| {g(rt,'llvm_o3','median_s')} | {g(rt,'bridge','median_s')} "
                f"| {r.get('runtime_vs_llvm_o3','—')} | {g(c,'llvm_o2','median_s')} "
                f"| {g(c,'llvm_o3','median_s')} | {g(c,'bridge_warm','median_s')} "
                f"| {r.get('compile_warm_vs_llvm_o2','—')} | {r.get('size_vs_llvm_o3','—')} "
                f"| {r.get('rss_vs_llvm_o3','—')} |")
        lines.append("")
        lines.append("> Output equality = exit codes with a full-width checksum folded in (mod 126); "
                      "a MATCH is probabilistic (collision caveat, contract section 6); a MISMATCH is definitive P0.")
        return "\n".join(lines)

    def attribution_report(self, srcs):
        """STEP 0: compile each program through the bridge with TCG_PERF_STATS=1
        and print the per-innermost-loop isel-vs-regalloc instruction mix. This
        is instruction-COUNT attribution (load-independent), so it runs without
        the quiet-box gate and does no timing."""
        if not self.dylib.is_file():
            self.die(2, f"bridge dylib missing: {self.dylib}")
        print("# x86 per-loop isel/optimizer/regalloc attribution "
              "(TCG_PERF_STATS=1, bridge, -Copt-level=3)")
        print(f"# dylib {self.dylib}\n")
        for src in srcs:
            out = self.workdir / f"{src.stem}_attrib"
            env = dict(self.env)
            env["TCG_PERF_STATS"] = "1"
            r = subprocess.run(self.compile_cmd(src, out, "3", bridge=True),
                               capture_output=True, text=True, env=env, timeout=COMPILE_TIMEOUT)
            print(f"## {src.stem}")
            if r.returncode != 0:
                errl = [l for l in r.stderr.splitlines() if l.startswith("error")]
                print(f"   bridge compile FAILED (fail-closed) rc={r.returncode}: "
                      f"{(errl[0] if errl else '')[:200]}\n")
                continue
            rows = parse_perf_stats(r.stderr)
            loop_rows = [kv for kv in rows
                         if kv.get("stage") in ("post_opt", "post_regalloc")
                         and kv.get("loop") not in (None, "none")]
            if not loop_rows:
                print("   (no innermost loop detected in any function)\n")
                continue
            for kv in loop_rows:
                print(f"   {str(kv.get('stage')):<14} fn={kv.get('fn')} loop={kv.get('loop')} "
                      f"insts={kv.get('insts')} loads={kv.get('loads')} stores={kv.get('stores')} "
                      f"movrr={kv.get('movrr')} sib_load={kv.get('sib_load')} "
                      f"sib_store={kv.get('sib_store')} lea={kv.get('lea')} "
                      f"load_fold={kv.get('load_fold')} imul_rr={kv.get('imul_rr')} "
                      f"shl_ri={kv.get('shl_ri')}")
            print()

    def main(self):
        if self.args.attribution:
            srcs = sorted((HERE / "progs").glob("*.rs"))
            if self.args.progs:
                want = set(self.args.progs)
                srcs = [s for s in srcs if s.stem in want]
            if not srcs:
                self.die(2, "no programs selected")
            self.attribution_report(srcs)
            return
        prov = self.provenance()
        if not prov["quiet"]:
            msg = (f"1-min load {prov['loadavg_before']} > threshold {prov['load_threshold']} "
                   f"(ncpu/2): machine is LOADED.")
            if not self.args.allow_loaded:
                self.die(2, msg + " Refusing (contract section 8). Use --allow-loaded to run anyway; "
                              "the row will be stamped LOADED and is NOT evidence.")
            print(f"beat-llvm: WARNING: {msg} Stamping LOADED; results are not headline-eligible.",
                  file=sys.stderr)
        srcs = sorted((HERE / "progs").glob("*.rs"))
        if self.args.progs:
            want = set(self.args.progs)
            srcs = [s for s in srcs if s.stem in want]
            missing = want - {s.stem for s in srcs}
            if missing:
                self.die(2, f"unknown programs: {sorted(missing)}")
        if not srcs:
            self.die(2, "no programs selected")
        programs = {}
        for src in srcs:
            programs[src.stem] = self.bench_program(src)
        load_after = os.getloadavg()[0]
        prov["loadavg_after"] = round(load_after, 2)
        prov["quiet"] = prov["quiet"] and load_after <= prov["load_threshold"]
        prov["load_status"] = "QUIET" if prov["quiet"] else "LOADED"
        prov["cache"]["verdict_count_after"] = self.cache_fingerprint()["verdict_count"]
        agg = self.aggregates(programs)
        # metrics-contract.md, "Required provenance": "Missing required data
        # never defaults to an eligible result." Enforce it rather than trusting
        # that every field happened to get stamped — a row that omits the build
        # command, toolchain, OS, aggregation method or corpus digest is not
        # contract-compliant no matter how quiet the machine was.
        required_provenance = (
            "git_sha", "dylib_path", "dylib_sha256", "dylib_mtime",
            "dylib_build_command", "rustc_version", "rustc_path",
            "cc_version", "linker_version", "os", "host_arch", "ncpu",
            "target", "aggregation", "corpus_manifest_sha256",
            "timestamp_utc", "harness",
        )
        missing_provenance = [k for k in required_provenance if not prov.get(k)]
        prov["missing_required_provenance"] = missing_provenance
        prov["provenance_complete"] = not missing_provenance
        if missing_provenance:
            print(
                "beat-llvm: WARNING: missing contract-required provenance "
                f"{missing_provenance} — row is NOT evidence.",
                file=sys.stderr,
            )
        weakening = ("TCG_NO_PROOF_CERTS" in prov["tcg_env"]
                     or prov["tcg_env"].get("TCG_REFINE_SOLVER") == "0"
                     or "TCG_NO_PROOF_CACHE" in prov["tcg_env"])
        res = {
            "schema": SCHEMA,
            "provenance": prov,
            "headline_eligible": bool(prov["quiet"] and not prov["git_dirty"] and not weakening
                                      and not prov["load_threshold_overridden"]
                                      and not prov["dylib_stale_override"]
                                      and not prov["runaway_processes"]
                                      and prov["provenance_complete"]
                                      and agg["mismatch_count"] == 0
                                      and self.args.n_compile >= 3 and self.args.n_run >= 5),
            "programs": programs,
            "aggregates": agg,
        }
        # emit
        outdir = Path(self.args.out_dir) if self.args.out_dir else HERE / "results"
        outdir.mkdir(parents=True, exist_ok=True)
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        base = f"{prov['git_sha'][:12]}{'-dirty' if prov['git_dirty'] else ''}-{stamp}"
        jpath = outdir / f"{base}.json"
        with open(jpath, "w") as f:
            json.dump(res, f, indent=1)
        md = self.markdown(res)
        mpath = outdir / f"{base}.md"
        mpath.write_text(md + "\n")
        print(md)
        print(f"\nresults: {jpath}\n         {mpath}")
        if agg["mismatch_count"] > 0:
            qdir = outdir / "mismatch"
            qdir.mkdir(exist_ok=True)
            shutil.copy(jpath, qdir / jpath.name)
            print(f"beat-llvm: *** MISMATCH — P0 STOP-THE-LINE *** quarantined: {qdir / jpath.name}",
                  file=sys.stderr)
            sys.exit(1)
        sys.exit(0)


def rnd(x):
    return round(x, 3) if x is not None else None


def parse_args():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=str(REPO_DEFAULT), help="repo root (default: two levels up)")
    ap.add_argument("--dylib", default=None, help=f"bridge dylib (default: <repo>/{DYLIB_REL})")
    ap.add_argument("--target", default="x86_64-apple-darwin")
    ap.add_argument("--progs", nargs="*", default=None, help="program stems to run (default: all)")
    ap.add_argument("--cold", action="store_true", help="also measure the bridge COLD lane (fresh cache per compile)")
    ap.add_argument("--n-compile", type=int, default=3, help="compile median-of-N (contract default 3)")
    ap.add_argument("--n-run", type=int, default=5, help="runtime median-of-N after 1 warmup (contract default 5)")
    ap.add_argument("--allow-loaded", action="store_true",
                    help="run even when 1-min load > ncpu/2; row is stamped LOADED (not evidence)")
    ap.add_argument("--load-threshold", type=float, default=None,
                    help="override quiet threshold (default ncpu/2); overriding forfeits headline eligibility")
    ap.add_argument("--allow-stale-dylib", action="store_true",
                    help="measure even when the bridge dylib is older than the backend sources (not evidence)")
    ap.add_argument("--out-dir", default=None, help="results dir (default: benchmarks/beat-llvm/results)")
    ap.add_argument("--attribution", action="store_true",
                    help="STEP 0: emit per-loop isel/optimizer/regalloc instruction "
                         "attribution (TCG_PERF_STATS) for the selected progs, then exit "
                         "(instruction counts only, no timing, no quiet-box gate)")
    return ap.parse_args()


if __name__ == "__main__":
    Harness(parse_args()).main()
