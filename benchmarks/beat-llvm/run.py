#!/usr/bin/env python3
"""benchmarks/beat-llvm/run.py — THE authoritative dual-lane benchmark harness (BENCH-2).

Contract: metrics-contract.md (normative). Gate predicates:
benchmarks/beat-llvm/contract/gates.json. Any performance number cited in a
done-criterion must come from a results JSON emitted by this harness, with the
full provenance stamp. Numbers without stamps are not evidence.

Lanes per program:
  llvm_o0 / llvm_o2 / llvm_o3 : pinned Trust compiler, -Cpanic=abort, compile wall
                                (median-of-N); llvm_o3 also runs (runtime baseline).
  bridge                      : same compiler + -Zcodegen-backend=<trust-cg dylib>,
                                default env (certs+solver+cache ON), WARM lane
                                (1 unmeasured warmup compile populates the dde503a
                                verdict cache, then median-of-N measured compiles).
  bridge_cold (--cold)        : true cold — a fresh, empty, private XDG_CACHE_HOME per
                                measured compile (every persistent trust-cg cache starts
                                empty and population cost is timed). TCG_* variables
                                cannot select it: trustc refuses that environment family.

Driver: the bridge pins channel = "trust", so every lane uses the Trust compiler
that pin names (the backend cannot load into a stock compiler).
scripts/trust_toolchain.py resolves the PATH trustc/targo package, or the package
trustc named by --driver, and refuses the retired stock nightly-2026-04-20 and any
unidentified compiler (exit 2). All lanes compile in Trust's explicit unverified
frontend lane (-Ztrust-verify=off), the same vanilla frontend the harness always
measured; that lane is diagnostic, makes no Trust-verified-compilation claim, and
does not measure the proof-enabled Trust frontend. The exact driver identity
(commit, sysroot, lane) is stamped into provenance.driver.

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
LLVM-lane failure, --pin-core on a host that cannot pin).

Target and backend: every lane compiles for the selected target, by default the
resolved Trust compiler's implicit host (stamped as target_selection). Only a
cross target adds --target, preserving native configuration. The bridge backend
is the newest built librustc_codegen_trust_cg with this host's shared-library
suffix (scripts/bridge_backend.py), or --dylib.

Provenance also names the CPU model and feature summary (hostinfo.py; never a
hostname), the -C target-cpu policy both lanes were given, the core-affinity
policy (--pin-core), and how peak RSS was sampled (peak_rss.py:
getrusage(RUSAGE_CHILDREN) via a single-child wrapper, bytes on every host,
with its floor and /usr/bin/time agreement). --retain-dir copies the run's
evidence into <DIR>/<date>-<rev>/ for committing beside its ledger row.

Aggregates are fail-closed: a geomean or worst-case over MATCH rows is null
unless every covered row has its ratio (the rows lacking one are listed). Size
and peak RSS use contract/check_gates.resource_aggregates, gated by
contract/gates.json version 3, and a run whose size/RSS readings are incomplete
or whose RSS sampler cannot be calibrated is not headline evidence
(`ineligible_reasons` says why a run is not).

Size has two measures. `size_bytes` is the linked file's st_size, which
includes the shared standard library. `emitted_size_bytes` is the emitted-code
size (emitted_size.py holds the definition): each lane's binary is linked once
more, from a fresh private directory, with the system linker's map, and the
code and read-only data bytes the map attributes to the objects that compile
produced are summed. The map-linked image must hold the same section bytes as
the timed compile's binary, or the reading is refused.

Peak RSS (program and compiler) is the median of --n-rss dedicated samples per
lane (contract N = 5, check_gates.RSS_CONTRACT_N), interleaved lane by lane
outside the timed loops; every sample is retained with its sampler status.
"""

import argparse
import atexit
import hashlib
import importlib.util
import shutil
import json
import os
import platform
import re
import shutil
import statistics
import struct
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

# Sibling helper modules resolve from this directory under any loader (a test
# importing run.py by path does not put its directory on sys.path).
sys.path.insert(0, str(Path(__file__).resolve().parent))
import corpus  # noqa: E402
import emitted_size  # noqa: E402
import hostinfo  # noqa: E402
import peak_rss as rss_capture  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent / "contract"))
import check_gates  # noqa: E402  (the one size/RSS aggregation, shared with the ratchet)

# v2 (gates.json version 3): emitted-code size and median-of-N peak RSS; a
# lane's `rss_samples` entry is a list of sample records.
SCHEMA = "trust-cg-bench-v2"
HERE = Path(__file__).resolve().parent
REPO_DEFAULT = HERE.parent.parent
_TRUST_SPEC = importlib.util.spec_from_file_location(
    "trust_cg_trust_toolchain", REPO_DEFAULT / "scripts" / "trust_toolchain.py")
TRUST_TOOLCHAIN = importlib.util.module_from_spec(_TRUST_SPEC)
_TRUST_SPEC.loader.exec_module(TRUST_TOOLCHAIN)
_BACKEND_SPEC = importlib.util.spec_from_file_location(
    "trust_cg_bridge_backend", REPO_DEFAULT / "scripts" / "bridge_backend.py")
BRIDGE_BACKEND = importlib.util.module_from_spec(_BACKEND_SPEC)
_BACKEND_SPEC.loader.exec_module(BRIDGE_BACKEND)
# The proof-tool naming routes the release gates and floors share
# (aterm_toolchain.rs's packaged-prefix rule).
_TOOLS_SPEC = importlib.util.spec_from_file_location(
    "trust_cg_release_gate_summary", REPO_DEFAULT / "scripts" / "release_gate_summary.py")
PROOF_TOOLS = importlib.util.module_from_spec(_TOOLS_SPEC)
_TOOLS_SPEC.loader.exec_module(PROOF_TOOLS)
# The bridge is built by the pinned Trust package in its unverified build lane.
DYLIB_BUILD_COMMAND = ("cd crates/rustc-codegen-trust-cg && CARGO_TARGET_DIR=target-bridge "
                       "RUSTC=<trust-package>/bin/trustc <trust-package>/bin/targo --unverified "
                       "build --release")
# The bridge backend: `librustc_codegen_trust_cg` with this host's shared-library
# suffix (.dylib on Darwin, .so on Linux). scripts/bridge_backend.py owns the
# candidate build locations (the canonical DYLIB_BUILD_COMMAND output in
# target-bridge/release first) and resolves the NEWEST existing one: several
# older recipes wrote elsewhere, and a fixed default once silently measured a
# backend days older than the tree (2026-07-25: five copies spanning four days).
# It also owns the freshness rule enforced in provenance().


def newest_dylib(repo):
    """Newest existing bridge backend among the known build locations, else None."""
    return BRIDGE_BACKEND.newest(repo)


def default_dylib(repo):
    """The backend the harness loads when --dylib is not given (may not exist)."""
    return newest_dylib(repo) or BRIDGE_BACKEND.candidates(repo)[0]


def stale_backend_source(repo, dylib):
    """A backend source file newer than the dylib, or None if the dylib is current.
    Test/bench/example sources are ignored (see scripts/bridge_backend.py)."""
    return BRIDGE_BACKEND.stale_source(repo, dylib)

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
# The banner trust-cg-verify prints once per process when the independent proof
# checker is provisioned but unusable (obligation_cert_store.rs).
DEGRADED_MARKER = "verification is DEGRADED"


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
        self.env["MACOSX_DEPLOYMENT_TARGET"] = self.env.get("MACOSX_DEPLOYMENT_TARGET", "13.0")
        self.dylib = Path(args.dylib) if args.dylib else default_dylib(self.repo)
        # Pin before any lane runs so every subprocess inherits the mask. A pin
        # that cannot be applied is a tooling error, never a silently unpinned
        # row stamped as pinned.
        self.affinity = hostinfo.unpinned_record(hostinfo.core_topology())
        if args.pin_core is not None:
            try:
                self.affinity = hostinfo.pin_core(args.pin_core)
            except RuntimeError as error:
                self.die(2, f"--pin-core: {error}")
        self.rustc = self.resolve_rustc()
        # Both lanes compile for the same target. Unless one is named, it is the
        # resolved Trust compiler's host (the only target its bridge was built
        # for on a native box); the selection is stamped in provenance.
        self.target_selection = "explicit --target" if args.target else "driver host"
        if not args.target:
            args.target = self.driver["host"]
        self.workdir = Path(tempfile.mkdtemp(prefix="beatllvm-")).resolve()
        # The binaries and caches built here are scratch: removed when the
        # harness exits (normally, by die() or by an exception). Results
        # and --retain-dir copies live elsewhere.
        # Never register a temporary-root deletion, even if a test double or
        # broken allocator returns that root instead of a fresh child.
        temp_root = Path(tempfile.gettempdir()).resolve()
        if self.workdir.parent != temp_root or not self.workdir.name.startswith("beatllvm-"):
            print(f"unsafe benchmark scratch directory: {self.workdir}", file=sys.stderr)
            raise SystemExit(2)
        scratch_identity = self.workdir.stat()

        def cleanup_scratch():
            try:
                current = self.workdir.lstat()
                if (current.st_dev, current.st_ino) == (scratch_identity.st_dev, scratch_identity.st_ino):
                    shutil.rmtree(self.workdir, ignore_errors=True)
            except OSError:
                pass

        atexit.register(cleanup_scratch)
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
        try:
            return corpus.load_programs(HERE / "progs")
        except corpus.CorpusError as error:
            self.die(2, str(error))

    # ---------- provenance ----------
    def resolve_rustc(self):
        """The Trust compiler the bridge pin names (see module docstring, Driver)."""
        try:
            self.driver = TRUST_TOOLCHAIN.resolve(
                self.args.driver, pin=self.repo / TRUST_TOOLCHAIN.PIN_RELATIVE)
        except TRUST_TOOLCHAIN.ToolchainError as error:
            self.die(2, f"cannot resolve the pinned Trust compiler: {error}")
        return self.driver["compiler"]

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

    def cert_store_dir(self):
        """Mirror of trust-cg-verify obligation_cert_store::store_dir()."""
        if "TCG_NO_CERT_STORE" in os.environ or "TCG_NO_PROOF_CACHE" in os.environ:
            return None
        if "TCG_PROOF_CERT_STORE" in os.environ:
            return Path(os.environ["TCG_PROOF_CERT_STORE"])
        # The one user-cache rule (private_fs::user_cache_base): an absolute
        # XDG_CACHE_HOME, else an absolute HOME's .cache, else no store.
        xdg = os.environ.get("XDG_CACHE_HOME", "")
        if os.path.isabs(xdg):
            return Path(xdg) / "trust-cg" / "alethe-certs"
        home = os.environ.get("HOME", "")
        if os.path.isabs(home):
            return Path(home) / ".cache" / "trust-cg" / "alethe-certs"
        return None

    def cache_fingerprint(self):
        d = self.cache_dir()
        try:
            names = sorted(p.name for p in d.iterdir() if p.name.endswith(".verdict"))
        except OSError:
            names = []
        fp = hashlib.sha256("\n".join(names).encode()).hexdigest()
        out = {"dir": str(d), "verdict_count": len(names), "fingerprint_sha256": fp}
        cd = self.cert_store_dir()
        if cd is None:
            out["cert_store"] = {"dir": None, "cert_count": 0, "disabled": True}
        else:
            try:
                certs = sorted(p.name for p in cd.iterdir() if p.name.endswith(".alethecert"))
            except OSError:
                certs = []
            cfp = hashlib.sha256("\n".join(certs).encode()).hexdigest()
            out["cert_store"] = {
                "dir": str(cd),
                "cert_count": len(certs),
                "fingerprint_sha256": cfp,
            }
        return out

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
                        f"CARGO_TARGET_DIR=target-bridge RUSTC={self.driver['compiler']} "
                        f"{self.driver['targo']} --unverified build --release)\n"
                        f"  Refusing (measuring a stale backend attributes results to the wrong tree). "
                        f"Use --allow-stale-dylib to override; the row is NOT evidence.")
        rustc_v = run([self.rustc, "--version"], env=self.env).stdout.strip()
        ncpu = os.cpu_count() or 1
        load1 = os.getloadavg()[0]
        thr = self.args.load_threshold if self.args.load_threshold is not None else ncpu / 2.0
        self.load_threshold = thr
        # host_model is the PROCESSOR (the contract's Platform row), never a
        # hostname or a board name: the ratchet keys same-host comparisons on
        # it, and a box's name says nothing about the silicon a ratio was
        # measured on. An undetectable model or feature list stays empty and
        # leaves the row's provenance incomplete (REQUIRED_PROVENANCE).
        host = hostinfo.host_provenance()
        if self.affinity["policy"] == "none" and self.affinity.get("heterogeneous"):
            print("beat-llvm: WARNING: this host mixes core types "
                  f"({self.affinity.get('topology_source')}) and the lanes are not pinned; "
                  "scheduler placement alone can move a ratio (reports/perf/run_scaling.sh "
                  "measured ~1.4x). Use --pin-core on Linux; the affinity policy is recorded "
                  "either way.", file=sys.stderr)
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
            # The exact Trust driver identity and its (diagnostic, unverified)
            # frontend lane; see the module docstring's Driver paragraph.
            "driver": {key: self.driver[key] for key in (
                "schema", "selection", "requested_driver", "compiler", "targo", "sysroot",
                "host", "commit", "release", "version", "targo_version", "lane", "lane_label",
                "compiler_flags", "bridge_pin",
            )},
            "target": self.args.target,
            "target_selection": getattr(self, "target_selection", "explicit --target"),
            "host_arch": platform.machine(),
            # host_model, host_model_source, host_name (informational only),
            # machine_model, legacy_host_model (the pre-CPU-model identity the
            # ratchet still matches older baselines on), cpu_features,
            # cpu_features_source, cpu_features_sha256
            **host,
            # The -C target-cpu / target-feature policy ACTUALLY passed, derived
            # from the lanes' compile commands rather than asserted ("default"
            # today), with the lane-parity statement the contract's Runtime
            # section asks for.
            "cpu_policy": self.cpu_policy(),
            "affinity": self.affinity,
            "rss_sampling": self.rss_sampling(),
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
            "dylib_build_command": DYLIB_BUILD_COMMAND
                .replace("<trust-package>/bin/trustc", self.driver["compiler"])
                .replace("<trust-package>/bin/targo", self.driver["targo"]),
            "cc_version": _tool_version(["cc", "--version"]),
            "cc_path": shutil.which("cc") or "",
            "linker_version": _tool_version(["ld", "-v"]),
            "os": _os_description(),
            "aggregation": f"median-of-N per program (compile N={self.args.n_compile}, "
                           f"run N={self.args.n_run} after {1} warmup, program and compiler "
                           f"peak RSS N={self.args.n_rss}); raw samples retained per "
                           f"program as times_s and rss_samples",
            # Emitted-code size: what `emitted_size_bytes` measures (gates.json v3).
            "size_definition": emitted_size.DEFINITION,
            "corpus_manifest_sha256": self.manifest_digest(),
            "dylib_stale_override": bool(self.args.allow_stale_dylib and stale_src is not None),
            "quiet": load1 <= thr,  # re-checked at the end
            "load_status": "QUIET" if load1 <= thr else "LOADED",
            # Named culprits, not just a load number — see detect_runaways().
            "runaway_processes": runaways,
            "tcg_env": tcg_env,
            # Backend knobs passed as -Ztrust-ir-cg-args (the tracked successor of
            # TCG_* env). Empty is the production default; anything else is a
            # diagnostic lane.
            "bridge_cg_args": list(getattr(self.args, "bridge_cg_arg", None) or []),
            # Bridge compiles that printed DEGRADED verification (filled at the end).
            "proof_checker_degraded": [],
            # Which independent proof checker the backend can use (see
            # proof_checker_record); none makes the row ineligible.
            "proof_checker": proof_checker_record(self.env, self.driver.get("sysroot")),
            "cache": {"mode": "warm", **self.cache_fingerprint(), "verdict_count_after": None},
            "n_compile": self.args.n_compile,
            "n_run": self.args.n_run,
            "n_rss": self.args.n_rss,
            "warmup_runs": 1,
        }

    # ---------- lanes ----------
    def compile_cmd(self, src, out, opt, bridge):
        # compiler_flags is the explicit unverified frontend lane (-Ztrust-verify=off),
        # identical for every lane so only the backend differs.
        cmd = [self.rustc, *self.driver["compiler_flags"], "--edition=2021", "--crate-type", "bin",
               *TRUST_TOOLCHAIN.target_arguments(self.driver, self.args.target),
               "-Cpanic=abort", f"-Copt-level={opt}",
               "-o", str(out), str(src)]
        if bridge:
            # Backend knobs travel as the TRACKED option (trustc refuses TCG_*
            # environment); any knob makes the run a diagnostic lane, not evidence.
            knobs = [f"-Ztrust-ir-cg-args={knob}" for knob in (getattr(self.args, "bridge_cg_arg", None) or [])]
            cmd[1:1] = [f"-Zcodegen-backend={self.dylib}", *knobs]
        return cmd

    def note_bridge_stderr(self, stem, lane, stderr):
        """Record a bridge compile that reported DEGRADED verification (an
        unusable independent proof checker makes the backend treat it as absent:
        solver UNSAT verdicts are no longer promoted and the certificate store
        neither mints nor honors certificates). That is not the production
        configuration the row claims, so the run cannot be evidence."""
        if DEGRADED_MARKER in (stderr or ""):
            degraded = self.__dict__.setdefault("proof_degraded", set())
            degraded.add(f"{stem}:{lane}")

    def compile_once(self, src, out, opt, bridge, extra_env=None):
        env = dict(self.env)
        if extra_env:
            env.update(extra_env)
        t0 = time.monotonic()
        r = subprocess.run(self.compile_cmd(src, out, opt, bridge),
                           capture_output=True, text=True, env=env, timeout=COMPILE_TIMEOUT)
        dt = time.monotonic() - t0
        if bridge:
            self.note_bridge_stderr(Path(src).stem, f"O{opt}", r.stderr)
        err = ""
        if r.returncode != 0:
            errl = [l for l in r.stderr.splitlines() if l.startswith("error")]
            err = (errl[0] if errl else r.stderr.strip()[-300:])[:300]
            # The first line of a fail-closed names only the umbrella code; the
            # per-function causes ([TCG-PROOF-465], ...) follow. Keep their codes.
            codes = sorted(set(re.findall(r"\[TCG-[A-Z0-9]+-[0-9]+\]", r.stderr)))
            if codes:
                err = f"{err} causes={','.join(codes)}"
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
        """True cold (metrics-contract.md "Compile time": a fresh cache, population
        cost included). Every measured compile gets its own new, empty, private
        per-user cache root through XDG_CACHE_HOME, under which every persistent
        trust-cg cache resolves: the Alethe certificate store, the solver-identity
        memo, the private AY execution copy and the CEGIS cache. Nothing is
        reused from an earlier compile, and whatever the compile writes (its
        population cost) is inside the timed region; the entry count it left is
        recorded per compile.

        The lane used to set TCG_NO_PROOF_CACHE / TCG_NO_CERT_STORE. The Trust
        driver refuses the whole TCG_/TRUST_CG_ environment family as untracked
        codegen controls, so every such compile failed, and a lane that only
        disabled the tiers would be a cold_proxy (no population cost), not cold.
        """
        rec = {"ok": False, "times_s": [], "median_s": None, "err": "",
               "cache": "fresh private XDG_CACHE_HOME per measured compile",
               "cache_entries_after": []}
        for i in range(n):
            root = fresh_cache_root(self.workdir, f"cold-{src.stem}-{i}-")
            try:
                ok, dt, err = self.compile_once(src, out, 3, True, {"XDG_CACHE_HOME": str(root)})
                rec["cache_entries_after"].append(count_entries(root))
            finally:
                shutil.rmtree(root, ignore_errors=True)
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
        code0 = None
        times = []

        def failed(kind, code=None, detail=None):
            return {"exit": code0, "nondet_exit": None, "times_s": times,
                    "median_s": None, "rel_spread": None,
                    "error": {"kind": kind, "returncode": code, "detail": detail,
                              "phase": "warmup" if index == 0 else "measured",
                              "sample": index}}

        for index in range(n + 1):
            try:
                code, dt = self.run_bin(path)
            except subprocess.TimeoutExpired as error:
                return failed("timeout", detail=str(error))
            except OSError as error:
                return failed("launch_error", detail=str(error))
            # Fixtures return their checksum modulo 126. A signal or reserved
            # exit status is a failed run, even when both lanes repeat it.
            if not 0 <= code < 126:
                return failed("signal" if code < 0 else "invalid_exit", code)
            if index == 0:  # warmup (unmeasured)
                code0 = code
                continue
            if code != code0:
                return {"exit": code0, "nondet_exit": code, "times_s": times, "median_s": None}
            # Preserve microsecond samples: millisecond rounding hides the
            # spread of the shortest programs without changing the metric.
            times.append(round(dt, 6))
        med = round(statistics.median(times), 6)
        spread = round((max(times) - min(times)) / med, 4) if med else None
        return {"exit": code0, "nondet_exit": None, "times_s": times, "median_s": med,
                "rel_spread": spread}

    def cpu_policy(self):
        """The CPU policy actually passed to both lanes (see cpu_policy_from_cmds),
        plus what "default" resolves to for the LLVM lane on this target."""
        probe_src, probe_out = self.workdir / "policy-probe.rs", self.workdir / "policy-probe"
        policy = hostinfo.cpu_policy_from_cmds(
            self.compile_cmd(probe_src, probe_out, "3", bridge=False),
            self.compile_cmd(probe_src, probe_out, "3", bridge=True))
        target_args = TRUST_TOOLCHAIN.target_arguments(self.driver, self.args.target)
        cpus = run([self.rustc, "--print", "target-cpus", *target_args],
                   env=self.env)
        policy["llvm_default_target_cpu"] = (hostinfo.parse_default_target_cpu(cpus.stdout)
                                             if cpus.returncode == 0 else None)
        cfg = run([self.rustc, "--print", "cfg", *target_args], env=self.env)
        policy["llvm_default_target_features"] = (hostinfo.parse_cfg_target_features(cfg.stdout)
                                                  if cfg.returncode == 0 else None)
        return policy

    def rss_sampling(self):
        """How peak RSS is sampled — the contract's 'Size and memory' section
        requires the compiler/program distinction and the sampling method."""
        return {
            "method": rss_capture.METHOD,
            "method_id": rss_capture.METHOD_ID,
            "sampler_identity": rss_capture.sampler_identity(env=self.env),
            "ru_maxrss_unit": rss_capture.maxrss_unit(),
            "reported_unit": "bytes",
            "peak_rss_bytes": "the compiled program: the median of N dedicated runs per lane "
                              "(N = n_rss), lanes interleaved run by run, outside the timed loop",
            "compile_peak_rss_bytes": "the compiler: the largest single process of the trustc "
                                      "invocation (trustc or its cc/ld link step); the median of "
                                      "N dedicated compiles per lane (N = n_rss), lanes "
                                      "interleaved compile by compile, outside the timed loop",
            "noise_policy": "every reading is the exact median of an odd number of samples, "
                            "each retained with its sampler status; a lane with any failed "
                            "sample has no reading (never a median of the survivors); a "
                            "program comparison's parity band is max(5%, "
                            f"{check_gates.RSS_SPREAD_FACTOR} x the larger lane's relative "
                            "sample spread (max-min)/median), and a comparison whose spread "
                            f"exceeds {check_gates.RSS_SPREAD_MAX} is unresolved; evidence "
                            f"needs N >= {check_gates.RSS_CONTRACT_N}",
            "gate": "contract/gates.json version 3: R1 (fails if any program's bridge median "
                    "exceeds max(its LLVM -O3 median, the floor) by more than its parity band; "
                    "passes only when every program's comparison is resolved, above the floor "
                    "and not noisy; otherwise "
                    "unmeasured) and R2 (compiler peak-RSS geomean of medians <= 1.00x LLVM "
                    "-O2, no floor-bound compiler reading); the program-RSS geomean is "
                    "reported, not gated",
            "floor_rule": "every reading is at least sampler_floor_bytes and one above it is "
                          "the process's peak; a comparison is resolved only when both readings "
                          f"are above {check_gates.RSS_FLOOR_BOUND_FACTOR}x sampler_floor_bytes",
            # Floor and /usr/bin/time agreement, measured on this host now.
            "cross_check": rss_capture.cross_check(env=self.env),
        }

    def compile_peak_rss(self, src, out, opt, bridge, extra_env=None):
        """Peak RSS of the COMPILER (bytes), via peak_rss.measure: the largest
        single process of the trustc invocation (trustc or its cc/ld link step).

        The third axis of the superiority goal. `peak_rss` below measures the
        PRODUCED PROGRAM's memory; this measures what it costs to produce it —
        a distinct claim.

        Run ONCE per lane, deliberately OUTSIDE the timing loop: the wrapper
        adds a fork+exec that would perturb the compile-time medians the whole
        contract is built on. Returns None when the compile fails or is killed,
        so a missing value is never silently read as zero.
        """
        return self.compile_rss_sample(src, out, opt, bridge, extra_env)["bytes"]

    def compile_rss_sample(self, src, out, opt, bridge, extra_env=None):
        """The compiler peak-RSS sample: bytes (None unless the compile succeeded
        and was reaped normally) plus the sampler's status, return code and wall
        time, retained as the raw sample so a missing value keeps its reason."""
        env = dict(self.env)
        if extra_env:
            env.update(extra_env)
        sample = rss_capture.measure(self.compile_cmd(src, out, opt, bridge), env=env,
                                     timeout=COMPILE_TIMEOUT)
        if bridge:
            self.note_bridge_stderr(Path(src).stem, f"rss-O{opt}", sample.stderr)
        return rss_record(sample, sample.peak_rss_bytes if sample.returncode == 0 else None)

    def peak_rss(self, path):
        """Peak RSS of the compiled program (bytes). Its exit code is the checksum,
        so only a killed or unexecutable run yields None."""
        return self.program_rss_sample(path)["bytes"]

    def program_rss_sample(self, path):
        """The program peak-RSS sample (see compile_rss_sample)."""
        sample = rss_capture.measure([str(path)], timeout=RUN_TIMEOUT)
        return rss_record(sample, sample.peak_rss_bytes)

    def rss_lanes(self, n, lanes, sample):
        """N samples per lane, interleaved lane by lane (so load drift during the
        measurement falls on every lane alike): {lane: [record, ...]} with the
        exact median of each lane's bytes (None unless every sample is valid)."""
        samples = {lane: [] for lane in lanes}
        for _ in range(n):
            for lane in lanes:
                samples[lane].append(sample(lane))
        medians = {lane: check_gates.sample_median([record["bytes"] for record in records])
                   for lane, records in samples.items()}
        return samples, medians

    def emitted_size_lane(self, src, stem, lane, opt, bridge, timed_binary):
        """Emitted-code size of one lane (emitted_size.py holds the definition).

        The lane is linked once more, into a fresh private directory, with the
        system linker's map; the map attributes the image's bytes to the
        objects this compile wrote into that directory. The reading is refused
        (bytes None, with the reason) when that compile fails or when its
        image's section bytes differ from the timed compile's binary: the map
        must describe the binary the other metrics measured."""
        directory = Path(tempfile.mkdtemp(prefix=f"size-{stem}-{lane}-", dir=self.workdir))
        out = directory / f"{stem}_{lane}"
        map_path = directory / "link.map"
        cmd = self.compile_cmd(src, out, opt, bridge) + emitted_size.link_map_args(map_path)
        record = {"method": "linker map", "link_map_args": emitted_size.link_map_args("<map>")}
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, env=self.env,
                               timeout=COMPILE_TIMEOUT, cwd=directory)
            if bridge:
                self.note_bridge_stderr(stem, f"size-O{opt}", r.stderr)
            if r.returncode != 0:
                errl = [l for l in r.stderr.splitlines() if l.startswith("error")]
                record.update(bytes=None, error="size compile failed: "
                              + (errl[0] if errl else r.stderr.strip()[-300:])[:300])
                return record
            record.update(emitted_size.measure_map(map_path, directory, cwd=directory))
            try:
                size_image, timed_image = emitted_size.image_digest(out), \
                    emitted_size.image_digest(timed_binary)
            except (OSError, ValueError, IndexError, struct.error) as error:
                size_image = timed_image = None
                record.update(bytes=None, error=f"image digest failed: {error}")
            record["image_sha256"] = size_image
            record["timed_image_sha256"] = timed_image
            if size_image is not None and size_image != timed_image:
                record.update(bytes=None, error="the map-linked image's section bytes differ from "
                                                "the timed compile's binary")
            return record
        except subprocess.TimeoutExpired:
            record.update(bytes=None, error=f"size compile timed out after {COMPILE_TIMEOUT}s")
            return record
        finally:
            shutil.rmtree(directory, ignore_errors=True)

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
               "emitted_size_bytes": {}, "emitted_size": {},
               "peak_rss_bytes": {}, "compile_peak_rss_bytes": {},
               "rss_samples": {"program": {}, "compiler": {}}, "ratios": {}}
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
        # sizes: the linked file, and the emitted code (a map-linked twin whose
        # section bytes must equal the timed binary's)
        for lane, bridge in (("llvm_o3", False), ("bridge", True)):
            row["size_bytes"][lane] = outs[lane].stat().st_size
            record = self.emitted_size_lane(src, stem, lane, "3", bridge, outs[lane])
            row["emitted_size"][lane] = record
            row["emitted_size_bytes"][lane] = record.get("bytes")
        # runtime medians (warmup + N), llvm -O3 vs bridge
        for lane in ("llvm_o3", "bridge"):
            row["run"][lane] = self.runtime_lane(outs[lane], self.args.n_run)
            if row["run"][lane].get("error") is not None:
                row["verdict"] = "INCOMPLETE"
                row["reason"] = f"runtime failed in lane {lane}: {row['run'][lane]['error']['kind']}"
                return row
            if row["run"][lane]["nondet_exit"] is not None:
                row["verdict"] = "MISMATCH"
                row["reason"] = f"nondeterministic exit code in lane {lane}"
                return row
        # peak RSS: the median of N dedicated runs per lane, not folded into the
        # timed medians
        n_rss = self.args.n_rss
        samples, medians = self.rss_lanes(n_rss, ("llvm_o3", "bridge"),
                                          lambda lane: self.program_rss_sample(outs[lane]))
        row["rss_samples"]["program"], row["peak_rss_bytes"] = samples, medians
        # COMPILER peak RSS: the median of N extra compiles per lane, outside the
        # timing loop.
        compiler_lanes = {"llvm_o2": ("2", False), "llvm_o3": ("3", False), "bridge": ("3", True)}
        samples, medians = self.rss_lanes(
            n_rss, tuple(compiler_lanes),
            lambda lane: self.compile_rss_sample(src, self.workdir / f"{stem}_rss_{lane}",
                                                 *compiler_lanes[lane]))
        row["rss_samples"]["compiler"], row["compile_peak_rss_bytes"] = samples, medians
        # Differential exit-residue check; collisions can hide different full states (contract section 6).
        le, be = row["run"]["llvm_o3"]["exit"], row["run"]["bridge"]["exit"]
        if le != be:
            row["verdict"] = "MISMATCH"
            row["reason"] = f"exit codes differ: llvm_o3={le} bridge={be}"
            return row
        row["verdict"] = "MATCH"
        row["ratios"] = row_ratios(row, cold="bridge_cold" in row["compile"])
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
    def aggregates(self, programs, cross_check=None):
        """Intent-to-treat counts and the aggregates over MATCH rows.

        Computed by contract/check_gates.py's shared functions, which the
        ledger ratchet reruns on the per-program table and compares with these
        stamps: counts and exact coverage (`count_aggregates`), runtime and
        compile ratios from each lane's raw samples (`ratio_aggregates`), and
        size and peak RSS (`resource_aggregates`). Every value is EXACT
        (rounding is for display only) and FAIL-CLOSED: null unless every
        covered MATCH row has its value, with the rows lacking one named in
        `ratio_missing` / `resource_missing` (metrics-contract.md: a missing
        value "cannot silently disappear from an aggregate"). The one deliberate
        subset, `runtime_geomean_reliable_only`, is non-gating and publishes
        its criteria."""
        agg = check_gates.count_aggregates(programs)
        agg.update(check_gates.ratio_aggregates(programs))
        match = {k: v for k, v in programs.items() if v["verdict"] == "MATCH"}

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
        agg["runtime_geomean_reliable_only"] = check_gates.complete_geomean(
            [check_gates.program_ratios(v)["runtime_vs_llvm_o3"] for v in reliable])
        agg["runtime_reliable_program_count"] = len(reliable)
        agg["runtime_reliable_criteria"] = {
            "min_llvm_median_s": RELIABLE_MIN_S,
            "max_rel_spread": RELIABLE_SPREAD_MAX,
        }
        agg.update(check_gates.resource_aggregates(programs, cross_check))
        return agg

    def markdown(self, res):
        p, a = res["provenance"], res["aggregates"]
        lines = [
            f"# beat-llvm results — {p['git_sha'][:12]}{'-dirty' if p['git_dirty'] else ''} "
            f"({p['timestamp_utc']}, {p['host_arch']}, {p['load_status']})",
            "",
            f"- dylib sha256 `{p['dylib_sha256'][:16]}…`  trustc `{p['rustc_version']}`  target `{p['target']}`",
            f"- host: {p.get('host_model') or 'CPU model UNAVAILABLE'} ({p.get('host_name')}, "
            f"{p.get('machine_model') or 'machine model unavailable'}); "
            f"-C target-cpu {(p.get('cpu_policy') or {}).get('target_cpu')}; "
            f"affinity {(p.get('affinity') or {}).get('policy')}"
            + (f" core {p['affinity']['core']}" if (p.get('affinity') or {}).get('core') is not None else ""),
            f"- load {p['loadavg_before']}→{p['loadavg_after']} (threshold {p['load_threshold']}, "
            f"quiet={p['quiet']})  cache: {p['cache']['mode']}, {p['cache']['verdict_count']}→"
            f"{p['cache']['verdict_count_after']} verdicts, "
            f"{(p['cache'].get('cert_store') or {}).get('cert_count')}→"
            f"{(p['cache'].get('cert_store') or {}).get('cert_count_after')} certificates  "
            f"N: compile={p['n_compile']} run={p['n_run']}",
            f"- TCG env: `{p['tcg_env'] or '{} (production defaults)'}`",
            f"- **headline-eligible: {res['headline_eligible']}**"
            + ("" if res["headline_eligible"] else
               "  (NOT evidence for gates: " + "; ".join(res.get("ineligible_reasons")
                                                         or ["see provenance"]) + ")"),
            "",
            # Display rounding only; the JSON keeps every aggregate exact.
            f"**coverage {fmt(a['coverage_pct'], 1)}% ({a['match_count']}/{a['total_programs']} MATCH, "
            f"{a['incomplete_count']} INCOMPLETE, {a['mismatch_count']} MISMATCH; "
            f"nondet: {a['nondet_failclosed_count']} NONDET-FAILCLOSED, "
            f"{a.get('nondet_candidate_count', 0)} NONDET-CANDIDATE)** — "
            f"runtime geomean vs LLVM -O3: **{fmt(a['runtime_geomean_vs_llvm_o3'])}x** "
            f"[resolvable-rows-only: **{fmt(a.get('runtime_geomean_reliable_only'))}x** over "
            f"{a.get('runtime_reliable_program_count')} programs with llvm median >= "
            f"{RELIABLE_MIN_S}s and rel_spread <= {RELIABLE_SPREAD_MAX}] "
            f"(scalar {fmt(a.get('scalar_runtime_geomean_vs_llvm_o3'))}x, "
            f"worst {fmt(a['runtime_worst_vs_llvm_o3'])}x); compile warm geomean vs -O2: "
            f"**{fmt(a['compile_warm_geomean_vs_llvm_o2'])}x** (vs -O3: {fmt(a['compile_warm_geomean_vs_llvm_o3'])}x)"
            + (f"; MISSING ratios: {a.get('ratio_missing')}" if a.get("ratio_missing") else ""),
            "",
            # Size and RSS aggregates are fail-closed (null when any MATCH row
            # lacks a reading, which is then listed) and gated by gates.json v3.
            f"emitted-code size geomean vs LLVM -O3: **{fmt(a.get('emitted_size_geomean_vs_llvm_o3'), 4)}x** "
            f"(worst {fmt(a.get('emitted_size_worst_vs_llvm_o3'), 4)}x; linked-map attribution, "
            f"text + read-only data); linked file bytes geomean: "
            f"{fmt(a.get('size_geomean_vs_llvm_o3'), 5)}x "
            f"(worst {fmt(a.get('size_worst_vs_llvm_o3'), 5)}x, shared std included); "
            f"peak RSS is the median of {p.get('n_rss')} samples per lane "
            f"(largest relative spread: program {fmt(a.get('program_rss_max_rel_spread'), 4)}, "
            f"compiler {fmt(a.get('compile_rss_max_rel_spread'), 4)}); program peak-RSS geomean "
            f"vs -O3: {fmt(a.get('rss_geomean_vs_llvm_o3'))}x ({a.get('program_rss_floor_bound_count')} "
            f"of {a['match_count']} programs floor-bound, R1 losses "
            f"{'unmeasured' if a.get('program_rss_resolved_loss_count') is None else a.get('program_rss_resolved_loss_count')} "
            f"{a.get('program_rss_resolved_losses') or ''}); "
            f"compiler peak-RSS geomean vs -O2: "
            f"{fmt(a.get('compile_rss_geomean_vs_llvm_o2'))}x (vs -O3: {fmt(a.get('compile_rss_geomean_vs_llvm_o3'))}x, "
            f"{a.get('compile_rss_floor_bound_count')} floor-bound readings) "
            f"— ru_maxrss ({(p.get('rss_sampling') or {}).get('ru_maxrss_unit', '?')}) normalised to bytes; "
            f"sampler floor {_cross(p).get('sampler_floor_bytes')} B (readings at or below "
            f"{a.get('rss_floor_bound_bytes')} B are upper bounds); /usr/bin/time agreement "
            f"{_cross(p).get('agree')}; gated by contract/gates.json v4 (S1/S2 linked size, "
            f"S3/S4 emitted size, R1/R2 RSS)"
            + (f"; MISSING readings: {a.get('resource_missing')}" if a.get("resource_missing") else ""),
            "",
            "coverage by category (intent-to-treat — INCOMPLETE rows stay in the denominator):",
            "",
            "| category | coverage % | match/total | incomplete | runtime geomean x |",
            "|---|---|---|---|---|",
        ]
        for cname, c in a.get("by_category", {}).items():
            lines.append(f"| {cname} | {fmt(c['coverage_pct'], 1)}% | {c['match']}/{c['total']} "
                         f"| {c['incomplete']} | {fmt(c.get('runtime_geomean_vs_llvm_o3'))} |")
        lines += [
            "",
            "| program | cat | verdict | run llvm-O3 (s) | run bridge (s) | runtime x | compile -O2 (s) | compile -O3 (s) | bridge warm (s) | warm x(-O2) | emitted B llvm/bridge | emitted x | size x | rss x | compiler rss x(-O2) |",
            "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|",
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
                f"| {fmt(r.get('runtime_vs_llvm_o3'))} | {g(c,'llvm_o2','median_s')} "
                f"| {g(c,'llvm_o3','median_s')} | {g(c,'bridge_warm','median_s')} "
                f"| {fmt(r.get('compile_warm_vs_llvm_o2'))} "
                f"| {g(v, 'emitted_size_bytes', 'llvm_o3')}/{g(v, 'emitted_size_bytes', 'bridge')} "
                f"| {fmt(r.get('emitted_size_vs_llvm_o3'))} | {fmt(r.get('size_vs_llvm_o3'))} "
                f"| {fmt(r.get('rss_vs_llvm_o3'))} | {fmt(r.get('compile_rss_vs_llvm_o2'))} |")
        lines.append("")
        lines.append("> MATCH means deterministic exit-residue agreement (checksum mod 126), "
                      "not full-output equality: different checksums or states can collide. "
                      "A MISMATCH is definitive P0 (contract section 6).")
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
        after = self.cache_fingerprint()
        prov["cache"]["verdict_count_after"] = after["verdict_count"]
        # The Alethe certificate store is the persistent reuse tier the warm lane
        # actually reads; its before/after entry counts are the contract's
        # "before/after entry counts" (the legacy verdict directory stays empty).
        prov["cache"]["cert_store"]["cert_count_after"] = after["cert_store"].get("cert_count")
        prov["proof_checker_degraded"] = sorted(getattr(self, "proof_degraded", set()))
        if prov["proof_checker_degraded"]:
            print("beat-llvm: WARNING: the independent proof checker was UNUSABLE (verification "
                  f"DEGRADED) in {len(prov['proof_checker_degraded'])} bridge compile(s) — the "
                  "measured configuration is not the production proof lane; row is NOT evidence. "
                  "Put a capable Clean package prefix on PATH.", file=sys.stderr)
        agg = self.aggregates(programs, (prov.get("rss_sampling") or {}).get("cross_check"))
        # metrics-contract.md, "Required provenance": "Missing required data
        # never defaults to an eligible result." Enforce it rather than trusting
        # that every field happened to get stamped — a row that omits the build
        # command, toolchain, OS, aggregation method or corpus digest is not
        # contract-compliant no matter how quiet the machine was.
        missing_provenance = missing_required_provenance(prov)
        prov["missing_required_provenance"] = missing_provenance
        prov["provenance_complete"] = not missing_provenance
        if missing_provenance:
            print(
                "beat-llvm: WARNING: missing contract-required provenance "
                f"{missing_provenance} — row is NOT evidence.",
                file=sys.stderr,
            )
        reasons = ineligibility_reasons(prov, agg, self.args.n_compile, self.args.n_run, programs,
                                        self.args.n_rss)
        if "size/RSS measurement incomplete" in " ".join(reasons):
            print(f"beat-llvm: WARNING: size/RSS readings missing {agg['resource_missing']} "
                  "— aggregates over them are null and the row is NOT evidence.", file=sys.stderr)
        res = {
            "schema": SCHEMA,
            "provenance": prov,
            "headline_eligible": not reasons,
            # Why a row is not evidence, in words (empty for an eligible row).
            "ineligible_reasons": reasons,
            "programs": programs,
            "aggregates": agg,
        }
        # emit
        outdir = Path(self.args.out_dir) if self.args.out_dir else HERE / "results"
        outdir.mkdir(parents=True, exist_ok=True)
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        base = f"{prov['git_sha'][:12]}{'-dirty' if prov['git_dirty'] else ''}-{stamp}"
        jpath = outdir / f"{base}.json"
        mpath = outdir / f"{base}.md"
        # The retained directory is named in the JSON so the condensed ledger
        # row can point at its raw evidence; plan it before the JSON is written.
        retain_dest = None
        if self.args.retain_dir:
            retain_dest = plan_retention_dir(Path(self.args.retain_dir).resolve(), prov)
            res["retention"] = {"dir": repo_relative(retain_dest, self.repo),
                                "harness_option": "--retain-dir"}
        with open(jpath, "w") as f:
            json.dump(res, f, indent=1)
        md = self.markdown(res)
        mpath.write_text(md + "\n")
        print(md)
        print(f"\nresults: {jpath}\n         {mpath}")
        if retain_dest is not None:
            write_retention(retain_dest, res, jpath, mpath)
            print(f"retained: {retain_dest}")
        if agg["mismatch_count"] > 0:
            qdir = outdir / "mismatch"
            qdir.mkdir(exist_ok=True)
            shutil.copy(jpath, qdir / jpath.name)
            print(f"beat-llvm: *** MISMATCH — P0 STOP-THE-LINE *** quarantined: {qdir / jpath.name}",
                  file=sys.stderr)
            sys.exit(1)
        sys.exit(0)


def fmt(value, digits=3):
    """A number for a table or README: rounded for reading, never for gating."""
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return "—" if value is None else str(value)
    return f"{value:.{digits}f}"


def row_ratios(row, cold=False):
    """A row's exact bridge/LLVM ratios (display and retention copy; the gates
    read the aggregates, which check_gates recomputes from raw samples)."""
    ratios = check_gates.program_ratios(row, cold)

    def ratio(field, lane, base):
        a = check_gates.resource_reading(row, field, lane)
        b = check_gates.resource_reading(row, field, base)
        return a / b if a and b else None

    ratios["size_vs_llvm_o3"] = ratio("size_bytes", "bridge", "llvm_o3")
    ratios["emitted_size_vs_llvm_o3"] = ratio("emitted_size_bytes", "bridge", "llvm_o3")
    ratios["rss_vs_llvm_o3"] = ratio("peak_rss_bytes", "bridge", "llvm_o3")
    for opt in ("2", "3"):
        ratios[f"compile_rss_vs_llvm_o{opt}"] = ratio("compile_peak_rss_bytes", "bridge",
                                                      f"llvm_o{opt}")
    return ratios


def fresh_cache_root(parent, prefix):
    """A new, empty, private (0700) directory for one compile's user cache."""
    return Path(tempfile.mkdtemp(prefix=prefix, dir=parent))


def count_entries(root):
    """Files and directories under `root` (how much a compile populated)."""
    return sum(1 for _ in Path(root).rglob("*"))


def rss_record(sample, peak_bytes):
    """A retained peak-RSS sample: the bytes the harness uses (None when the run
    has no meaningful peak) and the sampler's own account of the run."""
    return {"bytes": peak_bytes, "status": sample.status, "returncode": sample.returncode,
            "wall_s": sample.wall_s}


def _cross(prov):
    """The RSS sampler's cross-check record from provenance, or {}."""
    return ((prov.get("rss_sampling") or {}).get("cross_check")) or {}


# metrics-contract.md, "Required provenance": "Missing required data never
# defaults to an eligible result." Enforced rather than trusting that every
# field happened to get stamped — a row that omits the build command,
# toolchain, OS, CPU model, sampling method or corpus digest is not
# contract-compliant no matter how quiet the machine was.
REQUIRED_PROVENANCE = (
    "git_sha", "dylib_path", "dylib_sha256", "dylib_mtime",
    "dylib_build_command", "rustc_version", "rustc_path",
    "cc_version", "linker_version", "os", "host_arch", "ncpu",
    "target", "aggregation", "corpus_manifest_sha256",
    "timestamp_utc", "harness",
    # CPU/target parity: the processor, its features, the CPU policy passed to
    # both lanes, the affinity policy (a stated "none" counts; an absent one
    # does not) and how RSS was sampled. An empty model or feature list means
    # detection failed, which is not evidence.
    "host_model", "cpu_features", "cpu_policy", "affinity", "rss_sampling",
    # gates.json version 3: what emitted-code size measures, and the peak-RSS N.
    "size_definition", "n_rss",
)


def missing_required_provenance(prov):
    return [k for k in REQUIRED_PROVENANCE if not prov.get(k)]


CHECKER_PROBE_TIMEOUT = 30


def probe_checker(path, env):
    """Run `<clean> --version` once: whether the candidate actually executes.

    An existing +x file is not a checker: a text file with the bit set fails
    exec (ENOEXEC), and trust-cg-verify then drops the candidate with only a
    trace, no DEGRADED banner (its banner covers capability defects, not
    unrunnable or timed-out checkers). So the harness runs it itself."""
    try:
        r = subprocess.run([str(path), "--version"], capture_output=True, text=True, env=env,
                           timeout=CHECKER_PROBE_TIMEOUT)
    except subprocess.TimeoutExpired:
        return {"runs": False, "probe": "--version", "error": f"timed out after {CHECKER_PROBE_TIMEOUT}s"}
    except OSError as error:
        return {"runs": False, "probe": "--version", "error": f"cannot execute: {error}"}
    first = (r.stdout.strip().splitlines() or [""])[0]
    return {"runs": r.returncode == 0 and bool(first), "probe": "--version",
            "returncode": r.returncode, "version": first[:200]}


def proof_checker_record(env, sysroot, platform_name=None, probe=None):
    """The independent proof checker (Clean) the backend can use, in the order
    trust-cg-verify considers it (obligation_cert_store.rs
    default_clean_checker_candidates): an aterm-packaged `clean` named through
    a `<prefix>/bin` entry on PATH, then the `bin/clean` shipped in the driver's
    Trust sysroot. Each existing candidate is stamped with its SHA-256 and
    whether it ran when probed (`probe_checker`).

    This is positive evidence that a checker exists and executes; whether it
    is capable is what the backend's `verification is DEGRADED` banner reports.
    With no candidate that runs, the backend runs without one and may print
    nothing, so the run is ineligible. (TCG_EXTERNAL_CLEAN_CHECKER overrides
    cannot reach a trustc compile: trustc refuses the TCG_* environment.)"""
    probe = probe or probe_checker
    platform_name = platform_name or sys.platform
    found = []
    packaged = PROOF_TOOLS.packaged_tool("clean", env.get("PATH", ""), env.get("HOME", ""),
                                        platform_name)
    if packaged is not None:
        found.append((Path(packaged), "aterm-packaged"))
    if sysroot:
        shipped = PROOF_TOOLS.executable_file(Path(sysroot) / "bin" / "clean")
        if shipped is not None and all(shipped != path for path, _ in found):
            found.append((shipped, "toolchain-sysroot"))
    return {
        "tool": "clean",
        "candidates": [{"path": str(path), "route": route, "sha256": sha256_file(path),
                        **probe(path, env)}
                       for path, route in found],
        "order": "aterm-packaged (PATH <prefix>/bin), then the driver's sysroot bin/clean",
    }


def ineligibility_reasons(prov, agg, n_compile, n_run, programs=None, n_rss=None):
    """Every reason the run is not headline evidence (contract "Eligibility");
    an empty list is the only eligible outcome. contract/check_gates.py
    recomputes the same facts from the results JSON before any row counts."""
    env = prov.get("tcg_env") or {}
    reasons = []
    if programs is not None and not check_gates.full_corpus({"programs": programs}):
        reasons.append(f"program subset: {len(programs)} of the "
                       f"{len(check_gates.corpus_programs() or [])}-program contract corpus "
                       "(--progs runs are diagnostics, never evidence or baselines)")
    if not prov.get("quiet"):
        reasons.append(f"machine LOADED (1-min load {prov.get('loadavg_before')}->"
                       f"{prov.get('loadavg_after')} vs threshold {prov.get('load_threshold')})")
    if prov.get("git_dirty"):
        reasons.append("source tree has tracked edits")
    if ("TCG_NO_PROOF_CERTS" in env or env.get("TCG_REFINE_SOLVER") == "0"
            or "TCG_NO_PROOF_CACHE" in env):
        reasons.append("proof-weakening TCG_* environment")
    if prov.get("load_threshold_overridden"):
        reasons.append("--load-threshold overridden")
    if prov.get("dylib_stale_override"):
        reasons.append("stale bridge backend measured (--allow-stale-dylib)")
    if prov.get("runaway_processes"):
        reasons.append("runaway processes on the host")
    if prov.get("bridge_cg_args"):
        reasons.append(f"non-default backend knobs {prov['bridge_cg_args']} (diagnostic lane)")
    if not check_gates.proof_checker_runs(prov):
        candidates = (prov.get("proof_checker") or {}).get("candidates")
        reasons.append("no independent proof checker (Clean) resolvable for the backend"
                       if not candidates else
                       "no independent proof checker (Clean) candidate ran when probed")
    if prov.get("proof_checker_degraded"):
        reasons.append("independent proof checker unusable (verification DEGRADED) in "
                       f"{len(prov['proof_checker_degraded'])} bridge compile(s)")
    if not prov.get("provenance_complete"):
        reasons.append(f"missing required provenance {prov.get('missing_required_provenance')}")
    if agg.get("mismatch_count") != 0:
        reasons.append("MISMATCH rows")
    n_rss = prov.get("n_rss") if n_rss is None else n_rss
    below = []
    if n_compile < 3:
        below.append(f"compile {n_compile} < 3")
    if n_run < 5:
        below.append(f"run {n_run} < 5")
    if type(n_rss) is not int or n_rss < check_gates.RSS_CONTRACT_N:
        below.append(f"peak RSS {n_rss!r} < {check_gates.RSS_CONTRACT_N}")
    if below:
        reasons.append(f"below contract-default N ({', '.join(below)})")
    if agg.get("resource_measurement_complete") is not True:
        reasons.append(f"size/RSS measurement incomplete ({agg.get('resource_missing')})")
    elif agg.get("match_count") and not (type(agg.get("rss_min_samples")) is int
                                         and agg["rss_min_samples"] >= check_gates.RSS_CONTRACT_N):
        # check_gates.rss_samples_meet_contract: a run with no MATCH row has no
        # retained reading and is held to the provenance N above only.
        reasons.append(f"retained peak-RSS samples below the contract N (fewest "
                       f"{agg.get('rss_min_samples')!r} < {check_gates.RSS_CONTRACT_N})")
    if agg.get("ratio_missing"):
        reasons.append(f"runtime/compile samples missing ({agg.get('ratio_missing')})")
    if agg.get("rss_sampler_floor_bytes") is None:
        reasons.append("RSS sampler calibration failed or disagreed (no usable sampler floor)")
    return reasons


def repo_relative(path, repo):
    try:
        return str(Path(path).resolve().relative_to(Path(repo).resolve()))
    except ValueError:
        return str(path)


def plan_retention_dir(root, prov):
    """<root>/<date>-<rev>/ for this run. A second run of the same revision on
    the same day (a warm run and then `--cold`, say) gets the run's UTC time as
    a suffix instead of overwriting the first record."""
    root = Path(root)
    ts = prov["timestamp_utc"]
    name = f"{ts[:10]}-{prov['git_sha'][:12]}{'-dirty' if prov['git_dirty'] else ''}"
    dest = root / name
    if dest.exists():
        dest = root / f"{name}-{ts[11:19].replace(':', '')}Z"
    serial = 2
    while dest.exists():
        dest = root / f"{name}-{ts[11:19].replace(':', '')}Z-{serial}"
        serial += 1
    return dest


def retention_readme(res, jpath, mpath):
    p, a = res["provenance"], res["aggregates"]
    eligible = bool(res.get("headline_eligible"))
    policy = p.get("cpu_policy") or {}
    affinity = p.get("affinity") or {}
    rss = p.get("rss_sampling") or {}
    cross = rss.get("cross_check") or {}
    lanes = [f"warm compile (median-of-{p.get('n_compile')} after 1 unmeasured warmup compile)",
             f"runtime (median-of-{p.get('n_run')} after 1 warmup run)",
             "linked binary size and emitted-code size (linker-map attribution)",
             f"program and compiler peak RSS (median-of-{p.get('n_rss')})"]
    if any((row.get("compile") or {}).get("bridge_cold") for row in (res.get("programs") or {}).values()):
        lanes.append("true-cold compile (`--cold`)")
    metrics = [
        ("coverage (intent-to-treat)", f"{fmt(a.get('coverage_pct'), 1)}% ({a.get('match_count')}/{a.get('total_programs')} MATCH, "
                                       f"{a.get('incomplete_count')} INCOMPLETE, {a.get('mismatch_count')} MISMATCH)"),
        ("runtime geomean vs LLVM -O3", a.get("runtime_geomean_vs_llvm_o3")),
        ("scalar runtime geomean vs -O3", a.get("scalar_runtime_geomean_vs_llvm_o3")),
        ("runtime worst vs -O3", a.get("runtime_worst_vs_llvm_o3")),
        ("compile warm geomean vs -O2 / -O3", f"{fmt(a.get('compile_warm_geomean_vs_llvm_o2'))} / {fmt(a.get('compile_warm_geomean_vs_llvm_o3'))}"),
        ("compile cold geomean vs -O2", a.get("compile_cold_geomean_vs_llvm_o2")),
        ("emitted-code size geomean / worst vs -O3",
         f"{fmt(a.get('emitted_size_geomean_vs_llvm_o3'), 4)} / {fmt(a.get('emitted_size_worst_vs_llvm_o3'), 4)}"),
        ("size (linked file bytes) geomean / worst vs -O3",
         f"{fmt(a.get('size_geomean_vs_llvm_o3'), 5)} / {fmt(a.get('size_worst_vs_llvm_o3'), 5)}"),
        ("program peak-RSS geomean vs -O3", a.get("rss_geomean_vs_llvm_o3")),
        ("program peak-RSS floor-bound programs / R1 losses (null = unmeasured)",
         f"{a.get('program_rss_floor_bound_count')} / {a.get('program_rss_resolved_loss_count')}"),
        ("compiler peak-RSS geomean vs -O2 / -O3", f"{fmt(a.get('compile_rss_geomean_vs_llvm_o2'))} / {fmt(a.get('compile_rss_geomean_vs_llvm_o3'))}"),
        ("RSS samples per lane (fewest) / largest relative spread program / compiler",
         f"{a.get('rss_min_samples')} / {fmt(a.get('program_rss_max_rel_spread'), 4)} / "
         f"{fmt(a.get('compile_rss_max_rel_spread'), 4)}"),
        ("missing size/RSS readings", ", ".join(a.get("resource_missing") or []) or "none"),
    ]
    lines = [
        f"# beat-llvm evidence — `{p['git_sha'][:12]}` on {p.get('host_model') or 'UNKNOWN CPU'} ({p.get('target')})",
        "",
        f"Retained by `benchmarks/beat-llvm/run.py --retain-dir` at {p.get('timestamp_utc')} from revision",
        f"`{p['git_sha']}`{' (DIRTY tree)' if p.get('git_dirty') else ''}. Host `{p.get('host_name')}`: "
        f"{p.get('host_model') or 'CPU model unavailable'} ({p.get('host_arch')}, "
        f"{p.get('machine_model') or 'machine model unavailable'}), {p.get('os')}.",
        "",
        f"**headline_eligible: {'YES' if eligible else 'NO — NOT EVIDENCE'}**"
        + ("" if eligible else f" (load {p.get('load_status')}, dirty={p.get('git_dirty')}, "
                               f"mismatches={a.get('mismatch_count')}, "
                               f"provenance_complete={p.get('provenance_complete')}, "
                               f"missing={p.get('missing_required_provenance')}; reasons: "
                               f"{'; '.join(res.get('ineligible_reasons') or []) or 'see provenance'})"),
        "",
        "Lanes: " + "; ".join(lanes) + ".",
        "",
        f"CPU policy: `-C target-cpu` {policy.get('target_cpu')}, `-C target-feature` "
        f"{policy.get('target_feature')}, lane parity {policy.get('lane_parity')} "
        f"(bridge adds {policy.get('bridge_extra_flags')}). "
        f"Affinity: {affinity.get('policy')}"
        + (f", core {affinity.get('core')} ({affinity.get('selection')})" if affinity.get("core") is not None else "")
        + f" on a host with heterogeneous cores={affinity.get('heterogeneous')} "
        f"({affinity.get('topology_source')})"
        + f". RSS: {rss.get('method')}; sampler cross-check agree={cross.get('agree')} "
        f"(rusage {cross.get('rusage_bytes')} vs {cross.get('time_wrapper') or 'no /usr/bin/time'} "
        f"{cross.get('time_wrapper_bytes')}); sampler floor {cross.get('sampler_floor_bytes')} bytes "
        f"(readings at or below {a.get('rss_floor_bound_bytes')} bytes are upper bounds, "
        f"not resolved values).",
        "",
        "| metric | value |",
        "|---|---|",
    ]
    lines += [f"| {k} | {'— (not measured)' if v is None else fmt(v) if isinstance(v, float) else v} |"
              for k, v in metrics]
    lines += [
        "",
        "## Files",
        "",
        f"- `{jpath.name}` — the complete results JSON: provenance, per-program outcomes, raw `times_s` samples, ratios, aggregates.",
        f"- `{mpath.name}` — the per-program table as printed by the harness.",
        "- `outcomes.json` — per-input verdict/reason/label (intent-to-treat: INCOMPLETE and MISMATCH rows included).",
        "- `raw_samples.json` — raw compile/run samples, sizes (linked and emitted, with the "
        "emitted-size attribution per section and object), every peak-RSS sample per program "
        "and lane with its sampler status, and the cold lane's per-compile cache population.",
        "- `inventory.json` — byte size and SHA-256 of every file here.",
        "",
        "This directory is the raw evidence behind one ledger row: append the row with",
        f"`python3 scripts/check_perf_ratchet.py --append <results dir>/{jpath.name}`; the row's",
        "`retained_dir` names this directory. The numbers describe the recorded revision, host",
        "and session only; they are not a measurement of the current checkout.",
        "",
    ]
    return "\n".join(lines)


def write_retention(dest, res, jpath, mpath):
    """Copy one run's evidence into `dest` (see plan_retention_dir) with a README
    stub and a hashed inventory, so a committed ledger row can be accompanied
    by its raw samples and per-input outcomes."""
    dest = Path(dest)
    dest.mkdir(parents=True, exist_ok=False)
    shutil.copy2(jpath, dest / jpath.name)
    shutil.copy2(mpath, dest / mpath.name)
    programs = res.get("programs") or {}
    outcomes = {
        stem: {k: row.get(k) for k in ("category", "expected_bridge", "verdict", "reason", "label", "nondet")}
        for stem, row in programs.items()
    }
    raw = {}
    for stem, row in programs.items():
        raw[stem] = {
            "compile": {lane: rec.get("times_s") for lane, rec in (row.get("compile") or {}).items()},
            "cold_cache_entries_after": ((row.get("compile") or {}).get("bridge_cold") or {})
                                        .get("cache_entries_after"),
            "run": {lane: {k: rec.get(k) for k in ("exit", "nondet_exit", "times_s", "median_s", "rel_spread")}
                    for lane, rec in (row.get("run") or {}).items()},
            "size_bytes": row.get("size_bytes"),
            "emitted_size_bytes": row.get("emitted_size_bytes"),
            "emitted_size": row.get("emitted_size"),
            "peak_rss_bytes": row.get("peak_rss_bytes"),
            "compile_peak_rss_bytes": row.get("compile_peak_rss_bytes"),
            "rss_samples": row.get("rss_samples"),
            "ratios": row.get("ratios"),
        }
    (dest / "outcomes.json").write_text(json.dumps(outcomes, indent=1, sort_keys=True) + "\n")
    (dest / "raw_samples.json").write_text(json.dumps(raw, indent=1, sort_keys=True) + "\n")
    (dest / "README.md").write_text(retention_readme(res, jpath, mpath))
    prov = res["provenance"]
    inventory = {
        "generated_by": "benchmarks/beat-llvm/run.py --retain-dir",
        "source_results": jpath.name,
        "git_sha": prov["git_sha"],
        "git_dirty": prov.get("git_dirty"),
        "timestamp_utc": prov.get("timestamp_utc"),
        "headline_eligible": bool(res.get("headline_eligible")),
        "files": {f.name: {"bytes": f.stat().st_size, "sha256": sha256_file(f)}
                  for f in sorted(dest.iterdir()) if f.is_file()},
    }
    (dest / "inventory.json").write_text(json.dumps(inventory, indent=1, sort_keys=True) + "\n")
    return dest


def odd_positive_int(text):
    """argparse type for --n-rss: an odd positive integer (the median of an odd
    number of readings is itself a reading)."""
    value = int(text)
    if value < 1 or value % 2 == 0:
        raise argparse.ArgumentTypeError(f"{value} is not an odd positive integer")
    return value


def parse_args():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=str(REPO_DEFAULT), help="repo root (default: two levels up)")
    ap.add_argument("--dylib", default=None,
                    help="bridge backend (default: the newest of "
                         f"{', '.join(BRIDGE_BACKEND.BUILD_DIRS)} holding "
                         f"{BRIDGE_BACKEND.file_name()})")
    ap.add_argument("--target", default=None,
                    help="target triple for every lane (default: the resolved Trust "
                         "compiler's host)")
    ap.add_argument("--driver", default=None,
                    help="explicit Trust package trustc (default: the PATH trustc/targo package); "
                         "stock and retired-nightly drivers are refused")
    ap.add_argument("--progs", nargs="*", default=None, help="program stems to run (default: all)")
    ap.add_argument("--cold", action="store_true", help="also measure the bridge COLD lane (fresh cache per compile)")
    ap.add_argument("--n-compile", type=int, default=3, help="compile median-of-N (contract default 3)")
    ap.add_argument("--n-run", type=int, default=5, help="runtime median-of-N after 1 warmup (contract default 5)")
    ap.add_argument("--n-rss", type=odd_positive_int, default=check_gates.RSS_CONTRACT_N,
                    help="program and compiler peak-RSS median-of-N per lane, an odd number so "
                         f"the median is a reading (contract default {check_gates.RSS_CONTRACT_N}; "
                         "fewer is never evidence)")
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
    ap.add_argument("--pin-core", nargs="?", const="auto", default=None, metavar="CORE",
                    help="pin the harness and every lane subprocess to one core (Linux "
                         "sched_setaffinity); CORE omitted = the highest-cpu_capacity core, "
                         "as reports/perf/run_scaling.sh selects on big.LITTLE hosts. The "
                         "policy is recorded in provenance either way; an unpinnable host "
                         "is a tooling error (exit 2)")
    ap.add_argument("--bridge-cg-arg", action="append", default=None, metavar="KNOB",
                    help="pass -Ztrust-ir-cg-args=KNOB to every bridge compile (repeatable; "
                         "e.g. no-proof-certs). A DIAGNOSTIC lane: the row is never evidence, and "
                         "the ledger ratchet rejects proof-weakening knobs outright")
    ap.add_argument("--retain-dir", default=None, metavar="DIR",
                    help="also copy the results JSON/markdown, per-program outcomes, raw "
                         "samples and a README stub into DIR/<date>-<rev>/. Use an "
                         "out-of-tree DIR: raw captures are not committed; a committed "
                         "record is a reports/perf/<date>-<rev>/README.md naming the "
                         "run's identities and hashes")
    return ap.parse_args()


if __name__ == "__main__":
    Harness(parse_args()).main()
