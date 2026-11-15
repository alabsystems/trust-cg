#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""A/T/B measurement of TY native preparation on the 40 semantic-exact rows.

Holds the MEASURE side of ~/.ty/build.lock (ticket + LOCK_EX, the
corpus_rescreen.BoxLock protocol) for the whole run. Each observation is
`/usr/bin/time -l <ty> <census argv> --source-compile-diagnostic --max-states 1`;
binaries are interleaved per (row, rep) in rotating order. Records rc,
instructions retired, cycles elapsed, peak memory footprint, max RSS, and an
identity digest of the JSON result (status, statistics without timings, and
the source-compile-diagnostic provenance).
"""
import errno
import fcntl
import hashlib
import json
import os
import re
import statistics
import subprocess
import sys
import time
from pathlib import Path

HOME = Path.home()
LOCK_DIR = HOME / ".ty"
GATE = LOCK_DIR / "build.lock"
PEND = LOCK_DIR / "measure.pending"
CENSUS = Path("$HOME/ty/reports/perf/2026-09-25-semantic-lane-standard-instance/census.json")


class Lock:
    def __init__(self, label):
        self.label = label
        self.ticket = PEND / f"{os.getpid()}.ticket"
        self.fd = None

    def _ticket(self):
        PEND.mkdir(parents=True, exist_ok=True)
        self.ticket.write_text(f"{self.label} pid={os.getpid()} since={time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        os.utime(self.ticket, None)

    def acquire(self):
        LOCK_DIR.mkdir(parents=True, exist_ok=True)
        self.fd = os.open(str(GATE), os.O_RDWR | os.O_CREAT, 0o644)
        t0 = time.time()
        self._ticket()
        while True:
            try:
                fcntl.flock(self.fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                pass
            except OSError as exc:
                if exc.errno not in (errno.EAGAIN, errno.EWOULDBLOCK):
                    raise
            self._ticket()
            time.sleep(5)
        waited = int(time.time() - t0)
        try:
            self.ticket.unlink()
        except FileNotFoundError:
            pass
        os.ftruncate(self.fd, 0)
        os.pwrite(self.fd, f"{self.label} pid={os.getpid()} since={time.strftime('%Y-%m-%d %H:%M:%S')}\n".encode(), 0)
        print(f"[lock] acquired after {waited}s", flush=True)
        return waited

    def release(self):
        if self.fd is None:
            return
        try:
            self.ticket.unlink()
        except FileNotFoundError:
            pass
        os.ftruncate(self.fd, 0)
        fcntl.flock(self.fd, fcntl.LOCK_UN)
        os.close(self.fd)
        self.fd = None


TIME_KEYS = {
    "instructions retired": "instructions",
    "cycles elapsed": "cycles",
    "peak memory footprint": "peak_footprint",
    "maximum resident set size": "max_rss",
}


def strip_volatile(x):
    if isinstance(x, dict):
        return {k: strip_volatile(v) for k, v in x.items()
                if not any(s in k for s in ("time", "timestamp", "_ms", "per_second", "elapsed", "duration", "nanos"))}
    if isinstance(x, list):
        return [strip_volatile(v) for v in x]
    return x


def identity(stdout):
    try:
        d = json.loads(stdout)
    except Exception:
        return "unparsable:" + hashlib.sha256(stdout.encode()).hexdigest()[:16], None
    core = {
        "result": strip_volatile(d.get("result")),
        "statistics": strip_volatile(d.get("statistics")),
        "scd": strip_volatile((d.get("engine_provenance") or {}).get("source_compile_diagnostic")),
    }
    blob = json.dumps(core, sort_keys=True)
    return hashlib.sha256(blob.encode()).hexdigest()[:16], core


def run(binary, argv, timeout):
    cmd = ["/usr/bin/time", "-l", binary, *argv[0:], "--source-compile-diagnostic", "--max-states", "1"]
    import shutil, tempfile
    cache = tempfile.mkdtemp(prefix="typrep-cache-", dir=os.environ.get("TYPREP_TMP"))
    env = dict(os.environ, TY_DISABLE_ARTIFACT_CACHE="1", TY_CACHE_DIR=cache)
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        shutil.rmtree(cache, ignore_errors=True)
        return {"rc": "timeout", "wall": time.time() - t0}
    wall = time.time() - t0
    shutil.rmtree(cache, ignore_errors=True)
    out = {"rc": p.returncode, "wall": wall}
    for line in p.stderr.splitlines():
        m = re.match(r"\s*(\d+)\s+(.+?)\s*$", line)
        if m and m.group(2) in TIME_KEYS:
            out[TIME_KEYS[m.group(2)]] = int(m.group(1))
    ident, core = identity(p.stdout)
    out["identity"] = ident
    out["status"] = (core or {}).get("result", {}).get("status") if core else None
    out["strict_exactness"] = ((core or {}).get("scd") or {}).get("strict_exactness") if core else None
    out["shadow_status"] = (((core or {}).get("scd") or {}).get("shadow") or {}).get("status") if core else None
    armed = [l for l in p.stderr.splitlines() if l.startswith("[semantic-generator]")]
    out["semantic_generator"] = armed[0][:200] if armed else None
    return out


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", action="append", required=True, help="TAG=PATH")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--timeout", type=int, default=180)
    ap.add_argument("--out", required=True)
    ap.add_argument("--rows", nargs="*")
    args = ap.parse_args()
    bins = [tuple(b.split("=", 1)) for b in args.bin]
    census = json.loads(CENSUS.read_text())
    rows = {r["row"]: r for r in census["rows"]}
    exact = args.rows or census["exact_rows"]
    lock = Lock("compile-speed ty-prep A/T/B")
    waited = lock.acquire()
    started = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    load0 = os.getloadavg()
    results = {}
    try:
        for i, row in enumerate(exact):
            argv = rows[row]["argv"]
            results[row] = {tag: [] for tag, _ in bins}
            for rep in range(args.reps):
                order = bins[(i + rep) % len(bins):] + bins[:(i + rep) % len(bins)]
                for tag, path in order:
                    results[row][tag].append(run(path, argv, args.timeout))
            summ = " ".join(
                f"{tag}={statistics.median([o.get('instructions', 0) for o in results[row][tag]]) / 1e6:.0f}M"
                for tag, _ in bins)
            ids = {tag: {o["identity"] for o in results[row][tag]} for tag, _ in bins}
            print(f"[{i + 1}/{len(exact)}] {row}: {summ} ids={ {k: sorted(v) for k, v in ids.items()} }", flush=True)
    finally:
        lock.release()
    doc = {
        "schema": "compile-speed.ty-prep.v1",
        "bins": dict(bins),
        "reps": args.reps,
        "argv_suffix": ["--source-compile-diagnostic", "--max-states", "1"],
        "census": str(CENSUS),
        "lock_waited_s": waited,
        "started": started,
        "finished": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "loadavg_start": load0,
        "loadavg_end": os.getloadavg(),
        "rows": results,
    }
    Path(args.out).write_text(json.dumps(doc, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
