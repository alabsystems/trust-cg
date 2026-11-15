#!/usr/bin/env python3
"""Slice 17 (copied from slice 16): replay every .smt2 in DIR on AY 0.27.0 b12713 (strict Alethe) + Clean, in parallel,
each within BUDGET seconds (default 30, the live replay budget).

usage: replay_dir.py DIR OUT.tsv [workers]
Outcome per file: VERIFIED | SAT | HOLEY | SELFCHECK | UNKNOWN(...) | CLEANFAIL(...) | TIMEOUT
"""
import concurrent.futures, json, os, subprocess, sys, tempfile, time

AY = os.environ.get("AY", os.path.expanduser("~/.local/share/trust-overlays/x86-stage1-ay12713/bin/ay"))
CLEAN = os.environ.get("CLEAN", os.path.expanduser("~/.local/share/trust-overlays/x86-stage1-ay12713/bin/clean"))
ENV = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
BUDGET = float(os.environ.get("BUDGET", "30"))


def replay(path):
    smt2 = open(path).read()
    started = time.time()
    with tempfile.TemporaryDirectory() as d:
        q, p = os.path.join(d, "q.smt2"), os.path.join(d, "q.alethe")
        open(q, "w").write(smt2)
        try:
            r = subprocess.run(["nice", AY, "-smt2", q, "--strict-proofs", "--proof", p, "--proof-format", "alethe"],
                               capture_output=True, text=True, timeout=BUDGET, env=ENV)
        except subprocess.TimeoutExpired:
            return path, "TIMEOUT", time.time() - started, ""
        out = (r.stdout + r.stderr).splitlines()
        verdict = [l.strip() for l in out if l.strip() in ("sat", "unsat", "unknown")]
        verdict = verdict[-1] if verdict else "?"
        notes = " | ".join(l for l in out if "reason-unknown" in l or "unproved_steps" in l or "MODEL-UNCONFIRMED" in l)[:300]
        if verdict == "sat":
            return path, "SAT", time.time() - started, notes
        if verdict != "unsat":
            kind = "SELFCHECK" if "self-check" in notes else f"UNKNOWN"
            return path, kind, time.time() - started, notes
        if "unproved_steps=0" not in notes:
            return path, "HOLEY", time.time() - started, notes
        cj = os.path.join(d, "cert.json")
        json.dump({"type": "alethe_certificate", "version": "1.0", "problem": smt2, "proof": open(p).read()}, open(cj, "w"))
        try:
            c = subprocess.run(["nice", CLEAN, "cert", "verify-external", cj, "--verbose"],
                               capture_output=True, text=True, timeout=600, env=ENV)
        except subprocess.TimeoutExpired:
            return path, "CLEANTIMEOUT", time.time() - started, notes
        text = c.stdout + c.stderr
        if "verification: PASSED" in text and c.returncode == 0:
            return path, "VERIFIED", time.time() - started, ""
        err = " | ".join(l.strip() for l in text.splitlines() if "Error" in l or "FAILED" in l)[:300]
        return path, "CLEANFAIL", time.time() - started, err


def main():
    d, out = sys.argv[1], sys.argv[2]
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    files = sorted(os.path.join(d, f) for f in os.listdir(d) if f.endswith(".smt2"))
    counts = {}
    with open(out, "w") as o, concurrent.futures.ThreadPoolExecutor(workers) as pool:
        for path, kind, secs, notes in pool.map(replay, files):
            counts[kind] = counts.get(kind, 0) + 1
            o.write(f"{os.path.basename(path)}\t{kind}\t{secs:.1f}\t{notes}\n")
            o.flush()
    print(counts)


main()
