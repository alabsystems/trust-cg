#!/usr/bin/env python3
"""Sequential, resumable offline replays of query files through
~/tcg-scratch/ay-nd/runs/replay_nd.py's two routes (one solver at a time).

Before each query it waits while ~/tcg-scratch/quiet.request exists or a
trust-cg census runs (`pgrep -f "[t]rust_ir_cg_census"`). A quiet.request
whose writer is dead (older than QUIET_STALE_H hours and no land_quiet /
land_loop process alive) is logged and not waited on.

usage: run_replays.py --ay AY --clean CLEAN --route fresh|resident --label L
                      --qdir DIR --out OUT.jsonl [--budget-s 30] FILE...
"""
import argparse, json, os, subprocess, sys, time
sys.path.insert(0, os.path.expanduser("~/tcg-scratch/ay-nd/runs"))
import replay_nd as R

QUIET = os.path.expanduser("~/tcg-scratch/quiet.request")
QUIET_STALE_H = 6.0


def alive(pattern):
    return subprocess.run(["pgrep", "-f", pattern], capture_output=True).returncode == 0


def gate(log):
    waited = False
    while True:
        reasons = []
        if os.path.exists(QUIET):
            try:
                age_h = (time.time() - os.path.getmtime(QUIET)) / 3600
            except OSError:
                age_h = 0
            if age_h > QUIET_STALE_H and not alive("[l]and_quiet|[l]and_loop|[q]ual_live"):
                print(f"# quiet.request is {age_h:.1f} h old with no writer alive: not waiting", file=log, flush=True)
            else:
                reasons.append("quiet.request")
        if alive("[t]rust_ir_cg_census"):
            reasons.append("census")
        if not reasons:
            if waited:
                print(f"# resumed {time.strftime('%H:%M:%S')}", file=log, flush=True)
            return
        if not waited:
            print(f"# waiting ({','.join(reasons)}) {time.strftime('%H:%M:%S')}", file=log, flush=True)
            waited = True
        time.sleep(30)


def run_fresh(ay, clean, query, budget_s):
    """replay_nd.run_fresh, with a Clean that overruns the budget recorded
    as `clean-timeout` (replay_nd lets the TimeoutExpired escape)."""
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        q = os.path.join(d, "q.smt2")
        with open(q, "w") as f:
            f.write(query)
        proof = q + ".alethe"
        cmd = [ay, "-smt2", q, "--strict-proofs", "--proof", proof, "--proof-format", "alethe"]
        t0 = time.monotonic()
        try:
            p = subprocess.run(cmd, env=R.child_env(), capture_output=True, text=True, timeout=budget_s)
        except subprocess.TimeoutExpired:
            return {"outcome": "timeout", "ay_s": round(time.monotonic() - t0, 3)}
        ay_s = round(time.monotonic() - t0, 3)
        lines = [l.strip() for l in p.stdout.splitlines() if l.strip()]
        verdicts = [l for l in lines if l in ("sat", "unsat", "unknown")]
        rec = {"ay_s": ay_s, "exit": p.returncode, "verdict": verdicts, "detail": R.key_line(p.stderr)}
        if verdicts != ["unsat"] or p.returncode != 0:
            rec["outcome"] = "not-certified"
            return rec
        for line in p.stderr.splitlines():
            if line.startswith("c ay.proof.certificate ") and (
                    "unproved_steps=0" not in line or "trust_free=yes" not in line):
                rec["outcome"] = "incomplete-certificate"
                return rec
        try:
            proof_text = open(proof).read()
        except OSError as e:
            rec["outcome"] = f"no-proof ({e})"
            return rec
        rec["proof_bytes"] = len(proof_text)
        j = os.path.join(d, "cert.json")
        with open(j, "w") as f:
            json.dump({"type": "alethe_certificate", "version": "1.0", "problem": query, "proof": proof_text}, f)
        t1 = time.monotonic()
        try:
            c = subprocess.run([clean, "cert", "verify-external", j, "--verbose"], env=R.child_env(),
                               capture_output=True, text=True, timeout=budget_s)
        except subprocess.TimeoutExpired:
            rec["clean_s"] = round(time.monotonic() - t1, 3)
            rec["outcome"] = "clean-timeout"
            return rec
        rec["clean_s"] = round(time.monotonic() - t1, 3)
        out = [l.strip().lower() for l in c.stdout.splitlines()]
        ok = (c.returncode == 0 and "proof status: fully verified" in out
              and not any("failed" in l or "holey" in l or "incomplete" in l for l in out))
        rec["outcome"] = "certified" if ok else "checker-rejected"
        return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ay", required=True)
    ap.add_argument("--clean", default=os.path.expanduser("~/clean-checker/bin/clean"))
    ap.add_argument("--route", choices=["fresh", "resident"], required=True)
    ap.add_argument("--label", required=True)
    ap.add_argument("--qdir", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--budget-s", type=float, default=30.0)
    ap.add_argument("files", nargs="+")
    a = ap.parse_args()
    done = set()
    if os.path.exists(a.out):
        for line in open(a.out):
            try:
                done.add(json.loads(line)["query"])
            except Exception:
                pass
    log = sys.stderr
    with open(a.out, "a") as out:
        for i, f in enumerate(a.files):
            if f in done:
                continue
            gate(log)
            text = open(os.path.join(a.qdir, f)).read()
            t0 = time.time()
            if a.route == "fresh":
                rec = run_fresh(a.ay, a.clean, text, a.budget_s)
            else:
                rec = R.run_resident(a.ay, text, a.budget_s)
            rec.update({"query": f, "route": a.route, "label": a.label, "ay": os.path.basename(a.ay),
                        "budget_s": a.budget_s, "load1": round(os.getloadavg()[0], 2), "t": round(t0, 1)})
            out.write(json.dumps(rec) + "\n")
            out.flush()
            print(f"[{i+1}/{len(a.files)}] {rec['outcome']:22s} ay={rec.get('ay_s','-')} clean={rec.get('clean_s','-')} {f[:80]}",
                  file=log, flush=True)


if __name__ == "__main__":
    main()
