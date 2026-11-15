#!/usr/bin/env python3
"""(slice-19 copy of ~/tcg-scratch/ay-fix/land3/replay3.py: the host gate
before every query is widened to the slice-19 measurement's -- quiet.request,
a trust-cg census, or ANY other AY solver process -- so one solver runs at a
time on the host; everything else is replay3.py's, byte for byte.)

(land3 copy of ~/tcg-scratch/ay-nd/runs/replay_nd.py: a Clean timeout is an
outcome, `checker-timeout`, not an exception that ends the corpus.)

Replay dumped source-bound body queries through AY the way the trust-cg
bridge does, N times each, and classify every run.

Routes (the two the bridge's live replay takes):
  fresh     `<ay> -smt2 Q --strict-proofs --proof Q.alethe --proof-format alethe`
            (ay_bridge::solver_command, SolverEvidenceRequest::Alethe), then the
            exact proof is replayed by `<clean> cert verify-external J --verbose`
            (obligation_cert_store::run_clean_verify_external_with_env).
  resident  one `<ay> --incremental` process per run, fed the query minus its
            trailing `(exit)`, then `(echo "==S==")` and `(reset)`
            (ay_bridge::run_solver_via_server_with_authority); a resident
            `unsat` is only a candidate (the bridge replays it fresh), so it is
            reported as `resident-unsat`.

The child environment is the bridge's sanitized one (PATH=/usr/bin:/bin,
LANG=LC_ALL=C, TMPDIR). Output: one JSON line per run.
"""
import argparse, json, os, subprocess, sys, tempfile, time, concurrent.futures


def child_env():
    env = {"PATH": "/usr/bin:/bin", "LANG": "C", "LC_ALL": "C"}
    for k in ("TMPDIR", "TMP", "TEMP", "GOVERN_AY_MB", "AY_CONCURRENCY"):
        if k in os.environ:
            env[k] = os.environ[k]
    return env


def key_line(stderr):
    for needle in ("strict UNSAT proof validation failed", "computed UNSAT rejected",
                   ":reason-unknown", "c ay.proof.certificate", "SOUNDNESS GATE"):
        for line in stderr.splitlines():
            if needle in line:
                return line.strip()[:300]
    return stderr.strip().splitlines()[-1][:300] if stderr.strip() else ""


def run_fresh(ay, clean, query, budget_s):
    with tempfile.TemporaryDirectory() as d:
        q = os.path.join(d, "q.smt2")
        with open(q, "w") as f:
            f.write(query)
        proof = q + ".alethe"
        cmd = [ay, "-smt2", q, "--strict-proofs", "--proof", proof, "--proof-format", "alethe"]
        t0 = time.monotonic()
        try:
            p = subprocess.run(cmd, env=child_env(), capture_output=True, text=True, timeout=budget_s)
        except subprocess.TimeoutExpired:
            return {"outcome": "timeout", "ay_s": round(time.monotonic() - t0, 3)}
        ay_s = round(time.monotonic() - t0, 3)
        lines = [l.strip() for l in p.stdout.splitlines() if l.strip()]
        verdicts = [l for l in lines if l in ("sat", "unsat", "unknown")]
        rec = {"ay_s": ay_s, "exit": p.returncode, "verdict": verdicts, "detail": key_line(p.stderr)}
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
        j = os.path.join(d, "cert.json")
        with open(j, "w") as f:
            json.dump({"type": "alethe_certificate", "version": "1.0", "problem": query, "proof": proof_text}, f)
        t1 = time.monotonic()
        try:
            c = subprocess.run([clean, "cert", "verify-external", j, "--verbose"], env=child_env(),
                               capture_output=True, text=True, timeout=budget_s)
        except subprocess.TimeoutExpired:
            # land3 copy: a checker that runs past the budget is recorded, not raised.
            rec["clean_s"] = round(time.monotonic() - t1, 3)
            rec["outcome"] = "checker-timeout"
            return rec
        rec["clean_s"] = round(time.monotonic() - t1, 3)
        out = [l.strip().lower() for l in c.stdout.splitlines()]
        ok = (c.returncode == 0 and "proof status: fully verified" in out
              and not any("failed" in l or "holey" in l or "incomplete" in l for l in out))
        rec["outcome"] = "certified" if ok else "checker-rejected"
        return rec


def run_resident(ay, query, budget_s):
    body = query.rstrip("\n")
    if not body.endswith("(exit)"):
        return {"outcome": "no-exit-suffix"}
    body = body[: -len("(exit)")]
    script = f'{body}\n(echo "==S==")\n(reset)\n'
    t0 = time.monotonic()
    try:
        p = subprocess.run([ay, "--incremental"], input=script, env=child_env(), capture_output=True,
                           text=True, timeout=budget_s)
    except subprocess.TimeoutExpired:
        return {"outcome": "timeout", "ay_s": round(time.monotonic() - t0, 3)}
    lines = [l.strip() for l in p.stdout.splitlines() if l.strip()]
    verdicts = [l for l in lines if l in ("sat", "unsat", "unknown")]
    rec = {"ay_s": round(time.monotonic() - t0, 3), "verdict": verdicts,
           "detail": next((l for l in lines if ":reason-unknown" in l), "")}
    rec["outcome"] = {("unsat",): "resident-unsat", ("unknown",): "resident-unknown"}.get(tuple(verdicts), "other")
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ay", required=True)
    ap.add_argument("--clean", required=True)
    ap.add_argument("--route", choices=["fresh", "resident"], default="fresh")
    ap.add_argument("--runs", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=1, help="concurrent replays (1 = at rest)")
    ap.add_argument("--budget-s", type=float, default=45.0)
    ap.add_argument("--label", default="")
    ap.add_argument("queries", nargs="+")
    a = ap.parse_args()
    work = [(q, r) for r in range(a.runs) for q in a.queries]

    def quiet():
        # land3 copy (coordinator, 2026-10-19): no query starts while a trust-cg
        # census runs or ~/tcg-scratch/quiet.request exists; the loop ends when
        # the census process is gone, whether it finished or died.
        # slice-19 copy: nor while any other AY solver process runs (the
        # slice-19 measurement's gate), so one solver runs at a time.
        other_ay = r"[/]ay(-[A-Za-z0-9]+)* +(-smt2|--incremental|solve)"
        alive = lambda pattern: subprocess.run(["pgrep", "-f", pattern], capture_output=True).returncode == 0
        while (alive("[t]rust_ir_cg_census|[c]ensus12713|[c]ensus13556|[g]ates_then_census")
               or alive(other_ay) or alive("[a]y-merged")
               or os.path.exists(os.path.expanduser("~/tcg-scratch/quiet.request"))):
            time.sleep(15)

    def one(item):
        q, r = item
        quiet()
        text = open(q).read()
        rec = run_fresh(a.ay, a.clean, text, a.budget_s) if a.route == "fresh" else run_resident(a.ay, text, a.budget_s)
        rec.update({"query": os.path.basename(q), "run": r, "route": a.route, "jobs": a.jobs,
                    "label": a.label, "load1": round(os.getloadavg()[0], 2), "t": round(time.time(), 1)})
        return rec

    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        for rec in pool.map(one, work):
            print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    sys.exit(main())
