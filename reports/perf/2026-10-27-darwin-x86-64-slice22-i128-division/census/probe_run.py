#!/usr/bin/env python3
"""Replays like run.py (the bridge's one-shot and resident routes, one solver
at a time), with AY's `--probe-cert-reject` notes captured as a TIMELINE:
every stderr line of the probe channel is stamped with the seconds since the
AY process started, so the wall time of each raw-ground-closure attempt (and
of the passes between them) is read off the run itself.

  fresh     ay -smt2 Q --strict-proofs --proof P --proof-format alethe
            --probe-cert-reject, then `clean cert verify-external` (30 s);
  resident  ay --incremental --probe-cert-reject, fed the query minus its
            trailing (exit), then (echo "==S==") and (reset).

The AY process is killed at the budget + 2 s (so AY's own `:timeout` answer
and the notes it prints at the deadline are kept); the outcome is judged
against the budget: a verdict after it is a timeout.  stdout is streamed too,
so `verdict_s` is when AY printed its verdict.

Gate before every run (run.py's, widened): ~/tcg-scratch/quiet.request, a
trust-cg census, or any other AY solver process.
"""
import argparse, json, os, re, subprocess, sys, tempfile, threading, time

QUIET = os.path.expanduser("~/tcg-scratch/quiet.request")
OTHER_AY = r"[/]ay(-[A-Za-z0-9]+)* +(-smt2|--incremental|solve)"


def child_env():
    env = {"PATH": "/usr/bin:/bin", "LANG": "C", "LC_ALL": "C"}
    for k in ("TMPDIR", "TMP", "TEMP"):
        if k in os.environ:
            env[k] = os.environ[k]
    return env


def alive(pattern):
    return subprocess.run(["pgrep", "-f", pattern], capture_output=True).returncode == 0


def gate(log):
    waited = False
    while True:
        reasons = []
        if os.path.exists(QUIET):
            reasons.append("quiet.request")
        if alive("[t]rust_ir_cg_census"):
            reasons.append("census")
        if alive(OTHER_AY) or alive("[a]y-merged"):
            reasons.append("another AY")
        if not reasons:
            if waited:
                print(f"# resumed {time.strftime('%H:%M:%S')}", file=log, flush=True)
            return
        if not waited:
            print(f"# waiting ({','.join(reasons)}) {time.strftime('%H:%M:%S')}", file=log, flush=True)
            waited = True
        time.sleep(10)


def stream(proc, stdin_text, kill_at):
    """Run proc to completion or kill_at seconds; return (stdout_lines,
    stderr_lines) as [(t, line)] stamped from t0."""
    t0 = time.monotonic()
    out, err = [], []

    def pump(fh, acc):
        for line in iter(fh.readline, ""):
            acc.append((round(time.monotonic() - t0, 3), line.rstrip("\n")))
        fh.close()

    ths = [threading.Thread(target=pump, args=(proc.stdout, out), daemon=True),
           threading.Thread(target=pump, args=(proc.stderr, err), daemon=True)]
    for t in ths:
        t.start()
    if stdin_text is not None:
        try:
            proc.stdin.write(stdin_text)
            proc.stdin.close()
        except BrokenPipeError:
            pass
    killed = False
    try:
        proc.wait(timeout=kill_at)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()
        killed = True
    for t in ths:
        t.join(timeout=5)
    return out, err, round(time.monotonic() - t0, 3), killed


def notes(err):
    keep = []
    for t, l in err:
        if l.startswith("--probe-cert-reject:") or l.startswith("(:reason") or "ay.proof.certificate" in l \
                or "SOUNDNESS" in l or "validation failed" in l:
            keep.append([t, l.replace("--probe-cert-reject: ", "")[:200]])
    return keep


def closure_summary(nts):
    c = [x for x in nts if x[1].startswith("raw ground closure:")]
    declined = [x for x in c if "no conflict" in x[1] or "declined" in x[1] or "refused" in x[1]
                or "no raw roots" in x[1] or "not a pure" in x[1]]
    committed = [x for x in c if "committed" in x[1]]
    return {"closure_notes": len(c), "closure_declined": len(declined), "closure_committed": len(committed),
            "closure_t": [x[0] for x in c]}


def verdict_of(out):
    for t, l in out:
        if l.strip() in ("sat", "unsat", "unknown"):
            return l.strip(), t
    return None, None


PROBE = ["--probe-cert-reject"]
STRICT = ["--strict-proofs"]


def run_fresh(ay, clean, query, budget_s, clean_s):
    with tempfile.TemporaryDirectory() as d:
        q = os.path.join(d, "q.smt2")
        open(q, "w").write(query)
        proof = q + ".alethe"
        cmd = [ay, "-smt2", q] + STRICT + ["--proof", proof, "--proof-format", "alethe"] + PROBE
        p = subprocess.Popen(cmd, env=child_env(), stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True)
        out, err, ay_s, killed = stream(p, None, budget_s + 2)
        v, vt = verdict_of(out)
        nts = notes(err)
        rec = {"ay_s": ay_s, "verdict": v, "verdict_s": vt, "killed": killed, "exit": p.returncode}
        rec.update(closure_summary(nts))
        rec["notes"] = nts
        cert = [l for _, l in err if l.startswith("c ay.proof.certificate ")]
        if v != "unsat" or vt is None or vt > budget_s:
            rec["outcome"] = "timeout" if (v in (None, "unknown") and ay_s >= budget_s - 1) or (vt and vt > budget_s) \
                else "not-certified"
            return rec
        if any("unproved_steps=0" not in l or "trust_free=yes" not in l for l in cert):
            rec["outcome"] = "incomplete-certificate"
            return rec
        try:
            proof_text = open(proof).read()
        except OSError as e:
            rec["outcome"] = f"no-proof ({e})"
            return rec
        rec["proof_bytes"] = len(proof_text)
        if clean is None:
            rec["outcome"] = "ay-unsat (Clean not run)"
            return rec
        j = os.path.join(d, "cert.json")
        json.dump({"type": "alethe_certificate", "version": "1.0", "problem": query, "proof": proof_text}, open(j, "w"))
        t1 = time.monotonic()
        try:
            c = subprocess.run([clean, "cert", "verify-external", j, "--verbose"], env=child_env(),
                               capture_output=True, text=True, timeout=clean_s)
        except subprocess.TimeoutExpired:
            rec["clean_s"] = round(time.monotonic() - t1, 3)
            rec["outcome"] = "clean-timeout"
            return rec
        rec["clean_s"] = round(time.monotonic() - t1, 3)
        o = [l.strip().lower() for l in c.stdout.splitlines()]
        ok = (c.returncode == 0 and "proof status: fully verified" in o
              and not any("failed" in l or "holey" in l or "incomplete" in l for l in o))
        rec["outcome"] = "certified" if ok else "checker-rejected"
        if not ok:
            rec["clean_detail"] = (c.stdout + c.stderr).strip()[-300:]
        return rec


def run_resident(ay, query, budget_s):
    body = query.rstrip("\n")
    if not body.endswith("(exit)"):
        return {"outcome": "no-exit-suffix"}
    body = body[: -len("(exit)")]
    script = f'{body}\n(echo "==S==")\n(reset)\n'
    p = subprocess.Popen([ay, "--incremental"] + PROBE, env=child_env(), stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    out, err, ay_s, killed = stream(p, script, budget_s + 2)
    v, vt = verdict_of(out)
    nts = notes(err)
    rec = {"ay_s": ay_s, "verdict": v, "verdict_s": vt, "killed": killed}
    rec.update(closure_summary(nts))
    rec["notes"] = nts
    if v == "unsat" and vt is not None and vt <= budget_s:
        rec["outcome"] = "resident-unsat"
    elif v in (None, "unknown") or (vt and vt > budget_s):
        rec["outcome"] = "timeout" if (vt is None or vt >= budget_s - 1) else "resident-unknown"
    else:
        rec["outcome"] = "resident-" + v
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ay", default=os.path.expanduser("~/.local/share/trust-overlays/x86-stage1-ay13556/bin/ay"))
    ap.add_argument("--clean", default=os.path.expanduser("~/clean-checker/bin/clean"))
    ap.add_argument("--no-clean", action="store_true")
    ap.add_argument("--no-probe", action="store_true", help="control: the bridge's exact command line")
    ap.add_argument("--no-strict", action="store_true", help="AY's default rigor (standard) instead of --strict-proofs; the certificate line and Clean still judge")
    ap.add_argument("--route", choices=["fresh", "resident"], default="fresh")
    ap.add_argument("--label", required=True)
    ap.add_argument("--qdir", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--runs", type=int, default=1)
    ap.add_argument("--budget-s", type=float, default=30.0)
    ap.add_argument("--clean-s", type=float, default=30.0)
    ap.add_argument("files", nargs="+")
    a = ap.parse_args()
    if a.no_probe:
        PROBE.clear()
    if a.no_strict:
        STRICT.clear()
    done = set()
    if os.path.exists(a.out):
        for line in open(a.out):
            try:
                r = json.loads(line)
                done.add((r["query"], r.get("run", 0), r.get("label"), r.get("route")))
            except Exception:
                pass
    with open(a.out, "a") as out:
        for run in range(a.runs):
            for i, f in enumerate(a.files):
                if (f, run, a.label, a.route) in done:
                    continue
                gate(sys.stderr)
                text = open(os.path.join(a.qdir, f)).read()
                if a.budget_s != 30.0:
                    text = re.sub(r"\(set-option :timeout \d+\)", f"(set-option :timeout {int(a.budget_s*1000)})", text, count=1)
                load = round(os.getloadavg()[0], 2)
                t0 = time.time()
                if a.route == "fresh":
                    rec = run_fresh(a.ay, None if a.no_clean else a.clean, text, a.budget_s, a.clean_s)
                else:
                    rec = run_resident(a.ay, text, a.budget_s)
                rec["qdir"] = os.path.relpath(os.path.abspath(a.qdir), os.path.expanduser("~/tcg-scratch/s22-design/queries"))
                rec.update({"query": f, "run": run, "route": a.route, "label": a.label, "ay": os.path.basename(a.ay),
                            "budget_s": a.budget_s, "load1": load, "t": round(t0, 1)})
                out.write(json.dumps(rec) + "\n")
                out.flush()
                print(f"[{run}:{i+1}/{len(a.files)}] {rec['outcome']:22s} ay={rec.get('ay_s')} v@{rec.get('verdict_s')} "
                      f"clean={rec.get('clean_s','-')} closures={rec.get('closure_notes')}/{rec.get('closure_declined')}d "
                      f"load={load} {f[:80]}", file=sys.stderr, flush=True)


if __name__ == "__main__":
    main()
