#!/usr/bin/env python3
"""Slice 22: the class roots on the REAL builder's bytes (a probe run's `q/` directory, written by
run_probe.sh with S22_CLAIMS=1), replayed one-shot on AY 13556 + Clean 5f09e36c at the lane's
30 s deadline, one solver at a time, as the production replay route credits them: each unit (the
theorem, or each part) whole; a unit without a verdict replayed claim by claim (OD-197's split,
the probe's `<unit>.claim<i>.smt2`), serially, stopping at the first claim that does not certify.
A root closes when every unit is certified whole or credited claim by claim.

Every replay is cached by the sha256 of its bytes in data/replays.jsonl (shared across stages),
so bytes a stage leaves unchanged reuse the earlier measurement (the design's rule).

usage: measure.py <label> <probe out dir>   -> per-root table on stdout, rows in data/roots_<label>.tsv
"""
import collections, glob, hashlib, json, os, sys, time

S = os.path.expanduser("~/tcg-scratch/s22-run")
sys.path.insert(0, os.path.join(S, "scripts"))
import probe_run as P  # noqa: E402

P.PROBE.clear()  # the bridge's exact command line
AY = os.path.expanduser("~/.local/share/trust-overlays/x86-stage1-ay13556/bin/ay")
CLEAN = os.path.expanduser("~/.local/share/trust-overlays/x86-stage1-ay13556/bin/clean")
CACHE = os.path.join(S, "data", "replays.jsonl")


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def load_cache():
    cache = {}
    if os.path.exists(CACHE):
        for line in open(CACHE):
            r = json.loads(line)
            prev = cache.get(r["sha"])
            if prev is None or (r["outcome"] == "certified" and prev["outcome"] != "certified"):
                cache[r["sha"]] = r
    return cache


def replay(path, label, cache):
    h = sha(path)
    if h in cache:
        return cache[h]
    P.gate(sys.stderr)
    text = open(path).read()
    load = round(os.getloadavg()[0], 2)
    t0 = time.time()
    rec = P.run_fresh(AY, CLEAN, text, 30.0, 30.0)
    rec.update({"sha": h, "query": os.path.basename(path), "label": label, "load1": load,
                "t": round(t0, 1), "bytes": len(text)})
    with open(CACHE, "a") as out:
        out.write(json.dumps(rec) + "\n")
    cache[h] = rec
    print(f"  {rec['outcome']:22s} ay={rec.get('ay_s')} clean={rec.get('clean_s', '-')} load={load} "
          f"{os.path.basename(path)}", file=sys.stderr, flush=True)
    return rec


def main():
    label, out = sys.argv[1], sys.argv[2]
    q = os.path.join(out, "q")
    os.makedirs(os.path.join(S, "data"), exist_ok=True)
    cache = load_cache()
    rows = []
    for line in open(os.path.join(q, "index.tsv")):
        parts = line.rstrip("\n").split("\t")
        h, name = parts[0], parts[1]
        n = int(parts[2]) if len(parts) > 2 else 0
        stems = [f"{h}.part{k}" for k in range(1, n + 1)] if n else [h]
        short = name.split("4core")[-1]
        units = []
        for stem in stems:
            rec = replay(os.path.join(q, stem + ".smt2"), label, cache)
            state = "cert" if rec["outcome"] == "certified" else rec["outcome"]
            detail = f"{rec.get('ay_s')}"
            if state != "cert":
                claims = sorted(glob.glob(os.path.join(q, stem + ".claim*.smt2")),
                                key=lambda p: int(p.rsplit(".claim", 1)[1].split(".")[0]))
                if claims:
                    done = 0
                    worst = 0.0
                    for c in claims:
                        cr = replay(c, label, cache)
                        if cr["outcome"] != "certified":
                            break
                        done += 1
                        worst = max(worst, cr.get("ay_s") or 0.0)
                    if done == len(claims):
                        state = "claims"
                        detail = f"{len(claims)} claims, max {worst}"
                    else:
                        detail = f"claim {done + 1}/{len(claims)} {cr['outcome']}"
            units.append((stem, state, detail))
        closed = all(state in ("cert", "claims") for _, state, _ in units)
        rows.append((short, closed, units))
    with open(os.path.join(S, "data", f"roots_{label}.tsv"), "w") as f:
        for short, closed, units in rows:
            f.write(f"{short}\t{'closed' if closed else 'open'}\t" +
                    " ".join(f"{s.split('.')[-1] if '.' in s else 'whole'}={st}({d})" for s, st, d in units) + "\n")
    print(f"| root | units | closed | not closing |")
    print("| --- | ---: | --- | --- |")
    for short, closed, units in rows:
        bad = [f"{s.split('.')[-1] if '.' in s else 'whole'}: {st} {d}" for s, st, d in units if st not in ("cert", "claims")]
        print(f"| `{short}` | {len(units)} | {'yes' if closed else 'no'} | {'; '.join(bad)} |")
    print(f"\nroots closed: {sum(1 for _, c, _ in rows if c)} of {len(rows)}")


if __name__ == "__main__":
    main()
