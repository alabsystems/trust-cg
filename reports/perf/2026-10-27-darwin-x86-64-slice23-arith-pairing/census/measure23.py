#!/usr/bin/env python3
"""Slice 23: roots on the REAL builder's bytes (a probe run's `q/` directory, written by
run_probe.sh with S22_CLAIMS=1 S23_GENERAL=1), replayed one-shot on AY 13556 + Clean 5f09e36c at
the lane's 30 s deadline, one solver at a time, as the production replay route credits them
(OD-197 + OD-206): each unit (the theorem, or each part) whole; a unit without a certificate its
generalization (`<unit>.gen.smt2`) once; then claim by claim (`<unit>.claim<i>.smt2`), each claim
without a certificate its generalization (`<unit>.claim<i>.gen.smt2`) once, serially, stopping at
the first claim neither certifies. A root closes when every unit is certified whole, generalized,
or credited claim by claim.

A refuted (sat) exact replay would end the unit (never generalized); a sat generalization is no
verdict. Every replay is cached by the sha256 of its bytes in data/replays.jsonl (shared across
stages), so bytes a stage leaves unchanged reuse the earlier measurement.

usage: measure23.py <label> <probe out dir>   -> per-root table on stdout, rows in data/roots_<label>.tsv
"""
import glob, hashlib, json, os, sys, time

S = os.path.expanduser("~/tcg-scratch/s23-run")
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


def refuted(rec):
    return rec.get("verdict") == "sat"


def unit_route(q, stem, label, cache):
    """(state, detail) of one unit: cert | general | claims | refuted | open."""
    rec = replay(os.path.join(q, stem + ".smt2"), label, cache)
    if rec["outcome"] == "certified":
        return "cert", f"{rec.get('ay_s')}"
    if refuted(rec):
        return "refuted", "exact sat"
    gen = os.path.join(q, stem + ".gen.smt2")
    gen_note = "no generalization"
    if os.path.exists(gen):
        gr = replay(gen, label, cache)
        if gr["outcome"] == "certified":
            return "general", f"generalized {gr.get('ay_s')} (exact {rec['outcome']})"
        gen_note = f"generalized {gr['outcome']}"
    claims = sorted(glob.glob(os.path.join(q, stem + ".claim*.smt2")),
                    key=lambda p: int(p.rsplit(".claim", 1)[1].split(".")[0]))
    claims = [c for c in claims if not c.endswith(".gen.smt2")]
    if not claims:
        return "open", f"exact {rec['outcome']}; {gen_note}"
    done, worst, generalized = 0, 0.0, 0
    for c in claims:
        cr = replay(c, label, cache)
        if cr["outcome"] == "certified":
            done += 1
            worst = max(worst, cr.get("ay_s") or 0.0)
            continue
        if refuted(cr):
            return "refuted", f"claim {done + 1}/{len(claims)} sat"
        cg = c[:-len(".smt2")] + ".gen.smt2"
        if os.path.exists(cg):
            gr = replay(cg, label, cache)
            if gr["outcome"] == "certified":
                done += 1
                generalized += 1
                worst = max(worst, gr.get("ay_s") or 0.0)
                continue
            return "open", (f"exact {rec['outcome']}; {gen_note}; claim {done + 1}/{len(claims)} "
                            f"{cr['outcome']}, generalized {gr['outcome']}")
        return "open", (f"exact {rec['outcome']}; {gen_note}; claim {done + 1}/{len(claims)} "
                        f"{cr['outcome']}, no generalization")
    return "claims", f"{len(claims)} claims ({generalized} generalized), max {worst}"


def theorem_route(q, stems, label, cache):
    """Units serially, stopping at the first that does not close (OD-182)."""
    units = []
    for stem in stems:
        st, d = unit_route(q, stem, label, cache)
        units.append((stem, st, d))
        if st not in ("cert", "general", "claims"):
            break
    return units


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
        units = theorem_route(q, stems, label, cache)
        # OD-205: a refuted paired theorem is decided by the theorem without
        # the pairing (`<h>.unpaired[.part<k>].smt2`), when the probe wrote one.
        if any(state == "refuted" for _, state, _ in units):
            un = sorted(glob.glob(os.path.join(q, f"{h}.unpaired*.smt2")))
            un = [os.path.basename(u)[:-len(".smt2")] for u in un
                  if ".claim" not in u and not u.endswith(".gen.smt2")]
            if un:
                un.sort(key=lambda s: int(s.rsplit(".part", 1)[1]) if ".part" in s else 0)
                units = [(f"[unpaired] {s}", st, d) for s, st, d in theorem_route(q, un, label, cache)]
        closed = all(state in ("cert", "general", "claims") for _, state, _ in units)
        rows.append((short, closed, units))
    with open(os.path.join(S, "data", f"roots_{label}.tsv"), "w") as f:
        for short, closed, units in rows:
            f.write(f"{short}\t{'closed' if closed else 'open'}\t" +
                    " ".join(f"{s.split('.')[-1] if '.' in s else 'whole'}={st}({d})" for s, st, d in units) + "\n")
    print("| root | units | closed | how |")
    print("| --- | ---: | --- | --- |")
    for short, closed, units in rows:
        how = "; ".join(f"{s.split('.')[-1] if '.' in s else 'whole'}: {st} {d}" for s, st, d in units)
        print(f"| `{short}` | {len(units)} | {'yes' if closed else 'no'} | {how} |")
    print(f"\nroots closed: {sum(1 for _, c, _ in rows if c)} of {len(rows)}")


if __name__ == "__main__":
    main()
