#!/usr/bin/env python3
"""Slice 19 golden review: per golden file, every theorem that changed, checked against its
old spelling two independent ways (the slice-18 review's, smtq.py's parser and evaluator):
  * an evaluation sweep, 256 seeded inputs of the old theorem's free inputs: equal claim
    values, and every definition the new theorem keeps equal to the old definition of that
    name;
  * z3, both directions (z3_equiv.py's A and B queries), each UNSAT within 60 s.
A parts golden (sections `<shape> | part k of n`) is compared per shape: the conjunction of a
shape's parts (their definitions united: every part defines a name as the statement does),
since a part the new spelling empties drops out and renumbers the rest.
usage: review19.py <old dir> <new dir> <out dir>
Writes <out dir>/review.jsonl and prints a per-file table."""
import json, os, random, re, subprocess, sys, zlib
sys.path.insert(0, os.path.expanduser('~/tcg-scratch/s18-design/scripts'))
import smtq as S

old_dir, new_dir, out = sys.argv[1:4]
os.makedirs(os.path.join(out, 'z3'), exist_ok=True)

def sections(text):
    chunks = re.split(r"^;;;; (.*)$", text, flags=re.M)
    return [(chunks[k].strip(), chunks[k + 1].strip('\n')) for k in range(1, len(chunks), 2)]

class Th:
    """A theorem: free inputs, definitions (in order), source, machine (or the union of parts)."""
    def __init__(self, texts):
        self.free, self.defs, claims = [], [], []
        self.decls = {}
        seen_free = set(); defined = {}
        self.source = None
        for t in texts:
            q = S.Query(t); th = S.Theorem(q)
            for n, w in q.decls:
                self.decls[n] = w
            for n, w in th.free:
                if n not in seen_free:
                    seen_free.add(n); self.free.append((n, w))
            for n, e in th.defs:
                if n not in defined:
                    defined[n] = e; self.defs.append((n, e))
            claims.append(S.mk("=", (th.source, th.machine)))
            if len(texts) == 1:
                self.source, self.machine = th.source, th.machine
        self.claim = claims[0] if len(claims) == 1 else S.conj_right(claims)
        self.one = len(texts) == 1

def evaluate(th, env):
    vals = dict(env); memo = {}
    for n, e in th.defs:
        vals[n] = S.evaluate(e, vals, memo)
    return S.evaluate(th.claim, vals, memo), vals

def sweep(old, new, seed):
    rng = random.Random(seed)
    mm = fc = 0
    newfree = {n for n, _ in new.free}
    assert newfree <= {n for n, _ in old.free}, "the new theorem reads a new free input"
    for _ in range(256):
        env = {n: S.random_value(w, rng) if w else rng.randrange(2) for n, w in old.free}
        v1, x1 = evaluate(old, env); v2, x2 = evaluate(new, env)
        if v1 != v2 or any(x1[n] != x2[n] for n, _ in new.defs):
            mm += 1
        fc += not v1
    return mm, fc

def z3q(old, new, base):
    def defs_term(defs):
        leaves = [S.mk("=", (S.var(n, S.WIDTH[e]), e)) for n, e in defs]
        return S.balanced(leaves) if leaves else S.TRUE
    kept = {n for n, _ in new.defs}
    elim = [(n, e) for n, e in old.defs if n not in kept]
    same = S.mk("=", (old.claim, new.claim))
    D1, D2, DE = defs_term(old.defs), defs_term(new.defs), defs_term(elim)
    head = ["(set-logic QF_BV)"] + [f"(declare-const {n} " + ("Bool" if w == 0 else f"(_ BitVec {w})") + ")"
                                   for n, w in old.decls.items()]
    A = head + [f"(assert {S.to_str(D1)})", f"(assert (not (and {S.to_str(D2)} {S.to_str(same)})))", "(check-sat)"]
    B = head + [f"(assert {S.to_str(D2)})", f"(assert {S.to_str(DE)})",
                f"(assert (not (and {S.to_str(D1)} {S.to_str(same)})))", "(check-sat)"]
    res = []
    for tag, lines in (("A", A), ("B", B)):
        path = os.path.join(out, 'z3', f'{base}.{tag}.smt2')
        open(path, 'w').write("\n".join(lines) + "\n")
        try:
            p = subprocess.run(['z3', '-T:60', path], capture_output=True, text=True, timeout=90)
            res.append(p.stdout.strip().splitlines()[0] if p.stdout.strip() else 'none')
        except subprocess.TimeoutExpired:
            res.append('timeout')
    return res

rep = open(os.path.join(out, 'review.jsonl'), 'w')
table = []
for fn in sorted(os.listdir(new_dir)):
    if not fn.endswith('.smt2'):
        continue
    old = sections(open(os.path.join(old_dir, fn)).read())
    new = sections(open(os.path.join(new_dir, fn)).read())
    def groups(secs):
        g = {}
        for label, text in secs:
            g.setdefault(label.split(' | part ')[0], []).append(text)
        return g
    go, gn = groups(old), groups(new)
    assert list(go) == list(gn), fn
    changed = bad = 0
    for shape in go:
        if go[shape] == gn[shape]:
            continue
        changed += 1
        o, n = Th(go[shape]), Th(gn[shape])
        rec = {'file': fn, 'shape': shape, 'parts': [len(go[shape]), len(gn[shape])],
               'bytes': [sum(map(len, go[shape])), sum(map(len, gn[shape]))],
               'defs': [len(o.defs), len(n.defs)], 'one_path': o.one and o.source != S.TRUE}
        mm, fc = sweep(o, n, zlib.crc32((fn + shape).encode()))
        rec['sweep_mismatches'] = mm; rec['false_claims'] = fc
        base = re.sub(r'[^A-Za-z0-9_]', '_', f'{fn[:-5]}__{shape}')[:150]
        rec['z3_A'], rec['z3_B'] = z3q(o, n, base)
        if mm or rec['z3_A'] != 'unsat' or rec['z3_B'] != 'unsat':
            bad += 1
        rep.write(json.dumps(rec) + '\n'); rep.flush()
        print(f"{fn} {shape}: mm={mm} fc={fc} z3={rec['z3_A']}/{rec['z3_B']}", flush=True)
    table.append((fn, len(go), changed, bad))
print('| file | theorems (shapes) | changed | sweep or z3 failures |')
print('| --- | ---: | ---: | ---: |')
for fn, n, c, b in table:
    print(f'| `{fn}` | {n} | {c} | {b} |')
print(f'| total | {sum(t[1] for t in table)} | {sum(t[2] for t in table)} | {sum(t[3] for t in table)} |')
