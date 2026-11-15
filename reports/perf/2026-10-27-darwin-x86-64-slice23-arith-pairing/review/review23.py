#!/usr/bin/env python3
"""Slice 22 golden review: per golden file, every theorem that changed, checked against its old
spelling two independent ways (the slice-18 design's smtq.py parser and evaluator, and z3):
  * an evaluation sweep, 256 seeded inputs of the union of both theorems' free inputs: equal
    claim values, and every name both theorems define equal;
  * z3 (4.15.4, 60 s), one query: both theorems' definitions with each side's defined names
    renamed apart (`o_`, `n_`; definitions are total, so the premises are satisfiable for every
    free input and the query is never vacuous), asserting that the claims differ or some name
    both define differs; UNSAT is equivalence.
Unlike slice 19's review19.py this is symmetric: the new spelling may keep names the old one
eliminated (slice 9's rule falls back to slice 18's spelling) and the reverse.
A parts golden (sections `<shape> | part k of n`) is compared per shape (the conjunction).
usage: review23.py <old dir> <new dir> <out dir>"""
import json, os, random, re, subprocess, sys, zlib
sys.path.insert(0, os.path.expanduser('~/tcg-scratch/s18-design/scripts'))
import smtq as S

old_dir, new_dir, out = sys.argv[1:4]
os.makedirs(os.path.join(out, 'z3'), exist_ok=True)

def sections(text):
    chunks = re.split(r"^;;;; (.*)$", text, flags=re.M)
    return [(chunks[k].strip(), chunks[k + 1].strip('\n')) for k in range(1, len(chunks), 2)]

class Th:
    def __init__(self, texts):
        self.free, self.defs, claims = [], [], []
        self.decls = {}
        seen_free = set(); defined = {}
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
        self.claim = claims[0] if len(claims) == 1 else S.conj_right(claims)
        self.defined = {n for n, _ in self.defs}

def evaluate(th, env):
    vals = dict(env); memo = {}
    for n, e in th.defs:
        vals[n] = S.evaluate(e, vals, memo)
    return S.evaluate(th.claim, vals, memo), vals

def sweep(old, new, seed):
    rng = random.Random(seed)
    free = dict(old.free); free.update(dict(new.free))
    shared = old.defined & new.defined
    mm = fc = 0
    for _ in range(256):
        env = {n: S.random_value(w, rng) if w else rng.randrange(2) for n, w in free.items()}
        v1, x1 = evaluate(old, env); v2, x2 = evaluate(new, env)
        if v1 != v2 or any(x1[n] != x2[n] for n in shared):
            mm += 1
        fc += not v1
    return mm, fc

def renamed(text, names, prefix):
    if not names:
        return text
    pat = re.compile(r'(?<![A-Za-z0-9_.$])(' + '|'.join(sorted(map(re.escape, names), key=len, reverse=True)) + r')(?![A-Za-z0-9_.$])')
    return pat.sub(lambda m: prefix + m.group(1), text)

def z3q(old, new, base):
    def side(th, prefix):
        defs = [renamed(S.to_str(S.mk("=", (S.var(n, S.WIDTH[e]), e))), th.defined, prefix) for n, e in th.defs]
        return defs, renamed(S.to_str(th.claim), th.defined, prefix)
    od, oc = side(old, "o_"); nd, nc = side(new, "n_")
    decls = {}
    for th, prefix in ((old, "o_"), (new, "n_")):
        for n, w in th.decls.items():
            decls[(prefix + n) if n in th.defined else n] = w
    shared = sorted(old.defined & new.defined)
    differs = [f"(not (= {nc} {oc}))"] + [f"(not (= o_{n} n_{n}))" for n in shared]
    lines = ["(set-logic QF_BV)"] + [f"(declare-const {n} " + ("Bool" if w == 0 else f"(_ BitVec {w})") + ")" for n, w in decls.items()]
    lines += [f"(assert {d})" for d in od + nd]
    lines += [f"(assert (or {' '.join(differs)}))" if len(differs) > 1 else f"(assert {differs[0]})", "(check-sat)"]
    path = os.path.join(out, 'z3', f'{base}.smt2')
    open(path, 'w').write("\n".join(lines) + "\n")
    try:
        p = subprocess.run(['z3', '-T:60', path], capture_output=True, text=True, timeout=90)
        return p.stdout.strip().splitlines()[0] if p.stdout.strip() else 'none'
    except subprocess.TimeoutExpired:
        return 'timeout'

rep = open(os.path.join(out, 'review.jsonl'), 'w')
table = []
for fn in sorted(os.listdir(new_dir)):
    if not fn.endswith('.smt2') or not os.path.exists(os.path.join(old_dir, fn)):
        continue
    def groups(secs):
        g = {}
        for label, text in secs:
            g.setdefault(label.split(' | part ')[0], []).append(text)
        return g
    go = groups(sections(open(os.path.join(old_dir, fn)).read()))
    gn = groups(sections(open(os.path.join(new_dir, fn)).read()))
    changed = bad = 0
    for shape in go:
        if shape not in gn or go[shape] == gn[shape]:
            continue
        changed += 1
        o, n = Th(go[shape]), Th(gn[shape])
        rec = {'file': fn, 'shape': shape, 'bytes': [sum(map(len, go[shape])), sum(map(len, gn[shape]))],
               'defs': [len(o.defs), len(n.defs)]}
        mm, fc = sweep(o, n, zlib.crc32((fn + shape).encode()))
        rec['sweep_mismatches'] = mm; rec['false_claims'] = fc
        base = re.sub(r'[^A-Za-z0-9_]', '_', f'{fn[:-5]}__{shape}')[:150]
        rec['z3'] = z3q(o, n, base)
        if mm or rec['z3'] != 'unsat':
            bad += 1
        rep.write(json.dumps(rec) + '\n'); rep.flush()
        print(f"{fn} {shape}: mm={mm} fc={fc} z3={rec['z3']}", flush=True)
    table.append((fn, len(go), changed, bad))
print('| file | theorems (shapes) | changed | sweep or z3 failures |')
print('| --- | ---: | ---: | ---: |')
for fn, n, c, b in table:
    print(f'| `{fn}` | {n} | {c} | {b} |')
print(f'| total | {sum(t[1] for t in table)} | {sum(t[2] for t in table)} | {sum(t[3] for t in table)} |')
