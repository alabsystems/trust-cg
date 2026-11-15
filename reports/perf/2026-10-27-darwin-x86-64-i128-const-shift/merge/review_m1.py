#!/usr/bin/env python3
"""OD-215 lane merged with origin/main: review of every golden theorem whose bytes differ between an
old golden directory and the merged one, built on slice 23's review23.py (the slice-18 design's
smtq.py parser and evaluator, and z3 4.15.4), per changed shape (a parts golden per shape, the
conjunction):

  * sweep: 256 seeded inputs of the union of both theorems' free inputs; the old and the new
    claim evaluated on each (count of inputs where they differ, and where each is false);
  * z3 validity, each theorem alone: its definitions and (not claim); UNSAT = Valid;
  * z3 claim equivalence: both theorems' definitions with each side's defined names renamed apart
    (`o_`, `n_`), asserting the two claims differ; UNSAT = equivalent claims.

Unlike review23.py, names both theorems define are NOT required equal: a selector change (OD-215)
gives the machine side other rows, so a shared machine name (m<k>) may name another row. The
source side's names are compared on the sweep and reported (src_name_mismatches), since the source
is the same trust-ir in both.
usage: review_m1.py <old dir> <new dir> <out dir>"""
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

def is_source_name(n):
    return n.startswith('s')

def sweep(old, new, seed):
    rng = random.Random(seed)
    free = dict(old.free); free.update(dict(new.free))
    shared_src = {n for n in old.defined & new.defined if is_source_name(n)}
    mm = fo = fn = src = 0
    for _ in range(256):
        env = {n: S.random_value(w, rng) if w else rng.randrange(2) for n, w in free.items()}
        v1, x1 = evaluate(old, env); v2, x2 = evaluate(new, env)
        mm += v1 != v2; fo += not v1; fn += not v2
        src += any(x1[n] != x2[n] for n in shared_src)
    return mm, fo, fn, src

def renamed(text, names, prefix):
    if not names:
        return text
    pat = re.compile(r'(?<![A-Za-z0-9_.$])(' + '|'.join(sorted(map(re.escape, names), key=len, reverse=True)) + r')(?![A-Za-z0-9_.$])')
    return pat.sub(lambda m: prefix + m.group(1), text)

def side(th, prefix):
    defs = [renamed(S.to_str(S.mk("=", (S.var(n, S.WIDTH[e]), e))), th.defined, prefix) for n, e in th.defs]
    return defs, renamed(S.to_str(th.claim), th.defined, prefix)

def decls_of(ths):
    decls = {}
    for th, prefix in ths:
        for n, w in th.decls.items():
            decls[(prefix + n) if n in th.defined else n] = w
    return ["(declare-const {} {})".format(n, "Bool" if w == 0 else f"(_ BitVec {w})") for n, w in decls.items()]

def z3run(lines, path):
    open(path, 'w').write("\n".join(lines) + "\n")
    try:
        p = subprocess.run(['nice', '-n', '19', 'z3', '-T:120', path], capture_output=True, text=True, timeout=150)
        return p.stdout.strip().splitlines()[0] if p.stdout.strip() else 'none'
    except subprocess.TimeoutExpired:
        return 'timeout'

def z3_valid(th, base):
    d, c = side(th, "n_")
    lines = ["(set-logic QF_BV)"] + decls_of([(th, "n_")]) + [f"(assert {x})" for x in d] + [f"(assert (not {c}))", "(check-sat)"]
    return z3run(lines, os.path.join(out, 'z3', f'{base}.smt2'))

def z3_equiv(old, new, base):
    od, oc = side(old, "o_"); nd, nc = side(new, "n_")
    lines = ["(set-logic QF_BV)"] + decls_of([(old, "o_"), (new, "n_")]) + [f"(assert {x})" for x in od + nd]
    lines += [f"(assert (not (= {nc} {oc})))", "(check-sat)"]
    return z3run(lines, os.path.join(out, 'z3', f'{base}.smt2'))

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
    for shape in sorted(set(go) | set(gn)):
        if shape in go and shape in gn and go[shape] == gn[shape]:
            continue
        changed += 1
        if shape not in go or shape not in gn:
            rec = {'file': fn, 'shape': shape, 'only_in': 'new' if shape in gn else 'old'}
            bad += 1
            rep.write(json.dumps(rec) + '\n'); print(rec, flush=True)
            continue
        o, n = Th(go[shape]), Th(gn[shape])
        rec = {'file': fn, 'shape': shape, 'bytes': [sum(map(len, go[shape])), sum(map(len, gn[shape]))],
               'parts': [len(go[shape]), len(gn[shape])], 'defs': [len(o.defs), len(n.defs)]}
        mm, fo, fnew, src = sweep(o, n, zlib.crc32((fn + shape).encode()))
        rec.update(sweep_claim_mismatches=mm, false_old=fo, false_new=fnew, src_name_mismatches=src)
        base = re.sub(r'[^A-Za-z0-9_]', '_', f'{fn[:-5]}__{shape}')[:140]
        rec['z3_new_valid'] = z3_valid(n, base + '__new_valid')
        rec['z3_old_valid'] = z3_valid(o, base + '__old_valid')
        rec['z3_claims_equiv'] = z3_equiv(o, n, base + '__equiv')
        if mm or fo or fnew or src or rec['z3_new_valid'] != 'unsat' or rec['z3_claims_equiv'] != 'unsat':
            bad += 1
        rep.write(json.dumps(rec) + '\n'); rep.flush()
        print(f"{fn} {shape}: bytes {rec['bytes']} parts {rec['parts']} mm={mm} false(old,new)=({fo},{fnew}) src={src} "
              f"z3 valid(new)={rec['z3_new_valid']} valid(old)={rec['z3_old_valid']} equiv={rec['z3_claims_equiv']}", flush=True)
    table.append((fn, len(gn), changed, bad))
print('| file | theorems (shapes) | changed | failures |')
print('| --- | ---: | ---: | ---: |')
for fn, n, c, b in table:
    print(f'| `{fn}` | {n} | {c} | {b} |')
print(f'| total | {sum(t[1] for t in table)} | {sum(t[2] for t in table)} | {sum(t[3] for t in table)} |')
