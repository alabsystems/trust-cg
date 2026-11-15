#!/usr/bin/env python3
"""Slice 24c's ceiling on the slice-25 base (design ~/tcg-scratch/s24c-design/README.md
§7 "Before building" and its addendum), read-only over census output dirs.

Inputs: the slice-25 O2 census (census-o2-s25, the baseline) and the same dylib's
O2 census with if-conversion off (no-x86-ifconvert, no-x86-cmov-swap; tag
o2k-s25-nifc). Optionally a second (old) candidate list to cross-check, the S24a
base's candidates.tsv (design work/angleB/candidates.tsv).

Each failed root is keyed by the function its proof failure names (the
`non_verified proof entry <e> in <fn>:` message, as census_compare.py reads it)
and that function's LAST [TCG-X86-BODY-TRACE] line, its first refusal (a
`negative-memo hit` line is not a refusal and is skipped, as in census_compare.py).

First-refusal classes of the baseline:
  NC:two-entry     `not contracted: LIR block b is entered from [..], not from a alone`
  NC:brif          `not contracted: the predecessor x of LIR block y ends in a Brif ...`
  NC:switch        `... ends in a Switch ...`
  NC:not-on-chain  `not contracted: LIR block y is not on the chain ...`
  NOMB             `LIR block b has no machine block (merged, if-converted or removed)`
  other            anything else (normalized text printed)

Candidate shapes (design §1.1, §2.2; classifier copied from design
work/classify.py `classify`, which reads the members over the quotient and the
note over the original ids, mapping between them through the `chains=` list):
  IFCONV-DIAMOND-BOTH-ARMS  NC:brif/switch, the branch block x is a member of the
                            several-block machine block and every successor of x
                            is a member whose only live pred is x
  IFCONV-DIAMOND-ONE-ARM    x a member, some arm stamp-silent (not a member)
  SILENT-ARMS-ONLY          NOMB (all arms of the diamond stamp-silent)
  (an NC:switch IFCONV row is the "two-way Switch" shape; its x successor count
  is printed)
Other NC shapes (LICM-*, ROTATE-*) are not S24c candidates.

usage: ceiling_s25.py <baseline dir> <nifc dir> <out dir> [old candidates.tsv]
Writes roots.tsv, candidates.tsv, ceiling.txt to <out dir>; prints ceiling.txt.
"""
import collections
import csv
import json
import os
import re
import sys

base, new, out = sys.argv[1:4]
old_cand = sys.argv[4] if len(sys.argv) > 4 else None
os.makedirs(out, exist_ok=True)

PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
FN_IN_MSG = re.compile(r'non_verified proof entry \S+ in (\S+?): ')


def traces(d):
    by_fn = collections.defaultdict(list)
    for line in open(f'{d}/stderr.log', errors='replace'):
        m = PAT.match(line.rstrip('\n'))
        if m and 'negative-memo hit' not in m.group(2):
            by_fn[m.group(1)].append(m.group(2))
    return by_fn


def roots(d):
    found = {}
    for line in open(f'{d}/failed_roots.jsonl'):
        if not line.strip():
            continue
        r = json.loads(line)
        m = FN_IN_MSG.search(r.get('message', ''))
        found[r['symbol']] = m.group(1) if m else None
    return found


# --- design work/lib.py and work/classify.py, verbatim in substance ---------------
mem_re = re.compile(r"Block\((\d+)\)\[(\d+) row\(s\), pred \[([^\]]*)\], succ \[([^\]]*)\](, DEAD)?\]")
mb_re = re.compile(r"machine block Block\((\d+)\) lowers rows of several LIR blocks \[([^\]]*)\]")
NOTE = re.compile(r"; not contracted: (.*?)(?: \(over the merged-chain quotient: chains (.*)\))?$")


def blk(s):
    return [int(x) for x in re.findall(r"Block\((\d+)\)", s)]


def members(t):
    # Only the member list of the several-block decline (up to the note).
    t = t.split('; not contracted: ')[0]
    return {int(m[0]): dict(rows=int(m[1]), pred=blk(m[2]), succ=blk(m[3]), dead=bool(m[4]))
            for m in mem_re.findall(t)}


def chains_of(s):
    out = {}
    if not s:
        return out
    for part in s.split("; "):
        h, ms = part.split("=", 1)
        for m in blk(ms):
            out[m] = blk(h)[0]
    return out


def parse_note(note):
    d = {}
    m = re.match(r"the predecessor Block\((\d+)\) of LIR block Block\((\d+)\) ends in a (\w+), not a Jump to it", note)
    if m:
        d.update(kind=m.group(3).lower(), x=int(m.group(1)), y=int(m.group(2)))
        return d
    m = re.match(r"LIR block Block\((\d+)\) is entered from \[(.*)\], not from Block\((\d+)\) alone", note)
    if m:
        ents = [(int(a), bool(u)) for a, u in re.findall(r"Block\((\d+)\)( \(unreachable\))?", m.group(2))]
        d.update(kind="two-entry", y=int(m.group(1)), entering=ents, on=int(m.group(3)))
        return d
    m = re.match(r"LIR block Block\((\d+)\) is not on the chain of single-entry Jumps through Block\((\d+)\)(.*)", note)
    if m:
        d.update(kind="not-on-chain", y=int(m.group(1)), start=int(m.group(2)), extra=m.group(3).strip())
        return d
    d.update(kind="other")
    return d


def member_cycle(M):
    """The blocks of one cycle among the member edges (succ inside M), or []."""
    color = {}
    stack = []

    def dfs(b):
        color[b] = 1
        stack.append(b)
        for s in M[b]["succ"]:
            if s not in M:
                continue
            if color.get(s) == 1:
                return stack[stack.index(s):] + [s]
            if s not in color:
                c = dfs(s)
                if c:
                    return c
        color[b] = 2
        stack.pop()
        return []
    for b in sorted(M):
        if b not in color:
            c = dfs(b)
            if c:
                return c
    return []


def classify(M, n, absorbed):
    """Shape and detail of a decline (design work/classify.py `classify`)."""
    def q(b):
        return absorbed.get(b, b)
    det = {}
    k = n["kind"]
    if k in ("brif", "switch"):
        x, y = n["x"], n["y"]
        det["x"], det["y"] = x, y
        if q(x) in M:
            xs = M[q(x)]["succ"]
            arms = [a for a in xs if a in M and M[a]["pred"] == [q(x)]]
            det["arms_named"] = len(arms)
            det["x_succ"] = len(xs)
            # Added check (not in work/classify.py): a cycle among the member edges
            # makes the block a loop, not a diamond; S24c's C3 (design §2.1: member
            # edges are forward and no member has h as a successor) refuses such a
            # region. A forward chain Jump into x is not a cycle.
            det["member_cycle"] = member_cycle(M)
            return "IFCONV-DIAMOND-%s" % ("BOTH-ARMS" if len(arms) == len(xs) else "ONE-ARM"), det
        P = [p for p, v in M.items() if len(v["succ"]) == 1 and v["succ"][0] not in M
             and v["succ"][0] > p and not v["dead"]]
        hs = sorted({M[p]["succ"][0] for p in P})
        if P:
            return ("LICM-BODY-ROWS-IN-PREHEADER(x=header)" if q(x) in hs else
                    "LICM-BODY-ROWS-IN-PREHEADER(x=in-loop)"), det
        return "UNCLASSIFIED", det
    if k == "two-entry":
        y = n["y"]
        ents = n["entering"]
        A = [a for a, _ in ents if q(a) in M and M[q(a)]["succ"] == [q(y)]]
        if q(y) not in M:
            return "UNCLASSIFIED", det
        if A:
            return ("LICM-HEADER-ROWS-IN-PREHEADER" if A[0] < y else "ROTATE-HEADER-TEST-IN-LATCH"), det
        rot = [(m, v["succ"][0]) for m, v in M.items() if len(v["succ"]) == 1 and v["succ"][0] in M
               and len(M[v["succ"][0]]["pred"]) == 2 and m in M[v["succ"][0]]["pred"] and m > v["succ"][0]]
        if rot:
            return "ROTATE-HEADER-TEST-IN-LATCH", det
        return "UNCLASSIFIED", det
    if k == "not-on-chain":
        P = [p for p, v in M.items() if len(v["succ"]) == 1 and v["succ"][0] not in M and v["succ"][0] > p]
        if P:
            return "LICM-BODY-ROWS-IN-PREHEADER(not-on-chain)", det
        return "UNCLASSIFIED", det
    return "UNCLASSIFIED", det
# ----------------------------------------------------------------------------------


def norm(t):
    t = re.sub(r' \(over the merged-chain quotient: .*\)$', ' (over the quotient)', t)
    t = t.replace('unsupported source-bound x86-64 body: ', '')
    t = re.sub(r'lowers rows of several LIR blocks \[[^\]]*\]: .*?(?=; not contracted: |$)',
               'lowers rows of several LIR blocks', t)
    t = re.sub(r'Block\(\d+\)', 'Block(N)', t)
    t = re.sub(r'\b(instruction|row|access|slot|table) \d+', r'\1 N', t)
    t = re.sub(r'\[[^\[\]]*\]', '[..]', t)
    t = re.sub(r'\{[^{}]*\}', '{..}', t)
    t = re.sub(r'\b\d+\b', 'N', t)
    return t[:260]


def first_refusal(lines):
    """(class, shape, detail) of a function's last trace line."""
    if not lines:
        return 'untraced', '', ''
    t = lines[-1]
    if t.startswith('bound rows='):
        v = ('bound, replays Valid' if 'replay=Valid' in t else
             'bound, REFUTED' if 'Invalid' in t else 'bound, no independently checked proof')
        return v, '', ''
    if 'not contracted: ' in t and mb_re.search(t):
        m = NOTE.search(t)
        note, ch = m.group(1), m.group(2)
        n = parse_note(note)
        shape, det = classify(members(t), n, chains_of(ch))
        return 'NC:' + n['kind'], shape, json.dumps(det, sort_keys=True)
    if 'has no machine block' in t:
        return 'NOMB', 'SILENT-ARMS-ONLY', ''
    if mb_re.search(t):
        return 'several (no note)', '', ''
    return 'other', '', norm(t)


def outcome(lines):
    """Short outcome of a function in a census (its last trace line)."""
    if not lines:
        return 'untraced'
    t = lines[-1]
    if t.startswith('bound rows='):
        return ('BOUND-Valid' if 'replay=Valid' in t else
                'BOUND-REFUTED' if 'Invalid' in t else 'BOUND-uncertified')
    c, s, d = first_refusal(lines)
    if c.startswith('NC:'):
        return f'{c}/{s}'
    if c == 'NOMB':
        return 'NOMB'
    if c == 'several (no note)':
        return 'SEVERAL(no note)'
    return 'OTHER: ' + d[:150]


bt, nt = traces(base), traces(new)
br, nr = roots(base), roots(new)
promoted = sorted(set(br) - set(nr))
newly = sorted(set(nr) - set(br))
is_cand = lambda shape: shape.startswith('IFCONV') or shape == 'SILENT-ARMS-ONLY'

L = []
L.append(f'baseline: {base}')
L.append(f'nifc:     {new}')
L.append(f'baseline failed roots: {len(br)}; nifc failed roots: {len(nr)}; '
         f'promoted: {len(promoted)}; newly failing: {len(newly)}')
untr = [s for s, fn in br.items() if fn is None or fn not in bt]
L.append(f'baseline roots with no named fn or an untraced fn: {len(untr)}')

# Per baseline root: first refusal, shape, candidate, nifc outcome of its fn.
rows = []
for sym, fn in sorted(br.items()):
    c, shape, det = first_refusal(bt.get(fn, [])) if fn else ('(no fn in message)', '', '')
    rows.append(dict(symbol=sym, fn=fn or '', base_class=c, shape=shape, detail=det,
                     candidate=is_cand(shape), promoted=sym not in nr,
                     nifc_named=nr.get(sym) or '', nifc_fn_outcome=outcome(nt.get(fn, [])) if fn else ''))
with open(f'{out}/roots.tsv', 'w') as f:
    w = csv.writer(f, delimiter='\t', lineterminator='\n')
    keys = list(rows[0])
    w.writerow(keys)
    for r in rows:
        w.writerow([r[k] for k in keys])

# 1. Baseline first refusal classes and shapes (all roots).
L.append('')
L.append('baseline roots by first refusal class / shape (promoted under nifc):')
tab = collections.Counter((r['base_class'], r['shape']) for r in rows)
ptab = collections.Counter((r['base_class'], r['shape']) for r in rows if r['promoted'])
for (c, s), n in sorted(tab.items(), key=lambda kv: (-kv[1], kv[0])):
    if c == 'other':
        continue
    L.append(f'  {n:5d}  promoted {ptab[(c, s)]:4d}  {c:16s} {s}')
no = sum(n for (c, s), n in tab.items() if c == 'other')
L.append(f'  {no:5d}  promoted {sum(n for (c, s), n in ptab.items() if c == "other"):4d}  other')

# 2. Promoted roots by their baseline first refusal.
L.append('')
L.append(f'promoted roots ({len(promoted)}) by their census-o2-s25 first refusal:')
pc = collections.Counter()
for r in rows:
    if r['promoted']:
        k = r['base_class'] if r['base_class'] != 'other' else 'other: ' + r['detail'][:200]
        pc[k] += 1
for k, n in pc.most_common():
    L.append(f'  {n:5d}  {k}')
pnc = collections.Counter(r['shape'] for r in rows if r['promoted'] and r['base_class'].startswith('NC:'))
L.append('  promoted NC roots by shape: ' + ', '.join(f'{s} {n}' for s, n in sorted(pnc.items())))
pv = collections.Counter(outcome(nt.get(r['fn'], [])) for r in rows if r['promoted'])
L.append('  their named fn under nifc: ' + ', '.join(f'{k} {n}' for k, n in pv.most_common()))

# 3. Candidates (fn-level, deduplicated by named fn) and their nifc outcome.
cand = {}
for r in rows:
    if r['candidate']:
        cand.setdefault(r['fn'], dict(shape=r['shape'], detail=r['detail'], roots=[], base_class=r['base_class']))
        cand[r['fn']]['roots'].append(r['symbol'])
L.append('')
croots = sum(len(v['roots']) for v in cand.values())
L.append(f'S24c candidates on the S25 base: {len(cand)} functions ({croots} failed roots)')
by_shape = collections.Counter()
by_shape_bind = collections.Counter()
by_shape_prom = collections.Counter()
for fn, v in cand.items():
    key = v['shape']
    d = json.loads(v['detail']) if v['detail'] else {}
    if v['base_class'] == 'NC:switch':
        key += ' (Switch, %d-way)' % d.get('x_succ', -1)
    if d.get('member_cycle'):
        key += ' [LOOP: member edges form a cycle, not a diamond]'
    v['key'] = key
    v['nifc'] = outcome(nt.get(fn, []))
    v['promoted_roots'] = sum(1 for s in v['roots'] if s not in nr)
    by_shape[key] += 1
    by_shape_bind[key] += v['nifc'] == 'BOUND-Valid'
    by_shape_prom[key] += v['promoted_roots'] == len(v['roots'])
for k, n in sorted(by_shape.items()):
    L.append(f'  {n:4d}  bind Valid under nifc {by_shape_bind[k]:4d}  all roots promoted {by_shape_prom[k]:4d}  {k}')
nb = sum(by_shape_bind.values())
L.append(f'  total {len(cand)}: bind Valid without if-conversion {nb}; '
         f'functions whose roots all promote {sum(by_shape_prom.values())}')
L.append('  candidates that do not bind under nifc, by nifc outcome:')
nbc = collections.Counter(v['nifc'] for v in cand.values() if v['nifc'] != 'BOUND-Valid')
for k, n in nbc.most_common():
    L.append(f'    {n:4d}  {k}')
with open(f'{out}/candidates.tsv', 'w') as f:
    w = csv.writer(f, delimiter='\t', lineterminator='\n')
    w.writerow(['fn', 'shape', 'base_class', 'roots', 'promoted_roots', 'nifc', 'detail'])
    for fn, v in sorted(cand.items()):
        w.writerow([fn, v['key'], v['base_class'], len(v['roots']), v['promoted_roots'], v['nifc'], v['detail']])

# 4. Promoted roots that are not candidates (masked or other).
L.append('')
nonc = [r for r in rows if r['promoted'] and not r['candidate']]
L.append(f'promoted roots that are not S24c candidates: {len(nonc)}')
for r in nonc:
    L.append(f"  {r['base_class']:16s} {r['shape'] or r['detail'][:120]}  {r['fn'][-90:]}")

# 5. Anomalies: newly failing roots; promoted roots whose named fn does not bind
# Valid under nifc; mismatches and refuted bodies in the nifc census.
L.append('')
L.append(f'newly failing roots under nifc: {len(newly)}')
for s in newly:
    fn = nr[s]
    L.append(f"  {s} named {fn}: {outcome(nt.get(fn, [])) if fn else '(no fn)'}")
mism = [(fn, l) for fn, ls in nt.items() for l in ls if 'mismatch' in l]
ref = [(fn, l) for fn, ls in nt.items() for l in ls if 'Invalid' in l]
L.append(f'nifc named mismatches: {len(mism)}; refuted bodies (trace lines): {len(ref)}')
for fn, l in mism + ref:
    L.append(f'  {fn} {l[:200]}')
odd = [r for r in rows if r['promoted'] and outcome(nt.get(r['fn'], [])) != 'BOUND-Valid']
L.append(f'promoted roots whose named fn does not end bound Valid under nifc: {len(odd)}')
for r in odd:
    L.append(f"  {r['symbol']} named {r['fn'][-80:]}: {outcome(nt.get(r['fn'], []))}")

# 6. Cross-check against an older candidate list (the S24a base's 43).
if old_cand:
    oc = list(csv.DictReader(open(old_cand), delimiter='\t'))
    L.append('')
    L.append(f'S24a-base candidates ({len(oc)}) on the S25 base:')
    st = collections.Counter()
    for r in oc:
        fn = r['fn']
        if fn in cand:
            st['still a candidate (' + ('same shape' if cand[fn]['shape'] == r['shape'] else
                                        f"shape {r['shape']} -> {cand[fn]['shape']}") + ')'] += 1
        else:
            o = outcome(bt.get(fn, []))
            st['not a candidate on S25: ' + o[:120]] += 1
    for k, n in st.most_common():
        L.append(f'  {n:4d}  {k}')
    newc = [fn for fn in cand if fn not in {r['fn'] for r in oc}]
    L.append(f'  candidates on S25 not in the S24a list: {len(newc)}')

open(f'{out}/ceiling.txt', 'w').write('\n'.join(L) + '\n')
print('\n'.join(L))
