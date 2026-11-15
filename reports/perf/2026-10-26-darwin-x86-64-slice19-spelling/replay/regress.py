#!/usr/bin/env python3
"""Slice 19 whole-core regression check (no census): every function of census-ay13556's
core whose probe theorem bytes change between two probe runs (base: main, new: a slice-19
stage), with its census-ay13556 outcome (the last `[TCG-X86-BODY-TRACE] fn=... replay=`
line), the new bytes of every function the census certified written to <out>/queries
(census file names) for measure.py, and, after measure.py has replayed them, a report of
which still certify on each route.

  regress.py prepare <base probe dir> <new probe dir> <out dir>
  regress.py report  <out dir>
"""
import json, os, re, shutil, sys, hashlib
CENSUS = os.environ.get('S19_CENSUS_LOG', os.path.expanduser('~/tcg-scratch/runs/census-ay13556/stderr.log'))
HERE = os.path.dirname(os.path.abspath(__file__))

def idx(d):
    out = {}
    for l in open(f'{d}/smt2/index.tsv'):
        r = l.rstrip('\n').split('\t')
        out[r[1]] = [f'{r[0]}.part{k}.smt2' for k in range(1, int(r[2]) + 1)] if len(r) == 3 else [f'{r[0]}.smt2']
    return out

def dump_name(fn):
    return ''.join(c if (c.isascii() and (c.isalnum() or c == '_')) else '-' for c in fn)[:200]

def census_outcomes():
    last = {}
    pat = re.compile(r'\[TCG-X86-BODY-TRACE\] fn=(\S+) bound rows=\d+ replay=(.*)')
    for line in open(CENSUS, errors='replace'):
        m = pat.match(line.rstrip())
        if m:
            last[m.group(1)] = m.group(2)
    return last

def prepare(base, new, out):
    b, n = idx(base), idx(new)
    census = census_outcomes()
    os.makedirs(f'{out}/queries', exist_ok=True)
    rows = []
    for fn in sorted(set(b) & set(n)):
        tb = [open(f'{base}/smt2/{q}').read() for q in b[fn]]
        tn = [open(f'{new}/smt2/{q}').read() for q in n[fn]]
        if tb == tn:
            continue
        outcome = census.get(fn, 'not traced')
        valid = outcome.startswith('Valid')
        stem = dump_name(fn)
        names = [f'{stem}.smt2'] if len(n[fn]) == 1 and not n[fn][0].count('.part') else [f'{stem}.part{k+1}.smt2' for k in range(len(n[fn]))]
        if valid:
            for q, name in zip(n[fn], names):
                shutil.copyfile(f'{new}/smt2/{q}', f'{out}/queries/{name}')
        rows.append({'fn': fn, 'census': 'Valid' if valid else outcome[:80], 'queries': names,
                     'parts_before': len(tb), 'parts_after': len(tn)})
    with open(f'{out}/changed.jsonl', 'w') as f:
        for r in rows:
            f.write(json.dumps(r) + '\n')
    print(f'{len(rows)} functions change; {sum(r["census"] == "Valid" for r in rows)} certified by the census; '
          f'{len(os.listdir(out + "/queries"))} queries written')

def report(out):
    sys.path.insert(0, HERE)
    load = lambda route: {json.loads(l)['sha']: json.loads(l) for l in open(f'{HERE}/results/{route}.jsonl')} \
        if os.path.exists(f'{HERE}/results/{route}.jsonl') else {}
    fresh, resident = load('fresh'), load('resident')
    sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
    keep = lose1 = lose2 = unmeasured = 0
    lost = []
    for l in open(f'{out}/changed.jsonl'):
        r = json.loads(l)
        if r['census'] != 'Valid':
            continue
        ok1 = ok2 = True; missing = False
        for q in r['queries']:
            s = sha(f'{out}/queries/{q}')
            f = fresh.get(s, {}).get('outcome'); rr = resident.get(s, {}).get('outcome')
            if f is None:
                missing = True
            ok1 &= f == 'certified'; ok2 &= f == 'certified' and rr == 'resident-unsat'
        if missing:
            unmeasured += 1
        elif ok2:
            keep += 1
        else:
            lose1 += not ok1; lose2 += ok1 and not ok2
            lost.append((r['fn'], [fresh.get(sha(f'{out}/queries/{q}'), {}).get('outcome') for q in r['queries']]))
    print(f'census-certified functions whose bytes change: still certified on both routes {keep}; '
          f'lost one-shot {lose1}; lost only on the resident leg {lose2}; unmeasured {unmeasured}')
    for fn, outs in lost:
        print('  LOST', fn[:110], outs)

if __name__ == '__main__':
    if sys.argv[1] == 'prepare':
        prepare(*sys.argv[2:5])
    else:
        report(sys.argv[2])
