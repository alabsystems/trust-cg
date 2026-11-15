#!/usr/bin/env python3
"""Slice 19 real-bytes measurement over a mapped probe dump (census file names).

  measure.py run   <mapped dir> <label> [--fresh-only]
                                           replay every distinct query not yet measured:
                                           one-shot (fresh) first, then the resident route on
                                           those the one-shot route certifies (the census
                                           route's second leg); results appended to
                                           results/{fresh,resident}.jsonl keyed by sha256
  measure.py score <mapped dir> [--claims <claims dir>] [--retry]
                                           roots certified one-shot / by the census route
                                           (--retry: stage 3(b)'s route, a resident answer
                                           other than SAT followed by the one-shot replay, so
                                           the census route certifies what one-shot does)

AY 13556 and Clean from the x86-stage1-ay13556 overlay (byte-identical to
~/clean-checker/bin/clean); 30 s each; replay19.py's gate (quiet.request, census, any
other AY) before every query; one solver at a time.
"""
import hashlib, json, os, subprocess, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
OV = os.path.expanduser('~/.local/share/trust-overlays/x86-stage1-ay13556/bin')
AY, CLEAN = f'{OV}/ay', os.path.expanduser('~/clean-checker/bin/clean')
RES = os.path.join(HERE, 'results')
os.makedirs(RES, exist_ok=True)
NAMES41 = os.path.expanduser('~/tcg-scratch/s19/names41.txt')

def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()

def load(route):
    out = {}
    p = os.path.join(RES, f'{route}.jsonl')
    if os.path.exists(p):
        for line in open(p):
            r = json.loads(line)
            out[r['sha']] = r
    return out

def replay(route, paths, label):
    if not paths:
        return
    by_base = {}
    for p in paths:
        by_base[os.path.basename(p)] = p
    cmd = ['python3', os.path.join(HERE, 'replay19.py'), '--ay', AY, '--clean', CLEAN,
           '--route', route, '--budget-s', '30', '--label', label] + paths
    with open(os.path.join(RES, f'{route}.jsonl'), 'a') as out:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, text=True)
        for line in proc.stdout:
            r = json.loads(line)
            r['sha'] = sha(by_base[r['query']])
            out.write(json.dumps(r) + '\n'); out.flush()
            print(f"{route:8s} {r['outcome']:22s} ay={r.get('ay_s','-')} clean={r.get('clean_s','-')} "
                  f"load={r['load1']} {r['query'][:90]}", flush=True)
        proc.wait()

def distinct(mapped):
    seen = {}
    for f in sorted(os.listdir(mapped)):
        if f.endswith('.smt2'):
            seen.setdefault(sha(os.path.join(mapped, f)), os.path.join(mapped, f))
    return seen

def dump_name(fn):
    return ''.join(c if (c.isascii() and (c.isalnum() or c == '_')) else '-' for c in fn)[:200]

def roots(mapped):
    files = sorted(f for f in os.listdir(mapped) if f.endswith('.smt2'))
    out = []
    for fn in open(NAMES41).read().split():
        stem = dump_name(fn)
        mine = [f for f in files if f == stem + '.smt2' or (f.startswith(stem + '.part') and f[len(stem) + 5:-5].isdigit())]
        out.append((fn, stem, mine))
    return out

RETRY = '--retry' in sys.argv

def main():
    mode, mapped = sys.argv[1], sys.argv[2]
    if mode == 'run' and mapped == '--single':
        # One query file, one-shot (claims_seq.py).
        path, label = sys.argv[3], sys.argv[4]
        if sha(path) not in load('fresh'):
            replay('fresh', [path], label)
        return
    if mode == 'run':
        label = sys.argv[3]
        todo = distinct(mapped)
        fresh = load('fresh')
        replay('fresh', [p for s, p in todo.items() if s not in fresh], label)
        if '--fresh-only' in sys.argv:
            print('MEASURE-RUN-DONE', label, flush=True)
            return
        fresh = load('fresh'); resident = load('resident')
        replay('resident', [p for s, p in todo.items()
                            if fresh.get(s, {}).get('outcome') == 'certified' and s not in resident], label)
        print('MEASURE-RUN-DONE', label, flush=True)
        return
    fresh, resident = load('fresh'), load('resident')
    claims_dir = sys.argv[sys.argv.index('--claims') + 1] if '--claims' in sys.argv else None
    tot = collections.Counter()
    for fn, stem, parts in roots(mapped):
        one = census = True
        failing = []
        for p in parts:
            s = sha(os.path.join(mapped, p))
            f = fresh.get(s, {}).get('outcome')
            r = resident.get(s, {}).get('outcome')
            ok1, ok2 = f == 'certified', f == 'certified' and r == 'resident-unsat'
            if not ok1 and claims_dir:
                ok1, ok2 = claim_status(claims_dir, p, fresh, resident)
            if RETRY:
                ok2 = ok1
            if f is None:
                failing.append(f'{p[len(stem):]}?')
            elif not ok1:
                failing.append(f'{p[len(stem):]}:{f}')
            one &= ok1; census &= ok2
        if not parts:
            one = census = False; failing = ['no query (emptied or refused)']
        tot['one-shot'] += one; tot['census'] += census
        print(f"{'Y' if one else '-'}{'Y' if census else '-'} {fn[:70]:70s} {len(parts)} {' '.join(failing)[:160]}")
    print(f'roots certified: one-shot {tot["one-shot"]}, census route {tot["census"]} (of 41)')

def claim_status(claims_dir, part, fresh, resident):
    base = part[:-5]
    claims = sorted(f for f in os.listdir(claims_dir) if f.startswith(base + '.c') and f.endswith('.smt2'))
    if not claims:
        return False, False
    one = census = True
    for c in claims:
        s = sha(os.path.join(claims_dir, c))
        f = fresh.get(s, {}).get('outcome'); r = resident.get(s, {}).get('outcome')
        one &= f == 'certified'; census &= f == 'certified' and (RETRY or r == 'resident-unsat')
    return one, census

main()
