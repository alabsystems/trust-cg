#!/usr/bin/env python3
"""Slice 24c's O2 attribution (design §7): the census of the slice-24c head
against its baseline (census-o2-s25), by the `segments=K members=N
kinds=[..]` trace line a theorem stated over segments prints (OD-228).

Each failed root is keyed by the function its proof failure names and that
function's last [TCG-X86-BODY-TRACE] line (its first refusal, as
root_classes.py reads it). A function's segment kinds are those of its last
`segments=` line; its KIND SET is `diamond`, `silent` or `chain-only` when
every segment is of that one kind, and the `+`-joined kinds otherwise.

- The functions stated over segments, by kind set and verdict (last line).
- The promoted roots by the kind set of their function (a promoted root
  whose function states no segment is listed by name), by their baseline
  class (root_classes.py's `cls`, read from the copy beside this script) and
  by their normalized baseline refusal. The classifier is the given
  root_classes.py, or the copy beside this script.
- Against the ceiling (census-o2k-s25-nifc; ceiling_s25.py's roots.tsv, if
  given): its promoted roots that promote here, each one that does not with
  its new last line, and every root promoted here that the ceiling did not
  promote.
- The remaining roots by class and by normalized refusal, and the chooser's
  declines (`; no segment: ...`) among their last lines.
- Every newly failing root, named mismatch and refuted body (trace lines).

Writes segments.txt, roots.tsv, functions.tsv and segments.json to <out dir>
and prints segments.txt.

usage: census_segments.py <baseline dir> <new dir> <out dir> [<ceiling roots.tsv> [<root_classes.py>]]
"""
import ast
import collections
import csv
import json
import os
import re
import sys

base, new, out = sys.argv[1:4]
ceiling_tsv = sys.argv[4] if len(sys.argv) > 4 and sys.argv[4] else None
os.makedirs(out, exist_ok=True)

PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
FN_IN_MSG = re.compile(r'non_verified proof entry \S+ in (\S+?): ')
SEG = re.compile(r'^segments=(\d+) members=(\d+) kinds=\[([a-z,]*)\]$')
NO_SEGMENT = '; no segment: '

# root_classes.py's classifier, compiled from its source (the script runs on
# import), so both tables use one set of keys.
RC = (sys.argv[5] if len(sys.argv) > 5 else
      os.path.join(os.path.dirname(os.path.abspath(__file__)), 'root_classes.py'))
_tree = ast.parse(open(RC).read(), RC)
_cls = [n for n in _tree.body if isinstance(n, ast.FunctionDef) and n.name == 'cls']
_ns = {'re': re}
exec(compile(ast.Module(body=_cls, type_ignores=[]), RC, 'exec'), _ns)
cls = _ns['cls']


def traces(d):
    by_fn = collections.defaultdict(list)
    for line in open(f'{d}/stderr.log', errors='replace'):
        m = PAT.match(line.rstrip('\n'))
        if m:
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


# census_s25.py's normalization, with the slice-24c suffixes: `(over
# segments: ..)` (inside the quotient's) and `; no segment: ..`.
S_DETAIL = re.compile(r'( or scaled-index base)?: block Block\(\d+\) row (?:\d+|\(not laid out\) index \d+), '
                      r'(\w+) with operands \[.*?\] \(\d+ such rows?\)')
DOMAIN = re.compile(r'is outside the body domain \(MovRR, .*?operand-free Nop\): ')
SEVERAL = re.compile(r'lowers rows of several LIR blocks \[[^\]]*\]: .*?(?=; not contracted: |; no segment: |$)')


def norm(t):
    if t.startswith('bound rows='):
        return ('bound, replays Valid' if 'replay=Valid' in t else
                'bound, REFUTED' if 'Invalid' in t else 'bound, no independently checked proof')
    q = ' (over the quotient)' if 'over the merged-chain quotient' in t else ''
    t = re.sub(r' \(over the merged-chain quotient: .*\)$', '', t)
    s = ' (over segments)' if ' (over segments: ' in t else ''
    t = re.sub(r' \(over segments: .*\)$', '', t)
    t = t.replace('unsupported source-bound x86-64 body: ', '')
    t = S_DETAIL.sub(lambda m: f': {m.group(2)}', t)
    t = DOMAIN.sub('is outside the body domain (BODY_OPCODES): ', t)
    t = SEVERAL.sub('lowers rows of several LIR blocks', t)
    t = re.sub(r'Block\(\d+\)', 'Block(N)', t)
    t = re.sub(r'\b(instruction|row|access|slot|table) \d+', r'\1 N', t)
    t = re.sub(r'\(not laid out\) index \d+', 'N', t)
    t = re.sub(r'\(\d+ such rows?\)', '(K such rows)', t)
    t = re.sub(r'\[[^\[\]]*\]', '[..]', t)
    t = re.sub(r'\{[^{}]*\}', '{..}', t)
    t = re.sub(r'\b\d+\b', 'N', t)
    return t[:360] + s + q


def decline(t):
    """The chooser's decline in a last line, normalized, or None."""
    if NO_SEGMENT not in t:
        return None
    d = t.split(NO_SEGMENT, 1)[1]
    d = re.sub(r' \(over the merged-chain quotient: .*\)$', '', d)
    d = re.sub(r'Block\(\d+\)', 'Block(N)', d)
    d = re.sub(r'\[[^\[\]]*\]', '[..]', d)
    return d


def verdict(lines):
    last = lines[-1]
    if last.startswith('bound rows='):
        return ('bound, replays Valid' if 'replay=Valid' in last else
                'bound, REFUTED' if 'Invalid' in last else 'bound, no independently checked proof')
    if 'mismatch' in last:
        return 'MISMATCH'
    return 'refused'


def kind_set(kinds):
    ks = sorted(set(kinds))
    if ks == ['chain']:
        return 'chain-only'
    return '+'.join(ks) if ks else '(none)'


bt, nt = traces(base), traces(new)
br, nr = roots(base), roots(new)


def last_of(side, fn):
    if fn is None:
        return '(no fn in message)'
    ls = side.get(fn)
    return ls[-1] if ls else '(named fn untraced)'


def class_of(side, fn):
    if fn is None:
        return '(no fn in message)'
    return cls(side[fn][-1]) if fn in side else '(named fn untraced)'


# Functions stated over segments (the last `segments=` line of each).
segfns = {}
for fn, ls in nt.items():
    segs = [SEG.match(l) for l in ls if l.startswith('segments=')]
    segs = [m for m in segs if m]
    bad = [l for l in ls if l.startswith('segments=') and not SEG.match(l)]
    if bad:
        raise SystemExit(f'unparsed segments line of {fn}: {bad[0]}')
    if segs:
        m = segs[-1]
        kinds = [k for k in m.group(3).split(',') if k]
        segfns[fn] = {'segments': int(m.group(1)), 'members': int(m.group(2)), 'kinds': kinds,
                      'kind_set': kind_set(kinds), 'verdict': verdict(ls), 'attempts': len(segs),
                      'last': ls[-1]}
in_base = sum(1 for ls in bt.values() if any(l.startswith('segments=') for l in ls))

promoted = sorted(set(br) - set(nr))
newly = sorted(set(nr) - set(br))
lines = [f'baseline failed roots: {len(br)}', f'new failed roots: {len(nr)}',
         f'promoted: {len(promoted)}', f'newly failing: {len(newly)}',
         f'functions with a segments= line: baseline {in_base}, new {len(segfns)}']

lines.append('functions stated over segments, by kind set and verdict:')
fk = collections.Counter((v['kind_set'], v['verdict']) for v in segfns.values())
for (k, v), n in sorted(fk.items(), key=lambda x: (-x[1], x[0])):
    lines.append(f'  {n:5d}  {k:24s} {v}')
lines.append('  segments per function: ' + ', '.join(
    f'{k}: {n}' for k, n in sorted(collections.Counter(v['segments'] for v in segfns.values()).items())))
lines.append('  segments by kind (every segment of every function): ' + ', '.join(
    f'{k} {n}' for k, n in sorted(collections.Counter(k for v in segfns.values() for k in v['kinds']).items())))

# Promoted roots.
def by_kind_of(s):
    info = segfns.get(br[s])
    return info['kind_set'] if info else '(no segments line)'


def short_decline(t, c):
    """OD-226's decline note of a baseline refusal, normalized, or its class."""
    if '; not contracted: ' not in t:
        return c
    d = t.split('; not contracted: ', 1)[1]
    d = re.sub(r' \(over the merged-chain quotient: .*\)$', '', d)
    d = re.sub(r'Block\(\d+\)', 'Block(N)', d)
    d = re.sub(r'\[[^\[\]]*\]', '[..]', d)
    return 'not contracted: ' + d[:120]


by_kind = collections.Counter()
by_kind_class = collections.Counter()
no_seg = []
for s in promoted:
    fn = br[s]
    info = segfns.get(fn)
    k = info['kind_set'] if info else '(no segments line)'
    by_kind[k] += 1
    by_kind_class[(k, class_of(bt, fn))] += 1
    if not info:
        no_seg.append(s)
lines.append('promoted roots by the kind set of their function\'s segments:')
for k, n in by_kind.most_common():
    lines.append(f'  {n:5d}  {k}')
lines.append('promoted roots by kind set and baseline class (root_classes.py):')
for (k, c), n in sorted(by_kind_class.items(), key=lambda x: (-x[1], x[0])):
    lines.append(f'  {n:5d}  {k:24s} {c}')
lines.append('promoted roots by kind set and baseline decline (OD-226\'s note, or the class):')
for (k, d), n in sorted(collections.Counter(
        (by_kind_of(s), short_decline(last_of(bt, br[s]), class_of(bt, br[s]))) for s in promoted).items(),
        key=lambda x: (-x[1], x[0])):
    lines.append(f'  {n:5d}  {k:24s} {d}')
lines.append('promoted roots by their normalized baseline refusal:')
for t, n in collections.Counter(norm(last_of(bt, br[s])) for s in promoted).most_common():
    lines.append(f'  {n:5d}  {t}')
lines.append('promoted roots by the verdict of their named function in the new census:')
for t, n in collections.Counter(norm(last_of(nt, br[s])) for s in promoted).most_common():
    lines.append(f'  {n:5d}  {t}')
for s in no_seg:
    lines.append(f'PROMOTED WITHOUT A SEGMENTS LINE {s} named {br[s]}: {last_of(nt, br[s])[:300]}')

# Against the ceiling.
ceiling = {}
if ceiling_tsv:
    with open(ceiling_tsv) as f:
        for row in csv.DictReader(f, delimiter='\t'):
            ceiling[row['symbol']] = row
    cprom = sorted(s for s, row in ceiling.items() if row['promoted'] in ('1', 'True', 'yes', 'promoted'))
    if not cprom:
        raise SystemExit(f'no promoted root in {ceiling_tsv}: unknown promoted encoding')
    hit = [s for s in cprom if s in br and s not in nr]
    miss = [s for s in cprom if s in nr]
    extra = [s for s in promoted if s not in cprom]
    lines.append(f'ceiling (census-o2k-s25-nifc): promoted {len(cprom)}; promoted here {len(hit)}; '
                 f'still failing here {len(miss)}; promoted here, not by the ceiling {len(extra)}')
    shapes = collections.Counter((ceiling[s]['shape'], 'promoted' if s in hit else 'fails') for s in cprom)
    for (sh, o), n in sorted(shapes.items()):
        lines.append(f'  {n:5d}  {o:9s} {sh}')
    lines.append('promoted roots by kind set and ceiling shape:')
    for (k, sh), n in sorted(collections.Counter(
            (by_kind_of(s), ceiling[s]['shape'] if s in ceiling else '(not a ceiling root)')
            for s in promoted).items(), key=lambda x: (-x[1], x[0])):
        lines.append(f'  {n:5d}  {k:24s} {sh}')
    miss_by = collections.Counter(norm(last_of(nt, nr[s])) for s in miss)
    lines.append('ceiling roots still failing here, by their new refusal:')
    for t, n in miss_by.most_common():
        lines.append(f'  {n:5d}  {t}')
    for s in miss:
        lines.append(f'  CEILING-MISS {ceiling[s]["shape"]} {nr[s]}: {last_of(nt, nr[s])[:400]}')
    for s in extra:
        lines.append(f'  NOT-IN-CEILING {s} named {br[s]}: {segfns.get(br[s], {}).get("kind_set", "(no segments line)")}')

# Remaining roots.
lines.append('new failed roots by class (root_classes.py):')
for t, n in collections.Counter(class_of(nt, nr[s]) for s in nr).most_common():
    lines.append(f'  {n:5d}  {t}')
lines.append('new failed roots by their normalized refusal:')
for t, n in collections.Counter(norm(last_of(nt, nr[s])) for s in nr).most_common(80):
    lines.append(f'  {n:5d}  {t}')
dec = collections.Counter(decline(last_of(nt, nr[s])) for s in nr)
lines.append(f'new failed roots whose last line carries a chooser decline (`{NO_SEGMENT.strip()}`): '
             f'{sum(n for d, n in dec.items() if d)}')
for d, n in dec.most_common():
    if d:
        lines.append(f'  {n:5d}  {d[:300]}')
over_seg = [s for s in nr if ' (over segments: ' in last_of(nt, nr[s])]
lines.append(f'new failed roots refused over segments (`(over segments: ..)`): {len(over_seg)}')
for t, n in collections.Counter(norm(last_of(nt, nr[s])) for s in over_seg).most_common():
    lines.append(f'  {n:5d}  {t}')
seg_roots = [s for s in nr if nr[s] in segfns]
lines.append(f'new failed roots naming a function stated over segments: {len(seg_roots)}')
for t, n in collections.Counter((segfns[nr[s]]['kind_set'], norm(last_of(nt, nr[s]))) for s in seg_roots).most_common():
    lines.append(f'  {n:5d}  {t[0]:24s} {t[1]}')

# Stop-rule material.
mism = sorted({fn for fn, ls in nt.items() for l in ls if 'mismatch' in l})
refuted = [(fn, l) for fn, ls in nt.items() for l in ls if 'Invalid' in l]
lines.append(f'named mismatches (functions): {len(mism)}')
for fn in mism:
    lines.append(f'  MISMATCH {fn}: {[l for l in nt[fn] if "mismatch" in l][0][:400]}')
lines.append(f'refuted bodies (trace lines): {len(refuted)}')
for fn, l in refuted:
    lines.append(f'  REFUTED {fn} {l[:200]} segments={segfns.get(fn, {}).get("kinds")}')
for s in newly:
    lines.append(f'NEWLY FAILING {s} named {nr[s]}: {last_of(nt, nr[s])[:400]}')

with open(f'{out}/roots.tsv', 'w') as tsv:
    tsv.write('symbol\tfn\tstatus\tkind_set\tbaseline_class\tbaseline_last\tnew_class\tnew_last\tceiling_promoted\n')
    for s in sorted(set(br) | set(nr)):
        fn = br.get(s) or nr.get(s)
        status = 'promoted' if s not in nr else ('newly failing' if s not in br else 'fails')
        crow = ceiling.get(s)
        tsv.write('\t'.join([
            s, str(fn), status, segfns.get(fn, {}).get('kind_set', ''),
            class_of(bt, fn) if s in br else '', last_of(bt, fn) if s in br else '',
            class_of(nt, fn) if s in nr else '', last_of(nt, fn) if s in nr else '',
            crow['promoted'] if crow else '']) + '\n')
with open(f'{out}/functions.tsv', 'w') as tsv:
    tsv.write('fn\tsegments\tmembers\tkinds\tkind_set\tverdict\tattempts\tbaseline_last\tlast\n')
    for fn, v in sorted(segfns.items()):
        tsv.write('\t'.join([fn, str(v['segments']), str(v['members']), ','.join(v['kinds']), v['kind_set'],
                             v['verdict'], str(v['attempts']), last_of(bt, fn), v['last']]) + '\n')
json.dump({'promoted': promoted, 'newly_failing': newly, 'mismatches': mism,
           'refuted': [list(x) for x in refuted],
           'promoted_by_kind_set': dict(by_kind),
           'functions_over_segments': {fn: {k: v[k] for k in ('segments', 'members', 'kinds', 'kind_set', 'verdict')}
                                       for fn, v in segfns.items()}},
          open(f'{out}/segments.json', 'w'), indent=1)
open(f'{out}/segments.txt', 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
