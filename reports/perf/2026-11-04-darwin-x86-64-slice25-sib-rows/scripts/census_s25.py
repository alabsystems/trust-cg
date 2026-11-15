#!/usr/bin/env python3
"""Slice 25's census follow-ups (design §7), over the O2 baseline and the
slice-25 O2 census. Each failed root is keyed by the function its proof
failure names and that function's last [TCG-X86-BODY-TRACE] line (its
first refusal, as root_classes.py and firsthit.py read it).

- The baseline's first hit of each root (S, R:<Op> as firsthit.py names
  them, other), and what became of it: promoted, or the new last line.
- The promoted roots by their baseline first hit and refusal.
- The remaining roots by their new first hit and by their normalized new
  refusal.
- The baseline's R:AddMR roots, and how many now end at `has no row
  attributed` (the fused row, which carries no TV-1 stamp).
- The baseline's S roots, and how many now end at an Indexed `candidate
  offsets` refusal (a constant index lost); also every new root that does.
- Every newly failing root, with its last line.

Writes followup.txt, roots.tsv (one row per baseline or new root) and
followup.json to <out dir>, and prints followup.txt.

usage: census_s25.py <baseline dir> <new dir> <out dir>
"""
import collections
import json
import os
import re
import sys

base, new, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)

PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
FN_IN_MSG = re.compile(r'non_verified proof entry \S+ in (\S+?): ')
S_KEY = 'references a stack slot outside'
NO_ROW = 'has no row attributed to a LIR instruction'
CANDIDATES = 'candidate offsets'


def last_lines(d):
    last = {}
    for line in open(f'{d}/stderr.log', errors='replace'):
        m = PAT.match(line.rstrip('\n'))
        if m:
            last[m.group(1)] = m.group(2)
    return last


def roots(d):
    found = {}
    for line in open(f'{d}/failed_roots.jsonl'):
        if not line.strip():
            continue
        r = json.loads(line)
        m = FN_IN_MSG.search(r.get('message', ''))
        found[r['symbol']] = m.group(1) if m else None
    return found


def first_hit(t):
    """firsthit.py's key."""
    if S_KEY in t:
        return 'S'
    if 'outside the body domain (BODY_OPCODES' in t or 'is outside the body domain (' in t:
        d = t.split('Nop): ')[-1]
        return 'R:' + d.split(' with ')[0].split(' reads ')[0]
    return 'other'


# The stack-slot scan's row detail (slice 25.0; slice 25 adds the base
# phrase), which the baseline's text does not carry.
S_DETAIL = re.compile(r'( or scaled-index base)?: block Block\(\d+\) row (?:\d+|\(not laid out\) index \d+), '
                      r'(\w+) with operands \[.*?\] \(\d+ such rows?\)')
DOMAIN = re.compile(r'is outside the body domain \(MovRR, .*?operand-free Nop\): ')
SEVERAL = re.compile(r'lowers rows of several LIR blocks \[[^\]]*\]: .*?(?=; not contracted: |$)')


def norm(t, keep_op=True):
    """A refusal without its function-specific numbers and operand lists; the
    scan's detail becomes its opcode (keep_op) or nothing."""
    if t.startswith('bound rows='):
        return ('bound, replays Valid' if 'replay=Valid' in t else
                'bound, REFUTED' if 'Invalid' in t else 'bound, no independently checked proof')
    q = ' (over the quotient)' if 'over the merged-chain quotient' in t else ''
    t = re.sub(r' \(over the merged-chain quotient: .*\)$', '', t)
    t = t.replace('unsupported source-bound x86-64 body: ', '')
    t = S_DETAIL.sub(lambda m: f': {m.group(2)}' if keep_op else '', t)
    t = DOMAIN.sub('is outside the body domain (BODY_OPCODES): ', t)
    t = SEVERAL.sub('lowers rows of several LIR blocks', t)
    t = re.sub(r'Block\(\d+\)', 'Block(N)', t)
    t = re.sub(r'\b(instruction|row|access|slot|table) \d+', r'\1 N', t)
    t = re.sub(r'\(not laid out\) index \d+', 'N', t)
    t = re.sub(r'\(\d+ such rows?\)', '(K such rows)', t)
    t = re.sub(r'\[[^\[\]]*\]', '[..]', t)
    t = re.sub(r'\{[^{}]*\}', '{..}', t)
    t = re.sub(r'\b\d+\b', 'N', t)
    return t[:320] + q


bl, nl = last_lines(base), last_lines(new)
br, nr = roots(base), roots(new)


def line_of(side_last, fn):
    if fn is None:
        return '(no fn in message)'
    return side_last.get(fn, '(named fn untraced)')


promoted = sorted(set(br) - set(nr))
newly = sorted(set(nr) - set(br))
lines = [f'baseline failed roots: {len(br)}', f'new failed roots: {len(nr)}',
         f'promoted: {len(promoted)}', f'newly failing: {len(newly)}']

# Baseline first hit -> outcome.
by_hit = collections.defaultdict(collections.Counter)
for s, fn in br.items():
    hit = first_hit(line_of(bl, fn))
    by_hit[hit]['promoted' if s not in nr else 'remains'] += 1
lines.append('baseline first hit: roots, promoted, remaining')
for hit, c in sorted(by_hit.items(), key=lambda x: -sum(x[1].values())):
    lines.append(f'  {hit:24s} {sum(c.values()):5d} {c["promoted"]:5d} {c["remains"]:5d}')

promoted_by = collections.Counter(norm(line_of(bl, br[s])) for s in promoted)
lines.append('promoted roots by their baseline refusal:')
for k, n in promoted_by.most_common():
    lines.append(f'  {n:5d}  {k}')

remaining = sorted(set(nr) & set(br)) + newly
remain_hit = collections.Counter(first_hit(line_of(nl, nr[s])) for s in nr)
lines.append('new failed roots by their first hit:')
for k, n in remain_hit.most_common():
    lines.append(f'  {n:5d}  {k}')
remain_by = collections.Counter(norm(line_of(nl, nr[s])) for s in nr)
lines.append('new failed roots by their normalized refusal:')
for k, n in remain_by.most_common(60):
    lines.append(f'  {n:5d}  {k}')

# Roots whose first hit moved but which still fail: baseline hit -> new refusal.
moved = collections.Counter()
for s in sorted(set(nr) & set(br)):
    b, n = line_of(bl, br[s]), line_of(nl, nr[s])
    if first_hit(b) != 'other' or first_hit(n) != 'other':
        if norm(b, keep_op=False) != norm(n, keep_op=False):
            moved[(first_hit(b), norm(n))] += 1
lines.append('remaining S/R roots whose refusal changed: baseline first hit -> new refusal')
for (h, n), k in moved.most_common(60):
    lines.append(f'  {k:5d}  {h} -> {n}')

addmr = [s for s, fn in br.items() if first_hit(line_of(bl, fn)) == 'R:AddMR']
addmr_out = collections.Counter('promoted' if s not in nr else norm(line_of(nl, nr[s])) for s in addmr)
addmr_no_row = sum(1 for s in addmr if s in nr and NO_ROW in line_of(nl, nr[s]))
lines.append(f'baseline R:AddMR roots: {len(addmr)}; now ending at `{NO_ROW}`: {addmr_no_row}')
for k, n in addmr_out.most_common():
    lines.append(f'  {n:5d}  {k}')
addmr_new = [s for s, fn in nr.items() if first_hit(line_of(nl, fn)) == 'R:AddMR' or
             ('AddMR' in line_of(nl, fn) and NO_ROW in line_of(nl, fn))]
lines.append(f'new roots naming AddMR at their refusal or ending at `{NO_ROW}` with AddMR: {len(addmr_new)}')
no_row_all = sum(1 for s, fn in nr.items() if NO_ROW in line_of(nl, fn))
lines.append(f'new roots ending at `{NO_ROW}` (any): {no_row_all}; baseline: '
             f'{sum(1 for s, fn in br.items() if NO_ROW in line_of(bl, fn))}')

s_roots = [s for s, fn in br.items() if first_hit(line_of(bl, fn)) == 'S']
s_out = collections.Counter('promoted' if s not in nr else norm(line_of(nl, nr[s])) for s in s_roots)
s_cand = sum(1 for s in s_roots if s in nr and CANDIDATES in line_of(nl, nr[s]))
lines.append(f'baseline S roots: {len(s_roots)}; now ending at an Indexed `{CANDIDATES}` refusal: {s_cand}')
for k, n in s_out.most_common():
    lines.append(f'  {n:5d}  {k}')
cand_all = sum(1 for s, fn in nr.items() if CANDIDATES in line_of(nl, fn))
lines.append(f'new roots ending at a `{CANDIDATES}` refusal (any): {cand_all}; baseline: '
             f'{sum(1 for s, fn in br.items() if CANDIDATES in line_of(bl, fn))}')

for s in newly:
    lines.append(f'NEWLY FAILING {s} named {nr[s]}: {line_of(nl, nr[s])[:400]}')

with open(f'{out}/roots.tsv', 'w') as tsv:
    tsv.write('symbol\tfn\tbaseline_hit\tbaseline_last\tnew_status\tnew_last\n')
    for s in sorted(set(br) | set(nr)):
        fn = br.get(s) or nr.get(s)
        status = 'promoted' if s not in nr else ('newly failing' if s not in br else 'fails')
        tsv.write(f'{s}\t{fn}\t{first_hit(line_of(bl, br[s])) if s in br else ""}\t'
                  f'{line_of(bl, br[s]) if s in br else ""}\t{status}\t'
                  f'{line_of(nl, nr[s]) if s in nr else ""}\n')
json.dump({'promoted': promoted, 'newly_failing': newly, 'addmr_roots': addmr,
           'addmr_no_row': addmr_no_row, 's_roots': s_roots, 's_candidate_offsets': s_cand},
          open(f'{out}/followup.json', 'w'), indent=1)
open(f'{out}/followup.txt', 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
