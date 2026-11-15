#!/usr/bin/env python3
"""The slice-25.0 no-verdict-change check: compare two Darwin core census runs
(the baseline, then the S25.0 census) function by function.

S25.0 changes the text of one refusal, the stack-slot scan's, by inserting
": block B row r, Op with operands [..] (n such row(s))" after its fixed
prefix (and before an OverQuotient suffix). This script strips exactly that
detail from the new census's trace lines and then requires:

- the same failed-root symbols, each with a byte-identical record
  (failed_roots.jsonl), and the same typed refusals (refusals.jsonl);
- the same traced functions, each with the same trace lines in the same order
  once the detail is stripped (the last line is the verdict);
- the detail present on every new S line and absent from every baseline line.

Every other difference is an anomaly. Prints a summary, writes anomalies.txt,
s_records.tsv (each S function's baseline and new last line) and
trace_diff.json to <out dir>; exits 1 on any anomaly.

usage: trace_diff.py <baseline dir> <new dir> <out dir>
"""
import collections
import json
import os
import re
import sys

base, new, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)

PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
TIMING = re.compile(r'\b(age_s|recorded_solve_ms|recorded_cpu_ms)=\d+')
S_PREFIX = 'a row that references a stack slot outside a modelled `[slot + disp]` operand'
# The S25.0 detail (`unmodelled_stack_slot_rows`): the first offending row and
# the count. Operands are a Debug list; the count suffix ends the detail. The
# slice-25 production text names the scaled-index base after `operand`; the
# S25.0 diagnostic's did not, and both match.
DETAIL = re.compile(
    re.escape(S_PREFIX)
    + r'(?: or scaled-index base)?: block Block\(\d+\) row (?:\d+|\(not laid out\) index \d+), \w+ with operands \[.*?\] '
    r'\(\d+ such rows?\)')


def traces(d):
    """Trace lines by function, and the trace lines no function keys (the
    replay outcomes), as a multiset."""
    by_fn = collections.defaultdict(list)
    unkeyed = collections.Counter()
    for line in open(f'{d}/stderr.log', errors='replace'):
        line = line.rstrip('\n')
        m = PAT.match(line)
        if m:
            by_fn[m.group(1)].append(m.group(2))
        elif line.startswith('[TCG-X86-BODY-TRACE]'):
            # Wall-clock fields of a negative-memo hit vary from run to run.
            unkeyed[TIMING.sub(r'\1=N', line)] += 1
    return by_fn, unkeyed


def jsonl(path, key):
    found = collections.defaultdict(list)
    for line in open(path):
        line = line.strip()
        if line:
            record = json.loads(line)
            found[key(record)].append(line)
    return found


def strip(text):
    return DETAIL.sub(S_PREFIX, text)


anomalies = []
(bt, bu), (nt, nu) = traces(base), traces(new)
for line in sorted(set(bu) | set(nu)):
    if bu[line] != nu[line]:
        anomalies.append(f'unkeyed trace line count {bu[line]} -> {nu[line]}: {line[:300]}')
only_base = sorted(set(bt) - set(nt))
only_new = sorted(set(nt) - set(bt))
for fn in only_base:
    anomalies.append(f'traced only in the baseline: {fn}')
for fn in only_new:
    anomalies.append(f'traced only in the new census: {fn}')

s_lines_base = sum(1 for ls in bt.values() for l in ls if S_PREFIX in l)
s_lines_new = sum(1 for ls in nt.values() for l in ls if S_PREFIX in l)
detail_lines_new = sum(1 for ls in nt.values() for l in ls if DETAIL.search(l))
for fn, ls in bt.items():
    for l in ls:
        if DETAIL.search(l):
            anomalies.append(f'baseline line already carries the detail: {fn}')
for fn, ls in nt.items():
    for l in ls:
        if S_PREFIX in l and not DETAIL.search(l):
            anomalies.append(f'new S line without the detail: {fn}: {l[:300]}')
        if S_PREFIX in l and len(DETAIL.findall(l)) != 1:
            anomalies.append(f'new S line with {len(DETAIL.findall(l))} details: {fn}')

# The scan's order is fixed, so every attempt of one function names one row.
for fn, ls in nt.items():
    named = {l for l in ls if S_PREFIX in l}
    if len(named) > 1:
        anomalies.append(f'attempts of one function name different S rows: {fn}')
s_attempts_agree = sum(1 for ls in nt.values() if len({l for l in ls if S_PREFIX in l}) == 1)

last_changed = []      # last line differs after stripping (a verdict change)
lines_changed = []     # any line differs after stripping
s_records_changed = [] # last line differs before stripping, and is an S line
with open(f'{out}/s_records.tsv', 'w') as tsv:
    tsv.write('fn\tbaseline_last\tnew_last\n')
    for fn in sorted(set(bt) & set(nt)):
        b, n = bt[fn], nt[fn]
        ns = [strip(l) for l in n]
        if b[-1] != ns[-1]:
            last_changed.append(fn)
            anomalies.append(f'last trace line changed: {fn}\n    base: {b[-1][:400]}\n    new:  {n[-1][:400]}')
        if b != ns:
            lines_changed.append(fn)
            if b[-1] == ns[-1]:
                anomalies.append(f'an earlier trace line changed (last identical): {fn} '
                                 f'({len(b)} lines -> {len(n)} lines)')
        if b[-1] != n[-1] and S_PREFIX in n[-1]:
            s_records_changed.append(fn)
        if S_PREFIX in n[-1] or S_PREFIX in b[-1]:
            tsv.write(f'{fn}\t{b[-1]}\t{n[-1]}\n')

# Failed roots and typed refusals: byte-identical records.
br = jsonl(f'{base}/failed_roots.jsonl', lambda r: r['symbol'])
nr = jsonl(f'{new}/failed_roots.jsonl', lambda r: r['symbol'])
promoted = sorted(set(br) - set(nr))
newly = sorted(set(nr) - set(br))
root_text_changed = sorted(s for s in set(br) & set(nr) if sorted(br[s]) != sorted(nr[s]))
for s in promoted:
    anomalies.append(f'promoted root: {s}')
for s in newly:
    anomalies.append(f'newly failing root: {s}')
for s in root_text_changed:
    anomalies.append(f'failed-root record text changed: {s}')
bf = jsonl(f'{base}/refusals.jsonl', lambda r: r.get('function'))
nf = jsonl(f'{new}/refusals.jsonl', lambda r: r.get('function'))
refusal_changed = sorted(f for f in set(bf) | set(nf) if sorted(bf.get(f, [])) != sorted(nf.get(f, [])))
for f in refusal_changed:
    anomalies.append(f'typed refusal record changed: {f}')

mismatch_new = sorted(fn for fn, ls in nt.items() if any('mismatch' in l for l in ls))
refuted_new = sorted(fn for fn, ls in nt.items() if any('Invalid' in l for l in ls))
mismatch_base = sorted(fn for fn, ls in bt.items() if any('mismatch' in l for l in ls))
refuted_base = sorted(fn for fn, ls in bt.items() if any('Invalid' in l for l in ls))
for fn in mismatch_new:
    anomalies.append(f'named mismatch: {fn}')
for fn in refuted_new:
    anomalies.append(f'refuted body: {fn}')

s_last_new = sorted(fn for fn, ls in nt.items() if S_PREFIX in ls[-1])
s_last_base = sorted(fn for fn, ls in bt.items() if S_PREFIX in ls[-1])
summary = {
    'traced functions (baseline, new)': [len(bt), len(nt)],
    'trace lines (baseline, new)': [sum(map(len, bt.values())), sum(map(len, nt.values()))],
    'unkeyed trace lines (baseline, new)': [sum(bu.values()), sum(nu.values())],
    'failed roots (baseline, new)': [len(br), len(nr)],
    'promoted': len(promoted),
    'newly failing': len(newly),
    'failed-root records whose text changed': len(root_text_changed),
    'typed refusal records changed': len(refusal_changed),
    'named mismatches (baseline, new)': [len(mismatch_base), len(mismatch_new)],
    'refuted bodies (baseline, new)': [len(refuted_base), len(refuted_new)],
    'functions whose last line is S (baseline, new)': [len(s_last_base), len(s_last_new)],
    'S trace lines (baseline, new; new lines carrying the detail)': [s_lines_base, s_lines_new, detail_lines_new],
    'S records changed (last line differs, new last line S)': len(s_records_changed),
    'new S functions whose attempts all name one row': s_attempts_agree,
    'functions whose last line changed once the detail is stripped': len(last_changed),
    'functions with any trace line changed once the detail is stripped': len(lines_changed),
    'anomalies': len(anomalies),
}
json.dump({'summary': summary, 'promoted': promoted, 'newly_failing': newly,
           'last_changed': last_changed, 'lines_changed': lines_changed,
           's_records_changed': s_records_changed, 's_last_new': s_last_new},
          open(f'{out}/trace_diff.json', 'w'), indent=1)
open(f'{out}/anomalies.txt', 'w').write(''.join(a + '\n' for a in anomalies))
for k, v in summary.items():
    print(f'{k}: {v}')
for a in anomalies[:40]:
    print('ANOMALY', a)
sys.exit(1 if anomalies else 0)
