#!/usr/bin/env python3
"""OD-233's census follow-ups (design §7) over a baseline census and an OD-233
census of the Darwin x86-64 `core` crate.

Reads each side's stderr.log ([TCG-X86-BODY-TRACE] lines), failed_roots.jsonl
and refusals.jsonl. An attempt is a function's run of trace lines ending at a
refusal line or a `bound rows=` line (the `merged chains=`, `defined cut
inputs` and `stated in parts=` lines are not terminal, as in
parts_census.py). The unkeyed `replay outcome=` lines and `negative-memo hit`
lines a replay prints come before its function's trace lines, so each is
attributed to the next attempt that starts.

Reports, and checks as the stop rule's items:

- named mismatches (`mismatch` in a trace line) and refuted bodies (`Invalid`)
  on the new side;
- the K1 and K2 texts and any `(OD-233)` text anywhere in the new side's
  stderr.log, failed_roots.jsonl or refusals.jsonl;
- functions whose last trace line is the no-observable refusal (OD-115) on the
  new side and not on the baseline (a new NoObservable);
- functions with more attributed `replay outcome=Timeout` lines, or more
  negative-memo timeout hits, than on the baseline (a part that newly times
  out), and bound attempts whose replay was Valid on the baseline and is not
  now.

Also: every trace line of core::wtf8::slice_error_fail on both sides; the
count of cut_pairing's `no machine row writes a register as the definition of`
texts (OD-233b's trigger), in lines and functions, on both sides; per side,
the bound attempts by replay outcome and the attributed unkeyed lines by kind;
the in-parts functions whose part count changed.

Writes followup.txt and followup.json to <out dir> and prints followup.txt.
Exit 1 if any stop-rule item holds.

usage: census233.py <baseline dir> <new dir> <out dir>
"""
import collections
import json
import os
import re
import sys

base, new, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)

TRACE = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
UNKEYED = '[TCG-X86-BODY-TRACE] '
NONTERMINAL = re.compile(
    r'^(stated in parts=\d+|merged chains=\d+ absorbed=\d+|defined cut inputs bytes=\d+ items=\d+)$')
PARTS = re.compile(r'^stated in parts=(\d+)$')
DEFINED = re.compile(r'^defined cut inputs bytes=(\d+) items=(\d+)$')
BOUND = re.compile(r'^bound rows=(\d+) replay=(.*)$')
TIMING = re.compile(r'\b(age_s|recorded_solve_ms|recorded_cpu_ms|process_hit)=\d+')
NOOBS = 'requires a B1, I8, I16, I32 or I64 result, a call or an incoming-memory access'
CUT_PAIRING = 'no machine row writes a register as the definition of'
K1 = 'is defined by a term that is not fixed for the run (OD-233)'
K2 = re.compile(r"defined input \S+ is not claimed on the\s+edge from")
OD233 = '(OD-233)'
WTF8 = '_RNvNtCs7e1ihmkzmZ8_4core4wtf816slice_error_fail'


def outcome_class(replay):
    if replay == 'Valid':
        return 'Valid'
    if replay.startswith('Invalid'):
        return 'Invalid'
    if 'TIMEOUT' in replay or 'Timeout' in replay:
        return 'not certified: timeout'
    if replay.startswith('Unknown (FP abstraction'):
        return 'Unknown (FP abstraction)'
    return 'not certified: ' + re.sub(r'/\S+', '<path>', replay)[:90]


def read(d):
    attempts = collections.defaultdict(list)  # fn -> [attempt]
    pending = {}  # fn -> open attempt
    unattributed = []  # unkeyed lines waiting for the next attempt
    whole = {'cut_pairing_lines': 0, 'k1': 0, 'k2': 0, 'od233': 0}
    cut_pairing_fns = set()
    with open(f'{d}/stderr.log', errors='replace') as fh:
        for lineno, raw in enumerate(fh, 1):
            line = raw.rstrip('\n')
            if CUT_PAIRING in line:
                whole['cut_pairing_lines'] += 1
            if K1 in line:
                whole['k1'] += 1
            if K2.search(line):
                whole['k2'] += 1
            if OD233 in line:
                whole['od233'] += 1
            m = TRACE.match(line)
            if not m:
                if line.startswith(UNKEYED):
                    unattributed.append(TIMING.sub(r'\1=N', line[len(UNKEYED):]))
                continue
            fn, rest = m.group(1), m.group(2)
            if CUT_PAIRING in rest:
                cut_pairing_fns.add(fn)
            att = pending.get(fn)
            if att is None:
                att = {'lines': [], 'unkeyed': unattributed, 'first_line': lineno}
                unattributed = []
                pending[fn] = att
            att['lines'].append(rest)
            if BOUND.match(rest) or not NONTERMINAL.match(rest):
                attempts[fn].append(att)
                del pending[fn]
    for fn, att in pending.items():
        att['lines'].append('(trace ended without a terminal line)')
        attempts[fn].append(att)
    records = {}
    for f in ('failed_roots.jsonl', 'refusals.jsonl'):
        text = open(f'{d}/{f}', errors='replace').read()
        records[f] = {'k1': text.count(K1), 'k2': len(K2.findall(text)), 'od233': text.count(OD233),
                      'cut_pairing': text.count(CUT_PAIRING)}
    return {'attempts': attempts, 'whole': whole, 'cut_pairing_fns': cut_pairing_fns,
            'trailing_unkeyed': unattributed, 'records': records}


def summary(side):
    a = side['attempts']
    bound = collections.Counter()
    unkeyed = collections.Counter()
    for fn, atts in a.items():
        for att in atts:
            bm = BOUND.match(att['lines'][-1])
            if bm:
                bound[outcome_class(bm.group(2))] += 1
            for u in att['unkeyed']:
                unkeyed[re.sub(r'\(.*', '(..)', u)[:110]] += 1
    return bound, unkeyed


B, N = read(base), read(new)
lines = []
stops = []


def say(s=''):
    lines.append(s)


for label, side in (('baseline', B), ('new', N)):
    a = side['attempts']
    bound, unkeyed = summary(side)
    say(f'{label}: {len(a)} functions traced, {sum(map(len, a.values()))} attempts')
    say(f'  bound attempts by replay: {dict(bound.most_common())}')
    say(f'  unkeyed lines attributed to the next attempt: {sum(unkeyed.values())}; '
        f'trailing (no attempt after): {len(side["trailing_unkeyed"])}')
    for k, v in unkeyed.most_common():
        say(f'    {v:5d}  {k}')
    w = side['whole']
    say(f'  cut_pairing texts (`{CUT_PAIRING} …`): {w["cut_pairing_lines"]} lines, '
        f'{len(side["cut_pairing_fns"])} functions; records: '
        f'failed_roots {side["records"]["failed_roots.jsonl"]["cut_pairing"]}, '
        f'refusals {side["records"]["refusals.jsonl"]["cut_pairing"]}')
    for fn in sorted(side['cut_pairing_fns']):
        say(f'    {fn}')
    say(f'  K1 texts {w["k1"]}, K2 texts {w["k2"]}, `(OD-233)` texts {w["od233"]} in stderr.log; '
        f'records: {side["records"]}')

a_b, a_n = B['attempts'], N['attempts']

# Named mismatches and refuted bodies (new side).
mismatch = [(fn, l) for fn, atts in a_n.items() for att in atts for l in att['lines'] if 'mismatch' in l]
refuted = [(fn, l) for fn, atts in a_n.items() for att in atts for l in att['lines'] if 'Invalid' in l]
say(f'named mismatches (new): {len(mismatch)}')
say(f'refuted bodies (new): {len(refuted)} lines, {len({fn for fn, _ in refuted})} functions')
for fn, l in mismatch + refuted:
    say(f'  {fn} {l[:300]}')
if mismatch:
    stops.append(f'{len(mismatch)} named mismatch lines')
if refuted:
    stops.append(f'{len(refuted)} refuted body lines')
w = N['whole']
rec = N['records']
k1 = w['k1'] + rec['failed_roots.jsonl']['k1'] + rec['refusals.jsonl']['k1']
k2 = w['k2'] + rec['failed_roots.jsonl']['k2'] + rec['refusals.jsonl']['k2']
od = w['od233'] + rec['failed_roots.jsonl']['od233'] + rec['refusals.jsonl']['od233']
say(f'K1 texts (new, stderr and records): {k1}; K2 texts: {k2}; any `(OD-233)` text: {od}')
if k1 or k2 or od:
    stops.append(f'K1 {k1}, K2 {k2}, (OD-233) {od} texts')

# NoObservable (OD-115) by last trace line.
noobs_b = {fn for fn, atts in a_b.items() if NOOBS in atts[-1]['lines'][-1]}
noobs_n = {fn for fn, atts in a_n.items() if NOOBS in atts[-1]['lines'][-1]}
new_noobs = sorted(noobs_n - noobs_b)
say(f'no-observable functions (last line): baseline {len(noobs_b)}, new {len(noobs_n)}; '
    f'new {len(new_noobs)}, gone {len(noobs_b - noobs_n)}')
for fn in new_noobs:
    say(f'  NEW NoObservable: {fn}')
if new_noobs:
    stops.append(f'{len(new_noobs)} new NoObservable functions')


# Timeouts by function: attributed `replay outcome=Timeout` lines and
# negative-memo timeout hits, and bound replays with a timeout reason.
def timeouts(atts):
    t = collections.Counter()
    for att in atts:
        for u in att['unkeyed']:
            if u.startswith('replay outcome=Timeout'):
                t['outcome=Timeout'] += 1
            if u.startswith('replay negative-memo hit') and 'kind=timeout' in u:
                t['memo timeout'] += 1
        bm = BOUND.match(att['lines'][-1])
        if bm and outcome_class(bm.group(2)) == 'not certified: timeout':
            t['bound timeout'] += 1
    return t


newly_timing_out = []
for fn in sorted(set(a_b) | set(a_n)):
    tb, tn = timeouts(a_b.get(fn, [])), timeouts(a_n.get(fn, []))
    if any(tn[k] > tb[k] for k in tn):
        newly_timing_out.append((fn, dict(tb), dict(tn)))
tot_b = sum((timeouts(v) for v in a_b.values()), collections.Counter())
tot_n = sum((timeouts(v) for v in a_n.values()), collections.Counter())
say(f'timeouts (attributed): baseline {dict(tot_b)}, new {dict(tot_n)}')
say(f'functions with more timeouts than on the baseline: {len(newly_timing_out)}')
for fn, tb, tn in newly_timing_out:
    say(f'  MORE TIMEOUTS {fn}: baseline {tb} -> new {tn}')
if newly_timing_out:
    stops.append(f'{len(newly_timing_out)} functions with more timeouts')

# Bound attempts whose replay was Valid on the baseline and is not now (by
# attempt index), and changes in rows or part counts.
lost_valid, rows_changed, parts_changed, gained_valid = [], [], [], []
for fn in sorted(set(a_b) & set(a_n)):
    for k, (x, y) in enumerate(zip(a_b[fn], a_n[fn])):
        bx, by = BOUND.match(x['lines'][-1]), BOUND.match(y['lines'][-1])
        if bx and by:
            if bx.group(1) != by.group(1):
                rows_changed.append((fn, k, bx.group(1), by.group(1)))
            if bx.group(2) == 'Valid' and by.group(2) != 'Valid':
                lost_valid.append((fn, k, by.group(2)))
            if bx.group(2) != 'Valid' and by.group(2) == 'Valid':
                gained_valid.append((fn, k, bx.group(2)))
        px = [int(PARTS.match(l).group(1)) for l in x['lines'] if PARTS.match(l)]
        py = [int(PARTS.match(l).group(1)) for l in y['lines'] if PARTS.match(l)]
        if px != py:
            parts_changed.append((fn, k, px, py, any(DEFINED.match(l) for l in y['lines'])))
say(f'bound attempts Valid on the baseline and not now: {len(lost_valid)}')
for fn, k, r in lost_valid:
    say(f'  LOST VALID {fn} attempt {k}: {r[:300]}')
if lost_valid:
    stops.append(f'{len(lost_valid)} bound attempts no longer Valid')
say(f'bound attempts not Valid on the baseline and Valid now: {len(gained_valid)}')
for fn, k, r in gained_valid:
    say(f'  gained {fn} attempt {k} (was {r[:120]})')
say(f'bound attempts whose row count changed: {len(rows_changed)}')
for fn, k, x, y in rows_changed:
    say(f'  ROWS {fn} attempt {k}: {x} -> {y}')
say(f'attempts whose part count changed: {len(parts_changed)}')
for fn, k, x, y, d in parts_changed:
    say(f'  parts {fn} attempt {k}: {x} -> {y}{" (defines inputs)" if d else ""}')
attempt_count_changed = sorted(fn for fn in set(a_b) & set(a_n) if len(a_b[fn]) != len(a_n[fn]))
say(f'functions whose attempt count changed: {len(attempt_count_changed)}')
for fn in attempt_count_changed:
    say(f'  {fn}: {len(a_b[fn])} -> {len(a_n[fn])}')
only_b, only_n = sorted(set(a_b) - set(a_n)), sorted(set(a_n) - set(a_b))
say(f'functions traced only on the baseline: {len(only_b)}; only on the new side: {len(only_n)}')
for fn in only_b[:20]:
    say(f'  only baseline: {fn}')
for fn in only_n[:20]:
    say(f'  only new: {fn}')

# Definitions per function (last attempt) and the in-parts outcome.
defining = {}
for fn, atts in a_n.items():
    for l in atts[-1]['lines']:
        dm = DEFINED.match(l)
        if dm:
            defining[fn] = (int(dm.group(1)), int(dm.group(2)))
inparts_n = {fn for fn, atts in a_n.items() if any(PARTS.match(l) for l in atts[-1]['lines'])}
say(f'in-parts functions (new, last attempt): {len(inparts_n)}; defining inputs: {len(defining)}; '
    f'bytes {sum(b for b, _ in defining.values())}, items {sum(i for _, i in defining.values())}')
hist = collections.Counter()
for b, i in defining.values():
    hist[(b, i)] += 1
say('  (bytes, items) -> functions: ' + ', '.join(f'{k}: {v}' for k, v in sorted(hist.items())))

# The OD-233 target.
for label, a in (('baseline', a_b), ('new', a_n)):
    say(f'{WTF8} ({label}):')
    for k, att in enumerate(a.get(WTF8, [])):
        for u in att['unkeyed']:
            say(f'  attempt {k} (unkeyed before it) {u[:200]}')
        for l in att['lines']:
            say(f'  attempt {k}: {l[:300]}')

say('STOP RULE: ' + ('BROKEN: ' + '; '.join(stops) if stops else
                     'holds (no named mismatch, no refuted body, no K1/K2/(OD-233) text, no new '
                     'NoObservable, no function with more timeouts, no bound attempt lost Valid)'))
json.dump({'stops': stops, 'new_noobs': new_noobs, 'newly_timing_out': newly_timing_out,
           'lost_valid': lost_valid, 'gained_valid': gained_valid, 'rows_changed': rows_changed,
           'parts_changed': parts_changed, 'defining': defining,
           'cut_pairing_fns': {'baseline': sorted(B['cut_pairing_fns']),
                               'new': sorted(N['cut_pairing_fns'])}},
          open(f'{out}/followup.json', 'w'), indent=1)
open(f'{out}/followup.txt', 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
sys.exit(1 if stops else 0)
