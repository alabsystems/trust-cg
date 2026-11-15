#!/usr/bin/env python3
"""Where two censuses' UNKEYED replay lines differ (trace_diff.py's `unkeyed
trace line count` anomalies): each replay-outcome or negative-memo line names
no function, and is printed while the replay of the function whose next keyed
[TCG-X86-BODY-TRACE] line follows it runs, so it is attributed to that
function (per codegen attempt). Prints, for every function whose attributed
lines differ, both sides' lines (timing fields and counterexample values
masked) and both sides' verdict lines, and the totals; exits 1 if any such
function's verdict lines or keyed lines differ.

usage: o0_outcomes.py <baseline dir> <new dir>
"""
import collections
import re
import sys

PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
TIMING = re.compile(r'\b(age_s|recorded_solve_ms|recorded_cpu_ms)=\d+')


def attribute(d):
    per = collections.defaultdict(list)
    keyed = collections.defaultdict(list)
    pending = []
    for line in open(f'{d}/stderr.log', errors='replace'):
        line = line.rstrip('\n')
        m = PAT.match(line)
        if m:
            if pending:
                per[m.group(1)].append(tuple(pending))
                pending = []
            keyed[m.group(1)].append(m.group(2))
        elif line.startswith('[TCG-X86-BODY-TRACE]'):
            text = TIMING.sub(r'\1=N', line[len('[TCG-X86-BODY-TRACE] '):])
            pending.append(re.sub(r'\(\[.*\]\)', '([..])', text)[:110])
    return per, keyed, pending


(bp, bk, btail), (np_, nk, ntail) = attribute(sys.argv[1]), attribute(sys.argv[2])
bad = 0
differ = sorted(fn for fn in set(bp) | set(np_) if bp.get(fn) != np_.get(fn))
for fn in differ:
    same_keyed = bk.get(fn) == nk.get(fn)
    bad += not same_keyed
    verdicts = lambda k: [l for l in k.get(fn, []) if l.startswith('bound rows=')]
    print(f'FN {fn}')
    print(f'  baseline lines: {bp.get(fn)}')
    print(f'  new lines:      {np_.get(fn)}')
    print(f'  verdicts: baseline {verdicts(bk)}, new {verdicts(nk)}; keyed lines identical: {same_keyed}')
count = lambda per, key: sum(1 for groups in per.values() for g in groups for l in g if key in l)
print(f'functions whose unkeyed lines differ: {len(differ)}; of them with a keyed difference: {bad}')
for key in ('outcome=Timeout', 'outcome=Unknown', 'outcome=CounterExample', 'negative-memo hit'):
    print(f'`{key}` lines: baseline {count(bp, key)}, new {count(np_, key)}')
print(f'unattributed trailing lines: baseline {len(btail)}, new {len(ntail)}')
sys.exit(1 if bad else 0)
