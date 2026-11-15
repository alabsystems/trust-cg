#!/usr/bin/env python3
"""The slice-24c census stop rule, over the three censuses at once.

A stop is any of:
- a newly failing root (O2 against census-o2-s25, O0 against census-o0-s25);
- a named mismatch (a trace line holding `mismatch`) in any census;
- a refuted body (a trace line holding `Invalid`) other than the two known
  attempts of `core::wtf8::slice_error_fail` (`bound rows=555` and `bound
  rows=571`, `replay=Invalid (refuted)`: OD-227's cut-interface gap, which
  slice OD-233 handles), in any census;
- any O0 change: the failed-root and typed-refusal records not
  byte-identical to census-o0-s25's, or any trace_diff.py anomaly about a
  function (a function traced on one side only, any of its trace lines
  changed, a promoted or newly failing root, a record changed, a mismatch or
  a refuted body).

trace_diff.py's anomalies about the UNKEYED trace lines (replay outcomes and
negative-memo hits, which name no function: how many whole replays missed
their wall-clock deadline before a fallback decided) are printed as `NOTE:`
lines with their counts, every one of them; they are not records.

Prints every check and `STOP RULE HOLDS`, or `STOP:` lines; exits 1 on a stop.

usage: stop_rule.py <runs dir> <comparison dir>   (~/tcg-scratch/runs, s24c-run/census)
"""
import collections
import filecmp
import json
import os
import re
import sys

runs, comp = sys.argv[1:3]
PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
KNOWN_FN = '_RNvNtCs7e1ihmkzmZ8_4core4wtf816slice_error_fail'
KNOWN = collections.Counter({(KNOWN_FN, 'bound rows=555 replay=Invalid (refuted)'): 1,
                             (KNOWN_FN, 'bound rows=571 replay=Invalid (refuted)'): 1})
stops = []


def traces(d):
    by_fn = collections.defaultdict(list)
    for line in open(f'{d}/stderr.log', errors='replace'):
        m = PAT.match(line.rstrip('\n'))
        if m:
            by_fn[m.group(1)].append(m.group(2))
    return by_fn


def symbols(d):
    return {json.loads(l)['symbol'] for l in open(f'{d}/failed_roots.jsonl') if l.strip()}


for opt in ('2', '0', '3'):
    new = f'{runs}/census-o{opt}-s24c'
    if not os.path.exists(f'{new}/failed_roots.jsonl'):
        stops.append(f'O{opt}: census missing ({new})')
        continue
    nt = traces(new)
    mism = [(fn, l) for fn, ls in nt.items() for l in ls if 'mismatch' in l]
    refuted = collections.Counter((fn, l) for fn, ls in nt.items() for l in ls if 'Invalid' in l)
    other = refuted - KNOWN
    print(f'O{opt}: failed roots {len(symbols(new))}; named mismatches {len(mism)}; refuted trace lines '
          f'{sum(refuted.values())} ({sum((refuted & KNOWN).values())} known, {sum(other.values())} other)')
    for fn, l in mism:
        stops.append(f'O{opt}: named mismatch {fn}: {l[:300]}')
    for (fn, l), n in other.items():
        stops.append(f'O{opt}: refuted body {fn} x{n}: {l[:200]}')
    if opt in ('2', '0'):
        base = f'{runs}/census-o{opt}-s25'
        newly = sorted(symbols(new) - symbols(base))
        promoted = len(symbols(base) - symbols(new))
        print(f'O{opt}: against census-o{opt}-s25: {len(symbols(base))} -> {len(symbols(new))} failed roots, '
              f'{promoted} promoted, {len(newly)} newly failing')
        for s in newly:
            stops.append(f'O{opt}: newly failing root {s}')
    if opt == '0':
        base = f'{runs}/census-o0-s25'
        for f in ('failed_roots.jsonl', 'refusals.jsonl'):
            same = filecmp.cmp(f'{base}/{f}', f'{new}/{f}', shallow=False)
            print(f'O0: {f} {"byte-identical" if same else "DIFFERS"}')
            if not same:
                stops.append(f'O0: {f} differs from census-o0-s25')
        td = f'{comp}/o0/trace_diff/trace_diff.json'
        at = f'{comp}/o0/trace_diff/anomalies.txt'
        if not os.path.exists(td) or not os.path.exists(at):
            stops.append('O0: no trace_diff.json or anomalies.txt')
        else:
            summary = json.load(open(td))['summary']
            # One anomaly per line; a multi-line one continues indented.
            found = [a for a in open(at).read().split('\n') if a and not a.startswith(' ')]
            unkeyed = [a for a in found if a.startswith('unkeyed trace line count ')]
            keyed = [a for a in found if not a.startswith('unkeyed trace line count ')]
            print(f'O0: trace_diff.py anomalies {summary["anomalies"]} ({len(keyed)} about a function, '
                  f'{len(unkeyed)} unkeyed outcome counts); functions with any trace line changed '
                  f'{summary["functions with any trace line changed once the detail is stripped"]}')
            if len(found) != summary['anomalies']:
                stops.append(f'O0: anomalies.txt lists {len(found)} anomalies, trace_diff.json {summary["anomalies"]}')
            for a in keyed:
                stops.append(f'O0: trace_diff.py: {a[:300]}')
            for a in unkeyed:
                print(f'NOTE: O0 {a[:300]}')
for s in stops:
    print('STOP:', s)
print('STOP RULE HOLDS' if not stops else f'STOP RULE BROKEN: {len(stops)} stop(s)')
sys.exit(1 if stops else 0)
