#!/usr/bin/env python3
"""Per-part AY and Clean times of two Darwin x86-64 `core` censuses run with
the `solve-trace` knob: the OD-233 census and the re-run of the baseline
dylib (census.sh runs them back to back on the same host).

The knob prints one `TCG_SOLVE_TRACE` line per solve, per proof check and per
promoted result, each naming its obligation. A body theorem's obligation is
named by the theorem's constant name and, in parts, ` | part k of n` (plus
` | generalized` or a claim for its fallbacks), not by its function, so each
line is attributed by position: a replay prints its solve and check lines
before its function's [TCG-X86-BODY-TRACE] lines, and every such line before
an attempt's first trace line belongs to that attempt (attempts as in
parts_census.py). A line whose part count disagrees with the attempt's
`stated in parts=` is counted as an attribution anomaly.

Per part: AY seconds (resident `server_solve` and `server_timeout`, fresh
`live_solve`), Clean seconds (`clean_check`), the query's bytes (the solve
lines' `smt2_bytes`) and the promoted results. Parts are paired across the
two censuses by (function, attempt, part label). The OD-233 side's
`defined cut inputs` line splits the functions into those that define
inputs and those that do not; in the second group every paired part that
both sides solved must have the same query bytes (its statement is
unchanged), and a difference is reported.

Writes times.txt, parts.tsv and times.json to <out dir> and prints times.txt.

usage: part_times.py <OD-233 census dir> <baseline re-run dir> <out dir>
"""
import collections
import json
import os
import re
import sys

new, base, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)

BODY = ('Source-bound x86-64 whole-body theorem (System V, pre-RA ISel): the replayed body '
        'theorem credits every covered value row')
NAME = r'obligation="((?:[^"\\]|\\.)*)"'
TIMED = re.compile(r'^TCG_SOLVE_TRACE (server_solve|server_timeout|live_solve|clean_check) '
                   r'([0-9.]+)s ' + NAME + r'(.*)$')
PROMO = re.compile(r'^TCG_SOLVE_TRACE promotion_result ' + NAME + r' result=(.*)$')
OTHER = re.compile(r'^TCG_SOLVE_TRACE (\w+) .*?' + NAME + r'(.*)$')
BYTES = re.compile(r'\bsmt2_bytes=(\d+)')
TRACE = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
NONTERMINAL = re.compile(
    r'^(stated in parts=\d+|merged chains=\d+ absorbed=\d+|defined cut inputs bytes=\d+ items=\d+)$')
PARTS = re.compile(r'^stated in parts=(\d+)$')
DEFINED = re.compile(r'^defined cut inputs bytes=(\d+) items=(\d+)$')
BOUND = re.compile(r'^bound rows=(\d+) replay=(.*)$')
PART = re.compile(r'^ \| part (\d+) of (\d+)')
AY_KINDS = ('server_solve', 'server_timeout', 'live_solve')
THRESHOLD = 30.0


def read(d):
    attempts = collections.defaultdict(list)
    pending = {}
    events = []
    kinds = collections.Counter()
    other_body = collections.Counter()
    with open(f'{d}/stderr.log', errors='replace') as fh:
        for raw in fh:
            line = raw.rstrip('\n')
            if line.startswith('TCG_SOLVE_TRACE '):
                m = TIMED.match(line)
                if m and m.group(3).startswith(BODY):
                    kinds[m.group(1)] += 1
                    b = BYTES.search(m.group(4))
                    events.append((m.group(1), float(m.group(2)), m.group(3)[len(BODY):],
                                   int(b.group(1)) if b else None, None))
                    continue
                m = PROMO.match(line)
                if m and m.group(1).startswith(BODY):
                    kinds['promotion_result'] += 1
                    events.append(('promotion_result', 0.0, m.group(1)[len(BODY):], None,
                                   re.sub(r'\(.*', '(..)', m.group(2))[:60]))
                    continue
                m = OTHER.match(line)
                if m and m.group(2).startswith(BODY):
                    other_body[m.group(1)] += 1
                    b = BYTES.search(m.group(3))
                    events.append((m.group(1), 0.0, m.group(2)[len(BODY):],
                                   int(b.group(1)) if b else None, None))
                continue
            m = TRACE.match(line)
            if not m:
                continue
            fn, rest = m.group(1), m.group(2)
            att = pending.get(fn)
            if att is None:
                att = {'lines': [], 'events': events}
                events = []
                pending[fn] = att
            att['lines'].append(rest)
            if BOUND.match(rest) or not NONTERMINAL.match(rest):
                attempts[fn].append(att)
                del pending[fn]
    for fn, att in pending.items():
        attempts[fn].append(att)
    parts = {}
    anomalies = []
    for fn, atts in attempts.items():
        for k, att in enumerate(atts):
            stated = [int(PARTS.match(l).group(1)) for l in att['lines'] if PARTS.match(l)]
            bound = any(BOUND.match(l) for l in att['lines'])
            for kind, secs, label, nbytes, result in att['events']:
                pm = PART.match(label)
                key = f'part {pm.group(1)} of {pm.group(2)}' if pm else 'whole'
                if pm and stated != [int(pm.group(2))]:
                    anomalies.append(f'{fn} attempt {k}: a `{key}` line, stated {stated}')
                if not pm and stated:
                    anomalies.append(f'{fn} attempt {k}: a whole-theorem line in an attempt stated in parts')
                if not bound:
                    anomalies.append(f'{fn} attempt {k}: a body line before a refused attempt')
                p = parts.setdefault((fn, k, key), {'ay': 0.0, 'clean': 0.0, 'bytes': set(),
                                                     'results': [], 'kinds': collections.Counter()})
                p['kinds'][kind] += 1
                if kind in AY_KINDS:
                    p['ay'] += secs
                if kind == 'clean_check':
                    p['clean'] += secs
                if nbytes is not None:
                    p['bytes'].add(nbytes)
                if result is not None:
                    p['results'].append(result)
    trailing = len(events)
    defining = {}
    inparts = set()
    for fn, atts in attempts.items():
        for att in atts:
            for l in att['lines']:
                if DEFINED.match(l):
                    defining[fn] = DEFINED.match(l).groups()
                if PARTS.match(l):
                    inparts.add(fn)
    return {'parts': parts, 'anomalies': anomalies, 'kinds': kinds, 'other': other_body,
            'trailing': trailing, 'defining': defining, 'inparts': inparts}


def wall(d):
    try:
        text = open(f'{d}.out', errors='replace').read()
    except OSError:
        return None
    m = re.search(r'wall: (\d+)s', text)
    return int(m.group(1)) if m else None


N, B = read(new), read(base)
lines = []


def say(s=''):
    lines.append(s)


for label, side, d in (('OD-233', N, new), ('baseline re-run', B, base)):
    ps = side['parts']
    say(f'{label} ({d}): census wall {wall(d)} s')
    say(f'  body lines: {dict(side["kinds"])}; other body lines: {dict(side["other"])}; '
        f'after the last attempt: {side["trailing"]}')
    say(f'  attribution anomalies: {len(side["anomalies"])}')
    for a in side['anomalies'][:20]:
        say(f'    {a}')
    inp = {key: p for key, p in ps.items() if key[2] != 'whole'}
    say(f'  parts with a body line: {len(ps)} ({len(inp)} of in-parts statements); '
        f'solved by AY: {sum(1 for p in ps.values() if p["ay"] > 0)}; checked by Clean: '
        f'{sum(1 for p in ps.values() if p["clean"] > 0)}')
    say(f'  AY seconds: all {sum(p["ay"] for p in ps.values()):.1f}, in parts '
        f'{sum(p["ay"] for p in inp.values()):.1f}; Clean seconds: all '
        f'{sum(p["clean"] for p in ps.values()):.1f}, in parts {sum(p["clean"] for p in inp.values()):.1f}')
    top = sorted(ps.items(), key=lambda kv: -kv[1]['ay'])[:5]
    say('  slowest by AY: ' + '; '.join(f'{k[0][-60:]} a{k[1]} {k[2]} {p["ay"]:.1f}s' for k, p in top))
    topc = sorted(ps.items(), key=lambda kv: -kv[1]['clean'])[:3]
    say('  slowest by Clean: ' + '; '.join(f'{k[0][-60:]} a{k[1]} {k[2]} {p["clean"]:.1f}s' for k, p in topc))
    over = sorted((k, p) for k, p in ps.items() if p['ay'] > THRESHOLD or p['clean'] > THRESHOLD)
    say(f'  parts over {THRESHOLD:.0f} s (AY or Clean): {len(over)}')
    for k, p in over:
        say(f'    {k[0]} attempt {k[1]} {k[2]}: AY {p["ay"]:.1f}s Clean {p["clean"]:.1f}s '
            f'bytes {sorted(p["bytes"])} results {p["results"]} {dict(p["kinds"])}')

# Pairing.
keys = sorted(set(N['parts']) | set(B['parts']))
groups = {'defining': collections.defaultdict(float), 'other': collections.defaultdict(float)}
bytes_differ_nondefining = []
newly_over = []
rows = []
for key in keys:
    fn = key[0]
    g = 'defining' if fn in N['defining'] else 'other'
    pn, pb = N['parts'].get(key), B['parts'].get(key)
    an = pn['ay'] if pn else None
    ab = pb['ay'] if pb else None
    cn = pn['clean'] if pn else None
    cb = pb['clean'] if pb else None
    bn = sorted(pn['bytes']) if pn else []
    bb = sorted(pb['bytes']) if pb else []
    rows.append((fn, key[1], key[2], g, ab, an, cb, cn, bb, bn,
                 pb['results'] if pb else None, pn['results'] if pn else None))
    if pn and pb:
        groups[g]['paired'] += 1
        groups[g]['ay_base'] += ab
        groups[g]['ay_new'] += an
        groups[g]['clean_base'] += cb
        groups[g]['clean_new'] += cn
        if bn and bb:
            groups[g]['both solved'] += 1
            if bn != bb:
                groups[g]['bytes differ'] += 1
                if g == 'other':
                    bytes_differ_nondefining.append((key, bb, bn))
    else:
        groups[g]['only new' if pn else 'only baseline'] += 1
    if pn and (an > THRESHOLD or cn > THRESHOLD) and not (pb and (ab > THRESHOLD or cb > THRESHOLD)):
        newly_over.append((key, ab, an, cb, cn))
say('paired parts (function, attempt, part):')
for g in ('defining', 'other'):
    v = groups[g]
    say(f'  {g}: paired {int(v["paired"])}, only new {int(v["only new"])}, only baseline '
        f'{int(v["only baseline"])}, both solved by AY {int(v["both solved"])}, query bytes differ '
        f'{int(v["bytes differ"])}; AY {v["ay_base"]:.1f} s -> {v["ay_new"]:.1f} s, Clean '
        f'{v["clean_base"]:.1f} s -> {v["clean_new"]:.1f} s')
say(f'functions defining inputs (OD-233 side): {len(N["defining"])}, of them stated in parts: '
    f'{len(set(N["defining"]) & N["inparts"])}')
say(f'non-defining parts whose query bytes differ: {len(bytes_differ_nondefining)}')
for key, bb, bn in bytes_differ_nondefining[:40]:
    say(f'  BYTES DIFFER {key}: {bb} -> {bn}')
say(f'parts newly over {THRESHOLD:.0f} s (AY or Clean on the OD-233 side, not on the baseline re-run): '
    f'{len(newly_over)}')
for key, ab, an, cb, cn in newly_over:
    say(f'  NEWLY OVER {key}: AY {ab} -> {an:.1f} s, Clean {cb} -> {cn:.1f} s')
# The defining functions' parts, slowest first.
dparts = sorted((r for r in rows if r[3] == 'defining'), key=lambda r: -(r[5] or 0))
say('defining functions\' parts by OD-233 AY time (top 25): fn attempt part | AY base -> new | '
    'Clean base -> new | bytes base -> new')
for r in dparts[:25]:
    f = lambda x: '-' if x is None else f'{x:.2f}'
    say(f'  {r[0][-70:]} a{r[1]} {r[2]} | {f(r[4])} -> {f(r[5])} | {f(r[6])} -> {f(r[7])} | {r[8]} -> {r[9]}')
with open(f'{out}/parts.tsv', 'w') as tsv:
    tsv.write('fn\tattempt\tpart\tgroup\tay_base\tay_new\tclean_base\tclean_new\tbytes_base\tbytes_new'
              '\tresults_base\tresults_new\n')
    for r in rows:
        tsv.write('\t'.join('' if x is None else str(x) for x in r) + '\n')
json.dump({'groups': groups, 'newly_over': newly_over,
           'bytes_differ_nondefining': bytes_differ_nondefining,
           'anomalies': {'new': N['anomalies'], 'base': B['anomalies']}},
          open(f'{out}/times.json', 'w'), indent=1, default=list)
open(f'{out}/times.txt', 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
