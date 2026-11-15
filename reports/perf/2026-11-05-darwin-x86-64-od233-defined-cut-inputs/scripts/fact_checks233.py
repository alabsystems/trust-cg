#!/usr/bin/env python3
"""The census record's fact checks (2026-11-07): what the record states
about the O0 stop, the replay routes, the claim splits, AY and Clean time,
the Clean checks, wtf8's certificates and the host load, read from the
censuses' own outputs. It runs no compiler and no solver.

Attempts and attribution are census233.py's and part_times.py's: an attempt
is a function's run of [TCG-X86-BODY-TRACE] lines ending at a refusal or a
`bound rows=` line (`merged chains=`, `defined cut inputs` and `stated in
parts=` are not terminal), and every unkeyed trace line and every
TCG_SOLVE_TRACE line before an attempt's first line belongs to that attempt.

Sections:

A. Attributed timeouts per function (census233.py's counts: unkeyed
   `replay outcome=Timeout` lines and negative-memo timeout hits) for three
   pairs of O0 censuses, every function whose counts differ in either
   direction, and the sums of the increases and the decreases.
B. The body-theorem solve-trace events of named functions per attempt and
   part, on the OD-233 census and the baseline re-run (claim and
   generalized results counted, not listed).
C. How each of the O0 stop's six functions reaches `replay=Valid`: per
   attempt, its non-Verified results and its Verified `| claim i of m` and
   `| generalized` results.
D. Every claim split (`| claim 1 of m`) per census: function, attempt, the
   obligation it splits (a part or the whole theorem), m.
E. AY and Clean seconds per census: body-theorem obligations and all others.
F. Clean checks per census by outcome, and each not accepted.
G. wtf8's certificates against dump-o2-s25's queries, and wtf8's solve-trace
   events on the O2 OD-233 census and its re-run.
I. The O0 promotion results paired by (function, attempt, part), as
   part_times.py pairs them: the keys whose results differ, and the parts of
   in-parts statements with a Timeout result on either side.
H. The host load lines of census.log.

Writes <out file> and prints it.

usage: fact_checks233.py <runs dir> <census.log> <wtf8 cert dir> <out file>
"""
import collections
import datetime
import hashlib
import os
import re
import sys

runs, census_log, cert_dir, out = sys.argv[1:5]

BODY = ('Source-bound x86-64 whole-body theorem (System V, pre-RA ISel): the replayed body '
        'theorem credits every covered value row')
NAME = r'obligation="((?:[^"\\]|\\.)*)"'
TIMED = re.compile(r'^TCG_SOLVE_TRACE (server_solve|server_timeout|live_solve|clean_check) '
                   r'([0-9.]+)s ' + NAME + r'(.*)$')
PROMO = re.compile(r'^TCG_SOLVE_TRACE promotion_result ' + NAME + r' result=(.*)$')
OTHER = re.compile(r'^TCG_SOLVE_TRACE (\w+) .*?' + NAME + r'(.*)$')
BYTES = re.compile(r'\bsmt2_bytes=(\d+)')
OUTCOME = re.compile(r'\boutcome=(\w+)')
TRACE = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
UNKEYED = '[TCG-X86-BODY-TRACE] '
NONTERMINAL = re.compile(
    r'^(stated in parts=\d+|merged chains=\d+ absorbed=\d+|defined cut inputs bytes=\d+ items=\d+)$')
DEFINED = re.compile(r'^defined cut inputs bytes=(\d+) items=(\d+)$')
BOUND = re.compile(r'^bound rows=(\d+) replay=(.*)$')
CLAIM = re.compile(r' \| claim (\d+) of (\d+)$')
SIX = {
    '1243': 'cgu.0.1243._RNvMs0_NtNtCs7e1ihmkzmZ8_4core3fmt3numo10__fmt_inner',
    '1958': 'cgu.0.1958._RNvMsf_',
    '1975': 'cgu.0.1975._RNvMsk_',
    '2044': 'cgu.0.2044._RNvNtNtCs7e1ihmkzmZ8_4core10intrinsics8fallback13wide_mul_u128B5_',
    '2117': 'cgu.0.2117._RNvNtNtNtCs7e1ihmkzmZ8_4core3fmt3num3imp7exp_u64',
    '2271': 'cgu.0.2271._RNvNvNtNtCs7e1ihmkzmZ8_4core10intrinsics8fallback13wide_mul_u12810scalar_mul',
}
WTF8 = '_RNvNtCs7e1ihmkzmZ8_4core4wtf816slice_error_fail'

lines = []


def say(s=''):
    lines.append(s)


def short(fn):
    m = re.search(r'cgu\.0\.(\d+)\.', fn)
    return (f'cgu.0.{m.group(1)} ' if m else '') + fn[-70:]


def read(d):
    """Attempts of one census: fn -> [{'lines', 'unkeyed', 'events'}]."""
    attempts = collections.defaultdict(list)
    pending = {}
    unkeyed, events = [], []
    with open(f'{d}/stderr.log', errors='replace') as fh:
        for raw in fh:
            line = raw.rstrip('\n')
            if line.startswith('TCG_SOLVE_TRACE '):
                m = TIMED.match(line)
                if m and m.group(3).startswith(BODY):
                    b = BYTES.search(m.group(4))
                    o = OUTCOME.search(m.group(4))
                    events.append((m.group(1), float(m.group(2)), m.group(3)[len(BODY):],
                                   int(b.group(1)) if b else None, o.group(1) if o else None))
                    continue
                m = PROMO.match(line)
                if m and m.group(1).startswith(BODY):
                    events.append(('promotion_result', 0.0, m.group(1)[len(BODY):], None,
                                   re.sub(r'\(.*', '(..)', m.group(2))))
                    continue
                m = OTHER.match(line)
                if m and m.group(2).startswith(BODY):
                    events.append((m.group(1), 0.0, m.group(2)[len(BODY):], None, None))
                continue
            m = TRACE.match(line)
            if not m:
                if line.startswith(UNKEYED):
                    unkeyed.append(line[len(UNKEYED):])
                continue
            fn, rest = m.group(1), m.group(2)
            att = pending.get(fn)
            if att is None:
                att = {'lines': [], 'unkeyed': unkeyed, 'events': events}
                unkeyed, events = [], []
                pending[fn] = att
            att['lines'].append(rest)
            if BOUND.match(rest) or not NONTERMINAL.match(rest):
                attempts[fn].append(att)
                del pending[fn]
    for fn, att in pending.items():
        attempts[fn].append(att)
    return attempts


def timeouts(atts):
    t = collections.Counter()
    for att in atts:
        for u in att['unkeyed']:
            if u.startswith('replay outcome=Timeout'):
                t['outcome=Timeout'] += 1
            if u.startswith('replay negative-memo hit') and 'kind=timeout' in u:
                t['memo timeout'] += 1
    return t


def find(attempts, key):
    hits = [fn for fn in attempts if key in fn]
    return hits[0] if len(hits) == 1 else None


C = {name: read(f'{runs}/{name}') for name in (
    'census-o0-s25', 'census-o0-s24c', 'census-o0-s25-st', 'census-o0-od233',
    'census-o2-s25-st', 'census-o2-od233')}

# A. Attributed timeouts per function.
say('== A. attributed timeouts per function (outcome=Timeout, memo timeout), every function that differs')
for base, new in (('census-o0-s25', 'census-o0-od233'), ('census-o0-s25', 'census-o0-s25-st'),
                  ('census-o0-s25-st', 'census-o0-od233')):
    b, n = C[base], C[new]
    up, down = collections.Counter(), collections.Counter()
    tot_b = sum((timeouts(v) for v in b.values()), collections.Counter())
    tot_n = sum((timeouts(v) for v in n.values()), collections.Counter())
    say(f'{base} -> {new}: totals {dict(tot_b)} -> {dict(tot_n)}')
    for fn in sorted(set(b) | set(n)):
        tb, tn = timeouts(b.get(fn, [])), timeouts(n.get(fn, []))
        if tb == tn:
            continue
        ts = timeouts(C['census-o0-s24c'].get(fn, []))
        for k in ('outcome=Timeout', 'memo timeout'):
            d = tn[k] - tb[k]
            (up if d > 0 else down)[k] += abs(d)
        say(f'  {short(fn)}: ({tb["outcome=Timeout"]}, {tb["memo timeout"]}) -> '
            f'({tn["outcome=Timeout"]}, {tn["memo timeout"]}); census-o0-s24c '
            f'({ts["outcome=Timeout"]}, {ts["memo timeout"]})')
    say(f'  increases {dict(up)}; decreases {dict(down)}')


# B. Solve-trace events of named functions.
def events_of(att):
    per = collections.OrderedDict()
    for kind, secs, label, nbytes, result in att['events']:
        cm = CLAIM.search(label)
        if label.endswith(' | generalized'):
            part, tag = label[:-len(' | generalized')] or ' (whole)', 'generalized'
        elif cm:
            part, tag = label[:cm.start()] or ' (whole)', f'claim of {cm.group(2)}'
        else:
            part, tag = label or ' (whole)', None
        e = per.setdefault(part.strip(' |'), {'list': [], 'claims': collections.Counter()})
        if tag and kind == 'promotion_result':
            e['claims'][f'{tag} {result}'] += 1
        elif tag:
            e['claims'][f'{tag} {kind}'] += 1
        else:
            e['list'].append(f'{kind}' + (f' {secs:.3f}s' if secs else '') +
                             (f' {nbytes} B' if nbytes else '') + (f' {result}' if result else ''))
    return per


say()
say('== B. body-theorem events of named functions (claim and generalized lines counted)')
for key in ('cgu.0.1987.', 'format_shortest_opt'):
    for name in ('census-o0-od233', 'census-o0-s25-st'):
        a = C[name]
        fns = sorted(fn for fn in a if key in fn and (key != 'format_shortest_opt' or
                                                       fn.endswith('format_shortest_opt')))
        for fn in fns:
            for k, att in enumerate(a[fn]):
                say(f'{name} {short(fn)} attempt {k}: {att["lines"][-1][:60]}')
                for u in att['unkeyed']:
                    say(f'    unkeyed: {re.sub(r"age_s=[0-9]+ ", "", u)[:150]}')
                for part, e in events_of(att).items():
                    if e['list'] or e['claims']:
                        say(f'    {part or "(whole)"}: {"; ".join(e["list"])}'
                            + (f' | {dict(e["claims"])}' if e['claims'] else ''))

# C. The six functions' routes to Valid.
say()
say('== C. the O0 stop\'s six functions: results per attempt and part')
for name in ('census-o0-od233', 'census-o0-s25-st'):
    a = C[name]
    for tag, key in SIX.items():
        fn = find(a, key)
        if fn is None:
            say(f'{name} {tag}: not found uniquely')
            continue
        for k, att in enumerate(a[fn]):
            route = []
            for part, e in events_of(att).items():
                bad = [x for x in e['list'] if x.startswith('promotion_result') and 'Verified' not in x]
                if bad or e['claims']:
                    route.append(f'{part or "(whole)"}: {", ".join(bad) or "Verified"}'
                                 + (f' then {dict(e["claims"])}' if e['claims'] else ''))
            say(f'{name} {tag} attempt {k}: {att["lines"][-1]} | ' + ('; '.join(route) or 'every result Verified'))

# D. Claim splits.
say()
say('== D. claim splits (`| claim 1 of m`): census, function, attempt, obligation, m, defines inputs')
for name in ('census-o0-od233', 'census-o0-s25-st', 'census-o2-od233', 'census-o2-s25-st'):
    a = C[name]
    side = C[name.replace('s25-st', 'od233')]
    defining = {fn for fn, atts in side.items() for att in atts for l in att['lines'] if DEFINED.match(l)}
    ms = []
    for fn, atts in sorted(a.items()):
        for k, att in enumerate(atts):
            for kind, _, label, _, _ in att['events']:
                cm = CLAIM.search(label)
                if kind == 'promotion_result' and cm and cm.group(1) == '1':
                    obl = label[:cm.start()].strip(' |') or 'whole theorem'
                    ms.append(int(cm.group(2)))
                    say(f'{name} {short(fn)} attempt {k} {obl}: m={cm.group(2)}'
                        f'{" (defines inputs)" if fn in defining else ""}')
    say(f'{name}: {len(ms)} claim splits, largest m {max(ms) if ms else None}')

# E. AY and Clean seconds.
say()
say('== E. AY seconds (server_solve, server_timeout, live_solve) and Clean seconds (clean_check)')
for name in ('census-o2-od233', 'census-o2-s25-st', 'census-o0-od233', 'census-o0-s25-st'):
    tot, cnt, other = collections.Counter(), collections.Counter(), collections.Counter()
    with open(f'{runs}/{name}/stderr.log', errors='replace') as fh:
        for raw in fh:
            m = TIMED.match(raw.rstrip('\n'))
            if not m:
                continue
            where = 'body' if m.group(3).startswith(BODY) else 'other'
            tool = 'Clean' if m.group(1) == 'clean_check' else 'AY'
            tot[(where, tool)] += float(m.group(2))
            cnt[(where, tool)] += 1
            if where == 'other':
                other[re.sub(r'\d+', 'N', m.group(3))[:60]] += 1
    say(f'{name}: ' + ', '.join(f'{w} {t} {tot[(w, t)]:.1f} s in {cnt[(w, t)]} lines'
                                for w, t in sorted(tot)))
    say(f'    other obligations: {other.most_common(4)}')

# F. Clean checks.
say()
say('== F. Clean checks: outcomes, and each not accepted')
for name in ('census-o2-od233', 'census-o2-s25-st', 'census-o0-od233', 'census-o0-s25-st'):
    outcomes = collections.Counter()
    for fn, atts in C[name].items():
        for k, att in enumerate(atts):
            for kind, secs, label, _, outcome in att['events']:
                if kind != 'clean_check':
                    continue
                outcomes[outcome] += 1
                if outcome != 'accepted':
                    say(f'{name} {short(fn)} attempt {k} {label.strip(" |") or "whole theorem"}: '
                        f'outcome={outcome} {secs:.3f}s')
    say(f'{name}: {dict(outcomes)}')


# G. wtf8.
def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


say()
say('== G. wtf8: certificates (od233-run/census/wtf8) against dump-o2-s25')
dumps = {}
for n in sorted(os.listdir(f'{runs}/dump-o2-s25')):
    if n.startswith(WTF8):
        p = f'{runs}/dump-o2-s25/{n}'
        dumps[sha(p)] = n
        say(f'dump-o2-s25 {n}: {os.path.getsize(p)} B sha256 {sha(p)}')
for n in sorted(os.listdir(cert_dir)):
    p = f'{cert_dir}/{n}'
    head = open(p, 'rb').read(4096).decode('utf-8', 'replace')
    obl = re.search(r'obligation:([^\n]*)', head)
    h = re.search(r'smt2-sha256:([0-9a-f]{64})', head)
    mtime = datetime.datetime.fromtimestamp(os.path.getmtime(p)).strftime('%Y-%m-%d %H:%M:%S')
    say(f'{n[:16]}…: {obl.group(1)[len(BODY):] if obl else "?"}; smt2-sha256 {h.group(1) if h else "?"}; '
        f'mtime {mtime}; matches dump-o2-s25: {dumps.get(h.group(1), "none") if h else "?"}')
for name in ('census-o2-od233', 'census-o2-s25-st'):
    for k, att in enumerate(C[name].get(WTF8, [])):
        say(f'{name} wtf8 attempt {k}: {att["lines"][-1]}')
        for part, e in events_of(att).items():
            say(f'    {part or "(whole)"}: {"; ".join(e["list"])}')

# I. Paired promotion results (part_times.py's pairing).
PART = re.compile(r'^ \| part (\d+) of (\d+)')


def results(attempts):
    res = {}
    for fn, atts in attempts.items():
        for k, att in enumerate(atts):
            for kind, _, label, _, result in att['events']:
                if kind != 'promotion_result':
                    continue
                pm = PART.match(label)
                key = (fn, k, f'part {pm.group(1)} of {pm.group(2)}' if pm else 'whole')
                res.setdefault(key, []).append(result)
    return res


say()
say('== I. paired promotion results, census-o0-s25-st -> census-o0-od233 (key: function, attempt, part)')
rb, rn = results(C['census-o0-s25-st']), results(C['census-o0-od233'])
paired = sorted(set(rb) & set(rn))
differ = [k for k in paired if rb[k] != rn[k]]
newly = [k for k in paired if any(r == 'Timeout' for r in rn[k]) and not any(r == 'Timeout' for r in rb[k])]
inparts_t = [k for k in paired if k[2] != 'whole' and any(r == 'Timeout' for r in rb[k] + rn[k])]
say(f'paired {len(paired)}; results differ {len(differ)}; a Timeout result on the OD-233 side only {len(newly)}')
for k in differ:
    say(f'  DIFFER {short(k[0])} attempt {k[1]} {k[2]}: {rb[k]} -> {rn[k]}')
say(f'parts of in-parts statements with a Timeout result on either side: {len(inparts_t)}; '
    f'of them with the same results on both sides: {sum(1 for k in inparts_t if rb[k] == rn[k])}')

# H. Load.
say()
say('== H. census.log load lines')
for raw in open(census_log, errors='replace'):
    if 'load {' in raw:
        say(raw.rstrip('\n'))

os.makedirs(os.path.dirname(out), exist_ok=True)
open(out, 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
