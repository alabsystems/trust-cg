#!/usr/bin/env python3
"""Slice 16: classify the slice-16 probe's `--cf` run over the 101 size-refused
`core` functions (and the 103 bound-uncertified controls).

usage: measure_s16.py <cf.tsv> <size_roots.tsv> <out dir>

<cf.tsv> is the probe's `--cf` output (name, verdict, LIR blocks, loop, paths,
longest path, instructions, machine blocks, machine rows); a verdict is
`OWNER <bound> PARTS <n> defs/claims/bytes=<d/c/b>,...` for a theorem stated
in parts, `OWNER <bound> defs=<d>` for a single query, `... REFUTED...` when
the sampler refutes it, or the refusal text. <size_roots.tsv> is the design's
class list (name, class, roots, detail).

Writes <out>/s16_outcomes.tsv (one row per class function) and prints the
summary tables: outcome by class, the part counts, and the per-part sizes
(definitions, claims, query bytes).
"""
import collections, os, re, statistics, sys

cf_path, roots_path, out = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(out, exist_ok=True)
classes = {}
for line in open(roots_path):
    cols = line.rstrip('\n').split('\t')
    if len(cols) >= 2:
        classes[cols[0]] = cols[1]
rows = {}
for line in open(cf_path):
    cols = line.rstrip('\n').split('\t')
    if len(cols) >= 9:
        rows[cols[0]] = cols


def outcome(verdict):
    if verdict.startswith('OWNER') and 'REFUTED' in verdict:
        return 'refuted on samples'
    if verdict.startswith('OWNER') and ' PARTS ' in verdict:
        return 'stated in parts'
    if verdict.startswith('OWNER'):
        return 'one query'
    for key, label in [
        ('is an i128 value live across cut point', 'an i128 live across a cut'),
        ('divides a B1, i128', 'an i128 division'),
        ('is outside the body domain (MovRR', 'a machine row outside the domain'),
        ('joins paths that leave private stack slot', 'a join of different stored private addresses'),
        ('loads a bool from a private byte', 'a bool load from a byte no bool store wrote'),
        ('non-constant amount', 'non-constant private-slot offset'),
        ('MEMORY', 'MEMORY-class aggregate'),
        ('over 16 bytes', 'MEMORY-class aggregate'),
        ('edges outside its loop', 'multi-entry loop header'),
        ('no cut plan fits', 'no cut plan fits'),
        ('do not split cleanly', 'no clean split'),
        ('live across cut', 'a value live across a cut'),
        ('crossing a cut', 'a value crossing a cut'),
        ('is live at cut point', 'a value live across a cut'),
        ('holds no value on the edge', 'an item register without bits'),
        ('carries', 'a carried register read'),
        ('which its LIR source does not', 'a machine-only byte'),
        ('i128', 'an i128 crossing'),
    ]:
        if key in verdict:
            return label
    return 'refused: ' + verdict[:90]


table = collections.defaultdict(collections.Counter)
parts_by_class = collections.defaultdict(list)
part_sizes = []
with open(os.path.join(out, 's16_outcomes.tsv'), 'w') as o:
    o.write('class\tfunction\toutcome\tparts\tbound_rows\tmachine_rows\tverdict\n')
    for name, klass in sorted(classes.items()):
        cols = rows.get(name)
        if cols is None:
            table[klass]['not in the dump'] += 1
            o.write(f'{klass}\t{name}\tnot in the dump\t\t\t\t\n')
            continue
        verdict = cols[1]
        kind = outcome(verdict)
        table[klass][kind] += 1
        parts = ''
        bound = ''
        m = re.match(r'OWNER (\d+)', verdict)
        if m:
            bound = m.group(1)
        m = re.search(r'PARTS (\d+)', verdict)
        if m:
            parts = m.group(1)
            parts_by_class[klass].append(int(parts))
        m = re.search(r'defs/claims/bytes=(\S+)', verdict)
        if m:
            for shape in m.group(1).split(','):
                d, c, b = (int(x) for x in shape.split('/'))
                part_sizes.append((klass, name, d, c, b))
        o.write(f'{klass}\t{name}\t{kind}\t{parts}\t{bound}\t{cols[8]}\t{verdict[:300]}\n')

print('outcome by class:')
for klass, counts in sorted(table.items()):
    print(f'  {klass}: {sum(counts.values())}')
    for kind, n in counts.most_common():
        print(f'    {n:4d}  {kind}')


def stats(values):
    if not values:
        return '-'
    values = sorted(values)
    p90 = values[min(len(values) - 1, int(0.9 * len(values)))]
    return f'{statistics.median(values):g} / {p90} / {values[-1]} (n={len(values)})'


print('parts per function (median / p90 / max):')
for klass, values in sorted(parts_by_class.items()):
    print(f'  {klass}: {stats(values)}')
print('per part (median / p90 / max):')
print(f'  definitions: {stats([d for _, _, d, _, _ in part_sizes])}')
print(f'  claims: {stats([c for _, _, _, c, _ in part_sizes])}')
print(f'  query bytes: {stats([b for _, _, _, _, b in part_sizes])}')
