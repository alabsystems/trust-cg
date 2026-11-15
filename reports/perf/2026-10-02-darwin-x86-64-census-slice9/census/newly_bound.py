#!/usr/bin/env python3
"""The bodies the new census binds that the baseline did not, with their
bound rows and replay verdict; with --copy <dump dir> <out dir>, copy the
dumped query (`x86-body-dump`) of each uncertified one into <out dir> for
an offline replay (`replay_dir.py`).

usage: newly_bound.py <baseline census dir> <new census dir> [--copy <dump> <out>]
"""
import os
import re
import shutil
import sys

PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) bound rows=(\d+) replay=(\S+)')


def bound(d):
    out = {}
    for line in open(f'{d}/stderr.log', errors='replace'):
        m = PAT.match(line)
        if m:
            out[m.group(1)] = (int(m.group(2)), m.group(3))
    return out


base, new = bound(sys.argv[1]), bound(sys.argv[2])
fresh = {name: v for name, v in new.items() if name not in base}
copy = sys.argv[4:6] if len(sys.argv) > 5 and sys.argv[3] == '--copy' else None
if copy:
    os.makedirs(copy[1], exist_ok=True)
missing = 0
for name, (rows, replay) in sorted(fresh.items(), key=lambda kv: kv[1][0]):
    print(f'{rows}\t{replay}\t{name}')
    if copy and replay != 'Valid':
        # The dump names a query by the function's name with every
        # character outside [A-Za-z0-9_] replaced by `-`.
        stem = re.sub(r'[^A-Za-z0-9_]', '-', name)
        source = os.path.join(copy[0], f'{stem}.smt2')
        if os.path.exists(source):
            shutil.copy(source, os.path.join(copy[1], f'{stem}.smt2'))
        else:
            missing += 1
print(f'newly bound {len(fresh)}, Valid {sum(1 for v in fresh.values() if v[1] == "Valid")}'
      + (f', dumped queries missing {missing}' if copy else ''), file=sys.stderr)
