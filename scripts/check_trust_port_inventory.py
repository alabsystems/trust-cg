#!/usr/bin/env python3
"""Require complete source accounting; never grant port completion from a census."""
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'proofs/trust-port-inventory.json').read_text())
raw = subprocess.check_output(['git', 'ls-files', '--cached', '--others',
    '--exclude-standard', '-z', '--', '*.lean'], cwd=root)
actual = {x.decode() for x in raw.split(b'\0') if x}
rows = manifest['files']
paths = [row['path'] for row in rows]
if len(paths) != len(set(paths)) or set(paths) != actual:
    raise SystemExit(f'inventory mismatch: missing={sorted(actual-set(paths))}, obsolete={sorted(set(paths)-actual)}')
if manifest['complete'] is not False:
    raise SystemExit('completion needs independent implementation/proof evidence; census cannot grant it')
for row in rows:
    if row['state'] == 'shared-computation-compiled-by-trust':
        if not row['trust_unit'] or row['production_connection'] == 'unproved':
            raise SystemExit('compiled computation missing consumer')
    elif row['state'] not in ['port-required', 'tooling-port-required',
                             'required-proof-unit; computation-port-required']:
        raise SystemExit('unreviewed port state: '+row['state'])
print(f'TRUST-PORT-INVENTORY files={len(rows)} accounted; full port INCOMPLETE')
