#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256)."""
import hashlib, os
H = os.path.expanduser('~/tcg-scratch')
FILES = [
    'runs/s7.dylib',
    'runs/census-s7/provenance.json',
    'runs/census-s7/failed_roots.jsonl',
    'runs/census-s7/gap_table.md',
    'runs/census-s7/refusals.jsonl',
    'runs/census-s7/stderr.log',
    'runs/census-s7.out',
    's7native/census_s7.log',
    's7native/census-compare/promoted.txt',
    's7native/census-compare/newly_failing.txt',
    's7native/census-compare/body_trace_classes.tsv',
    's7native/offline_probe.tsv',
    's7native/typehint_check.txt',
    's7native/uncertified_names.txt',
    's7native/replay_uncertified.tsv',
    's7native/replay_uncertified_serial.tsv',
    's7native/replay_words.tsv',
    's7native/qualification_fresh.txt',
    's7native/qualification_and_credit.txt',
    's7native/gate_row_slice7.txt',
    's7native/e2e_and_must_refuse.txt',
    's7native/mutants.txt',
    's7native/probe_trace_main336a.txt',
    's7native/probe_trace_s7.txt',
    's7native/credited_O0.txt',
    's7native/credited_O123.txt',
    's7native/m145_O0_O2.txt',
]
for f in FILES:
    p = os.path.join(H, f)
    if not os.path.exists(p):
        print(f'| `{f}` | MISSING | |')
        continue
    data = open(p, 'rb').read()
    print(f'| `{f}` | {len(data)} | `{hashlib.sha256(data).hexdigest()}` |')
