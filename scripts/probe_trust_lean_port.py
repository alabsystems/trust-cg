#!/usr/bin/env python3
"""Inventory every Lean source and probe its actual Trust Clean-unit admission.

Diagnostic progress only. Accepted proof declarations do not imply emitted bodies
or production consumer bindings; those are separate port completion obligations.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def sources():
    raw = subprocess.check_output(['git', 'ls-files', '--cached', '--others',
        '--exclude-standard', '-z', '--', '*.lean'], cwd=ROOT)
    return sorted(set(x.decode() for x in raw.split(b'\0') if x))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path, required=True)
    parser.add_argument('--only', action='append', default=[])
    parser.add_argument('--timeout', type=int, default=30)
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    if any(args.out_dir.iterdir()):
        raise SystemExit('output directory must be empty')
    out = args.out_dir.resolve()
    names = sources()
    if set(args.only) - set(names):
        raise SystemExit("unknown selected source")
    rows = []
    for name in names:
        text = (ROOT / name).read_text()
        role = 'build-tool' if Path(name).name == 'lakefile.lean' else (
            'negative-control' if '/negative/' in name else 'proof-or-program')
        rows.append(dict(path=name, sha256=digest(ROOT / name), role=role,
            imports=re.findall(r'^import\s+([^\n]+)', text, re.M),
            status='unmeasured', consumer_binding='unproved'))
    (out / 'inventory.json').write_text(json.dumps(rows, indent=2) + '\n')
    version = subprocess.check_output(['trustc', '-Vv'], text=True)
    (out / 'compiler.txt').write_text(version)
    if 'trust:' not in version:
        raise SystemExit('compiler is not Trust')
    for index, row in enumerate(rows):
        name = row['path']
        if args.only and name not in args.only:
            continue
        if row['role'] == 'build-tool':
            row['status'] = 'tooling-port-required'
            continue
        stem = f'{index:03d}'
        (out / (stem + '.input.lean')).write_bytes((ROOT / name).read_bytes())
        wrapper = out / (stem + '.rs')
        wrapper.write_text('#[path = ' + json.dumps(str(ROOT / name)) + ']\n'
            'clean mod port_unit;\nfn main() {}\n')
        command = ['trustc', '-Ztrust-verify=off', '--edition=2024',
                   str(wrapper), '-o', str(out / stem)]
        with (out / (stem + '.log')).open('wb') as log:
            child = subprocess.Popen(command, cwd=ROOT, stdout=log,
                stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = child.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGTERM)
                try:
                    child.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
                code = 124
        text = (out / (stem + '.log')).read_text(errors='replace')
        census = re.findall(r'Clean island kernel-checked: (\d+) declaration', text)
        row.update(exit_code=code, command=command, log=stem+'.log',
            checked_declarations=sum(map(int, census)),
            status='timed-out' if code == 124 else 'refused' if code else (
                'accepted-declarations-only' if sum(map(int, census)) > 0 else 'uncredited-no-census'))
        if digest(ROOT / name) != row['sha256']:
            row['status'] = 'input-changed-no-credit'
        (out / 'inventory.json').write_text(json.dumps(rows, indent=2) + '\n')
        print(f"TRUST-PORT {index+1}/{len(rows)} {name}: {row['status']}", flush=True)
    counts = {}
    for row in rows:
        counts[row['status']] = counts.get(row['status'], 0) + 1
    (out / 'summary.json').write_text(json.dumps(dict(total=len(rows), statuses=counts,
        completion=False, qualification='diagnostic admission; NOT ATTESTED'), indent=2)+'\n')
    print(json.dumps(counts), flush=True)


if __name__ == '__main__':
    main()
