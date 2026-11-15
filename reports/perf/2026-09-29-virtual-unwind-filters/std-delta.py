from pathlib import Path
import json
p = Path('$HOME/trust-cg/target/virtual-unwind-investigation')
before = p.parent / 'zst-tuple-investigation/std-O2-first-results.json'
after = p / 'std-O2-third-results.json'
def read(f):
    d = json.loads(f.read_text())
    assert d['returncode'] == 1 and not d['timed_out']
    roots = d['failed_roots']
    keyed = {s.split(': ', 1)[0]: s for s in roots}
    assert len(keyed) == len(roots)
    return keyed
a, b = read(before), read(after)
result = dict(counts=[len(a), len(b)],
              removed=[a[k] for k in sorted(a.keys() - b.keys())],
              added=[b[k] for k in sorted(b.keys() - a.keys())],
              changed=[dict(before=a[k], after=b[k]) for k in sorted(a.keys() & b.keys()) if a[k] != b[k]],
              before_file=str(before), after_file=str(after))
(p / 'std-delta-third.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
