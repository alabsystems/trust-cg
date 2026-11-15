from pathlib import Path
import json, re

p = Path('$HOME/trust-cg/target/std-completion-investigation')
labels = ['std-O0-reference-merged-1', 'std-O0-reference-second']
results = [json.loads((p / (label + '-results.json')).read_text()) for label in labels]
assert all(r['returncode'] == 1 and not r['timed_out'] for r in results)

def key(root):
    match = re.search(r'\(monomorphized as `([^`]+)`', root)
    if match:
        return match.group(1)
    match = re.search(r'\(symbol `([^`]+)`', root)
    if match:
        return match.group(1)
    return root.split(': ', 1)[0].split(' (reachable Rust-internal', 1)[0]

maps = [{key(root): root for root in r['failed_roots']} for r in results]
assert all(len(m) == len(r['failed_roots']) for m, r in zip(maps, results))
before, after = maps
delta = dict(
    labels=labels,
    counts=[len(m) for m in maps],
    wall_seconds=[r['wall_seconds'] for r in results],
    removed=[before[s] for s in sorted(before.keys() - after.keys())],
    added=[after[s] for s in sorted(after.keys() - before.keys())],
    changed=[dict(symbol=s, before=before[s], after=after[s])
             for s in sorted(before.keys() & after.keys()) if before[s] != after[s]],
)
(p / 'reference-std-delta.json').write_text(json.dumps(delta, indent=2) + '\n')
print(delta['counts'], 'removed', len(delta['removed']), 'added', len(delta['added']),
      'changed diagnostic text', len(delta['changed']))
