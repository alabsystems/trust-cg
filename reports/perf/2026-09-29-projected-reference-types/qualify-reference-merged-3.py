from pathlib import Path
import json, subprocess, time

p = Path('$HOME/trust-cg/target/std-completion-investigation')
cases = [
    ('aggregate-reference', 'residual_conversion::no_proof_projected_aggregate_reference_types_match_llvm'),
    ('reference', 'residual_conversion::no_proof_projected_reference_types_match_llvm'),

]
rows = []
for name, test_filter in cases:
    command = ['python3', str(p / 'runtime-reference-merged-3.py'), test_filter]
    start = time.monotonic()
    log_path = p / f'runtime-reference-merged-3-{name}.log'
    with log_path.open('wb') as log:
        result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=600)
    rows.append(dict(name=name, command=command, returncode=result.returncode,
                     wall_seconds=time.monotonic() - start, log=str(log_path)))
    (p / 'qualify-reference-merged-3-results.json').write_text(json.dumps(rows, indent=2) + '\n')
    print(name, result.returncode, flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
