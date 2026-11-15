from pathlib import Path
import json, subprocess, time
from concurrent.futures import ThreadPoolExecutor

p = Path('$HOME/trust-cg/target/std-completion-investigation')
cases = [
    ('aggregate-reference', 'residual_conversion::no_proof_projected_aggregate_reference_types_match_llvm'),
    ('reference', 'residual_conversion::no_proof_projected_reference_types_match_llvm'),

]
def run_case(case):
    name, test_filter = case
    command = ['python3', str(p / 'runtime-reference-merged-4.py'), test_filter]
    start = time.monotonic()
    log_path = p / f'runtime-reference-merged-4-{name}.log'
    with log_path.open('wb') as log:
        result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=600)
    print(name, result.returncode, flush=True)
    return dict(name=name, command=command, returncode=result.returncode,
                wall_seconds=time.monotonic() - start, log=str(log_path))
with ThreadPoolExecutor(max_workers=2) as pool:
    rows = list(pool.map(run_case, cases))
(p / 'qualify-reference-merged-4-results.json').write_text(json.dumps(rows, indent=2) + '\n')
raise SystemExit(0 if all(row['returncode'] == 0 for row in rows) else 1)
