from pathlib import Path
import dataclasses, hashlib, json, os, subprocess, sys

r = Path('/home/ayates/trust-cg-soundness-20260914')
p = Path('/home/ayates/trust-cg-output-byte-binding-20260917')
out = r / ('cg-maintained-aot-' + sys.argv[1])
out.mkdir()
installed = json.loads((r / 'installed-floor-repair-first/identity.json').read_text())
release = json.loads((r / 'cg-floor-repair-release-first/result.json').read_text())
assert release['passed']
def git(*args):
    return subprocess.check_output(['git', *args], cwd=p, text=True).strip()
head = git('rev-parse', 'HEAD')
assert not git('status', '--porcelain')
assert not git('diff', '--name-only', release['source'], head, '--', 'Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml', '.cargo', 'crates')
for row in installed['tools']:
    assert hashlib.sha256(Path(row['executable']).read_bytes()).hexdigest() == row['sha256']
env = {k:v for k,v in os.environ.items() if not k.startswith(('TCG_', 'TRUST_CG_', 'AY_'))}
pack = Path(installed['directory'])
env.update(PATH=str(pack / 'bin') + ':/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin:/home/ayates/.cargo/bin:/usr/bin:/bin', AY_SOLVER_PATH=str(pack / 'ay'), TCG_EXTERNAL_CLEAN_CHECKER=str(pack / 'clean'), RUSTUP_TOOLCHAIN='1.97.1')
sys.path.insert(0, '/home/ayates/ay-pblendvb-repair-20260914/scripts')
import _oom_guard as guard
plan = guard.plan_solver_resources(jobs=1, mem_floor_mb=16384, label='Maintained complete arithmetic AOT acceptance')
cmd = ['python3', 'scripts/check_aarch64_aot_arithmetic.py', '--trust-cg', str(pack / 'trust-cg'), '--require-clean', '--max-rss-gib', '16', '--out', str(out / 'gate')]
record = dict(source=head, cli_build_source=release['source'], source_code_unchanged_since_cli_build=True, installed_tools=installed['tools'], command=cmd, resources=plan._asdict(), rss_limit_mb=16384, grace_mb=0, scope='Unmodified maintained 48-case arithmetic AOT runner with exact installed CLI and independently replayed AY/Clean certificates; no complete source-to-native or platform closure claim.')
(out / 'request.json').write_text(json.dumps(record, indent=2) + '\n')
result = guard.run_captured(['python3', str(r / 'run-command-to-log.py'), str(out / 'runner.log'), *cmd], 16384, 10800, label='Maintained arithmetic AOT runner', env=env, cwd=p)
record['execution'] = dataclasses.asdict(result)
record['source_unchanged'] = git('rev-parse', 'HEAD') == head and not git('status', '--porcelain')
report = json.loads((out / 'gate/report.json').read_text())
record['summary'] = report['summary']
record['passed'] = result.returncode == 0 and record['source_unchanged'] and report['status'] == 'pass' and not any([result.timed_out, result.memout, result.cancelled, result.stdout_truncated, result.stderr_truncated])
(out / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(dict(passed=record['passed'], summary=record['summary'])), flush=True)
raise SystemExit(0 if record['passed'] else 1)
