from pathlib import Path
import dataclasses, json, os, subprocess, sys

r = Path('/home/ayates/trust-cg-soundness-20260914')
p = Path('/home/ayates/trust-cg-output-byte-binding-20260917')
out = r / ('cg-maintained-bridge-' + sys.argv[1])
out.mkdir()
installed = json.loads((r / 'installed-floor-repair-first/identity.json').read_text())
sealed = Path('/home/ayates/toolchains/trust-a62ae50d')
assert Path('/home/ayates/.rustup/toolchains/trust').resolve() == sealed
def git(*args):
    return subprocess.check_output(['git', *args], cwd=p, text=True).strip()
head = git('rev-parse', 'HEAD')
assert not git('status', '--porcelain')
env = {k:v for k,v in os.environ.items() if not k.startswith(('TCG_', 'TRUST_CG_', 'AY_')) and k not in ['RUSTFLAGS', 'RUSTC', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER', 'CARGO_ENCODED_RUSTFLAGS', 'CARGO_BUILD_TARGET', 'CARGO_BUILD_RUSTC', 'CARGO_BUILD_RUSTC_WRAPPER', 'CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER']}
env.update(PATH=str(Path(installed['directory']) / 'bin') + ':' + str(sealed / 'bin') + ':/home/ayates/.cargo/bin:/home/ayates/.local/bin:/usr/bin:/bin', RUSTUP_TOOLCHAIN='trust', RUST_TEST_THREADS='1', CARGO_BUILD_JOBS='2', RUST_MIN_STACK='16777216', XDG_CACHE_HOME=str(out / 'cache'))
sys.path.insert(0, '/home/ayates/ay-pblendvb-repair-20260914/scripts')
import _oom_guard as guard
plan = guard.plan_solver_resources(jobs=1, mem_floor_mb=16384, label='Maintained complete Linux private bridge gate')
cmd = ['python3', 'scripts/check_linux_aarch64_bridge.py', '--out', str(out / 'gate'), '--target-dir', str(r / 'sealed-aarch64-bridge-target'), '--jobs', '2', '--timeout-seconds', '7200']
record = dict(source=head, command=cmd, resources=plan._asdict(), rss_limit_mb=16384, grace_mb=0, scope='Unmodified maintained complete native C aggregate/HFA/ScalarCell runner; fresh genuine Trust backend; explicit unverified frontend lane; all original floors and refusal controls preserved.')
(out / 'request.json').write_text(json.dumps(record, indent=2) + '\n')
result = guard.run_captured(['python3', str(r / 'run-command-to-log.py'), str(out / 'runner.log'), *cmd], 16384, 18000, label='Maintained complete Linux private bridge gate', env=env, cwd=p)
record['execution'] = dataclasses.asdict(result)
record['source_unchanged'] = git('rev-parse', 'HEAD') == head and not git('status', '--porcelain')
report = json.loads((out / 'gate/report.json').read_text())
record['status'] = report['status']
record['passed'] = result.returncode == 0 and record['source_unchanged'] and report['status'] == 'pass' and not any([result.timed_out, result.memout, result.cancelled, result.stdout_truncated, result.stderr_truncated])
(out / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(dict(passed=record['passed'], errors=report['errors'])), flush=True)
raise SystemExit(0 if record['passed'] else 1)
