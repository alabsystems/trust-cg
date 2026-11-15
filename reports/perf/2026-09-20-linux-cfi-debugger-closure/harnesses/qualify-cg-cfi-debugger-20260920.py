from pathlib import Path
import dataclasses, hashlib, importlib.util, json, os, shutil, subprocess, sys
from datetime import datetime, timezone

r = Path('/home/ayates/trust-cg-soundness-20260914')
p = Path('/home/ayates/trust-cg-output-byte-binding-20260917')
out = r / ('cg-cfi-debugger-' + sys.argv[1])
out.mkdir()
for name in ['bin', 'calls', 'blobs']:
    (out / name).mkdir()
sys.path.insert(0, '/home/ayates/ay-pblendvb-repair-20260914/scripts')
import _oom_guard as guard
plan = guard.plan_solver_resources(jobs=1, mem_floor_mb=16384, label='Independent CFI and Linux debugger closure')
tools = {}
for name in ['cc', 'gdb', 'llvm-dwarfdump', 'llvm-readelf', 'llvm-objdump']:
    # Preserve argv[0]: llvm-readelf and llvm-readobj share a binary but select
    # different output modes from the invoked filename.
    real = Path(shutil.which(name)).absolute()
    tools[name] = dict(path=str(real), resolved=str(real.resolve()), sha256=hashlib.sha256(real.read_bytes()).hexdigest())
    wrapper = out / 'bin' / name
    shutil.copyfile(r / 'capture-cg-cfi-tools-20260920.py', wrapper)
    wrapper.chmod(0o755)
(out / 'tools.json').write_text(json.dumps(tools, indent=2) + '\n')
env = {k:v for k,v in os.environ.items() if not k.startswith(('TCG_', 'TRUST_CG_', 'AY_')) and k not in ['RUSTFLAGS', 'RUSTC', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER', 'CARGO_ENCODED_RUSTFLAGS', 'CARGO_BUILD_TARGET', 'CARGO_BUILD_RUSTC', 'CARGO_BUILD_RUSTC_WRAPPER', 'CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER']}
env.update(PATH=str(out / 'bin') + ':/home/ayates/.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin:/home/ayates/.cargo/bin:/home/ayates/.local/bin:/usr/bin:/bin', RUSTUP_TOOLCHAIN='1.97.1', CARGO_BUILD_JOBS='2', RUST_TEST_THREADS='1', RUST_MIN_STACK='16777216', CARGO_TARGET_DIR='$HOME/trust-cg/target', TRUST_CG_LLVM_BIN=str(out / 'bin'), CG_CFI_CAPTURE_ROOT=str(out))
os.environ.clear()
os.environ.update(env)
os.chdir(p)
spec = importlib.util.spec_from_file_location('linux_floor', p / 'scripts/check_linux_aarch64.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
provenance = gate.preflight()
assert not provenance['dirty']
record = dict(scope='Unchanged CFI differential and Linux debugger tests with exact-argument tool forwarding and retained tool transcripts/inputs. Synchronous CFI only, no epilogue or asynchronous unwind claim.', provenance=provenance, resources=plan._asdict(), rss_limit_mb=16384, grace_mb=0, started=datetime.now(timezone.utc).isoformat(), tools=tools, commands=[], complete=False)
def save():
    (out / 'results.json').write_text(json.dumps(record, indent=2) + '\n')
save()
for target in ['aarch64_elf_cfi_differential', 'e2e_aarch64_elf_debugger_linux']:
    cmd = ['cargo', 'test', '--locked', '--offline', '--color', 'never', '-j', '2', '-p', 'trust-cg-codegen', '--test', target, '--', '--nocapture', '--test-threads=1']
    log = out / (target + '.log')
    result = guard.run_captured(['python3', str(r / 'run-command-to-log.py'), str(log), *cmd], 16384, 1200, label=target, env=env, cwd=p)
    row = dict(target=target, command=cmd, execution=dataclasses.asdict(result), **gate.classify_result(result.returncode, log.read_text()))
    record['commands'].append(row)
    save()
    print(json.dumps(dict(target=target, status=row['status'], seconds=result.wall_sec)), flush=True)
    assert row['status'] == 'pass' and not any([result.timed_out, result.memout, result.cancelled, result.stdout_truncated, result.stderr_truncated])
calls = [json.loads(path.read_text()) for path in sorted((out / 'calls').glob('*/result.json'))]
assert len(calls) == len(list((out / 'calls').glob('*/request.json')))
assert all(row['exit_code'] == 0 for row in calls)
gdb = [row for row in calls if row['tool'] == 'gdb']
assert len(gdb) == 4
assert {Path(row['args'][-1]).name for row in gdb} == {'fixture_O' + str(i) for i in range(4)}
for name in ['llvm-dwarfdump', 'llvm-objdump', 'llvm-readelf']:
    assert any(row['tool'] == name and row['snapshots']['before'] for row in calls), name
record['final_source'] = gate.source_provenance(provenance['tools']['git'])
record['source_unchanged'] = record['final_source']['source_fingerprint'] == provenance['source_fingerprint']
assert record['source_unchanged']
record.update(captured_calls=len(calls), debugger_calls=len(gdb), complete=True, passed=True, finished=datetime.now(timezone.utc).isoformat())
save()
print(json.dumps(dict(passed=True, calls=len(calls), debugger_calls=len(gdb))), flush=True)
