#!/usr/bin/env python3
"""Run ONLY the functions the slice-6 body theorem credits at each opt level, built
with proofs REQUIRED (so the emitted code is exactly the credited code), natively
against the LLVM oracle (4 cells). usage: s6_credited_native.py <dylib> [levels...]"""
import os, re, subprocess, sys, tempfile, importlib.util
# s6_xback_orig.py is ../s6_xback.py without its final `main()` call (a module).
spec = importlib.util.spec_from_file_location('h', os.path.join(
    os.path.dirname(os.path.abspath(__file__)), 's6_xback_orig.py'))
h = importlib.util.module_from_spec(spec); spec.loader.exec_module(h)
TRUSTC, TARGET = h.TRUSTC, h.TARGET
dylib = sys.argv[1]; levels = sys.argv[2:] or ['1', '2', '3']
env = dict(os.environ, RUSTC_BOOTSTRAP='1', MACOSX_DEPLOYMENT_TARGET='13.0')
base = [TRUSTC, '--edition=2021', '-Ztrust-verify=off', '--target', TARGET, '-Cpanic=abort', '-Coverflow-checks=off', '-Ccodegen-units=1']
items = re.split(r'(?=^#\[inline\(never\)\] pub fn )', h.CALLEE.split('#![no_std]\n', 1)[1], flags=re.M)
items = {re.match(r'#\[inline\(never\)\] pub fn (\w+)', it).group(1): it for it in items if it.strip()}
def callee_src(fns):
    return '#![no_std]\n' + ''.join(items[f] for f in h.FUNCTIONS if f in fns)
def caller_src(fns):
    out = []
    lines = h.CALLER.splitlines(keepends=True); i = 0
    while i < len(lines):
        l = lines[i]
        if 'let mut slot' in l:
            block = lines[i:i+3]; i += 3
            if 'store_min' in fns: out += block
            continue
        m = re.search(r'callee::(\w+)\(', l)
        if m and m.group(1) not in fns: i += 1; continue
        out.append(l); i += 1
    return ''.join(out)
failures = 0
for opt in levels:
    with tempfile.TemporaryDirectory() as tmp:
        open(os.path.join(tmp, 'callee.rs'), 'w').write(h.CALLEE)
        o = os.path.join(tmp, 'probe'); os.makedirs(o)
        r = subprocess.run([TRUSTC, f'-Zcodegen-backend={dylib}', '-Ztrust-ir-cg-args=x86-body-trace'] + base[1:] +
                           ['--crate-type', 'rlib', '--crate-name', 'callee', f'-Copt-level={opt}', '--out-dir', o,
                            os.path.join(tmp, 'callee.rs')], env=env, capture_output=True, text=True)
        valid = set()
        for fn in h.FUNCTIONS:
            for line in r.stderr.splitlines():
                if 'X86-BODY-TRACE' in line and f'{len(fn)}{fn}' in line and 'replay=Valid' in line:
                    valid.add(fn)
        # a credited caller of an uncredited callee cannot be emitted alone: drop it
        if 'call_arm' in valid and 'twice' not in valid: valid.discard('call_arm')
        # abs_i64 calls core's wrapping_neg out of line at O1; that callee is not credited.
        if os.environ.get('DROP_ABS') and 'abs_i64' in valid: valid.discard('abs_i64')
        print(f'O{opt} credited: {sorted(valid)}')
        if not valid: continue
        open(os.path.join(tmp, 'callee.rs'), 'w').write(callee_src(valid))
        open(os.path.join(tmp, 'caller.rs'), 'w').write(caller_src(valid))
        rl = {}
        for be in ('llvm', 'tcg'):
            out = os.path.join(tmp, f'c_{be}'); os.makedirs(out)
            cmd = base + ['--crate-type', 'rlib', '--crate-name', 'callee', f'-Copt-level={opt}', '--out-dir', out,
                          os.path.join(tmp, 'callee.rs')]
            if be == 'tcg': cmd[1:1] = [f'-Zcodegen-backend={dylib}']   # proofs REQUIRED
            r = subprocess.run(cmd, env=env, capture_output=True, text=True)
            if r.returncode != 0:
                print(f'O{opt} {be} callee (proofs required) FAILED: ' + ' | '.join(r.stderr.splitlines()[-4:])[:600]); failures += 1; rl[be] = None
            else: rl[be] = os.path.join(out, 'libcallee.rlib')
        res = {}
        for rb, bb in (('llvm','llvm'),('llvm','tcg'),('tcg','llvm'),('tcg','tcg')):
            if not rl.get(rb): continue
            binp = os.path.join(tmp, f'b_{rb}_{bb}')
            cmd = base + ['--crate-type', 'bin', f'-Copt-level={opt}', '--extern', f'callee={rl[rb]}', '-L',
                          os.path.dirname(rl[rb]), '-o', binp, os.path.join(tmp, 'caller.rs')]
            if bb == 'tcg': cmd[1:1] = [f'-Zcodegen-backend={dylib}', '-Ztrust-ir-cg-args=no-proof-certs']
            r = subprocess.run(cmd, env=env, capture_output=True, text=True)
            if r.returncode != 0: print(f'O{opt} {rb}-rlib+{bb}-bin compile FAILED'); failures += 1; continue
            run = subprocess.run([binp], capture_output=True, text=True); res[(rb,bb)] = (run.returncode, run.stdout)
            print(f'O{opt} {rb}-rlib+{bb}-bin: exit {run.returncode}, {len(run.stdout.splitlines())} lines')
        oracle = res.get(('llvm','llvm'))
        for k, v in res.items():
            if v != oracle: print(f'O{opt} MISMATCH {k} vs llvm-llvm'); failures += 1
print(f'failures: {failures}')
