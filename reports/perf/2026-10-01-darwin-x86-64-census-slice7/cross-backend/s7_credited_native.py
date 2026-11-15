#!/usr/bin/env python3
"""Slice-7 cross-backend matrix (calls through memory), natively.

Three crates: `dep` holds the callees that return through a buffer or write an
out-parameter (`make3`, `triple`, `pair_opt`, `mixed`, `bump`, `peek`, `fill`),
always compiled by LLVM, so every callee is an LLVM-compiled one; `callee` holds
the functions under test (callers of `dep` that pass a private slot's address:
a return buffer or `&mut`/`&` local); `main` drives them. The `callee` rlib is
built by LLVM or by trust-cg WITH PROOFS REQUIRED (the bridge default: it
promotes only if every function's body theorem replays Valid), containing
EXACTLY the functions a first traced compile credits (`replay=Valid`); the bin
by LLVM or trust-cg (`no-proof-certs`, it only calls). All four rlib x bin
cells must print exactly the oracle's (LLVM rlib + LLVM bin) output.

usage: s7_credited_native.py <dylib> [opt levels...]   (default: 0)
"""
import os
import re
import subprocess
import sys
import tempfile

TRUSTC = os.path.expanduser('trust/build/x86_64-apple-darwin/stage1/bin/trustc')
TARGET = 'x86_64-apple-darwin'
DEP = r'''
#![no_std]
pub struct Three { pub a: u64, pub b: u64, pub c: u64 }
#[inline(never)] pub fn make3(x: u64) -> Three { Three { a: x, b: x.wrapping_add(1), c: x.wrapping_mul(3) } }
#[inline(never)] pub fn triple(x: u64) -> (u64, u64, u64) { (x, x ^ 5, x.wrapping_sub(2)) }
#[inline(never)] pub fn pair_opt(x: u64) -> Option<(u64, u64)> { if x & 1 == 1 { Some((x, x >> 1)) } else { None } }
#[inline(never)] pub fn mixed(x: u64) -> (u64, u32, bool) { (x, (x as u32) ^ 3, x & 4 != 0) }
#[inline(never)] pub fn bump(p: &mut u64) { *p = p.wrapping_add(1); }
#[inline(never)] pub fn peek(p: &u64) -> u64 { p.wrapping_mul(7) }
#[inline(never)] pub fn fill(o: &mut Option<u64>, x: u64) { if x > 3 { *o = Some(x) } }
#[inline(never)] pub fn twice(x: u64) -> u64 { x.wrapping_mul(2) }
'''
CALLEE = r'''
#![no_std]
use dep::*;
#[inline(never)] pub fn sum3(x: u64) -> u64 { let t = make3(x); t.a.wrapping_add(t.b).wrapping_add(t.c) }
#[inline(never)] pub fn field3(x: u64) -> u64 { make3(x).b }
#[inline(never)] pub fn mid(x: u64) -> u64 { triple(x).1 }
#[inline(never)] pub fn two_buffers(x: u64, y: u64) -> u64 { make3(x).a.wrapping_add(make3(y).c) }
#[inline(never)] pub fn fwd3(x: u64) -> Three { make3(x) }
#[inline(never)] pub fn branch_sret(c: bool, x: u64) -> u64 { if c { make3(x).c } else { x } }
#[inline(never)] pub fn opt_xor(x: u64) -> u64 { match pair_opt(x) { Some((a, b)) => a ^ b, None => 9 } }
#[inline(never)] pub fn mixed_sum(x: u64) -> u64 { let r = mixed(x); r.0 ^ (r.1 as u64) ^ (r.2 as u64) }
#[inline(never)] pub fn out_param(x: u64) -> u64 { let mut v = x; bump(&mut v); v }
#[inline(never)] pub fn out_twice(x: u64) -> u64 { let mut v = x; bump(&mut v); bump(&mut v); v }
#[inline(never)] pub fn read_ref(x: u64) -> u64 { let v = x; peek(&v) }
#[inline(never)] pub fn out_then_call(x: u64, y: u64) -> u64 { let mut v = x; bump(&mut v); twice(y).wrapping_add(v) }
#[inline(never)] pub fn out_then_store(p: &mut u64, x: u64) { let mut v = x; bump(&mut v); *p = v; }
#[inline(never)] pub fn opt_out(x: u64) -> u64 { let mut o = None; fill(&mut o, x); match o { Some(v) => v, None => 0 } }
'''
FUNCTIONS = ['sum3', 'field3', 'mid', 'two_buffers', 'fwd3', 'branch_sret', 'opt_xor',
             'mixed_sum', 'out_param', 'out_twice', 'read_ref', 'out_then_call',
             'out_then_store', 'opt_out']
CALLS = {
    'sum3': 'out(callee::sum3(bb(a)));',
    'field3': 'out(callee::field3(bb(a)));',
    'mid': 'out(callee::mid(bb(a)));',
    'two_buffers': 'out(callee::two_buffers(bb(a), bb(b)));',
    'fwd3': '{ let t = callee::fwd3(bb(a)); out(t.a ^ t.b ^ t.c); }',
    'branch_sret': 'out(callee::branch_sret(bb(a < b), bb(a)));',
    'opt_xor': 'out(callee::opt_xor(bb(a)));',
    'mixed_sum': 'out(callee::mixed_sum(bb(a)));',
    'out_param': 'out(callee::out_param(bb(a)));',
    'out_twice': 'out(callee::out_twice(bb(a)));',
    'read_ref': 'out(callee::read_ref(bb(a)));',
    'out_then_call': 'out(callee::out_then_call(bb(a), bb(b)));',
    'out_then_store': '{ let mut s = 99u64; callee::out_then_store(bb(&mut s), bb(a)); out(s); }',
    'opt_out': 'out(callee::opt_out(bb(a)));',
}


def caller_src(fns):
    body = '\n        '.join(CALLS[f] for f in FUNCTIONS if f in fns)
    return ('use std::hint::black_box as bb;\n'
            '#[inline(never)] fn out(v: u64) { println!("{}", v); }\n'
            'fn main() {\n'
            '    let v: [u64; 10] = [0, 1, 2, 5, 7, 0x7f, 0x80, 200, 1 << 63, u64::MAX];\n'
            '    for &a in &v { for &b in &v {\n'
            f'        {body}\n'
            '    } }\n'
            '}\n')


def callee_src(fns):
    items = re.split(r'(?=^#\[inline\(never\)\] pub fn )', CALLEE.split('use dep::*;\n', 1)[1],
                     flags=re.M)
    keep = [it for it in items if it.strip()
            and re.match(r'#\[inline\(never\)\] pub fn (\w+)', it).group(1) in fns]
    return '#![no_std]\nuse dep::*;\n' + ''.join(keep)


def main():
    dylib = sys.argv[1]
    levels = sys.argv[2:] or ['0']
    env = dict(os.environ, RUSTC_BOOTSTRAP='1', MACOSX_DEPLOYMENT_TARGET='13.0')
    base = [TRUSTC, '--edition=2021', '-Ztrust-verify=off', '--target', TARGET,
            '-Cpanic=abort', '-Coverflow-checks=off', '-Ccodegen-units=1']
    tcg = [f'-Zcodegen-backend={dylib}']
    failures = 0
    for opt in levels:
        with tempfile.TemporaryDirectory() as tmp:
            depdir = os.path.join(tmp, 'dep')
            os.makedirs(depdir)
            open(os.path.join(tmp, 'dep.rs'), 'w').write(DEP)
            r = subprocess.run(base + ['--crate-type', 'rlib', '--crate-name', 'dep',
                                       f'-Copt-level={opt}', '--out-dir', depdir,
                                       os.path.join(tmp, 'dep.rs')],
                               env=env, capture_output=True, text=True)
            assert r.returncode == 0, r.stderr
            dep = ['--extern', f'dep={depdir}/libdep.rlib', '-L', depdir]
            # The first traced compile names the credited functions.
            open(os.path.join(tmp, 'callee.rs'), 'w').write(CALLEE)
            probe = os.path.join(tmp, 'probe')
            os.makedirs(probe)
            r = subprocess.run(base + tcg + ['-Ztrust-ir-cg-args=x86-body-trace', '--crate-type',
                                             'rlib', '--crate-name', 'callee',
                                             f'-Copt-level={opt}', '--out-dir', probe] + dep +
                               [os.path.join(tmp, 'callee.rs')],
                               env=env, capture_output=True, text=True)
            valid, traced = set(), {}
            for line in r.stderr.splitlines():
                if 'X86-BODY-TRACE' not in line:
                    continue
                for fn in FUNCTIONS:
                    if f'{len(fn)}{fn} ' in line or line.split('fn=', 1)[1].split(' ', 1)[0].endswith(f'{len(fn)}{fn}'):
                        traced[fn] = line.split(' ', 2)[2][:200]
                        if 'replay=Valid' in line:
                            valid.add(fn)
            print(f'O{opt} credited ({len(valid)}/{len(FUNCTIONS)}): {sorted(valid)}')
            for fn in FUNCTIONS:
                if fn not in valid:
                    print(f'O{opt}   not credited: {fn}: {traced.get(fn, "(no trace line)")}')
            if not valid:
                continue
            open(os.path.join(tmp, 'callee.rs'), 'w').write(callee_src(valid))
            open(os.path.join(tmp, 'caller.rs'), 'w').write(caller_src(valid))
            rlibs = {}
            for be in ('llvm', 'tcg'):
                out = os.path.join(tmp, f'c_{be}')
                os.makedirs(out)
                cmd = base + (tcg if be == 'tcg' else []) + [
                    '--crate-type', 'rlib', '--crate-name', 'callee', f'-Copt-level={opt}',
                    '--out-dir', out] + dep + [os.path.join(tmp, 'callee.rs')]
                r = subprocess.run(cmd, env=env, capture_output=True, text=True)
                if r.returncode != 0:
                    print(f'O{opt} {be} callee (proofs required) FAILED: ' +
                          ' | '.join(r.stderr.splitlines()[-4:])[:800])
                    failures += 1
                    rlibs[be] = None
                else:
                    rlibs[be] = os.path.join(out, 'libcallee.rlib')
            results = {}
            for rb, bb in (('llvm', 'llvm'), ('llvm', 'tcg'), ('tcg', 'llvm'), ('tcg', 'tcg')):
                if not rlibs.get(rb):
                    continue
                binp = os.path.join(tmp, f'b_{rb}_{bb}')
                cmd = base + ['--crate-type', 'bin', f'-Copt-level={opt}', '--extern',
                              f'callee={rlibs[rb]}', '-L', os.path.dirname(rlibs[rb])] + dep + [
                    '-o', binp, os.path.join(tmp, 'caller.rs')]
                if bb == 'tcg':
                    cmd[1:1] = tcg + ['-Ztrust-ir-cg-args=no-proof-certs']
                r = subprocess.run(cmd, env=env, capture_output=True, text=True)
                if r.returncode != 0:
                    print(f'O{opt} {rb}-rlib+{bb}-bin compile FAILED: ' +
                          ' | '.join(r.stderr.splitlines()[-3:])[:600])
                    failures += 1
                    continue
                run = subprocess.run([binp], capture_output=True, text=True)
                results[(rb, bb)] = (run.returncode, run.stdout)
                print(f'O{opt} {rb}-rlib+{bb}-bin: exit {run.returncode}, '
                      f'{len(run.stdout.splitlines())} lines')
            oracle = results.get(('llvm', 'llvm'))
            for cell, outcome in results.items():
                if outcome != oracle:
                    print(f'O{opt} MISMATCH {cell} vs llvm-llvm')
                    failures += 1
    print(f'failures: {failures}')
    sys.exit(1 if failures else 0)


if __name__ == '__main__':
    main()
