#!/usr/bin/env python3
"""Slice-8 cross-backend matrix (aggregates in general-purpose registers),
natively.

Three crates: `dep` holds callees that take or return small aggregates by
value (`take4([u8; 4])`, `give2 -> [u32; 2]`, `give5 -> [u8; 5]`,
`opt_ref(Option<&u64>)`, `take6([u16; 3])`), always compiled by LLVM, so every
callee is an LLVM-compiled one; `callee` holds the functions under test
(aggregate parameters and results, and callers of `dep` passing or receiving
aggregates); `main` drives them. The `callee` rlib is
built by LLVM or by trust-cg WITH PROOFS REQUIRED (the bridge default: it
promotes only if every function's body theorem replays Valid), containing
EXACTLY the functions a first traced compile credits (`replay=Valid`); the bin
by LLVM or trust-cg (`no-proof-certs`, it only calls). All four rlib x bin
cells must print exactly the oracle's (LLVM rlib + LLVM bin) output.

usage: s8_credited_native.py <dylib> [opt levels...]   (default: 0)
       S8_ALL=1 compiles every function, without proof certificates
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
#[inline(never)] pub fn take4(a: [u8; 4]) -> u64 { (a[0] as u64) | ((a[3] as u64) << 40) ^ ((a[1] as u64) * 3) }
#[inline(never)] pub fn give2(x: u64) -> [u32; 2] { [x as u32, (x >> 32) as u32 ^ 0x55] }
#[inline(never)] pub fn give5(x: u64) -> [u8; 5] { let b = x.to_le_bytes(); [b[0], b[1], b[2], b[3] ^ 7, b[4]] }
#[inline(never)] pub fn opt_ref(o: Option<&u64>) -> u64 { match o { Some(v) => v.wrapping_mul(3), None => 11 } }
#[inline(never)] pub fn take6(a: [u16; 3]) -> u64 { (a[0] as u64) ^ ((a[1] as u64) << 16) ^ ((a[2] as u64) << 33) }
'''
CALLEE = r'''
#![no_std]
use dep::*;
#[inline(never)] pub fn field(a: [u8; 4]) -> u8 { a[2] }
#[inline(never)] pub fn wide_field(a: [u8; 4]) -> u32 { a[1] as u32 }
#[inline(never)] pub fn arr3(a: [u16; 3]) -> u16 { a[0] ^ a[2] }
#[inline(never)] pub fn opt_or(o: Option<&u64>, d: u64) -> u64 { match o { Some(v) => *v, None => d } }
#[inline(never)] pub fn pair(x: u32, y: u32) -> [u32; 2] { [x, y] }
#[inline(never)] pub fn bytes5(x: u8) -> [u8; 5] { [x, 1, 2, 3, x] }
#[inline(never)] pub fn wide(x: u64, y: u64) -> [u64; 2] { [x, y] }
#[inline(never)] pub fn fwd(a: [u16; 2]) -> [u16; 2] { a }
#[inline(never)] pub fn pass4(x: u8) -> u64 { take4([x, 1, 2, x]) }
#[inline(never)] pub fn pass6(a: [u16; 3]) -> u64 { take6(a) }
#[inline(never)] pub fn res2(x: u64) -> u32 { let r = give2(x); r[0] ^ r[1] }
#[inline(never)] pub fn fwd2(x: u64) -> [u32; 2] { give2(x) }
#[inline(never)] pub fn res5(x: u64) -> u8 { let r = give5(x); r[0] ^ r[4] }
#[inline(never)] pub fn opt_pass(o: Option<&u64>) -> u64 { opt_ref(o) }
'''
FUNCTIONS = ['field', 'wide_field', 'arr3', 'opt_or', 'pair', 'bytes5', 'wide', 'fwd', 'pass4',
             'pass6', 'res2', 'fwd2', 'res5', 'opt_pass']
CALLS = {
    'field': 'out(callee::field(bb((a as u32).to_le_bytes())) as u64);',
    'wide_field': 'out(callee::wide_field(bb((a as u32).to_le_bytes())) as u64);',
    'arr3': 'out(callee::arr3(bb([a as u16, b as u16, (a >> 16) as u16])) as u64);',
    'opt_or': 'out(callee::opt_or(bb(if a & 1 == 1 { Some(&b) } else { None }), bb(a)));',
    'pair': '{ let p = callee::pair(bb(a as u32), bb(b as u32)); out((p[0] as u64) ^ ((p[1] as u64) << 32)); }',
    'bytes5': '{ let p = callee::bytes5(bb(a as u8)); out(p.iter().fold(0u64, |s, x| (s << 8) | *x as u64)); }',
    'wide': '{ let p = callee::wide(bb(a), bb(b)); out(p[0] ^ p[1].rotate_left(7)); }',
    'fwd': '{ let p = callee::fwd(bb([a as u16, b as u16])); out((p[0] as u64) | ((p[1] as u64) << 16)); }',
    'pass4': 'out(callee::pass4(bb(a as u8)));',
    'pass6': 'out(callee::pass6(bb([a as u16, b as u16, (a >> 20) as u16])));',
    'res2': 'out(callee::res2(bb(a)) as u64);',
    'fwd2': '{ let p = callee::fwd2(bb(a)); out((p[0] as u64) ^ ((p[1] as u64) << 32)); }',
    'res5': 'out(callee::res5(bb(a)) as u64);',
    'opt_pass': 'out(callee::opt_pass(bb(if a & 2 == 2 { Some(&b) } else { None })));',
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
                if 'X86-BODY-TRACE' not in line or 'fn=' not in line:
                    continue
                for fn in FUNCTIONS:
                    if f'{len(fn)}{fn} ' in line or line.split('fn=', 1)[1].split(' ', 1)[0].endswith(f'{len(fn)}{fn}'):
                        traced[fn] = line.split(' ', 2)[2][:200]
                        if 'replay=Valid' in line:
                            valid.add(fn)
            # S8_ALL=1: every function, the trust-cg rlib without proof
            # certificates (an ABI matrix of the shapes that make no claim).
            if os.environ.get('S8_ALL'):
                valid = set(FUNCTIONS)
                tcg = tcg + ['-Ztrust-ir-cg-args=no-proof-certs']
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
