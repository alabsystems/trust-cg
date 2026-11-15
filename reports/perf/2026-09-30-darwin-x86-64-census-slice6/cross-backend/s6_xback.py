#!/usr/bin/env python3
"""Slice-6 cross-backend matrix: a callee crate of branchy functions (diamonds and joins,
early returns, nested and sequential branches, a `match` compare chain, a branch on a
`bool` parameter, a call on one arm, a panic arm), compiled by LLVM and by trust-cg WITH
PROOFS REQUIRED (the bridge default: the crate promotes only if every function's body
theorem replays Valid), crossed with LLVM and trust-cg callers in all four rlib x bin cells.
Every cell must print exactly the oracle's (LLVM rlib + LLVM bin) output.
usage: s6_xback.py <dylib> [opt levels...]"""
import os
import shutil
import subprocess
import sys
import tempfile

TRUSTC = os.path.expanduser('trust/build/x86_64-apple-darwin/stage1/bin/trustc')
TARGET = 'x86_64-apple-darwin'
CALLEE = r'''
#![no_std]
#[inline(never)] pub fn min_u64(a: u64, b: u64) -> u64 { if a < b { a } else { b } }
#[inline(never)] pub fn max_i32(a: i32, b: i32) -> i32 { if a > b { a } else { b } }
#[inline(never)] pub fn abs_i64(x: i64) -> i64 { if x < 0 { x.wrapping_neg() } else { x } }
#[inline(never)] pub fn early_ret(x: u64) -> u64 { if x == 0 { return 7; } x.wrapping_add(1) }
#[inline(never)] pub fn pick(c: bool, a: u64, b: u64) -> u64 { if c { a } else { b } }
#[inline(never)] pub fn nested(a: u64, b: u64, c: u64) -> u64 {
    if a < b { if a < c { 1 } else { 2 } } else { 3 }
}
#[inline(never)] pub fn clamp_u64(x: u64, lo: u64, hi: u64) -> u64 {
    let y = if x < lo { lo } else { x };
    if y > hi { hi } else { y }
}
#[inline(never)] pub fn sign_i64(x: i64) -> i64 { if x < 0 { -1 } else if x > 0 { 1 } else { 0 } }
#[inline(never)] pub fn match3(x: u64) -> u64 { match x { 1 => 10, 2 => 20, 7 => 70, _ => 0 } }
#[inline(never)] pub fn match_u8(x: u8) -> u32 { match x { 0 => 1, 200 => 2, _ => 3 } }
#[inline(never)] pub fn both(c: bool, d: bool) -> bool { if c { d } else { false } }
#[inline(never)] pub fn nz_or_one(x: u8) -> u8 { if x != 0 { x } else { 1 } }
#[inline(never)] pub fn twice(x: u64) -> u64 { x.wrapping_mul(2) }
#[inline(never)] pub fn call_arm(c: bool, x: u64) -> u64 { if c { twice(x) } else { x } }
#[inline(never)] pub fn checked_index(i: u64, n: u64) -> u64 { if i >= n { panic!("out of range") } i }
#[inline(never)] pub fn store_min(p: &mut u64, a: u64, b: u64) { if a < b { *p = a } }
'''
FUNCTIONS = ['min_u64', 'max_i32', 'abs_i64', 'early_ret', 'pick', 'nested', 'clamp_u64',
             'sign_i64', 'match3', 'match_u8', 'both', 'nz_or_one', 'twice', 'call_arm',
             'checked_index', 'store_min']
CALLER = r'''
use std::hint::black_box as bb;
#[inline(never)] fn out(v: u64) { println!("{}", v); }
fn main() {
    let v: [u64; 10] = [0, 1, 2, 5, 7, 0x7f, 0x80, 200, 1 << 63, u64::MAX];
    for &a in &v { for &b in &v {
        out(callee::min_u64(bb(a), bb(b)));
        out(callee::max_i32(bb(a as i32), bb(b as i32)) as u64);
        out(callee::abs_i64(bb(a as i64)) as u64);
        out(callee::early_ret(bb(a)));
        out(callee::pick(bb(a < b), bb(a), bb(b)));
        for &c in &v { out(callee::nested(bb(a), bb(b), bb(c))); }
        out(callee::clamp_u64(bb(a), bb(b), bb(5)));
        out(callee::clamp_u64(bb(a), bb(2), bb(b)));
        out(callee::sign_i64(bb(a as i64)) as u64);
        out(callee::match3(bb(a)));
        out(callee::match_u8(bb(a as u8)) as u64);
        out(callee::both(bb(a < b), bb(b < 7)) as u64);
        out(callee::nz_or_one(bb(a as u8)) as u64);
        out(callee::call_arm(bb(a > b), bb(a)));
        // In range: the panic arm is compiled and proved, never taken.
        out(callee::checked_index(bb(a % 7), bb(8)));
        let mut slot = 99u64;
        callee::store_min(bb(&mut slot), bb(a), bb(b));
        out(slot);
    } }
}
'''


def main():
    dylib = sys.argv[1]
    opts = sys.argv[2:] or ['0']
    base = [TRUSTC, '--edition=2021', '-Ztrust-verify=off', '--target', TARGET,
            '-Cpanic=abort', '-Coverflow-checks=off', '-Ccodegen-units=1']
    env = dict(os.environ, RUSTC_BOOTSTRAP='1', MACOSX_DEPLOYMENT_TARGET='13.0')
    tmp = tempfile.mkdtemp(prefix='s6_xback_')
    open(os.path.join(tmp, 'callee.rs'), 'w').write(CALLEE)
    open(os.path.join(tmp, 'caller.rs'), 'w').write(CALLER)
    failures, cells = [], 0
    for opt in opts:
        rlibs = {}
        for be in ('llvm', 'tcg'):
            out = os.path.join(tmp, f'callee_{be}_O{opt}')
            os.makedirs(out, exist_ok=True)
            cmd = base + ['--crate-type', 'rlib', '--crate-name', 'callee', f'-Copt-level={opt}',
                          '--out-dir', out, os.path.join(tmp, 'callee.rs')]
            if be == 'tcg':
                # Proofs REQUIRED (the bridge default): no `no-proof-certs`.
                cmd[1:1] = [f'-Zcodegen-backend={dylib}', '-Ztrust-ir-cg-args=x86-body-trace']
            r = subprocess.run(cmd, env=env, capture_output=True, text=True)
            if be == 'tcg':
                traced = [line for line in r.stderr.splitlines() if 'X86-BODY-TRACE' in line]
                for fn in FUNCTIONS:
                    hits = [line.split(' bound ', 1)[-1] if ' bound ' in line else
                            line.split(' ', 2)[-1] for line in traced
                            if f'{len(fn)}{fn}' in line]
                    print(f'O{opt} trace {fn:14s} ' + (' || '.join(sorted(set(hits)))[:240]
                                                       if hits else '(no trace line)'))
            if r.returncode != 0:
                failures.append(f'O{opt} callee rlib ({be}) failed: '
                                + ' | '.join(r.stderr.strip().splitlines()[-8:])[:1200])
                rlibs[be] = None
            else:
                rlibs[be] = os.path.join(out, 'libcallee.rlib')
        if rlibs['llvm'] is None:
            continue
        outputs = {}
        for rl_be, bin_be in (('llvm', 'llvm'), ('llvm', 'tcg'), ('tcg', 'llvm'), ('tcg', 'tcg')):
            rl = rlibs[rl_be]
            if rl is None:
                continue
            binp = os.path.join(tmp, f'caller_{rl_be}rlib_{bin_be}bin_O{opt}')
            cmd = base + ['--crate-type', 'bin', f'-Copt-level={opt}', '--extern', f'callee={rl}',
                          '-L', os.path.dirname(rl), '-o', binp, os.path.join(tmp, 'caller.rs')]
            if bin_be == 'tcg':
                # The caller's `main` is outside the lane: the bin is built without proof
                # certificates; the callee rlib's proof requirement is what this matrix tests.
                cmd[1:1] = [f'-Zcodegen-backend={dylib}', '-Ztrust-ir-cg-args=no-proof-certs']
            r = subprocess.run(cmd, env=env, capture_output=True, text=True)
            label = f'O{opt} {rl_be}-rlib+{bin_be}-bin'
            if r.returncode != 0:
                failures.append(f'{label}: compile failed: '
                                + ' | '.join(r.stderr.strip().splitlines()[-6:])[:800])
                continue
            run = subprocess.run([binp], capture_output=True, text=True)
            cells += 1
            outputs[(rl_be, bin_be)] = (run.returncode, run.stdout)
            print(f'{label}: exit {run.returncode}, {len(run.stdout.splitlines())} lines')
        oracle = outputs.get(('llvm', 'llvm'))
        for key, got in outputs.items():
            if got != oracle:
                a = oracle[1].splitlines() if oracle else []
                b = got[1].splitlines()
                diff = next((f'line {i}: oracle [{x}] got [{y}]' for i, (x, y) in enumerate(zip(a, b))
                             if x != y), f'exit/len differ: {oracle and oracle[0]} vs {got[0]}')
                failures.append(f'O{opt} {key[0]}-rlib+{key[1]}-bin differs from the oracle: {diff}')
    print(f'cells built and run: {cells}; failures: {len(failures)}')
    for f in failures:
        print('  FAIL', f)
    shutil.rmtree(tmp, ignore_errors=True)
    sys.exit(1 if failures else 0)


main()
