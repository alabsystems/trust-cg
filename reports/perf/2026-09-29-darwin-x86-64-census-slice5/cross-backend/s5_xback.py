#!/usr/bin/env python3
"""Slice-5 cross-backend matrix: a callee crate whose every function is inside the x86-64
body-theorem slice-5 domain (scalar pairs, a pair call, branch-free compares, a static's
address and a load through it), compiled by LLVM and by trust-cg WITH PROOFS REQUIRED (the
bridge default: the crate must promote, so every function's body theorem must replay Valid),
crossed with LLVM and trust-cg callers in all four rlib x bin cells. Every cell must print
exactly the oracle's (LLVM rlib + LLVM bin) output.
usage: s5_xback.py <dylib> [opt levels...]"""
import os
import shutil
import subprocess
import sys
import tempfile

TRUSTC = os.path.expanduser('trust/build/x86_64-apple-darwin/stage1/bin/trustc')
TARGET = 'x86_64-apple-darwin'
CALLEE = r'''
#![no_std]
pub static G: u64 = 0x1234_5678_9abc_def0;
#[inline(never)] pub fn pair_swap(a: u64, b: u64) -> (u64, u64) { (b, a) }
#[inline(never)] pub fn pair_u32(a: u32, b: u32) -> (u32, u32) { (b.wrapping_add(1), a ^ 0xff) }
#[inline(never)] pub fn pair_u8(a: u8, b: u8) -> (u8, u8) { (a.wrapping_add(b), b) }
#[inline(never)] pub fn pair_u64_bool(a: u64, b: u64) -> (u64, bool) { (a.wrapping_add(b), a < b) }
#[inline(never)] pub fn pair_i16(a: i16, b: i16) -> (i16, i64) { (a.wrapping_sub(b), b as i64) }
#[inline(never)] pub fn pair_diff(a: u64, b: u64) -> u64 { let (x, y) = pair_swap(a, b); x.wrapping_sub(y) }
#[inline(never)] pub fn lt_u64(a: u64, b: u64) -> bool { a < b }
#[inline(never)] pub fn lt_i64(a: i64, b: i64) -> bool { a < b }
#[inline(never)] pub fn ge_i8(a: i8, b: i8) -> bool { a >= b }
#[inline(never)] pub fn le_u16(a: u16, b: u16) -> bool { a <= b }
#[inline(never)] pub fn gt_i32(a: i32, b: i32) -> bool { a > b }
#[inline(never)] pub fn ne_u32(a: u32, b: u32) -> bool { a != b }
#[inline(never)] pub fn lt_as_u64(a: u64, b: u64) -> u64 { (a < b) as u64 }
#[inline(never)] pub fn eq_five(a: u64) -> bool { a == 5 }
#[inline(never)] pub fn g_addr() -> &'static u64 { &G }
#[inline(never)] pub fn g_load() -> u64 { G }
#[inline(never)] pub fn store_lt(p: &mut bool, a: u64, b: u64) { *p = a < b }
'''
FUNCTIONS = ['pair_swap', 'pair_u32', 'pair_u8', 'pair_u64_bool', 'pair_i16', 'pair_diff',
             'lt_u64', 'lt_i64', 'ge_i8', 'le_u16', 'gt_i32', 'ne_u32', 'lt_as_u64', 'eq_five',
             'g_addr', 'g_load', 'store_lt']
CALLER = r'''
use std::hint::black_box as bb;
#[inline(never)] fn out(v: u64) { println!("{}", v); }
fn main() {
    let v: [u64; 8] = [0, 1, 2, 5, 0x7f, 0x80, 1 << 63, u64::MAX];
    for &a in &v { for &b in &v {
        let (x, y) = callee::pair_swap(bb(a), bb(b)); out(x); out(y);
        let (p, q) = callee::pair_u32(bb(a as u32), bb(b as u32)); out(p as u64); out(q as u64);
        let (r, s) = callee::pair_u8(bb(a as u8), bb(b as u8)); out(r as u64); out(s as u64);
        let (t, u) = callee::pair_u64_bool(bb(a), bb(b)); out(t); out(u as u64);
        let (w, z) = callee::pair_i16(bb(a as i16), bb(b as i16)); out(w as u64); out(z as u64);
        out(callee::pair_diff(bb(a), bb(b)));
        out(callee::lt_u64(bb(a), bb(b)) as u64);
        out(callee::lt_i64(bb(a as i64), bb(b as i64)) as u64);
        out(callee::ge_i8(bb(a as i8), bb(b as i8)) as u64);
        out(callee::le_u16(bb(a as u16), bb(b as u16)) as u64);
        out(callee::gt_i32(bb(a as i32), bb(b as i32)) as u64);
        out(callee::ne_u32(bb(a as u32), bb(b as u32)) as u64);
        out(callee::lt_as_u64(bb(a), bb(b)));
        out(callee::eq_five(bb(a)) as u64);
        let mut flag = !callee::lt_u64(a, b);
        callee::store_lt(bb(&mut flag), bb(a), bb(b));
        out(flag as u64);
    } }
    out(callee::g_load());
    out(core::ptr::eq(callee::g_addr(), &callee::G) as u64);
}
'''


def main():
    dylib = sys.argv[1]
    opts = sys.argv[2:] or ['0']
    base = [TRUSTC, '--edition=2021', '-Ztrust-verify=off', '--target', TARGET,
            '-Cpanic=abort', '-Coverflow-checks=off', '-Ccodegen-units=1']
    env = dict(os.environ, RUSTC_BOOTSTRAP='1', MACOSX_DEPLOYMENT_TARGET='13.0')
    tmp = tempfile.mkdtemp(prefix='s5_xback_')
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
                            line.split(' ', 2)[-1] for line in traced if f'{fn}' in line]
                    print(f'O{opt} trace {fn:14s} ' + (' || '.join(sorted(set(hits)))[:200]
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
