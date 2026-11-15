#!/usr/bin/env python3
"""OD-224: z3 lemmas for the two x86-64 spellings that depart from the design.

EVIDENCE CLASS: SOLVER-BACKED (z3, in Python) ONLY. Nothing here is replayed by AY or checked by
Clean, nothing is registered or credited, and the lemmas are composed by the argument in the
report (README section 4.7), not by a checker. A query z3 does not decide within its budget is
recorded as `undecided`, never as proved.

Each lemma is one query "exists a counterexample" whose expected answer is `unsat`.

K  The unsigned multiply by a constant C (`build_u128_mul_overflow_divfree`, its `constant` arm):
   flag = x >u limit(C), limit(C) = u128::MAX.checked_div(C).unwrap_or(u128::MAX). For every C the
   adapter admits (`mulo_u128_constant`: any canonical trust-ir constant, i.e. every C in
   [0, 2^128)) and every x in [0, 2^128), the flag equals "the exact product x * C is at least
   2^128". C = 0 and C = 1 are their own queries (C = 0: no division is done, the limit is MAX and
   the flag false; C = 1: the limit is MAX by the division and the flag false); C >= 2 is
   stated with the limit's defining bounds and, separately, with z3's integer division.

S  The signed magnitudes route (`build_i128_signed_mul_overflow_divfree`), lemma by lemma:
   S1 the I64 mask arithmetic is the 128-bit `x <s 0 ? -x : x` for every x (BV);
   S1b that value read unsigned is |x| for every signed x, MIN included (|MIN| = 2^127) (Int);
   S2 the masks are 0 or all ones as the signs say, and `push_masked_negation_high` is the high
      limb of `neg ? -r : r` (BV);
   S3 the signed product is `neg ? -N : N` with N = |a| * |b|, and `neg ? -r : r` is N mod 2^128
      for r = a * b mod 2^128 (Int, by the four sign cases);
   S4 the unsigned core: core(x, y, hi(x * y mod 2^128)) <=> x * y >= 2^128 (Int; the design's
      `int 128 u` query over the shipped op list, which is the design's);
   S5 the sign check's bits: ((r1 >>a 63) ^ mn) != 0 <=> (r <s 0) xor neg, and (r0 | r1) != 0
      <=> r != 0 (BV);
   S6 the composition: with N free, flag(N, neg) = (N >= 2^128) | (r != 0 & (r >= 2^127) != neg)
      equals "neg ? -N : N is outside [-2^127, 2^127)" (Int).
   S7 the whole shipped signed spelling at once (BV at 128 bits): an attempt, expected to be
      undecided (multiplier circuits), and recorded as what it is.
   X  cross-checks: the shipped spelling (`shipped_smulo`, the adapter's 58 instructions in order)
      against trust-ir's flag on every pair at W = 8 and on a 128-bit edge battery, concretely.

usage: od224_z3.py [timeout_s] [widths...]   -> one JSON object on stdout
"""
import json
import os
import resource
import sys
import time

import z3

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "design"))
from lir_model import Conc, Z3Ops, u_core  # noqa: E402
from z3_proofs import IntOps  # noqa: E402


def check(solver, timeout_s):
    solver.set("timeout", int(timeout_s * 1000))
    t0 = time.process_time()
    result = str(solver.check())
    cpu = round(time.process_time() - t0, 3)
    verdict = {"unsat": "proved", "sat": "REFUTED", "unknown": "undecided"}[result]
    out = {"z3": result, "verdict": verdict, "cpu_s": cpu}
    if result == "sat":
        out["model"] = str(solver.model())
    return out


# ---------------------------------------------------------------------------
# K: x * C vs x >u limit(C)
# ---------------------------------------------------------------------------

def constant_lemmas(W, timeout_s):
    M = (1 << W) - 1  # u128::MAX at W = 128
    x, c, lim = z3.Ints("x c lim")
    dom = [x >= 0, x <= M, c >= 0, c <= M]
    out = {}

    # C = 0: checked_div(0) is None -> unwrap_or(MAX): no division is performed, the limit
    # is MAX; the flag x >u MAX is false, and so is the spec (x * 0 = 0 <= MAX).
    s = z3.Solver()
    s.add(*dom, c == 0)
    flag = x > M
    spec = x * c > M
    s.add(z3.Or(flag != spec, flag))
    out[f"K0[W={W}] C=0: limit=MAX, flag false and = spec"] = check(s, timeout_s)

    # C = 1: checked_div(1) is Some(MAX): the limit is MAX; flag false = spec.
    s = z3.Solver()
    s.add(*dom, c == 1)
    flag = x > M / c
    spec = x * c > M
    s.add(z3.Or(flag != spec, flag))
    out[f"K1[W={W}] C=1: limit=MAX/1=MAX, flag false and = spec"] = check(s, timeout_s)

    # C >= 2, the limit by its defining bounds (floor division: lim*C <= MAX < (lim+1)*C,
    # lim >= 0 -- what u128's `/` computes for a nonzero divisor).
    s = z3.Solver()
    s.add(*dom, c >= 2, lim >= 0, lim * c <= M, M < lim * c + c)
    s.add((x > lim) != (x * c > M))
    out[f"K2[W={W}] C>=2: x >u floor(MAX/C) <=> x*C > MAX (floor by its bounds)"] = check(
        s, timeout_s)

    # C >= 2, the limit as z3's integer division (floor for a positive divisor).
    s = z3.Solver()
    s.add(*dom, c >= 2)
    s.add((x > M / c) != (x * c > M))
    out[f"K3[W={W}] C>=2: x >u MAX div C <=> x*C > MAX (z3 div)"] = check(s, timeout_s)

    # The bounds characterize z3's division (so K2 and K3 state the same limit).
    s = z3.Solver()
    s.add(c >= 1, c <= M)
    q = M / c
    s.add(z3.Not(z3.And(q >= 0, q * c <= M, M < q * c + c)))
    out[f"K4[W={W}] MAX div C satisfies the floor bounds"] = check(s, timeout_s)
    return out


def constant_exhaustive(W):
    """Every (x, C) at W bits, concretely: the limit form as the adapter computes it."""
    M = (1 << W) - 1
    bad = 0
    for c in range(M + 1):
        limit = M // c if c else M
        for x in range(M + 1):
            if (x > limit) != (x * c > M):
                bad += 1
    return {"pairs": (M + 1) ** 2, "mismatches": bad}


# ---------------------------------------------------------------------------
# The shipped signed spelling, as BV terms (the adapter's op list, in order)
# ---------------------------------------------------------------------------

def bv_limbs(x, W):
    H = W // 2
    return z3.Extract(H - 1, 0, x), z3.Extract(H - 1, 0, z3.LShR(x, H))


def bv_masked_negation_high(x0, x1, m, H):
    """`push_masked_negation_high`: (x1 ^ m) - m - (((x0 | (0 - x0)) >>u (H-1)) & m)."""
    zero = z3.BitVecVal(0, H)
    neg0 = zero - x0
    nonzero = z3.LShR(x0 | neg0, H - 1)
    borrow = nonzero & m
    return ((x1 ^ m) - m) - borrow


def bv_magnitude(x0, x1, m, H):
    """`push_magnitude_limbs`: [(x0 ^ m) - m, masked_negation_high]."""
    return (x0 ^ m) - m, bv_masked_negation_high(x0, x1, m, H)


def bv_core(x0, x1, y0, y1, p1, H):
    """`push_u128_mulo_core` over limbs (the design's u_core, limb inputs)."""
    def cu(u, v):
        p = z3.ZeroExt(H, u) * z3.ZeroExt(H, v)
        return z3.Extract(H - 1, 0, p), z3.Extract(2 * H - 1, H, p) != 0
    m1, o1 = cu(x1, y0)
    m2, o2 = cu(x0, y1)
    t = m1 + m2
    c = z3.ULT(p1, t)
    zero = z3.BitVecVal(0, H)
    both = z3.And(x1 != zero, y1 != zero)
    return z3.Or(o1, o2, c, both)


def bv_shipped_smulo(a, b, W):
    """The adapter's 58-instruction signed flag (adapter_i128_mulo_tests' `expected_s`)."""
    H = W // 2
    k = H - 1
    zero = z3.BitVecVal(0, H)
    r = a * b                                            # v2 = Imul
    a0, a1 = bv_limbs(a, W)                              # v6, v8
    b0, b1 = bv_limbs(b, W)                              # v9, v11
    r0, r1 = bv_limbs(r, W)                              # v12, v14
    ma, mb = a1 >> k, b1 >> k                            # v15, v16 (Sshr)
    ua0, ua1 = bv_magnitude(a0, a1, ma, H)               # v18, v25
    ub0, ub1 = bv_magnitude(b0, b1, mb, H)               # v27, v34
    mn = ma ^ mb                                         # v35
    pu1 = bv_masked_negation_high(r0, r1, mn, H)         # v42
    ou = bv_core(ua0, ua1, ub0, ub1, pu1, H)             # v54
    sign = ((r1 >> k) ^ mn) != zero                      # v55..v57
    r_nz = (r0 | r1) != zero                             # v58, v59
    return z3.Or(ou, z3.And(sign, r_nz))                 # v60, v61


def bv_spec_s(a, b, W):
    p = z3.SignExt(W, a) * z3.SignExt(W, b)
    return p != z3.SignExt(W, z3.Extract(W - 1, 0, p))


# ---------------------------------------------------------------------------
# S: lemma by lemma
# ---------------------------------------------------------------------------

def signed_lemmas(W, timeout_s, monolithic_s):
    H = W // 2
    Mw = 1 << W
    ones = z3.BitVecVal((1 << H) - 1, H)
    zero = z3.BitVecVal(0, H)
    out = {}

    # S1: the mask arithmetic is |x| as a W-bit pattern, i.e. ite(x <s 0, -x, x).
    x = z3.BitVec("x", W)
    x0, x1 = bv_limbs(x, W)
    m = x1 >> (H - 1)
    lo, hi = bv_magnitude(x0, x1, m, H)
    s = z3.Solver()
    s.add(z3.Concat(hi, lo) != z3.If(x < 0, -x, x))
    out[f"S1[W={W}] magnitude limbs == ite(x <s 0, -x, x)"] = check(s, timeout_s)
    s = z3.Solver()
    s.add(x == z3.BitVecVal(1 << (W - 1), W), z3.Concat(hi, lo) != z3.BitVecVal(1 << (W - 1), W))
    out[f"S1-MIN[W={W}] magnitude(MIN) == 2^{W - 1}"] = check(s, timeout_s)

    # S1b: that pattern, read unsigned, is |xs| for the signed value xs (MIN included).
    xs = z3.Int("xs")
    xu = xs % Mw                                        # the pattern of xs
    pat = z3.If(xu >= Mw // 2, (-xu) % Mw, xu)          # ite(x <s 0, -x, x), unsigned
    s = z3.Solver()
    s.add(xs >= -(Mw // 2), xs < Mw // 2)
    s.add(z3.Not(z3.And(pat == z3.If(xs < 0, -xs, xs), pat >= 0, pat <= Mw // 2)))
    out[f"S1b[W={W}] ite(x<s0,-x,x) read unsigned == |xs| <= 2^{W - 1}"] = check(s, timeout_s)

    # S2: the masks, and pu1 = hi(neg ? -r : r).
    a, b, r = z3.BitVecs("a b r", W)
    a1 = bv_limbs(a, W)[1]
    b1 = bv_limbs(b, W)[1]
    ma, mb = a1 >> (H - 1), b1 >> (H - 1)
    s = z3.Solver()
    s.add(z3.Not(z3.And(
        ma == z3.If(a < 0, ones, zero),
        mb == z3.If(b < 0, ones, zero),
        (ma ^ mb) == z3.If(z3.Xor(a < 0, b < 0), ones, zero),
    )))
    out[f"S2a[W={W}] sign masks: all ones iff negative; mn iff the signs differ"] = check(
        s, timeout_s)
    neg = z3.Bool("neg")
    mn = z3.If(neg, ones, zero)
    r0, r1 = bv_limbs(r, W)
    pu1 = bv_masked_negation_high(r0, r1, mn, H)
    s = z3.Solver()
    s.add(pu1 != bv_limbs(z3.If(neg, -r, r), W)[1])
    out[f"S2b[W={W}] masked_negation_high(r, mn) == hi(neg ? -r : r)"] = check(s, timeout_s)

    # S3: by sign case, in integers (the design's L2 for the shipped magnitudes, which S1/S1b
    # make |a| and |b|): P = as*bs = (neg ? -N : N), N = |as|*|bs|, and
    # (neg ? -r : r) mod 2^W = N mod 2^W for r = P mod 2^W.
    As, Bs = z3.Ints("as bs")
    half = Mw // 2
    for ca in (False, True):
        for cb in (False, True):
            s = z3.Solver()
            s.add(As >= -half, As < half, Bs >= -half, Bs < half)
            s.add(As < 0 if ca else As >= 0, Bs < 0 if cb else Bs >= 0)
            ua = -As if ca else As
            ub = -Bs if cb else Bs
            N = ua * ub
            P = As * Bs
            negc = ca != cb
            rr = P % Mw
            pu = ((-rr) % Mw) if negc else rr
            s.add(z3.Not(z3.And(P == (-N if negc else N), pu == N % Mw, N >= 0)))
            out[f"S3[W={W}] a<0={ca} b<0={cb}: P = neg?-N:N, (neg?-r:r) = N mod 2^W"] = check(
                s, timeout_s)

    # S4: the unsigned core (shipped op list = the design's), integer encoding.
    o = IntOps(W)
    xi, yi = z3.Ints("x y")
    s = z3.Solver()
    s.add(xi >= 0, xi < Mw, yi >= 0, yi < Mw)
    p = o.imul_w(xi, yi)
    s.add(u_core(o, xi, yi, p) != (xi * yi >= Mw))
    out[f"S4[W={W}] core(x, y, x*y mod 2^W) <=> x*y >= 2^W"] = check(s, timeout_s)

    # S5: the sign check's bits.
    s = z3.Solver()
    s.add(z3.Not(z3.And(
        (((r1 >> (H - 1)) ^ mn) != zero) == z3.Xor(r < 0, neg),
        ((r0 | r1) != zero) == (r != 0),
    )))
    out[f"S5[W={W}] sign-check bits: ((r1>>a{H - 1})^mn)!=0 <=> (r<s0)^neg; (r0|r1)!=0 <=> r!=0"] = (
        check(s, timeout_s))

    # S6: the composition, N free (N = |a|*|b| <= 2^(2W-2)).
    Ni = z3.Int("N")
    negb = z3.Bool("negb")
    Pn = z3.If(negb, -Ni, Ni)
    rr = Pn % Mw
    ou = Ni >= Mw
    bad = z3.And(rr != 0, (rr >= half) != negb)
    flag = z3.Or(ou, bad)
    spec = z3.Not(z3.And(Pn >= -half, Pn < half))
    s = z3.Solver()
    s.add(Ni >= 0, Ni <= (half * half))
    s.add(flag != spec)
    out[f"S6[W={W}] (N>=2^W) | (r!=0 & (r>=2^{W - 1})!=neg) <=> neg?-N:N out of range"] = check(
        s, timeout_s)

    # S7: the whole shipped signed spelling against trust-ir's flag, bit-blasted.
    if monolithic_s:
        s = z3.Solver()
        s.add(bv_shipped_smulo(a, b, W) != bv_spec_s(a, b, W))
        out[f"S7[W={W}] shipped signed flag == spec, monolithic BV (attempt)"] = check(
            s, monolithic_s)
    return out


# ---------------------------------------------------------------------------
# C: negative controls -- each lemma's query with one deliberate defect must be SAT
# (so the queries are not vacuous), and each lemma's hypotheses are satisfiable
# ---------------------------------------------------------------------------

def controls(W, timeout_s):
    H = W // 2
    Mw = 1 << W
    M = Mw - 1
    half = Mw // 2
    ones = z3.BitVecVal((1 << H) - 1, H)
    zero = z3.BitVecVal(0, H)
    out = {}

    def expect_sat(name, solver):
        res = check(solver, timeout_s)
        res["verdict"] = {"sat": "refuted, as a control must be", "unsat": "SURVIVED (vacuous?)",
                          "unknown": "undecided"}[res["z3"]]
        res.pop("model", None)
        out[name] = res

    x, c, lim = z3.Ints("x c lim")
    dom = [x >= 0, x <= M, c >= 0, c <= M]
    s = z3.Solver()
    s.add(*dom, c >= 2, lim >= 0, lim * c <= M, M < lim * c + c)
    expect_sat(f"C-K2-hyp[W={W}] the floor bounds are satisfiable", s)
    s = z3.Solver()
    s.add(*dom, c >= 2)
    s.add((x >= M / c) != (x * c > M))
    expect_sat(f"C-K-uge[W={W}] x >=u limit for x >u limit", s)
    s = z3.Solver()
    s.add(*dom, c >= 2)
    s.add((x > M / c + 1) != (x * c > M))
    expect_sat(f"C-K-plus1[W={W}] the limit plus one", s)
    s = z3.Solver()
    s.add(*dom, c == 0)
    s.add((x > 0) != (x * c > M))
    expect_sat(f"C-K-zero[W={W}] C = 0 with a limit of 0 (no unwrap_or(MAX))", s)

    xb = z3.BitVec("x", W)
    x0, x1 = bv_limbs(xb, W)
    m = x1 >> (H - 1)
    lo = (x0 ^ m) - m
    hi_no_borrow = (x1 ^ m) - m
    s = z3.Solver()
    s.add(z3.Concat(hi_no_borrow, lo) != z3.If(xb < 0, -xb, xb))
    expect_sat(f"C-S1-borrow[W={W}] the magnitude's high limb without the borrow", s)
    ml = z3.LShR(x1, H - 1)
    lo2, hi2 = bv_magnitude(x0, x1, ml, H)
    s = z3.Solver()
    s.add(z3.Concat(hi2, lo2) != z3.If(xb < 0, -xb, xb))
    expect_sat(f"C-S1-shr[W={W}] the sign mask by a logical shift", s)

    rb = z3.BitVec("r", W)
    neg = z3.Bool("neg")
    mn = z3.If(neg, ones, zero)
    r0, r1 = bv_limbs(rb, W)
    s = z3.Solver()
    s.add(((r1 ^ mn) - mn) != bv_limbs(z3.If(neg, -rb, rb), W)[1])
    expect_sat(f"C-S2b-borrow[W={W}] pu1 without the borrow", s)
    s = z3.Solver()
    s.add((((r1 >> (H - 1)) | mn) != zero) != z3.Xor(rb < 0, neg))
    expect_sat(f"C-S5-or[W={W}] the sign check's xor as an or", s)

    o = IntOps(W)
    xi, yi = z3.Ints("x y")
    s = z3.Solver()
    s.add(xi >= 0, xi < Mw, yi >= 0, yi < Mw)
    s.add(u_core(o, xi, yi, o.imul_w(xi, yi), "drop_carry") != (xi * yi >= Mw))
    expect_sat(f"C-S4-carry[W={W}] the core without its carry term", s)

    Ni = z3.Int("N")
    negb = z3.Bool("negb")
    Pn = z3.If(negb, -Ni, Ni)
    rr = Pn % Mw
    flag = z3.Or(Ni >= Mw, (rr >= half) != negb)
    spec = z3.Not(z3.And(Pn >= -half, Pn < half))
    s = z3.Solver()
    s.add(Ni >= 0, Ni <= half * half, flag != spec)
    expect_sat(f"C-S6-zero[W={W}] the composition without the r != 0 guard", s)
    return out


# ---------------------------------------------------------------------------
# X: concrete cross-checks of the shipped spelling
# ---------------------------------------------------------------------------

def conc_shipped_smulo(a, b, W):
    """`bv_shipped_smulo` on Python ints (the same op list, concretely)."""
    H = W // 2
    MH, MW = (1 << H) - 1, (1 << W) - 1
    k = H - 1
    def sar(v):
        return MH if (v >> k) & 1 else 0
    def mag_high(x0, x1, m):
        neg0 = (-x0) & MH
        nonzero = ((x0 | neg0) >> k) & 1
        borrow = nonzero & m
        return (((x1 ^ m) - m) - borrow) & MH
    r = (a * b) & MW
    a0, a1, b0, b1, r0, r1 = a & MH, a >> H, b & MH, b >> H, r & MH, r >> H
    ma, mb = sar(a1), sar(b1)
    ua0, ua1 = ((a0 ^ ma) - ma) & MH, mag_high(a0, a1, ma)
    ub0, ub1 = ((b0 ^ mb) - mb) & MH, mag_high(b0, b1, mb)
    mn = ma ^ mb
    pu1 = mag_high(r0, r1, mn)
    def cu(u, v):
        pr = u * v
        return pr & MH, (pr >> H) != 0
    m1, o1 = cu(ua1, ub0)
    m2, o2 = cu(ua0, ub1)
    t = (m1 + m2) & MH
    ou = o1 or o2 or pu1 < t or (ua1 != 0 and ub1 != 0)
    sign = (sar(r1) ^ mn) != 0
    r_nz = (r0 | r1) != 0
    return ou or (sign and r_nz)


def cross_checks():
    c8 = Conc(8)
    bad8 = sum(1 for a in range(256) for b in range(256)
               if conc_shipped_smulo(a, b, 8) != c8.spec_s(a, b))
    c128 = Conc(128)
    edges = [0, 1, 2, 3, (1 << 63), (1 << 64) - 1, 1 << 64, (1 << 64) + 1, (1 << 126),
             (1 << 127) - 1, 1 << 127, (1 << 127) + 1, (1 << 128) - 1, (1 << 128) - 2,
             0x2AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA, 0xdeadbeefcafef00d0123456789abcdef]
    edges = sorted(set(edges + [(-e) & ((1 << 128) - 1) for e in edges]))
    bad128 = sum(1 for a in edges for b in edges
                 if conc_shipped_smulo(a, b, 128) != c128.spec_s(a, b))
    return {"X[W=8] shipped signed spelling vs trust-ir flag, every pair":
            {"pairs": 65536, "mismatches": bad8},
            "X[W=128] the same on every pair of an edge battery":
            {"pairs": len(edges) ** 2, "mismatches": bad128},
            "K-exhaustive[W=8] every (x, C)": constant_exhaustive(8)}


if __name__ == "__main__":
    timeout_s = float(sys.argv[1]) if len(sys.argv) > 1 else 120
    widths = [int(w) for w in sys.argv[2:]] or [128, 64]
    soft, hard = resource.getrlimit(resource.RLIMIT_CPU)
    t0 = time.process_time()
    results = {"z3": z3.get_version_string(), "timeout_s": timeout_s,
               "evidence_class": "solver-backed (z3) only; not replayed by AY/Clean",
               "cpu_limit_s": None if soft == resource.RLIM_INFINITY else soft}
    for W in widths:
        results.update(constant_lemmas(W, timeout_s))
    results.update(signed_lemmas(128, timeout_s, monolithic_s=min(timeout_s, 120)))
    results.update(signed_lemmas(64, timeout_s, monolithic_s=0))
    results.update(controls(128, timeout_s))
    results.update(cross_checks())
    results["total_cpu_s"] = round(time.process_time() - t0, 2)
    print(json.dumps(results, indent=1))
