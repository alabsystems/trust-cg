"""z3 evidence for the division-free I128 MulOverflow expansions.

The expansions are the SAME functions the sweeps run (lir_model.u_core / umulo_new /
smulo_new); only the op backend changes.

  int W     : full-width proof in integer arithmetic. IntOps gives each LIR op its exact
              modular semantics over Ints in [0, 2^w) (Imul = x*y mod 2^W, Trunc = mod 2^H,
              Ushr 64 = div 2^H, Icmp slt = compare after sign interpretation, ...).
              Query: exists (a, b) in range with flag != spec  -> expect unsat.
  bv W      : direct bit-vector query (lir_model.Z3Ops) with z3's bit-blaster.
  mutant W M: the same query for a mutant -> expect sat; the model is replayed on
              lir_model.Conc(W) to confirm a real counterexample.
  lemmas    : the structured signed route at W = 128 (core lemma + sign reduction).

usage: z3_proofs.py int|bv|mutant|lemmas W [u|s] [mutant] [timeout_s]
"""
import json
import sys
import time

import z3

from lir_model import Conc, Z3Ops, smulo_new, umulo_new


class IntOps:
    def __init__(self, W):
        self.W, self.H = W, W // 2
        self.MW, self.MH = 1 << W, 1 << (W // 2)

    def _sx(self, x, w):
        return z3.If(x >= (1 << (w - 1)), x - (1 << w), x)

    def imul_w(self, x, y):
        return (x * y) % self.MW

    def ineg_w(self, x):
        return (-x) % self.MW

    def trunc(self, x):
        return x % self.MH

    def hi(self, x):
        return (x / self.MH) % self.MH

    def iadd_h(self, x, y):
        return (x + y) % self.MH

    def bor_h(self, x, y):
        raise NotImplementedError("no bitwise or on Int; the t_or mutant is bv-only")

    def checked_umul_h(self, x, y):
        p = x * y
        return p % self.MH, p >= self.MH

    def checked_smul_h(self, x, y):
        p = self._sx(x, self.H) * self._sx(y, self.H)
        lim = 1 << (self.H - 1)
        return p % self.MH, z3.Not(z3.And(p >= -lim, p < lim))

    def ult_h(self, x, y):
        return x < y

    def ule_h(self, x, y):
        return x <= y

    def slt_h(self, x, y):
        return self._sx(x, self.H) < self._sx(y, self.H)

    def ne_h(self, x, k):
        return x != k

    def slt_w(self, x, k):
        return self._sx(x, self.W) < k

    def ne_w(self, x, k):
        return x != k

    def eq_w(self, x, k):
        return x == k

    def select(self, c, x, y):
        return z3.If(c, x, y)

    def band(self, p, q):
        return z3.And(p, q)

    def bor(self, p, q):
        return z3.Or(p, q)

    def bxor(self, p, q):
        return z3.Xor(p, q)

    def bnot(self, p):
        return z3.Not(p)

    def spec_u(self, a, b):
        return a * b >= self.MW

    def spec_s(self, a, b):
        p = self._sx(a, self.W) * self._sx(b, self.W)
        lim = 1 << (self.W - 1)
        return z3.Not(z3.And(p >= -lim, p < lim))


def check(solver, timeout_s):
    solver.set("timeout", int(timeout_s * 1000))
    t0 = time.process_time()
    r = solver.check()
    return str(r), round(time.process_time() - t0, 2)


def int_query(W, kind, mutant=None):
    o = IntOps(W)
    a, b = z3.Ints("a b")
    s = z3.Solver()
    s.add(a >= 0, a < o.MW, b >= 0, b < o.MW)
    if kind == "u":
        r, f = umulo_new(o, a, b, mutant)
        spec = o.spec_u(a, b)
    else:
        r, f = smulo_new(o, a, b, mutant)
        spec = o.spec_s(a, b)
    s.add(f != spec)
    return s, (a, b)


def bv_query(W, kind, mutant=None):
    o = Z3Ops(W)
    a, b = z3.BitVecs("a b", W)
    s = z3.Solver()
    if kind == "u":
        r, f = umulo_new(o, a, b, mutant)
        spec = o.spec_u(a, b)
    else:
        r, f = smulo_new(o, a, b, mutant)
        spec = o.spec_s(a, b)
    s.add(f != spec)
    return s, (a, b)


def replay(W, kind, mutant, av, bv):
    c = Conc(W)
    fn = umulo_new if kind == "u" else smulo_new
    spec = c.spec_u if kind == "u" else c.spec_s
    _, f_mut = fn(c, av, bv, mutant)
    _, f_new = fn(c, av, bv)
    return {"a": hex(av), "b": hex(bv), "mutant_flag": bool(f_mut), "new_flag": bool(f_new),
            "true_overflow": spec(av, bv),
            "real_counterexample": bool(f_mut) != spec(av, bv) and bool(f_new) == spec(av, bv)}


def lemmas(timeout_s):
    """Structured signed route at W = 128, each piece its own query.

    L1 (core): for x, y in [0, 2^128) and p = x*y mod 2^128, u_core(x, y, p) <=> x*y >= 2^128.
        This is exactly the `int 128 u` theorem (umulo_new passes p = Imul(x, y)).
    L2 (magnitude product): with ua = Select(a<0, -a, a) and ub likewise (as LIR patterns),
        ua*ub = |sx(a)*sx(b)| and pu = Select(neg, -r, r) = ua*ub mod 2^128.
    L3 (sign reduction): with N = |sx(a)*sx(b)| abstracted, ou := N >= 2^128 (by L1+L2),
        ou | ((r <s 0) xor neg) & r != 0  <=>  sx(a)*sx(b) out of i128 range.
    """
    W = 128
    o = IntOps(W)
    M = 1 << W
    out = {}
    a, b = z3.Ints("a b")
    dom = [a >= 0, a < M, b >= 0, b < M]
    sa, sb = o.slt_w(a, 0), o.slt_w(b, 0)
    ua = o.select(sa, o.ineg_w(a), a)
    ub = o.select(sb, o.ineg_w(b), b)
    va, vb = o._sx(a, W), o._sx(b, W)
    P = va * vb
    absP = z3.If(P >= 0, P, -P)
    r = o.imul_w(a, b)
    neg = o.bxor(sa, sb)
    pu = o.select(neg, o.ineg_w(r), r)
    # L2, split by the four sign cases; in each case ua/ub/va/vb are the explicit linear
    # terms the LIR ops compute there (Ineg of a negative pattern a is M - a).
    for ca in (False, True):
        for cb in (False, True):
            ua_c = (M - a) if ca else a
            ub_c = (M - b) if cb else b
            va_c = (a - M) if ca else a
            vb_c = (b - M) if cb else b
            P_c = va_c * vb_c
            absP_c = z3.If(P_c >= 0, P_c, -P_c)
            r_c = (a * b) % M
            pu_c = ((-r_c) % M) if (ca != cb) else r_c
            s = z3.Solver()
            s.add(*dom)
            s.add(a >= M // 2 if ca else a < M // 2, b >= M // 2 if cb else b < M // 2)
            # the case's terms are what the LIR ops compute in this case
            s.add(z3.Not(z3.And(ua == ua_c, ub == ub_c, va == va_c, vb == vb_c, pu == pu_c,
                                ua_c * ub_c == absP_c, pu_c == (ua_c * ub_c) % M,
                                r_c == P_c % M)))
            out[f"L2_magnitude_product[a<0={ca},b<0={cb}]"] = check(s, timeout_s)

    # L3 with the product abstracted: Pv is any integer with the sign facts of va*vb.
    Pv = z3.Int("Pv")
    s = z3.Solver()
    s.add(*dom)
    sign_facts = [
        z3.Implies(Pv > 0, z3.Not(neg)), z3.Implies(Pv < 0, neg),
        (Pv == 0) == z3.Or(va == 0, vb == 0),
        z3.Implies(z3.Or(va == 0, vb == 0), Pv == 0),
    ]
    s.add(*sign_facts)
    rr = Pv % M
    Nv = z3.If(Pv >= 0, Pv, -Pv)
    ou = Nv >= M
    rneg = o.slt_w(rr, 0)
    flag = z3.Or(ou, z3.And(z3.Xor(rneg, neg), rr != 0))
    lim = 1 << (W - 1)
    spec = z3.Not(z3.And(Pv >= -lim, Pv < lim))
    s.add(flag != spec)
    out["L3_sign_reduction(product_abstracted)"] = check(s, timeout_s)
    # the sign facts used in L3 hold for the real product
    s = z3.Solver()
    s.add(*dom)
    s.add(z3.Not(z3.And(*[z3.substitute(f, (Pv, P)) for f in sign_facts])))
    out["L3_sign_facts_hold_for_va*vb"] = check(s, timeout_s)
    return out


if __name__ == "__main__":
    mode, W = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 128
    kind = sys.argv[3] if len(sys.argv) > 3 else "u"
    if mode == "lemmas":
        tmo = float(sys.argv[3]) if len(sys.argv) > 3 else 60
        print(json.dumps({"mode": "lemmas", "W": 128, "results": lemmas(tmo)}, indent=1))
        sys.exit(0)
    if mode in ("int", "bv"):
        tmo = float(sys.argv[4]) if len(sys.argv) > 4 else 60
        s, _ = (int_query if mode == "int" else bv_query)(W, kind)
        res, cpu = check(s, tmo)
        print(json.dumps({"mode": mode, "W": W, "kind": kind, "result": res, "cpu_s": cpu,
                          "z3": z3.get_version_string()}))
    elif mode == "mutant":
        m = sys.argv[4]
        tmo = float(sys.argv[5]) if len(sys.argv) > 5 else 60
        enc = sys.argv[6] if len(sys.argv) > 6 else "bv"
        s, (a, b) = (int_query if enc == "int" else bv_query)(W, kind, m)
        res, cpu = check(s, tmo)
        out = {"mode": "mutant", "enc": enc, "W": W, "kind": kind, "mutant": m, "result": res,
               "cpu_s": cpu}
        if res == "sat":
            mdl = s.model()
            av = mdl.eval(a, model_completion=True)
            bv_ = mdl.eval(b, model_completion=True)
            out["replay"] = replay(W, kind, m, av.as_long(), bv_.as_long())
        print(json.dumps(out))
