"""Width-generic model of the LIR ops the division-free I128 MulOverflow expansion uses.

The same expansion functions run on two op backends:
  * Conc(W): concrete Python ints (exhaustive sweeps), W = 2*H.
  * Z3Ops(W): z3 bit-vectors (solver proof), W = 128 is the real width.

Every method is one LIR opcode at its stated type; W stands for I128 and H for I64.
  imul_w        Imul       (I128, wrapping low W bits)
  ineg_w        Ineg       (I128)
  trunc         Trunc{I64} (I128 -> I64, low limb)
  hi            Trunc{I64}(Ushr(x, Iconst128 64))  (two ops: the high limb)
  iadd_h        Iadd       (I64, wrapping)
  checked_umul_h CheckedUmul (I64) -> [low product, high-half != 0]
  checked_smul_h CheckedSmul (I64) -> [low product, signed overflow]  (mutants only)
  ult_h/slt_h/ne_h  Icmp (I64)
  slt_w/ne_w    Icmp (I128)
  select        Select (I128)
  band/bor/bxor Band/Bor/Bxor on B1
"""


class Conc:
    def __init__(self, W):
        assert W % 2 == 0
        self.W, self.H = W, W // 2
        self.MW, self.MH = (1 << W) - 1, (1 << (W // 2)) - 1

    def sx(self, x, w):
        return x - (1 << w) if x >> (w - 1) else x

    def imul_w(self, x, y):
        return (x * y) & self.MW

    def ineg_w(self, x):
        return (-x) & self.MW

    def trunc(self, x):
        return x & self.MH

    def hi(self, x):
        return (x >> self.H) & self.MH

    def iadd_h(self, x, y):
        return (x + y) & self.MH

    def bor_h(self, x, y):
        return x | y

    def checked_umul_h(self, x, y):
        p = x * y
        return p & self.MH, (p >> self.H) != 0

    def checked_smul_h(self, x, y):
        p = self.sx(x, self.H) * self.sx(y, self.H)
        lim = 1 << (self.H - 1)
        return p & self.MH, not (-lim <= p < lim)

    def ult_h(self, x, y):
        return x < y

    def ule_h(self, x, y):
        return x <= y

    def slt_h(self, x, y):
        return self.sx(x, self.H) < self.sx(y, self.H)

    def ne_h(self, x, k):
        return x != k

    def slt_w(self, x, k):
        return self.sx(x, self.W) < self.sx(k, self.W)

    def ne_w(self, x, k):
        return x != k

    def select(self, c, x, y):
        return x if c else y

    def band(self, p, q):
        return p and q

    def bor(self, p, q):
        return p or q

    def bxor(self, p, q):
        return p != q

    def bnot(self, p):
        return not p

    # -- the current (division-based) expansion's extra ops --
    def udiv_w(self, x, y):
        assert y != 0
        return x // y

    def sdiv_w(self, x, y):
        sx, sy = self.sx(x, self.W), self.sx(y, self.W)
        assert sy != 0 and not (sx == -(1 << (self.W - 1)) and sy == -1)
        q = abs(sx) // abs(sy)
        if (sx < 0) != (sy < 0):
            q = -q
        return q & self.MW

    def eq_w(self, x, k):
        return x == k

    # -- specifications: the true (unbounded) product --
    def spec_u(self, a, b):
        return a * b >= (1 << self.W)

    def spec_s(self, a, b):
        p = self.sx(a, self.W) * self.sx(b, self.W)
        lim = 1 << (self.W - 1)
        return not (-lim <= p < lim)


class Z3Ops:
    def __init__(self, W):
        import z3

        self.z3 = z3
        self.W, self.H = W, W // 2

    def c(self, v, w):
        return self.z3.BitVecVal(v, w)

    def imul_w(self, x, y):
        return x * y

    def ineg_w(self, x):
        return -x

    def trunc(self, x):
        return self.z3.Extract(self.H - 1, 0, x)

    def hi(self, x):
        # Trunc(Ushr(x, H)): spelled with the shift so the encoding is the LIR pair.
        return self.z3.Extract(self.H - 1, 0, self.z3.LShR(x, self.H))

    def iadd_h(self, x, y):
        return x + y

    def bor_h(self, x, y):
        return x | y

    def checked_umul_h(self, x, y):
        z3 = self.z3
        p = z3.ZeroExt(self.H, x) * z3.ZeroExt(self.H, y)
        return z3.Extract(self.H - 1, 0, p), z3.Extract(2 * self.H - 1, self.H, p) != 0

    def checked_smul_h(self, x, y):
        z3 = self.z3
        p = z3.SignExt(self.H, x) * z3.SignExt(self.H, y)
        lo = z3.Extract(self.H - 1, 0, p)
        return lo, p != z3.SignExt(self.H, lo)

    def ult_h(self, x, y):
        return self.z3.ULT(x, y)

    def ule_h(self, x, y):
        return self.z3.ULE(x, y)

    def slt_h(self, x, y):
        return x < y

    def ne_h(self, x, k):
        return x != self.c(k, self.H)

    def slt_w(self, x, k):
        return x < self.c(k, self.W)

    def ne_w(self, x, k):
        return x != self.c(k, self.W)

    def eq_w(self, x, k):
        return x == self.c(k, self.W)

    def select(self, c, x, y):
        return self.z3.If(c, x, y)

    def band(self, p, q):
        return self.z3.And(p, q)

    def bor(self, p, q):
        return self.z3.Or(p, q)

    def bxor(self, p, q):
        return self.z3.Xor(p, q)

    def bnot(self, p):
        return self.z3.Not(p)

    def udiv_w(self, x, y):
        return self.z3.UDiv(x, y)

    def sdiv_w(self, x, y):
        return x / y

    def spec_u(self, a, b):
        z3 = self.z3
        p = z3.ZeroExt(self.W, a) * z3.ZeroExt(self.W, b)
        return z3.Extract(2 * self.W - 1, self.W, p) != 0

    def spec_s(self, a, b):
        z3 = self.z3
        p = z3.SignExt(self.W, a) * z3.SignExt(self.W, b)
        return p != z3.SignExt(self.W, z3.Extract(self.W - 1, 0, p))


# ---------------------------------------------------------------------------
# Expansions. `m` selects a mutant (None = the proposed expansion).
# ---------------------------------------------------------------------------


def u_core(o, x, y, p, m=None):
    """Overflow flag of the unsigned W-bit product x*y, given p = x*y mod 2^W.

    LLVM's ExpandIntRes_XMULO(UMULO) shape, with the carry read off p's high limb:
      ovf = (x1!=0 & y1!=0) | hi(x1*y0)!=0 | hi(x0*y1)!=0 | (p1 <u t),
      t   = lo(x1*y0) + lo(x0*y1)  (wrapping H-bit add).
    """
    x0, x1 = o.trunc(x), o.hi(x)
    y0, y1 = o.trunc(y), o.hi(y)
    p1 = o.hi(p)
    mul = o.checked_smul_h if m == "smul_cross" else o.checked_umul_h
    m1, o1 = mul(x1, y0)
    m2, o2 = mul(x0, y1)
    t = o.bor_h(m1, m2) if m == "t_or" else o.iadd_h(m1, m2)
    if m == "carry_signed":
        c = o.slt_h(p1, t)
    elif m == "carry_ule":
        c = o.ule_h(p1, t)
    else:
        c = o.ult_h(p1, t)
    both = o.band(o.ne_h(x1, 0), o.ne_h(y1, 0))
    terms = {"o1": o1, "o2": o2, "c": c, "both": both}
    drop = {"drop_carry": "c", "drop_both": "both", "drop_o1": "o1", "drop_o2": "o2"}.get(m)
    acc = None
    for k in ("o1", "o2", "c", "both"):
        if k == drop:
            continue
        acc = terms[k] if acc is None else o.bor(acc, terms[k])
    return acc


def umulo_new(o, a, b, m=None):
    r = o.imul_w(a, b)
    return r, u_core(o, a, b, r, m)


def smulo_new(o, a, b, m=None):
    """Signed: unsigned core on the magnitudes, plus a sign check on the wrapped product.

      ovf = umulo(|a|,|b|) | ((r <s 0) xor neg) & (r != 0),   neg = (a<s0) xor (b<s0).
    The core's carry term reads pu = neg ? -r : r, which is |a|*|b| mod 2^W.
    """
    r = o.imul_w(a, b)
    if m == "spelling_sign_hi":  # NOT a mutant: signs read on the I64 high limb
        sa, sb = o.slt_h(o.hi(a), 0), o.slt_h(o.hi(b), 0)
    else:
        sa, sb = o.slt_w(a, 0), o.slt_w(b, 0)
    if m == "unsigned_core_raw":  # signed/unsigned swap: core on the raw bit patterns
        ua, ub = a, b
    else:
        ua = o.select(sa, o.ineg_w(a), a)
        ub = o.select(sb, o.ineg_w(b), b)
    neg = o.bor(sa, sb) if m == "neg_or" else o.bxor(sa, sb)
    pu = r if m in ("pu_eq_r", "unsigned_core_raw") else o.select(neg, o.ineg_w(r), r)
    ou = u_core(o, ua, ub, pu)
    rneg = o.slt_h(o.hi(r), 0) if m == "spelling_sign_hi" else o.slt_w(r, 0)
    rnz = o.ne_w(r, 0)
    bad = o.bxor(rneg, neg) if m == "no_zero_guard" else o.band(o.bxor(rneg, neg), rnz)
    if m == "no_sign_check":
        return r, ou
    if m == "no_ou":
        return r, bad
    return r, o.bor(ou, bad)


def umulo_div(o, a, b):
    """The CURRENT unsigned expansion (adapter build_u128_mul_overflow)."""
    r = o.imul_w(a, b)
    safe_a = o.select(o.eq_w(a, 0), 1 if isinstance(o, Conc) else o.c(1, o.W), a)
    q = o.udiv_w(r, safe_a)
    return r, o.band(o.ne_w(a, 0), o.bnot(q == b) if isinstance(o, Conc) else q != b)


def smulo_div(o, a, b):
    """The CURRENT signed expansion (adapter build_i128_signed_mul_overflow)."""
    W = o.W
    minv = 1 << (W - 1)
    r = o.imul_w(a, b)
    one = 1 if isinstance(o, Conc) else o.c(1, W)
    min_neg1 = o.band(o.eq_w(a, minv), o.eq_w(b, (1 << W) - 1))
    avoid = o.bor(o.eq_w(b, 0), min_neg1)
    safe_b = o.select(avoid, one, b)
    q = o.sdiv_w(r, safe_b)
    q_ne_a = (q != a)
    return r, o.bor(o.band(o.ne_w(b, 0), q_ne_a), min_neg1)


U_MUTANTS = ["drop_carry", "drop_both", "drop_o1", "drop_o2", "carry_signed", "carry_ule",
             "smul_cross", "t_or"]
S_MUTANTS = ["no_zero_guard", "no_sign_check", "no_ou", "neg_or", "pu_eq_r",
             "unsigned_core_raw"]
