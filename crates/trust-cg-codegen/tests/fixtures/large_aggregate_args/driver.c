/* C oracle for the by-reference composite argument corpora (corpus.trust_ir,
 * tail.trust_ir, variadic.trust_ir). AAPCS64 B.4 passes a composite over 16
 * bytes that is not an HFA/HVA as a pointer to a copy the caller allocates,
 * and the callee owns that copy: every c_* callee below digests the bytes it
 * received and then writes every by-reference parameter, as C may. The
 * trust-cg functions store the aggregates they passed into `out` after their
 * calls; this driver requires those bytes unchanged and every digest equal to
 * the digest of the original values. Prints one line per shape, then a
 * summary; exits nonzero on any mismatch. */
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef struct { int64_t q0, q1, q2, q3; } Quad;
typedef struct { int64_t t0, t1, t2; } Tri;
typedef struct { int32_t o0, o1, o2, o3, o4; } Odd;
typedef struct { __int128 w0; int64_t w1; } Wide;
typedef struct { int64_t h[40]; } Huge;
typedef struct { double d0, d1, d2, d3; } Hfa;
typedef struct { Quad a; Tri t; Odd o; Wide w; Hfa h; } MixedOut;
typedef struct { int64_t f[5]; } Five;
typedef struct { int64_t g[9000]; } Giant;
typedef struct { int64_t g[128]; } K;
_Static_assert(sizeof(Five) == 40 && sizeof(Giant) == 72000 && sizeof(K) == 1024, "big");
_Static_assert(sizeof(Quad) == 32 && sizeof(Tri) == 24 && sizeof(Odd) == 20, "sizes");
_Static_assert(sizeof(Wide) == 32 && _Alignof(Wide) == 16, "wide");
_Static_assert(sizeof(Huge) == 320 && sizeof(Hfa) == 32, "huge/hfa");
_Static_assert(offsetof(MixedOut, t) == 32 && offsetof(MixedOut, o) == 56, "mixed t/o");
_Static_assert(offsetof(MixedOut, w) == 80 && offsetof(MixedOut, h) == 112, "mixed w/h");

/* Digest of the bytes a callee received (the same function models it). */
static uint64_t mix(uint64_t h, uint64_t x) {
  h ^= x;
  h *= 0x100000001b3ULL;
  return h ^ (h >> 29);
}
static uint64_t dbits(double d) { uint64_t u; memcpy(&u, &d, 8); return u; }
static uint64_t d_quad(uint64_t h, const Quad *b) {
  h = mix(h, (uint64_t)b->q0);
  h = mix(h, (uint64_t)b->q1);
  h = mix(h, (uint64_t)b->q2);
  return mix(h, (uint64_t)b->q3);
}
static uint64_t d_tri(uint64_t h, const Tri *t) {
  return mix(mix(mix(h, (uint64_t)t->t0), (uint64_t)t->t1), (uint64_t)t->t2);
}
static uint64_t d_odd(uint64_t h, const Odd *o) {
  h = mix(h, (uint32_t)o->o0);
  h = mix(h, (uint32_t)o->o1);
  h = mix(h, (uint32_t)o->o2);
  h = mix(h, (uint32_t)o->o3);
  return mix(h, (uint32_t)o->o4);
}
static uint64_t d_wide(uint64_t h, const Wide *w) {
  unsigned __int128 u = (unsigned __int128)w->w0;
  h = mix(h, (uint64_t)u);
  h = mix(h, (uint64_t)(u >> 64));
  return mix(h, (uint64_t)w->w1);
}
static uint64_t d_huge(uint64_t h, const Huge *b) {
  for (int i = 0; i < 40; i++) h = mix(h, (uint64_t)b->h[i]);
  return h;
}
static uint64_t d_hfa(uint64_t h, const Hfa *f) {
  h = mix(h, dbits(f->d0));
  h = mix(h, dbits(f->d1));
  h = mix(h, dbits(f->d2));
  return mix(h, dbits(f->d3));
}

/* Mixed into a digest when a parameter's copy is misaligned for its type, or
 * when two by-reference parameters share one address. */
#define SENTINEL_ALIGN 0xa119eULL
#define SENTINEL_ALIAS 0xa11a5ULL
#define ALIGNED(p) ((((uintptr_t)(p)) % _Alignof(__typeof__(*(p)))) == 0)
#define ESCAPE(p) __asm__ volatile("" : : "r"(p) : "memory")

/* Write every byte of a by-reference parameter's copy. */
static void clobber_quad(Quad *b, int64_t v) {
  b->q0 = ~b->q0;
  b->q1 = v;
  b->q2 = v ^ 0x5555;
  b->q3 = -1;
  ESCAPE(b);
}
static void clobber_tri(Tri *t) { t->t0 = -7; t->t1 = ~t->t1; t->t2 = 0; ESCAPE(t); }
static void clobber_odd(Odd *o) {
  o->o0 = -1; o->o1 = 0x7777; o->o2 = ~o->o2; o->o3 = 3; o->o4 = INT32_MIN;
  ESCAPE(o);
}
static void clobber_wide(Wide *w) { w->w0 = ~w->w0; w->w1 = 0x1234; ESCAPE(w); }
static void clobber_hfa(Hfa *f) { f->d0 = -1.0; f->d3 = 99.0; ESCAPE(f); }

/* ---- C callees: digest what was received, then write the copies. ---- */

__attribute__((noinline)) int64_t c_mut_quad(Quad b, int64_t v) {
  uint64_t h = d_quad(mix(1, (uint64_t)v), &b);
  if (!ALIGNED(&b)) h = mix(h, SENTINEL_ALIGN);
  clobber_quad(&b, v);
  return (int64_t)h;
}

__attribute__((noinline)) int64_t c_mut_two(Quad a, Quad b, int64_t v) {
  uint64_t h = d_quad(mix(2, (uint64_t)v), &a);
  if (&a == &b) h = mix(h, SENTINEL_ALIAS);
  clobber_quad(&a, v);
  h = d_quad(h, &b);
  if (!ALIGNED(&a) || !ALIGNED(&b)) h = mix(h, SENTINEL_ALIGN);
  clobber_quad(&b, v + 1);
  return (int64_t)h;
}

__attribute__((noinline)) int64_t c_mut_mixed(int64_t f0, Quad a, int64_t f1, Tri t, double d,
                                              int64_t f2, Odd o, Hfa hfa, int64_t f3, Wide w,
                                              Quad a2, int64_t v) {
  uint64_t h = mix(4, (uint64_t)v);
  h = mix(h, (uint64_t)f0);
  h = d_quad(h, &a);
  h = mix(h, (uint64_t)f1);
  h = d_tri(h, &t);
  h = mix(h, dbits(d));
  h = mix(h, (uint64_t)f2);
  h = d_odd(h, &o);
  h = d_hfa(h, &hfa);
  h = mix(h, (uint64_t)f3);
  h = d_wide(h, &w);
  h = d_quad(h, &a2);
  if (&a == &a2) h = mix(h, SENTINEL_ALIAS);
  if (!ALIGNED(&a) || !ALIGNED(&t) || !ALIGNED(&o) || !ALIGNED(&w) || !ALIGNED(&a2))
    h = mix(h, SENTINEL_ALIGN);
  clobber_quad(&a, v);
  clobber_tri(&t);
  clobber_odd(&o);
  clobber_hfa(&hfa);
  clobber_wide(&w);
  clobber_quad(&a2, ~v);
  return (int64_t)h;
}

__attribute__((noinline)) int64_t c_mut_huge(Huge b, int64_t v) {
  uint64_t h = d_huge(mix(5, (uint64_t)v), &b);
  if (!ALIGNED(&b)) h = mix(h, SENTINEL_ALIGN);
  for (int i = 0; i < 40; i++) b.h[i] = ~b.h[i] ^ v;
  ESCAPE(&b);
  return (int64_t)h;
}

__attribute__((noinline)) Quad c_mut_ret(Quad b, int64_t v) {
  uint64_t h = d_quad(mix(6, (uint64_t)v), &b);
  if (!ALIGNED(&b)) h = mix(h, SENTINEL_ALIGN);
  Quad r = {(int64_t)h, b.q1, b.q2, b.q3 ^ v};
  clobber_quad(&b, v);
  return r;
}

__attribute__((noinline)) int64_t c_mut_spill(int64_t a0, int64_t a1, int64_t a2, int64_t a3,
                                              int64_t a4, int64_t a5, int64_t a6, int64_t a7,
                                              Quad b, int64_t v) {
  uint64_t h = mix(3, (uint64_t)v);
  const int64_t lead[8] = {a0, a1, a2, a3, a4, a5, a6, a7};
  for (int i = 0; i < 8; i++) h = mix(h, (uint64_t)lead[i]);
  h = d_quad(h, &b);
  if (!ALIGNED(&b)) h = mix(h, SENTINEL_ALIGN);
  clobber_quad(&b, v);
  return (int64_t)h;
}

__attribute__((noinline)) int64_t c_scalar(int64_t v) { return v * 3 + 1; }

static uint64_t d_words(uint64_t h, const int64_t *w, int n) {
  for (int i = 0; i < n; i++) h = mix(h, (uint64_t)w[i]);
  return h;
}
static void clobber_words(int64_t *w, int n, int64_t v) {
  for (int i = 0; i < n; i++) w[i] = ~w[i] ^ v;
  ESCAPE(w);
}

__attribute__((noinline)) int64_t c_mut_five(Five b, int64_t v) {
  uint64_t h = d_words(mix(10, (uint64_t)v), b.f, 5);
  if (!ALIGNED(&b)) h = mix(h, SENTINEL_ALIGN);
  clobber_words(b.f, 5, v);
  return (int64_t)h;
}

/* Where the caller's giant source lives, so a callee can tell whether it was
 * handed that storage instead of a copy. */
static const char *giant_lo, *giant_hi;
#define SENTINEL_SOURCE 0x5a5eULL

__attribute__((noinline)) int64_t c_mut_giant(Giant b, int64_t v) {
  uint64_t h = d_words(mix(11, (uint64_t)v), b.g, 9000);
  if (!ALIGNED(&b)) h = mix(h, SENTINEL_ALIGN);
  if ((const char *)&b < giant_hi && (const char *)&b + sizeof b > giant_lo)
    h = mix(h, SENTINEL_SOURCE);
  clobber_words(b.g, 9000, v);
  return (int64_t)h;
}

__attribute__((noinline)) int64_t c_mut_k(K b, int64_t v) {
  uint64_t h = d_words(mix(12, (uint64_t)v), b.g, 128);
  if (!ALIGNED(&b)) h = mix(h, SENTINEL_ALIGN);
  clobber_words(b.g, 128, v);
  return (int64_t)h;
}

/* AAPCS64 passes each anonymous Quad as a pointer to the caller's copy;
 * reading that GPR slot as `Quad *` reaches the copy itself. */
__attribute__((noinline)) int64_t c_var_mut(int64_t v, ...) {
  va_list ap;
  va_start(ap, v);
  Quad *first = va_arg(ap, Quad *);
  Quad *second = va_arg(ap, Quad *);
  va_end(ap);
  uint64_t h = d_quad(mix(7, (uint64_t)v), first);
  if (first == second) h = mix(h, SENTINEL_ALIAS);
  clobber_quad(first, v);
  h = d_quad(h, second);
  if (!ALIGNED(first) || !ALIGNED(second)) h = mix(h, SENTINEL_ALIGN);
  clobber_quad(second, v + 1);
  return (int64_t)h;
}

__attribute__((noinline)) int64_t c_var_sum(int64_t v, ...) {
  va_list ap;
  va_start(ap, v);
  Quad a = va_arg(ap, Quad);
  Tri t = va_arg(ap, Tri);
  Quad c = va_arg(ap, Quad);
  va_end(ap);
  return (int64_t)d_quad(d_tri(d_quad(mix(8, (uint64_t)v), &a), &t), &c);
}

/* ---- trust-cg functions ---- */

extern int64_t param_pass(Quad *, Quad, int64_t);
extern int64_t const_pass(Quad *, int64_t);
extern int64_t load_pass(Quad *, const Quad *, int64_t);
extern int64_t twice_pass(Quad *, Quad, int64_t);
extern int64_t spill_pass(Quad *, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t,
                          int64_t, Quad, int64_t);
extern int64_t mixed_pass(MixedOut *, Quad, Tri, Odd, Wide, Hfa, int64_t);
extern int64_t huge_pass(Huge *, Huge, int64_t);
extern int64_t indirect_pass(Quad *, int64_t (*)(Quad, int64_t), Quad, int64_t);
extern int64_t sret_pass(Quad *, Quad, int64_t);
extern int64_t loop_pass(Quad *, Quad, int64_t);
extern int64_t cg_writes_param(Quad *, Quad, int64_t);
extern int64_t cg_to_cg(Quad *, Quad, int64_t);
extern int64_t phi_pass(Quad *, Quad, Quad, int64_t, int64_t);
extern int64_t tail_pass(Quad, int64_t);
extern int64_t tail_const(int64_t);
extern int64_t tail_huge(Huge, int64_t);
extern int64_t tail_scalar(int64_t);
extern int64_t var_mut_pass(Quad *, Quad, int64_t);
extern int64_t var_value_pass(Quad *, Quad, Tri, int64_t);
extern int64_t five_pass(Five *, Five, int64_t);
extern int64_t giant_pass(Giant *, const Giant *, int64_t);
extern int64_t giant_load_pass(const Giant *, int64_t);
extern int64_t many_pass(K *, const K *, int64_t);
extern int64_t k_param_pass(K *, K, int64_t);
extern int64_t k_block_pass(K *, const K *, int64_t);
typedef struct { int64_t g[33]; } M2;
extern int64_t var_param_k(K *, K, int64_t);
extern int64_t var_block_k(K *, const K *, int64_t);
extern int64_t var_param_m2(M2 *, M2, int64_t);

/* AAPCS64 passes an anonymous K or M2 as a pointer to the caller's copy. */
__attribute__((noinline)) int64_t c_var_k(int64_t v, ...) {
  va_list ap;
  va_start(ap, v);
  K *p = va_arg(ap, K *);
  va_end(ap);
  uint64_t h = d_words(mix(13, (uint64_t)v), p->g, 128);
  if (!ALIGNED(p)) h = mix(h, SENTINEL_ALIGN);
  clobber_words(p->g, 128, v);
  return (int64_t)h;
}
__attribute__((noinline)) int64_t c_var_m2(int64_t v, ...) {
  va_list ap;
  va_start(ap, v);
  M2 *p = va_arg(ap, M2 *);
  va_end(ap);
  uint64_t h = d_words(mix(14, (uint64_t)v), p->g, 33);
  if (!ALIGNED(p)) h = mix(h, SENTINEL_ALIGN);
  clobber_words(p->g, 33, v);
  return (int64_t)h;
}

/* ---- checking ---- */

static int shape_checks, shape_failures, total_checks, total_failures, failed_shapes;

static void check_bits(const char *shape, const char *field, int input, uint64_t got,
                       uint64_t want) {
  shape_checks++;
  if (got != want) {
    shape_failures++;
    if (shape_failures <= 4)
      printf("  %s input %d %s: got 0x%016llx want 0x%016llx\n", shape, input, field,
             (unsigned long long)got, (unsigned long long)want);
  }
}
static void check_quad(const char *shape, const char *what, int input, const Quad *got,
                       const Quad *want) {
  char field[64];
  const int64_t *g = &got->q0, *w = &want->q0;
  for (int i = 0; i < 4; i++) {
    snprintf(field, sizeof field, "%s.q%d", what, i);
    check_bits(shape, field, input, (uint64_t)g[i], (uint64_t)w[i]);
  }
}
static void check_tri(const char *shape, int input, const Tri *got, const Tri *want) {
  check_bits(shape, "t.t0", input, (uint64_t)got->t0, (uint64_t)want->t0);
  check_bits(shape, "t.t1", input, (uint64_t)got->t1, (uint64_t)want->t1);
  check_bits(shape, "t.t2", input, (uint64_t)got->t2, (uint64_t)want->t2);
}
static void check_odd(const char *shape, int input, const Odd *got, const Odd *want) {
  const int32_t *g = &got->o0, *w = &want->o0;
  for (int i = 0; i < 5; i++) check_bits(shape, "o", input, (uint32_t)g[i], (uint32_t)w[i]);
}
static void check_wide(const char *shape, int input, const Wide *got, const Wide *want) {
  unsigned __int128 g = (unsigned __int128)got->w0, w = (unsigned __int128)want->w0;
  check_bits(shape, "w.w0.lo", input, (uint64_t)g, (uint64_t)w);
  check_bits(shape, "w.w0.hi", input, (uint64_t)(g >> 64), (uint64_t)(w >> 64));
  check_bits(shape, "w.w1", input, (uint64_t)got->w1, (uint64_t)want->w1);
}
static void check_hfa(const char *shape, int input, const Hfa *got, const Hfa *want) {
  check_bits(shape, "h.d0", input, dbits(got->d0), dbits(want->d0));
  check_bits(shape, "h.d1", input, dbits(got->d1), dbits(want->d1));
  check_bits(shape, "h.d2", input, dbits(got->d2), dbits(want->d2));
  check_bits(shape, "h.d3", input, dbits(got->d3), dbits(want->d3));
}
static void check_huge(const char *shape, int input, const Huge *got, const Huge *want) {
  for (int i = 0; i < 40; i++) check_bits(shape, "huge", input, (uint64_t)got->h[i],
                                          (uint64_t)want->h[i]);
}
static void check_mem(const char *shape, const char *what, int input, const void *got,
                      const void *want, size_t n) {
  shape_checks++;
  if (memcmp(got, want, n) != 0) {
    shape_failures++;
    if (shape_failures <= 4) printf("  %s input %d %s: bytes differ\n", shape, input, what);
  }
}
static void end_shape(const char *shape) {
  printf("shape %s checks=%d failures=%d %s\n", shape, shape_checks, shape_failures,
         shape_failures ? "FAIL" : "ok");
  total_checks += shape_checks;
  total_failures += shape_failures;
  if (shape_failures) failed_shapes++;
  shape_checks = shape_failures = 0;
}

/* ---- inputs ---- */

#define NQ 3
static const Quad QUADS[NQ] = {
    {1, 2, 3, 4},
    {-5, INT64_MAX, 0x0123456789abcdefLL, INT64_MIN},
    {0, -1, 42, 0x5a5a5a5a5a5a5a5aLL},
};
static const int64_t VALUES[NQ] = {42, -9, INT64_MIN};
static const Tri TRIS[NQ] = {{10, 20, 30}, {-1, INT64_MIN, 7}, {0x1111, 0, -0x2222}};
static const Odd ODDS[NQ] = {{1, 2, 3, 4, 5}, {-1, INT32_MAX, INT32_MIN, 0, 9}, {7, 7, 7, 7, 7}};
static const Hfa HFAS[NQ] = {{1.5, -2.25, 3.0, 0.125}, {-0.0, 1e300, -1e-300, 42.0},
                             {3.14159, 2.71828, 1.41421, 1.73205}};
static const int64_t TRIPS[4] = {0, 1, 2, 5};

static Wide wide_at(int i) {
  Wide w;
  memset(&w, 0, sizeof w);
  w.w0 = ((__int128)(0x1000 + i) << 70) - 17 * (i + 1);
  w.w1 = -333 * (i + 1);
  return w;
}
static Huge huge_at(int i) {
  Huge b;
  for (int k = 0; k < 40; k++) b.h[k] = (int64_t)(0x0101010101010101ULL * (uint64_t)(k + 1)) ^ (i * 977);
  return b;
}
/* A C variable that the trust-cg function must not change, even though its
 * copy was passed to a callee that writes it. */
#define ORIGINAL(T, name, value) const T name##_want = (value); T name = name##_want

int main(void) {
  int in;

  for (in = 0; in < NQ * NQ; in++) {
    Quad b = QUADS[in % NQ], out;
    int64_t v = VALUES[in / NQ];
    int64_t r = param_pass(&out, b, v);
    check_bits("param_pass", "r", in, (uint64_t)r, d_quad(mix(1, (uint64_t)v), &b));
    check_quad("param_pass", "out", in, &out, &b);
  }
  end_shape("param_pass");

  for (in = 0; in < NQ; in++) {
    const Quad k = {101, -102, 103, -104};
    Quad out;
    int64_t v = VALUES[in];
    uint64_t r1 = d_quad(mix(1, (uint64_t)v), &k);
    int64_t r = const_pass(&out, v);
    check_bits("const_pass", "r", in, (uint64_t)r, d_quad(mix(1, r1), &k));
    check_quad("const_pass", "out", in, &out, &k);
  }
  end_shape("const_pass");

  for (in = 0; in < NQ * NQ; in++) {
    ORIGINAL(Quad, src, QUADS[in % NQ]);
    Quad out;
    int64_t v = VALUES[in / NQ];
    int64_t r = load_pass(&out, &src, v);
    check_bits("load_pass", "r", in, (uint64_t)r, d_quad(mix(1, (uint64_t)v), &src_want));
    check_quad("load_pass", "out", in, &out, &src_want);
    check_quad("load_pass", "src", in, &src, &src_want);
  }
  end_shape("load_pass");

  for (in = 0; in < NQ * NQ; in++) {
    Quad b = QUADS[in % NQ], out;
    int64_t v = VALUES[in / NQ];
    int64_t r = twice_pass(&out, b, v);
    check_bits("twice_pass", "r", in, (uint64_t)r, d_quad(d_quad(mix(2, (uint64_t)v), &b), &b));
    check_quad("twice_pass", "out", in, &out, &b);
  }
  end_shape("twice_pass");

  for (in = 0; in < NQ * NQ; in++) {
    Quad b = QUADS[in % NQ], out;
    int64_t v = VALUES[in / NQ];
    int64_t lead[8];
    uint64_t h = mix(3, (uint64_t)v);
    for (int i = 0; i < 8; i++) {
      lead[i] = (int64_t)(i + 1) * -1000003 + in;
      h = mix(h, (uint64_t)lead[i]);
    }
    int64_t r = spill_pass(&out, lead[0], lead[1], lead[2], lead[3], lead[4], lead[5], lead[6],
                           lead[7], b, v);
    check_bits("spill_pass", "r", in, (uint64_t)r, d_quad(h, &b));
    check_quad("spill_pass", "out", in, &out, &b);
  }
  end_shape("spill_pass");

  for (in = 0; in < NQ; in++) {
    Quad a = QUADS[in];
    Tri t = TRIS[in];
    Odd o = ODDS[in];
    Wide w = wide_at(in);
    Hfa f = HFAS[in];
    int64_t v = VALUES[in];
    MixedOut out;
    memset(&out, 0xee, sizeof out);
    int64_t r = mixed_pass(&out, a, t, o, w, f, v);
    uint64_t h = mix(4, (uint64_t)v);
    h = mix(h, 1);
    h = d_quad(h, &a);
    h = mix(h, 2);
    h = d_tri(h, &t);
    h = mix(h, dbits(2.5));
    h = mix(h, 3);
    h = d_odd(h, &o);
    h = d_hfa(h, &f);
    h = mix(h, 4);
    h = d_wide(h, &w);
    h = d_quad(h, &a);
    check_bits("mixed_pass", "r", in, (uint64_t)r, h);
    check_quad("mixed_pass", "a", in, &out.a, &a);
    check_tri("mixed_pass", in, &out.t, &t);
    check_odd("mixed_pass", in, &out.o, &o);
    check_wide("mixed_pass", in, &out.w, &w);
    check_hfa("mixed_pass", in, &out.h, &f);
  }
  end_shape("mixed_pass");

  for (in = 0; in < NQ; in++) {
    Huge b = huge_at(in), out;
    int64_t v = VALUES[in];
    int64_t r = huge_pass(&out, b, v);
    check_bits("huge_pass", "r", in, (uint64_t)r, d_huge(mix(5, (uint64_t)v), &b));
    check_huge("huge_pass", in, &out, &b);
  }
  end_shape("huge_pass");

  for (in = 0; in < NQ * NQ; in++) {
    Quad b = QUADS[in % NQ], out;
    int64_t v = VALUES[in / NQ];
    int64_t r = indirect_pass(&out, c_mut_quad, b, v);
    check_bits("indirect_pass", "r", in, (uint64_t)r, d_quad(mix(1, (uint64_t)v), &b));
    check_quad("indirect_pass", "out", in, &out, &b);
  }
  end_shape("indirect_pass");

  for (in = 0; in < NQ * NQ; in++) {
    Quad b = QUADS[in % NQ], out[2];
    int64_t v = VALUES[in / NQ];
    int64_t r = sret_pass(out, b, v);
    uint64_t h = d_quad(mix(6, (uint64_t)v), &b);
    Quad q = {(int64_t)h, b.q1, b.q2, b.q3 ^ v};
    check_bits("sret_pass", "r", in, (uint64_t)r, h);
    check_quad("sret_pass", "out", in, &out[0], &b);
    check_quad("sret_pass", "result", in, &out[1], &q);
  }
  end_shape("sret_pass");

  for (in = 0; in < NQ * 4; in++) {
    Quad b = QUADS[in % NQ], out;
    int64_t n = TRIPS[in / NQ];
    uint64_t acc = 0;
    for (int64_t i = 0; i < n; i++) acc = acc * 31 + d_quad(mix(1, (uint64_t)i), &b);
    int64_t r = loop_pass(&out, b, n);
    check_bits("loop_pass", "r", in, (uint64_t)r, acc);
    check_quad("loop_pass", "out", in, &out, &b);
  }
  end_shape("loop_pass");

  for (in = 0; in < NQ * NQ; in++) {
    Quad b = QUADS[in % NQ], out[2];
    int64_t v = VALUES[in / NQ];
    int64_t r = cg_writes_param(out, b, v);
    Quad b2 = b;
    b2.q2 = v;
    check_bits("cg_writes_param", "r", in, (uint64_t)r, d_quad(mix(1, (uint64_t)v), &b2));
    check_quad("cg_writes_param", "param", in, &out[0], &b);
    check_quad("cg_writes_param", "inserted", in, &out[1], &b2);
  }
  end_shape("cg_writes_param");

  for (in = 0; in < NQ * NQ; in++) {
    Quad b = QUADS[in % NQ], out;
    int64_t v = VALUES[in / NQ];
    int64_t r = cg_to_cg(&out, b, v);
    Quad b2 = b;
    b2.q1 = v;
    check_bits("cg_to_cg", "r", in, (uint64_t)r,
               d_quad(mix(1, (uint64_t)v), &b2) ^ (uint64_t)b.q1);
    check_quad("cg_to_cg", "out", in, &out, &b);
  }
  end_shape("cg_to_cg");

  for (in = 0; in < NQ * 2; in++) {
    Quad a = QUADS[in % NQ], b = QUADS[(in + 1) % NQ], out[3];
    int64_t c = in / NQ, v = VALUES[in % NQ];
    const Quad *x = c ? &a : &b;
    int64_t r = phi_pass(out, a, b, c, v);
    check_bits("phi_pass", "r", in, (uint64_t)r, d_quad(mix(1, (uint64_t)v), x));
    check_quad("phi_pass", "joined", in, &out[0], x);
    check_quad("phi_pass", "a", in, &out[1], &a);
    check_quad("phi_pass", "b", in, &out[2], &b);
  }
  end_shape("phi_pass");

  /* Tail position: C's own arguments are unchanged by C semantics; the
   * digests show each callee read an intact copy. */
  for (in = 0; in < NQ * NQ; in++) {
    ORIGINAL(Quad, b, QUADS[in % NQ]);
    int64_t v = VALUES[in / NQ];
    int64_t r = tail_pass(b, v);
    check_bits("tail_pass", "r", in, (uint64_t)r, d_quad(mix(1, (uint64_t)v), &b_want));
    check_quad("tail_pass", "arg", in, &b, &b_want);
  }
  end_shape("tail_pass");

  for (in = 0; in < NQ; in++) {
    const Quad k = {7, -8, 9, -10};
    int64_t v = VALUES[in];
    check_bits("tail_const", "r", in, (uint64_t)tail_const(v), d_quad(mix(1, (uint64_t)v), &k));
  }
  end_shape("tail_const");

  for (in = 0; in < NQ; in++) {
    ORIGINAL(Huge, b, huge_at(in));
    int64_t v = VALUES[in];
    int64_t r = tail_huge(b, v);
    check_bits("tail_huge", "r", in, (uint64_t)r, d_huge(mix(5, (uint64_t)v), &b_want));
    check_huge("tail_huge", in, &b, &b_want);
  }
  end_shape("tail_huge");

  for (in = 0; in < NQ; in++) {
    int64_t v = VALUES[in];
    check_bits("tail_scalar", "r", in, (uint64_t)tail_scalar(v), (uint64_t)v * 3 + 1);
  }
  end_shape("tail_scalar");

  for (in = 0; in < NQ * NQ; in++) {
    Quad b = QUADS[in % NQ], out;
    int64_t v = VALUES[in / NQ];
    int64_t r = var_mut_pass(&out, b, v);
    check_bits("var_mut_pass", "r", in, (uint64_t)r, d_quad(d_quad(mix(7, (uint64_t)v), &b), &b));
    check_quad("var_mut_pass", "out", in, &out, &b);
  }
  end_shape("var_mut_pass");

  for (in = 0; in < NQ; in++) {
    Quad b = QUADS[in];
    Tri t = TRIS[in];
    int64_t v = VALUES[in];
    struct { Quad q; Tri t; } out;
    int64_t r = var_value_pass(&out.q, b, t, v);
    check_bits("var_value_pass", "r", in, (uint64_t)r,
               d_quad(d_tri(d_quad(mix(8, (uint64_t)v), &b), &t), &b));
    check_quad("var_value_pass", "out", in, &out.q, &b);
    check_tri("var_value_pass", in, &out.t, &t);
  }
  end_shape("var_value_pass");

  for (in = 0; in < NQ * NQ; in++) {
    Five b, out;
    for (int i = 0; i < 5; i++) b.f[i] = QUADS[in % NQ].q0 * (i + 3) - i;
    int64_t v = VALUES[in / NQ];
    int64_t r = five_pass(&out, b, v);
    check_bits("five_pass", "r", in, (uint64_t)r, d_words(mix(10, (uint64_t)v), b.f, 5));
    check_mem("five_pass", "out", in, &out, &b, sizeof b);
  }
  end_shape("five_pass");

  {
    static Giant src, want, out;
    for (in = 0; in < NQ; in++) {
      for (int i = 0; i < 9000; i++) src.g[i] = (int64_t)(0x9e3779b97f4a7c15ULL * (uint64_t)(i + 1)) ^ in;
      want = src;
      giant_lo = (const char *)&src;
      giant_hi = (const char *)&src + sizeof src;
      int64_t v = VALUES[in];
      uint64_t h = d_words(mix(11, (uint64_t)v), want.g, 9000);
      memset(&out, 0xee, sizeof out);
      check_bits("giant_pass", "r", in, (uint64_t)giant_pass(&out, &src, v), h);
      check_mem("giant_pass", "out", in, &out, &want, sizeof want);
      check_mem("giant_pass", "src", in, &src, &want, sizeof want);
      check_bits("giant_load_pass", "r", in, (uint64_t)giant_load_pass(&src, v), h);
      check_mem("giant_load_pass", "src", in, &src, &want, sizeof want);
    }
    giant_lo = giant_hi = 0;
    end_shape("giant_pass");
  }

  for (in = 0; in < NQ; in++) {
    K k, want, out;
    for (int i = 0; i < 128; i++) k.g[i] = (int64_t)(i * 1000003) - in;
    want = k;
    int64_t v = VALUES[in];
    uint64_t r = (uint64_t)v;
    for (int c = 0; c < 8; c++) r = d_words(mix(12, r), want.g, 128);
    check_bits("many_pass", "r", in, (uint64_t)many_pass(&out, &k, v), r);
    check_mem("many_pass", "out", in, &out, &want, sizeof want);
    check_mem("many_pass", "src", in, &k, &want, sizeof want);
  }
  end_shape("many_pass");

  /* Parameters over 256 bytes forwarded in fixed and anonymous positions. */
  for (in = 0; in < NQ; in++) {
    K k, want, out;
    for (int i = 0; i < 128; i++) k.g[i] = (int64_t)(i * 7919) ^ (in << 20);
    want = k;
    int64_t v = VALUES[in];
    uint64_t fixed = d_words(mix(12, (uint64_t)v), want.g, 128);
    uint64_t anon = d_words(mix(13, (uint64_t)v), want.g, 128);
    check_bits("param_big", "k_param r", in, (uint64_t)k_param_pass(&out, k, v), fixed);
    check_mem("param_big", "k_param out", in, &out, &want, sizeof want);
    check_bits("param_big", "k_block r", in, (uint64_t)k_block_pass(&out, &k, v), fixed);
    check_mem("param_big", "k_block out", in, &out, &want, sizeof want);
    check_mem("param_big", "k_block src", in, &k, &want, sizeof want);
    check_bits("param_big", "var_param r", in, (uint64_t)var_param_k(&out, k, v), anon);
    check_mem("param_big", "var_param out", in, &out, &want, sizeof want);
    check_bits("param_big", "var_block r", in, (uint64_t)var_block_k(&out, &k, v), anon);
    check_mem("param_big", "var_block out", in, &out, &want, sizeof want);
    check_mem("param_big", "var_block src", in, &k, &want, sizeof want);
    M2 m, mwant, mout;
    for (int i = 0; i < 33; i++) m.g[i] = (int64_t)(i * 31) - in;
    mwant = m;
    check_bits("param_big", "var_m2 r", in, (uint64_t)var_param_m2(&mout, m, v),
               d_words(mix(14, (uint64_t)v), mwant.g, 33));
    check_mem("param_big", "var_m2 out", in, &mout, &mwant, sizeof mwant);
  }
  end_shape("param_big");

  printf("large-aggregate-args shapes_failed=%d checks=%d failures=%d\n", failed_shapes,
         total_checks, total_failures);
  return total_failures != 0;
}
