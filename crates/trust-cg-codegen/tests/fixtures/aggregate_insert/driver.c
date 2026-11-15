/* C oracle for the aggregate InsertField/InsertElement value-semantics corpus
 * (corpus.trust_ir). Every shape is called with several inputs and every
 * returned field, and every byte it may write, is compared bit-exactly with a
 * C reimplementation. Prints one line per shape, then a summary; exits nonzero
 * on any mismatch. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef struct { int64_t m0, m1; } PI;
typedef struct { float m0, m1; } PF;
typedef struct { _Float16 m0, m1; } PH;
typedef struct { int64_t q0, q1, q2, q3; } Q;
typedef struct { PI inner; int64_t x; } Outer;
typedef struct __attribute__((packed)) { int8_t a; int64_t b; } Packed;
_Static_assert(sizeof(PI) == 16 && sizeof(PF) == 8 && sizeof(PH) == 4, "pairs");
_Static_assert(sizeof(Q) == 32 && sizeof(Outer) == 24 && sizeof(Packed) == 9, "wide");

extern PI swap_i64(PI);
extern PF swap_f32(PF);
extern PH swap_f16(PH);
extern Q old_new(PI, int64_t);
extern int64_t big_callee(Q, int64_t);
extern Q big_caller(Q, int64_t);
extern Q load_insert(const PI *, int64_t);
extern Q global_insert(int64_t);
extern PI agg_insert_global;
extern Q nested_inner(Outer, int64_t);
extern Q nested_outer(Outer, PI);
extern Q array_elem(const int64_t *, int64_t, int64_t);
extern Q copy_shape(PI, int64_t);
extern Q select_shape(PI, PI, int64_t, int64_t);
extern Q phi_join(PI, PI, int64_t, int64_t);
extern Q loop_prev(PI, int64_t);
extern Q loop_exit_old(PI, int64_t);
extern PI loop_swap(PI, int64_t);
extern Q const_twice(int64_t, int64_t);
extern PI make_pair(void);
extern Q call_result(int64_t);
extern int64_t store_after(PI, PI *, int64_t);
extern Q vec_shape(int32_t);
extern Q packed_shape(const Packed *, int64_t);
extern Q fanout(PI, int64_t, int64_t);
extern Q loop_rotate(PI, PI, int64_t);
extern Q vec_f32(float);
extern int64_t loop_load_prev(PI *, int64_t);
extern Q loop_const_prev(PI, int64_t);
static int shape_checks, shape_failures, total_checks, total_failures, failed_shapes;

static void check_bits(const char *shape, const char *field, int input,
                       uint64_t got, uint64_t want) {
  shape_checks++;
  if (got != want) {
    shape_failures++;
    if (shape_failures <= 4)
      printf("  %s input %d %s: got 0x%016llx want 0x%016llx\n", shape, input, field,
             (unsigned long long)got, (unsigned long long)want);
  }
}
static void check_q(const char *shape, int input, Q got, Q want) {
  check_bits(shape, "q0", input, (uint64_t)got.q0, (uint64_t)want.q0);
  check_bits(shape, "q1", input, (uint64_t)got.q1, (uint64_t)want.q1);
  check_bits(shape, "q2", input, (uint64_t)got.q2, (uint64_t)want.q2);
  check_bits(shape, "q3", input, (uint64_t)got.q3, (uint64_t)want.q3);
}
static void check_pi(const char *shape, int input, PI got, PI want) {
  check_bits(shape, "m0", input, (uint64_t)got.m0, (uint64_t)want.m0);
  check_bits(shape, "m1", input, (uint64_t)got.m1, (uint64_t)want.m1);
}
static uint32_t f32_bits(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }
static uint16_t f16_bits(_Float16 f) { uint16_t u; memcpy(&u, &f, 2); return u; }
static void end_shape(const char *shape) {
  printf("shape %s checks=%d failures=%d %s\n", shape, shape_checks, shape_failures,
         shape_failures ? "FAIL" : "ok");
  total_checks += shape_checks;
  total_failures += shape_failures;
  failed_shapes += shape_failures != 0;
  shape_checks = shape_failures = 0;
}

static const PI PAIRS[] = {
  {1, 2}, {-5, INT64_MAX}, {(int64_t)0x0123456789abcdefLL, -1}, {0, INT64_MIN},
};
static const int64_t VALUES[] = {42, -9, INT64_MIN, (int64_t)0x5a5a5a5a5a5a5a5aLL};
#define NPAIRS (int)(sizeof PAIRS / sizeof PAIRS[0])
#define NVALUES (int)(sizeof VALUES / sizeof VALUES[0])
static Q q(int64_t a, int64_t b, int64_t c, int64_t d) { Q r = {a, b, c, d}; return r; }

int main(void) {
  int in;
  /* swap: the source is live after the first insert. */
  for (in = 0; in < NPAIRS; in++) {
    PI s = PAIRS[in];
    PI want = {s.m1, s.m0};
    check_pi("swap_i64", in, swap_i64(s), want);
  }
  end_shape("swap_i64");
  {
    static const float F[][2] = {{1.0f, 2.0f}, {-0.0f, 3.5f}, {1e30f, -1e-30f}, {0.1f, -7.25f}};
    for (in = 0; in < 4; in++) {
      PF s = {F[in][0], F[in][1]};
      PF got = swap_f32(s);
      check_bits("swap_f32", "m0", in, f32_bits(got.m0), f32_bits(s.m1));
      check_bits("swap_f32", "m1", in, f32_bits(got.m1), f32_bits(s.m0));
    }
    end_shape("swap_f32");
  }
  {
    static const float H[][2] = {{1.0f, 2.0f}, {-0.0f, 3.5f}, {65504.0f, -0.25f}, {0.125f, -7.0f}};
    for (in = 0; in < 4; in++) {
      PH s = {(_Float16)H[in][0], (_Float16)H[in][1]};
      PH got = swap_f16(s);
      check_bits("swap_f16", "m0", in, f16_bits(got.m0), f16_bits(s.m1));
      check_bits("swap_f16", "m1", in, f16_bits(got.m1), f16_bits(s.m0));
    }
    end_shape("swap_f16");
  }
  /* ExtractField of the source after an insert, source a register param. */
  for (in = 0; in < NPAIRS * NVALUES; in++) {
    PI s = PAIRS[in % NPAIRS];
    int64_t v = VALUES[in / NPAIRS];
    check_q("old_new", in, old_new(s, v), q(s.m0, s.m1, v, s.m1));
  }
  end_shape("old_new");
  /* A 32-byte parameter passed by reference: the callee's insert must not
   * write the caller's copy (checked from C and from a TrustCG caller). */
  for (in = 0; in < NVALUES; in++) {
    Q b = q(11, 22, 33 + in, 44);
    int64_t v = VALUES[in];
    int64_t r = big_callee(b, v);
    check_bits("big_callee", "ret", in, (uint64_t)r, (uint64_t)(v + b.q3));
    check_q("big_callee", in, b, q(11, 22, 33 + in, 44));
  }
  end_shape("big_callee");
  for (in = 0; in < NVALUES; in++) {
    Q b = q(11, 22, 33 + in, 44);
    int64_t v = VALUES[in];
    check_q("big_caller", in, big_caller(b, v), q(11, 22, 33 + in, v + 44));
  }
  end_shape("big_caller");
  /* An aggregate Load's copy: the insert must not reach memory. */
  for (in = 0; in < NPAIRS * NVALUES; in++) {
    PI s = PAIRS[in % NPAIRS];
    int64_t v = VALUES[in / NPAIRS];
    check_q("load_insert", in, load_insert(&s, v), q(s.m0, v, s.m0, s.m1));
    check_pi("load_insert_mem", in, s, PAIRS[in % NPAIRS]);
  }
  end_shape("load_insert");
  for (in = 0; in < NVALUES; in++) {
    PI g = {5, 6};
    agg_insert_global = g;
    check_q("global_insert", in, global_insert(VALUES[in]), q(6, VALUES[in], 5, 6));
    check_pi("global_insert_mem", in, agg_insert_global, g);
  }
  end_shape("global_insert");
  /* Nested aggregates: an insert into an extracted inner field, and an
   * aggregate-valued insert into the outer. */
  for (in = 0; in < NPAIRS * NVALUES; in++) {
    Outer o = {PAIRS[in % NPAIRS], 1000 + in};
    int64_t v = VALUES[in / NPAIRS];
    check_q("nested_inner", in, nested_inner(o, v), q(o.inner.m1, v, o.inner.m1, o.x));
  }
  end_shape("nested_inner");
  for (in = 0; in < NPAIRS * NVALUES; in++) {
    Outer o = {PAIRS[in % NPAIRS], 1000 + in};
    int64_t v = VALUES[in / NPAIRS];
    PI p = {v, ~v};
    check_q("nested_outer", in, nested_outer(o, p), q(o.inner.m0, p.m0, o.inner.m1, o.x));
  }
  end_shape("nested_outer");
  /* Array InsertElement over a loaded [i64 x 4]. */
  for (in = 0; in < 4 * NVALUES; in++) {
    int64_t a[4] = {100 + in, 200, 300, 400};
    int64_t idx = in % 4, v = VALUES[in / 4];
    check_q("array_elem", in, array_elem(a, idx, v), q(a[idx], v, a[0], idx == 0 ? v : a[0]));
  }
  end_shape("array_elem");
  /* Copy, Select and a block-parameter join of aggregates. */
  for (in = 0; in < NPAIRS * NVALUES; in++) {
    PI s = PAIRS[in % NPAIRS];
    int64_t v = VALUES[in / NPAIRS];
    check_q("copy_shape", in, copy_shape(s, v), q(s.m0, s.m1, v, s.m0));
  }
  end_shape("copy_shape");
  for (in = 0; in < 2 * NPAIRS * NVALUES; in++) {
    PI a = PAIRS[in % NPAIRS], b = PAIRS[(in + 1) % NPAIRS];
    int64_t c = in & 1, v = VALUES[(in / 2) % NVALUES];
    PI sel = c ? a : b;
    check_q("select_shape", in, select_shape(a, b, c, v), q(a.m0, b.m0, v, sel.m0));
  }
  end_shape("select_shape");
  for (in = 0; in < 2 * NPAIRS * NVALUES; in++) {
    PI a = PAIRS[in % NPAIRS], b = PAIRS[(in + 1) % NPAIRS];
    int64_t c = in & 1, v = VALUES[(in / 2) % NVALUES];
    PI sel = c ? a : b;
    check_q("phi_join", in, phi_join(a, b, c, v), q(a.m1, b.m1, sel.m1, v));
  }
  end_shape("phi_join");
  /* Loop-carried aggregates whose previous value is read after the insert. */
  static const int64_t N[] = {0, 1, 2, 3, 5, 8};
#define NLOOP (NPAIRS * 6)
  for (in = 0; in < NLOOP; in++) {
    PI s = PAIRS[in % NPAIRS], acc = s;
    int64_t n = N[in / NPAIRS], i, sum = 0;
    for (i = 0; i < n; i++) {
      int64_t old0 = acc.m0;
      PI nw = {(int64_t)((uint64_t)acc.m1 + (uint64_t)i), old0};
      sum = (int64_t)((uint64_t)sum * 31u + (uint64_t)old0);
      acc = nw;
    }
    check_q("loop_prev", in, loop_prev(s, n), q(acc.m0, acc.m1, sum, n > 0 ? n : 0));
  }
  end_shape("loop_prev");
  /* loop_exit_old exits with the value before the last insert and after it. */
  for (in = 0; in < NLOOP; in++) {
    PI s = PAIRS[in % NPAIRS], a2 = s, nx;
    int64_t n = N[in / NPAIRS], j = 0;
    for (;;) {
      nx = a2; nx.m0 = j;
      if (j + 1 < n) { a2 = nx; j++; continue; }
      break;
    }
    check_q("loop_exit_old", in, loop_exit_old(s, n), q(a2.m0, a2.m1, nx.m0, nx.m1));
  }
  end_shape("loop_exit_old");
  for (in = 0; in < NLOOP; in++) {
    PI s = PAIRS[in % NPAIRS];
    int64_t n = N[in / NPAIRS];
    PI want = (n & 1) ? (PI){s.m1, s.m0} : s;
    check_pi("loop_swap", in, loop_swap(s, n), want);
  }
  end_shape("loop_swap");
  /* Two aggregate block parameters exchanged on the back edge. */
  for (in = 0; in < NLOOP; in++) {
    PI s = PAIRS[in % NPAIRS], a = s, b = PAIRS[(in + 1) % NPAIRS];
    int64_t n = N[in / NPAIRS], i;
    for (i = 0; i < n; i++) {
      PI a2 = a; a2.m0 = (int64_t)((uint64_t)a.m0 + (uint64_t)i);
      a = b; b = a2;
    }
    check_q("loop_rotate", in, loop_rotate(s, PAIRS[(in + 1) % NPAIRS], n), q(a.m0, a.m1, b.m0, b.m1));
  }
  end_shape("loop_rotate");
  /* A constant aggregate used as the source of two inserts. */
  for (in = 0; in < NVALUES; in++) {
    int64_t v = VALUES[in], w = VALUES[(in + 1) % NVALUES];
    check_q("const_twice", in, const_twice(v, w), q(v, 2, 1, w));
  }
  end_shape("const_twice");
  /* A call result as the source. */
  for (in = 0; in < NVALUES; in++)
    check_q("call_result", in, call_result(VALUES[in]), q(7, 8, VALUES[in], 8));
  end_shape("call_result");
  /* Store of the source after the insert. */
  for (in = 0; in < NPAIRS * NVALUES; in++) {
    PI s = PAIRS[in % NPAIRS], out[2] = {{0, 0}, {0, 0}};
    int64_t v = VALUES[in / NPAIRS];
    int64_t r = store_after(s, out, v);
    check_bits("store_after", "ret", in, (uint64_t)r, (uint64_t)v);
    check_pi("store_after_old", in, out[0], s);
    check_pi("store_after_new", in, out[1], (PI){v, s.m1});
  }
  end_shape("store_after");
  /* Vector InsertElement (register value). */
  for (in = 0; in < NVALUES; in++) {
    int32_t a = (int32_t)VALUES[in];
    check_q("vec_shape", in, vec_shape(a), q(3, a, 1, 1));
  }
  end_shape("vec_shape");
  /* Packed struct: the explicit-offset insert path. */
  for (in = 0; in < NVALUES; in++) {
    Packed p;
    p.a = (int8_t)(-3 - in);
    p.b = 0x1122334455667788LL + in;
    int64_t v = VALUES[in];
    check_q("packed_shape", in, packed_shape(&p, v), q(p.b, v, p.a, p.a));
  }
  end_shape("packed_shape");
  /* One insert result used as the source of two further inserts. */
  for (in = 0; in < NPAIRS * NVALUES; in++) {
    PI s = PAIRS[in % NPAIRS];
    int64_t v = VALUES[in / NPAIRS], w = ~VALUES[in / NPAIRS];
    check_q("fanout", in, fanout(s, v, w), q(v, w, s.m1, s.m1));
  }
  end_shape("fanout");
  {
    static const float A[] = {-0.0f, 1.5f, 1e-40f, -3.25e7f};
    for (in = 0; in < 4; in++) {
      float a = A[in];
      check_q("vec_f32", in, vec_f32(a),
              q(f32_bits(2.0f), f32_bits(a), f32_bits(4.0f), f32_bits(4.0f)));
    }
    end_shape("vec_f32");
  }
  /* An aggregate Load re-executed in a loop while the previous iteration's
   * loaded value, carried by a block parameter, is still read. */
  for (in = 0; in < 6; in++) {
    PI p = {100 + in, 7};
    int64_t n = N[in], k;
    uint64_t sum = 0;
    for (k = 0; k < n; k++) {
      int64_t acc0 = k == 0 ? 100 + in : 100 + in + (k - 1);
      sum = sum * 31u + (uint64_t)acc0;
    }
    check_bits("loop_load_prev", "ret", in, (uint64_t)loop_load_prev(&p, n), sum);
    check_bits("loop_load_prev", "mem", in, (uint64_t)p.m0, (uint64_t)(100 + in + n));
  }
  end_shape("loop_load_prev");
  /* A constant re-materialized in a loop and inserted into in place, while the
   * previous iteration's value, carried by a block parameter, is read. */
  for (in = 0; in < NLOOP; in++) {
    PI s = PAIRS[in % NPAIRS], acc = s;
    int64_t n = N[in / NPAIRS], i;
    uint64_t sum = 0;
    for (i = 0; i < n; i++) {
      int64_t old0 = acc.m0;
      PI nw = {i, (int64_t)((uint64_t)acc.m0 + (uint64_t)acc.m1)};
      sum = sum * 31u + (uint64_t)old0;
      acc = nw;
    }
    check_q("loop_const_prev", in, loop_const_prev(s, n), q(acc.m0, acc.m1, (int64_t)sum, n));
  }
  end_shape("loop_const_prev");
  printf("aggregate-insert shapes_failed=%d checks=%d failures=%d\n", failed_shapes,
         total_checks, total_failures);
  return total_failures != 0;
}
