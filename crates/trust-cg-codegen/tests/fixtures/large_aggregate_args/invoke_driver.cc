// C++ oracle for invoke.trust_ir: each callee digests the by-reference
// parameter it received, writes all of it, and throws on odd input; the
// trust-cg functions catch the exception in their landing pads. The driver
// requires the value each trust-cg function stored after the call (on the
// normal and the exceptional path) to equal what it passed, and the source
// objects to be unchanged. Prints one line per shape, then a summary; exits
// nonzero on any mismatch.
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef struct { int64_t q0, q1, q2, q3; } Quad;
typedef struct { int64_t g[40]; } Big;
typedef struct { int64_t g[9000]; } Giant;

extern "C" int64_t inv_param(Quad *, Quad, int64_t);
extern "C" int64_t inv_load_copy(Big *, const Big *, int64_t);
extern "C" int64_t inv_load_fast(const Big *, int64_t);
extern "C" int64_t inv_giant(Giant *, const Giant *, int64_t);

static uint64_t digest(uint64_t h, const int64_t *w, int n) {
  for (int i = 0; i < n; i++) {
    h ^= (uint64_t)w[i];
    h *= 0x100000001b3ULL;
    h ^= h >> 29;
  }
  return h;
}

// Where the caller's source object lives: a callee handed that storage
// instead of a copy mixes in a sentinel.
static const char *source_lo, *source_hi;

template <typename T>
static int64_t take(T &b, int64_t v, uint64_t seed) {
  const int n = sizeof b / sizeof(int64_t);
  int64_t *w = reinterpret_cast<int64_t *>(&b);
  uint64_t h = digest(seed ^ (uint64_t)v, w, n);
  if ((const char *)&b < source_hi && (const char *)&b + sizeof b > source_lo) h ^= 0x5a5e;
  for (int i = 0; i < n; i++) w[i] = ~w[i] ^ v;
  __asm__ volatile("" : : "r"(w) : "memory");
  if (v & 1) throw 42;
  return (int64_t)h;
}

extern "C" __attribute__((noinline)) int64_t c_throw_quad(Quad b, int64_t v) {
  return take(b, v, 1);
}
extern "C" __attribute__((noinline)) int64_t c_throw_big(Big b, int64_t v) {
  return take(b, v, 2);
}
extern "C" __attribute__((noinline)) int64_t c_throw_giant(Giant b, int64_t v) {
  return take(b, v, 3);
}

static int checks, failures, shape_checks, shape_failures, failed_shapes;
static void check(const char *shape, const char *what, int64_t v, bool ok) {
  shape_checks++;
  if (!ok) {
    shape_failures++;
    printf("  %s v=%lld %s\n", shape, (long long)v, what);
  }
}
static void end_shape(const char *shape) {
  printf("shape %s checks=%d failures=%d %s\n", shape, shape_checks, shape_failures,
         shape_failures ? "FAIL" : "ok");
  checks += shape_checks;
  failures += shape_failures;
  failed_shapes += shape_failures != 0;
  shape_checks = shape_failures = 0;
}
template <typename T>
static int64_t expected(const T &b, int64_t v, uint64_t seed) {
  return (v & 1) ? -1 : (int64_t)digest(seed ^ (uint64_t)v, reinterpret_cast<const int64_t *>(&b),
                                        sizeof b / sizeof(int64_t));
}

static Giant giant_src, giant_want, giant_out;

int main() {
  for (int64_t v = 2; v <= 5; v++) {
    Quad q = {v, -v, 3 * v, 0x5a5a}, out;
    memset(&out, 0xee, sizeof out);
    int64_t r = inv_param(&out, q, v);
    check("inv_param", "result", v, r == expected(q, v, 1));
    check("inv_param", "stored value", v, memcmp(&out, &q, sizeof q) == 0);
  }
  end_shape("inv_param");

  for (int64_t v = 2; v <= 5; v++) {
    Big src, want, out;
    for (int i = 0; i < 40; i++) src.g[i] = i * 7 + v;
    want = src;
    source_lo = (const char *)&src;
    source_hi = (const char *)&src + sizeof src;
    memset(&out, 0xee, sizeof out);
    int64_t r = inv_load_copy(&out, &src, v);
    check("inv_load_copy", "result", v, r == expected(want, v, 2));
    check("inv_load_copy", "stored value", v, memcmp(&out, &want, sizeof want) == 0);
    check("inv_load_copy", "source", v, memcmp(&src, &want, sizeof want) == 0);
    r = inv_load_fast(&src, v);
    check("inv_load_fast", "result", v, r == expected(want, v, 2));
    check("inv_load_fast", "source", v, memcmp(&src, &want, sizeof want) == 0);
    source_lo = source_hi = nullptr;
  }
  end_shape("inv_load");

  for (int64_t v = 2; v <= 3; v++) {
    for (int i = 0; i < 9000; i++) giant_src.g[i] = (int64_t)(i * 0x9e3779b9) - v;
    giant_want = giant_src;
    source_lo = (const char *)&giant_src;
    source_hi = (const char *)&giant_src + sizeof giant_src;
    memset(&giant_out, 0xee, sizeof giant_out);
    int64_t r = inv_giant(&giant_out, &giant_src, v);
    check("inv_giant", "result", v, r == expected(giant_want, v, 3));
    check("inv_giant", "stored value", v,
          memcmp(&giant_out, &giant_want, sizeof giant_want) == 0);
    check("inv_giant", "source", v, memcmp(&giant_src, &giant_want, sizeof giant_want) == 0);
    source_lo = source_hi = nullptr;
  }
  end_shape("inv_giant");

  printf("large-aggregate-invoke shapes_failed=%d checks=%d failures=%d\n", failed_shapes, checks,
         failures);
  return failures != 0;
}
