// C++ oracle for invoke_variadic.trust_ir: each variadic callee reads its
// anonymous by-reference argument with va_arg (AAPCS64 passes a pointer to
// the caller's copy), digests it, writes all of it and throws on odd input.
// The driver requires the value each trust-cg function stored after the call,
// on both paths, and its source to be unchanged. Prints one line per shape,
// then a summary; exits nonzero on any mismatch.
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef struct { int64_t q0, q1, q2, q3; } Quad;
typedef struct { int64_t g[128]; } K;

extern "C" int64_t inv_var_param(Quad *, Quad, int64_t);
extern "C" int64_t inv_var_block_k(K *, const K *, int64_t);

static uint64_t digest(uint64_t h, const int64_t *w, int n) {
  for (int i = 0; i < n; i++) {
    h ^= (uint64_t)w[i];
    h *= 0x100000001b3ULL;
    h ^= h >> 29;
  }
  return h;
}

static const char *source_lo, *source_hi;

template <typename T>
static int64_t take(T *b, int64_t v, uint64_t seed) {
  const int n = sizeof *b / sizeof(int64_t);
  int64_t *w = reinterpret_cast<int64_t *>(b);
  uint64_t h = digest(seed ^ (uint64_t)v, w, n);
  if ((const char *)b < source_hi && (const char *)b + sizeof *b > source_lo) h ^= 0x5a5e;
  for (int i = 0; i < n; i++) w[i] = ~w[i] ^ v;
  __asm__ volatile("" : : "r"(w) : "memory");
  if (v & 1) throw 42;
  return (int64_t)h;
}

extern "C" __attribute__((noinline)) int64_t c_var_throw_quad(int64_t v, ...) {
  va_list ap;
  va_start(ap, v);
  Quad *p = va_arg(ap, Quad *);
  va_end(ap);
  return take(p, v, 21);
}
extern "C" __attribute__((noinline)) int64_t c_var_throw_k(int64_t v, ...) {
  va_list ap;
  va_start(ap, v);
  K *p = va_arg(ap, K *);
  va_end(ap);
  return take(p, v, 22);
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

int main() {
  for (int64_t v = 2; v <= 5; v++) {
    Quad q = {v, -v, 5 * v, 0x77}, out;
    memset(&out, 0xee, sizeof out);
    int64_t r = inv_var_param(&out, q, v);
    check("inv_var_param", "result", v, r == expected(q, v, 21));
    check("inv_var_param", "stored value", v, memcmp(&out, &q, sizeof q) == 0);
  }
  end_shape("inv_var_param");

  for (int64_t v = 2; v <= 5; v++) {
    K src, want, out;
    for (int i = 0; i < 128; i++) src.g[i] = i * 13 - v;
    want = src;
    source_lo = (const char *)&src;
    source_hi = (const char *)&src + sizeof src;
    memset(&out, 0xee, sizeof out);
    int64_t r = inv_var_block_k(&out, &src, v);
    check("inv_var_block_k", "result", v, r == expected(want, v, 22));
    check("inv_var_block_k", "stored value", v, memcmp(&out, &want, sizeof want) == 0);
    check("inv_var_block_k", "source", v, memcmp(&src, &want, sizeof want) == 0);
    source_lo = source_hi = nullptr;
  }
  end_shape("inv_var_block_k");

  printf("large-aggregate-invoke-variadic shapes_failed=%d checks=%d failures=%d\n",
         failed_shapes, checks, failures);
  return failures != 0;
}
