/* C oracle for zero_sized.trust_ir: every function takes and returns an
 * int64_t; the zero-sized values it carries have no observable bytes. Prints
 * one line per function, then a summary; exits nonzero on any mismatch. */
#include <stdint.h>
#include <stdio.h>

extern int64_t unit_pair(int64_t);
extern int64_t empty_pair(int64_t);
extern int64_t empty_loop(int64_t);
extern int64_t empty_const_param(int64_t);
extern int64_t zero_insert(int64_t);
extern int64_t undef_unit_pair(int64_t);
extern int64_t empty_field_loop(int64_t);
extern int64_t field_insert_twice(int64_t);

static const int64_t INPUTS[] = {0, 1, 5, -3, 1000};
#define N (int)(sizeof INPUTS / sizeof INPUTS[0])
static int total_checks, total_failures, failed_shapes;

static void shape(const char *name, int64_t (*f)(int64_t), int64_t (*model)(int64_t)) {
  int failures = 0;
  for (int i = 0; i < N; i++) {
    int64_t got = f(INPUTS[i]), want = model(INPUTS[i]);
    if (got != want) {
      failures++;
      printf("  %s input %lld: got %lld want %lld\n", name, (long long)INPUTS[i],
             (long long)got, (long long)want);
    }
  }
  printf("shape %s checks=%d failures=%d %s\n", name, N, failures, failures ? "FAIL" : "ok");
  total_checks += N;
  total_failures += failures;
  failed_shapes += failures != 0;
}

static int64_t m_unit_pair(int64_t x) { return (int64_t)((uint64_t)x * 3u); }
static int64_t m_empty_pair(int64_t x) { return (x != 0 ? x : 0) + 1; }
static int64_t m_empty_loop(int64_t x) { return x > 0 ? x : 0; }
static int64_t m_empty_const_param(int64_t x) { return x - 7; }
static int64_t m_zero_insert(int64_t x) { return x ^ 5; }
static int64_t m_undef_unit_pair(int64_t x) { return x != 0 ? x : 0; }
static int64_t m_empty_field_loop(int64_t x) { return x > 0 ? 0 : x; }
static int64_t m_field_insert_twice(int64_t x) { return 10 + x; }

int main(void) {
  shape("unit_pair", unit_pair, m_unit_pair);
  shape("empty_pair", empty_pair, m_empty_pair);
  shape("empty_loop", empty_loop, m_empty_loop);
  shape("empty_const_param", empty_const_param, m_empty_const_param);
  shape("zero_insert", zero_insert, m_zero_insert);
  shape("undef_unit_pair", undef_unit_pair, m_undef_unit_pair);
  shape("empty_field_loop", empty_field_loop, m_empty_field_loop);
  shape("field_insert_twice", field_insert_twice, m_field_insert_twice);
  printf("zero-sized shapes_failed=%d checks=%d failures=%d\n", failed_shapes, total_checks,
         total_failures);
  return total_failures != 0;
}
