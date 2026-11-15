#include <stdio.h>
extern unsigned long tcg_tls_get(void), tcg_tls_get_z(void);
__thread unsigned long c_t = 7;
int main(void) {
  unsigned long a = tcg_tls_get(), z = tcg_tls_get_z();
  printf("tcg_t=%#lx tcg_tz=%#lx c_t=%lu\n", a, z, c_t);
  return a == 42 && z == 0 && c_t == 7 ? 0 : 1;
}
