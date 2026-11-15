#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
const uint64_t foreign_value = UINT64_C(0x1029384756abcdef);
uint64_t foreign_mutable = 0;
#if PRESENT
uint64_t optional_mutable = 0;
const uint64_t optional_data = UINT64_C(0xfedcba9876543210);
uint64_t optional_function(uint64_t x) { return x * 31 + 7; }
#endif
extern uint64_t strong_read(void), strong_write(uint64_t), weak_read(uint64_t);
extern uintptr_t weak_address_direct(void), weak_address_saved(void);
extern void weak_mutable_set(uint64_t);
extern uint64_t weak_mutable_get(void);
static size_t checks;
static void check(uint64_t a,uint64_t b) { ++checks; if(a!=b) {fprintf(stderr,"check=%zu got=%llx want=%llx\n",checks,(unsigned long long)a,(unsigned long long)b);abort();} }
int main(void) {
 check(strong_read(),(foreign_value*37)^foreign_value);
 check(weak_address_direct(),weak_address_saved());
 check(weak_mutable_get(),PRESENT ? 0 : 0x13579bdf);
 for(uint64_t seed=0;seed<4096;++seed) {
  uint64_t x=seed*UINT64_C(0x9281abcd) ^ (seed<<51);
  check(strong_write(x),x);check(foreign_mutable,x);
  uint64_t want=PRESENT ? (x*31+7)^UINT64_C(0xfedcba9876543210) : (x+17)^UINT64_C(0x88776655);
  check(weak_read(x),want);
  weak_mutable_set(x);
  check(weak_mutable_get(),PRESENT ? x : UINT64_C(0x13579bdf));
 }
 printf("PASS foreign_statics checks=%zu\n",checks);
}
