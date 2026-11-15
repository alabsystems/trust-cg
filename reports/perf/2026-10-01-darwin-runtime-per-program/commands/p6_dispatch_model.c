// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// C model of p6_branch_match's random 7-way dispatch, to compare a compare
// tree with a jump table on the host core:
//   clang -O3 -o p6_tree p6_dispatch_model.c   (Apple clang emits a tree)
//   clang -O3 -mllvm -aarch64-min-jump-table-entries=4 -o p6_jt p6_dispatch_model.c

#include <stdint.h>
#include <stdlib.h>
static inline uint64_t rotl(uint64_t x, unsigned r){ r&=63; return (x<<r)|(x>>((64-r)&63)); }
int main(int argc, char**argv){
  volatile uint64_t vs = 88172645463325252ull, va = 0, vn = 200000000ull;
  uint64_t s = vs, acc = va, n = vn;
  for (uint64_t i = 0; i < n; i++) {
    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
    switch (s % 7) {
      case 0: acc += s; break;
      case 1: acc ^= s; break;
      case 2: acc *= (s|1); break;
      case 3: acc = rotl(acc, (unsigned)(s & 63)); break;
      case 4: acc -= (s >> 5); break;
      case 5: acc += s >> (s & 31); break;
      default: acc += s ^ (acc >> 11); break;
    }
  }
  exit((int)(acc % 126));
}
