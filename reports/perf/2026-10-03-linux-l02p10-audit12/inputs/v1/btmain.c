#include <execinfo.h>
#include <stdio.h>
extern unsigned long tcg_get(void);
int main(void) {
  void *frames[16];
  unsigned long v = tcg_get();
  int n = backtrace(frames, 16);
  printf("v=%lu frames=%d\n", v, n);
  return v == 42 && n > 0 ? 0 : 1;
}
