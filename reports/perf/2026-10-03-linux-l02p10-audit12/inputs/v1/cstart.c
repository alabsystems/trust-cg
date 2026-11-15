extern __thread unsigned long tcg_t __attribute__((tls_model("local-exec")));
extern __thread unsigned long tcg_tz __attribute__((tls_model("local-exec")));
static void sys_exit(long c) {
  register long x0 asm("x0") = c;
  register long x8 asm("x8") = 94;
  asm volatile("svc 0" : : "r"(x0), "r"(x8) : "memory");
  for (;;) {}
}
void _start(void) { sys_exit(tcg_t == 42 && tcg_tz == 0 ? 0 : (tcg_t == 0 ? 3 : 4)); }
