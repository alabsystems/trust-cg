extern unsigned long tcg_tls_get(void), tcg_tls_get_z(void);
static void sys_exit(long c) {
  register long x0 asm("x0") = c;
  register long x8 asm("x8") = 94;
  asm volatile("svc 0" : : "r"(x0), "r"(x8) : "memory");
  for (;;) {}
}
/* Exit status: tcg_tls_get_z() (trust-cg's zero-initialized thread-local), low byte; 0 when correct. */
void _start(void) {
  unsigned long a = tcg_tls_get(), z = tcg_tls_get_z();
  sys_exit(a != 42 ? 200 : (long)(z & 0xff));
}
