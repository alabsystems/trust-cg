extern unsigned long tcg_get(void), tcg_get_z(void);
void _start(void) { unsigned long a = tcg_get(), z = tcg_get_z(); long code = (a == 42 && z == 0) ? 0 : (a == 0 ? 50 : 1);
  register long x0 __asm__("x0") = code; register long x8 __asm__("x8") = 93; __asm__ volatile("svc 0" :: "r"(x0), "r"(x8)); for (;;); }
