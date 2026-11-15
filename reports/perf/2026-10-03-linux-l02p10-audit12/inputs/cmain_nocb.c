#include <stdio.h>
extern unsigned long tcg_get(void), tcg_bump(void), tcg_call(void), tcg_tls_bump(void), tcg_cb(void), tcg_cword(void);
int main(void)
{
    unsigned long a = tcg_get(), b = tcg_bump(), c = tcg_call(), d = tcg_tls_bump(), e = tcg_cb(), f = tcg_cword();
    int ok = a == 42 && b == 43 && c == 43 && d == 8 && e == 10 && f == 1000;
    printf("v=%s a=%lu b=%lu c=%lu d=%lu e=%lu f=%lu\n", ok ? "OK" : "BAD", a, b, c, d, e, f);
    return ok ? 0 : 1;
}
