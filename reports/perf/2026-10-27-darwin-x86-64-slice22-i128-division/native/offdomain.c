// Informational: the two bindings at trust-ir's undefined signed input MIN / -1
// (no zero divisor: compiler_builtins makes it unreachable(), compiler-rt traps).
#include <stdio.h>
typedef __int128 i128;
i128 __divti3(i128, i128);
i128 __modti3(i128, i128);
#ifdef CB_LINK
#include <stdlib.h>
void rust_eh_personality(void) { abort(); }
#endif
static i128 (*volatile D)(i128, i128) = __divti3;
static i128 (*volatile M)(i128, i128) = __modti3;
int main(void) {
    i128 min = (i128)((unsigned __int128)1 << 127);
    i128 q = D(min, -1), r = M(min, -1);
    printf("MIN/-1 = %s, MIN%%-1 = %lld\n", q == min ? "MIN (wraps)" : "other", (long long)r);
    return 0;
}
