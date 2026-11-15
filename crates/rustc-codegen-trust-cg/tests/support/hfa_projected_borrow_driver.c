#include <stdint.h>
#include <stdio.h>

typedef struct { double value; } Inner;
typedef struct { Inner inner; } Outer;

static unsigned long change_calls, leaf_calls, aliased;
static const void *seen_outer;

/* c_change sees the whole by-value HFA formal by address; c_change_leaf sees
 * its nested leaf. Both must reach the one storage the callee then reads. */
void c_change(Outer *p, double value) {
    change_calls++;
    seen_outer = p;
    p->inner.value = p->inner.value * 3.0 + value;
}
void c_change_leaf(double *p, double value) {
    leaf_calls++;
    if ((const void *)p == seen_outer) aliased++;
    *p = *p - value * 0.5;
}

double projected_borrow(Outer a, double value);

int main(void) {
    unsigned long checks = 0;
    for (int i = -300; i <= 300; i++) {
        for (int j = -40; j <= 40; j++) {
            Outer a = {{i * 0.375 + 0.125}};
            double value = j * 1.25 - 0.0625;
            double got = projected_borrow(a, value);
            double want = (a.inner.value * 3.0 + value) - value * 0.5;
            if (got != want) {
                printf("MISMATCH i=%d j=%d got=%a want=%a\n", i, j, got, want);
                return 1;
            }
            checks++;
        }
    }
    printf("PASS projected_borrow checks=%lu change=%lu leaf=%lu aliased=%lu\n", checks,
           change_calls, leaf_calls, aliased);
    return 0;
}
