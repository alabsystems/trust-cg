/* One driver for the two local scalar-cell control sources: a
 * 16-byte-aligned single-f64 record (CELL_ALIGN 16, `overaligned_cell`, a
 * required refusal of `rejected_boundaries` under certificates) and an f64
 * with a trailing zero-sized field (CELL_ALIGN 8, `zst_sibling_cell`, the
 * required promoted positive `zst_sibling_cell_promoted`). Each function
 * stores -21.5 into a local record, passes its address to c_change and
 * returns the field. */
#include <stdint.h>
#include <stdio.h>

#ifndef CELL
#error "define CELL to the function name"
#endif
#ifndef CELL_ALIGN
#error "define CELL_ALIGN to the record's alignment"
#endif

typedef struct { _Alignas(CELL_ALIGN) double value; } Record;

static unsigned long calls, misaligned, unseeded;

void c_change(Record *p, double value) {
    calls++;
    if ((uintptr_t)p % CELL_ALIGN) misaligned++;
    if (p->value != -21.5) unseeded++;
    p->value = p->value * value + 0.25;
}

double CELL(double value);

int main(void) {
    unsigned long checks = 0;
    for (int i = -2000; i <= 2000; i++) {
        double value = i * 0.375 - 0.0625;
        double got = CELL(value), want = -21.5 * value + 0.25;
        if (got != want) {
            printf("MISMATCH i=%d got=%a want=%a\n", i, got, want);
            return 1;
        }
        checks++;
    }
    printf("PASS cell checks=%lu calls=%lu misaligned=%lu unseeded=%lu\n", checks, calls,
           misaligned, unseeded);
    return 0;
}
