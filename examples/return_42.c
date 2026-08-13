#include <stdio.h>

extern long _return_42(void);

int main(void) {
    long result = _return_42();
    printf("%ld\n", result);
    return result == 42 ? 0 : 1;
}
