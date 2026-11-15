#include <stdint.h>
#include <stdarg.h>
uint64_t variadic_callback(uint64_t (*callback)(uint64_t), uint32_t tag, ...) {
    va_list ap;
    va_start(ap, tag);
    uint64_t value = va_arg(ap, uint64_t);
    va_end(ap);
    return callback(value) ^ tag;
}
