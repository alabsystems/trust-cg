#include <stdint.h>
#include <stdarg.h>
struct Record {uint64_t a,b,*out;};
uint64_t reference_callback(uint64_t(*cb)(uint64_t),uint32_t tag,...) {
    va_list ap;va_start(ap,tag);struct Record *p=va_arg(ap,struct Record*);
    uint64_t x=va_arg(ap,uint64_t);va_end(ap);
    p->a=(p->a^x)+tag;p->b=(p->b+x)*17;
    return cb(x);
}
