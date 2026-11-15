#include <stdint.h>
#include <stdarg.h>
#include <stdio.h>
uint64_t variadic_write(uint32_t tag, ...) {
    va_list ap;va_start(ap,tag);uint64_t *p=va_arg(ap,uint64_t*);
    uint64_t x=va_arg(ap,uint64_t);*p=(*p ^ x)+tag;va_end(ap);return x*13;
}
uint64_t variadic_ref(uint64_t *p, ...) {
    va_list ap;va_start(ap,p);uint64_t x=va_arg(ap,uint64_t);
    *p=(*p ^ x)+19;va_end(ap);return x*17;
}
extern uint64_t call_write(uint64_t);
extern uint64_t call_ref(uint64_t*,uint64_t);
int variadic_driver(void) {
    for(unsigned i=0;i<4096;i++) {
        uint64_t a=i*UINT64_C(0xf00e00d00c00b00a),b=(a<<17)|(a>>47);
        if(call_write(a)!=(((a^b)+11)^(b*13)))return 1;
        uint64_t value=a,actual=call_ref(&value,b);
        if(actual!=(((a^b)+19)^(b*17)) || value!=(a^b)+19)return 2;
    }
    puts("PASS variadic_mutation checks=12288");return 0;
}
