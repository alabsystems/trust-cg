#include <stdint.h>
#include <stddef.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

uint64_t variadic_words(uint32_t count, ...) {
    va_list ap;
    va_start(ap, count);
    uint64_t result = UINT64_C(0xd391546cdf84359a);
    for (uint32_t i = 0; i < count; ++i)
        result = (result ^ va_arg(ap, uint64_t)) * UINT64_C(0x9e3779b97f4a7c15);
    va_end(ap);
    return result;
}
uint64_t variadic_mixed(uint64_t tag, ...) {
    va_list ap;
    va_start(ap, tag);
    int a = va_arg(ap, int);
    double b = va_arg(ap, double);
    const uint64_t *ptr = va_arg(ap, const uint64_t *);
    uint64_t bits;
    memcpy(&bits, &b, sizeof(bits));
    va_end(ap);
    return tag ^ (uint64_t)(int64_t)a ^ bits ^ *ptr;
}

double variadic_floats(uint32_t count, ...) {
    va_list ap; va_start(ap,count); double r=0;
    for (unsigned i=0;i<count;++i) r += (i+1) * va_arg(ap,double);
    va_end(ap); return r;
}
uint64_t variadic_cross(uint32_t count, ...) {
    va_list ap; va_start(ap,count); uint64_t r=31;
    for (unsigned i=0;i<count;++i) {
        uint64_t a=va_arg(ap,uint64_t); double b=va_arg(ap,double); uint64_t bits;
        memcpy(&bits,&b,sizeof bits); r=(r ^ a ^ bits)*UINT64_C(0x9e3779b97f4a7c15);
    }
    r ^= (uint64_t)(int64_t)va_arg(ap,int); va_end(ap); return r;
}
uint64_t variadic_fixed(uint64_t a, uint64_t b, uint64_t c, uint64_t d,
                       uint64_t e, uint64_t f, uint64_t g, uint32_t count, ...) {
    uint64_t r=a+3*b+5*c+7*d+11*e+13*f+17*g;
    va_list ap; va_start(ap,count);
    for (unsigned i=0;i<count;++i) r=(r ^ va_arg(ap,uint64_t))*UINT64_C(0x9e3779b97f4a7c15);
    va_end(ap); return r;
}
double variadic_fixed_float(float a, double b, uint32_t count, ...) {
    double r=(double)a+3*b; va_list ap; va_start(ap,count);
    for (unsigned i=0;i<count;++i) r += (i+1)*va_arg(ap,double);
    va_end(ap); return r;
}
uint64_t variadic_promoted(uint32_t tag, ...) {
    va_list ap; va_start(ap,tag);
    uint64_t r=tag;
    r += 3*(uint64_t)(int64_t)va_arg(ap,int);
    r += 5*(uint64_t)va_arg(ap,unsigned);
    r += 7*(uint64_t)va_arg(ap,int64_t);
    r += 11*va_arg(ap,uint64_t);
    r += 13*(uint64_t)va_arg(ap,intptr_t);
    r += 17*(uint64_t)va_arg(ap,uintptr_t);
    r += 19*(*va_arg(ap,const uint64_t *));
    va_end(ap); return r;
}
extern uint64_t call_words(uint64_t, uint64_t);
extern uint64_t call_empty(void);
extern uint64_t call_mixed(int32_t, double, const uint64_t *);
extern uint64_t call_spill(uint64_t);
extern uint64_t call_pointer_empty(uint64_t (*)(uint32_t, ...));
static void check(uint64_t actual, uint64_t expected, unsigned seed, const char *label) {
    if (actual != expected) {
        fprintf(stderr, "%s seed=%u actual=%llu expected=%llu\n", label, seed,
                (unsigned long long)actual, (unsigned long long)expected);
        exit(1);
    }
}
extern double call_floats(double);
extern uint64_t call_cross(uint64_t,double);
extern uint64_t call_fixed(uint64_t,uint64_t);
extern double call_fixed_float(float,double);
extern uint64_t call_promoted(int32_t,uint32_t,int64_t,uint64_t,intptr_t,uintptr_t,const uint64_t *);
extern _Bool call_libc(void);
static void check_double(double actual, double expected, unsigned seed, const char *label) {
    if (actual != expected) { fprintf(stderr,"%s seed=%u actual=%.17g expected=%.17g\n",label,seed,actual,expected); exit(1); }
}
int variadic_driver(void) {
    unsigned checks = 0;
    for (unsigned seed = 0; seed < 4096; ++seed) {
        uint64_t a = seed * UINT64_C(0xf00e00d00c00b00a);
        uint64_t b = ~a;
        uint64_t expected = UINT64_C(0xd391546cdf84359a);
        expected = (expected ^ a) * UINT64_C(0x9e3779b97f4a7c15);
        expected = (expected ^ b) * UINT64_C(0x9e3779b97f4a7c15);
        check(call_words(a,b), expected, seed, "words"); ++checks;
        check(call_pointer_empty(variadic_words), UINT64_C(0xd391546cdf84359a), seed, "pointer-empty"); ++checks;
        check(call_empty(), UINT64_C(0xd391546cdf84359a), seed, "empty"); ++checks;
        expected = UINT64_C(0xd391546cdf84359a);
        for (unsigned i = 0; i < 10; ++i)
            expected = (expected ^ (a+i)) * UINT64_C(0x9e3779b97f4a7c15);
        check(call_spill(a), expected, seed, "spill"); ++checks;
        double d = (double)seed * 0.25 - 700.125;
        uint64_t bits;
        memcpy(&bits, &d, sizeof(bits));
        int32_t signed_word = (int32_t)seed - 2048;
        check(call_mixed(signed_word,d,&b), UINT64_C(17) ^ (uint64_t)(int64_t)signed_word ^ bits ^ b, seed, "mixed"); ++checks;
        double sum=0;
        for (unsigned i=0;i<10;++i) sum += (i+1)*(d+i);
        check_double(call_floats(d),sum,seed,"floats"); ++checks;
        expected=31;
        for (unsigned i=0;i<10;++i) { double x=d+i; memcpy(&bits,&x,sizeof bits); expected=(expected ^ (a+i) ^ bits)*UINT64_C(0x9e3779b97f4a7c15); }
        expected ^= (uint64_t)(int64_t)-17;
        check(call_cross(a,d),expected,seed,"cross"); ++checks;
        expected=a+3*b+5*(a^b)+7*(~a)+11*(~b)+13*(a+b)+17*(a-b);
        expected=(expected ^ b)*UINT64_C(0x9e3779b97f4a7c15);
        expected=(expected ^ a)*UINT64_C(0x9e3779b97f4a7c15);
        expected=(expected ^ (a^17))*UINT64_C(0x9e3779b97f4a7c15);
        check(call_fixed(a,b),expected,seed,"fixed"); ++checks;
        float fa=(float)seed*0.5f-91.25f; sum=(double)fa+3*d;
        for (unsigned i=0;i<8;++i) sum += (i+1)*(d+i+1);
        check_double(call_fixed_float(fa,d),sum,seed,"fixed-float"); ++checks;
        int64_t si=(int64_t)seed-2147483649LL; intptr_t ip=(intptr_t)seed-70000;
        uint32_t ui=UINT32_MAX-seed;
        expected=19+3*(uint64_t)(int64_t)signed_word+5*(uint64_t)ui+7*(uint64_t)si+11*a+13*(uint64_t)ip+17*(uintptr_t)b+19*b;
        check(call_promoted(signed_word,ui,si,a,ip,(uintptr_t)b,&b),expected,seed,"promoted"); ++checks;
    }
    check(call_libc(),1,0,"libc"); ++checks;
    printf("PASS variadic_call checks=%u\n", checks);
    return 0;
}
