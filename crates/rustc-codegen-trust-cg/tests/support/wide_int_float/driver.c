#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 U;
typedef __int128 I;
extern float wide_s32(I); extern double wide_s64(I);
extern float wide_u32(U); extern double wide_u64(U);
struct Results { float s32, u32; double s64, u64, saved; uint64_t word; };
extern uint64_t wide_pressure(I,U,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,double,struct Results*);
static float (*volatile s32p)(I)=wide_s32;
static double (*volatile s64p)(I)=wide_s64;
static float (*volatile u32p)(U)=wide_u32;
static double (*volatile u64p)(U)=wide_u64;
static uint64_t cases, checks, observations;
static uint32_t fbits(float f) { uint32_t u; memcpy(&u,&f,4); return u; }
static uint64_t dbits(double f) { uint64_t u; memcpy(&u,&f,8); return u; }
static double from_bits(uint64_t u) { double f; memcpy(&f,&u,8); return f; }
uint64_t wide_float_observe(uint64_t word, double saved) {
    observations++;
    return word ^ dbits(saved) ^ UINT64_C(0x5367bc6eacf0d843);
}
// An integer-only IEEE round-to-nearest, ties-to-even oracle. No integer-to-
// float casts or floating arithmetic occur here, avoiding a shared libcall oracle.
static uint64_t ieee(U magnitude, unsigned negative, unsigned precision) {
    if (!magnitude) return 0;
    uint64_t hi=(uint64_t)(magnitude>>64), lo=(uint64_t)magnitude;
    unsigned exponent=hi ? 127-__builtin_clzll(hi) : 63-__builtin_clzll(lo);
    U significand;
    if (exponent < precision) {
        significand=magnitude << (precision-1-exponent);
    } else {
        unsigned shift=exponent-(precision-1);
        significand=magnitude>>shift;
        U half=(U)1<<(shift-1), remainder=magnitude&(((U)1<<shift)-1);
        if (remainder>half || (remainder==half && (significand&1))) significand++;
        if (significand==((U)1<<precision)) { significand>>=1; exponent++; }
    }
    unsigned bias=precision==24 ? 127 : 1023;
    unsigned sign_shift=precision==24 ? 31 : 63;
    return ((uint64_t)negative<<sign_shift) |
        ((uint64_t)(exponent+bias)<<(precision-1)) |
        ((uint64_t)significand&(((uint64_t)1<<(precision-1))-1));
}
static void check(uint64_t actual,uint64_t expected,const char *kind,U x) {
    checks++;
    if (actual!=expected) {
        fprintf(stderr,"%s x=%016llx%016llx actual=%016llx expected=%016llx\n",kind,
            (unsigned long long)(x>>64),(unsigned long long)x,
            (unsigned long long)actual,(unsigned long long)expected);
        exit(1);
    }
}
static void value(U x) {
    cases++;
    I sx; memcpy(&sx,&x,16);
    unsigned negative=(unsigned)(x>>127);
    U magnitude=negative ? (U)0-x : x;
    uint64_t s32=ieee(magnitude,negative,24),s64=ieee(magnitude,negative,53);
    uint64_t u32=ieee(x,0,24),u64=ieee(x,0,53);
    check(fbits(wide_s32(sx)),s32,"direct s32",x);
    check(dbits(wide_s64(sx)),s64,"direct s64",x);
    check(fbits(wide_u32(x)),u32,"direct u32",x);
    check(dbits(wide_u64(x)),u64,"direct u64",x);
    check(fbits(s32p(sx)),s32,"indirect s32",x);
    check(dbits(s64p(sx)),s64,"indirect s64",x);
    check(fbits(u32p(x)),u32,"indirect u32",x);
    check(dbits(u64p(x)),u64,"indirect u64",x);
    uint64_t lo=(uint64_t)x,hi=(uint64_t)(x>>64);
    uint64_t a=lo,b=hi,c=~lo,d=hi+7,e=lo^31,f=hi*37;
    uint64_t saved_bits=UINT64_C(0x3fd0000000000000)|(lo&UINT64_C(0x000fffffffffffff));
    double saved=from_bits(saved_bits);
    U y=(x<<17)|(x>>111);
    uint64_t word=a^b^c^d^e^f^saved_bits^UINT64_C(0x5367bc6eacf0d843)^hi^(uint64_t)y^(uint64_t)(y>>64);
    struct Results out;
    memset(&out,0xA5,sizeof(out));
    uint64_t returned=wide_pressure(sx,y,a,b,c,d,e,f,saved,&out);
    check(fbits(out.s32),s32,"pressure s32",x);
    check(dbits(out.s64),s64,"pressure s64",x);
    check(fbits(out.u32),ieee(y,0,24),"pressure u32",x);
    check(dbits(out.u64),ieee(y,0,53),"pressure u64",x);
    check(dbits(out.saved),saved_bits,"preserved float",x);
    check(out.word,word,"preserved integer",x);
    check(returned,word,"returned integer",x);
}
int main(void) {
    U fixed[]={0,1,~(U)0,(U)1<<127,((U)1<<127)-1,((U)1<<64)+1,((U)1<<100)+7,((U)1<<80)-1};
    for (unsigned i=0;i<sizeof(fixed)/sizeof(fixed[0]);i++) value(fixed[i]);
    for (unsigned i=0;i<65536;i++) { value(i); value((U)0-i); }
    for (unsigned e=0;e<128;e++) for (int d=-4;d<=4;d++) value(((U)1<<e)+(U)d);
    for (unsigned which=0;which<2;which++) {
        unsigned p=which==0 ? 24 : 53;
        U edge=(U)1<<(p-1);
        U offsets[]={0,1,2,3,edge-4,edge-3,edge-2,edge-1};
        for (unsigned e=p;e<128;e++) for (unsigned j=0;j<8;j++) {
            unsigned shift=e-(p-1);
            U midpoint=((edge+offsets[j])<<shift)+((U)1<<(shift-1));
            value(midpoint-1); value(midpoint); value(midpoint+1);
        }
    }
    uint64_t state=UINT64_C(0x1f34d7065b28e9ca);
    for (unsigned i=0;i<16384;i++) {
        state^=state<<13; state^=state>>7; state^=state<<17; uint64_t hi=state;
        state^=state<<13; state^=state>>7; state^=state<<17;
        value(((U)hi<<64)|state);
    }
    check(observations,cases,"callback count",0);
    printf("PASS wide_int_float values=%llu checks=%llu\n",(unsigned long long)cases,(unsigned long long)checks);
    return 0;
}
