#include <stdint.h>
#include <stdarg.h>
#include <stdio.h>
struct Pair {uint64_t a,b;};
uint64_t ref_shared(uint32_t tag,...) {
    va_list ap;va_start(ap,tag);const int32_t *p=va_arg(ap,const int32_t *);
    uint64_t r=(uint64_t)(int64_t)*p ^ tag;va_end(ap);return r;
}
uint64_t ref_write(uint32_t tag,...) {
    va_list ap;va_start(ap,tag);uint64_t *p=va_arg(ap,uint64_t *);uint64_t b=va_arg(ap,uint64_t);
    *p=(*p^b)+tag;va_end(ap);return b*13;
}
uint64_t ref_pair(uint32_t tag,...) {
    va_list ap;va_start(ap,tag);struct Pair *p=va_arg(ap,struct Pair *);uint64_t x=va_arg(ap,uint64_t);
    p->a=(p->a^x)+tag;p->b=(p->b+x)*17;va_end(ap);return x*19;
}
uint64_t ref_cell(uint32_t tag,...) {
    va_list ap;va_start(ap,tag);uint64_t *p=va_arg(ap,uint64_t *);uint64_t b=va_arg(ap,uint64_t);
    *p=(*p^b)+tag;va_end(ap);return b*13;
}

uint64_t ref_identity(uint32_t tag,...) {
    va_list ap;va_start(ap,tag);const uint64_t *a=va_arg(ap,const uint64_t*);
    const uint64_t *b=va_arg(ap,const uint64_t*);va_end(ap);return a==b ? tag : UINT64_MAX;
}
uint64_t ref_many(uint32_t count,...) {
    va_list ap;va_start(ap,count);
    for(unsigned i=0;i<count;i++){uint64_t *p=va_arg(ap,uint64_t*);*p=(*p^UINT64_C(0xd3547a6312))+i;}
    va_end(ap);return 0;
}
extern uint64_t identity(uint64_t),many(uint64_t);

uint64_t ref_pair_identity(uint32_t tag,...) {
    va_list ap;va_start(ap,tag);const struct Pair *a=va_arg(ap,const struct Pair*);
    const struct Pair *b=va_arg(ap,const struct Pair*);va_end(ap);return a==b ? tag : UINT64_MAX;
}
extern uint64_t identity_pair(uint64_t,uint64_t),identity_projected(uint64_t,uint64_t),identity_branch(uint64_t,uint64_t,_Bool);
extern uint64_t shared(int32_t),promoted(void),mutate(uint64_t,uint64_t),forward(uint64_t*,uint64_t);
extern uint64_t pair_local(uint64_t,uint64_t,uint64_t),pair_forward(struct Pair*,uint64_t),cell(uint64_t,uint64_t);
int variadic_driver(void) {
    for(unsigned i=0;i<4096;i++) {
        uint64_t a=i*UINT64_C(0xf00e00d00c00b00a),b=~a,x=a^UINT64_C(0x731245786b);
        if(shared((int32_t)i-2048)!=((uint64_t)(int64_t)((int32_t)i-2048)^17))return 1;
        if(promoted()!=((uint64_t)(int64_t)-19^17))return 2;
        if(mutate(a,b)!=(((a^b)+23)^(b*13)))return 3;
        uint64_t v=a;if(forward(&v,b)!=(((a^b)+23)^(b*13)) || v!=(a^b)+23)return 4;
        uint64_t pa=(a^x)+31,pb=(b+x)*17;
        if(pair_local(a,b,x)!=(pa^pb^(x*19)))return 5;
        struct Pair p={a,b};if(pair_forward(&p,x)!=(pa^pb^(x*19)) || p.a!=pa || p.b!=pb)return 6;
        if(cell(a,b)!=(((a^b)+37)^(b*13)))return 7;
        if(identity(a)!=0)return 8;
        uint64_t expected=31;
        for(unsigned j=0;j<10;j++)expected=(expected^(((a+j)^UINT64_C(0xd3547a6312))+j))*UINT64_C(0x9e3779b97f4a7c15);
        if(many(a)!=expected)return 9;
        if(identity_pair(a,b)!=0)return 10;
        if(identity_projected(a,b)!=0)return 11;
        if(identity_branch(a,b,i&1)!=0)return 12;
    }
    puts("PASS variadic_reference checks=61440");return 0;
}
