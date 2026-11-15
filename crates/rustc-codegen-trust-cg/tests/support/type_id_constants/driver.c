#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h>
struct Mixed { uint64_t id[2]; const uint64_t *pointer; };
extern const uint64_t U64_ID[2], VALUE;
extern const struct Mixed MIXED;
extern const struct Mixed * const PROMOTED_REF;
extern const void *low_word(void);
extern const void *high_word(void);
extern uint64_t compare_ids(uint32_t,uint32_t);
extern void id_words(uint32_t,uint64_t *);
extern uint64_t static_check(uint32_t);
int main(void) {
    uint64_t ids[8][2],checks=0;
    for(uint32_t a=0;a<8;++a) {
        struct { uint64_t before, words[2], after; } v={UINT64_MAX,{0,0},17};
        id_words(a,v.words);
        if(v.before!=UINT64_MAX || v.after!=17)return 1;
        ids[a][0]=v.words[0];ids[a][1]=v.words[1];
        printf("ID %u %016"PRIx64" %016"PRIx64"\n",a,ids[a][0],ids[a][1]);
        checks+=2;
    }
    for(uint32_t a=0;a<8;++a)for(uint32_t b=0;b<8;++b) {
        uint64_t wanted=a==b;
        if(compare_ids(a,b)!=wanted || ((ids[a][0]==ids[b][0] && ids[a][1]==ids[b][1])!=(a==b)))return 2;
        checks+=2;
    }
    for(uint32_t m=0;m<8;++m) {
        uint64_t wanted=m==3 || m==4?UINT64_C(0x9876543210123456):m==7?0:1;
        if(static_check(m)!=wanted){fprintf(stderr,"static TypeId mode %u mismatch\n",m);return 3;}
        ++checks;
    }
    if(memcmp(U64_ID,ids[1],16) || memcmp(MIXED.id,ids[5],16) ||
       memcmp(PROMOTED_REF->id,ids[0],16) || MIXED.pointer!=&VALUE ||
       PROMOTED_REF->pointer!=&VALUE || *MIXED.pointer!=UINT64_C(0x9876543210123456) ||
       *PROMOTED_REF->pointer!=UINT64_C(0x9876543210123456))return 4;
    checks+=10;
    if((uint64_t)(uintptr_t)low_word()!=ids[1][0] || (uint64_t)(uintptr_t)high_word()!=ids[1][1])return 5;
    checks+=2;
    printf("PASS type_id checks=%"PRIu64"\n",checks);
    return 0;
}
