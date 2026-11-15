#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
extern int32_t shared(const int32_t *);
extern int32_t mutable(int32_t *);
extern uint64_t owned(uint64_t);
extern uint64_t owned_mut(uint64_t);
extern int32_t nested(const int32_t *);
extern int32_t nested_mut(int32_t *);
int main(void) {
    const uint32_t values[]={0,1,2,7,UINT32_MAX,UINT32_C(0x80000000),UINT32_C(0x1234abcd)};
    uint64_t state=UINT64_C(0x1729abcdef456789),checks=0;
    for(unsigned i=0;i<263;++i) {
        state^=state<<13;state^=state>>7;state^=state<<17;
        uint32_t value=i<7?values[i]:(uint32_t)state;
        struct { uint32_t before; int32_t value; uint32_t after; } data={0x51ad,0,0xfa32};
        memcpy(&data.value,&value,4);
        uint32_t read=(uint32_t)shared(&data.value);
        if(read!=value || (uint32_t)data.value!=value) { fprintf(stderr,"shared case=%u got=%"PRIu32" expected=%"PRIu32"\n",i,read,value);return 1; }
        uint32_t want=value+7,changed=(uint32_t)mutable(&data.value);
        if(changed!=want || (uint32_t)data.value!=want || data.before!=0x51ad || data.after!=0xfa32) { fprintf(stderr,"mutable case=%u got=%"PRIu32" stored=%"PRIu32" expected=%"PRIu32"\n",i,changed,(uint32_t)data.value,want);return 1; }
        uint64_t wide=i<7?(uint64_t)value:state;
        uint64_t first=wide*9+17,second=first*9+17;
        if(owned(wide)!=first || owned_mut(wide)!=second) {fprintf(stderr,"owned case=%u\n",i);return 1;}
        if((uint32_t)nested(&data.value)!=want || (uint32_t)data.value!=want) {fprintf(stderr,"nested case=%u\n",i);return 1;}
        want+=7;
        if((uint32_t)nested_mut(&data.value)!=want || (uint32_t)data.value!=want || data.before!=0x51ad || data.after!=0xfa32) {fprintf(stderr,"nested mutable case=%u\n",i);return 1;}
        checks+=14;
    }
    printf("PASS closure_wrappers checks=%"PRIu64"\n",checks);return 0;
}
