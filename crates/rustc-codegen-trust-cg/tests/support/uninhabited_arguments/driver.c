#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
extern uint64_t live_path(uint64_t);
extern uint64_t inhabited_zsts(uint64_t);
extern uint64_t more_inhabited(uint64_t);
extern uint64_t tagged_neighbor(uint64_t);
int main(void) {
    const uint64_t values[]={0,1,2,7,UINT64_MAX,UINT64_C(0x8000000000000000),UINT64_C(0x123456789abcdef0)};
    uint64_t state=UINT64_C(0x1729abcdef456789),checks=0;
    for(unsigned i=0;i<263;++i) {
        state^=state<<13;state^=state>>7;state^=state<<17;
        uint64_t value=i<7?values[i]:state;
        uint64_t wanted=value;
        for(unsigned k=0;k<4;++k) wanted=wanted*3+k;
        uint64_t actual=live_path(value);
        if(actual!=wanted){fprintf(stderr,"live path case=%u got=%"PRIu64" expected=%"PRIu64"\n",i,actual,wanted);return 1;}
        ++checks;
        if(inhabited_zsts(value)!=value+41){fprintf(stderr,"inhabited zsts case=%u\n",i);return 2;}
        ++checks;
        if(more_inhabited(value)!=value+71){fprintf(stderr,"inhabited union case=%u\n",i);return 3;}
        ++checks;
        if(tagged_neighbor(value)!=((value&1)?value+31:7)){fprintf(stderr,"tagged neighbor case=%u\n",i);return 4;}
        ++checks;
    }
    printf("PASS uninhabited_arguments checks=%"PRIu64"\n",checks);return 0;
}
