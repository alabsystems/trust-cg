#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
extern uint64_t exercise(uint64_t,uint32_t);
int main(void) {
    const uint64_t values[]={0,1,2,7,UINT64_MAX,UINT64_C(0x8000000000000000),UINT64_C(0x123456789abcdef0)};
    uint64_t state=UINT64_C(0x1729abcdef456789),checks=0;
    for(unsigned i=0;i<263;++i) {
        state^=state<<13;state^=state>>7;state^=state<<17;
        uint64_t value=i<7?values[i]:state;
        for(uint32_t mode=0;mode<8;++mode) {
            uint64_t wanted=0;
            switch(mode){case 0:case 3:wanted=value;break;case 1:wanted=(value%3)-1;break;case 2:wanted=5;break;case 4:wanted=value^0x101;break;case 5:wanted=value+7;break;case 6:wanted=((value%3)-1)^((value&1)?0x42:0);break;case 7:wanted=value+9;break;}
            uint64_t actual=exercise(value,mode);
            if(actual!=wanted){fprintf(stderr,"ControlFlow case=%u mode=%u got=%"PRIu64" expected=%"PRIu64"\n",i,mode,actual,wanted);return 1;}
            ++checks;
        }
    }
    printf("PASS control_flow checks=%"PRIu64"\n",checks);return 0;
}
