#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
struct Header { uint64_t tag, count, data[4]; };
struct Nested { uint64_t prefix; struct Header inner; uint64_t padding; };
extern uint64_t exercise(struct Nested *, size_t, uint64_t, uint32_t);
extern uint64_t shape_probe(uint8_t *, size_t, uint32_t);
int main(void) {
    const uint64_t values[] = {0, 1, 17, UINT64_C(0x1020304050607080), UINT64_MAX};
    uint64_t checks = 0;
    for (unsigned a=0; a<5; ++a) for (unsigned b=0; b<5; ++b)
    for (unsigned s=0; s<5; ++s) for (size_t len=0; len<=4; ++len)
    for (uint32_t mode=0; mode<14; ++mode) {
        _Alignas(16) struct { uint64_t before[2]; struct Nested value; uint64_t after[2]; } box = {
            {UINT64_C(0x3141592653589793),UINT64_C(0x445566778899aabb)},
            {UINT64_C(0xaabbccddeeff0011),{values[a],values[b],
             {0,1,UINT64_MAX,UINT64_C(0x9080706050403020)}},UINT64_C(0x123456789abcdef0)},
            {UINT64_C(0x2718281828459045),UINT64_C(0xffeeddccbbaa9988)}};
        struct Nested expected=box.value;
        uint64_t salt=values[s], result=0;
        switch(mode) {
            case 0: result=expected.inner.tag+expected.inner.count;break;
            case 1: case 7:result=len;break;
            case 2:result=(24+len*8+15)&~UINT64_C(15);break;
            case 3:result=16;break;
            case 4:for(size_t i=0;i<len;++i)result+=expected.inner.data[i];break;
            case 5:expected.inner.count^=salt;result=expected.inner.count;break;
            case 6:
                expected.inner.tag+=salt;expected.inner.count^=salt;
                result=expected.inner.tag+expected.inner.count;
                for(size_t i=0;i<len;++i){expected.inner.data[i]+=salt;result+=expected.inner.data[i];}
                break;
            case 8:
                if(len){expected.inner.data[len-1]^=salt;result=expected.inner.data[len-1];}else result=salt;
                break;
            case 9:result=64;break;
            case 10:result=4;break;
            case 11: case 12:
                result=salt;
                for(unsigned turn=0;turn<(mode==11?1:3);++turn)
                    for(size_t i=0;i<len;++i)result-=expected.inner.data[i];
                break;
            case 13:
                result=salt;
                for(size_t i=0;i<len;++i)result=result*3+(expected.inner.data[i]^salt);
                break;
        }
        uint64_t actual=exercise(&box.value,len,salt,mode);
        if(actual!=result || memcmp(&box.value,&expected,sizeof(expected)) ||
           box.before[0]!=UINT64_C(0x3141592653589793) || box.before[1]!=UINT64_C(0x445566778899aabb) ||
           box.after[0]!=UINT64_C(0x2718281828459045) || box.after[1]!=UINT64_C(0xffeeddccbbaa9988)) {
            fprintf(stderr,"DST mismatch a=%u b=%u s=%u len=%zu mode=%u got=%"PRIu64" expected=%"PRIu64"\n",a,b,s,len,mode,actual,result);
            return 1;
        }
        checks+=13;
    }
    for (uint32_t kind=0;kind<4;++kind) for (size_t len=0;len<=4;++len) {
        _Alignas(16) struct { uint64_t before[2]; uint8_t bytes[32]; uint64_t after[2]; } box = {
            {UINT64_C(0x123456789abcdef0),UINT64_MAX}, {0}, {17,UINT64_C(0xabcdef0123456789)}};
        for(unsigned i=0;i<32;++i)box.bytes[i]=(uint8_t)(65+i);
        box.bytes[0]=0x42;
        uint8_t expected[32];memcpy(expected,box.bytes,32);
        uint64_t size=kind==1?4+4*len:kind==2?1:1+len;
        uint64_t align=kind==1?4:1,last=0;
        if(len && kind==0){expected[len]=(uint8_t)(expected[len]+0x42);last=expected[len];}
        if(len && kind==1){uint32_t word;memcpy(&word,&expected[4*len],4);word+=0x42;memcpy(&expected[4*len],&word,4);last=word&255;}
        if(len && kind==3)last=expected[len];
        uint64_t wanted=(size<<32)|(align<<16)|(last<<8)|len;
        uint64_t got=shape_probe(box.bytes,len,kind);
        if(got!=wanted || memcmp(box.bytes,expected,32) || box.before[0]!=UINT64_C(0x123456789abcdef0) ||
           box.before[1]!=UINT64_MAX || box.after[0]!=17 || box.after[1]!=UINT64_C(0xabcdef0123456789)) {
            fprintf(stderr,"DST shape kind=%u len=%zu got=%"PRIu64" expected=%"PRIu64"\n",kind,len,got,wanted);
            return 1;
        }
        checks+=37;
    }
    printf("PASS dst_tail checks=%"PRIu64"\n",checks);
    return 0;
}
