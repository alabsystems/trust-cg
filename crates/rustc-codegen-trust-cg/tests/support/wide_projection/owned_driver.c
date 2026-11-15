#define _POSIX_C_SOURCE 200112L
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
static uint64_t checks,allocations,frees,expected_value;
static unsigned drops,releases,call_frees,expected_drops;
static size_t expected_size,expected_align;
static unsigned char *base,*payload;
#define CHECK(c) do { ++checks; if(!(c)) { fprintf(stderr,"failed line %d\n",__LINE__);abort(); } } while(0)
void dropped(uint64_t value) { CHECK(drops==0);CHECK(releases==0);CHECK(value==expected_value);++drops; }
void released(unsigned char *p,size_t size,size_t align) {
    CHECK(releases==0);CHECK(p==payload);CHECK(size==expected_size);CHECK(align==expected_align);CHECK(drops==expected_drops);
    if(size) {
        unsigned pre=1,post=1;
        for(unsigned i=0;i<64;++i){pre &= base[i]==0xa5;post &= payload[size+i]==0xa5;}
        CHECK(pre);CHECK(post);free(base);++frees;++call_frees;
    }
    ++releases;
}
extern void destroy_small(void*),destroy_aligned(void*),destroy_plain(void*),destroy_zero(void*),destroy_slice(void*),destroy_empty(void*);
int main(void) {
    void(*cases[])(void*)={destroy_small,destroy_aligned,destroy_plain,destroy_zero,destroy_slice,destroy_empty};
    for(uint64_t seed=0;seed<1024;++seed)for(unsigned k=0;k<6;++k) {
        expected_size=(k==3||k==5)?0:k==1?64:k==4?56:8;expected_align=k==3?32:k==1?64:8;
        expected_drops=(k==2||k>=4)?0:1;expected_value=k==3?0xface1234:seed*UINT64_C(0x9876543219876543);
        drops=releases=call_frees=0;
        if(expected_size){
            void *allocation=NULL;if(posix_memalign(&allocation,64,expected_size+128))abort();base=allocation;
            memset(base,0xa5,expected_size+128);payload=base+64;memcpy(payload,&expected_value,8);
            if(k==1){uint64_t first=expected_value^0x12345678,second=0x12345678;memcpy(payload,&first,8);memcpy(payload+8,&second,8);}
            CHECK((uintptr_t)payload%expected_align==0);++allocations;
        }else{base=NULL;payload=(unsigned char*)(uintptr_t)expected_align;}
        cases[k](payload);CHECK(drops==expected_drops);CHECK(releases==1);CHECK(call_frees==(expected_size!=0));
    }
    CHECK(allocations==4096);CHECK(frees==4096);
    if(checks!=70658)abort();printf("PASS wide_projection_owned checks=%llu\n",(unsigned long long)checks);return 0;
}
