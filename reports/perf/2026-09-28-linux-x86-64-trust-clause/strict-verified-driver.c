#include <stdio.h>
#include <stdint.h>
uint32_t t_add_wrapping(uint32_t,uint32_t); uint64_t t_xor(uint64_t,uint64_t);
uint64_t t_shl_masked(uint64_t,uint32_t); uint64_t t_shr_masked(uint64_t,uint32_t);
uint64_t t_mul_wrapping(uint64_t,uint64_t); uint64_t t_xorshift(uint64_t);
uint64_t t_cond_select(uint64_t,uint64_t,uint32_t);
uint64_t s01(uint64_t,uint64_t); uint64_t s02(uint64_t,uint64_t); uint64_t s03(uint64_t);
uint64_t s04(uint64_t); uint64_t s05(uint64_t); uint64_t s06(uint64_t,uint32_t);
int32_t  s07(int32_t,int32_t); uint32_t s08(uint64_t,uint64_t);
uint64_t s09(uint64_t,uint32_t); uint64_t s10(uint64_t);
uint64_t e01(uint64_t,uint32_t); uint32_t f03(double,double);
uint64_t g02(uint64_t,uint64_t,uint32_t); uint64_t i01(uint64_t,uint64_t);
uint64_t tr02(uint64_t); uint32_t u02(uint32_t,uint32_t);
int main(void){
  uint64_t acc=0,x=0x123456789ABCDEFull;
  for(int i=0;i<64;i++){
    x=t_xorshift(x);
    acc^=(uint64_t)t_add_wrapping((uint32_t)x,(uint32_t)i);
    acc+=t_xor(x,acc); acc^=t_shl_masked(x,(uint32_t)i);
    acc+=t_shr_masked(x,(uint32_t)i); acc^=t_mul_wrapping(x,0x2545F4914F6CDD1Dull);
    acc+=t_cond_select(x,acc,(uint32_t)i);
    acc^=s01(x,acc); acc+=s02(x,acc); acc^=s03(x); acc+=s04(x);
    acc^=s05(x); acc+=s06(x,(uint32_t)i);
    acc^=(uint64_t)(int64_t)s07((int32_t)x,(int32_t)i);
    acc+=(uint64_t)s08(x,acc); acc^=s09(x,(uint32_t)i); acc+=s10(x);
    acc^=e01(x,(uint32_t)i); acc+=(uint64_t)f03((double)i,(double)(i^3));
    acc^=g02(x,acc,(uint32_t)i); acc+=i01(x,acc); acc^=tr02(x);
    acc+=(uint64_t)u02((uint32_t)x,(uint32_t)i);
  }
  printf("%llu\n",(unsigned long long)acc); return 0;
}
