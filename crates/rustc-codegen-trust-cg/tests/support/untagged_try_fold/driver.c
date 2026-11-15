#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
extern uint64_t live_path(uint64_t);
extern uint64_t drain_path(uint64_t,uint32_t,uint64_t*,uint64_t*);
extern uint64_t narrow_path(uint64_t,uint32_t,uint32_t);
extern uint64_t tagged_path(uint64_t,uint32_t,uint64_t*);
extern uint64_t tagged_narrow_path(uint64_t,uint32_t,uint32_t,uint64_t*);
static uint64_t checks;
static int check(uint64_t got,uint64_t want,unsigned row,unsigned n,const char *what){++checks;if(got==want)return 1;fprintf(stderr,"%s row=%u n=%u got=%"PRIu64" expected=%"PRIu64"\n",what,row,n,got,want);return 0;}
#define CHECK(got,want,label) do{if(!check((got),(want),i,n,(label)))return 1;}while(0)
int main(void) {
 const uint64_t values[]={0,1,2,7,UINT64_MAX,UINT64_C(0x8000000000000000),UINT64_C(0x123456789abcdef0)};
 uint64_t state=UINT64_C(0x1729abcdef456789);
 for(unsigned i=0;i<263;++i) {
  state^=state<<13;state^=state>>7;state^=state<<17;
  uint64_t value=i<7?values[i]:state,wanted=value;
  unsigned n=4;
  for(unsigned k=0;k<4;++k)wanted=wanted*3+k;
  CHECK(live_path(value),wanted,"original");
  for(n=0;n<9;++n){
   struct {uint64_t left,cursor,calls,right;} memory={0x11223344,UINT64_MAX,UINT64_MAX,0x55667788};
   wanted=value;for(unsigned k=0;k<n;++k)wanted=wanted*((value&3)+1)+k;
   CHECK(drain_path(value,n,&memory.cursor,&memory.calls),wanted^0x123,"drain result");
   CHECK(memory.cursor,n,"drain cursor");CHECK(memory.calls,n,"closure calls");CHECK(memory.left,0x11223344,"left guard");CHECK(memory.right,0x55667788,"right guard");
   for(unsigned mode=0;mode<3;++mode){
    uint64_t mask=mode==0?0xff:mode==1?UINT64_C(0xffffffff):UINT64_MAX;
    wanted=value&mask;for(unsigned k=0;k<n;++k)wanted=(wanted*3+k)&mask;
    CHECK(narrow_path(value,n,mode),wanted,"integer lane");
   }
   memory.cursor=UINT64_MAX;wanted=value;
   for(unsigned k=0;k<n && k<2;++k)wanted=wanted*3+k;
   wanted^=n>2?0x55:0xaa;
   CHECK(tagged_path(value,n,&memory.cursor),wanted,"tagged result");CHECK(memory.cursor,n>2?3:n,"tagged cursor");CHECK(memory.left,0x11223344,"tagged left guard");CHECK(memory.right,0x55667788,"tagged right guard");
   for(unsigned mode=0;mode<2;++mode){
    uint64_t mask=mode==0?0xff:UINT64_C(0xffffffff);
    wanted=value&mask;for(unsigned k=0;k<n && k<2;++k)wanted=(wanted*3+k)&mask;
    wanted^=n>2?0x55:0xaa;memory.cursor=UINT64_MAX;
    CHECK(tagged_narrow_path(value,n,mode,&memory.cursor),wanted,"tagged narrow result");
    CHECK(memory.cursor,n>2?3:n,"tagged narrow cursor");CHECK(memory.left,0x11223344,"tagged narrow left guard");CHECK(memory.right,0x55667788,"tagged narrow right guard");
   }
  }
 }
 printf("PASS untagged_try_fold checks=%"PRIu64"\n",checks);return 0;
}
