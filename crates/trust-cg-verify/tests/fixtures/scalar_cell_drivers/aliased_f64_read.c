#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef double Scalar;
typedef struct {Scalar value;} Inner;
typedef struct {Inner inner;} Outer;
typedef struct {uint64_t before;Outer data;uint64_t after;} Guard;
typedef struct {uint64_t before;Scalar data[6];uint64_t after;} Output;
_Static_assert(sizeof(Outer)==sizeof(Scalar),"full scalar cell extent");
_Static_assert(_Alignof(Outer)==_Alignof(Scalar),"full scalar cell alignment");
_Static_assert(offsetof(Outer,inner.value)==0,"nested zero-offset scalar");
static const uint64_t CANARY1=UINT64_C(0x75182ab3c69def04),CANARY2=UINT64_C(0xb4e69d721ac3580f);
static unsigned calls,checks,events,changes,records;
static uintptr_t seen,forbidden;
static Scalar expected_memory[16],expected_argument[16],observed[16];
static unsigned expected_tag[16];
static void check(int ok,const char*name){checks++;if(!ok){fprintf(stderr,"FAIL scalar-cell %s check=%u events=%u\n",name,checks,events);exit(1);}}
static void bytes(const void*actual,const void*expected,const char*name){check(memcmp(actual,expected,sizeof(Scalar))==0,name);}
static void canaries(const uint64_t*before,const uint64_t*after){check(*before==CANARY1,"C-before-canary");check(*after==CANARY2,"C-after-canary");}
static const uint64_t bits[17]={UINT64_C(0x403f800000000000),UINT64_C(0x3ff4000000000000),UINT64_C(0xc004000000000000),UINT64_C(0x400e000000000000),UINT64_C(0xc011000000000000),UINT64_C(0x8000000000000000),0,UINT64_C(0x7ff0000000000000),UINT64_C(0xfff0000000000000),UINT64_C(0x7ff8123456789abc),UINT64_C(0xfff8543210fedcba),UINT64_C(0x3fe0000000000001),UINT64_C(0xbfe0000000000003),UINT64_C(0x0010000000000001),UINT64_C(0x8010000000000003),1,UINT64_C(0x8000000000000001)};
static Scalar pattern(unsigned i){Scalar value;memcpy(&value,&bits[i%17],sizeof value);return value;}
static void reset(const void*input){events=changes=records=0;seen=0;forbidden=(uintptr_t)input;}
static void observe(void*p){
 if(events>=16){fputs("too many callbacks\n",stderr);exit(1);}
 check((uintptr_t)p%_Alignof(Scalar)==0,"actual-cell-alignment");
 if(events==0)seen=(uintptr_t)p;
 check((uintptr_t)p==seen,"same-live-cell-address");
 check((uintptr_t)p!=forbidden,"by-value-cell-not-C-input");
 memcpy(&observed[events],p,sizeof(Scalar));
 bytes(&observed[events],&expected_memory[events],"opaque-memory-observation");
 events++;
}
void c_change(void*p,Scalar value){unsigned event=events;observe(p);bytes(&value,&expected_argument[event],"opaque-write-argument");memcpy(p,&value,sizeof value);changes++;}
void c_record(void*p,uint32_t tag){if(events>=16){fputs("too many callbacks\n",stderr);exit(1);}check(tag==expected_tag[events],"observation-order");observe(p);records++;}
extern Scalar aliased_f64_read(Outer,Scalar);
int main(void){for(unsigned data=0;data<17;data++){Guard input={CANARY1,{{-21.5}},CANARY2},output={CANARY1,{{0}},CANARY2};Scalar value=pattern(data),original=input.data.inner.value;reset(&input.data);expected_argument[0]=value;expected_memory[0]=original;output.data.inner.value=aliased_f64_read(input.data,value);
calls++;check(events==1,"callback-count");check(changes==1,"write-count");bytes(&output.data.inner.value,&value,"returned-live-value");bytes(&input.data.inner.value,&original,"C-input-unchanged");Scalar expected=pattern(data);bytes(&value,&expected,"replacement-unchanged");canaries(&input.before,&input.after);canaries(&output.before,&output.after);}if(calls!=17||checks!=238){fprintf(stderr,"wrong counts calls=%u checks=%u\n",calls,checks);return 2;}printf("PASS scalar_cell family=aliased_f64_read calls=%u checks=%u\n",calls,checks);return 0;}
