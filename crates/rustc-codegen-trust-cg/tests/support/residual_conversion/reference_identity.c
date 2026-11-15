#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
typedef struct {uint64_t a,b;} Pair;
bool fixed_identity(const uint64_t*a,const uint64_t*b){return a==b;}
bool pair_identity(const Pair*a,const Pair*b){return a==b;}
bool ref_identity(const uint64_t*const*a,const uint64_t*const*b){return a==b && *a==*b;}
const uint64_t*address(const uint64_t*a){return a;}
bool cell_alias(uint64_t*a,uint64_t*b,uint64_t x){*a=x;return a==b && *b==x;}
extern bool c_same(uint64_t),rust_same(uint64_t),c_alias(uint64_t),rust_alias(uint64_t),c_across(uint64_t),rust_across(uint64_t),c_nested(uint64_t),c_distinct(uint64_t),rust_distinct(uint64_t);
extern bool c_branch(uint64_t,uint64_t,bool),rust_branch(uint64_t,uint64_t,bool),c_projected(uint64_t,uint64_t),rust_projected(uint64_t,uint64_t),c_pair(uint64_t,uint64_t),rust_pair(uint64_t,uint64_t),c_cell(uint64_t,uint64_t);
extern bool c_indirect(uint64_t,bool(*)(const uint64_t*,const uint64_t*));
extern int8_t compare_signed(uint8_t,uint8_t),compare_unsigned(uint8_t,uint8_t);
typedef struct {const uint64_t *p;} Cursor;
uint64_t nested_shared(const uint64_t *const *p){return **p;}
uint64_t scalar_read(const uint64_t *p){return *p;}
uint64_t observe_raw(const Cursor *p){return *p->p;}
uint64_t observe_ref(const Cursor *p){return *p->p;}
extern uint64_t shared_reborrow(uint64_t *),raw_reborrow(const uint64_t *);
extern uint64_t raw_field(const uint64_t *,const uint64_t *),ref_field(const uint64_t *,const uint64_t *);
extern bool field_borrow(uint64_t);
extern uint64_t nested_field_borrow(uint64_t);
int reference_identity_driver(void){
 unsigned failures[25]={0};uint64_t checks=0;
 for(unsigned i=0;i<4096;i++) {
  uint64_t a=UINT64_C(0xfedcba9876543211)*i,b=a^UINT64_C(0x81403);bool pick=(i&1)!=0;
  uint8_t x=i%3,y=(i/3)%3;int8_t expected=(x>y)-(x<y);
  bool results[]={c_same(a),rust_same(a),c_alias(a),rust_alias(a),c_branch(a,b,pick),rust_branch(a,b,pick),c_projected(a,b),rust_projected(a,b),c_pair(a,b),rust_pair(a,b),c_across(a),rust_across(a),c_indirect(a,fixed_identity),c_nested(a),c_cell(a,b),c_distinct(a),rust_distinct(a),compare_signed(x,y)==expected,compare_unsigned(x,y)==expected,shared_reborrow(&a)==a,raw_reborrow(&a)==a,raw_field(&a,&b)==a+b+b,ref_field(&a,&b)==a+b+b,field_borrow(a),nested_field_borrow(a)==a};
  for(unsigned n=0;n<25;n++){checks++;if(!results[n])failures[n]++;}
 }
 unsigned bad=0;for(unsigned n=0;n<25;n++)if(failures[n]){printf("case=%u failures=%u\n",n,failures[n]);bad++;}
 printf("PASS reference_identity checks=%llu failing_cases=%u\n",(unsigned long long)checks,bad);
 return bad!=0;
}
