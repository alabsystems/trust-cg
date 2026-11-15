from pathlib import Path

def write_fixture(out: Path):
    ir=['; TrustIr text format v1', 'module "cli_diamond_native"',
        'functy.0 = (i32, i32, i32, i32) -> (i32)',
        'functy.1 = (i64, i64, i64, i64) -> (i64)']
    declarations=[]; calls=[]
    for type_id,bits in enumerate([32,64]):
        for condition,op in enumerate(['eq','ne','slt','sle','sgt','sge','ult','ule','ugt','uge']):
            name=f'choose_{bits}_{op}'
            ir.extend([f'fn @{name}(functy.{type_id}) {{',
                f'bb0(%0: i{bits}, %1: i{bits}, %2: i{bits}, %3: i{bits}):',
                f'    %4 = icmp {op} i{bits} %0, %1',
                f'    condbr %4, bb1, bb2', 'bb1:', f'    %5 = copy i{bits} %2', '    br bb3(%5)', 'bb2:', f'    %6 = copy i{bits} %3', '    br bb3(%6)', f'bb3(%7: i{bits}):', '    ret %7','}'])
            declarations.append(f'extern uint{bits}_t {name}(uint{bits}_t,uint{bits}_t,uint{bits}_t,uint{bits}_t);')
            calls.append(f'if(test{bits}({name},{condition})) return 1;')
    c=r'''#include <stdint.h>
#include <stdio.h>
DECLARATIONS
static unsigned checks;
#define TEST(W) \
static int test##W(uint##W##_t (*fn)(uint##W##_t,uint##W##_t,uint##W##_t,uint##W##_t),int cc) { \
const uint##W##_t sign=(uint##W##_t)1<<(W-1),max=(uint##W##_t)-1; \
const uint##W##_t values[]={0,1,2,sign-1,sign,sign+1,max-1,max}; \
const uint##W##_t payloads[][2]={{0,max},{sign,sign-1},{max-1,2}}; \
for(unsigned i=0;i<8;i++) for(unsigned j=0;j<8;j++) for(unsigned k=0;k<3;k++){ \
const uint##W##_t a=values[i],b=values[j],t=payloads[k][0],f=payloads[k][1]; \
const int##W##_t sa=(int##W##_t)a,sb=(int##W##_t)b; int take; \
switch(cc){case 0:take=a==b;break;case 1:take=a!=b;break;case 2:take=sa<sb;break; \
case 3:take=sa<=sb;break;case 4:take=sa>sb;break;case 5:take=sa>=sb;break; \
case 6:take=a<b;break;case 7:take=a<=b;break;case 8:take=a>b;break;default:take=a>=b;} \
if(fn(a,b,t,f)!=(take?t:f)){fprintf(stderr,"condition %d case %u/%u/%u failed\n",cc,i,j,k);return 1;} \
checks++;} return 0; }
TEST(32)
TEST(64)
int main(void){
CALLS
printf("CLI_DIAMOND_NATIVE functions=20 checks=%u\n",checks);
return checks==3840 ? 0 : 2;
}
'''.replace('DECLARATIONS','\n'.join(declarations)).replace('CALLS','\n'.join(calls))
    fixture=out/'diamond-native.trust_ir'; oracle=out/'diamond-native.c'
    fixture.write_text('\n'.join(ir)+'\n'); oracle.write_text(c)
    return fixture,oracle
