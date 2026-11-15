from pathlib import Path

def write_fixtures(out):
 out=Path(out);out.mkdir(parents=True)
 for ty in ['i32','u32','i64','u64']:
  width=int(ty[1:]);ct=('int' if ty[0]=='i' else 'uint')+str(width)+'_t';ut='uint'+str(width)+'_t'
  for shape in ['add','sub','double']:
   source=out/(ty+'-'+shape+'.trust_ir');rhs='%0' if shape=='double' else '%1';op='sub' if shape=='sub' else 'add'
   source.write_text(f'; TrustIr text format v1\nmodule "aot_arithmetic"\nfuncty.0 = ({ty}, {ty}) -> ({ty})\nfn @calculate(functy.0) {{\nbb0(%0: {ty}, %1: {ty}):\n    %2 = {op} {ty} %0, {rhs}\n    ret %2\n}}\n')
   oracle=out/(ty+'-'+shape+'.c');expression={'add':'a+b','sub':'a-b','double':'a+a'}[shape]
   oracle.write_text(f'''#include <stdint.h>
 #include <stdio.h>
 extern {ct} calculate({ct}, {ct});
 int main(void){{
 uint64_t values[]={{0,1,2,4095,4096,UINT32_MAX,UINT64_C(1)<<31,UINT64_C(1)<<32,INT64_MAX,UINT64_C(1)<<63,UINT64_MAX-1,UINT64_MAX}};
 for(unsigned i=0;i<12;i++)for(unsigned j=0;j<12;j++){{
 uint64_t a=({ut})values[i], b=({ut})values[j];
 {ut} actual=({ut})calculate(({ct})a,({ct})b), expected=({ut})({expression});
 if(actual!=expected)return 1;
 }}
 puts("ARITHMETIC_AOT_NATIVE calls=144");return 0;
 }}
 ''')
   yield source,oracle,ty+'-'+shape
