#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
static uint64_t get_fpcr(void){uint64_t x;__asm__ volatile("mrs %0, fpcr":"=r"(x));return x;}
static void set_fpcr(uint64_t x){__asm__ volatile("msr fpcr, %0\n\tisb"::"r"(x):"memory");}
static uint64_t get_fpsr(void){uint64_t x;__asm__ volatile("mrs %0, fpsr":"=r"(x)::"memory");return x;}
static void clear_fpsr(void){__asm__ volatile("msr fpsr, xzr":::"memory");}
static uint64_t random_bits(uint64_t *x){*x^=*x<<13;*x^=*x>>7;*x^=*x<<17;return *x;}
extern float fp32_fmadd(float,float,float,unsigned);
extern float fp32_fmadd_out(float,float,float,unsigned);
extern float fp32_alias(float,float,float,unsigned);
extern float fp32_sqrt(float,float,float,unsigned);
extern float fp32_sqrt_out(float,float,float,unsigned);
extern float fp32_round(float,float,float,unsigned);
extern float fp32_round_out(float,float,float,unsigned);
extern float fp32_loop(float,float,float,unsigned);
extern float fp32_constant(float,float,float,unsigned);
typedef float (*fn32)(float,float,float,unsigned);
static fn32 functions32[]={fp32_fmadd,fp32_fmadd_out,fp32_alias,fp32_sqrt,fp32_sqrt_out,fp32_round,fp32_round_out,fp32_loop,fp32_constant};
static uint32_t bits32(float x){uint32_t y;memcpy(&y,&x,sizeof y);return y;}
static float value32(uint32_t x){float y;memcpy(&y,&x,sizeof y);return y;}
static float oracle32(unsigned kind,float x,float y,float z,unsigned n){
    if(kind==8){x=0x1.000002p0f;y=0x1.fffffcp-1f;z=-1;kind=0;}
    if(kind==2){__asm__ volatile("fmadd %s0, %s1, %s2, %s2":"=w"(x):"w"(y),"w"(x));}
    else if(kind==3||kind==4){__asm__ volatile("fsqrt %s0, %s1":"=w"(x):"w"(x));}
    else if(kind==5||kind==6){__asm__ volatile("frintn %s0, %s1":"=w"(x):"w"(x));}
    else{unsigned count=kind==7?n:1;for(unsigned i=0;i<count;i++)__asm__ volatile("fmadd %s0, %s1, %s2, %s3":"=w"(x):"w"(x),"w"(y),"w"(z));}
    return x;
}
extern double fp64_fmadd(double,double,double,unsigned);
extern double fp64_fmadd_out(double,double,double,unsigned);
extern double fp64_alias(double,double,double,unsigned);
extern double fp64_sqrt(double,double,double,unsigned);
extern double fp64_sqrt_out(double,double,double,unsigned);
extern double fp64_round(double,double,double,unsigned);
extern double fp64_round_out(double,double,double,unsigned);
extern double fp64_loop(double,double,double,unsigned);
extern double fp64_constant(double,double,double,unsigned);
typedef double (*fn64)(double,double,double,unsigned);
static fn64 functions64[]={fp64_fmadd,fp64_fmadd_out,fp64_alias,fp64_sqrt,fp64_sqrt_out,fp64_round,fp64_round_out,fp64_loop,fp64_constant};
static uint64_t bits64(double x){uint64_t y;memcpy(&y,&x,sizeof y);return y;}
static double value64(uint64_t x){double y;memcpy(&y,&x,sizeof y);return y;}
static double oracle64(unsigned kind,double x,double y,double z,unsigned n){
    if(kind==8){x=0x1.0000000000001p0;y=0x1.ffffffffffffep-1;z=-1;kind=0;}
    if(kind==2){__asm__ volatile("fmadd %d0, %d1, %d2, %d2":"=w"(x):"w"(y),"w"(x));}
    else if(kind==3||kind==4){__asm__ volatile("fsqrt %d0, %d1":"=w"(x):"w"(x));}
    else if(kind==5||kind==6){__asm__ volatile("frintn %d0, %d1":"=w"(x):"w"(x));}
    else{unsigned count=kind==7?n:1;for(unsigned i=0;i<count;i++)__asm__ volatile("fmadd %d0, %d1, %d2, %d3":"=w"(x):"w"(x),"w"(y),"w"(z));}
    return x;
}
static const uint64_t special64[]={0,UINT64_C(0x8000000000000000),1,UINT64_C(0x8000000000000001),UINT64_C(0x000fffffffffffff),UINT64_C(0x0010000000000000),UINT64_C(0x7fefffffffffffff),UINT64_C(0xffefffffffffffff),UINT64_C(0x7ff0000000000000),UINT64_C(0xfff0000000000000),UINT64_C(0x7ff0000000000001),UINT64_C(0xfff0000000001234),UINT64_C(0x7ff8123456789abc),UINT64_C(0xfff856789abcdef0),UINT64_C(0x3fe0000000000000),UINT64_C(0x3ff8000000000000),UINT64_C(0x4004000000000000),UINT64_C(0xc004000000000000)};
static const uint32_t special32[]={0,0x80000000,1,0x80000001,0x007fffff,0x00800000,0x7f7fffff,0xff7fffff,0x7f800000,0xff800000,0x7f800001,0xff801234,0x7fc12345,0xffc6789a,0x3f000000,0x3fc00000,0x40200000,0xc0200000};
int main(void){uint64_t saved=get_fpcr(),checks=0;
for(unsigned mode=0;mode<16;mode++){
    set_fpcr(((uint64_t)(mode&3)<<22)|((uint64_t)(mode>>2)<<24));
    uint64_t state=UINT64_C(0x624f19ba30e875cd);
    for(unsigned i=0;i<4096;i++){
        {unsigned total=sizeof special32/sizeof special32[0];
        uint32_t bx=i<total*total?special32[i%total]:(uint32_t)random_bits(&state);
        uint32_t by=i<total*total?special32[(i/total)%total]:(uint32_t)random_bits(&state);
        uint32_t bz=i<total*total?special32[(i*7+3)%total]:(uint32_t)random_bits(&state);
        float x=value32(bx),y=value32(by),z=value32(bz);
        for(unsigned k=0;k<9;k++){
            clear_fpsr();uint32_t expected=bits32(oracle32(k,x,y,z,i%5));uint64_t want_status=get_fpsr();
            clear_fpsr();uint32_t actual=bits32(functions32[k](x,y,z,i%5));uint64_t actual_status=get_fpsr();
            if(actual!=expected||actual_status!=want_status){set_fpcr(saved);fprintf(stderr,"fp32 mode=%u i=%u k=%u x=%llx y=%llx z=%llx expected=%llx actual=%llx status=%llx/%llx\n",mode,i,k,(unsigned long long)bx,(unsigned long long)by,(unsigned long long)bz,(unsigned long long)expected,(unsigned long long)actual,(unsigned long long)want_status,(unsigned long long)actual_status);return 1;}
            checks+=2;
        }}
        {unsigned total=sizeof special64/sizeof special64[0];
        uint64_t bx=i<total*total?special64[i%total]:(uint64_t)random_bits(&state);
        uint64_t by=i<total*total?special64[(i/total)%total]:(uint64_t)random_bits(&state);
        uint64_t bz=i<total*total?special64[(i*7+3)%total]:(uint64_t)random_bits(&state);
        double x=value64(bx),y=value64(by),z=value64(bz);
        for(unsigned k=0;k<9;k++){
            clear_fpsr();uint64_t expected=bits64(oracle64(k,x,y,z,i%5));uint64_t want_status=get_fpsr();
            clear_fpsr();uint64_t actual=bits64(functions64[k](x,y,z,i%5));uint64_t actual_status=get_fpsr();
            if(actual!=expected||actual_status!=want_status){set_fpcr(saved);fprintf(stderr,"fp64 mode=%u i=%u k=%u x=%llx y=%llx z=%llx expected=%llx actual=%llx status=%llx/%llx\n",mode,i,k,(unsigned long long)bx,(unsigned long long)by,(unsigned long long)bz,(unsigned long long)expected,(unsigned long long)actual,(unsigned long long)want_status,(unsigned long long)actual_status);return 1;}
            checks+=2;
        }}
    }
}
set_fpcr(saved);clear_fpsr();printf("PASS aarch64_fp_asm checks=%llu\n",(unsigned long long)checks);return 0;
}
