#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
extern size_t library_count(const unsigned char *, size_t);
static size_t encode(unsigned char *out, unsigned n) {
    if (n < 128) {out[0]=n;return 1;}
    if (n < 2048) {out[0]=192|(n>>6);out[1]=128|(n&63);return 2;}
    if (n < 65536) {out[0]=224|(n>>12);out[1]=128|((n>>6)&63);out[2]=128|(n&63);return 3;}
    out[0]=240|(n>>18);out[1]=128|((n>>12)&63);out[2]=128|((n>>6)&63);out[3]=128|(n&63);return 4;
}
extern bool library_validate(const unsigned char *, size_t, size_t *, size_t *);
static bool validate(const unsigned char *s, size_t n, size_t *valid, size_t *error) {
    size_t i=0;
    while (i<n) {
        unsigned a=s[i];
        if(a<128) { ++i; continue; }
        unsigned width = a>=0xc2 && a<=0xdf ? 2 : a>=0xe0 && a<=0xef ? 3 : a>=0xf0 && a<=0xf4 ? 4 : 0;
        *valid=i;
        if(!width) { *error=1; return false; }
        for(unsigned j=1;j<width;++j) {
            if(i+j==n) { *error=0; return false; }
            unsigned c=s[i+j];
            bool ok=c>=0x80 && c<=0xbf;
            if(j==1) {
                if(a==0xe0) ok &= c>=0xa0;
                if(a==0xed) ok &= c<0xa0;
                if(a==0xf0) ok &= c>=0x90;
                if(a==0xf4) ok &= c<0x90;
            }
            if(!ok) { *error=j; return false; }
        }
        i+=width;
    }
    *valid=n; *error=0; return true;
}
static void check_validate(const unsigned char *s, size_t n) {
    size_t av,ae,bv,be;
    bool a=validate(s,n,&av,&ae), b=library_validate(s,n,&bv,&be);
    if(a!=b || av!=bv || ae!=be) {
        fprintf(stderr,"UTF8 n=%zu expected=%d/%zu/%zu actual=%d/%zu/%zu\n",n,a,av,ae,b,bv,be);
        abort();
    }
}
int main(void) {
    unsigned char storage[8192]; unsigned char *s=storage;
    size_t checks=0,n=0,count=0;
    for (unsigned c=0;c<0x110000;c+=97) {
        if (c>=0xd800 && c<=0xdfff) continue;
        n+=encode(s+n,c); ++count;
        if (library_count(s,n)!=count) abort();
        ++checks;
        if (n>4000) {s=storage+checks%32;n=0;count=0;}
    }
    for(unsigned x=0;x<65536;++x) {
        s[0]=x>>8;s[1]=x;check_validate(s,2);++checks;
    }
    uint64_t state=0x57492312907532abULL;
    for(size_t k=0;k<4096;++k) {
        size_t n=k%129;
        for(size_t j=0;j<n;++j) {state^=state<<13;state^=state>>7;state^=state<<17;s[j]=state;}
        check_validate(s,n);++checks;
    }
    printf("PASS linked_core checks=%zu\n",checks);
}
