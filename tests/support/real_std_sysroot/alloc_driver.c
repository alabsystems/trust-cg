#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static size_t live_allocations;
void *test_alloc(size_t size, size_t align) {
    void *p = NULL;
    if (align < sizeof(void *)) align = sizeof(void *);
    if (posix_memalign(&p, align, size ? size : 1)) return NULL;
    ++live_allocations;
    return p;
}
void test_free(void *p) {
    if (p) {
        if (!live_allocations) abort();
        --live_allocations;
        free(p);
    }
}
extern uint64_t library_utf16(const unsigned char *, size_t, unsigned);
extern uint64_t library_unicode(const unsigned char *, size_t, unsigned);
extern uint64_t library_vec_drain(const unsigned char *, size_t, size_t, size_t, size_t);
extern uint64_t library_string_drain(const unsigned char *, size_t, size_t, size_t, size_t, size_t *);
static size_t checks;
static void check(const char *what, size_t seed, size_t n, uint64_t got, uint64_t want) {
    ++checks;
    if (got != want) {
        fprintf(stderr, "%s seed=%zu n=%zu got=%llu want=%llu\n", what, seed, n,
                (unsigned long long)got, (unsigned long long)want);
        abort();
    }
}
static void check_allocations(void) { check("allocations",0,0,live_allocations,0); }
static uint64_t hash(const unsigned char *s, size_t n) {
    uint64_t h = 0x1978;
    for (size_t i=0;i<n;++i) h=h*37+s[i];
    return h ^ (((uint64_t)n << 17) | ((uint64_t)n >> 47));
}
static size_t encode(unsigned char *p, uint32_t c) {
    if (c < 128) { p[0]=c; return 1; }
    if (c < 2048) { p[0]=192|(c>>6);p[1]=128|(c&63);return 2; }
    if (c < 65536) { p[0]=224|(c>>12);p[1]=128|((c>>6)&63);p[2]=128|(c&63);return 3; }
    p[0]=240|(c>>18);p[1]=128|((c>>12)&63);p[2]=128|((c>>6)&63);p[3]=128|(c&63);return 4;
}
static unsigned unit(const unsigned char *p, unsigned little) {
    return little ? p[0] + 256u*p[1] : 256u*p[0] + p[1];
}
static uint64_t utf16(const unsigned char *s, size_t n, unsigned kind) {
    unsigned char out[1024];size_t used=0,i=0;
    unsigned lossy=kind>=2,little=kind&1;
    if (!lossy && (n&1)) return UINT64_C(0xfedcba9876543210);
    while (i+1<n) {
        uint32_t c=unit(s+i,little);i+=2;
        if (c>=0xd800 && c<=0xdbff) {
            unsigned low=i+1<n ? unit(s+i,little) : 0;
            if (low>=0xdc00 && low<=0xdfff) {c=0x10000+((c-0xd800)<<10)+(low-0xdc00);i+=2;}
            else {if(!lossy)return UINT64_C(0xfedcba9876543210);c=0xfffd;}
        } else if (c>=0xdc00 && c<=0xdfff) {
            if(!lossy)return UINT64_C(0xfedcba9876543210);c=0xfffd;
        }
        used+=encode(out+used,c);
    }
    if (n&1) used+=encode(out+used,0xfffd);
    return hash(out,used);
}
int main(void) {
    unsigned char storage[1024], remaining[1024];
    const unsigned units[]={0,0x41,0xd800,0xdfff,0xd83d,0xde42,0xd834,0xdd1e,0x1234,0xffff};
    for(size_t seed=0;seed<256;++seed) {
        unsigned char *s=storage+(seed%8);
        for(size_t j=0;j<128;j+=2) {
            unsigned c=units[((j/2)*3+seed)%10];
            s[j]=c;s[j+1]=c>>8;
        }
        for(size_t n=0;n<=65;++n) for(unsigned kind=0;kind<4;++kind) {
            check("utf16",seed,n,library_utf16(s,n,kind),utf16(s,n,kind));
            check_allocations();
        }
    }
    const char *cases[][4]={
        {"","","",""},
        {"AΣ","aς","AΣ","Aς"},
        {"ΟΣ","ος","ΟΣ","Ος"},
        {"ΟΣΑ","οσα","ΟΣΑ","Οσα"},
        {"Σ","σ","Σ","Σ"},
        {"ÁΣ","áς","ÁΣ","Áς"},
        {"ΟΣ́Α","οσ́α","ΟΣ́Α","Οσ́α"},
        {"ß","ß","SS","Ss"},
        {"ﬃ","ﬃ","FFI","Ffi"},
        {"İ","i̇","İ","İ"},
        {"'TWAS","'twas","'TWAS","'Twas"},
        {"🙂ABC","🙂abc","🙂ABC","🙂Abc"}
    };
    for(size_t i=0;i<sizeof(cases)/sizeof(cases[0]);++i) for(unsigned mode=0;mode<3;++mode) {
        check("unicode",i,mode,library_unicode((const unsigned char *)cases[i][0],strlen(cases[i][0]),mode),
              hash((const unsigned char *)cases[i][mode+1],strlen(cases[i][mode+1])));
        check_allocations();
    }
    for(size_t seed=0;seed<128;++seed) for(size_t n=0;n<=64;++n) {
        unsigned char *s=storage+(seed%8);
        for(size_t i=0;i<n;++i)s[i]=(seed*11+i*17)&255;
        size_t start=seed%(n+1),end=start+(seed*13+n)%(n-start+1),take=seed%(end-start+3);
        size_t consumed=take<end-start?take:end-start;
        uint64_t out=1;for(size_t i=0;i<consumed;++i)out=out*17+s[start+i];
        memcpy(remaining,s,start);memcpy(remaining+start,s+end,n-end);
        check("vec_drain",seed,n,library_vec_drain(s,n,start,end,take),out^hash(remaining,start+n-end));
        check_allocations();
    }
    const uint32_t scalars[]={0,0x41,0xe9,0x3a3,0x200d,0x1f642,0x10ffff};
    for(size_t seed=0;seed<128;++seed)for(size_t n=0;n<=32;++n) {
        unsigned char *s=storage+(seed%8);size_t offsets[34],bytes=0;
        offsets[0]=0;
        for(size_t i=0;i<n;++i) {bytes+=encode(s+bytes,scalars[(i*3+seed)%7]);offsets[i+1]=bytes;}
        size_t start=seed%(n+1),end=start+(seed*13+n)%(n-start+1),take=seed%(end-start+3);
        size_t consumed=take<end-start?take:end-start;
        uint64_t out=1;for(size_t i=0;i<consumed;++i)out=out*17+scalars[((start+i)*3+seed)%7];
        memcpy(remaining,s,offsets[start]);memcpy(remaining+offsets[start],s+offsets[end],bytes-offsets[end]);
        size_t state[4],left=offsets[end]-offsets[start+consumed];
        check("string_drain",seed,n,library_string_drain(s,bytes,offsets[start],offsets[end],take,state),out^hash(remaining,offsets[start]+bytes-offsets[end]));
        check("string_hint_low",seed,n,state[0],left/4+(left%4!=0));
        check("string_hint_high",seed,n,state[1],left);
        check("string_remaining_len",seed,n,state[2],left);
        check("string_remaining_hash",seed,n,state[3],hash(s+offsets[start+consumed],left));
        check_allocations();
    }
    printf("PASS linked_alloc checks=%zu\n",checks);
}
