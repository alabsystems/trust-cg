#include <stdio.h>
extern unsigned long tcg_tls_get(void), tcg_tls_get_z(void);
int main(void){unsigned long a=tcg_tls_get(),z=tcg_tls_get_z();printf("tcg_t=%#lx tcg_tz=%#lx\n",a,z);return a==42&&z==0?0:1;}
