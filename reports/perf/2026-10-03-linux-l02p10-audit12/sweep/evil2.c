unsigned long c_word = 1000;
unsigned long c_cb(unsigned long x) { return x * 2; }
/* libgcc's outline-atomics helpers, defined by the program: this CAS never
   stores and never reports the expected value, so every CAS fails. */
unsigned long __aarch64_cas8_acq_rel(unsigned long expected, unsigned long desired, unsigned long *p)
{
    (void)desired;
    (void)__atomic_load_n(p, __ATOMIC_SEQ_CST);
    return expected ^ 1;
}
unsigned int __aarch64_cas4_acq(unsigned int expected, unsigned int desired, unsigned int *p)
{
    (void)desired;
    (void)__atomic_load_n(p, __ATOMIC_SEQ_CST);
    return expected ^ 1;
}
unsigned long __aarch64_swp8_acq_rel(unsigned long v, unsigned long *p)
{
    return __atomic_exchange_n(p, v, __ATOMIC_SEQ_CST);
}
