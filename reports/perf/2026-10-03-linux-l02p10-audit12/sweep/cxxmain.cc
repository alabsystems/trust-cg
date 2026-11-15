#include <cstdio>
#include <stdexcept>
#include <string>
#include <vector>
extern "C" {
unsigned long c_word = 1000;
unsigned long c_cb(unsigned long x) { return x * 2; }
unsigned long tcg_get(void), tcg_bump(void), tcg_call(void), tcg_tls_bump(void), tcg_cb(void), tcg_cword(void);
}
static thread_local std::string tl_name = "tls";
int main()
{
    std::vector<unsigned long> v;
    int caught = 0;
    try {
        v.push_back(tcg_get());
        v.push_back(tcg_bump());
        v.push_back(tcg_call());
        v.push_back(tcg_tls_bump());
        v.push_back(tcg_cb());
        v.push_back(tcg_cword());
        throw std::runtime_error("x");
    } catch (const std::exception &e) {
        caught = 1;
    }
    int ok = caught && v.size() == 6 && v[0] == 42 && v[1] == 43 && v[2] == 43 && v[3] == 8 && v[4] == 10 && v[5] == 1000 && tl_name == "tls";
    std::printf("v=%s n=%zu\n", ok ? "OK" : "BAD", v.size());
    return ok ? 0 : 1;
}
