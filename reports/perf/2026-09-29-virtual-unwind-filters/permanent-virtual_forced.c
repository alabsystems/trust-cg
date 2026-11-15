#include <unwind.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
extern void forced_outer(void);
extern uint64_t forced_events(void);
static struct _Unwind_Exception exception;
static _Unwind_Reason_Code stop(int version, _Unwind_Action actions,
    uint64_t exception_class, struct _Unwind_Exception *ex,
    struct _Unwind_Context *context, void *arg) {
    (void)version; (void)exception_class; (void)ex; (void)arg;
    if (!(actions & _UA_FORCE_UNWIND)) _exit(81);
    if (_Unwind_GetRegionStart(context) == (uintptr_t)forced_outer) {
        if (forced_events() != 2) _exit(82);
        if (write(1, "PASS forced filter\n", 19) != 19) _exit(88);
        _exit(0);
    }
    if (actions & _UA_END_OF_STACK) _exit(83);
    return _URC_NO_REASON;
}
void forced_begin(void) {
    exception.exception_class = 0x464f524345443030ULL;
    _Unwind_ForcedUnwind(&exception, stop, 0);
    _exit(84);
}
