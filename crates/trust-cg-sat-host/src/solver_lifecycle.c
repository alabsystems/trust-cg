/* trust-cg-sat-host - lifecycle helpers for the vendored MicroSAT solver.
 *
 * Keep allocation and deallocation on the C side of the FFI boundary.  The
 * vendored initCDCL() owns one malloc allocation through solver::DB; every
 * other solver pointer aliases that allocation.
 */

#include "microsat_wrapper.h"

#include <stdlib.h>
#include <string.h>

void microsat_destroy(struct solver *s) {
  if (s == NULL) return;

  free(s->DB);
  memset(s, 0, sizeof(*s));
}
