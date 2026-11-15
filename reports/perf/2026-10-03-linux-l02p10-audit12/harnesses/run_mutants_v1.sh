#!/bin/bash
# Run every mutant of the first verifier's repair (mutants_v1.py) against the
# unit rows (link_driver::tests) and the two native rows it extends, with one
# build whose guards read L02P10_MUTANT. A mutant is killed when some row
# fails. LIB: the trust-cg-codegen unit-test executable, CLI: the
# link_options test executable, both built after `mutants_v1.py apply`;
# REPO: the checkout.
E=${E:-$(cd "$(dirname "$0")" && pwd)}
LIB=${LIB:?set LIB}
CLI=${CLI:?set CLI}
cd "${REPO:?set REPO}/crates/trust-cg-cli" || exit 2
mkdir -p "$E/mutants_v1"
for m in none $(python3 "$E/mutants_v1.py" list); do
  unit=$(L02P10_MUTANT=$m "$LIB" link_driver::tests --test-threads 4 2>&1)
  native=$(L02P10_MUTANT=$m TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1 "$CLI" --test-threads 2 \
    tls_templates_that segments_without_the_permissions 2>&1)
  printf '%s\n%s\n' "$unit" "$native" > "$E/mutants_v1/$m.log"
  ufail=$(printf '%s\n' "$unit" | grep -E '^test .* FAILED$' | sed 's/^test //; s/ \.\.\. FAILED//' | tr '\n' ' ')
  nfail=$(printf '%s\n' "$native" | grep -E '^test .* FAILED$' | sed 's/^test //; s/ \.\.\. FAILED//' | tr '\n' ' ')
  ures=$(printf '%s\n' "$unit" | grep 'test result' | sed 's/;.*//')
  nres=$(printf '%s\n' "$native" | grep 'test result' | sed 's/;.*//')
  if [ -n "$ufail$nfail" ]; then verdict=KILLED; else verdict=SURVIVED; fi
  echo "$m $verdict | unit: $ures [$ufail] | native: $nres [$nfail]"
done
