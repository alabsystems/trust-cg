#!/bin/bash
# Run every L02-P10 twelfth-audit mutant (mutants.py) against the unit rows
# (link_driver::tests) and the three new native rows, with one build whose
# guards read L02P10_MUTANT. A mutant is killed when some row fails.
# LIB: the trust-cg-codegen unit-test executable, CLI: the link_options
# test executable, both built after `mutants.py apply`; REPO: the checkout.
E=${E:-$(cd "$(dirname "$0")" && pwd)}
LIB=${LIB:?set LIB}
CLI=${CLI:?set CLI}
cd "${REPO:?set REPO}/crates/trust-cg-cli" || exit 2
mkdir -p "$E/mutants"
for m in none $(python3 "$E/mutants.py" list); do
  unit=$(L02P10_MUTANT=$m "$LIB" link_driver::tests --test-threads 4 2>&1)
  native=$(L02P10_MUTANT=$m TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1 "$CLI" --test-threads 3 \
    tls_templates_that segments_without_the_permissions llvm_bitcode_inputs_are_read 2>&1)
  printf '%s\n%s\n' "$unit" "$native" > "$E/mutants/$m.log"
  ufail=$(printf '%s\n' "$unit" | grep -E '^test .* FAILED$' | sed 's/^test //; s/ \.\.\. FAILED//' | tr '\n' ' ')
  nfail=$(printf '%s\n' "$native" | grep -E '^test .* FAILED$' | sed 's/^test //; s/ \.\.\. FAILED//' | tr '\n' ' ')
  ures=$(printf '%s\n' "$unit" | grep 'test result' | sed 's/;.*//')
  nres=$(printf '%s\n' "$native" | grep 'test result' | sed 's/;.*//')
  if [ -n "$ufail$nfail" ]; then verdict=KILLED; else verdict=SURVIVED; fi
  echo "$m $verdict | unit: $ures [$ufail] | native: $nres [$nfail]"
done
