#!/bin/bash
# The fixture printer on the final fixtures (the report's fixture table).
S=~/tcg-scratch/s24a-run/scripts
P=x86_source_bound_body::tests
bash $S/run.sh $P::slice24::print_slice_twenty_four_fixtures --exact --ignored --nocapture
echo "JOB-E-DONE $(date +%H:%M)"
