#!/bin/zsh
# Start the slice-9 census only when no other census runs, no quiet window is
# requested and more than 600000 pages are free; re-check right before starting.
# usage: census_when_clear.sh <tag>
TAG=${1:?tag}
clear() {
  [ ! -e $HOME/tcg-scratch/quiet.request ] &&
    ! pgrep -f 'trust_ir_cg_[c]ensus' > /dev/null &&
    [ "$(vm_stat | awk '/Pages free/ {gsub(/\./,"",$3); print $3}')" -gt 600000 ]
}
until clear; do sleep 30; done
sleep 60
until clear; do sleep 30; done
exec zsh $HOME/trust-cg/.claude/worktrees/agent-aa09eb375ba4049fc/reports/perf/2026-10-02-darwin-x86-64-census-slice9/census/census_s9.sh "$TAG"
