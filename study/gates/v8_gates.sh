#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: regression gates for the staged library nt_fix7 (strings + big-certificate merge on top of the current
# library). Re-runs every previously PROVED fact of each package with the default driver configuration (split 8) and
# writes results v8-<pkg>; v8_compare.py then checks that every baseline PROVED fact is PROVED again with no acc_fallback.
# Two lanes in parallel (16 jobs each).
cd ${NT_BOX} || exit 1
log=${NT_BOX}/laneV8.log
run() { # name pkg baseline [extra...]
  local name=$1 pkg=$2 base=$3; shift 3
  echo "$(date -u +%FT%TZ) start $name (baseline $base) $*" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py "$name" "$pkg" --skip-build --nt-root ${NT_BOX}/nt_fix7 --jobs 16 \
    --from-results "$base" --from-verdict PROVED "$@" > ${NT_BOX}/m2_$name.ax5.out 2>&1
  echo "$(date -u +%FT%TZ) end $name rc=$? $(tail -1 ${NT_BOX}/m2_$name.ax5.out)" >> $log
}
laneA() {
  run v8-cvc5-logos ${NT_BOX}/repos/cvc5-logos cvc5-logos-nt18
  run v8-lido-srv3 ${NT_BOX}/repos/lido-srv3-proof-closure lido-srv3
  run v8-cedar-lean ${NT_BOX}/repos/cedar-spec/cedar-lean cedar-lean
  run v8-sounio ${NT_BOX}/repos/sounio/formal sounio
  run v8-asi-stack-book ${NT_BOX}/repos/asi-stack-book/lean asi-stack-book
  run v8-humanfia-icho2026 ${NT_BOX}/repos/humanfia-hoa/icho2026/gpt-5.6-sol-full68-formalization humanfia-icho2026
}
laneB() {
  run v8-zag ${NT_BOX}/repos_s/FrederickPu_Zag retry-zag
  run v8-strata ${NT_BOX}/repos/Strata strata-nt18
  run v8-trainverify ${NT_BOX}/repos/tainverify_lean/trainverify trainverify --sample 2000
  run v8-formal-conjectures ${NT_BOX}/repos/formal-conjectures formal-conjectures-nt18
}
laneA & laneB & wait
echo "$(date -u +%FT%TZ) ALL DONE" >> $log
