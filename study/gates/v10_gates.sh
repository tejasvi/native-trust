#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: regression gates for library v10 = v9 + copies in types (keepTypes, motive equations, nested transport,
# NativeTrust/Param.lean), build nt_fix9. Re-runs every previously PROVED fact of each package (split 8), results
# v10-<pkg>; laneC also re-runs all 23 Zag facts and the 13 cast facts of v9 (baselines retry-zag, v9c-*); v10_compare.py checks.
# Two lanes in parallel (8 jobs each, the box is shared).
cd ${NT_BOX} || exit 1
log=${NT_BOX}/laneV10.log
run() { # name pkg baseline [extra...]
  local name=$1 pkg=$2 base=$3; shift 3
  echo "$(date -u +%FT%TZ) start $name (baseline $base) $*" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py "$name" "$pkg" --skip-build --nt-root ${NT_BOX}/nt_fix9 --jobs 8 \
    --from-results "$base" --from-verdict PROVED "$@" > ${NT_BOX}/m2_$name.ax5.out 2>&1
  echo "$(date -u +%FT%TZ) end $name rc=$? $(tail -1 ${NT_BOX}/m2_$name.ax5.out)" >> $log
}
laneA() {
  run v10-cvc5-logos ${NT_BOX}/repos/cvc5-logos cvc5-logos-nt18
  run v10-lido-srv3 ${NT_BOX}/repos/lido-srv3-proof-closure lido-srv3
  run v10-cedar-lean ${NT_BOX}/repos/cedar-spec/cedar-lean cedar-lean
  run v10-sounio ${NT_BOX}/repos/sounio/formal sounio
  run v10-asi-stack-book ${NT_BOX}/repos/asi-stack-book/lean asi-stack-book
  run v10-humanfia-icho2026 ${NT_BOX}/repos/humanfia-hoa/icho2026/gpt-5.6-sol-full68-formalization humanfia-icho2026
}
laneB() {
  run v10-zag ${NT_BOX}/repos_s/FrederickPu_Zag retry-zag
  run v10-strata ${NT_BOX}/repos/Strata strata-nt18
  run v10-trainverify ${NT_BOX}/repos/tainverify_lean/trainverify trainverify --sample 2000
  run v10-formal-conjectures ${NT_BOX}/repos/formal-conjectures formal-conjectures-nt18
}
laneC() {
  run v10c-asi-stack-book ${NT_BOX}/repos/asi-stack-book/lean v9c-asi-stack-book
  run v10c-formal-conjectures ${NT_BOX}/repos/formal-conjectures v9c-formal-conjectures
  echo "$(date -u +%FT%TZ) start v10-zag-all (all retry-zag facts)" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py v10-zag-all ${NT_BOX}/repos_s/FrederickPu_Zag --skip-build --nt-root ${NT_BOX}/nt_fix9 --jobs 8 \
    --from-results retry-zag > ${NT_BOX}/m2_v10-zag-all.ax5.out 2>&1
  rc=$?
  echo "$(date -u +%FT%TZ) end v10-zag-all rc=$rc $(tail -1 ${NT_BOX}/m2_v10-zag-all.ax5.out)" >> $log
}
laneA & laneB & laneC & wait
echo "$(date -u +%FT%TZ) ALL DONE" >> $log
