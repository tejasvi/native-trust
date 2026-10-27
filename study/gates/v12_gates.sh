#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: regression gates for library v12 = v10 + KernelFirstLite + iterator strings as a retry (StrLib,
# @[kernel_replace_retry], @[kernel_fold]; the iterator-strings patch), build nt_fix11. Results v12-<pkg>; laneC: cast facts,
# all 23 Zag facts; laneD: the facts of the iterator-strings patch (codegraff 5, minidregg 12, cedar 16); v12_compare.py checks.
# Two lanes in parallel (8 jobs each, the box is shared).
cd ${NT_BOX} || exit 1
log=${NT_BOX}/laneV12.log
run() { # name pkg baseline [extra...]
  local name=$1 pkg=$2 base=$3; shift 3
  echo "$(date -u +%FT%TZ) start $name (baseline $base) $*" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py "$name" "$pkg" --skip-build --nt-root ${NT_BOX}/nt_fix11 --jobs 8 \
    --from-results "$base" --from-verdict PROVED "$@" > ${NT_BOX}/m2_$name.ax5.out 2>&1
  echo "$(date -u +%FT%TZ) end $name rc=$? $(tail -1 ${NT_BOX}/m2_$name.ax5.out)" >> $log
}
laneA() {
  run v12-cvc5-logos ${NT_BOX}/repos/cvc5-logos cvc5-logos-nt18
  run v12-lido-srv3 ${NT_BOX}/repos/lido-srv3-proof-closure lido-srv3
  run v12-cedar-lean ${NT_BOX}/repos/cedar-spec/cedar-lean cedar-lean
  run v12-sounio ${NT_BOX}/repos/sounio/formal sounio
  run v12-asi-stack-book ${NT_BOX}/repos/asi-stack-book/lean asi-stack-book
  run v12-humanfia-icho2026 ${NT_BOX}/repos/humanfia-hoa/icho2026/gpt-5.6-sol-full68-formalization humanfia-icho2026
}
laneB() {
  run v12-zag ${NT_BOX}/repos_s/FrederickPu_Zag retry-zag
  run v12-strata ${NT_BOX}/repos/Strata strata-nt18
  run v12-trainverify ${NT_BOX}/repos/tainverify_lean/trainverify trainverify --sample 2000
  run v12-formal-conjectures ${NT_BOX}/repos/formal-conjectures formal-conjectures-nt18
}
laneC() {
  run v12c-asi-stack-book ${NT_BOX}/repos/asi-stack-book/lean v9c-asi-stack-book
  run v12c-formal-conjectures ${NT_BOX}/repos/formal-conjectures v9c-formal-conjectures
  echo "$(date -u +%FT%TZ) start v12-zag-all (all retry-zag facts)" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py v12-zag-all ${NT_BOX}/repos_s/FrederickPu_Zag --skip-build --nt-root ${NT_BOX}/nt_fix11 --jobs 8 \
    --from-results retry-zag > ${NT_BOX}/m2_v12-zag-all.ax5.out 2>&1
  rc=$?
  echo "$(date -u +%FT%TZ) end v12-zag-all rc=$rc $(tail -1 ${NT_BOX}/m2_v12-zag-all.ax5.out)" >> $log
}
laneD() {
  run v12s-codegraff ${NT_BOX}/repos_s/justrach_codegraff/lean-proofs v8s-codegraff-nt9c
  run v12s-minidregg ${NT_BOX}/repos_s/emberian_minidregg v8s-minidregg-nt9c
  run v12s-cedar ${NT_BOX}/repos/cedar-spec/cedar-lean v8s-cedar-nt9c
}
laneA & laneB & laneC & laneD & wait
echo "$(date -u +%FT%TZ) ALL DONE" >> $log
