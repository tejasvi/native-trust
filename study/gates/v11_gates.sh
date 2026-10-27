#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: regression gates for library v11 = v10 + iterator strings (StrLib, @[kernel_fold]) + KernelFirstLite,
# build nt_fix10. Re-runs every previously PROVED fact of each package (split 8), results v11-<pkg>; laneC re-runs
# the 13 cast facts, all 23 Zag facts, and the iterator-string facts proved by the iterator-strings patch (v8s-*-nt9c); v11_compare.py.
# Two lanes in parallel (8 jobs each, the box is shared).
cd ${NT_BOX} || exit 1
log=${NT_BOX}/laneV11.log
run() { # name pkg baseline [extra...]
  local name=$1 pkg=$2 base=$3; shift 3
  echo "$(date -u +%FT%TZ) start $name (baseline $base) $*" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py "$name" "$pkg" --skip-build --nt-root ${NT_BOX}/nt_fix10 --jobs 8 \
    --from-results "$base" --from-verdict PROVED "$@" > ${NT_BOX}/m2_$name.ax5.out 2>&1
  echo "$(date -u +%FT%TZ) end $name rc=$? $(tail -1 ${NT_BOX}/m2_$name.ax5.out)" >> $log
}
laneA() {
  run v11-cvc5-logos ${NT_BOX}/repos/cvc5-logos cvc5-logos-nt18
  run v11-lido-srv3 ${NT_BOX}/repos/lido-srv3-proof-closure lido-srv3
  run v11-cedar-lean ${NT_BOX}/repos/cedar-spec/cedar-lean cedar-lean
  run v11-sounio ${NT_BOX}/repos/sounio/formal sounio
  run v11-asi-stack-book ${NT_BOX}/repos/asi-stack-book/lean asi-stack-book
  run v11-humanfia-icho2026 ${NT_BOX}/repos/humanfia-hoa/icho2026/gpt-5.6-sol-full68-formalization humanfia-icho2026
}
laneB() {
  run v11-zag ${NT_BOX}/repos_s/FrederickPu_Zag retry-zag
  run v11-strata ${NT_BOX}/repos/Strata strata-nt18
  run v11-trainverify ${NT_BOX}/repos/tainverify_lean/trainverify trainverify --sample 2000
  run v11-formal-conjectures ${NT_BOX}/repos/formal-conjectures formal-conjectures-nt18
}
laneC() {
  run v11c-asi-stack-book ${NT_BOX}/repos/asi-stack-book/lean v9c-asi-stack-book
  run v11c-formal-conjectures ${NT_BOX}/repos/formal-conjectures v9c-formal-conjectures
  echo "$(date -u +%FT%TZ) start v11-zag-all (all retry-zag facts)" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py v11-zag-all ${NT_BOX}/repos_s/FrederickPu_Zag --skip-build --nt-root ${NT_BOX}/nt_fix10 --jobs 8 \
    --from-results retry-zag > ${NT_BOX}/m2_v11-zag-all.ax5.out 2>&1
  rc=$?
  echo "$(date -u +%FT%TZ) end v11-zag-all rc=$rc $(tail -1 ${NT_BOX}/m2_v11-zag-all.ax5.out)" >> $log
}
laneD() {
  run v11s-codegraff ${NT_BOX}/repos_s/justrach_codegraff/lean-proofs v8s-codegraff-nt9c
  run v11s-minidregg ${NT_BOX}/repos_s/emberian_minidregg v8s-minidregg-nt9c
  run v11s-cedar ${NT_BOX}/repos/cedar-spec/cedar-lean v8s-cedar-nt9c
}
laneA & laneB & laneC & laneD & wait
echo "$(date -u +%FT%TZ) ALL DONE" >> $log
