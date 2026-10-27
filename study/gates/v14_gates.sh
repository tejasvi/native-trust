#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: regression gates for library v14 (build nt_fix13; see nt_fix13_build.sh), as for the earlier library, plus
# laneE: all facts of ninegates (the word-size case split) with a 3,600 s fact timeout. Results v14-<pkg>; laneC: cast facts, all 23 Zag facts; laneD: the
# iterator-string facts (codegraff 5, minidregg 12, cedar 16); 6 jobs per lane (the box is shared); v14_compare.py checks.
# Two lanes in parallel (8 jobs each, the box is shared).
cd ${NT_BOX} || exit 1
log=${NT_BOX}/laneV14.log
run() { # name pkg baseline [extra...]
  local name=$1 pkg=$2 base=$3; shift 3
  echo "$(date -u +%FT%TZ) start $name (baseline $base) $*" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py "$name" "$pkg" --skip-build --nt-root ${NT_BOX}/nt_fix13 --jobs 6 \
    --from-results "$base" --from-verdict PROVED "$@" > ${NT_BOX}/m2_$name.ax5.out 2>&1
  echo "$(date -u +%FT%TZ) end $name rc=$? $(tail -1 ${NT_BOX}/m2_$name.ax5.out)" >> $log
}
laneA() {
  run v14-cvc5-logos ${NT_BOX}/repos/cvc5-logos cvc5-logos-nt18
  run v14-lido-srv3 ${NT_BOX}/repos/lido-srv3-proof-closure lido-srv3
  run v14-cedar-lean ${NT_BOX}/repos/cedar-spec/cedar-lean cedar-lean
  run v14-sounio ${NT_BOX}/repos/sounio/formal sounio
  run v14-asi-stack-book ${NT_BOX}/repos/asi-stack-book/lean asi-stack-book
  run v14-humanfia-icho2026 ${NT_BOX}/repos/humanfia-hoa/icho2026/gpt-5.6-sol-full68-formalization humanfia-icho2026
}
laneB() {
  run v14-zag ${NT_BOX}/repos_s/FrederickPu_Zag retry-zag
  run v14-strata ${NT_BOX}/repos/Strata strata-nt18
  run v14-trainverify ${NT_BOX}/repos/tainverify_lean/trainverify trainverify --sample 2000
  run v14-formal-conjectures ${NT_BOX}/repos/formal-conjectures formal-conjectures-nt18
}
laneC() {
  run v14c-asi-stack-book ${NT_BOX}/repos/asi-stack-book/lean v9c-asi-stack-book
  run v14c-formal-conjectures ${NT_BOX}/repos/formal-conjectures v9c-formal-conjectures
  echo "$(date -u +%FT%TZ) start v14-zag-all (all retry-zag facts)" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py v14-zag-all ${NT_BOX}/repos_s/FrederickPu_Zag --skip-build --nt-root ${NT_BOX}/nt_fix13 --jobs 6 \
    --from-results retry-zag > ${NT_BOX}/m2_v14-zag-all.ax5.out 2>&1
  rc=$?
  echo "$(date -u +%FT%TZ) end v14-zag-all rc=$rc $(tail -1 ${NT_BOX}/m2_v14-zag-all.ax5.out)" >> $log
}
laneD() {
  run v14s-codegraff ${NT_BOX}/repos_s/justrach_codegraff/lean-proofs v8s-codegraff-nt9c
  run v14s-minidregg ${NT_BOX}/repos_s/emberian_minidregg v8s-minidregg-nt9c
  run v14s-cedar ${NT_BOX}/repos/cedar-spec/cedar-lean v8s-cedar-nt9c
}
laneE() {
  run v14s-ninegates ${NT_BOX}/repos_s/sun123zxy_ninegates-lean4 s_sun123zxy_ninegates_lean4 --fact-timeout 3600
}
laneA & laneB & laneC & laneD & laneE & wait
echo "$(date -u +%FT%TZ) ALL DONE" >> $log
