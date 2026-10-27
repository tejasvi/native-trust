#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v15_stage2.sh (library v15): run as ntbuild inside a systemd scope that carries MemoryMax. The final
# tests/kz/StageAxioms.lean (its negative case uses an axiom instead of `sorry`, whose warning is worded differently
# before 4.29) on every toolchain given, with the v15 build (nt_fix14) and with the v14 build (nt_fix13). Outputs in
# $NT_BOX/v15_tests/stage2/{v15,v14}/<tc>/, each compared with src/kz/StageAxioms.expected, normalized as
# v15_tests.sh does.
# usage: v15_stage2.sh TC...
B=${NT_BOX}/v15_tests; S=$B/stage2
[ $# -gt 0 ] || { echo "no toolchains"; exit 2; }
[ -e $S ] && { echo "refusing: $S exists"; exit 3; }
export ELAN_HOME=${NT_BOX}/elan LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
normx() { grep -v '^secs \|^Command exited\|^NT ' "$1" | sed -E 's/\(([0-9]+) ms\)/(N ms)/g; s/\(([0-9]+) ms in total\)/(N ms in total)/g; s/kernel_ms=[0-9]+/kernel_ms=_/; s/total_ms=[0-9]+/total_ms=_/'; }
for tc in "$@"; do
  case $tc in nightly-*) L=${NT_BOX}/elan/toolchains/leanprover--lean4-nightly---$tc/bin/lean;; *) L=${NT_BOX}/elan/toolchains/leanprover--lean4---$tc/bin/lean;; esac
  for spec in v15:${NT_BOX}/nt_fix14 v14:${NT_BOX}/nt_fix13; do
    lab=${spec%%:*}; ROOT=${spec#*:}; D=$S/$lab/$tc
    mkdir -p $D && cd $D || exit 3
    cp $B/src/kz/StageAxioms.lean .
    LEAN_PATH=$ROOT/$tc/.lake/build/lib/lean:$D timeout -k 30 900 $L -j1 --tstack=1048576 StageAxioms.lean > StageAxioms.out 2>&1
    echo "rc=$?" >> StageAxioms.out
    if diff <(normx StageAxioms.out) <(normx $B/src/kz/StageAxioms.expected) > StageAxioms.exp.diff; then x=SAME
    else x="DIFF($(grep -c '^[<>]' StageAxioms.exp.diff))"; fi
    echo "$tc $lab StageAxioms: $(grep '^rc=' StageAxioms.out) vs_expected=$x"
  done
done
