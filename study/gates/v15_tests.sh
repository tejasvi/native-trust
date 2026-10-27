#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v15_tests.sh (library v15; from v14_tests.sh, adds StageAxioms; no ulimit: run it inside a systemd scope
# that carries MemoryMax). Run as ntbuild: the self-contained tests for toolchain TC with the NativeTrust build ROOT/TC,
# against tests/kz/*.expected (normalized: "(N ms)", kernel_ms/total_ms masked, time lines and NT trace lines dropped).
# Sources staged in $NT_BOX/v15_tests/src (tests/kz + tests/StrLib.lean). Outputs in OUT/<TC>/.
# usage: v15_tests.sh TC ROOT OUT
TC=${1:?}; ROOT=${2:?}; OUT=${3:?}; B=${NT_BOX}/v15_tests
case "$OUT" in ${NT_BOX}/v15_tests/v15|${NT_BOX}/v15_tests/v14base) ;; *) echo "bad OUT $OUT"; exit 2;; esac
case "$ROOT" in ${NT_BOX}/nt_fix14|${NT_BOX}/nt_fix13) ;; *) echo "bad ROOT $ROOT"; exit 2;; esac
case $TC in nightly-*) L=${NT_BOX}/elan/toolchains/leanprover--lean4-nightly---$TC/bin/lean;; *) L=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin/lean;; esac
export ELAN_HOME=${NT_BOX}/elan LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
D=$OUT/$TC
case "$D" in "$OUT"/v4.*|"$OUT"/nightly-*) ;; *) echo "bad dir $D"; exit 2;; esac
[ -e "$D" ] && { echo "refusing: $D exists"; exit 3; }
mkdir -p $D && cd $D || exit 3
NTL=$ROOT/$TC/.lake/build/lib/lean
TESTS="KernelFirstTest KernelFirstModule LintKernel LintStrict AuditMod KernelFirstLite KernelFirstScope KernelFirstScopeModule CastRetry TypesRepro StrLib PlatformCases StageAxioms"
for f in $TESTS KzNative; do if [ -f $B/src/kz/$f.lean ]; then cp $B/src/kz/$f.lean .; else cp $B/src/$f.lean .; fi; done
LEAN_PATH=$NTL:$D $L -o KzNative.olean KzNative.lean > KzNative.build.out 2>&1
run() { ( export LEAN_PATH="$NTL:$D"
  timeout -k 30 900 $L -j1 --tstack=1048576 $1.lean > $1.out 2>&1; echo "rc=$?" >> $1.out ) ; }
pids=(); n=0
for f in $TESTS; do run $f & pids+=($!); n=$((n+1)); [ $n -ge 4 ] && { wait ${pids[@]}; pids=(); n=0; }; done
wait ${pids[@]}
normx() { grep -v '^secs \|^Command exited\|^NT ' "$1" | sed -E 's/\(([0-9]+) ms\)/(N ms)/g; s/\(([0-9]+) ms in total\)/(N ms in total)/g; s/kernel_ms=[0-9]+/kernel_ms=_/; s/total_ms=[0-9]+/total_ms=_/'; }
for f in $TESTS; do
  e=$B/src/kz/$f.expected; [ -f $e ] || e=$B/src/$f.expected
  if [ $f = TypesRepro ]; then sel() { normx "$1" | grep -E '^(KERNELIZED|OK|FAIL|rc=)'; }; else sel() { normx "$1"; }; fi
  if [ -f $e ]; then if diff <(sel $f.out) <(sel $e) > $f.exp.diff; then x=SAME; else x="DIFF($(grep -c '^[<>]' $f.exp.diff))"; fi; else x="no-expected $(grep -c . $f.out) lines"; fi
  echo "$TC $f: $(grep '^rc=' $f.out) vs_expected=$x"
done
