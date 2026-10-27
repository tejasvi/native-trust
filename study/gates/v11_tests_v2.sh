#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v2: TypesRepro compared on its KERNELIZED/OK/FAIL/rc lines only (trace continuation lines differ by toolchain).
# run as ntbuild: self-contained tests of library v11 (build nt_fix10) for toolchain TC, against tests/kz/*.expected
# (normalized: "(N ms)", kernel_ms/total_ms masked, time lines and NT trace lines dropped). Files staged in
# $NT_BOX/v11_tests/src (tests/kz + tests/StrLib.lean). Outputs in $NT_BOX/v11_tests/<TC>/ (v2).
TC=${1:?}; B=${NT_BOX}/v11_tests
case $TC in nightly-*) L=${NT_BOX}/elan/toolchains/leanprover--lean4-nightly---$TC/bin/lean;; *) L=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin/lean;; esac
export ELAN_HOME=${NT_BOX}/elan LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
D=$B/$TC
case "$D" in ${NT_BOX}/v11_tests/v4.*|${NT_BOX}/v11_tests/nightly-*) ;; *) echo "bad dir $D"; exit 2;; esac
mkdir -p $D && cd $D || exit 3
NTL=${NT_BOX}/nt_fix10/$TC/.lake/build/lib/lean
TESTS="KernelFirstTest KernelFirstModule LintKernel LintStrict AuditMod KernelFirstLite KernelFirstScope KernelFirstScopeModule CastRetry TypesRepro StrLib"
for f in $TESTS KzNative; do if [ -f $B/src/kz/$f.lean ]; then cp $B/src/kz/$f.lean .; else cp $B/src/$f.lean .; fi; done
LEAN_PATH=$NTL:$D $L -o KzNative.olean KzNative.lean > KzNative.build.out 2>&1
run() { ( export LEAN_PATH="$NTL:$D"; ulimit -v $((48*1024*1024))
  timeout -k 30 900 $L -j1 --tstack=1048576 $1.lean > $1.out 2>&1; echo "rc=$?" >> $1.out ) ; }
pids=(); n=0
for f in $TESTS; do run $f & pids+=($!); n=$((n+1)); [ $n -ge 4 ] && { wait ${pids[@]}; pids=(); n=0; }; done
wait ${pids[@]}
normx() { grep -v '^secs \|^Command exited\|^NT ' "$1" | sed -E 's/\(([0-9]+) ms\)/(N ms)/g; s/\(([0-9]+) ms in total\)/(N ms in total)/g; s/kernel_ms=[0-9]+/kernel_ms=_/; s/total_ms=[0-9]+/total_ms=_/'; }
for f in $TESTS; do
  e=$B/src/kz/$f.expected
  if [ $f = TypesRepro ]; then sel() { normx "$1" | grep -E '^(KERNELIZED|OK|FAIL|rc=)'; }; else sel() { normx "$1"; }; fi
  if [ -f $e ]; then if diff <(sel $f.out) <(sel $e) > $f.exp.diff; then x=SAME; else x="DIFF($(grep -c '^[<>]' $f.exp.diff))"; fi; else x="no-expected $(grep -c . $f.out) lines"; fi
  echo "$TC $f: $(grep '^rc=' $f.out) vs_expected=$x"
done
