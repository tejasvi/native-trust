#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild (v11 = v10 + KernelFirstLite + iterator strings as a retry (StrLib, @[kernel_replace_retry], @[kernel_fold]), stub on 4.27-4.29; earlier v10 build had StrLib in the first attempt; v9 = v8 + copies in types: keepTypes, motive equations, nested transport, NativeTrust/Param.lean; v8 = v7 + cast retry, NativeTrust/CastFree.lean; v7 = staged strings + big-certificate merge; v6: also the driver, NativeTrust/Driver/*.lean, and the `ntrust` executable with `migrate`): build the
# current NativeTrust (staged in $NT_BOX/nt_fix11/src) into $NT_BOX/nt_fix11/<tc> for each toolchain in TCS
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=2
S=${NT_BOX}/nt_fix11/src; W=${NT_BOX}/nt_fix11
for tc in ${TCS:?}; do
  ( d=$W/$tc
    case "$d" in ${NT_BOX}/nt_fix11/v4.*|${NT_BOX}/nt_fix11/nightly-*) ;; *) echo "bad dir $d"; exit 2;; esac
    mkdir -p "$d/NativeTrust/Driver"
    cp $S/lakefile.toml $S/NativeTrust.lean "$d/"; cp $S/NativeTrust/*.lean "$d/NativeTrust/"; cp $S/NativeTrust/Driver/*.lean "$d/NativeTrust/Driver/"
    case $tc in v4.27*|v4.28*|v4.29*) cp $S/NativeTrust/CSimpCompatStub.lean.txt "$d/NativeTrust/CSimpCompat.lean"; cp $S/NativeTrust/StrLibStub.lean.txt "$d/NativeTrust/StrLib.lean";; esac
    echo "leanprover/lean4:$tc" > "$d/lean-toolchain"
    cd "$d" && ( ulimit -v 50331648; timeout 2400 lake build NativeTrust NativeTrust.KernelFirst NativeTrust.KernelFirstLite ntrust > build.log 2>&1; echo "exit $?" >> build.log )
    if grep -q '^exit 0' build.log; then echo "$tc OK $(date -u +%T)"; else echo "$tc FAIL: $(grep -m5 'error' build.log | cut -c1-300 | tr '\n' ' ')"; fi
  ) > $W/result_$tc.txt 2>&1 &
done
wait; cat $W/result_*.txt
