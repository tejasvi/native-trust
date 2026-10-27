#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: build NativeTrust with the copy patch and the retry design (transport and skipUnchanged only in a fuel-route retry) (sources in
# $NT_BOX/nt_fix3/src) into $NT_BOX/nt_fix3/<tc> for each toolchain in TCS
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=2
S=${NT_BOX}/nt_fix3/src; W=${NT_BOX}/nt_fix3
for tc in ${TCS:?}; do
  ( d=$W/$tc
    case "$d" in ${NT_BOX}/nt_fix3/v4.*|${NT_BOX}/nt_fix3/nightly-*) ;; *) echo "bad dir $d"; exit 2;; esac
    mkdir -p "$d/NativeTrust"
    cp $S/lakefile.toml $S/NativeTrust.lean "$d/"; cp $S/NativeTrust/*.lean "$d/NativeTrust/"
    echo "leanprover/lean4:$tc" > "$d/lean-toolchain"
    cd "$d" && ( ulimit -v 50331648; timeout 1800 lake build > build.log 2>&1; echo "exit $?" >> build.log )
    if grep -q '^exit 0' build.log; then echo "$tc OK $(date -u +%T)"; else echo "$tc FAIL: $(grep -m5 'error' build.log | cut -c1-300 | tr '\n' ' ')"; fi
  ) > $W/result_$tc.txt 2>&1 &
done
wait; cat $W/result_*.txt
