#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# (as ntbuild on the box) is the default-maxRecDepth "deep recursion" threshold content dependent? (no maxRecDepth, TO=60; dir thr2)
set -u
cd ${NT_BOX}/strlit || exit 2
mkdir -p thr2
python3 -I gen4.py ${NT_BOX}/strlit/thr2 a:2000:ubs:dk a:8000:ubs:dk rep8:4000:ubs:dk dw:1750:ubs:dk > /dev/null
N=""
for f in thr2/*_ubs_dk.lean; do b=$(basename $f .lean); sed '/maxRecDepth/d' $f > thr2/${b}_nomrd.lean; rm -f $f; N="$N ${b}_nomrd"; done
TC=v4.34.0-rc2
echo "start (TO=60) $(date -u +%H:%M:%S)" >> thr2/summary.$TC.tsv
TO=60 ./run2.sh $TC ${NT_BOX}/strlit/thr2 $N >> thr2/summary.$TC.tsv
for f in thr2/*.log; do printf '%s\t%s\n' "$(basename $f)" "$(grep -o 'error: .\{0,60\}' $f | head -1)"; done >> thr2/summary.$TC.tsv
echo "end $(date -u +%H:%M:%S)" >> thr2/summary.$TC.tsv
