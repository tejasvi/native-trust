#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# (as ntbuild on the box) wait for PID $1, then locate the literal size above which the default maxRecDepth
# gives "(kernel) deep recursion detected" (DW21 prefixes, no maxRecDepth option, 20 s timeout; dir thr).
set -u
W=${1:?}
while kill -0 "$W" 2>/dev/null; do sleep 5; done
cd ${NT_BOX}/strlit || exit 2
mkdir -p thr
S=""
for n in 1500 2000 2500 3000 3500 4000 5000 6000; do S="$S dw:$n:ubs:dk"; done
python3 -I gen4.py ${NT_BOX}/strlit/thr $S > /dev/null
N=""
for f in thr/dw_*_ubs_dk.lean; do b=$(basename $f .lean); sed '/maxRecDepth/d' $f > thr/${b}_nomrd.lean; rm -f $f; N="$N ${b}_nomrd"; done
TC=v4.34.0-rc2
echo "start (TO=20) $(date -u +%H:%M:%S)" >> thr/summary.$TC.tsv
TO=20 ./run2.sh $TC ${NT_BOX}/strlit/thr $N >> thr/summary.$TC.tsv
for f in thr/*.log; do printf '%s\t%s\n' "$(basename $f)" "$(grep -o 'error: .\{0,60\}' $f | head -1)"; done >> thr/summary.$TC.tsv
echo "end $(date -u +%H:%M:%S)" >> thr/summary.$TC.tsv
