#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# (as ntbuild on the box) wait for the m5 batch (PID given) to end, then run the period-8 block probes (batch m6).
set -u
W=${1:?}
while kill -0 "$W" 2>/dev/null; do sleep 5; done
cd ${NT_BOX}/strlit || exit 2
./batch4.sh v4.34.0-rc2 ${NT_BOX}/strlit/m6 B-613~201_:8000:ubs:dk B-613~2000:8000:ubs:dk B-613~200_:8000:ubs:dk B-613~200_:7000:ubs:dk B-200_613~:8000:ubs:dk B-61302000:8000:ubs:dk B-abcdefgh:8000:ubs:dk B-aaaaaaab:8000:ubs:dk
