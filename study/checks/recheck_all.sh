#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: independent re-check (nanoda + con-ron) of stratified samples, one package after another
cd ${NT_BOX}
X=${NT_BOX}/tools; R=${NT_BOX}/repos
run() { echo "$(date -u +%FT%TZ) start $1"; timeout 7000 python3 -u recheck.py "$@" > ${NT_BOX}/work/recheck_$1.out 2>&1; echo "$(date -u +%FT%TZ) end $1 :: $(grep VERDICT ${NT_BOX}/work/recheck_$1.out)"; }
run lido-srv3 $R/lido-srv3-proof-closure 30 --export $X/lean4export-v4.31.0/.lake/build/bin/lean4export --mem 300
run rs-mca-m31_dyadic_weight_laws $R/rs-mca/experimental/lean/m31_dyadic_weight_laws 9 --export $X/lean4export-v4.31.0/.lake/build/bin/lean4export --mem 300
run cedar-lean $R/cedar-spec/cedar-lean 10 --export $X/lean4export-v4.35.0/.lake/build/bin/lean4export --mem 300
run strata $R/Strata 20 --results-name strata-fuel --export $X/lean4export-v4.31.0/.lake/build/bin/lean4export --mem 300
run asi-stack-book $R/asi-stack-book/lean 30 --export $X/lean4export-v4.31.0/.lake/build/bin/lean4export --mem 300
run sounio $R/sounio/formal 30 --export $X/lean4export-v4.30.0-rc2/.lake/build/bin/lean4export --mem 300
run humanfia-icho2026 $R/humanfia-hoa/icho2026/gpt-5.6-sol-full68-formalization 40 --export $X/lean4export-v4.31.0/.lake/build/bin/lean4export --mem 300
run longfellow-zk $R/longfellow-zk/formal 30 --export $X/lean4export-v4.31.0/.lake/build/bin/lean4export --mem 300
run formal-conjectures $R/formal-conjectures 30 --results-name formal-conjectures-fuel --export $X/lean4export-v4.33.1/.lake/build/bin/lean4export --mem 300
run clean-remedy $R/clean 30 --export $X/lean4export-v4.33.1/.lake/build/bin/lean4export --mem 300 --extra-import KernelFactsClean --extra-path ${NT_BOX}/work/clean-remedy/extra
run trainverify $R/tainverify_lean/trainverify 40 --export $X/lean4export-v4.32.2/.lake/build/bin/lean4export --mem 300
echo "$(date -u +%FT%TZ) all done"
