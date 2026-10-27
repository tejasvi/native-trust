#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# copies_scan_v1.sh (read-only; run on the box as root or ntbuild with bash -s < this file): for every package of the study, the
# per-fact logs whose fact was PROVED (driver m2_axioms*.py: ax1/ax2 logs) and how many of them report copies > 0 on an NT line
# (copies of definitions that the kernel cannot evaluate as they stand, made by the copier); for rs-mca's sub-projects of the earlier
# per-theorem driver, its check logs (chk*.log) with KERNELIZED and how many of them report copies > 0. Prints one line per package.
export LC_ALL=C
W=${NT_BOX}/work
cd "$W" || exit 1
for p in trainverify cvc5-logos humanfia-icho2026 formal-conjectures longfellow-zk asi-stack-book rs-mca-m31_dyadic_weight_laws \
         rs-mca-m31_flatness_keystone sounio lido-srv3 berry-esseen strata clean cedar-lean aks sorting-network-expanders aeneas-lean; do
  [ -d "$p" ] || { echo "$p: no logs"; continue; }
  proved=$(find "$p" -maxdepth 1 -name 'ax[12]*_*.log' -print0 | xargs -0 -r grep -l '^PROVED ' | wc -l)
  withc=$(find "$p" -maxdepth 1 -name 'ax[12]*_*.log' -print0 | xargs -0 -r grep -l '^PROVED ' | xargs -r grep -l '^NT .*copies=[1-9]' | wc -l)
  echo "$p: logs of PROVED facts $proved, with copies $withc"
done
for p in rs-mca-RS_disproof_v3 rs-mca-asymptotic_spine rs-mca-cs25_cap_v13 rs-mca-l1_threshold_ledger rs-mca-moment_to_max \
         rs-mca-razorband_witness rs-mca-syndrome_line rs-mca-syndrome_secant; do
  [ -d "$p" ] || { echo "$p: no logs"; continue; }
  kern=$(find "$p" -maxdepth 1 -name 'chk*.log' -print0 | xargs -0 -r grep -l '^KERNELIZED ' | wc -l)
  withc=$(find "$p" -maxdepth 1 -name 'chk*.log' -print0 | xargs -0 -r grep -l '^KERNELIZED ' | xargs -r grep -l 'copies=[1-9]' | wc -l)
  echo "$p (per-theorem driver): check logs with KERNELIZED $kern, with copies $withc"
  find "$p" -maxdepth 1 -name 'chk*.log' -print0 | xargs -0 -r grep -l '^KERNELIZED ' | xargs -r grep -h '^OK.*copies=[1-9]' | cut -f1,2,7- | sed 's/^/  /'
done
