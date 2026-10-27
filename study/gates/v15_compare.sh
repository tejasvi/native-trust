#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v15_compare.sh (library v15): run as ntbuild. For each toolchain, compares the v15 test outputs
# ($NT_BOX/v15_tests/v15/<tc>) with the v14 ones ($NT_BOX/v14_tests/<tc> where the v14 run exists, else the
# v14 baseline $NT_BOX/v15_tests/v14base/<tc>), normalized as the test scripts do (times masked, time and NT
# trace lines dropped); TypesRepro also on its verdict lines only. StageAxioms is new: compared where the baseline has it.
normx() { grep -v '^secs \|^Command exited\|^NT ' "$1" | sed -E 's/\(([0-9]+) ms\)/(N ms)/g; s/\(([0-9]+) ms in total\)/(N ms in total)/g; s/kernel_ms=[0-9]+/kernel_ms=_/; s/total_ms=[0-9]+/total_ms=_/'; }
TESTS="KernelFirstTest KernelFirstModule LintKernel LintStrict AuditMod KernelFirstLite KernelFirstScope KernelFirstScopeModule CastRetry TypesRepro StrLib PlatformCases StageAxioms"
for tc in ${TCS:?}; do
  N=${NT_BOX}/v15_tests/v15/$tc
  if [ -d ${NT_BOX}/v14_tests/$tc ]; then O=${NT_BOX}/v14_tests/$tc; src=v14_tests; else O=${NT_BOX}/v15_tests/v14base/$tc; src=v14base; fi
  line="$tc (baseline $src):"
  for f in $TESTS; do
    if [ ! -f $N/$f.out ]; then line="$line $f=MISSING_V15"; continue; fi
    if [ ! -f $O/$f.out ]; then line="$line $f=new"; continue; fi
    if diff <(normx $O/$f.out) <(normx $N/$f.out) > /dev/null; then r=same
    else
      r="DIFF($(diff <(normx $O/$f.out) <(normx $N/$f.out) | grep -c '^[<>]'))"
      if [ $f = TypesRepro ] && diff <(normx $O/$f.out | grep -E '^(KERNELIZED|OK|FAIL|rc=)') <(normx $N/$f.out | grep -E '^(KERNELIZED|OK|FAIL|rc=)') > /dev/null; then r="$r,verdicts-same"; fi
    fi
    [ $r = same ] || line="$line $f=$r"
  done
  echo "$line"
done
