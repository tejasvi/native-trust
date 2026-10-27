#!/bin/bash
# v15_compare_artifact.sh: the comparison of v15_compare.sh, on the copies in this artifact. For each toolchain, the test outputs
# of library v15 (study/results/gates/v15_tests/v15/<tc>) against those of v14 (study/results/gates/v14_tests/<tc> where that run
# exists, else study/results/gates/v15_tests/v14base/<tc>), normalized as v15_tests.sh normalizes them (times masked, time and NT
# trace lines dropped); TypesRepro also on its verdict lines alone. A test missing from the baseline is reported as new. Then
# the final StageAxioms test on every toolchain, with v15 and with v14 (stage2/), against tests/kz/StageAxioms.expected.
# Run from the artifact's top directory.
G=study/results/gates
normx() { grep -v '^secs \|^Command exited\|^NT ' "$1" | sed -E 's/\(([0-9]+) ms\)/(N ms)/g; s/\(([0-9]+) ms in total\)/(N ms in total)/g; s/kernel_ms=[0-9]+/kernel_ms=_/; s/total_ms=[0-9]+/total_ms=_/'; }
TESTS="KernelFirstTest KernelFirstModule LintKernel LintStrict AuditMod KernelFirstLite KernelFirstScope KernelFirstScopeModule CastRetry TypesRepro StrLib PlatformCases StageAxioms"
n=0; extra=""
for d in $G/v15_tests/v15/*/; do
  tc=$(basename "$d"); n=$((n + 1))
  if [ -d $G/v14_tests/$tc ]; then O=$G/v14_tests/$tc; src=v14_tests; else O=$G/v15_tests/v14base/$tc; src=v14base; fi
  line="$tc (baseline $src):"
  for f in $TESTS; do
    if [ ! -f "$d/$f.out" ]; then line="$line $f=MISSING_V15"; continue; fi
    if [ ! -f "$O/$f.out" ]; then line="$line $f=new"; continue; fi
    if diff <(normx "$O/$f.out") <(normx "$d/$f.out") > /dev/null; then continue; fi
    r="DIFF($(diff <(normx "$O/$f.out") <(normx "$d/$f.out") | grep -c '^[<>]'))"
    if [ $f = TypesRepro ] && diff <(normx "$O/$f.out" | grep -E '^(KERNELIZED|OK|FAIL|rc=)') <(normx "$d/$f.out" | grep -E '^(KERNELIZED|OK|FAIL|rc=)') > /dev/null; then
      r="$r,verdicts-same"; fi
    line="$line $f=$r"
  done
  echo "$line"
  rest=$(echo "${line#*:}" | tr ' ' '\n' | grep -v '^StageAxioms=new$' | grep . | tr '\n' ' ')
  [ -n "$rest" ] && extra="$extra $tc: ${rest% };"
done
echo "toolchains compared: $n"
echo "differences other than a new StageAxioms test:${extra:- none}"
same=0; total=0
for o in $G/v15_tests/stage2/*/*/StageAxioms.out; do
  total=$((total + 1))
  diff <(normx "$o") <(normx tests/kz/StageAxioms.expected) > /dev/null && same=$((same + 1))
done
echo "final StageAxioms test (v15 and v14): $same of $total identical to tests/kz/StageAxioms.expected"
