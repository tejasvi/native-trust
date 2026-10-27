#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# Test of `ntrust migrate --fact-budget` / `--max-slowdown` (v3: the defaults are budget 2000 + max-slowdown 2;
# results kept outside the project, a rebuild after each --restore). Run as ntbuild:
#   run_test.sh NT_DIR TC WORK   (NT_DIR: a NativeTrust build with the patched driver for toolchain TC;
#                                    WORK: an empty directory, created; the fixture is copied there)
# Expected (checked below, PASS/FAIL per line):
#  defaults (= budget 2000, max-slowdown 2): cheapSum and cheapMul replaced, slowDivSum kept (budget 2000: EXPENSIVE), the cheap example
#               replaced, the slow example kept (over the budget in the build round), native axioms 3 -> 1;
#               the final sources contain no `set_option maxHeartbeats` wrapper
#  --fact-budget 0 --max-slowdown 0: everything replaced, native axioms 3 -> 0
#  --fact-budget 0 (max-slowdown 2 by default): the Facts module (slowDivSum makes its build several times slower) and the
#               Examples module are reverted whole (per-module guard), so native axioms stay 3
set -u
NT=${1:?}; TC=${2:?}; WK=${3:?}
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=2
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$WK" && cd "$WK" || exit 2
[ -e lakefile.toml ] && { echo "WORK not empty"; exit 2; }
cp -r "$HERE/MigBudget" "$HERE/MigBudget.lean" "$HERE/lakefile.toml" .
echo "leanprover/lean4:$TC" > lean-toolchain
printf '\n[[require]]\nname = "NativeTrust"\npath = "%s"\n' "$NT" >> lakefile.toml
lake update NativeTrust > update.log 2>&1 || { echo "FAIL lake update"; cat update.log; exit 1; }
lake build > build0.log 2>&1 || { echo "FAIL original build"; tail -20 build0.log; exit 1; }
chk() { if eval "$2"; then echo "PASS $1"; else echo "FAIL $1"; fi; }
S=.ntrust/migrate/summary.json; P=.ntrust/migrate/plan.tsv; R="$WK.results"; mkdir -p "$R"
lake exe ntrust migrate --jobs 2 > mig2000.log 2>&1; echo "rc=$?" >> mig2000.log
chk "defaults: budget 2000, max-slowdown 2, nothing reverted for time" "grep -q '\"fact_budget\": 2000,' $S && grep -q '\"max_slowdown_x10\": 20,' $S && grep -q '\"slowdown_reverted_modules\": \[\]' $S"
chk "2000: build ok, 5 uses, 3 axioms before" "grep -q '\"build_ok\": true' $S && grep -q '\"uses\": 5,' $S && grep -q '\"native_axioms_before\": 3,' $S"
chk "2000: axioms 3 -> 1" "grep -q '\"native_axioms_before\": 3' $S && grep -q '\"native_axioms_after\": 1' $S"
chk "2000: cheapSum replaced" "awk -F'\t' '\$2==6 && \$5==\"replaced\"' $P | grep -q ."
chk "2000: cheapMul replaced" "awk -F'\t' '\$2==8 && \$5==\"replaced\"' $P | grep -q ."
chk "2000: slowDivSum kept, EXPENSIVE" "awk -F'\t' '\$2==10 && \$5==\"keep\" && \$6 ~ /budget 2000: EXPENSIVE/' $P | grep -q ."
chk "2000: cheap example replaced" "awk -F'\t' '\$1 ~ /Examples/ && \$2==5 && \$5==\"replaced\"' $P | grep -q ."
chk "2000: slow example kept" "awk -F'\t' '\$1 ~ /Examples/ && \$2==7 && \$5==\"keep\"' $P | grep -q ."
chk "2000: no wrapper left" "! grep -rq 'set_option maxHeartbeats' MigBudget"
chk "2000: audit tags" "grep -q '\"REPLACEABLE\": 2' $S && grep -q '\"EXPENSIVE\": 1' $S"
cp -r .ntrust/migrate "$R/result_2000"
lake exe ntrust migrate --restore > restore1.log 2>&1
lake build > build1.log 2>&1 || echo "FAIL rebuild after restore 1"
lake exe ntrust migrate --fact-budget 0 --max-slowdown 0 --jobs 2 > mig0.log 2>&1; echo "rc=$?" >> mig0.log
chk "0: build ok, 5 uses, 3 axioms before" "grep -q '\"build_ok\": true' $S && grep -q '\"uses\": 5,' $S && grep -q '\"native_axioms_before\": 3,' $S"
chk "0: axioms 3 -> 0" "grep -q '\"native_axioms_after\": 0' $S"
chk "0: all 5 replaced" "grep -q '\"replaced\": 5' $S"
cp -r .ntrust/migrate "$R/result_0"
lake exe ntrust migrate --restore > restore2.log 2>&1
lake build > build2.log 2>&1 || echo "FAIL rebuild after restore 2"
lake exe ntrust migrate --fact-budget 0 --jobs 2 > migslow.log 2>&1; echo "rc=$?" >> migslow.log
chk "slowdown: build ok, 3 axioms before and after" "grep -q '\"build_ok\": true' $S && grep -q '\"native_axioms_before\": 3,' $S && grep -q '\"native_axioms_after\": 3,' $S"
chk "slowdown: time0 rebuilt the modules" "grep -q 'time0 (--max-slowdown): rc=0' .ntrust/migrate/migrate.log && ! grep -q ' 0 files deleted' .ntrust/migrate/migrate.log"
chk "slowdown: Facts and Examples modules reverted" "grep -q '\"slowdown_reverted_modules\": \[.*MigBudget.Examples.*MigBudget.Facts' $S"
cp -r .ntrust/migrate "$R/result_slow"
lake exe ntrust migrate --restore > restore3.log 2>&1
