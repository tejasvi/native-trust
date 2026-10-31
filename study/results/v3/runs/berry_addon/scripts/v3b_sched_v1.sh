#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3b_sched_v1.sh (v3 BerryEsseen, parse-once covers): run as ntbuild inside the run's unit. Builds the modules of every
# cover in COVERS (lines: TAG PEAK_GB PARSE_GB, largest first) in order: Tree; then Parse and the leaf modules of
# batches.txt; then All; then the check F2_<TAG>. A job starts only while (a) fewer than MAXP jobs run, (b) the predicted
# peaks of the running jobs plus its own stay within the budget in BUDGETF (GiB, re-read every loop, so it can be raised
# when the tokenizer pass ends), (c) MemAvailable >= 64 GiB + its cap, and (d) the root file system has at least
# 20 GB free. Each job is v3b_lrun_v1.sh with an
# address-space cap. Resumable: a module whose olean exists and whose log ends with rc=0 counts as done (F2: rc=0 and a
# PROVED line). A failed module is not retried; its cover is reported as failed.
# usage: v3b_sched_v1.sh COVERS BUDGETF MAXP
COVERS=${1:?}; BUDGETF=${2:?}; MAXP=${3:?}
B=${NT_BOX}/v3/berry; C=$B/covers; R=$B/bin/v3b_lrun_v1.sh; LOG=$B/logs/sched.log
mkdir -p $B/logs || exit 3
log() { echo "$(date -u +%FT%TZ) $*" >> $LOG; }
done_mod() { [ -f "$1/$2.olean" ] && [ "$(tail -2 "$1/$2.log" 2>/dev/null | head -1)" = "rc=0" ]; }
done_f2() { [ -f "$1/F2_$2.log" ] && command grep -q '^rc=0$' "$1/F2_$2.log" && command grep -q 'PROVED `' "$1/F2_$2.log"; }
declare -A PEAK PARSE STAGE NPEND JTAG JMOD JKIND JPRED
QUEUE=()      # ready jobs: "TAG KIND MOD"
TAGS=()
while read -r tag pk ps; do
  [ -n "$tag" ] || continue
  TAGS+=("$tag"); PEAK[$tag]=$pk; PARSE[$tag]=$ps
done < "$COVERS"
pred_of() { # tag kind -> predicted peak GiB
  case $2 in tree) echo 2;; parse) awk -v p="${PARSE[$1]}" 'BEGIN{print int(p + 1.999)}';;
    leaf) awk -v p="${PEAK[$1]}" 'BEGIN{print int(p * 1.1 + 0.999)}';; all|f2) echo 4;; esac; }
cap_of() { # tag kind -> address-space cap GiB
  case $2 in tree) echo 16;; parse) awk -v p="${PARSE[$1]}" 'BEGIN{c=int(2*p+8); if(c<24)c=24; print c}';;
    leaf) awk -v p="${PEAK[$1]}" 'BEGIN{c=int(1.5*p+8); if(c<24)c=24; if(c>64)c=64; print c}';; all|f2) echo 32;; esac; }
to_of() { case $1 in tree) echo 1800;; parse) echo 7200;; leaf) echo 14400;; all) echo 7200;; f2) echo 3600;; esac; }
enqueue_mid() { # tag: Parse and the leaf modules that are not done
  local t=$1 d=$C/$1 n=0 m
  if ! done_mod $d BO_${t}_Parse; then QUEUE+=("$t parse BO_${t}_Parse"); n=$((n + 1)); fi
  while read -r m; do [ -n "$m" ] || continue; done_mod $d $m || { QUEUE+=("$t leaf $m"); n=$((n + 1)); }; done < $d/batches.txt
  NPEND[$t]=$n
  if [ $n -eq 0 ]; then advance_all $t; else STAGE[$t]=mid; fi
}
advance_all() { local t=$1 d=$C/$1
  if done_mod $d BO_${t}_All; then advance_f2 $t; else STAGE[$t]=all; QUEUE+=("$t all BO_${t}_All"); fi; }
advance_f2() { local t=$1 d=$C/$1
  if done_f2 $d $t; then STAGE[$t]=done; else STAGE[$t]=f2; QUEUE+=("$t f2 F2_${t}"); fi; }
# initial state (resume)
for t in "${TAGS[@]}"; do
  d=$C/$t
  if done_f2 $d $t; then STAGE[$t]=done
  elif done_mod $d BO_${t}_Tree; then enqueue_mid $t
  else STAGE[$t]=tree; QUEUE+=("$t tree BO_${t}_Tree"); fi
done
log "start covers=${#TAGS[@]} queue=${#QUEUE[@]} maxp=$MAXP"
USED=0; NRUN=0
start_ready() {
  local budget avail i job t k m pr cp nq=()
  budget=$(cat "$BUDGETF" 2>/dev/null); case "$budget" in ''|*[!0-9]*) budget=0;; esac
  avail=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)
  # disk guard: no new job while the root file system has less than 20 GB free
  if [ "$(df -B1G --output=avail / | tail -1 | tr -d ' ')" -lt 20 ]; then log "disk below 20 GB free: no new job"; return; fi
  for i in "${!QUEUE[@]}"; do
    job=${QUEUE[$i]}; read -r t k m <<< "$job"
    pr=$(pred_of $t $k); cp=$(cap_of $t $k)
    if [ $NRUN -lt $MAXP ] && [ $((USED + pr)) -le $budget ] && [ $avail -ge $((64 + cp)) ]; then
      if [ $k = f2 ]; then MEMGB=$cp TO=$(to_of $k) bash $R $C/$t $m & else OLEAN=1 MEMGB=$cp TO=$(to_of $k) bash $R $C/$t $m & fi
      local pid=$!
      JTAG[$pid]=$t; JMOD[$pid]=$m; JKIND[$pid]=$k; JPRED[$pid]=$pr
      USED=$((USED + pr)); NRUN=$((NRUN + 1)); avail=$((avail - pr))
      log "start $t $m kind=$k pred=${pr}G cap=${cp}G pid=$pid used=${USED}G run=$NRUN budget=${budget}G"
    else
      nq+=("$job")
    fi
  done
  QUEUE=("${nq[@]}")
}
finish() { # pid
  local pid=$1 t=${JTAG[$1]} m=${JMOD[$1]} k=${JKIND[$1]} d ok=0
  d=$C/$t
  USED=$((USED - JPRED[$pid])); NRUN=$((NRUN - 1))
  unset "JTAG[$pid]" "JMOD[$pid]" "JKIND[$pid]" "JPRED[$pid]"
  if [ $k = f2 ]; then done_f2 $d $t && ok=1; else done_mod $d $m && ok=1; fi
  log "end $t $m kind=$k ok=$ok $(tail -2 $d/$m.log | tr '\n' ' ')"
  if [ $ok = 0 ]; then STAGE[$t]=failed; log "cover $t FAILED at $m"; return; fi
  case $k in
    tree) enqueue_mid $t;;
    parse|leaf) [ "${STAGE[$t]}" = failed ] && return; NPEND[$t]=$((NPEND[$t] - 1)); [ ${NPEND[$t]} -eq 0 ] && advance_all $t;;
    all) advance_f2 $t;;
    f2) STAGE[$t]=done; log "cover $t DONE";;
  esac
}
while :; do
  # drop queued jobs of failed covers
  nq=(); for job in "${QUEUE[@]}"; do read -r t k m <<< "$job"; [ "${STAGE[$t]}" = failed ] || nq+=("$job"); done; QUEUE=("${nq[@]}")
  start_ready
  if [ $NRUN -eq 0 ]; then
    [ ${#QUEUE[@]} -eq 0 ] && break
    sleep 30; continue
  fi
  wait -n -p FIN; finish $FIN
done
nd=0; nf=0; for t in "${TAGS[@]}"; do case ${STAGE[$t]} in done) nd=$((nd + 1));; failed) nf=$((nf + 1));; esac; done
log "end covers=${#TAGS[@]} done=$nd failed=$nf"
