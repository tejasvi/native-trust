#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# task 3: kernel supplement of one QEC theorem, as in Section 6.1 (ops/m1_final.sh), then the checks of Section 6.
# 1. Supp_<TAG>.lean imports NativeTrust, the driver's per-fact modules of the theorem's native facts (their registered
#    kernel proofs; list from fm_for_v1.py) and the theorem's module, runs `kernelize T` (declares T.kernel), prints
#    the axioms of T and T.kernel and compares the two types (Expr ==); compiled with lean -o.
# 2. Statement check in a fresh process: Stmt_<TAG>.lean imports Supp_<TAG> and runs the script of ops/stmt_check.py
#    (sha 8592f646): same / defeq / different type, axioms beyond the standard three, positive control (the original
#    uses a non-standard axiom).
# 3. leanexport exports T.kernel with its closure; nanoda (standard axioms only, any other a hard error) checks it.
# Runs as ntbuild inside a systemd unit (MemoryMax); no ulimit -v. usage: supp_build_v1.sh TAG THEOREM MODULE FACTMODS
set -u
TAG=${1:?}; T=${2:?}; M=${3:?}; FM=${4:?}
Q=${NT_BOX}/work_resv8/qec; S=$Q/supp; D=$Q/drv/qec/mods; X=${NT_BOX}/work_resv8/box/qec
B=${NT_BOX}/elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
mkdir -p "$S" && cd "$S" || exit 2
LP=$(cd "$Q/lean4" && lake env printenv LEAN_PATH) || exit 2
export LEAN_PATH=${NT_BOX}/nt_fix14/v4.35.0-rc3/.lake/build/lib/lean:$LP:$D:$S
F=Supp_$TAG; L=$S/$F.summary
[ -e "$F.lean" ] && { echo "REFUSE: $S/$F.lean exists"; exit 2; }
{ echo "import NativeTrust"; sed 's/^/import /' "$FM"; echo "import $M"
  echo "set_option maxHeartbeats 0"; echo "set_option maxRecDepth 1000000"
  echo "kernelize $T"
  echo "#print axioms $T"; echo "#print axioms $T.kernel"
  echo "open Lean in"; echo "run_cmd Elab.Command.liftTermElabM do"
  echo "  let env ← getEnv"
  echo "  let a := (env.find? \`$T).get!.type"
  echo "  let b := (env.find? \`$T.kernel).get!.type"
  echo "  logInfo m!\"statements identical (Expr ==): {a == b}\""
} > "$F.lean"
echo "$(date -u +%FT%TZ) $F: $(wc -l < "$FM") fact modules, theorem $T, module $M" > "$L"
/usr/bin/time -f "supp_compile: %e s wall %U s user %S s sys %M KB" "$B/lean" -j1 --tstack=1048576 -o "$F.olean" "$F.lean" > "$F.log" 2>&1
echo "supp_compile rc=$? $(tail -n 1 "$F.log")" >> "$L"
grep -E "statements identical|depends on axioms|does not depend" -A3 "$F.log" | head -40 >> "$L"
[ -s "$F.olean" ] || { echo "no olean: stop" >> "$L"; exit 1; }
{ echo "import $F"; sed "s/{MOD}/$F/" "$X/stmt_script_from_ops_stmt_check.lean.txt"; } > "Stmt_$TAG.lean"
/usr/bin/time -f "stmt_check: %e s wall %U s user %S s sys %M KB" "$B/lean" -j1 --tstack=1048576 "Stmt_$TAG.lean" > "Stmt_$TAG.log" 2>&1
echo "stmt_check rc=$? $(grep -E '^STMT|^DIFF|^DEFEQ|^AXIOMS|^MISSING|NOMODULE' "Stmt_$TAG.log" | tr '\n' ' ')" >> "$L"
/usr/bin/time -f "leanexport: %e s wall %M KB" "$B/leanexport" "$F" -- "$T.kernel" > "$F.export" 2> "$F.export.err"
echo "leanexport rc=$? lines=$(wc -l < "$F.export") bytes=$(wc -c < "$F.export") $(tail -n 1 "$F.export.err")" >> "$L"
printf '{"export_file_path":"%s/%s.export","permitted_axioms":["propext","Classical.choice","Quot.sound"],"unpermitted_axiom_hard_error":true,"nat_extension":true,"string_extension":true,"print_success_message":true}\n' "$S" "$F" > "$F.nanoda.json"
( ulimit -s unlimited; /usr/bin/time -f "nanoda: %e s wall %U s user %M KB" timeout 7200 "$B/nanoda_bin" "$F.nanoda.json" ) > "$F.nanoda.log" 2>&1
echo "nanoda rc=$? $(tail -n 3 "$F.nanoda.log" | tr '\n' ' ')" >> "$L"
echo "$(date -u +%FT%TZ) done" >> "$L"
cat "$L"
