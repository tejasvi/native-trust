#!/bin/bash
# v3u_list_v2.sh (v3 components, R1; v2: also reads the pass runner's suffixed heavy-pass files v3h-NAME_t (timeouts, 3,600 s),
# v3h-NAME_b (bv_decide timeouts) and v3h-NAME_r (harness redo), the aggregator's D passes; v1 read only unsuffixed
# names and missed facts proved there): run as ntbuild. Writes /home/ntbuild/results/v3u-NAME.ax.tsv: the facts
# of the default run v3-NAME that no v3 pass proved, i.e. not PROVED in v3-NAME nor in v3r-, v3h-, v3h-NAME_t, _b, _r,
# v3p-NAME (whichever exist). Each fact keeps the row of the latest of these files (in that order) that has it (the
# driver's 12 columns), so the driver can select them with --from-results v3u-NAME. NOT_BUILT rows are left out.
# usage: v3u_list_v2.sh NAME
set -u
N=${1:?}
case "$N" in *[!A-Za-z0-9_.-]*) echo "bad name"; exit 2;; esac
R=/home/ntbuild/results; OUT=$R/v3u-$N.ax.tsv
[ -s "$R/v3-$N.ax.tsv" ] || { echo "no $R/v3-$N.ax.tsv"; exit 3; }
[ -e "$OUT" ] && { echo "refusing: $OUT exists"; exit 3; }
files=("$R/v3-$N.ax.tsv")
for f in "v3r-$N" "v3h-$N" "v3h-${N}_t" "v3h-${N}_b" "v3h-${N}_r" "v3p-$N"; do [ -s "$R/$f.ax.tsv" ] && files+=("$R/$f.ax.tsv"); done
awk -F'\t' -v OFS='\t' '
  FNR == 1 { fi++ }
  NF >= 7 && $3 != "-" && $3 != "" { k = $2 SUBSEP $3; if (fi == 1) base[k] = 1; last[k] = $0; if ($6 == "PROVED") proved[k] = 1 }
  END { for (k in base) if (!(k in proved)) print last[k] }' "${files[@]}" | LC_ALL=C sort --parallel=1 > "$OUT.part" || exit 4
mv "$OUT.part" "$OUT"
echo "$N: files ${files[*]##*/}; base $(awk -F'\t' 'NF>=7 && $3!="-" && $3!=""{print $2 FS $3}' "$R/v3-$N.ax.tsv" | LC_ALL=C sort -u --parallel=1 | wc -l) facts; unconverted $(wc -l < "$OUT")"
awk -F'\t' '{print $6"/"$7}' "$OUT" | sort | uniq -c | sort -rn | head -8
