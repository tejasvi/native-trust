#!/bin/bash
# berry_summary_v1.sh (local, read-only): BerryEsseen add-on summary from one pull dir (copyback_v1.sh layout).
# Tokenizer facts (results/v3b-tok-berry-esseen.ax.tsv): verdicts, per-fact seconds (median, max, > 900 s, > 3,600 s),
# peak GiB. Covers (v3/berry/covers/<tag>/*.time, one per module and check): per cover the total of its processes'
# seconds (single-threaded work), the critical path Tree + max(Parse, leaves) + All + F2, the longest single process, and
# the peak GiB; only covers whose F2 check has a .time file.
# usage: berry_summary_v1.sh PULL_DIR
set -u
P=${1:?}
T=$P/results/v3b-tok-berry-esseen.ax.tsv; C=$P/v3/berry/covers
[ -s "$T" ] && [ -d "$C" ] || { echo "missing $T or $C"; exit 2; }
stats() { # stdin: one number per line; prints median, max, count > 900, count > 3600
  LC_ALL=C sort -g | awk '{a[NR]=$1; if ($1 > 900) n9++; if ($1 > 3600) n36++} END{if (NR) printf "n=%d median=%.0f max=%.0f over900=%d over3600=%d", NR, (NR%2 ? a[(NR+1)/2] : (a[NR/2]+a[NR/2+1])/2), a[NR], n9+0, n36+0}'; }
echo "tokenizer: $(awk -F'\t' '{v[$6]++} END{for (k in v) printf "%s=%d ", k, v[k]}' "$T")"
echo "  secs: $(awk -F'\t' '{print $10}' "$T" | stats)  peak GiB max: $(awk -F'\t' '$9>m{m=$9} END{printf "%.1f", m/1048576}' "$T")"
for d in "$C"/*/; do
  t=$(basename "$d"); [ -f "$d/F2_$t.time" ] || continue
  awk -v t="$t" 'FNR==1{n=FILENAME; sub(/.*\//, "", n); sub(/\.time$/, "", n)} /^TIME/{s=$2; k=$4
      tot+=s; if (s>mx) mx=s; if (k>pk) pk=k
      if (n ~ /_Tree$/) tr=s; else if (n ~ /_All$/) al=s; else if (n ~ /^F2_/) f2=s; else if (s>mid) mid=s}
    END{printf "%s %.2f %.2f %.2f %.0f %.2f\n", t, tot, tr+mid+al+f2, mx, pk, f2}' "$d"/*.time
done > "$P/cover_times_v1.txt"
echo "covers with a finished check: $(wc -l < "$P/cover_times_v1.txt")"
echo "  per-cover total secs: $(awk '{print $2}' "$P/cover_times_v1.txt" | stats)"
echo "  critical path secs:   $(awk '{print $3}' "$P/cover_times_v1.txt" | stats)"
echo "  longest process secs: $(awk '{print $4}' "$P/cover_times_v1.txt" | stats)"
echo "  F2 check secs:        $(awk '{print $6}' "$P/cover_times_v1.txt" | stats)"
echo "  peak GiB max: $(awk '$5>m{m=$5} END{printf "%.1f", m/1048576}' "$P/cover_times_v1.txt")"
