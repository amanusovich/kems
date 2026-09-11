#!/usr/bin/env bash
# Refreshes the per-problem table in README.md (between the two markers) from
# results/library-*.tsv, both PB placements side by side.
set -euo pipefail
B="$(cd "$(dirname "$0")" && pwd)"; R="$B/results"
TABLE="$(
  echo "| Problem | Expected | Deferred | ms | Nodes | Branches | Immediate | ms | Nodes | Branches |"
  echo "|---|---|---|---:|---:|---:|---|---:|---:|---:|"
  awk -F'\t' '
    FNR==1 { next }
    FILENAME ~ /deferred/ { d[$1]=$3"\t"$4"\t"$5"\t"$6; exp_[$1]=$2; order[++n]=$1; next }
    { i[$1]=$3"\t"$4"\t"$5"\t"$6 }
    END { for (k=1;k<=n;k++) { p=order[k]; split(d[p],a,"\t"); split(i[p],b,"\t");
          printf "| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n", p, exp_[p], a[1],a[2],a[3],a[4], b[1],b[2],b[3],b[4] } }
  ' "$R/library-deferred.tsv" "$R/library-immediate.tsv"
)"
{
  sed -n '1,/<!-- library-table:start -->/p' "$B/README.md"
  printf '%s\n' "$TABLE"
  sed -n '/<!-- library-table:end -->/,$p' "$B/README.md"
} > "$B/README.md.tmp" && mv "$B/README.md.tmp" "$B/README.md"
