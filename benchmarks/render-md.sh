#!/usr/bin/env bash
# Renders results/*.tsv as Markdown: results/table.md (selected instances) and
# results/library.md (all problems, both PB placements side by side).
set -euo pipefail
R="$(cd "$(dirname "$0")" && pwd)/results"

{
  echo "| Problem | Expected | Status | Median ms | Nodes | Branches |"
  echo "|---|---|---|---:|---:|---:|"
  awk -F'\t' 'NR>1 { printf "| %s | %s | %s | %s | %s | %s |\n", $1,$2,$3,$4,$5,$6 }' "$R/table.tsv"
} > "$R/table.md"

{
  echo "| Problem | Expected | Deferred | ms | Nodes | Branches | Immediate | ms | Nodes | Branches |"
  echo "|---|---|---|---:|---:|---:|---|---:|---:|---:|"
  awk -F'\t' '
    FNR==1 { next }
    FILENAME ~ /deferred/ { d[$1]=$3"\t"$4"\t"$5"\t"$6; exp_[$1]=$2; order[++n]=$1; next }
    { i[$1]=$3"\t"$4"\t"$5"\t"$6 }
    END { for (k=1;k<=n;k++) { p=order[k]; split(d[p],a,"\t"); split(i[p],b,"\t");
          printf "| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n", p, exp_[p], a[1],a[2],a[3],a[4], b[1],b[2],b[3],b[4] } }
  ' "$R/library-deferred.tsv" "$R/library-immediate.tsv"
} > "$R/library.md"
echo "wrote $R/table.md and $R/library.md" >&2
