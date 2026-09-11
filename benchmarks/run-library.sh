#!/usr/bin/env bash
# Runs the whole ILTP propositional library (274 problems), one JVM per problem with a
# 10 s limit, under one PB placement. Usage: run-library.sh [DEFERRED|IMMEDIATE]
# Writes results/library-<policy>.tsv and prints a summary.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
POLICY="${1:-DEFERRED}"
LIMIT="${LIMIT_MS:-10000}"
[ -f "$ROOT/build/classpath.txt" ] || "$ROOT/benchmarks/build.sh"
CP="$(cat "$ROOT/build/classpath.txt")"
OUT="$ROOT/benchmarks/results/library-$(echo "$POLICY" | tr 'A-Z' 'a-z').tsv"
cd "$ROOT/kems.prover"
{
  printf 'problem\texpected\tstatus\tms\tnodes\tbranches\n'
  find tests/resources/iltp/Problems -name "*.p" | sort | while read -r f; do
    java -cp "$CP" logicalSystems.ipl.IltpRun --policy "$POLICY" --limit "$LIMIT" "$f" || true
  done
} > "$OUT"
awk -F'\t' 'NR>1 { n++; if ($3=="closed"||$3=="open") { d++; if (($3=="closed" && $2=="theorem")||($3=="open" && $2=="non-theorem")) ok++; else if ($2=="theorem"||$2=="non-theorem") bad++ } else if ($3=="timeout") t++; else e++ }
  END { printf "%s: %d problems, %d decided (%d agree with ILTP status, %d disagree), %d timeout, %d error\n", FILENAME, n, d, ok, bad, t, e }' "$OUT"
