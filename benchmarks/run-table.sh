#!/usr/bin/env bash
# Benchmark table over selected instances: the listed problems, one JVM
# each, one warmup run discarded, median of five timed runs. Writes results/table.tsv.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
[ -f "$ROOT/build/classpath.txt" ] || "$ROOT/benchmarks/build.sh"
CP="$(cat "$ROOT/build/classpath.txt")"
OUT="$ROOT/benchmarks/results/table.tsv"
PROBLEMS="${@:-SYJ105+1.004 SYJ207+1.001 SYJ209+1.003 SYJ201+1.001 SYJ205+1.010 SYJ205+1.020}"
cd "$ROOT/kems.prover"
{
  printf 'problem\texpected\tstatus\tmedian_ms\tnodes\tbranches\n'
  for p in $PROBLEMS; do
    java -cp "$CP" logicalSystems.ipl.IltpRun --runs 5 --limit 60000 "$p"
  done
} | tee "$OUT"
