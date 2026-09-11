# Benchmarks

Everything in the evaluation section of the LANMR 2026 paper is produced by the scripts
in this directory, on the ILTP v1.1.2 propositional library shipped under
`kems.prover/tests/resources/iltp/Problems` (274 problems: 252 SYJ, 20 SYN, 2 LCL).

## Protocol

* One problem per JVM (`logicalSystems.ipl.IltpRun`), so no problem is timed with
  another one's JIT state or heap behind it. Only the prove step is timed.
* Benchmark table: one warmup run discarded, then the median of five timed runs.
* Full library: a single run per problem with a 10 s wall-clock limit, once per PB
  placement (`DEFERRED`, the default, and `IMMEDIATE`).
* Verdicts are checked against the `Status (intuit.)` field of each problem file
  (`theorem` / `non-theorem`; 37 problems are `unsolved` in the library).
* Machine used for `results/`: Apple Silicon Mac, macOS, Eclipse Temurin 17.

## Reproducing

    benchmarks/build.sh                 # javac into build/, same recipe as the Dockerfile
    benchmarks/run-table.sh             # -> results/table.tsv   (a minute or two)
    benchmarks/run-library.sh DEFERRED  # -> results/library-deferred.tsv   (~30 min)
    benchmarks/run-library.sh IMMEDIATE # -> results/library-immediate.tsv  (~35 min)

`run-table.sh` accepts problem ids as arguments to time other instances. `IltpRun` can
also be invoked directly; see its javadoc for the options.

## Results

### Benchmark table (`results/table.tsv`)

| Problem      | Expected    | Status | Median ms | Nodes | Branches |
|--------------|-------------|--------|----------:|------:|---------:|
| SYJ105+1.004 | theorem     | closed |       101 |   117 |        1 |
| SYJ207+1.001 | non-theorem | open   |         3 |    35 |        7 |
| SYJ209+1.003 | non-theorem | open   |      8868 |  3067 |      551 |
| SYJ201+1.001 | theorem     | closed |       308 |   928 |      180 |
| SYJ205+1.010 | theorem     | closed |        85 |   121 |        2 |
| SYJ205+1.020 | theorem     | closed |       820 |   221 |        2 |

`closed` = proof found; `open` = completed branch, from which a counter-model is read off.

### Full library (`results/library-*.tsv`)

| PB placement       | Decided / 274 | Timeout | Error | Disagree with ILTP |
|--------------------|--------------:|--------:|------:|-------------------:|
| Deferred (default) |           113 |     158 |     3 |                  0 |
| Immediate          |            98 |     173 |     3 |                  0 |

Over the 94 problems both placements decide (68 of them with different derivations),
deferred totals 14 361 nodes and 2 368 branches against 24 268 and 4 514 for immediate.
Deferred alone decides 19 problems (all of SYJ205 from `.003` on among them); immediate
alone decides 4 (SYJ201+1.002, SYJ208+1.003, SYJ212+1.004, SYJ212+1.005).

The three errors are the same under both placements: SYN915+1 and SYN916+1 use the
constants `$true`/`$false`, for which the implemented rule set (Table 2 of the theory
paper) has no rule, so the input is rejected; SYN007+1.014 runs out of memory.

Columns of the TSV files: `problem`, `expected` (ILTP status), `status` (`closed`,
`open`, `timeout`, `error:<Exception>`), `ms`, `nodes`, `branches`.
