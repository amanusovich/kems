# Benchmarks

The scripts in this directory evaluate the IPL prover on the ILTP v1.1.2 propositional
library shipped under `kems.prover/tests/resources/iltp/Problems` (274 problems: 252 SYJ, 20 SYN, 2 LCL).

## Protocol

* One problem per JVM (`logicalSystems.ipl.IltpRun`), so no problem is timed with
  another one's JIT state or heap behind it. Only the prove step is timed.
* Benchmark table (selected instances): one warmup run discarded, then the median of
  five timed runs.
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
    benchmarks/render-md.sh             # refreshes the per-problem table below

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
constants `$true`/`$false`, for which the implemented rule set (Table 2 of Solares-Rojas,
Baldi and Rodriguez 2026) has no rule, so the input is rejected; SYN007+1.014 runs out of memory.

Columns of the TSV files: `problem`, `expected` (ILTP status), `status` (`closed`,
`open`, `timeout`, `error:<Exception>`), `ms`, `nodes`, `branches`.

### All problems, both placements

<!-- library-table:start -->
| Problem | Expected | Deferred | ms | Nodes | Branches | Immediate | ms | Nodes | Branches |
|---|---|---|---:|---:|---:|---|---:|---:|---:|
| LCL181+1 | non-theorem | open | 10 | 12 | 2 | open | 9 | 12 | 2 |
| LCL230+1 | non-theorem | open | 12 | 20 | 4 | open | 11 | 20 | 4 |
| SYJ101+1 | theorem | closed | 2 | 2 | 1 | closed | 2 | 2 | 1 |
| SYJ102+1 | theorem | closed | 3 | 4 | 1 | closed | 3 | 4 | 1 |
| SYJ103+1 | theorem | closed | 5 | 7 | 1 | closed | 4 | 7 | 1 |
| SYJ104+1 | theorem | closed | 2 | 2 | 1 | closed | 2 | 2 | 1 |
| SYJ105+1.002 | theorem | closed | 6 | 9 | 1 | closed | 7 | 9 | 1 |
| SYJ105+1.003 | theorem | closed | 19 | 30 | 1 | closed | 32 | 30 | 1 |
| SYJ105+1.004 | theorem | closed | 173 | 117 | 1 | closed | 178 | 150 | 7 |
| SYJ106+1 | theorem | closed | 129 | 377 | 76 | closed | 69 | 210 | 25 |
| SYJ107+1.001 | theorem | closed | 5 | 8 | 1 | closed | 6 | 11 | 2 |
| SYJ107+1.002 | theorem | closed | 16 | 17 | 2 | closed | 16 | 24 | 4 |
| SYJ107+1.003 | theorem | closed | 16 | 26 | 3 | closed | 22 | 48 | 8 |
| SYJ107+1.004 | theorem | closed | 27 | 35 | 4 | closed | 34 | 86 | 15 |
| SYJ201+1.001 | theorem | closed | 411 | 928 | 180 | closed | 87 | 467 | 70 |
| SYJ201+1.002 | theorem | timeout | - | - | - | closed | 3713 | 4490 | 578 |
| SYJ201+1.003 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.004 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.005 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.006 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.007 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.008 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.009 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.010 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.011 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.012 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.013 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.014 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.015 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.016 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.017 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.018 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.019 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ201+1.020 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.001 | theorem | closed | 6 | 5 | 1 | closed | 2 | 5 | 1 |
| SYJ202+1.002 | theorem | closed | 19 | 28 | 2 | closed | 29 | 45 | 8 |
| SYJ202+1.003 | theorem | closed | 196 | 140 | 15 | closed | 567 | 408 | 83 |
| SYJ202+1.004 | theorem | closed | 7867 | 653 | 82 | timeout | - | - | - |
| SYJ202+1.005 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.006 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.007 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.008 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.009 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.010 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.011 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.012 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.013 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.014 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.015 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.016 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.017 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.018 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.019 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ202+1.020 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.001 | theorem | closed | 8 | 10 | 1 | closed | 8 | 10 | 1 |
| SYJ203+1.002 | theorem | closed | 22 | 34 | 1 | closed | 27 | 37 | 2 |
| SYJ203+1.003 | theorem | closed | 138 | 132 | 1 | closed | 196 | 165 | 7 |
| SYJ203+1.004 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.005 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.006 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.007 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.008 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.009 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.010 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.011 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.012 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.013 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.014 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.015 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.016 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.017 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.018 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.019 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ203+1.020 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ204+1.001 | theorem | closed | 5 | 5 | 1 | closed | 8 | 8 | 2 |
| SYJ204+1.002 | theorem | closed | 8 | 8 | 1 | closed | 9 | 10 | 2 |
| SYJ204+1.003 | theorem | closed | 10 | 11 | 1 | closed | 7 | 15 | 3 |
| SYJ204+1.004 | theorem | closed | 12 | 14 | 1 | closed | 11 | 20 | 4 |
| SYJ204+1.005 | theorem | closed | 10 | 17 | 1 | closed | 10 | 25 | 5 |
| SYJ204+1.006 | theorem | closed | 13 | 20 | 1 | closed | 15 | 30 | 6 |
| SYJ204+1.007 | theorem | closed | 19 | 23 | 1 | closed | 13 | 35 | 7 |
| SYJ204+1.008 | theorem | closed | 18 | 26 | 1 | closed | 15 | 40 | 8 |
| SYJ204+1.009 | theorem | closed | 20 | 29 | 1 | closed | 17 | 45 | 9 |
| SYJ204+1.010 | theorem | closed | 22 | 32 | 1 | closed | 23 | 50 | 10 |
| SYJ204+1.011 | theorem | closed | 24 | 35 | 1 | closed | 21 | 55 | 11 |
| SYJ204+1.012 | theorem | closed | 31 | 38 | 1 | closed | 22 | 60 | 12 |
| SYJ204+1.013 | theorem | closed | 28 | 41 | 1 | closed | 25 | 65 | 13 |
| SYJ204+1.014 | theorem | closed | 31 | 44 | 1 | closed | 25 | 70 | 14 |
| SYJ204+1.015 | theorem | closed | 36 | 47 | 1 | closed | 28 | 75 | 15 |
| SYJ204+1.016 | theorem | closed | 38 | 50 | 1 | closed | 29 | 80 | 16 |
| SYJ204+1.017 | theorem | closed | 43 | 53 | 1 | closed | 30 | 85 | 17 |
| SYJ204+1.018 | theorem | closed | 47 | 56 | 1 | closed | 37 | 90 | 18 |
| SYJ204+1.019 | theorem | closed | 52 | 59 | 1 | closed | 34 | 95 | 19 |
| SYJ204+1.020 | theorem | closed | 56 | 62 | 1 | closed | 41 | 100 | 20 |
| SYJ205+1.001 | theorem | closed | 18 | 31 | 2 | closed | 93 | 247 | 43 |
| SYJ205+1.002 | theorem | closed | 24 | 41 | 2 | closed | 2628 | 4587 | 703 |
| SYJ205+1.003 | theorem | closed | 29 | 51 | 2 | timeout | - | - | - |
| SYJ205+1.004 | theorem | closed | 39 | 61 | 2 | timeout | - | - | - |
| SYJ205+1.005 | theorem | closed | 53 | 71 | 2 | timeout | - | - | - |
| SYJ205+1.006 | theorem | closed | 74 | 81 | 2 | timeout | - | - | - |
| SYJ205+1.007 | theorem | closed | 106 | 91 | 2 | timeout | - | - | - |
| SYJ205+1.008 | theorem | closed | 149 | 101 | 2 | timeout | - | - | - |
| SYJ205+1.009 | theorem | closed | 192 | 111 | 2 | timeout | - | - | - |
| SYJ205+1.010 | theorem | closed | 270 | 121 | 2 | timeout | - | - | - |
| SYJ205+1.011 | theorem | closed | 335 | 131 | 2 | timeout | - | - | - |
| SYJ205+1.012 | theorem | closed | 399 | 141 | 2 | timeout | - | - | - |
| SYJ205+1.013 | theorem | closed | 447 | 151 | 2 | timeout | - | - | - |
| SYJ205+1.014 | theorem | closed | 535 | 161 | 2 | timeout | - | - | - |
| SYJ205+1.015 | theorem | closed | 576 | 171 | 2 | timeout | - | - | - |
| SYJ205+1.016 | theorem | closed | 658 | 181 | 2 | timeout | - | - | - |
| SYJ205+1.017 | theorem | closed | 726 | 191 | 2 | timeout | - | - | - |
| SYJ205+1.018 | theorem | closed | 837 | 201 | 2 | timeout | - | - | - |
| SYJ205+1.019 | theorem | closed | 955 | 211 | 2 | timeout | - | - | - |
| SYJ205+1.020 | theorem | closed | 1085 | 221 | 2 | timeout | - | - | - |
| SYJ206+1.001 | theorem | closed | 4 | 6 | 2 | closed | 6 | 6 | 2 |
| SYJ206+1.002 | theorem | closed | 8 | 14 | 2 | closed | 10 | 17 | 3 |
| SYJ206+1.003 | theorem | closed | 65 | 121 | 17 | closed | 636 | 1333 | 180 |
| SYJ206+1.004 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.005 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.006 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.007 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.008 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.009 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.010 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.011 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.012 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.013 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.014 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.015 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.016 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.017 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.018 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.019 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ206+1.020 | theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.001 | non-theorem | open | 25 | 35 | 7 | open | 22 | 34 | 7 |
| SYJ207+1.002 | non-theorem | open | 1830 | 2838 | 656 | open | 2878 | 5456 | 1043 |
| SYJ207+1.003 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.004 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.005 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.006 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.007 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.008 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.009 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.010 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.011 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.012 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.013 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.014 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.015 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.016 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.017 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.018 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.019 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ207+1.020 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.001 | non-theorem | open | 12 | 16 | 1 | open | 13 | 16 | 1 |
| SYJ208+1.002 | non-theorem | open | 143 | 270 | 62 | open | 51 | 123 | 13 |
| SYJ208+1.003 | non-theorem | timeout | - | - | - | open | 835 | 909 | 99 |
| SYJ208+1.004 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.005 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.006 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.007 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.008 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.009 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.010 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.011 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.012 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.013 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.014 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.015 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.016 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.017 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.018 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.019 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ208+1.020 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.001 | non-theorem | open | 14 | 18 | 3 | open | 14 | 18 | 3 |
| SYJ209+1.002 | non-theorem | open | 45 | 92 | 11 | open | 48 | 92 | 11 |
| SYJ209+1.003 | non-theorem | open | 9280 | 3067 | 551 | open | 8960 | 3071 | 556 |
| SYJ209+1.004 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.005 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.006 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.007 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.008 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.009 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.010 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.011 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.012 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.013 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.014 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.015 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.016 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.017 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.018 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.019 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ209+1.020 | unsolved | timeout | - | - | - | timeout | - | - | - |
| SYJ210+1.001 | non-theorem | open | 12 | 15 | 2 | open | 8 | 15 | 2 |
| SYJ210+1.002 | non-theorem | open | 17 | 29 | 3 | open | 15 | 25 | 4 |
| SYJ210+1.003 | non-theorem | open | 24 | 43 | 4 | open | 13 | 36 | 8 |
| SYJ210+1.004 | non-theorem | open | 29 | 57 | 5 | open | 19 | 54 | 12 |
| SYJ210+1.005 | non-theorem | open | 36 | 71 | 6 | open | 22 | 69 | 16 |
| SYJ210+1.006 | non-theorem | open | 41 | 85 | 7 | open | 27 | 95 | 22 |
| SYJ210+1.007 | non-theorem | open | 54 | 99 | 8 | open | 37 | 114 | 27 |
| SYJ210+1.008 | non-theorem | open | 61 | 113 | 9 | open | 44 | 148 | 35 |
| SYJ210+1.009 | non-theorem | open | 78 | 127 | 10 | open | 45 | 171 | 41 |
| SYJ210+1.010 | non-theorem | open | 97 | 141 | 11 | open | 52 | 213 | 51 |
| SYJ210+1.011 | non-theorem | open | 139 | 155 | 12 | open | 62 | 240 | 58 |
| SYJ210+1.012 | non-theorem | open | 155 | 169 | 13 | open | 75 | 290 | 70 |
| SYJ210+1.013 | non-theorem | open | 209 | 183 | 14 | open | 80 | 321 | 78 |
| SYJ210+1.014 | non-theorem | open | 255 | 197 | 15 | open | 88 | 379 | 92 |
| SYJ210+1.015 | non-theorem | open | 305 | 211 | 16 | open | 104 | 414 | 101 |
| SYJ210+1.016 | non-theorem | open | 366 | 225 | 17 | open | 124 | 480 | 117 |
| SYJ210+1.017 | non-theorem | open | 437 | 239 | 18 | open | 143 | 519 | 127 |
| SYJ210+1.018 | non-theorem | open | 514 | 253 | 19 | open | 163 | 593 | 145 |
| SYJ210+1.019 | non-theorem | open | 593 | 267 | 20 | open | 175 | 636 | 156 |
| SYJ210+1.020 | non-theorem | open | 683 | 281 | 21 | open | 218 | 718 | 176 |
| SYJ211+1.001 | non-theorem | open | 483 | 1021 | 268 | open | 60 | 203 | 29 |
| SYJ211+1.002 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.003 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.004 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.005 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.006 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.007 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.008 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.009 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.010 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.011 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.012 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.013 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.014 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.015 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.016 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.017 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.018 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.019 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ211+1.020 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.001 | non-theorem | open | 9 | 12 | 2 | open | 10 | 12 | 2 |
| SYJ212+1.002 | non-theorem | open | 30 | 67 | 10 | open | 22 | 53 | 9 |
| SYJ212+1.003 | non-theorem | open | 349 | 496 | 103 | open | 67 | 218 | 40 |
| SYJ212+1.004 | non-theorem | timeout | - | - | - | open | 351 | 778 | 145 |
| SYJ212+1.005 | non-theorem | timeout | - | - | - | open | 2225 | 2324 | 430 |
| SYJ212+1.006 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.007 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.008 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.009 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.010 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.011 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.012 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.013 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.014 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.015 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.016 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.017 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.018 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.019 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYJ212+1.020 | non-theorem | timeout | - | - | - | timeout | - | - | - |
| SYN001+1 | non-theorem | open | 11 | 12 | 2 | open | 10 | 12 | 2 |
| SYN007+1.014 | non-theorem | error:OutOfMemoryError | - | - | - | error:OutOfMemoryError | - | - | - |
| SYN040+1 | non-theorem | open | 28 | 62 | 13 | open | 17 | 34 | 6 |
| SYN041+1 | theorem | closed | 7 | 12 | 1 | closed | 10 | 12 | 1 |
| SYN044+1 | theorem | closed | 17 | 48 | 10 | closed | 17 | 39 | 7 |
| SYN045+1 | theorem | closed | 14 | 35 | 6 | closed | 20 | 42 | 7 |
| SYN046+1 | non-theorem | open | 10 | 18 | 2 | open | 11 | 18 | 2 |
| SYN047+1 | non-theorem | open | 63 | 214 | 42 | open | 28 | 95 | 16 |
| SYN387+1 | non-theorem | open | 3 | 4 | 1 | open | 3 | 4 | 1 |
| SYN388+1 | non-theorem | open | 5 | 6 | 1 | open | 5 | 6 | 1 |
| SYN389+1 | non-theorem | open | 4 | 6 | 1 | open | 5 | 6 | 1 |
| SYN390+1 | theorem | closed | 4 | 6 | 2 | closed | 4 | 6 | 2 |
| SYN391+1 | theorem | closed | 16 | 22 | 4 | closed | 15 | 25 | 4 |
| SYN392+1 | non-theorem | open | 19 | 33 | 5 | open | 14 | 32 | 6 |
| SYN393+1 | non-theorem | open | 59 | 138 | 24 | open | 31 | 89 | 14 |
| SYN416+1 | non-theorem | open | 4 | 7 | 1 | open | 4 | 7 | 1 |
| SYN915+1 | theorem | error:IllegalArgumentException | - | - | - | error:IllegalArgumentException | - | - | - |
| SYN916+1 | non-theorem | error:IllegalArgumentException | - | - | - | error:IllegalArgumentException | - | - | - |
| SYN977+1 | non-theorem | open | 5 | 10 | 2 | open | 7 | 10 | 2 |
| SYN978+1 | theorem | closed | 6 | 10 | 2 | closed | 9 | 10 | 2 |
<!-- library-table:end -->
