ILTP v1.1.2 propositional fragments (subset) for IPL regression tests.

Source: https://www.iltp.de/ — tarball ILTP-v1.1.2-propositional.tar.gz

To refresh or add problems, extract e.g.:
  tar -xzf ILTP-v1.1.2-propositional.tar.gz \
    ILTP-v1.1.2-propositional/Problems/SYN/SYN041+1.p \
    --strip-components=3
into Problems/<Domain>/ (see ILTP directory layout).

Tests resolve paths from working directory kems.prover/ or repository root
(see IltpPropBenchmarkTest.resolveProblem).

Repeatable timings for the LANMR paper (warmup + median of 5 runs):
  Run logicalSystems.ipl.IltpBenchmarkRunner.main from IntelliJ
  (working directory kems.prover). Copy median_ms and nodes into
  paper-lanmr2026/sections/05-evaluation.tex.
  Do not use the web UI "Done in Xs" timer for the table.
