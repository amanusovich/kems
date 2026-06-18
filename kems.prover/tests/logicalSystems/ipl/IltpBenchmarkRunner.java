package logicalSystems.ipl;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Locale;

import logic.problem.Problem;
import logic.signedFormulas.SignedFormulaCreator;
import main.newstrategy.Prover;
import main.newstrategy.cpl.configurable.comparator.InsertionOrderSignedFormulaComparator;
import main.newstrategy.ipl.IPLSimpleStrategy;
import main.newstrategy.ipl.IPLTracer;
import main.tableau.Method;
import main.tableau.Proof;
import proverinterface.RuleStructureFactory;

/**
 * Repeatable ILTP timing harness for the LANMR evaluation table.
 *
 * <p>Methodology (standard for Java prover papers):
 * <ul>
 *   <li>Measure wall-clock time of {@code prover.prove()} only (parse and file
 *       load are done once per problem beforehand).</li>
 *   <li>{@link IPLTracer} disabled; no proof-tree or trace I/O.</li>
 *   <li>One JVM warmup pass over the whole suite (discarded) so JIT compilation
 *       does not skew the first timed problem.</li>
 *   <li>{@value #MEASUREMENT_RUNS} timed runs per problem; report the
 *       <em>median</em> (robust to outliers).</li>
 *   <li>Per-run timeout ({@value #TIMEOUT_MS} ms); timed out runs are dropped
 *       from the median (status {@code timeout} if all runs time out).</li>
 * </ul>
 *
 * <p>Run from IntelliJ (Run {@code IltpBenchmarkRunner.main}) with working
 * directory {@code kems.prover}, or:
 * <pre>
 *   java -cp ... logicalSystems.ipl.IltpBenchmarkRunner
 * </pre>
 *
 * <p>Do <strong>not</strong> use the web UI timer ({@code performance.now()} on
 * {@code /api/prove}): that includes HTTP, HTML export, and tracer overhead,
 * and Fly.io cold starts.
 */
public final class IltpBenchmarkRunner {

    private static final int WARMUP_PASSES = 1;
    private static final int MEASUREMENT_RUNS = 5;
    private static final long TIMEOUT_MS = 60_000L;

    private static final String[][] PROBLEMS = {
        {"SYJ", "SYJ201+1.001.p"},
        {"SYJ", "SYJ207+1.001.p"},
        {"SYN", "SYN001+1.p"},
        {"SYN", "SYN041+1.p"},
        {"SYN", "SYN046+1.p"},
        {"LCL", "LCL181+1.p"},
    };

    public static void main(String[] args) throws Exception {
        printEnvironment();
        List<LoadedProblem> loaded = loadAll();
        if (loaded.isEmpty()) {
            System.err.println("No ILTP problems found.");
            System.exit(1);
        }

        System.out.println("# Warmup (" + WARMUP_PASSES + " pass(es), discarded)");
        for (int w = 0; w < WARMUP_PASSES; w++) {
            for (LoadedProblem lp : loaded) {
                runOnce(lp, TIMEOUT_MS);
            }
        }

        System.out.println("# Measurement (" + MEASUREMENT_RUNS
                + " runs/problem, median ms, timeout=" + TIMEOUT_MS + " ms)");
        System.out.println("problem\texpected\tstatus\tmedian_ms\tmin_ms\tmax_ms\tnodes");
        for (LoadedProblem lp : loaded) {
            printRow(measure(lp));
        }
    }

    private static void printEnvironment() {
        System.out.println("# ILTP benchmark environment");
        System.out.println("java.version\t" + System.getProperty("java.version"));
        System.out.println("java.vendor\t" + System.getProperty("java.vendor"));
        System.out.println("os.name\t" + System.getProperty("os.name"));
        System.out.println("os.arch\t" + System.getProperty("os.arch"));
        System.out.println("user.dir\t" + System.getProperty("user.dir"));
        System.out.println("tracer\toff");
        System.out.println("strategy\tIPLSimpleStrategy");
        System.out.println("timed_scope\tprover.prove() only");
    }

    private static List<LoadedProblem> loadAll() throws Exception {
        SignedFormulaCreator creator = new SignedFormulaCreator("ipl");
        creator.setTwoPhases(false);
        IPLTracer.setEnabled(false);

        List<LoadedProblem> out = new ArrayList<LoadedProblem>();
        for (String[] spec : PROBLEMS) {
            Path path = IltpPropBenchmarkTest.resolveProblem(spec[0], spec[1]);
            if (!Files.isRegularFile(path)) {
                System.err.println("SKIP missing " + path);
                continue;
            }
            String polish = polishFromFile(path);
            Problem problem = creator.parseText(polish);
            String id = spec[1].replace(".p", "");
            String expected = readIntuitStatus(path);
            out.add(new LoadedProblem(id, expected, polish, problem));
        }
        return out;
    }

    private static String polishFromFile(Path path) throws Exception {
        List<IltpProblemLoader.FofEntry> entries = IltpProblemLoader.load(path);
        StringBuilder lines = new StringBuilder();
        for (IltpProblemLoader.FofEntry e : entries) {
            String kems = IltpTptpFormulaConverter.toKemsIpl(e.tptpBody);
            if ("axiom".equals(e.role)) {
                lines.append("T ").append(kems).append(" c0\n");
            } else if ("conjecture".equals(e.role)) {
                lines.append("F ").append(kems).append(" c0\n");
            }
        }
        return lines.toString().trim();
    }

    private static String readIntuitStatus(Path path) throws Exception {
        for (String line : Files.readAllLines(path)) {
            if (line.contains("Status (intuit.)")) {
                if (line.contains("Non-Theorem")) {
                    return "non-theorem";
                }
                if (line.contains("Theorem")) {
                    return "theorem";
                }
            }
        }
        return "unknown";
    }

    private static MeasurementRow measure(LoadedProblem lp) {
        List<Long> times = new ArrayList<Long>();
        Boolean closed = null;
        int nodes = 0;
        int timeouts = 0;

        for (int i = 0; i < MEASUREMENT_RUNS; i++) {
            TimedProof tp = runOnce(lp, TIMEOUT_MS);
            if (tp == null) {
                timeouts++;
                continue;
            }
            times.add(tp.timeMs);
            closed = tp.closed;
            nodes = tp.nodes;
        }

        String status;
        if (times.isEmpty()) {
            status = "timeout";
        } else if (Boolean.TRUE.equals(closed)) {
            status = "closed";
        } else {
            status = "open";
        }

        long median = times.isEmpty() ? -1L : median(times);
        long min = times.isEmpty() ? -1L : Collections.min(times);
        long max = times.isEmpty() ? -1L : Collections.max(times);
        return new MeasurementRow(lp.id, lp.expected, status, median, min, max, nodes, timeouts);
    }

    private static TimedProof runOnce(LoadedProblem lp, long timeoutMs) {
        final SignedFormulaCreator creator = new SignedFormulaCreator("ipl");
        creator.setTwoPhases(false);
        final String polish = lp.polish;

        final TimedProof[] result = new TimedProof[1];
        final Exception[] error = new Exception[1];

        Thread worker = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    Problem problem = creator.parseText(polish);
                    Method method = new Method(
                            RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
                    IPLSimpleStrategy strategy = new IPLSimpleStrategy(method);
                    strategy.setComparator(new InsertionOrderSignedFormulaComparator());
                    Prover prover = new Prover();
                    prover.setMethod(method);
                    prover.setStrategy(strategy);
                    IPLTracer.getInstance().reset();

                    long t0 = System.nanoTime();
                    Proof proof = prover.prove(problem);
                    long timeMs = (System.nanoTime() - t0) / 1_000_000L;
                    result[0] = new TimedProof(proof.isClosed(), timeMs,
                            proof.getProofTree().getNumberOfNodes());
                } catch (Exception ex) {
                    error[0] = ex;
                }
            }
        }, "iltp-prove");
        worker.setDaemon(true);
        worker.start();
        try {
            worker.join(timeoutMs);
        } catch (InterruptedException ex) {
            Thread.currentThread().interrupt();
            return null;
        }
        if (worker.isAlive()) {
            worker.interrupt();
            return null;
        }
        if (error[0] != null) {
            throw new RuntimeException(error[0]);
        }
        return result[0];
    }

    private static long median(List<Long> values) {
        List<Long> copy = new ArrayList<Long>(values);
        Collections.sort(copy);
        int n = copy.size();
        if (n % 2 == 1) {
            return copy.get(n / 2);
        }
        return (copy.get(n / 2 - 1) + copy.get(n / 2)) / 2;
    }

    private static void printRow(MeasurementRow row) {
        System.out.printf(Locale.ROOT, "%s\t%s\t%s\t%d\t%d\t%d\t%d%n",
                row.id, row.expected, row.status, row.medianMs, row.minMs, row.maxMs, row.nodes);
        if (row.timeouts > 0) {
            System.err.println("# " + row.id + ": " + row.timeouts
                    + " run(s) hit timeout (" + TIMEOUT_MS + " ms)");
        }
    }

    private static final class LoadedProblem {
        final String id;
        final String expected;
        final String polish;

        LoadedProblem(String id, String expected, String polish, Problem ignored) {
            this.id = id;
            this.expected = expected;
            this.polish = polish;
        }
    }

    private static final class TimedProof {
        final boolean closed;
        final long timeMs;
        final int nodes;

        TimedProof(boolean closed, long timeMs, int nodes) {
            this.closed = closed;
            this.timeMs = timeMs;
            this.nodes = nodes;
        }
    }

    private static final class MeasurementRow {
        final String id;
        final String expected;
        final String status;
        final long medianMs;
        final long minMs;
        final long maxMs;
        final int nodes;
        final int timeouts;

        MeasurementRow(String id, String expected, String status,
                long medianMs, long minMs, long maxMs, int nodes, int timeouts) {
            this.id = id;
            this.expected = expected;
            this.status = status;
            this.medianMs = medianMs;
            this.minMs = minMs;
            this.maxMs = maxMs;
            this.nodes = nodes;
            this.timeouts = timeouts;
        }
    }

    private IltpBenchmarkRunner() {}
}
