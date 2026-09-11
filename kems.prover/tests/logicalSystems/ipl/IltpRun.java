package logicalSystems.ipl;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

import logic.problem.Problem;
import logic.signedFormulas.SignedFormulaCreator;
import main.newstrategy.Prover;
import main.newstrategy.cpl.configurable.comparator.InsertionOrderSignedFormulaComparator;
import main.newstrategy.ipl.IPLSimpleStrategy;
import main.newstrategy.ipl.IPLTracer;
import main.newstrategy.ipl.IPLCanonicalStrategyImplementation.PBPolicy;
import main.proofTree.IProofTree;
import main.tableau.Method;
import main.tableau.Proof;
import proverinterface.RuleStructureFactory;

/**
 * Runs the IPL prover on one ILTP problem and prints one tab-separated line:
 * <pre>problem  expected  status  ms  nodes  branches</pre>
 *
 * <p>One problem per JVM is the point: every figure in the paper's evaluation was
 * produced by invoking this class once per problem from {@code benchmarks/*.sh}, so no
 * problem is timed with another one's JIT state or heap behind it.
 *
 * <p>Two modes, selected by {@code --runs}:
 * <ul>
 *   <li>{@code --runs 1} (default): a single run under a wall-clock limit. Used for the
 *       full-library sweep; on the limit the line says {@code timeout}.</li>
 *   <li>{@code --runs N} with N &gt; 1: one warmup run is discarded, then N timed runs;
 *       the median is reported. Used for the paper's benchmark table.</li>
 * </ul>
 *
 * <p>Options: {@code --policy DEFERRED|IMMEDIATE} (default DEFERRED), {@code --limit ms}
 * (default 10000), {@code --runs N}. The positional argument is a problem id such as
 * {@code SYJ209+1.003} (looked up under tests/resources/iltp/Problems) or a path to a
 * {@code .p} file. Working directory: {@code kems.prover} or the repository root.
 *
 * <p>{@code status} is {@code closed} (proof found), {@code open} (completed branch,
 * counter-model available), {@code timeout}, or {@code error:<Exception>}; the prover
 * throws instead of answering when no rule applies yet Definition 5.3 fails, and when
 * the input uses a connective Table 2 has no rule for. {@code expected} is the
 * {@code Status (intuit.)} field of the ILTP file ({@code theorem}, {@code non-theorem} or
 * {@code unsolved}: 37 problems carry no status in the library).
 */
public final class IltpRun {

    public static void main(String[] args) throws Exception {
        PBPolicy policy = PBPolicy.DEFERRED;
        long limitMs = 10_000L;
        int runs = 1;
        String target = null;
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--policy": policy = PBPolicy.valueOf(args[++i]); break;
                case "--limit":  limitMs = Long.parseLong(args[++i]); break;
                case "--runs":   runs = Integer.parseInt(args[++i]); break;
                default:         target = args[i];
            }
        }
        if (target == null) {
            System.err.println("usage: IltpRun [--policy DEFERRED|IMMEDIATE] [--limit ms] [--runs N] <problem-id|file.p>");
            System.exit(2);
        }
        final PBPolicy pol = policy;
        final long limit = limitMs;
        final int n = Math.max(runs, 1);
        final String arg = target;

        // Parsing and proving run on a thread with a 1 GiB stack: both the TPTP converter
        // and the prover recurse on formula structure, and some library formulas are
        // nested deeply enough to overflow the default stack.
        Thread worker = new Thread(null, () -> {
            String id = arg, expected = "unknown";
            long[] started = { 0L };
            try {
                Path file = resolve(arg);
                id = file.getFileName().toString().replaceFirst("\\.p$", "");
                expected = expectedStatus(file);
                final String fid = id, fexp = expected;

                // Watchdog: the limit applies to each timed run; halt() rather than
                // interrupt(), because the prover does not poll the interrupt flag.
                Thread watchdog = new Thread(() -> {
                    try {
                        while (true) {
                            Thread.sleep(50);
                            long t0 = started[0];
                            if (t0 != 0 && System.nanoTime() - t0 > limit * 1_000_000L) {
                                System.out.println(fid + "\t" + fexp + "\ttimeout\t-\t-\t-");
                                System.out.flush();
                                Runtime.getRuntime().halt(0);
                            }
                        }
                    } catch (InterruptedException ignored) { }
                });
                watchdog.setDaemon(true);
                watchdog.start();

                String polish = polish(file);
                if (n > 1) prove(polish, pol, started);                 // warmup, discarded
                List<Long> times = new ArrayList<>();
                Result last = null;
                for (int i = 0; i < n; i++) {
                    last = prove(polish, pol, started);
                    times.add(last.ms);
                }
                times.sort(null);
                long median = times.get(times.size() / 2);
                System.out.println(id + "\t" + expected + "\t" + (last.closed ? "closed" : "open")
                        + "\t" + median + "\t" + last.nodes + "\t" + last.branches);
            } catch (Throwable t) {
                System.out.println(id + "\t" + expected + "\terror:" + t.getClass().getSimpleName() + "\t-\t-\t-");
            }
            System.out.flush();
            Runtime.getRuntime().halt(0);
        }, "iltp-run", 1L << 30);
        worker.start();
        worker.join();
    }

    private static final class Result {
        final boolean closed; final long ms; final int nodes; final int branches;
        Result(boolean closed, long ms, int nodes, int branches) {
            this.closed = closed; this.ms = ms; this.nodes = nodes; this.branches = branches;
        }
    }

    private static Result prove(String polish, PBPolicy policy, long[] started) throws Exception {
        SignedFormulaCreator creator = new SignedFormulaCreator("ipl");
        creator.setTwoPhases(false);
        IPLTracer.setEnabled(false);
        Problem problem = creator.parseText(polish);
        Method method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
        IPLSimpleStrategy strategy = new IPLSimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());
        strategy.setPbPolicy(policy);
        Prover prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);

        started[0] = System.nanoTime();
        Proof proof = prover.prove(problem);
        long ms = (System.nanoTime() - started[0]) / 1_000_000L;
        started[0] = 0L;
        IProofTree tree = proof.getProofTree();
        return new Result(proof.isClosed(), ms, tree.getNumberOfNodes(), leaves(tree));
    }

    /** Branches of the finished derivation: leaves of the proof tree. */
    static int leaves(IProofTree t) {
        if (t == null) return 0;
        if (t.getLeft() == null && t.getRight() == null) return 1;
        return leaves(t.getLeft()) + leaves(t.getRight());
    }

    static Path resolve(String target) throws Exception {
        Path p = Paths.get(target);
        if (Files.isRegularFile(p)) return p;
        String name = target.endsWith(".p") ? target : target + ".p";
        for (String root : new String[] { "tests/resources/iltp/Problems", "kems.prover/tests/resources/iltp/Problems" }) {
            Path dir = Paths.get(root);
            if (!Files.isDirectory(dir)) continue;
            try (Stream<Path> s = Files.walk(dir)) {
                Path hit = s.filter(f -> f.getFileName().toString().equals(name)).findFirst().orElse(null);
                if (hit != null) return hit;
            }
        }
        throw new IllegalArgumentException("problem not found: " + target);
    }

    /** The {@code Status (intuit.)} field of an ILTP problem file. */
    static String expectedStatus(Path file) throws Exception {
        for (String line : Files.readAllLines(file)) {
            if (!line.contains("Status (intuit.)")) continue;
            if (line.contains("Non-Theorem")) return "non-theorem";
            if (line.contains("Theorem")) return "theorem";
            if (line.contains("Unsolved")) return "unsolved";
        }
        return "unknown";
    }

    /** Axioms as T ... : c0 and the conjecture as F ... : c0, in the prover's Polish syntax. */
    static String polish(Path file) throws Exception {
        StringBuilder sb = new StringBuilder();
        for (IltpProblemLoader.FofEntry e : IltpProblemLoader.load(file)) {
            String kems = IltpTptpFormulaConverter.toKemsIpl(e.tptpBody);
            if ("axiom".equals(e.role)) sb.append("T ").append(kems).append(" c0\n");
            else if ("conjecture".equals(e.role)) sb.append("F ").append(kems).append(" c0\n");
        }
        return sb.toString().trim();
    }

    private IltpRun() { }
}
