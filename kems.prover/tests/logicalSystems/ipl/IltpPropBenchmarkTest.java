package logicalSystems.ipl;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assume.assumeTrue;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;

import logic.problem.Problem;
import logic.signedFormulas.SignedFormulaCreator;
import main.newstrategy.Prover;
import main.newstrategy.cpl.configurable.comparator.InsertionOrderSignedFormulaComparator;
import main.newstrategy.ipl.IPLSimpleStrategy;
import main.newstrategy.ipl.IPLTracer;
import main.proofTree.IProofTree;
import main.tableau.Method;
import main.tableau.Proof;
import proverinterface.RuleStructureFactory;

/**
 * Regression tests from the ILTP v1.1.2 propositional library
 * (<a href="https://www.iltp.de/">iltp.de</a>). Problem files live under
 * {@code kems.prover/tests/resources/iltp/Problems/} (run with working directory
 * {@code kems.prover} or repository root — see {@link #resolveProblem}).
 * <p>
 * Expected status uses the {@code Status (intuit.)} line in each {@code .p} file.
 */
public class IltpPropBenchmarkTest {

    private SignedFormulaCreator signedFormulaCreator;

    @Before
    public void setUp() {
        // Same base setup as IPLRulesComprehensiveTest (IPL parser + no Wagner pre-phase).
        signedFormulaCreator = new SignedFormulaCreator("ipl");
        signedFormulaCreator.setTwoPhases(false);
        // ILTP suite: keep trace off (ComprehensiveTest enables it for rule-level logs).
        IPLTracer.setEnabled(false);
    }

    @Test
    public void converter_syn041_matches_manual() {
        assertEquals(
                "->(-(->(p q)) (->(q p)))",
                IltpTptpFormulaConverter.toKemsIpl("( ~ ( p => q ) => ( q => p ) )"));
    }

    @Test
    public void iltp_SYN041_intuit_theorem_closes() throws Exception {
        Path p = resolveProblem("SYN", "SYN041+1.p");
        assumeTrue("ILTP problem file missing: " + p, Files.isRegularFile(p));
        Proof proof = proveLoaded(p);
        printProofTree(proof, p);
        assertTrue("SYN041+1: Status (intuit.) Theorem → expect closed", proof.isClosed());
    }

    @Test
    public void iltp_SYN001_intuit_nonTheorem_stays_open() throws Exception {
        Path p = resolveProblem("SYN", "SYN001+1.p");
        assumeTrue("ILTP problem file missing: " + p, Files.isRegularFile(p));
        Proof proof = proveLoaded(p);
        printProofTree(proof, p);
        assertFalse("SYN001+1: Status (intuit.) Non-Theorem → expect not closed", proof.isClosed());
    }

    @Test
    public void iltp_SYN046_intuit_nonTheorem_stays_open() throws Exception {
        Path p = resolveProblem("SYN", "SYN046+1.p");
        assumeTrue("ILTP problem file missing: " + p, Files.isRegularFile(p));
        Proof proof = proveLoaded(p);
        printProofTree(proof, p);
        assertFalse("SYN046+1: Status (intuit.) Non-Theorem → expect not closed", proof.isClosed());
    }

    @Test
    public void iltp_LCL181_intuit_nonTheorem_stays_open() throws Exception {
        Path p = resolveProblem("LCL", "LCL181+1.p");
        assumeTrue("ILTP problem file missing: " + p, Files.isRegularFile(p));
        Proof proof = proveLoaded(p);
        printProofTree(proof, p);
        assertFalse("LCL181+1: Status (intuit.) Non-Theorem → expect not closed", proof.isClosed());
    }

    @Test
    public void iltp_SYJ201_1_001_intuit_theorem_closes() throws Exception {
        Path p = resolveProblem("SYJ", "SYJ201+1.001.p");
        assumeTrue("ILTP problem file missing: " + p, Files.isRegularFile(p));
        Proof proof = proveLoaded(p);
        printProofTree(proof, p);
        assertTrue("SYJ201+1.001: Status (intuit.) Theorem → expect closed", proof.isClosed());
    }

    @Test
    public void iltp_SYJ207_1_001_intuit_nonTheorem_stays_open() throws Exception {
        Path p = resolveProblem("SYJ", "SYJ207+1.001.p");
        assumeTrue("ILTP problem file missing: " + p, Files.isRegularFile(p));
        Proof proof = proveLoaded(p);
        printProofTree(proof, p);
        assertFalse("SYJ207+1.001: Status (intuit.) Non-Theorem → expect not closed", proof.isClosed());
    }

    /** Same pattern as {@link IPLRulesComprehensiveTest}: {@code tree.toString()} after proof. */
    private void printProofTree(Proof proof, Path problemFile) {
        IProofTree tree = proof.getProofTree();
        String treeOutput = tree.toString();
        System.out.println(problemFile.getFileName() + ":");
        System.out.println("Árbol resultado:");
        System.out.println(treeOutput);
    }

    private Proof proveLoaded(Path path) throws Exception {
        List<IltpProblemLoader.FofEntry> entries = IltpProblemLoader.load(path);
        Assume.assumeFalse("No fof entries in " + path, entries.isEmpty());
        StringBuilder lines = new StringBuilder();
        for (IltpProblemLoader.FofEntry e : entries) {
            String kems = IltpTptpFormulaConverter.toKemsIpl(e.tptpBody);
            if ("axiom".equals(e.role)) {
                lines.append("T ").append(kems).append(" c0\n");
            } else if ("conjecture".equals(e.role)) {
                lines.append("F ").append(kems).append(" c0\n");
            }
        }
        return proveText(lines.toString().trim());
    }

    /**
     * Mirrors {@link IPLRulesComprehensiveTest#proveFormulasWithContext} for the
     * default case {@code predefinedContext == null}: same {@link Method}, {@link IPLSimpleStrategy},
     * and {@link InsertionOrderSignedFormulaComparator}. ILTP strings use label {@code c0} only, so
     * the custom Context / {@link IPLSignedFormulaFactory} relabelling path is not used.
     */
    private Proof proveText(String allFormulas) throws Exception {
        Problem problem = signedFormulaCreator.parseText(allFormulas);

        Method method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
        IPLSimpleStrategy strategy = new IPLSimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());

        Prover prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);

        IPLTracer.getInstance().reset();
        return prover.prove(problem);
    }

    /**
     * Resolves {@code tests/resources/iltp/Problems/<sub>/...} from either
     * {@code kems.prover} or repository root as current working directory.
     */
    static Path resolveProblem(String subdir, String filename) {
        String cwd = System.getProperty("user.dir");
        Path a = Paths.get(cwd, "tests", "resources", "iltp", "Problems", subdir, filename);
        if (Files.isRegularFile(a)) {
            return a;
        }
        Path b = Paths.get(cwd, "kems.prover", "tests", "resources", "iltp", "Problems", subdir, filename);
        if (Files.isRegularFile(b)) {
            return b;
        }
        return a;
    }
}
