package logicalSystems.ipl;
import java.nio.file.*; import java.util.*;
import logic.problem.Problem; import logic.signedFormulas.SignedFormulaCreator;
import main.newstrategy.Prover; import main.newstrategy.cpl.configurable.comparator.InsertionOrderSignedFormulaComparator;
import main.newstrategy.ipl.IPLCanonicalStrategyImplementation; import main.newstrategy.ipl.IPLSimpleStrategy;
import main.newstrategy.ipl.IPLTracer; import main.proofTree.IProofTree;
import main.tableau.Method; import main.tableau.Proof; import proverinterface.RuleStructureFactory;

/**
 * Solves ONE ILTP problem and prints one TSV line: name, declared status, obtained status,
 * nodes, branches, milliseconds. One process per problem, so a run that does not terminate
 * can be killed without leaving a thread burning CPU behind.
 *
 * <p>args: problemFile [DEFERRED|IMMEDIATE]   (PB policy, default DEFERRED)
 */
public class OneIltp {
    public static void main(String[] args) {
        Path p = Paths.get(args[0]);
        String name = p.getFileName().toString().replace(".p","");
        String declared = "unknown";
        try {
            for (String line : Files.readAllLines(p, java.nio.charset.StandardCharsets.ISO_8859_1))
                if (line.contains("Status (intuit.)")) {
                    if (line.contains("Non-Theorem")) declared="Non-Theorem";
                    else if (line.contains("Unsolved")) declared="Unsolved";
                    else if (line.contains("Theorem")) declared="Theorem";
                    break;
                }
        } catch (Exception e) {}
        try {
            StringBuilder lines = new StringBuilder();
            for (IltpProblemLoader.FofEntry e : IltpProblemLoader.load(p)) {
                String k = IltpTptpFormulaConverter.toKemsIpl(e.tptpBody);
                if ("axiom".equals(e.role)) lines.append("T ").append(k).append(" c0\n");
                else if ("conjecture".equals(e.role)) lines.append("F ").append(k).append(" c0\n");
            }
            SignedFormulaCreator c=new SignedFormulaCreator("ipl"); c.setTwoPhases(false);
            IPLTracer.setEnabled(false);
            Problem prob=c.parseText(lines.toString().trim());
            Method m=new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
            IPLSimpleStrategy s=new IPLSimpleStrategy(m); s.setComparator(new InsertionOrderSignedFormulaComparator());
            if (args.length>1 && "IMMEDIATE".equals(args[1])) s.setPbPolicy(IPLCanonicalStrategyImplementation.PBPolicy.IMMEDIATE);
            Prover pr=new Prover(); pr.setMethod(m); pr.setStrategy(s);
            long t0=System.currentTimeMillis();
            Proof proof=pr.prove(prob);
            long ms=System.currentTimeMillis()-t0;
            main.strategy.ClassicalProofTree t=(main.strategy.ClassicalProofTree)proof.getProofTree();
            System.out.printf("%s\t%s\t%s\t%d\t%d\t%d%n", name, declared,
                proof.isClosed()?"Theorem":"Non-Theorem", t.getNumberOfNodes(), leaves(t), ms);
        } catch (Throwable e) {
            String kind = (e instanceof IllegalStateException && String.valueOf(e.getMessage()).contains("Definition 5.3"))
                ? "STALL" : "ERROR:"+e.getClass().getSimpleName();
            System.out.printf("%s\t%s\t%s\t0\t0\t0%n", name, declared, kind);
        }
    }
    static int leaves(main.strategy.ClassicalProofTree n){
        if(n==null) return 0;
        IProofTree l=n.getLeft(), r=n.getRight();
        if(l==null&&r==null) return 1;
        return leaves((main.strategy.ClassicalProofTree)l)+leaves((main.strategy.ClassicalProofTree)r);
    }
}
