package logicalSystems.ipl;

import static org.junit.Assert.*;
import org.junit.Test;

import logic.formulas.FormulaFactory;
import logic.formulas.Formula;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.problem.Problem;
import logic.signedFormulas.SignedFormula;
import logicalSystems.ipl.IPLConnectives;
import logic.signedFormulas.FormulaSign;
import logicalSystems.ipl.IPLSigns;
import logicalSystems.ipl.IPLSignedFormulaFactory;
import main.newstrategy.cpl.configurable.comparator.InsertionOrderSignedFormulaComparator;
import main.newstrategy.ipl.IPLSimpleStrategy;
import main.newstrategy.Prover;
import main.tableau.Method;
import main.tableau.Proof;
import main.proofTree.IProofTree;
import proverinterface.RuleStructureFactory;

/**
 * Comprehensive test of IPL rules using an explicit Context to establish
 * ordering relations between labels according to the paper "Free-variable KE tableaux for IPL"
 *
 * Unlike IPLRulesComprehensiveTest, which uses string parsing,
 * this test creates formulas directly with Context to
 * explicitly establish the partial ordering relations between labels.
 */
public class IPLRulesContextTest {

    /**
     * Base method for creating a proof with an explicit Context
     */
    private Proof proveWithContext(TestCase testCase) throws Exception {
        // Create problem with IPLSignedFormulaFactory
        Problem problem = new Problem("ipl");
        IPLSignedFormulaFactory iplFactory = new IPLSignedFormulaFactory();
        problem.setSignedFormulaFactory(iplFactory);

        // Get the Context from the factory
        Context context = iplFactory.getContext();

        // Establish the ordering relations according to the test case
        ContextFormulaLabel[] labels = testCase.createLabelsWithOrdering(context);

        // Create formulas using FormulaFactory
        FormulaFactory ff = new FormulaFactory();

        // Create the formulas for the test case
        for (int i = 0; i < testCase.formulas.length; i++) {
            FormulaSpec spec = testCase.formulas[i];

            // Create the formula
            Formula formula = createFormula(ff, spec);

            // Create SignedFormula with the correct label
            SignedFormula signedFormula = iplFactory.createSignedFormula(
                spec.sign, formula, labels[spec.labelIndex]);

            // Create LabelledFormula (the factory will preserve the ContextFormulaLabel)
            LabelledFormula labelledFormula = iplFactory.createLabelledFormula(
                labels[spec.labelIndex], signedFormula);

            problem.getFormulas().add(labelledFormula);
        }

        // Create method with IPL rules
        Method method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));

        // Create IPL strategy
        IPLSimpleStrategy strategy = new IPLSimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());

        // Create and configure the prover
        Prover prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);

        return prover.prove(problem);
    }

    /**
     * Creates a formula based on the specification
     */
    private Formula createFormula(FormulaFactory ff, FormulaSpec spec) {
        switch (spec.type) {
            case ATOMIC:
                return ff.createAtomicFormula(spec.name);
                
            case OR:
                Formula left = createFormula(ff, spec.subformulas[0]);
                Formula right = createFormula(ff, spec.subformulas[1]);
                return ff.createCompositeFormula(IPLConnectives.OR, left, right);
                
            case AND:
                Formula leftAnd = createFormula(ff, spec.subformulas[0]);
                Formula rightAnd = createFormula(ff, spec.subformulas[1]);
                return ff.createCompositeFormula(IPLConnectives.AND, leftAnd, rightAnd);
                
            case IMPLICATION:
                Formula leftImp = createFormula(ff, spec.subformulas[0]);
                Formula rightImp = createFormula(ff, spec.subformulas[1]);
                return ff.createCompositeFormula(IPLConnectives.IMPLIES, leftImp, rightImp);
                
            default:
                throw new RuntimeException("Unsupported formula type: " + spec.type);
        }
    }

    // =====================================
    // HELPER CLASSES FOR DEFINING TEST CASES
    // =====================================

    /**
     * Specifies a test case with formulas and ordering relations
     */
    static class TestCase {
        String name;
        String description;
        FormulaSpec[] formulas;
        String[] expectedConclusions;
        boolean shouldBeClosed;
        OrderRelation[] labelOrdering;
        
        TestCase(String name, String description, FormulaSpec[] formulas, 
                 OrderRelation[] labelOrdering, String[] expectedConclusions, 
                 boolean shouldBeClosed) {
            this.name = name;
            this.description = description;
            this.formulas = formulas;
            this.labelOrdering = labelOrdering;
            this.expectedConclusions = expectedConclusions;
            this.shouldBeClosed = shouldBeClosed;
        }
        
        /**
         * Creates the labels and establishes the ordering relations in the Context
         */
        ContextFormulaLabel[] createLabelsWithOrdering(Context context) {
            // Determine how many labels we need
            int maxLabelIndex = 0;
            for (FormulaSpec formula : formulas) {
                if (formula.labelIndex > maxLabelIndex) {
                    maxLabelIndex = formula.labelIndex;
                }
            }

            ContextFormulaLabel[] labels = new ContextFormulaLabel[maxLabelIndex + 1];

            // Create base labels
            for (int i = 0; i <= maxLabelIndex; i++) {
                labels[i] = (ContextFormulaLabel) context.getNewFormulaLabel();
            }

            // Establish ordering relations
            for (OrderRelation relation : labelOrdering) {
                context.setAsGreaterThan(labels[relation.smaller], labels[relation.greater]);
            }

            return labels;
        }
    }

    /**
     * Specifies a formula with its type, sign, and label
     */
    static class FormulaSpec {
        FormulaType type;
        String name;
        FormulaSpec[] subformulas;
        FormulaSign sign;
        int labelIndex;

        // Constructor for atomic formulas
        FormulaSpec(FormulaType type, String name, FormulaSign sign, int labelIndex) {
            this.type = type;
            this.name = name;
            this.sign = sign;
            this.labelIndex = labelIndex;
        }

        // Constructor for composite formulas
        FormulaSpec(FormulaType type, FormulaSpec[] subformulas, FormulaSign sign, int labelIndex) {
            this.type = type;
            this.subformulas = subformulas;
            this.sign = sign;
            this.labelIndex = labelIndex;
        }
    }

    enum FormulaType {
        ATOMIC, OR, AND, IMPLICATION
    }

    /**
     * Specifies an ordering relation: smaller ≤ greater
     */
    static class OrderRelation {
        int smaller;
        int greater;

        OrderRelation(int smaller, int greater) {
            this.smaller = smaller;
            this.greater = greater;
        }
    }

    // =====================================
    // IPL RULE TESTS
    // =====================================
    
    @Test
    public void testRule1_F_OR_BasicApplication() {
        System.out.println("\n=== TEST RULE 1: F_OR (Context-based) ===");
        System.out.println("F (P\u2228Q) c0 \u2192 F P c0, F Q c0");

        try {
            // Define test case: F (P∨Q) c0
            FormulaSpec P = new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.FALSE, 0);
            FormulaSpec Q = new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.FALSE, 0);
            FormulaSpec PorQ = new FormulaSpec(FormulaType.OR, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.FALSE, 0);

            TestCase testCase = new TestCase(
                "F_OR",
                "F (P\u2228Q) c0 \u2192 F P c0, F Q c0",
                new FormulaSpec[]{PorQ},
                new OrderRelation[]{}, // No specific ordering relations are needed
                new String[]{"F P c0", "F Q c0"},
                false
            );

            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Resulting tree:");
            System.out.println(treeOutput);

            // Verify that F_OR was applied
            assertTrue("Should generate F P c0", treeOutput.contains("F P c0"));
            assertTrue("Should generate F Q c0", treeOutput.contains("F Q c0"));

            System.out.println("✅ RULE 1 (F_OR): CORRECT");

        } catch (Exception e) {
            fail("Error in F_OR test: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule3_X_OR_F_LEFT_ValidLabelCondition() {
        System.out.println("\n=== TEST RULE 3: X_OR_F_LEFT (Context-based) ===");
        System.out.println("T (P\u2228Q) c0, F P c1 (c0 \u2AAF c1: main.label \u2264 aux.label) \u2192 T Q c0");

        try {
            // Define test case: T (P∨Q) c0, F P c1 with c0 ≤ c1
            FormulaSpec PorQ = new FormulaSpec(FormulaType.OR, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.TRUE, 0);

            FormulaSpec FalseP = new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.FALSE, 1);

            TestCase testCase = new TestCase(
                "X_OR_F_LEFT",
                "T (P\u2228Q) c0, F P c1 (c0 \u2264 c1) \u2192 T Q c0",
                new FormulaSpec[]{PorQ, FalseP},
                new OrderRelation[]{new OrderRelation(0, 1)}, // c0 ≤ c1
                new String[]{"T Q c0"},
                false
            );

            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Resulting tree:");
            System.out.println(treeOutput);

            // Verify that the rule was applied and generated T Q c0
            assertTrue("Should generate T Q c0", treeOutput.contains("T Q c0"));
            assertFalse("Should NOT be closed", proof.isClosed());

            System.out.println("✅ RULE 3 (X_OR_F_LEFT): CORRECT with explicit Context");

        } catch (Exception e) {
            fail("Error in X_OR_F_LEFT test: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule4_X_OR_F_RIGHT_ValidLabelCondition() {
        System.out.println("\n=== TEST RULE 4: X_OR_F_RIGHT (Context-based) ===");
        System.out.println("T (P\u2228Q) c0, F Q c1 (c0 \u2AAF c1: main.label \u2264 aux.label) \u2192 T P c0");

        try {
            // Define test case: T (P∨Q) c0, F Q c1 with c0 ≤ c1
            FormulaSpec PorQ = new FormulaSpec(FormulaType.OR, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.TRUE, 0);

            FormulaSpec FalseQ = new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.FALSE, 1);

            TestCase testCase = new TestCase(
                "X_OR_F_RIGHT",
                "T (P\u2228Q) c0, F Q c1 (c0 \u2264 c1) \u2192 T P c0",
                new FormulaSpec[]{PorQ, FalseQ},
                new OrderRelation[]{new OrderRelation(0, 1)}, // c0 ≤ c1
                new String[]{"T P c0"},
                false
            );

            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Resulting tree:");
            System.out.println(treeOutput);

            // Verify that the rule was applied and generated T P c0
            assertTrue("Should generate T P c0", treeOutput.contains("T P c0"));
            assertFalse("Should NOT be closed", proof.isClosed());

            System.out.println("✅ RULE 4 (X_OR_F_RIGHT): CORRECT with explicit Context");

        } catch (Exception e) {
            fail("Error in X_OR_F_RIGHT test: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule5_F_AND_BasicApplication() {
        System.out.println("\n=== TEST RULE 5: F_AND (Context-based) ===");
        System.out.println("F (P\u2227Q) c0 \u2192 F P c0 | F Q c0");

        try {
            // Define test case: F (P∧Q) c0
            FormulaSpec PandQ = new FormulaSpec(FormulaType.AND, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.FALSE, 0);

            TestCase testCase = new TestCase(
                "F_AND",
                "F (P\u2227Q) c0 \u2192 F P c0 | F Q c0",
                new FormulaSpec[]{PandQ},
                new OrderRelation[]{}, // No specific ordering relations are needed
                new String[]{"F P c0", "F Q c0"},
                false
            );

            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Resulting tree:");
            System.out.println(treeOutput);

            // Verify that F_AND was applied (produces branches)
            assertTrue("Should contain F P c0 or F Q c0",
                treeOutput.contains("F P c0") || treeOutput.contains("F Q c0"));

            System.out.println("✅ RULE 5 (F_AND): CORRECT");

        } catch (Exception e) {
            fail("Error in F_AND test: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule7_T_AND_ValidLabelCondition() {
        System.out.println("\n=== TEST RULE 7: T_AND (Context-based) ===");
        System.out.println("T (P\u2227Q) c0 \u2192 T P c0, T Q c0");

        try {
            // Define test case: T (P∧Q) c0
            FormulaSpec PandQ = new FormulaSpec(FormulaType.AND, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.TRUE, 0);

            TestCase testCase = new TestCase(
                "T_AND",
                "T (P\u2227Q) c0 \u2192 T P c0, T Q c0",
                new FormulaSpec[]{PandQ},
                new OrderRelation[]{}, // No specific ordering relations are needed
                new String[]{"T P c0", "T Q c0"},
                false
            );

            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Resulting tree:");
            System.out.println(treeOutput);

            // Verify that T_AND was applied
            assertTrue("Should generate T P c0", treeOutput.contains("T P c0"));
            assertTrue("Should generate T Q c0", treeOutput.contains("T Q c0"));

            System.out.println("✅ RULE 7 (T_AND): CORRECT");

        } catch (Exception e) {
            fail("Error in T_AND test: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule11_F_IMPLICATION_BasicApplication() {
        System.out.println("\n=== TEST RULE 11: F_IMPLICATION (Context-based) ===");
        System.out.println("F (P\u2192Q) c0 \u2192 T P c0, F Q c0");

        try {
            // Define test case: F (P→Q) c0
            FormulaSpec PimpQ = new FormulaSpec(FormulaType.IMPLICATION, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.FALSE, 0);

            TestCase testCase = new TestCase(
                "F_IMPLICATION",
                "F (P\u2192Q) c0 \u2192 T P c0, F Q c0",
                new FormulaSpec[]{PimpQ},
                new OrderRelation[]{}, // No specific ordering relations are needed
                new String[]{"T P c0", "F Q c0"},
                false
            );

            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Resulting tree:");
            System.out.println(treeOutput);

            // Verify that F_IMPLICATION was applied
            assertTrue("Should generate T P c0", treeOutput.contains("T P c0"));
            assertTrue("Should generate F Q c0", treeOutput.contains("F Q c0"));

            System.out.println("✅ RULE 11 (F_IMPLICATION): CORRECT");

        } catch (Exception e) {
            fail("Error in F_IMPLICATION test: " + e.getMessage());
        }
    }
    
    @Test
    public void testLabelOrderingComparisons() {
        System.out.println("\n=== TEST: LABEL ORDERING VERIFICATION ===");
        System.out.println("Verifying that the relations c0 \u2264 c1 \u2264 c2 are established correctly");

        try {
            // Create problem and context
            Problem problem = new Problem("ipl");
            IPLSignedFormulaFactory iplFactory = new IPLSignedFormulaFactory();
            problem.setSignedFormulaFactory(iplFactory);
            Context context = iplFactory.getContext();

            // Create labels with ordering relations: c0 ≤ c1 ≤ c2
            ContextFormulaLabel c0 = (ContextFormulaLabel) context.getNewFormulaLabel();
            ContextFormulaLabel c1 = (ContextFormulaLabel) context.getNewFormulaLabelGreaterThan(c0);
            ContextFormulaLabel c2 = (ContextFormulaLabel) context.getNewFormulaLabelGreaterThan(c1);

            System.out.println("Labels created: c0=" + c0 + ", c1=" + c1 + ", c2=" + c2);

            // Verify ordering relations
            assertTrue("c0 \u2264 c0 should be true", c0.lowerOrEqualThan(c0));
            assertTrue("c0 \u2264 c1 should be true", c0.lowerOrEqualThan(c1));
            assertTrue("c0 \u2264 c2 should be true", c0.lowerOrEqualThan(c2));
            assertTrue("c1 \u2264 c1 should be true", c1.lowerOrEqualThan(c1));
            assertTrue("c1 \u2264 c2 should be true", c1.lowerOrEqualThan(c2));
            assertTrue("c2 \u2264 c2 should be true", c2.lowerOrEqualThan(c2));

            assertFalse("c1 \u2264 c0 should be false", c1.lowerOrEqualThan(c0));
            assertFalse("c2 \u2264 c0 should be false", c2.lowerOrEqualThan(c0));
            assertFalse("c2 \u2264 c1 should be false", c2.lowerOrEqualThan(c1));

            System.out.println("✅ LABEL ORDERING: CORRECT");

        } catch (Exception e) {
            fail("Error in ordering test: " + e.getMessage());
        }
    }
}
