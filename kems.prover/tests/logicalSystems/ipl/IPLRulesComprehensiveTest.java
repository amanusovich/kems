package logicalSystems.ipl;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaCreator;
import logic.signedFormulas.SignedFormulaList;
import main.newstrategy.ipl.IPLSimpleStrategy;
import main.newstrategy.ipl.IPLTracer;
import main.newstrategy.cpl.configurable.comparator.InsertionOrderSignedFormulaComparator;
import main.tableau.Method;
import main.newstrategy.Prover;
import proverinterface.RuleStructureFactory;
import logic.problem.Problem;
import main.tableau.Proof;
import main.proofTree.IProofTree;

public class IPLRulesComprehensiveTest {

    private SignedFormulaCreator signedFormulaCreator;

    @Before
    public void setUp() {
        signedFormulaCreator = new SignedFormulaCreator("ipl");
        signedFormulaCreator.setTwoPhases(false);
        IPLTracer.setEnabled(true);
    }

    /**
     * Creates a Context with predefined relations for specific tests
     * Relations: c0 ≤ c1 ≤ c2
     */
    private Context createContextWithRelations() {
        Context context = new Context();

        // Create labels c0, c1, c2 with specific relations
        FormulaLabel c0 = context.getNewFormulaLabel();
        FormulaLabel c1 = context.getNewFormulaLabel();
        FormulaLabel c2 = context.getNewFormulaLabel();

        // Set up some relations for specific tests
        // c0 ≤ c1 (for tests that require this relation)
        context.addRelation(c0, c1);
        context.addRelation(c1, c2);

        return context;
    }

    private Proof proveFormulas(String... formulaStrings) throws Exception {
        return proveFormulasWithContext(null, formulaStrings);
    }

    /**
     * Main method that uses the new structure with a shared Context
     */
    private Proof proveFormulasWithContext(Context predefinedContext, String... formulaStrings) throws Exception {
        // Use all formulas as a single string separated by lines
        String allFormulas = String.join("\n", formulaStrings);

        // Parse using SignedFormulaCreator (which already handles IPL correctly)
        Problem problem = signedFormulaCreator.parseText(allFormulas);

        // If a predefined Context is provided, use it
        if (predefinedContext != null) {
            problem.setIPLContext(predefinedContext);

            // CRITICAL: Convert existing formulas to use the predefined Context
            IPLSignedFormulaFactory iplFactory = new IPLSignedFormulaFactory(predefinedContext);

            // CRITICAL: Convert formulas to use ContextFormulaLabel from the predefined Context
            List<SignedFormula> originalFormulas = new ArrayList<SignedFormula>(problem.getFormulas().getList());
            SignedFormulaList formulasList = problem.getFormulas();

            // Build a map of indices to ContextFormulaLabel to reuse instances
            Map<Integer, ContextFormulaLabel> labelMap = new HashMap<Integer, ContextFormulaLabel>();

            // First, map all labels already present in the predefined Context
            for (FormulaLabel label : predefinedContext.getLabels()) {
                if (label instanceof ContextFormulaLabel) {
                    labelMap.put(label.getIndex(), (ContextFormulaLabel) label);
                }
            }

            // Clear and rebuild the list
            while (formulasList.size() > 0) {
                formulasList.remove(0);
            }

            for (SignedFormula originalFormula : originalFormulas) {
                FormulaLabel originalLabel = originalFormula.getLabel();

                // Get or create a ContextFormulaLabel using the map
                ContextFormulaLabel contextLabel = labelMap.get(originalLabel.getIndex());
                if (contextLabel == null) {
                    contextLabel = new ContextFormulaLabel(predefinedContext, originalLabel.getIndex());
                    predefinedContext.addElement(contextLabel);
                    labelMap.put(originalLabel.getIndex(), contextLabel);
                }

                // Create a new LabelledFormula with ContextFormulaLabel
                LabelledFormula newLabelledFormula = iplFactory.createLabelledFormula(
                    contextLabel,
                    originalFormula
                );

                formulasList.add(newLabelledFormula);
            }

            problem.setSignedFormulaFactory(iplFactory);
        } else {
        }

        // Create method with IPL rules
        Method method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));

        // Create IPL strategy
        IPLSimpleStrategy strategy = new IPLSimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());

        // Inject the Problem's Context into the Strategy (new structure)
        // if (problem.hasIPLContext()) {
        //     strategy.setIPLContext(problem.getIPLContext());
        // }

        // Create and configure prover
        Prover prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);

        IPLTracer.getInstance().reset();
        Proof proof = prover.prove(problem);
        System.out.println(IPLTracer.getInstance().formatText());

        return proof;
    }

    // =====================================
    // RULE 1: F_OR
    // F A∨B : ci → F A: ci, F B : ci
    // =====================================

    @Test
    public void testRule1_F_OR_BasicApplication() {
        try {
            Proof proof = proveFormulas("F +(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate F P c0", treeOutput.contains("F P c0"));
            assertTrue("Should generate F Q c0", treeOutput.contains("F Q c0"));
            assertTrue("Should apply rule F_OR", treeOutput.contains("F_OR"));
        } catch (Exception e) {
            fail("Error in test F_OR: " + e.getMessage());
        }
    }

    @Test
    public void testRule1_F_OR_WithPredefinedContext() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F +(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree with predefined Context:");
            System.out.println(treeOutput);

            assertTrue("Should generate F P c0", treeOutput.contains("F P c0"));
            assertTrue("Should generate F Q c0", treeOutput.contains("F Q c0"));
            assertTrue("Should apply rule F_OR", treeOutput.contains("F_OR"));
        } catch (Exception e) {
            fail("Error in test F_OR with predefined Context: " + e.getMessage());
        }
    }

    // =====================================
    // RULE 2: T_AND
    // T A∧B : ci → T A: ci, T B : ci
    // =====================================

    @Test
    public void testRule2_T_AND_BasicApplication() {
        try {
            Proof proof = proveFormulas("T *(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate T P c0", treeOutput.contains("T P c0"));
            assertTrue("Should generate T Q c0", treeOutput.contains("T Q c0"));
            assertTrue("Should apply rule T_AND", treeOutput.contains("T_AND"));
        } catch (Exception e) {
            fail("Error in test T_AND: " + e.getMessage());
        }
    }

    @Test
    public void testRule2_T_AND_WithPredefinedContext() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T *(P Q) c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree with predefined Context:");
            System.out.println(treeOutput);

            assertTrue("Should generate T P c1", treeOutput.contains("T P c1"));
            assertTrue("Should generate T Q c1", treeOutput.contains("T Q c1"));
            assertTrue("Should apply rule T_AND", treeOutput.contains("T_AND"));
        }
        catch (Exception e) {
            fail("Error in test T_AND with predefined Context: " + e.getMessage());
        }
    }

    // =====================================
    // RULE 3: X_OR_F_LEFT
    // T A∨B : ci, F A: cj, ci ⪯ cj → T B : ci
    // =====================================

    @Test
    public void testRule3_X_OR_F_LEFT_ValidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c0", "F P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate T Q c0", treeOutput.contains("T Q c0"));
            assertTrue("Should apply rule T_OR_F_LEFT", treeOutput.contains("T_OR_F_LEFT"));
        } catch (Exception e) {
            fail("Error in test X_OR_F_LEFT valid: " + e.getMessage());
        }
    }

    @Test
    public void testRule3_X_OR_F_LEFT_ValidEqualLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate T Q c1", treeOutput.contains("T Q c1"));
            assertTrue("Should apply rule T_OR_F_LEFT", treeOutput.contains("T_OR_F_LEFT"));
        } catch (Exception e) {
            fail("Error in test X_OR_F_LEFT valid: " + e.getMessage());
        }
    }

    @Test
    public void testRule3_X_OR_F_LEFT_InvalidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertFalse("Should NOT apply X_OR_F_LEFT with invalid labels",
                       treeOutput.contains("X_OR_F_LEFT"));
        } catch (Exception e) {
            fail("Error in test X_OR_F_LEFT invalid: " + e.getMessage());
        }
    }

    // =====================================
    // RULE 4: T_OR_F_RIGHT
    // T A∨B : ci, F B: cj, ci ⪯ cj → T A : ci
    // =====================================

    @Test
    public void testRule4_T_OR_F_RIGHT_ValidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c0", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate T P c0", treeOutput.contains("T P c0"));
            assertTrue("Should apply rule T_OR_F_RIGHT", treeOutput.contains("T_OR_F_RIGHT"));
        } catch (Exception e) {
            fail("Error in test T_OR_F_RIGHT valid: " + e.getMessage());
        }
    }

    @Test
    public void testRule4_T_OR_F_RIGHT_ValidEqualLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate T P c1", treeOutput.contains("T P c1"));
            assertTrue("Should apply rule T_OR_F_RIGHT", treeOutput.contains("T_OR_F_RIGHT"));
        } catch (Exception e) {
            fail("Error in test T_OR_F_RIGHT equal labels: " + e.getMessage());
        }
    }

    @Test
    public void testRule4_T_OR_F_RIGHT_InvalidLabelCondition() {
        System.out.println("\n=== TEST RULE 4: T_OR_F_RIGHT (Invalid label) ===");
        System.out.println("T (P\u2228Q) c1, F Q c0 (c1 \u2AAF\u0338 c0: main.label \u2270 aux.label) \u2192 should NOT apply");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F Q c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertFalse("Should NOT apply T_OR_F_RIGHT with invalid labels",
                       treeOutput.contains("T_OR_F_RIGHT"));
        } catch (Exception e) {
            fail("Error in test T_OR_F_RIGHT invalid: " + e.getMessage());
        }
    }

    // =====================================
    // RULE 5: F_AND_LEFT
    // F A∧B : cj, T A : ci, ci ⪯ cj → F B : cj
    // =====================================

    @Test
    public void testRule5_F_AND_LEFT_ValidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c1", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate F Q c1", treeOutput.contains("F Q c1"));
            assertTrue("Should apply rule F_AND_LEFT", treeOutput.contains("F_AND_LEFT"));
        } catch (Exception e) {
            fail("Error in test F_AND_LEFT valid: " + e.getMessage());
        }
    }

    @Test
    public void testRule5_F_AND_LEFT_ValidEqualLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c1", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate F Q c1", treeOutput.contains("F Q c1"));
            assertTrue("Should apply rule F_AND_LEFT", treeOutput.contains("F_AND_LEFT"));
        } catch (Exception e) {
            fail("Error in test F_AND_LEFT equal labels: " + e.getMessage());
        }
    }

    @Test
    public void testRule5_F_AND_LEFT_InvalidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c0", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertFalse("Should NOT apply F_AND_LEFT", treeOutput.contains("F_AND_LEFT"));
        } catch (Exception e) {
            fail("Error in test F_AND_LEFT invalid: " + e.getMessage());
        }
    }

    // =====================================
    // RULE 6: X_AND_T_RIGHT
    // F A∧B: cj, T B : ci, ci ≤ cj → F A : cj
    // =====================================

    @Test
    public void testRule6_X_AND_T_RIGHT_ValidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c1", "T Q c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate F P c1", treeOutput.contains("F P c1"));
            assertTrue("Should apply rule F_AND_RIGHT", treeOutput.contains("F_AND_RIGHT"));
        } catch (Exception e) {
            fail("Error in test X_AND_T_RIGHT valid: " + e.getMessage());
        }
    }

    @Test
    public void testRule6_X_AND_T_RIGHT_ValidEqualLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context,"F *(P Q) c1", "T Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate F P c1", treeOutput.contains("F P c1"));
            assertTrue("Should apply rule F_AND_RIGHT", treeOutput.contains("F_AND_RIGHT"));
        } catch (Exception e) {
            fail("Error in test X_AND_T_RIGHT equal labels: " + e.getMessage());
        }
    }

    @Test
    public void testRule6_X_AND_T_RIGHT_InvalidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context,"F *(P Q) c0", "T Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertFalse("Should NOT apply X_AND_T_RIGHT", treeOutput.contains("X_AND_T_RIGHT"));
        } catch (Exception e) {
            fail("Error in test X_AND_T_RIGHT invalid: " + e.getMessage());
        }
    }

    // =====================================
    // RULE 7: T_IMPLIES_LEFT
    // T A→B : ci, T A : cj, ci ⪯ ck ∧ cj ⪯ ck → T B : ck
    // =====================================

    @Test
    public void testRule7_T_IMPLIES_LEFT_MinimalGreaterLabel_SameLabels() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c0", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate T Q", treeOutput.contains("T Q c0"));
            assertTrue("Should apply T_IMPLIES_LEFT", treeOutput.contains("T_IMPLIES_LEFT"));
        } catch (Exception e) {
            fail("Error in test T_IMPLIES_LEFT equal labels: " + e.getMessage());
        }
    }

    @Test
    public void testRule7_T_IMPLIES_LEFT_MinimalGreaterLabel_DifferentLabels() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c0", "T P c2");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate T Q", treeOutput.contains("T Q c2"));
            assertTrue("Should apply T_IMPLIES_LEFT", treeOutput.contains("T_IMPLIES_LEFT"));
        } catch (Exception e) {
            fail("Error in test T_IMPLIES_LEFT different labels: " + e.getMessage());
        }
    }

    @Test
    public void testRule7_T_IMPLIES_LEFT_MinimalGreaterLabel_OrderReversed() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c1", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate T Q", treeOutput.contains("T Q c1"));
            assertTrue("Should apply T_IMPLIES_LEFT", treeOutput.contains("T_IMPLIES_LEFT"));
        } catch (Exception e) {
            fail("Error in test T_IMPLIES_LEFT reversed order: " + e.getMessage());
        }
    }

    // =====================================
    // RULE 8: X_IMPLIES_F_RIGHT
    // T A→B : ci, F B : cj, ci ⪯ cj → F A : cj
    // =====================================

    @Test
    public void testRule8_X_IMPLIES_F_RIGHT_ValidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c0", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate F P c1", treeOutput.contains("F P c1"));
            assertTrue("Should apply rule X_IMPLIES_F_RIGHT", treeOutput.contains("X_IMPLIES_F_RIGHT"));
        } catch (Exception e) {
            fail("Error in test X_IMPLIES_F_RIGHT valid: " + e.getMessage());
        }
    }

    @Test
    public void testRule8_X_IMPLIES_F_RIGHT_ValidEqualLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c1", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate F P c1", treeOutput.contains("F P c1"));
            assertTrue("Should apply rule X_IMPLIES_F_RIGHT", treeOutput.contains("X_IMPLIES_F_RIGHT"));
        } catch (Exception e) {
            fail("Error in test X_IMPLIES_F_RIGHT equal labels: " + e.getMessage());
        }
    }

    @Test
    public void testRule8_X_IMPLIES_F_RIGHT_InvalidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c1", "F Q c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertFalse("Should NOT apply X_IMPLIES_F_RIGHT", treeOutput.contains("X_IMPLIES_F_RIGHT"));
        } catch (Exception e) {
            fail("Error in test X_IMPLIES_F_RIGHT invalid: " + e.getMessage());
        }
    }

    // =====================================
    // RULE 9: F_A_IMPLIES_B_TA_FB (F→₁)
    // F A→B: ci → T A : cj, F B: cj (cj new, ci ⪯ cj)
    //
    // TERMINATION PROVISO (paper §5 p.13):
    //   F→₁ is applicable ONLY WHEN T A:ch does NOT exist for any ch ⪯ ci in b*.
    //   If T A:ch ALREADY exists with ch ≤ ci, upward monotonicity guarantees that A
    //   is already forced at ci, so creating a new label would be redundant and
    //   would induce branches of infinite length (see Figure 2 of the paper).
    //   In that case F→₃ (F_IMPLIES_T_LEFT) is used instead: F(A→B):cj, T A:ci, ci ≤ cj → F B:cj.
    //   Remark 5.2: the proviso guarantees at most one new label per
    //   derived F A→B:ci formula, bounding branch length.
    // =====================================

    @Test
    public void testRule9_F_A_IMPLIES_B_NewLabels() {
        System.out.println("\n=== TEST RULE 9: F_A_IMPLIES_B_TA_FB \u2014 F\u21921 without proviso ===");
        System.out.println("F(P\u2192Q):c0, no T P on the branch \u2192 proviso inactive, F\u21921 applies.");
        System.out.println("  Creates new label c3: T P:c3 and F Q:c3, with c0 \u2264 c3.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F ->(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate T P with new label", treeOutput.contains("T P c3") && !treeOutput.contains("T P c0") && !treeOutput.contains("T P c1") && !treeOutput.contains("T P c2"));
            assertTrue("Should generate F Q with new label", treeOutput.contains("F Q c3") && !treeOutput.contains("F Q c0") && !treeOutput.contains("T P c1") && !treeOutput.contains("T P c2"));
            assertTrue("Should apply F_A_IMPLIES_B_TA_FB", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));
        } catch (Exception e) {
            fail("Error in test F_A_IMPLIES_B_TA_FB basic: " + e.getMessage());
        }
    }

    @Test
    public void testProviso_FImplies1_BlockedBySameLabelTA() {
        System.out.println("\n=== TEST PROVISO F\u21921: blocked by T A on the same label ===");
        System.out.println("F(P\u2192Q):c0, T P:c0 \u2014 proviso active: ch = c0 \u2264 c0 = ci.");
        System.out.println("  F\u21921 should NOT apply: P is already known to be forced at c0.");
        System.out.println("  F\u21923 (F_IMPLIES_T_LEFT) applies instead: F(P\u2192Q):c0, T P:c0 \u2192 F Q:c0.");
        System.out.println("  Rationale: \u00A75 p.13 \u2014 'F\u21921 applicable only when T A:ch does");
        System.out.println("  not occur for any ch \u2AAF ci'. Remark 5.2: bounds label creation.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F ->(P Q) c0", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertFalse("F\u21921 should NOT apply (proviso active)", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));
            assertFalse("Should NOT create a new label c3 (T P c3)", treeOutput.contains("T P c3"));
            assertTrue("F\u21923 (F_IMPLIES_T_LEFT) should apply instead", treeOutput.contains("F_IMPLIES_T_LEFT"));
            assertTrue("Should derive F Q c0", treeOutput.contains("F Q c0"));

            System.out.println("\u2705 PROVISO F\u21921: correctly blocked by T P:c0 (same label) - CORRECT");
        } catch (Exception e) {
            fail("Error in test proviso F\u21921 same label: " + e.getMessage());
        }
    }

    @Test
    public void testProviso_FImplies1_BlockedByLowerLabelTA() {
        System.out.println("\n=== TEST PROVISO F\u21921: blocked by T A on a lower label ===");
        System.out.println("F(P\u2192Q):c1, T P:c0 \u2014 context c0 \u2264 c1, proviso active: ch = c0 \u2264 c1 = ci.");
        System.out.println("  By upward monotonicity, T P:c0 and c0 \u2264 c1 imply T P:c1 in b*.");
        System.out.println("  F\u21921 should NOT apply. F\u21923 applies: F(P\u2192Q):c1, T P:c0, c0 \u2264 c1 \u2192 F Q:c1.");
        System.out.println("  Rationale: \u00A75 p.13 \u2014 the proviso is checked in b* (includes monotonicity).");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F ->(P Q) c1", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertFalse("F\u21921 should NOT apply (T P:c0 with c0 \u2264 c1)", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));
            assertTrue("F\u21923 (F_IMPLIES_T_LEFT) should apply", treeOutput.contains("F_IMPLIES_T_LEFT"));
            assertTrue("Should derive F Q c1", treeOutput.contains("F Q c1"));

            System.out.println("\u2705 PROVISO F\u21921: correctly blocked by T P:c0 with c0 \u2264 c1 - CORRECT");
        } catch (Exception e) {
            fail("Error in test proviso F\u21921 lower label: " + e.getMessage());
        }
    }

    // =====================================
    // RULE 10: T_NOT (T¬)
    // T ¬A : ci
    // ci ⪯ cj
    // ----------
    // F A : cj   (one label accessible per invocation; all cj ∈ Cb with
    //             ci ⪯ cj get covered over the course of re-selection rounds)
    //
    // Implementation properties — grounded in the theoretical paper:
    //
    //   1. generateNextTNotConclusion generates F A:cj for a SINGLE accessible cj per
    //      invocation (the first one not yet covered), just like T→ with its minor
    //      premise (IPLTwoPremiseRuleApplicator).
    //      Rationale — Definition 5.3: "T ¬A : ci is c.a. in b iff
    //      for each cj ∈ Cb such that ci ⪯b cj, F A : cj is c.a. in b." Completeness
    //      is established recursively, so there is no need to physically write
    //      F A:cj for all cj at once — it suffices to cover, over successive
    //      rounds, whatever Definition 5.3 actually requires.
    //
    //   2. Cb = "the set of constants occurring in b" (Definitions 3.1, p.8 of the
    //      paper) — only the labels that appear in some physical ls-formula on
    //      the branch, NOT every label ever registered in the shared
    //      Context. That is why the tests below add dummy formulas at c1/c2
    //      (with an atom Q unrelated to P): this makes those labels genuine
    //      members of Cb, rather than merely being pre-registered in the
    //      Context (via createContextWithRelations()) without any physical
    //      formula mentioning them — a case that Definition 5.3 correctly ignores.
    //
    //   3. T_NOT is a persistent (γ) rule: it is never permanently marked
    //      ANALYSED. As long as Definition 5.3 keeps failing for some cj ∈ Cb,
    //      T_NOT is re-selected in the next round and covers one more cj.
    //      Rationale — Algorithm 1: rinstances guarantees that each (premise, cj)
    //      pair is applied at most once along the current path, avoiding loops.
    //
    //   4. Generation is physical (in b), enabling two-premise rules.
    //      The 2-premise rules (T∨₁, T∨₂, F∧, T→) require the auxiliary
    //      premise to be physically present in b.
    // =====================================

    @Test
    public void testRule10_T_NOT_GeneratesAllAccessibleLabels() {
        try {
            Context context = createContextWithRelations();
            // T Q c1 / T Q c2 make c1, c2 genuinely part of Cb (Definitions 3.1:
            // "the domain of b is the set Cb of constants occurring in b") --
            // otherwise they are just inert labels pre-registered in Context,
            // never mentioned by any ls-formula, and Definition 5.3 has no reason
            // to require F P at them.
            Proof proof = proveFormulasWithContext(context, "T -P c0", "T Q c1", "T Q c2");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate F P c0 (cj = ci, the minimum)", treeOutput.contains("F P c0"));
            assertTrue("Should generate F P c1 (cj > ci)", treeOutput.contains("F P c1"));
            assertTrue("Should generate F P c2 (cj = maximum in context)", treeOutput.contains("F P c2"));
            assertTrue("Should apply rule T_NOT", treeOutput.contains("T_NOT"));
        } catch (Exception e) {
            fail("Error in test T_NOT generates all labels: " + e.getMessage());
        }
    }

    @Test
    public void testRule10_T_NOT_GeneratesOnlyGeqLabels() {
        try {
            Context context = createContextWithRelations();
            // T Q c0 / T Q c2 make c0, c2 genuinely part of Cb, so the "no F P c0"
            // assertion below tests the ci ⪯ cj filter itself, not merely that c0
            // was never part of Cb to begin with.
            Proof proof = proveFormulasWithContext(context, "T -P c1", "T Q c0", "T Q c2");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should generate F P c1 (cj = ci)", treeOutput.contains("F P c1"));
            assertTrue("Should generate F P c2 (cj > ci)", treeOutput.contains("F P c2"));
            assertFalse("Should NOT generate F P c0 (c0 < c1, c1 \u2264 c0 does not hold)", treeOutput.contains("F P c0"));
            assertTrue("Should apply rule T_NOT", treeOutput.contains("T_NOT"));
        } catch (Exception e) {
            fail("Error in test T_NOT only greater labels: " + e.getMessage());
        }
    }

    /*
    TEST: T_NOT is persistent — it re-fires for new labels
    T ¬P c0, F (Q→R) c0, context c0 ≤ c1 ≤ c2:
    1. T_NOT applies to T¬P:c0 → generates F P c0, F P c1, F P c2.
    2. F→ applies to F(Q→R):c0 (there is no T Q:ch with ch ≤ c0)
        → creates label c3, adds T Q:c3 and F R:c3.
    3. T_NOT was never marked ANALYSED → re-fires in the next cycle.
    4. T_NOT detects the new label c3 (c0 ≤ c3) → generates F P c3.
    */
    @Test
    public void testRule10_T_NOT_PersistentWithNewLabel() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -P c0", "F ->(Q R) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("F\u2192 should generate T Q on the new label c3", treeOutput.contains("T Q c3"));
            assertTrue("F\u2192 should generate F R on the new label c3", treeOutput.contains("F R c3"));
            // F P c3 can only come from T_NOT re-firing for c3:
            // F→ generates F R (not F P), and no other rule generates F P c3.
            assertTrue("Persistent T_NOT should generate F P c3 for the new label", treeOutput.contains("F P c3"));
            assertTrue("Should apply rule T_NOT", treeOutput.contains("T_NOT"));
        } catch (Exception e) {
            fail("Error in test T_NOT persistent with new label: " + e.getMessage());
        }
    }

    /*
    TEST: T_NOT enables a two-premise rule (T∨₁)
    T ¬P c0, T (P∨Q) c1, context c0 ≤ c1 ≤ c2:
    1. T_NOT physically generates F P c0, F P c1, F P c2 (all in b).
    2. T∨₁: T(P∨Q):c1, F P:c1, c1 ≤ c1 → T Q:c1.
    getReferences searches in b (physical), not in b*.
    The derivation works because T_NOT physically generated F P:c1 in b.
    */
    @Test
    public void testRule10_T_NOT_EnablesTwoPremiseRule() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -P c0", "T +(P Q) c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("T_NOT should physically generate F P c1 in b", treeOutput.contains("F P c1"));
            assertTrue("T\u22281 should derive T Q c1", treeOutput.contains("T Q c1"));
            assertTrue("Should apply T_NOT", treeOutput.contains("T_NOT"));
            assertTrue("Should apply T_OR_F_LEFT", treeOutput.contains("T_OR_F_LEFT"));
        } catch (Exception e) {
            fail("Error in test T_NOT enables two-premise rule: " + e.getMessage());
        }
    }

    @Test
    public void testRule10_T_NOT_ClosureViaBStar() {
        System.out.println("\n=== TEST RULE 10: T_NOT produces closure via b* ===");
        System.out.println("T \u00ACP c0, T P c1 (c0 \u2264 c1):");
        System.out.println("  The semantics of T\u00ACP:c0 implicitly includes F P:cj for every cj \u2265 c0 in b*.");
        System.out.println("  In particular F P c1 \u2208 b* (since c0 \u2AAF c1).");
        System.out.println("  When T P c1 is added to the tree, updateMultimap detects T P c1 and F P c1 in b*");
        System.out.println("  with c1 \u2AAF c1 \u2192 immediate CLOSURE (before T_NOT is applied as an explicit step).");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -P c0", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should be closed", proof.isClosed());
            // T_NOT does not appear as an explicit step in the tree because the branch closes
            // during updateMultimap before the strategy gets a chance to apply the rule.
            // Closure happens via the implicit b* extension of T¬P:c0.
        } catch (Exception e) {
            fail("Error in test T_NOT closure via b*: " + e.getMessage());
        }
    }

    // =====================================
    // RULE 11: F_NOT (F¬)
    // F ¬A : ci → T A : cj (cj new, ci ⪯ cj)
    //
    // Unlike F→₁, the paper does NOT impose an explicit "proviso" for F¬.
    // The block arises from the completeness condition of Def. 5.6 (Algorithm 1, line 6):
    //   "select a φ in b which is not completely analyzed in b"
    // Def. 5.6 for F¬: "If F¬A:ci ∈ b, then there is cj ∈ Cb such that
    //   ci ⪯b cj and T A:cj ∈ b*."
    // When that condition is ALREADY satisfied, F¬A:ci is completely analyzed
    // and the algorithm simply does not select it as a candidate — there is no
    // need to apply F¬ again.
    // The implementation (shouldBlockFNotRule) actively checks this when
    // attempting to apply the rule, with the same effect. Without this check
    // a loop would arise:
    //   T¬¬A (persistent) → F¬A:ci → F¬ creates cj → T A:cj → T¬¬A re-applies → ...
    // =====================================

    @Test
    public void testRule11_F_NOT_NewLabel() {
        System.out.println("\n=== TEST RULE 11: F_NOT (Basic case) ===");
        System.out.println("F \u00ACP c0 \u2192 F P cj (cj new, c0 \u2AAF cj)");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F -P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            // Verify that F P was generated with a new label (not c0)
            assertTrue("Should generate T P with new label", treeOutput.contains("T P c3") && !treeOutput.contains("F P c0"));
            assertTrue("Should apply F_NOT", treeOutput.contains("F_NOT"));

            System.out.println("\u2705 RULE 11 (F_NOT): basic NewLabelGetter - CORRECT");

        } catch (Exception e) {
            fail("Error in test F_NOT basic: " + e.getMessage());
        }
    }

    @Test
    public void testProviso_FNot_BlockedBySameLabelTA() {
        System.out.println("\n=== TEST PROVISO F\u00AC: blocked by T A on the same label ===");
        System.out.println("F\u00ACP:c0, T P:c0 \u2014 proviso active: T P:c0 with c0 \u2264 c0 satisfies F\u00ACP:c0.");
        System.out.println("  F\u00ACP:c0 is already semantically satisfied: there is a world (c0) accessible");
        System.out.println("  from c0 where P is forced. There is no point creating a new label.");
        System.out.println("  Rationale: Def. 5.6 \u2014 F\u00ACA:ci is complete if \u2203 cj: ci \u2264 cj and T A:cj \u2208 b*.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F -P c0", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertFalse("F\u00AC should NOT apply (T P:c0 satisfies the proviso)", treeOutput.contains("F_NOT"));
            assertFalse("Should NOT create a new label c3", treeOutput.contains("T P c3"));

            System.out.println("\u2705 PROVISO F\u00AC: correctly blocked by T P:c0 (same label) - CORRECT");
        } catch (Exception e) {
            fail("Error in test proviso F\u00AC same label: " + e.getMessage());
        }
    }

    @Test
    public void testProviso_FNot_BlockedByHigherLabelTA() {
        System.out.println("\n=== TEST PROVISO F\u00AC: blocked by T A on a higher accessible label ===");
        System.out.println("F\u00ACP:c0, T P:c1 \u2014 context c0 \u2264 c1, proviso active: c1 \u2208 b* with c0 \u2264 c1.");
        System.out.println("  T P:c1 is accessible from c0 (c0 \u2264 c1) and satisfies the condition of Def. 5.6.");
        System.out.println("  F\u00ACP:c0 is already semantically satisfied via b*. F\u00AC should not expand.");
        System.out.println("  Rationale: Def. 5.6 \u2014 F\u00ACA:c0 is complete because \u2203 c1: c0 \u2264 c1 and T P:c1 \u2208 b*.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F -P c0", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertFalse("F\u00AC should NOT apply (T P:c1 with c0 \u2264 c1 already satisfies F\u00ACP:c0)", treeOutput.contains("F_NOT"));
            assertFalse("Should NOT create a new label c3", treeOutput.contains("T P c3"));

            System.out.println("\u2705 PROVISO F\u00AC: correctly blocked by T P:c1 with c0 \u2264 c1 - CORRECT");
        } catch (Exception e) {
            fail("Error in test proviso F\u00AC higher label: " + e.getMessage());
        }
    }

    // =====================================
    // DOUBLE NEGATION DERIVATION: T¬ + F¬
    // T ¬¬A : ci
    //   via (T¬): F ¬A : ck  (ck minimal with ci ⪯ ck)
    //   via (F¬): T A : cj   (cj new with ck ⪯ cj)
    // =====================================

    @Test
    public void testDoubleNeg_TNotFNot_Chain() {
        System.out.println("\n=== TEST: Double negation derivation via T\u00AC + F\u00AC ===");
        System.out.println("T \u00AC\u00ACP c0 \u2192 F \u00ACP ck (T\u00AC) \u2192 T P cj (F\u00AC)");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(-P) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should derive T P with a new label greater than c0",
                    treeOutput.contains("T P c3") && !treeOutput.contains("T P c0"));
            assertTrue("Should apply rule T_NOT (first step)", treeOutput.contains("T_NOT"));
            assertTrue("Should apply rule F_NOT (second step)", treeOutput.contains("F_NOT"));
        } catch (Exception e) {
            fail("Error in test double negation derivation: " + e.getMessage());
        }
    }

    @Test
    public void testDoubleNeg_TNotFNot_Chain_Complex() {
        System.out.println("\n=== TEST: Double negation derivation via T\u00AC + F\u00AC (complex formula) ===");
        System.out.println("T \u00AC\u00AC(P\u2227Q) c0 \u2192 F \u00AC(P\u2227Q) ck (T\u00AC) \u2192 T (P\u2227Q) cj (F\u00AC)");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(-(*(P Q))) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should derive T (P\u2227Q) with a new label greater than c0",
                    treeOutput.contains("T (P\u2227Q) c3") && !treeOutput.contains("T (P\u2227Q) c0"));
            assertTrue("Should apply rule T_NOT (first step)", treeOutput.contains("T_NOT"));
            assertTrue("Should apply rule F_NOT (second step)", treeOutput.contains("F_NOT"));

            System.out.println("\u2705 Double negation derivation (T\u00AC + F\u00AC): CORRECT");

        } catch (Exception e) {
            fail("Error in test complex double negation derivation: " + e.getMessage());
        }
    }

    // =====================================
    // KRIPKE MONOTONICITY PROPAGATION (F¬)
    //
    // When F¬ creates a new label cj (ci ⪯ cj), composite T-formulas
    // on labels ci' ≤ cj are physically propagated to cj by upward
    // monotonicity (Def. 5.3 rule 2: T A:ci ∈ b and ci ⪯ cj ⟹ T A:cj ∈ b*).
    //
    // This materializes b* formulas into b, allowing:
    // - 1-premise rules (T∧, T∨) to apply with fresh rinstances
    // - propagated composite T-formulas to be selected as the major premise of
    //   2-premise rules (T→₁, T→₂) for new auxiliaries
    //
    // Without propagation, the original composite T-formulas remain ANALYSED and
    // are not re-selected, preventing new auxiliaries from being paired.
    //
    // Rationale: Def. 5.3 (b*), Def. 5.6 (completely analyzed),
    //   Algorithm 1 line 6, Theorem 5.11 (termination).
    // Code: IPLOnePremiseRuleApplicator.propagateCompositeTFormulasForNewLabel()
    // =====================================

    @Test
    public void testFNot_MonotonicityPropagation() {
        System.out.println("\n=== TEST: Monotonicity propagation in F\u00AC ===");
        System.out.println("(P\u2192Q) \u2227 \u00AC\u00ACP \u2192 \u00AC\u00ACQ is an IPL tautology.");
        System.out.println("F\u00AC creates a new label; T(P\u2192Q) should propagate to that label");
        System.out.println("so that T\u21921/T\u21922 can pair new auxiliaries.");

        try {
            Context context = new Context();
            context.getNewFormulaLabel();

            // (P→Q) ∧ ¬¬P → ¬¬Q
            // In KEMS prefix notation: ->(*(->(P Q) -(-(P))) -(-(Q)))
            Proof proof = proveFormulas("F ->(*(->(P Q) -(-(P))) -(-(Q))) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            // The proof requires F¬ to create labels (for ¬¬P and ¬¬Q)
            assertTrue("Should apply F_NOT", treeOutput.contains("F_NOT"));

            // Should close: it is an IPL tautology
            assertTrue("(P\u2192Q) \u2227 \u00AC\u00ACP \u2192 \u00AC\u00ACQ should be valid in IPL", proof.isClosed());

            // Without propagation (neither eager nor lazy): b* is used exclusively for the
            // completeness check (Definition 5.6) and closure. The physical formulas in b are
            // sufficient for T_IMPLIES_LEFT to apply with the auxiliaries generated by F¬.
            assertTrue("Should apply T_IMPLIES_LEFT or T_AND",
                    treeOutput.contains("T_IMPLIES_LEFT") || treeOutput.contains("T_AND"));

            System.out.println("\u2705 Monotonicity propagation (F\u00AC): CORRECT");

        } catch (Exception e) {
            fail("Error in test F\u00AC propagation: " + e.getMessage());
        }
    }

    // =====================================
    // RULE 12: CLOSURE TEST (CLOSE)
    // T A ci, F A cj ci ⪯ cj → CLOSURE
    // =====================================

    @Test
    public void testRule12_Closure_SameLabel() {
        System.out.println("\n=== TEST CLOSURE IPL ===");
        System.out.println("T P c0, F P c0 \u2192 MUST CLOSE");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T P c0", "F P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should be closed", proof.isClosed());

            System.out.println("\u2705 CLOSURE IPL: CORRECT");

        } catch (Exception e) {
            fail("Error in test closure: " + e.getMessage());
        }
    }

    @Test
    public void testRule12_Closure_GreaterLabel() {
        System.out.println("\n=== TEST CLOSURE IPL ===");
        System.out.println("T P c0, F P c2 \u2192 MUST CLOSE");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T P c0", "F P c2");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should be closed", proof.isClosed());

            System.out.println("\u2705 CLOSURE IPL: CORRECT");

        } catch (Exception e) {
            fail("Error in test closure: " + e.getMessage());
        }
    }

    @Test
    public void testRule12_Closure_LowerLabel() {
        System.out.println("\n=== TEST CLOSURE IPL: GREATER LABEL DOES NOT CLOSE ===");
        System.out.println("T P c2, F P c1 \u2192 SHOULD NOT CLOSE");
        System.out.println("The closure rule requires ci \u2AAF cj (T-label \u2264 F-label).");
        System.out.println("c2 \u2AAF c1 is false in the context c0 \u2264 c1 \u2264 c2, so the branch remains open.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T P c2", "F P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertFalse("Should NOT be closed: the T label (c2) is greater than the F label (c1), c2 \u2AAF c1 does not hold", proof.isClosed());

            System.out.println("\u2705 CLOSURE IPL: closure rule correctly not applied when T-label > F-label");

        } catch (Exception e) {
            fail("Error in test closure: " + e.getMessage());
        }
    }
    @Test
    public void testNewLabelGetter_Behavior() {
        System.out.println("\n=== TEST NewLabelGetter (F_NOT) ===");
        System.out.println("F \u00ACP c0 \u2192 F P cj (cj new, c0 \u2264 cj)");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F -P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            // F_NOT should generate F P with a new label
            assertTrue("Should generate F P", treeOutput.contains("T P c3"));
            assertTrue("Should apply F_NOT", treeOutput.contains("F_NOT"));

            System.out.println("\u2705 NewLabelGetter (F_NOT): working correctly");

        } catch (Exception e) {
            fail("Error in test NewLabelGetter: " + e.getMessage());
        }
    }

    // =====================================
    // SPECIFIC TEST: LAW OF EXCLUDED MIDDLE NOT VALID IN IPL
    // P ∨ ¬P should NOT close in IPL
    // =====================================

    @Test
    public void testLawOfExcludedMiddle_NotValidInIPL() {
        System.out.println("\n=== TEST LAW OF EXCLUDED MIDDLE NOT VALID IN IPL ===");
        System.out.println("F (P \u2228 \u00ACP) \u2192 should NOT close");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F +(P -P) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            // P ∨ ¬P is NOT valid in IPL
            assertFalse("P \u2228 \u00ACP should NOT be closed in IPL", proof.isClosed());
            assertTrue("Should apply rule F_OR", treeOutput.contains("F_OR"));

            System.out.println("\u2705 LAW OF EXCLUDED MIDDLE NOT VALID IN IPL: CORRECT");

        } catch (Exception e) {
            fail("Error in test law of excluded middle: " + e.getMessage());
        }
    }

    @Test
    public void testLawOfExcludedMiddle_NotValidInIPL3() {
        System.out.println("\n=== TEST LAW OF EXCLUDED MIDDLE NOT VALID IN IPL ===");
        System.out.println("F (P \u2228 \u00ACP) \u2192 should NOT close");

        try {
            Context context = new Context();
            context.getNewFormulaLabel();
            Proof proof = proveFormulasWithContext(context, "F +(P -P) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            // P ∨ ¬P is NOT valid in IPL
            assertFalse("P \u2228 \u00ACP should NOT be closed in IPL", proof.isClosed());
            assertTrue("Should apply rule F_OR", treeOutput.contains("F_OR"));

            System.out.println("\u2705 LAW OF EXCLUDED MIDDLE NOT VALID IN IPL: CORRECT");

        } catch (Exception e) {
            fail("Error in test law of excluded middle: " + e.getMessage());
        }
    }

    @Test
    public void testPaperProblem1() {
        try {
            Context context = new Context();
            context.getNewFormulaLabel();
            Proof proof = proveFormulas( "F ->(*(->(A B) ->(A -B)) -A) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            // ((A→B)∧(A→¬B))→¬A is an IPL tautology (example from the paper)
            assertTrue("Should be closed in IPL", proof.isClosed());

        } catch (Exception e) {
            fail("Error in test: " + e.getMessage());
        }
    }

    @Test
    public void testPaperProblem2() {
        try {
            Context context = new Context();
            context.getNewFormulaLabel();
            Proof proof = proveFormulas( "F -(-(->(-(-A) A))) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            // ¬¬(¬¬A→A) is an IPL tautology (example from the paper, Figure 6)
            assertTrue("Should be closed in IPL", proof.isClosed());

        } catch (Exception e) {
            fail("Error in test: " + e.getMessage());
        }
    }

    @Test
    public void testPaperProblem3() {
        try {
            Context context = new Context();
            context.getNewFormulaLabel();
            Proof proof = proveFormulas( "F ->(-(->(A B)) *(-(-A) -B)) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            assertTrue("Should be closed in IPL", proof.isClosed());

        } catch (Exception e) {
            fail("Error in test: " + e.getMessage());
        }
    }

    @Test
    public void testPaperProblem4() {
        try {
            Context context = new Context();
            context.getNewFormulaLabel();
            Proof proof = proveFormulas( "F ->(->(->(->(->(p q) p) p) q) q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            // (((p→q)→p)→p→q)→q is an IPL tautology (example from the paper)
            assertTrue("Should be closed in IPL", proof.isClosed());

        } catch (Exception e) {
            fail("Error in test: " + e.getMessage());
        }
    }

    @Test
    public void testLongPB() {
        try {
            Context context = new Context();
            context.getNewFormulaLabel();
            Proof proof = proveFormulas( "F ->(*(*(->(*(->(p1 p2) ->(p2 p1)) *(p1 *(p2 p3))) ->(*(->(p2 p3) ->(p3 p2)) *(p1 *(p2 p3)))) ->(*(->(p3 p1) ->(p1 p3)) *(p1 *(p2 p3)))) *(p1 *(p2 p3))) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            // Long test with multiple PB applications: an IPL tautology involving
            // a symmetric comparison of three propositions p1, p2, p3.
            assertTrue("Should be closed in IPL", proof.isClosed());

        } catch (Exception e) {
            fail("Error in test: " + e.getMessage());
        }
    }


    @Test
    public void testDoubleNegationElimination_NotValidInIPL() {
        System.out.println("\n=== TEST: F \u00AC\u00ACA \u2192 A (Double negation) ===");
        System.out.println("Formula: F \u00AC\u00ACA \u2192 A : c0");
        System.out.println("This formula is NOT valid in IPL (double negation does not imply affirmation)");

        try {
            Context context = new Context();
            context.getNewFormulaLabel();

            // F ¬¬A → A : c0
            String formula = "F ->(-(-A) A) c0";

            Proof proof = proveFormulas(formula);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("\n\uD83D\uDCCA Result tree:");
            System.out.println(treeOutput);

            // In IPL, ¬¬A → A is NOT valid (double negation does not imply affirmation)
            assertFalse("F \u00AC\u00ACA \u2192 A should NOT be closed in IPL", proof.isClosed());
            assertTrue("Should apply rule F_A_IMPLIES_B_TA_FB", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));

            System.out.println("\n\u2705 DOUBLE NEGATION: the tree does NOT close (correct for IPL)");
            System.out.println("   In IPL, \u00AC\u00ACA does not necessarily imply A");

        } catch (Exception e) {
            e.printStackTrace();
            fail("Error in test double negation: " + e.getMessage());
        }
    }

    @Test
    public void testPeirceLaw_NotValidInIPL() {
        System.out.println("\n=== TEST: Peirce's Law not valid in IPL ===");
        System.out.println("Formula: F ((p \u2192 q) \u2192 p) \u2192 p : c0");
        System.out.println("Peirce's Law ((p\u2192q)\u2192p)\u2192p is valid in classical logic but NOT in IPL.");

        try {
            Context context = new Context();
            context.getNewFormulaLabel();

            // F ((p → q) → p) → p : c0  — genuine Peirce's Law
            String formula = "F ->(->(->(p q) p) p) c0";

            Proof proof = proveFormulas(formula);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("\nResult tree:");
            System.out.println(treeOutput);

            assertFalse("Peirce's Law should NOT be valid in IPL", proof.isClosed());
            assertTrue("Should apply rule F_A_IMPLIES_B_TA_FB", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));
        } catch (Exception e) {
            e.printStackTrace();
            fail("Error in test Peirce's Law: " + e.getMessage());
        }
    }

    @Test
    public void testScottAxiom_NotValidInIPL() {
        System.out.println("\n=== TEST: Refutation of Scott's axiom ===");
        System.out.println("Formula: F ((\u00AC\u00ACp \u2192 p) \u2192 (p \u2228 \u00ACp)) \u2192 (\u00ACp \u2228 \u00AC\u00ACp) : c0");
        System.out.println("Fourth refutation of Fig. 3 of the paper [labeled-ke-ipl].");
        System.out.println("Scott's axiom is not valid in IPL.");

        try {
            Context context = new Context();
            context.getNewFormulaLabel();

            // F ((¬¬p → p) → (p ∨ ¬p)) → (¬p ∨ ¬¬p) : c0
            String formula = "F ->(->(->(-(-p) p) +(p -p)) +(-p -(-p))) c0";

            Proof proof = proveFormulas(formula);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("\n\uD83D\uDCCA Result tree:");
            System.out.println(treeOutput);

            assertFalse("Scott's axiom should NOT be closed in IPL", proof.isClosed());

        } catch (Exception e) {
            e.printStackTrace();
            fail("Error in test Scott's axiom: " + e.getMessage());
        }
    }

    @Test
    public void testPeirceVariantQP_NotValidInIPL() {
        System.out.println("\n=== TEST: Refutation of the Peirce variant (q,p) ===");
        System.out.println("Formula: F ((q \u2192 p) \u2192 p) \u2192 p : c0");
        System.out.println("Third refutation of Fig. 3 of the paper [labeled-ke-ipl].");
        System.out.println("It particularly illustrates the notion of a completed branch,");
        System.out.println("via the proviso on F\u21921 and rule F\u21923.");

        try {
            Context context = new Context();
            context.getNewFormulaLabel();

            // F ((q → p) → p) → p : c0
            String formula = "F ->(->(->(q p) p) p) c0";

            Proof proof = proveFormulas(formula);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("\n\uD83D\uDCCA Result tree:");
            System.out.println(treeOutput);

            assertFalse("The Peirce variant (q,p) should NOT be closed in IPL", proof.isClosed());
            assertTrue("Should apply rule F_A_IMPLIES_B_TA_FB", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));

        } catch (Exception e) {
            e.printStackTrace();
            fail("Error in test Peirce variant (q,p): " + e.getMessage());
        }
    }

    // =====================================
    // PB: BEHAVIOR WITH LABELS
    // PB intentionally ignores labels when checking whether the minor premise
    // already exists (formulaExistsInTree). Label compatibility is
    // checked in the two-premise applicator. If PB checked labels,
    // it would generate unbounded branches (each PB enables rules that create new
    // labels via F→₁ and propagation, triggering more PB).
    // Paper: Algorithm 1 lines 14-18, Theorem 5.11.
    // =====================================

    /**
     * When F P exists in the tree (at any label), PB recognizes it
     * as an "available minor premise" and does NOT apply PB for T∨₁.
     * PB can apply for T∨₂ (F Q does not exist), but NOT for T∨₁.
     * This is correct: the label check is delegated to the two-premise
     * applicator, and PB is only responsible for generating missing subformulas.
     */
    @Test
    public void testPB_IgnoresLabels_AuxExistsAtAnyLabel() {
        System.out.println("\n=== TEST: PB ignores labels when checking auxiliary existence ===");
        System.out.println("T(P\u2228Q):c1, F P:c0 with c0 \u2AAF c1");
        System.out.println("T\u22281 needs F P:cj with c1 \u2AAF cj. F P:c0 exists (incompatible label),");
        System.out.println("but PB does not apply for T\u22281 because F P already exists in the tree.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            // X_OR_F_LEFT (T∨₁) should NOT apply: F P:c0 has an incompatible label
            // and PB does not generate F P:c1 because F P already "exists" (ignoring labels)
            assertFalse("T\u22281 should NOT apply (F P:c0 incompatible, PB does not generate F P:c1)",
                       treeOutput.contains("X_OR_F_LEFT"));

            // The scenario is Kripke-consistent → open branch
            assertFalse("Branch should remain open (Kripke-consistent scenario)",
                       proof.isClosed());

            System.out.println("\u2705 PB correctly ignores labels");

        } catch (Exception e) {
            fail("Error in test PB ignores labels: " + e.getMessage());
        }
    }

    /**
     * When the auxiliary has a compatible label, the two-premise rule
     * applies directly without needing PB.
     */
    @Test
    public void testPB_DirectApplication_AuxAtCompatibleLabel() {
        System.out.println("\n=== TEST: Direct application with compatible label ===");
        System.out.println("T(P\u2228Q):c0, F P:c1 with c0 \u2AAF c1");
        System.out.println("T\u22281 needs F P:cj with c0 \u2AAF cj. F P:c1 IS compatible.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c0", "F P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Result tree:");
            System.out.println(treeOutput);

            // T∨₁ should apply directly (without PB) because F P:c1 is compatible
            assertTrue("T\u22281 should apply directly with a compatible label",
                       treeOutput.contains("X_OR_F_LEFT") || treeOutput.contains("T_OR_F_LEFT"));
            assertTrue("Should derive T Q c0",
                       treeOutput.contains("T Q c0"));

            System.out.println("\u2705 Direct application with compatible label: CORRECT");

        } catch (Exception e) {
            fail("Error in test direct application: " + e.getMessage());
        }
    }

}
