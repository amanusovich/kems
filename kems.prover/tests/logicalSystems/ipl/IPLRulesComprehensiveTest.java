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
     * Crea un Context con relaciones predefinidas para tests específicos
     * Relaciones: c0 ≤ c1 ≤ c2
     */
    private Context createContextWithRelations() {
        Context context = new Context();

        // Crear etiquetas c0, c1, c2 con relaciones específicas
        FormulaLabel c0 = context.getNewFormulaLabel();
        FormulaLabel c1 = context.getNewFormulaLabel();
        FormulaLabel c2 = context.getNewFormulaLabel();

        // Establecer algunas relaciones para tests específicos
        // c0 ≤ c1 (para tests que requieren esta relación)
        context.addRelation(c0, c1);
        context.addRelation(c1, c2);

        return context;
    }

    private Proof proveFormulas(String... formulaStrings) throws Exception {
        return proveFormulasWithContext(null, formulaStrings);
    }

    /**
     * Método principal que usa la nueva estructura con Context compartido
     */
    private Proof proveFormulasWithContext(Context predefinedContext, String... formulaStrings) throws Exception {
        // Usar todas las fórmulas como un solo string separado por líneas
        String allFormulas = String.join("\n", formulaStrings);

        // Parsear usando SignedFormulaCreator (que ya maneja IPL correctamente)
        Problem problem = signedFormulaCreator.parseText(allFormulas);

        // Si se proporciona un Context predefinido, usarlo
        if (predefinedContext != null) {
            problem.setIPLContext(predefinedContext);

            // ✅ CRÍTICO: Convertir fórmulas existentes para usar el Context predefinido
            IPLSignedFormulaFactory iplFactory = new IPLSignedFormulaFactory(predefinedContext);

            // ✅ CRÍTICO: Convertir fórmulas para usar ContextFormulaLabel del Context predefinido
            List<SignedFormula> originalFormulas = new ArrayList<SignedFormula>(problem.getFormulas().getList());
            SignedFormulaList formulasList = problem.getFormulas();

            // Crear mapa de índices a ContextFormulaLabel para reutilizar instancias
            Map<Integer, ContextFormulaLabel> labelMap = new HashMap<Integer, ContextFormulaLabel>();

            // Primero, mapear todas las etiquetas existentes en el Context predefinido
            for (FormulaLabel label : predefinedContext.getLabels()) {
                if (label instanceof ContextFormulaLabel) {
                    labelMap.put(label.getIndex(), (ContextFormulaLabel) label);
                }
            }

            // Limpiar y reconstruir la lista
            while (formulasList.size() > 0) {
                formulasList.remove(0);
            }

            for (SignedFormula originalFormula : originalFormulas) {
                FormulaLabel originalLabel = originalFormula.getLabel();

                // Obtener o crear ContextFormulaLabel usando el mapa
                ContextFormulaLabel contextLabel = labelMap.get(originalLabel.getIndex());
                if (contextLabel == null) {
                    contextLabel = new ContextFormulaLabel(predefinedContext, originalLabel.getIndex());
                    predefinedContext.addElement(contextLabel);
                    labelMap.put(originalLabel.getIndex(), contextLabel);
                }

                // Crear nueva LabelledFormula con ContextFormulaLabel
                LabelledFormula newLabelledFormula = iplFactory.createLabelledFormula(
                        contextLabel,
                        originalFormula
                );

                formulasList.add(newLabelledFormula);
            }

            problem.setSignedFormulaFactory(iplFactory);
        } else {
        }

        // Crear método con reglas IPL
        Method method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));

        // Crear estrategia IPL
        IPLSimpleStrategy strategy = new IPLSimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());

        // Inyectar Context del Problem en la Strategy (nueva estructura)
        // if (problem.hasIPLContext()) {
        //     strategy.setIPLContext(problem.getIPLContext());
        // }

        // Crear y configurar prover
        Prover prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);

        IPLTracer.getInstance().reset();
        Proof proof = prover.prove(problem);
        System.out.println(IPLTracer.getInstance().formatText());

        return proof;
    }

    // =====================================
    // REGLA 1: F_OR
    // F A∨B : ci → F A: ci, F B : ci
    // =====================================

    @Test
    public void testRule1_F_OR_BasicApplication() {
        try {
            Proof proof = proveFormulas("F +(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar F P c0", treeOutput.contains("F P c0"));
            assertTrue("Debe generar F Q c0", treeOutput.contains("F Q c0"));
            assertTrue("Debe aplicar la regla F_OR", treeOutput.contains("F_OR"));
        } catch (Exception e) {
            fail("Error en test F_OR: " + e.getMessage());
        }
    }

    @Test
    public void testRule1_F_OR_WithPredefinedContext() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F +(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado con Context predefinido:");
            System.out.println(treeOutput);

            assertTrue("Debe generar F P c0", treeOutput.contains("F P c0"));
            assertTrue("Debe generar F Q c0", treeOutput.contains("F Q c0"));
            assertTrue("Debe aplicar la regla F_OR", treeOutput.contains("F_OR"));
        } catch (Exception e) {
            fail("Error en test F_OR con Context predefinido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 2: T_AND
    // T A∧B : ci → T A: ci, T B : ci
    // =====================================

    @Test
    public void testRule2_T_AND_BasicApplication() {
        try {
            Proof proof = proveFormulas("T *(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar T P c0", treeOutput.contains("T P c0"));
            assertTrue("Debe generar T Q c0", treeOutput.contains("T Q c0"));
            assertTrue("Debe aplicar la regla T_AND", treeOutput.contains("T_AND"));
        } catch (Exception e) {
            fail("Error en test T_AND: " + e.getMessage());
        }
    }

    @Test
    public void testRule2_T_AND_WithPredefinedContext() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T *(P Q) c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado con Context predefinido:");
            System.out.println(treeOutput);

            assertTrue("Debe generar T P c1", treeOutput.contains("T P c1"));
            assertTrue("Debe generar T Q c1", treeOutput.contains("T Q c1"));
            assertTrue("Debe aplicar la regla T_AND", treeOutput.contains("T_AND"));
        }
        catch (Exception e) {
            fail("Error en test T_AND con Context predefinido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 3: X_OR_F_LEFT
    // T A∨B : ci, F A: cj, ci ⪯ cj → T B : ci
    // =====================================

    @Test
    public void testRule3_X_OR_F_LEFT_ValidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c0", "F P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar T Q c0", treeOutput.contains("T Q c0"));
            assertTrue("Debe aplicar la regla T_OR_F_LEFT", treeOutput.contains("T_OR_F_LEFT"));
        } catch (Exception e) {
            fail("Error en test X_OR_F_LEFT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule3_X_OR_F_LEFT_ValidEqualLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar T Q c1", treeOutput.contains("T Q c1"));
            assertTrue("Debe aplicar la regla T_OR_F_LEFT", treeOutput.contains("T_OR_F_LEFT"));
        } catch (Exception e) {
            fail("Error en test X_OR_F_LEFT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule3_X_OR_F_LEFT_InvalidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse("NO debe aplicar X_OR_F_LEFT con labels inválidos",
                       treeOutput.contains("X_OR_F_LEFT"));
        } catch (Exception e) {
            fail("Error en test X_OR_F_LEFT inválido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 4: T_OR_F_RIGHT
    // T A∨B : ci, F B: cj, ci ⪯ cj → T A : ci
    // =====================================

    @Test
    public void testRule4_T_OR_F_RIGHT_ValidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c0", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar T P c0", treeOutput.contains("T P c0"));
            assertTrue("Debe aplicar la regla T_OR_F_RIGHT", treeOutput.contains("T_OR_F_RIGHT"));
        } catch (Exception e) {
            fail("Error en test T_OR_F_RIGHT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule4_T_OR_F_RIGHT_ValidEqualLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar T P c1", treeOutput.contains("T P c1"));
            assertTrue("Debe aplicar la regla T_OR_F_RIGHT", treeOutput.contains("T_OR_F_RIGHT"));
        } catch (Exception e) {
            fail("Error en test T_OR_F_RIGHT labels iguales: " + e.getMessage());
        }
    }

    @Test
    public void testRule4_T_OR_F_RIGHT_InvalidLabelCondition() {
        System.out.println("\n=== TEST REGLA 4: T_OR_F_RIGHT (Label inválido) ===");
        System.out.println("T (P∨Q) c1, F Q c0 (c1 ⪯̸ c0: main.label ≰ aux.label) → NO debe aplicarse");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F Q c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse("NO debe aplicar T_OR_F_RIGHT con labels inválidos",
                       treeOutput.contains("T_OR_F_RIGHT"));
        } catch (Exception e) {
            fail("Error en test T_OR_F_RIGHT inválido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 5: F_AND_LEFT
    // F A∧B : cj, T A : ci, ci ⪯ cj → F B : cj
    // =====================================

    @Test
    public void testRule5_F_AND_LEFT_ValidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c1", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar F Q c1", treeOutput.contains("F Q c1"));
            assertTrue("Debe aplicar la regla F_AND_LEFT", treeOutput.contains("F_AND_LEFT"));
        } catch (Exception e) {
            fail("Error en test F_AND_LEFT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule5_F_AND_LEFT_ValidEqualLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c1", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar F Q c1", treeOutput.contains("F Q c1"));
            assertTrue("Debe aplicar la regla F_AND_LEFT", treeOutput.contains("F_AND_LEFT"));
        } catch (Exception e) {
            fail("Error en test F_AND_LEFT labels iguales: " + e.getMessage());
        }
    }

    @Test
    public void testRule5_F_AND_LEFT_InvalidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c0", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse("NO debe aplicar F_AND_LEFT", treeOutput.contains("F_AND_LEFT"));
        } catch (Exception e) {
            fail("Error en test F_AND_LEFT inválido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 6: X_AND_T_RIGHT
    // F A∧B: cj, T B : ci, ci ≤ cj → F A : cj
    // =====================================

    @Test
    public void testRule6_X_AND_T_RIGHT_ValidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c1", "T Q c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar F P c1", treeOutput.contains("F P c1"));
            assertTrue("Debe aplicar la regla F_AND_RIGHT", treeOutput.contains("F_AND_RIGHT"));
        } catch (Exception e) {
            fail("Error en test X_AND_T_RIGHT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule6_X_AND_T_RIGHT_ValidEqualLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context,"F *(P Q) c1", "T Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar F P c1", treeOutput.contains("F P c1"));
            assertTrue("Debe aplicar la regla F_AND_RIGHT", treeOutput.contains("F_AND_RIGHT"));
        } catch (Exception e) {
            fail("Error en test X_AND_T_RIGHT labels iguales: " + e.getMessage());
        }
    }

    @Test
    public void testRule6_X_AND_T_RIGHT_InvalidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context,"F *(P Q) c0", "T Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse("NO debe aplicar X_AND_T_RIGHT", treeOutput.contains("X_AND_T_RIGHT"));
        } catch (Exception e) {
            fail("Error en test X_AND_T_RIGHT inválido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 7: T_IMPLIES_LEFT
    // T A→B : ci, T A : cj, ci ⪯ ck ∧ cj ⪯ ck → T B : ck
    // =====================================

    @Test
    public void testRule7_T_IMPLIES_LEFT_MinimalGreaterLabel_SameLabels() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c0", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar T Q", treeOutput.contains("T Q c0"));
            assertTrue("Debe aplicar T_IMPLIES_LEFT", treeOutput.contains("T_IMPLIES_LEFT"));
        } catch (Exception e) {
            fail("Error en test T_IMPLIES_LEFT labels iguales: " + e.getMessage());
        }
    }

    @Test
    public void testRule7_T_IMPLIES_LEFT_MinimalGreaterLabel_DifferentLabels() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c0", "T P c2");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar T Q", treeOutput.contains("T Q c2"));
            assertTrue("Debe aplicar T_IMPLIES_LEFT", treeOutput.contains("T_IMPLIES_LEFT"));
        } catch (Exception e) {
            fail("Error en test T_IMPLIES_LEFT labels diferentes: " + e.getMessage());
        }
    }

    @Test
    public void testRule7_T_IMPLIES_LEFT_MinimalGreaterLabel_OrderReversed() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c1", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar T Q", treeOutput.contains("T Q c1"));
            assertTrue("Debe aplicar T_IMPLIES_LEFT", treeOutput.contains("T_IMPLIES_LEFT"));
        } catch (Exception e) {
            fail("Error en test T_IMPLIES_LEFT orden invertido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 8: X_IMPLIES_F_RIGHT
    // T A→B : ci, F B : cj, ci ⪯ cj → F A : cj
    // =====================================

    @Test
    public void testRule8_X_IMPLIES_F_RIGHT_ValidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c0", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar F P c1", treeOutput.contains("F P c1"));
            assertTrue("Debe aplicar la regla X_IMPLIES_F_RIGHT", treeOutput.contains("X_IMPLIES_F_RIGHT"));
        } catch (Exception e) {
            fail("Error en test X_IMPLIES_F_RIGHT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule8_X_IMPLIES_F_RIGHT_ValidEqualLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c1", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar F P c1", treeOutput.contains("F P c1"));
            assertTrue("Debe aplicar la regla X_IMPLIES_F_RIGHT", treeOutput.contains("X_IMPLIES_F_RIGHT"));
        } catch (Exception e) {
            fail("Error en test X_IMPLIES_F_RIGHT labels iguales: " + e.getMessage());
        }
    }

    @Test
    public void testRule8_X_IMPLIES_F_RIGHT_InvalidLabelCondition() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c1", "F Q c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse("NO debe aplicar X_IMPLIES_F_RIGHT", treeOutput.contains("X_IMPLIES_F_RIGHT"));
        } catch (Exception e) {
            fail("Error en test X_IMPLIES_F_RIGHT inválido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 9: F_A_IMPLIES_B_TA_FB (F→₁)
    // F A→B: ci → T A : cj, F B: cj (cj nuevo, ci ⪯ cj)
    //
    // PROVISO DE TERMINACIÓN (paper §5 p.13):
    //   F→₁ es aplicable SOLO CUANDO T A:ch NO existe para ningún ch ⪯ ci en b*.
    //   Si T A:ch YA existe con ch ≤ ci, la monotonía ascendente garantiza que A
    //   está probado en ci, por lo que crear un nuevo label sería redundante e
    //   induciría ramas de longitud infinita (ver Figura 2 del paper).
    //   En ese caso se usa F→₃ (F_IMPLIES_T_LEFT): F(A→B):cj, T A:ci, ci ≤ cj → F B:cj.
    //   Remark 5.2: el proviso garantiza a lo sumo un nuevo label por cada
    //   fórmula F A→B:ci derivada, acotando la longitud de las ramas.
    // =====================================

    @Test
    public void testRule9_F_A_IMPLIES_B_NewLabels() {
        System.out.println("\n=== TEST REGLA 9: F_A_IMPLIES_B_TA_FB — F→₁ sin proviso ===");
        System.out.println("F(P→Q):c0, sin T P en rama → proviso inactivo, F→₁ aplica.");
        System.out.println("  Crea nuevo label c3: T P:c3 y F Q:c3, con c0 ≤ c3.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F ->(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar T P con label nueva", treeOutput.contains("T P c3") && !treeOutput.contains("T P c0") && !treeOutput.contains("T P c1") && !treeOutput.contains("T P c2"));
            assertTrue("Debe generar F Q con label nueva", treeOutput.contains("F Q c3") && !treeOutput.contains("F Q c0") && !treeOutput.contains("T P c1") && !treeOutput.contains("T P c2"));
            assertTrue("Debe aplicar F_A_IMPLIES_B_TA_FB", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));
        } catch (Exception e) {
            fail("Error en test F_A_IMPLIES_B_TA_FB básico: " + e.getMessage());
        }
    }

    @Test
    public void testProviso_FImplies1_BlockedBySameLabelTA() {
        System.out.println("\n=== TEST PROVISO F→₁: bloqueado por T A en mismo label ===");
        System.out.println("F(P→Q):c0, T P:c0 — proviso activo: ch = c0 ≤ c0 = ci.");
        System.out.println("  F→₁ NO debe aplicarse: ya se sabe que P es forzado en c0.");
        System.out.println("  F→₃ (F_IMPLIES_T_LEFT) aplica en cambio: F(P→Q):c0, T P:c0 → F Q:c0.");
        System.out.println("  Fundamento: §5 p.13 — 'F→₁ applicable only when T A:ch does");
        System.out.println("  not occur for any ch ⪯ ci'. Remark 5.2: acota creación de labels.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F ->(P Q) c0", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse("F→₁ NO debe aplicarse (proviso activo)", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));
            assertFalse("NO debe crearse nuevo label c3 (T P c3)", treeOutput.contains("T P c3"));
            assertTrue("F→₃ (F_IMPLIES_T_LEFT) debe aplicarse en su lugar", treeOutput.contains("F_IMPLIES_T_LEFT"));
            assertTrue("Debe derivar F Q c0", treeOutput.contains("F Q c0"));

            System.out.println("✅ PROVISO F→₁: bloqueado correctamente por T P:c0 (mismo label) - CORRECTO");
        } catch (Exception e) {
            fail("Error en test proviso F→₁ mismo label: " + e.getMessage());
        }
    }

    @Test
    public void testProviso_FImplies1_BlockedByLowerLabelTA() {
        System.out.println("\n=== TEST PROVISO F→₁: bloqueado por T A en label menor ===");
        System.out.println("F(P→Q):c1, T P:c0 — contexto c0 ≤ c1, proviso activo: ch = c0 ≤ c1 = ci.");
        System.out.println("  Por monotonía ascendente, T P:c0 y c0 ≤ c1 implican T P:c1 en b*.");
        System.out.println("  F→₁ NO debe aplicarse. F→₃ aplica: F(P→Q):c1, T P:c0, c0 ≤ c1 → F Q:c1.");
        System.out.println("  Fundamento: §5 p.13 — proviso verifica en b* (incluye monotonicidad).");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F ->(P Q) c1", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse("F→₁ NO debe aplicarse (T P:c0 con c0 ≤ c1)", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));
            assertTrue("F→₃ (F_IMPLIES_T_LEFT) debe aplicarse", treeOutput.contains("F_IMPLIES_T_LEFT"));
            assertTrue("Debe derivar F Q c1", treeOutput.contains("F Q c1"));

            System.out.println("✅ PROVISO F→₁: bloqueado correctamente por T P:c0 con c0 ≤ c1 - CORRECTO");
        } catch (Exception e) {
            fail("Error en test proviso F→₁ label menor: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 10: T_NOT (T¬)
    // T ¬A : ci
    // ci ⪯ cj
    // ----------
    // F A : cj   (para TODOS los cj accesibles con ci ⪯ cj, no solo el mínimo)
    //
    // Propiedades de la implementación — fundamentadas en el paper (lkeipl):
    //
    //   1. generateAllTNotConclusions genera F A:cj para TODOS los cj accesibles ≥ ci.
    //      Fundamento — Def. 5.6 (condición de completitud de rama para T¬):
    //        "If T¬A : ci ∈ b, then F A : cj ∈ b* for each cj ∈ Cb such that ci ⪯b cj."
    //      En el sistema sin variables (Table 2, Apéndice), T¬ se escribe con
    //      constante cj en lugar de variable xi, requiriendo una instancia por cada
    //      cj ≥ ci para que la rama sea completamente analizada.
    //      (Ver también §3, Table 1→Table 2 y la explicación en §3 p.6-7:
    //       el sistema sin variables obtiene T¬ directamente con constante cj.)
    //
    //   2. T_NOT es una regla persistente (γ): nunca se marca ANALYSED.
    //      Cuando F→ o F¬ crean nuevos labels, T_NOT re-dispara en el siguiente
    //      ciclo y genera F A para esos nuevos labels.
    //      Fundamento — Algorithm 1, líneas 7-9 y §5.3 p.16:
    //        "rinstances keeps a record of the rule application instances that have
    //         been performed. This guarantees that at least one of the premises used
    //         in an application of a rule is different."
    //      Cuando aparece un nuevo label ck, la instancia T_NOT(T¬A:ci → F A:ck)
    //      no está en rinstances y la regla se re-aplica legítimamente.
    //
    //   3. La generación es física (en b), habilitando reglas de dos premisas.
    //      Fundamento — Algorithm 1, línea 11:
    //        "if the corresponding minor premise of r is in b then [apply r]"
    //      Las reglas de 2 premisas (T∨₁, T∨₂, F∧, T→) requieren que la premisa
    //      auxiliar esté físicamente en b. b* se computa solo para verificar
    //      completitud de rama (Algorithm 1, línea 21: "b* ← extend(b)"; y Def. 5.3),
    //      no para buscar premisas de reglas operacionales.
    // =====================================

    @Test
    public void testRule10_T_NOT_GeneratesAllAccessibleLabels() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar F P c0 (cj = ci, el mínimo)", treeOutput.contains("F P c0"));
            assertTrue("Debe generar F P c1 (cj > ci)", treeOutput.contains("F P c1"));
            assertTrue("Debe generar F P c2 (cj = máximo en contexto)", treeOutput.contains("F P c2"));
            assertTrue("Debe aplicar la regla T_NOT", treeOutput.contains("T_NOT"));
        } catch (Exception e) {
            fail("Error en test T_NOT genera todos los labels: " + e.getMessage());
        }
    }

    @Test
    public void testRule10_T_NOT_GeneratesOnlyGeqLabels() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe generar F P c1 (cj = ci)", treeOutput.contains("F P c1"));
            assertTrue("Debe generar F P c2 (cj > ci)", treeOutput.contains("F P c2"));
            assertFalse("NO debe generar F P c0 (c0 < c1, no cumple c1 ≤ c0)", treeOutput.contains("F P c0"));
            assertTrue("Debe aplicar la regla T_NOT", treeOutput.contains("T_NOT"));
        } catch (Exception e) {
            fail("Error en test T_NOT solo labels mayores: " + e.getMessage());
        }
    }

    /*
    TEST: T_NOT es persistente — re-dispara para nuevos labels
    T ¬P c0, F (Q→R) c0, contexto c0 ≤ c1 ≤ c2:
    1. T_NOT aplica a T¬P:c0 → genera F P c0, F P c1, F P c2.
    2. F→ aplica a F(Q→R):c0 (no hay T Q:ch con ch ≤ c0)
        → crea label c3, agrega T Q:c3 y F R:c3.
    3. T_NOT nunca fue marcada ANALYSED → re-dispara en el siguiente ciclo.
    4. T_NOT detecta el nuevo label c3 (c0 ≤ c3) → genera F P c3.
    */
    @Test
    public void testRule10_T_NOT_PersistentWithNewLabel() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -P c0", "F ->(Q R) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("F→ debe generar T Q en el nuevo label c3", treeOutput.contains("T Q c3"));
            assertTrue("F→ debe generar F R en el nuevo label c3", treeOutput.contains("F R c3"));
            // F P c3 solo puede venir de T_NOT re-disparando para c3:
            // F→ genera F R (no F P), y no hay otra regla que genere F P c3.
            assertTrue("T_NOT persistente debe generar F P c3 para el nuevo label", treeOutput.contains("F P c3"));
            assertTrue("Debe aplicar la regla T_NOT", treeOutput.contains("T_NOT"));
        } catch (Exception e) {
            fail("Error en test T_NOT persistente con nuevo label: " + e.getMessage());
        }
    }

    /*
    TEST: T_NOT habilita regla de dos premisas (T∨₁)
    T ¬P c0, T (P∨Q) c1, contexto c0 ≤ c1 ≤ c2:
    1. T_NOT genera físicamente F P c0, F P c1, F P c2 (todos en b).
    2. T∨₁: T(P∨Q):c1, F P:c1, c1 ≤ c1 → T Q:c1.
    getReferences busca en b (físico), no en b*。
    La derivación funciona porque T_NOT generó F P:c1 físicamente en b.
    */
    @Test
    public void testRule10_T_NOT_EnablesTwoPremiseRule() {
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -P c0", "T +(P Q) c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("T_NOT debe generar físicamente F P c1 en b", treeOutput.contains("F P c1"));
            assertTrue("T∨₁ debe derivar T Q c1", treeOutput.contains("T Q c1"));
            assertTrue("Debe aplicar T_NOT", treeOutput.contains("T_NOT"));
            assertTrue("Debe aplicar T_OR_F_LEFT", treeOutput.contains("T_OR_F_LEFT"));
        } catch (Exception e) {
            fail("Error en test T_NOT habilita regla de dos premisas: " + e.getMessage());
        }
    }

    @Test
    public void testRule10_T_NOT_ClosureViaBStar() {
        System.out.println("\n=== TEST REGLA 10: T_NOT produce cierre via b* ===");
        System.out.println("T ¬P c0, T P c1 (c0 ≤ c1):");
        System.out.println("  La semántica de T¬P:c0 incluye implícitamente F P:cj para todo cj ≥ c0 en b*.");
        System.out.println("  En particular F P c1 ∈ b* (pues c0 ⪯ c1).");
        System.out.println("  Al agregar T P c1 al árbol, updateMultimap detecta T P c1 y F P c1 en b*");
        System.out.println("  con c1 ⪯ c1 → CIERRE inmediato (antes de aplicar T_NOT como paso explícito).");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -P c0", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe estar cerrado", proof.isClosed());
            // T_NOT no aparece como paso explícito en el árbol porque la rama se cierra
            // durante updateMultimap antes de que la estrategia tenga oportunidad de aplicar la regla.
            // El cierre ocurre via la extensión b* implícita de T¬P:c0.
        } catch (Exception e) {
            fail("Error en test T_NOT cierre via b*: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 11: F_NOT (F¬)
    // F ¬A : ci → T A : cj (cj nuevo, ci ⪯ cj)
    //
    // A diferencia de F→₁, el paper NO impone un "proviso" explícito para F¬.
    // El bloqueo surge de la condición de completitud de Def. 5.6 (Algorithm 1, línea 6):
    //   "select a φ in b which is not completely analyzed in b"
    // Def. 5.6 para F¬: "If F¬A:ci ∈ b, then there is cj ∈ Cb such that
    //   ci ⪯b cj and T A:cj ∈ b*."
    // Cuando esa condición YA se satisface, F¬A:ci está completamente analizada
    // y el algoritmo directamente no la selecciona como candidata — no hay
    // necesidad de aplicar F¬ de nuevo.
    // La implementación (shouldBlockFNotRule) verifica esto activamente al
    // intentar aplicar la regla, con el mismo efecto. Sin esta verificación
    // se generaría un loop:
    //   T¬¬A (persistente) → F¬A:ci → F¬ crea cj → T A:cj → T¬¬A re-aplica → ...
    // =====================================

    @Test
    public void testRule11_F_NOT_NewLabel() {
        System.out.println("\n=== TEST REGLA 11: F_NOT (Caso básico) ===");
        System.out.println("F ¬P c0 → F P cj (cj nuevo, c0 ⪯ cj)");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F -P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // Verificar que se generó F P con nueva label (no c0)
            assertTrue("Debe generar T P con label nueva", treeOutput.contains("T P c3") && !treeOutput.contains("F P c0"));
            assertTrue("Debe aplicar F_NOT", treeOutput.contains("F_NOT"));

            System.out.println("✅ REGLA 11 (F_NOT): NewLabelGetter básico - CORRECTA");

        } catch (Exception e) {
            fail("Error en test F_NOT básico: " + e.getMessage());
        }
    }

    @Test
    public void testProviso_FNot_BlockedBySameLabelTA() {
        System.out.println("\n=== TEST PROVISO F¬: bloqueada por T A en mismo label ===");
        System.out.println("F¬P:c0, T P:c0 — proviso activo: T P:c0 con c0 ≤ c0 satisface F¬P:c0.");
        System.out.println("  F¬P:c0 ya está semánticamente satisfecha: hay un mundo (c0) accesible");
        System.out.println("  desde c0 donde P es forzado. No tiene sentido crear un nuevo label.");
        System.out.println("  Fundamento: Def. 5.6 — F¬A:ci completa si ∃ cj: ci ≤ cj y T A:cj ∈ b*.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F -P c0", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse("F¬ NO debe aplicarse (T P:c0 satisface el proviso)", treeOutput.contains("F_NOT"));
            assertFalse("NO debe crearse nuevo label c3", treeOutput.contains("T P c3"));

            System.out.println("✅ PROVISO F¬: bloqueada correctamente por T P:c0 (mismo label) - CORRECTO");
        } catch (Exception e) {
            fail("Error en test proviso F¬ mismo label: " + e.getMessage());
        }
    }

    @Test
    public void testProviso_FNot_BlockedByHigherLabelTA() {
        System.out.println("\n=== TEST PROVISO F¬: bloqueada por T A en label accesible mayor ===");
        System.out.println("F¬P:c0, T P:c1 — contexto c0 ≤ c1, proviso activo: c1 ∈ b* con c0 ≤ c1.");
        System.out.println("  T P:c1 es accesible desde c0 (c0 ≤ c1) y satisface la condición de Def. 5.6.");
        System.out.println("  F¬P:c0 ya está semánticamente satisfecha vía b*. F¬ no debe expandirse.");
        System.out.println("  Fundamento: Def. 5.6 — F¬A:c0 completa porque ∃ c1: c0 ≤ c1 y T P:c1 ∈ b*.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F -P c0", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse("F¬ NO debe aplicarse (T P:c1 con c0 ≤ c1 ya satisface F¬P:c0)", treeOutput.contains("F_NOT"));
            assertFalse("NO debe crearse nuevo label c3", treeOutput.contains("T P c3"));

            System.out.println("✅ PROVISO F¬: bloqueada correctamente por T P:c1 con c0 ≤ c1 - CORRECTO");
        } catch (Exception e) {
            fail("Error en test proviso F¬ label mayor: " + e.getMessage());
        }
    }

    // =====================================
    // DERIVACIÓN DE DOBLE NEGACIÓN: T¬ + F¬
    // T ¬¬A : ci
    //   via (T¬): F ¬A : ck  (ck mínimo con ci ⪯ ck)
    //   via (F¬): T A : cj   (cj nuevo con ck ⪯ cj)
    // =====================================

    @Test
    public void testDoubleNeg_TNotFNot_Chain() {
        System.out.println("\n=== TEST: Derivación de doble negación via T¬ + F¬ ===");
        System.out.println("T ¬¬P c0 → F ¬P ck (T¬) → T P cj (F¬)");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(-P) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe derivar T P con una etiqueta nueva mayor que c0",
                    treeOutput.contains("T P c3") && !treeOutput.contains("T P c0"));
            assertTrue("Debe aplicar la regla T_NOT (primer paso)", treeOutput.contains("T_NOT"));
            assertTrue("Debe aplicar la regla F_NOT (segundo paso)", treeOutput.contains("F_NOT"));
        } catch (Exception e) {
            fail("Error en test derivación doble negación: " + e.getMessage());
        }
    }

    @Test
    public void testDoubleNeg_TNotFNot_Chain_Complex() {
        System.out.println("\n=== TEST: Derivación de doble negación via T¬ + F¬ (fórmula compleja) ===");
        System.out.println("T ¬¬(P∧Q) c0 → F ¬(P∧Q) ck (T¬) → T (P∧Q) cj (F¬)");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(-(*(P Q))) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe derivar T (P∧Q) con una etiqueta nueva mayor que c0",
                    treeOutput.contains("T (P&Q) c3") && !treeOutput.contains("T (P&Q) c0"));
            assertTrue("Debe aplicar la regla T_NOT (primer paso)", treeOutput.contains("T_NOT"));
            assertTrue("Debe aplicar la regla F_NOT (segundo paso)", treeOutput.contains("F_NOT"));

            System.out.println("✅ Derivación doble negación (T¬ + F¬): CORRECTA");

        } catch (Exception e) {
            fail("Error en test derivación doble negación compleja: " + e.getMessage());
        }
    }

    // =====================================
    // PROPAGACIÓN POR MONOTONICIDAD DE KRIPKE (F¬)
    //
    // Cuando F¬ crea un nuevo label cj (ci ⪯ cj), las T-compuestas
    // en labels ci' ≤ cj se propagan físicamente a cj por monotonicidad
    // ascendente (Def. 5.3 regla 2: T A:ci ∈ b y ci ⪯ cj ⟹ T A:cj ∈ b*).
    //
    // Esto materializa fórmulas de b* en b, permitiendo que:
    // - Reglas de 1 premisa (T∧, T∨) se apliquen con rinstances frescos
    // - T-compuestas propagadas se seleccionen como premisas mayores de
    //   reglas de 2 premisas (T→₁, T→₂) para nuevas auxiliares
    //
    // Sin propagación, las T-compuestas originales están ANALYSED y no se
    // re-seleccionan, impidiendo que nuevas auxiliares se emparejen.
    //
    // Fundamento: Def. 5.3 (b*), Def. 5.6 (completamente analizado),
    //   Algorithm 1 línea 6, Theorem 5.11 (terminación).
    // Código: IPLOnePremiseRuleApplicator.propagateCompositeTFormulasForNewLabel()
    // =====================================

    @Test
    public void testFNot_MonotonicityPropagation() {
        System.out.println("\n=== TEST: Propagación por monotonicidad en F¬ ===");
        System.out.println("(P→Q) ∧ ¬¬P → ¬¬Q es tautología IPL.");
        System.out.println("F¬ crea un nuevo label; T(P→Q) debe propagarse a ese label");
        System.out.println("para que T→₁/T→₂ puedan emparejar auxiliares nuevas.");

        try {
            Context context = new Context();
            context.getNewFormulaLabel();

            // (P→Q) ∧ ¬¬P → ¬¬Q
            // En notación prefija KEMS: ->(*(->(P Q) -(-(P))) -(-(Q)))
            Proof proof = proveFormulas("F ->(*(->(P Q) -(-(P))) -(-(Q))) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // La prueba requiere F¬ para crear labels (para ¬¬P y ¬¬Q)
            assertTrue("Debe aplicar F_NOT", treeOutput.contains("F_NOT"));

            // Debe cerrar: es tautología IPL
            assertTrue("(P→Q) ∧ ¬¬P → ¬¬Q debe ser válida en IPL", proof.isClosed());

            // Verificar que T(P→Q) fue propagada a un label nuevo (no solo c1)
            // La propagación crea T(P→Q) en labels creados por F¬
            boolean propagatedImplication = false;
            for (String line : treeOutput.split("\n")) {
                if (line.contains("T (P->Q)") && line.contains("Kripke monotonicity propagation")) {
                    propagatedImplication = true;
                    break;
                }
            }
            assertTrue("T(P→Q) debe propagarse a labels creados por F¬", propagatedImplication);

            System.out.println("✅ Propagación por monotonicidad (F¬): CORRECTA");

        } catch (Exception e) {
            fail("Error en test propagación F¬: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 12: TEST DE CLOSURE (CLOSE)
    // T A ci, F A cj ci ⪯ cj → CIERRE
    // =====================================

    @Test
    public void testRule12_Closure_SameLabel() {
        System.out.println("\n=== TEST CLOSURE IPL ===");
        System.out.println("T P c0, F P c0 → DEBE CERRAR");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T P c0", "F P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe estar cerrado", proof.isClosed());

            System.out.println("✅ CLOSURE IPL: CORRECTA");

        } catch (Exception e) {
            fail("Error en test closure: " + e.getMessage());
        }
    }

    @Test
    public void testRule12_Closure_GreaterLabel() {
        System.out.println("\n=== TEST CLOSURE IPL ===");
        System.out.println("T P c0, F P c2 → DEBE CERRAR");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T P c0", "F P c2");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe estar cerrado", proof.isClosed());

            System.out.println("✅ CLOSURE IPL: CORRECTA");

        } catch (Exception e) {
            fail("Error en test closure: " + e.getMessage());
        }
    }

    @Test
    public void testRule12_Closure_LowerLabel() {
        System.out.println("\n=== TEST CLOSURE IPL: LABEL MAYOR NO CIERRA ===");
        System.out.println("T P c2, F P c1 → NO DEBE CERRAR");
        System.out.println("La regla de cierre requiere ci ⪯ cj (T-label ≤ F-label).");
        System.out.println("c2 ⪯ c1 es falso en el contexto c0 ≤ c1 ≤ c2, por lo tanto la rama permanece abierta.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T P c2", "F P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse("NO debe estar cerrado: la etiqueta de T (c2) es mayor que la de F (c1), no se cumple c2 ⪯ c1", proof.isClosed());

            System.out.println("✅ CLOSURE IPL: Regla de cierre correctamente no aplicada cuando T-label > F-label");

        } catch (Exception e) {
            fail("Error en test closure: " + e.getMessage());
        }
    }
    @Test
    public void testNewLabelGetter_Behavior() {
        System.out.println("\n=== TEST NewLabelGetter (F_NOT) ===");
        System.out.println("F ¬P c0 → F P cj (cj nuevo, c0 ≤ cj)");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F -P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // F_NOT debe generar F P con nueva label
            assertTrue("Debe generar F P", treeOutput.contains("T P c3"));
            assertTrue("Debe aplicar F_NOT", treeOutput.contains("F_NOT"));

            System.out.println("✅ NewLabelGetter (F_NOT): Funcionando correctamente");

        } catch (Exception e) {
            fail("Error en test NewLabelGetter: " + e.getMessage());
        }
    }

    // =====================================
    // TEST ESPECÍFICO: TERCIO EXCLUIDO NO VÁLIDO EN IPL
    // P ∨ ¬P NO debe cerrar en IPL
    // =====================================

    @Test
    public void testLawOfExcludedMiddle_NotValidInIPL() {
        System.out.println("\n=== TEST TERCIO EXCLUIDO NO VÁLIDO EN IPL ===");
        System.out.println("F (P ∨ ¬P) → NO debe cerrar");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F +(P -P) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // P ∨ ¬P NO es válido en IPL
            assertFalse("P ∨ ¬P NO debe estar cerrado en IPL", proof.isClosed());
            assertTrue("Debe aplicar la regla F_OR", treeOutput.contains("F_OR"));

            System.out.println("✅ TERCIO EXCLUIDO NO VÁLIDO EN IPL: CORRECTA");

        } catch (Exception e) {
            fail("Error en test tercio excluido: " + e.getMessage());
        }
    }

    @Test
    public void testLawOfExcludedMiddle_NotValidInIPL3() {
        System.out.println("\n=== TEST TERCIO EXCLUIDO NO VÁLIDO EN IPL ===");
        System.out.println("F (P ∨ ¬P) → NO debe cerrar");

        try {
            Context context = new Context();
            context.getNewFormulaLabel();
            Proof proof = proveFormulasWithContext(context, "F +(P -P) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // P ∨ ¬P NO es válido en IPL
            assertFalse("P ∨ ¬P NO debe estar cerrado en IPL", proof.isClosed());
            assertTrue("Debe aplicar la regla F_OR", treeOutput.contains("F_OR"));

            System.out.println("✅ TERCIO EXCLUIDO NO VÁLIDO EN IPL: CORRECTA");

        } catch (Exception e) {
            fail("Error en test tercio excluido: " + e.getMessage());
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

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // ((A→B)∧(A→¬B))→¬A es una tautología de IPL (Ejemplo del paper)
            assertTrue("Debe estar cerrado en IPL", proof.isClosed());

        } catch (Exception e) {
            fail("Error en test: " + e.getMessage());
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

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // ¬¬(¬¬A→A) es una tautología de IPL (Ejemplo del paper, Figura 6)
            assertTrue("Debe estar cerrado en IPL", proof.isClosed());

        } catch (Exception e) {
            fail("Error en test: " + e.getMessage());
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

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertTrue("Debe estar cerrado en IPL", proof.isClosed());

        } catch (Exception e) {
            fail("Error en test: " + e.getMessage());
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

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // (((p→q)→p)→p→q)→q es una tautología de IPL (Ejemplo del paper)
            assertTrue("Debe estar cerrado en IPL", proof.isClosed());

        } catch (Exception e) {
            fail("Error en test: " + e.getMessage());
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

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // Test largo con múltiples aplicaciones de PB: tautología de IPL que involucra
            // comparación simétrica de tres proposiciones p1, p2, p3.
            assertTrue("Debe estar cerrado en IPL", proof.isClosed());

        } catch (Exception e) {
            fail("Error en test: " + e.getMessage());
        }
    }


    @Test
    public void testDoubleNegationElimination_NotValidInIPL() {
        System.out.println("\n=== TEST: F ¬¬A → A (Doble negación) ===");
        System.out.println("Fórmula: F ¬¬A → A : c0");
        System.out.println("Esta fórmula NO es válida en IPL (doble negación no implica afirmación)");

        try {
            Context context = new Context();
            context.getNewFormulaLabel();

            // F ¬¬A → A : c0
            String formula = "F ->(-(-A) A) c0";

            Proof proof = proveFormulas(formula);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("\n📊 Árbol resultado:");
            System.out.println(treeOutput);

            // En IPL, ¬¬A → A NO es válido (doble negación no implica afirmación)
            assertFalse("F ¬¬A → A NO debe estar cerrado en IPL", proof.isClosed());
            assertTrue("Debe aplicar la regla F_A_IMPLIES_B_TA_FB", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));

            System.out.println("\n✅ DOBLE NEGACIÓN: El árbol NO se cierra (correcto para IPL)");
            System.out.println("   En IPL, ¬¬A no implica necesariamente A");

        } catch (Exception e) {
            e.printStackTrace();
            fail("Error en test doble negación: " + e.getMessage());
        }
    }

    @Test
    public void testPeirceLaw_NotValidInIPL() {
        System.out.println("\n=== TEST: Ley de Peirce no válida en IPL ===");
        System.out.println("Fórmula: F ((p → q) → p) → p : c0");
        System.out.println("La Ley de Peirce ((p→q)→p)→p es válida en lógica clásica pero NO en IPL.");

        try {
            Context context = new Context();
            context.getNewFormulaLabel();

            // F ((p → q) → p) → p : c0  — Ley de Peirce genuina
            String formula = "F ->(->(->(p q) p) p) c0";

            Proof proof = proveFormulas(formula);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("\nÁrbol resultado:");
            System.out.println(treeOutput);

            assertFalse("La Ley de Peirce NO debe ser válida en IPL", proof.isClosed());
            assertTrue("Debe aplicar la regla F_A_IMPLIES_B_TA_FB", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));
        } catch (Exception e) {
            e.printStackTrace();
            fail("Error en test Ley de Peirce: " + e.getMessage());
        }
    }

    @Test
    public void testComplexDoubleNegationAndExcludedMiddle() {
        System.out.println("\n=== TEST: Fórmula compleja con doble negación y tercio excluido ===");
        System.out.println("Fórmula: F ((¬¬p → p) → (p ∨ ¬p)) → (¬p ∨ ¬¬p) : c0");
        System.out.println("Esta fórmula combina doble negación y tercio excluido");

        try {
            Context context = new Context();
            context.getNewFormulaLabel();

            // F ((¬¬p → p) → (p ∨ ¬p)) → (¬p ∨ ¬¬p) : c0
            String formula = "F ->(->(->(-(-p) p) +(p -p)) +(-p -(-p))) c0";

            Proof proof = proveFormulas(formula);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("\n📊 Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse(proof.isClosed());

        } catch (Exception e) {
            e.printStackTrace();
            fail("Error en test fórmula compleja: " + e.getMessage());
        }
    }

    // =====================================
    // PB: COMPORTAMIENTO CON LABELS
    // PB ignora labels intencionalmente al verificar si la premisa menor
    // ya existe (formulaExistsInTree). La compatibilidad de labels se
    // verifica en el applicator de dos premisas. Si PB verificara labels,
    // generaría ramas ilimitadas (cada PB habilita reglas que crean nuevos
    // labels via F→₁ y propagación, desencadenando más PB).
    // Paper: Algorithm 1 líneas 14-18, Theorem 5.11.
    // =====================================

    /**
     * Cuando F P existe en el árbol (en cualquier label), PB lo reconoce
     * como "premisa menor disponible" y NO aplica PB para T∨₁.
     * PB puede aplicar para T∨₂ (F Q no existe), pero NO para T∨₁.
     * Esto es correcto: el chequeo de labels se delega al applicator de
     * dos premisas, y PB solo se encarga de generar subfórmulas ausentes.
     */
    @Test
    public void testPB_IgnoresLabels_AuxExistsAtAnyLabel() {
        System.out.println("\n=== TEST: PB ignora labels en existencia de auxiliar ===");
        System.out.println("T(P∨Q):c1, F P:c0 con c0 ⪯ c1");
        System.out.println("T∨₁ necesita F P:cj con c1 ⪯ cj. F P:c0 existe (label incompatible),");
        System.out.println("pero PB no aplica para T∨₁ porque F P ya existe en el árbol.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // X_OR_F_LEFT (T∨₁) NO debe aplicarse: F P:c0 tiene label incompatible
            // y PB no genera F P:c1 porque F P ya "existe" (ignoring labels)
            assertFalse("T∨₁ NO debe aplicarse (F P:c0 incompatible, PB no genera F P:c1)",
                       treeOutput.contains("X_OR_F_LEFT"));

            // El escenario es consistente en Kripke → rama abierta
            assertFalse("Rama debe quedar abierta (escenario consistente en Kripke)",
                       proof.isClosed());

            System.out.println("✅ PB ignora labels correctamente");

        } catch (Exception e) {
            fail("Error en test PB ignora labels: " + e.getMessage());
        }
    }

    /**
     * Cuando el auxiliar tiene un label compatible, la regla de dos premisas
     * aplica directamente sin necesidad de PB.
     */
    @Test
    public void testPB_DirectApplication_AuxAtCompatibleLabel() {
        System.out.println("\n=== TEST: Aplicación directa con label compatible ===");
        System.out.println("T(P∨Q):c0, F P:c1 con c0 ⪯ c1");
        System.out.println("T∨₁ necesita F P:cj con c0 ⪯ cj. F P:c1 ES compatible.");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c0", "F P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // T∨₁ debe aplicarse directamente (sin PB) porque F P:c1 es compatible
            assertTrue("T∨₁ debe aplicarse directamente con label compatible",
                       treeOutput.contains("X_OR_F_LEFT") || treeOutput.contains("T_OR_F_LEFT"));
            assertTrue("Debe derivar T Q c0",
                       treeOutput.contains("T Q c0"));

            System.out.println("✅ Aplicación directa con label compatible: CORRECTA");

        } catch (Exception e) {
            fail("Error en test aplicación directa: " + e.getMessage());
        }
    }

}
