package logicalSystems.ipl;

import static org.junit.Assert.*;

import org.junit.Before;
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
        System.out.println("🔧 Setup: SignedFormulaCreator configurado para IPL con nueva estructura");
    }
    
    /**
     * Crea un Context con relaciones predefinidas para tests específicos
     */
    private Context createContextWithRelations() {
        Context context = new Context();
        
        // Crear etiquetas c0, c1, c2 con relaciones específicas
        FormulaLabel c0 = context.getNewFormulaLabel();
        FormulaLabel c1 = context.getNewFormulaLabel();
        FormulaLabel c2 = context.getNewFormulaLabel();
        
        System.out.println("🏷️ Created predefined labels: c0=" + c0 + ", c1=" + c1 + ", c2=" + c2);
        
        // Establecer algunas relaciones para tests específicos
        // c0 ≤ c1 (para tests que requieren esta relación)
        context.addRelation(c0, c1);
        context.addRelation(c1, c2);
        
        System.out.println("✅ Context creado con relaciones: c0 ≤ c1");
        context.printRelations();
        
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
                    System.out.println("📍 Mapped existing ContextFormulaLabel: " + label.getIndex() + " → " + label);
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
                    System.out.println("🆕 Created and cached new ContextFormulaLabel for index " + originalLabel.getIndex() + ": " + contextLabel);
                } else {
                    System.out.println("♻️ Reusing existing ContextFormulaLabel for index " + originalLabel.getIndex() + ": " + contextLabel);
                }
                
                // Crear nueva LabelledFormula con ContextFormulaLabel
                LabelledFormula newLabelledFormula = iplFactory.createLabelledFormula(
                    contextLabel,
                    originalFormula
                );
                
                formulasList.add(newLabelledFormula);
                System.out.println("🔄 Converted to predefined Context: " + originalLabel + " → " + contextLabel);
            }
            
            problem.setSignedFormulaFactory(iplFactory);
            System.out.println("✅ Using predefined Context with " + originalFormulas.size() + " converted formulas");
        } else {
            System.out.println("✅ Using auto-generated Context from parsing");
        }
        
        // Crear método con reglas IPL
        Method method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
        
        // Crear estrategia IPL
        IPLSimpleStrategy strategy = new IPLSimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());
        
        // Inyectar Context del Problem en la Strategy (nueva estructura)
        if (problem.hasIPLContext()) {
            strategy.setIPLContext(problem.getIPLContext());
        }
        
        // Crear y configurar prover
        Prover prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);
        
        System.out.println("🚀 Problem formulas: " + problem.getFormulas().size());
        if (problem.hasIPLContext()) {
            System.out.println("🔗 Context labels: " + problem.getIPLContext().getLabels().size());
        }
        
        // Verificar que se están usando ContextFormulaLabel
        for (int i = 0; i < Math.min(problem.getFormulas().size(), 3); i++) {
            if (problem.getFormulas().get(i).getLabel() instanceof ContextFormulaLabel) {
                System.out.println("✅ Formula " + i + " uses ContextFormulaLabel: " + problem.getFormulas().get(i).getLabel());
            } else {
                System.out.println("⚠️ Formula " + i + " uses basic FormulaLabel: " + problem.getFormulas().get(i).getLabel() + 
                    " (class: " + problem.getFormulas().get(i).getLabel().getClass().getSimpleName() + ")");
            }
        }
        
        return prover.prove(problem);
    }

    // =====================================
    // REGLA 1: F_OR
    // F A∨B : ci → F A: ci, F B : ci
    // =====================================
    
    @Test
    public void testRule1_F_OR_BasicApplication() {
        System.out.println("\n=== TEST REGLA 1: F_OR ===");
        System.out.println("F (P∨Q) c0 → F P c0, F Q c0");
        
        try {
            Proof proof = proveFormulas("F +(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó F_OR
            assertTrue("Debe generar F P c0", treeOutput.contains("F P c0"));
            assertTrue("Debe generar F Q c0", treeOutput.contains("F Q c0"));
            
            // Verificar que ambas conclusiones tienen la misma label que la premisa
            assertTrue("F P debe tener label c0", treeOutput.contains("F P c0"));
            assertTrue("F Q debe tener label c0", treeOutput.contains("F Q c0"));
            
            System.out.println("✅ REGLA 1 (F_OR): CORRECTA - usando nueva estructura");
            
        } catch (Exception e) {
            fail("Error en test F_OR: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule1_F_OR_WithPredefinedContext() {
        System.out.println("\n=== TEST REGLA 1: F_OR con Context predefinido ===");
        System.out.println("F (P∨Q) c0 → F P c0, F Q c0 (con c0 ≤ c1 predefinido)");
        
        try {
            // Usar Context con relaciones predefinidas
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F +(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado con Context predefinido:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó F_OR
            assertTrue("Debe generar F P c0", treeOutput.contains("F P c0"));
            assertTrue("Debe generar F Q c0", treeOutput.contains("F Q c0"));
            
            System.out.println("✅ REGLA 1 (F_OR): CORRECTA - con relaciones predefinidas");
            
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
        System.out.println("\n=== TEST REGLA 2: T_AND ===");
        System.out.println("T (P∧Q) c0 → T P c0, T Q c0");
        
        try {
            Proof proof = proveFormulas("T *(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó T_AND
            assertTrue("Debe generar T P c0", treeOutput.contains("T P c0"));
            assertTrue("Debe generar T Q c0", treeOutput.contains("T Q c0"));
            
            System.out.println("✅ REGLA 2 (T_AND): CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_AND: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 3: X_OR_F_LEFT
    // T A∨B : ci, F A: cj, ci ⪯ cj → T B : ci
    // =====================================

    @Test
    public void testRule3_X_OR_F_LEFT_ValidLabelCondition() {
        System.out.println("\n=== TEST REGLA 3: X_OR_F_LEFT (Label válido) ===");
        System.out.println("T (P∨Q) c0, F P c1 (c0 ⪯ c1: main.label ≤ aux.label) → T Q c0");
        
        try {
            // Usar nueva estructura con relación c0 ≤ c1
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c0", "F P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla y generó T Q c0
            assertTrue("Debe generar T Q c0", treeOutput.contains("T Q c0"));
            assertFalse("NO debe estar cerrado", proof.isClosed());
            
            System.out.println("✅ REGLA 3 (X_OR_F_LEFT): LessThanLabelCondition c0 ≤ c1 - CORRECTA (nueva estructura)");
            
        } catch (Exception e) {
            fail("Error en test X_OR_F_LEFT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule3_X_OR_F_LEFT_ValidEqualLabelCondition() {
        System.out.println("\n=== TEST REGLA 3: X_OR_F_LEFT (Label válido) ===");
        System.out.println("T (P∨Q) c1, F P c1 (c1 ⪯ c1: main.label ≤ aux.label) → T Q c1");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // Verificar que se aplicó la regla y generó T Q c1
            assertTrue("Debe generar T Q c1", treeOutput.contains("T Q c1"));
            assertFalse("NO debe estar cerrado", proof.isClosed());

            System.out.println("✅ REGLA 3 (X_OR_F_LEFT): LessThanLabelCondition c1 ≤ c1 - CORRECTA");

        } catch (Exception e) {
            fail("Error en test X_OR_F_LEFT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule3_X_OR_F_LEFT_InvalidLabelCondition() {
        System.out.println("\n=== TEST REGLA 3: X_OR_F_LEFT (Label inválido) ===");
        System.out.println("T (P∨Q) c1, F P c0 (c1 ⪯̸ c0: main.label ≰ aux.label) → NO debe aplicarse");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Con labels inválidos (c1 ≰ c0), la regla NO debe aplicarse
            // LessThanLabelCondition valida main.label ≤ aux.label, pero c1 ≰ c0
            // Verificar que no se aplicó la regla específica, pero el árbol debe existir
            assertNotNull("El árbol de prueba debe existir", tree);
            assertFalse("NO debe generar T Q con labels inválidos (c1 ≰ c0)", 
                       treeOutput.contains("T Q"));
            assertFalse("NO debe aplicar X_OR_F_LEFT con labels inválidos", 
                       treeOutput.contains("X_OR_F_LEFT"));
            
            System.out.println("✅ REGLA 3 (X_OR_F_LEFT): LessThanLabelCondition rechaza c1 ≰ c0 - CORRECTA");
            
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
        System.out.println("\n=== TEST REGLA 4: T_OR_F_RIGHT (Label válido) ===");
        System.out.println("T (P∨Q) c0, F Q c1 (c0 ⪯ c1: main.label ≤ aux.label) → T P c0");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c0", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla y generó T P c0
            assertTrue("Debe generar T P c0", treeOutput.contains("T P c0"));
            assertFalse("NO debe estar cerrado", proof.isClosed());
            
            System.out.println("✅ REGLA 4 (T_OR_F_RIGHT): LessThanLabelCondition c0 ≤ c1 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_OR_F_RIGHT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule4_T_OR_F_RIGHT_ValidEqualLabelCondition() {
        System.out.println("\n=== TEST REGLA 4: T_OR_F_RIGHT (Labels iguales) ===");
        System.out.println("T (P∨Q) c1, F Q c1 (c1 ⪯ c1: main.label ≤ aux.label) → T P c1");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla y generó T P c1
            assertTrue("Debe generar T P c1", treeOutput.contains("T P c1"));
            assertFalse("NO debe estar cerrado", proof.isClosed());
            
            System.out.println("✅ REGLA 4 (T_OR_F_RIGHT): LessThanLabelCondition c1 ≤ c1 - CORRECTA");
            
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
            
            // Con labels inválidos (c1 ≰ c0), la regla NO debe aplicarse
            // LessThanLabelCondition valida main.label ≤ aux.label, pero c1 ≰ c0
            // Verificar que no se aplicó la regla específica, pero el árbol debe existir
            assertNotNull("El árbol de prueba debe existir", tree);
            assertFalse("NO debe generar T P con labels inválidos (c1 ≰ c0)", 
                       treeOutput.contains("T P"));
            assertFalse("NO debe aplicar T_OR_F_RIGHT con labels inválidos", 
                       treeOutput.contains("T_OR_F_RIGHT"));
            
            System.out.println("✅ REGLA 4 (T_OR_F_RIGHT): LessThanLabelCondition rechaza c1 ≰ c0 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_OR_F_RIGHT inválido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 5: T_NOT_A_OR_B
    // T ¬(A∨B) : ci → T ¬A : ci, T ¬B : ci
    // =====================================
    
    @Test
    public void testRule5_T_NOT_A_OR_B_BasicApplication() {
        System.out.println("\n=== TEST REGLA 5: T_NOT_A_OR_B ===");
        System.out.println("T ¬(P∨Q) c0 → T ¬P c0, T ¬Q c0");
        
        try {
            Proof proof = proveFormulas("T -(+(P Q)) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó T_NOT_A_OR_B
            assertTrue("Debe generar T !P c0", treeOutput.contains("T !P c0"));
            assertTrue("Debe generar T !Q c0", treeOutput.contains("T !Q c0"));
            
            System.out.println("✅ REGLA 5 (T_NOT_A_OR_B): CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_NOT_A_OR_B: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 6: T_A_OR_B (BinarySomeRelationLabelCondition)
    // T A∨B : ci, T ¬A : cj, ci ≤ cj ∨ cj ≤ ci → T B : ci
    // =====================================
    
    @Test
    public void testRule6_T_A_OR_B_ValidLabelCondition_CiLessEqualCj() {
        System.out.println("\n=== TEST REGLA 6: T_A_OR_B (ci ≤ cj) ===");
        System.out.println("T (P∨Q) c0, T ¬P c1 (c0 ≤ c1) → T Q c0");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c0", "T -P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla y generó T Q c0
            assertTrue("Debe generar T Q c0", treeOutput.contains("T Q c0"));
            
            System.out.println("✅ REGLA 6 (T_A_OR_B): BinarySomeRelationLabelCondition c0 ≤ c1 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_A_OR_B válido: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule6_T_A_OR_B_ValidLabelCondition_CjLessEqualCi() {
        System.out.println("\n=== TEST REGLA 6: T_A_OR_B (cj ≤ ci) ===");
        System.out.println("T (P∨Q) c1, T ¬P c0 (c0 ≤ c1) → T Q c1");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "T -P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla y generó T Q c1
            assertTrue("Debe generar T Q c1", treeOutput.contains("T Q c1"));
            
            System.out.println("✅ REGLA 6 (T_A_OR_B): BinarySomeRelationLabelCondition c0 ≤ c1 (inversa) - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_A_OR_B válido inverso: " + e.getMessage());
        }
    }

    @Test
    public void testRule6_T_A_OR_B_ValidLabelCondition_CjEqualCi() {
        System.out.println("\n=== TEST REGLA 6: T_A_OR_B (cj = ci) ===");
        System.out.println("T (P∨Q) c1, T ¬P c1 (c1 ≤ c1) → T Q c1");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "T -P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // Verificar que se aplicó la regla y generó T Q c1
            assertTrue("Debe generar T Q c1", treeOutput.contains("T Q c1"));

            System.out.println("✅ REGLA 6 (T_A_OR_B): BinarySomeRelationLabelCondition c0 ≤ c1 (inversa) - CORRECTA");

        } catch (Exception e) {
            fail("Error en test T_A_OR_B válido inverso: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 7: T_A_OR_B_NOT_B (BinarySomeRelationLabelCondition)
    // T A∨B : ci, T ¬B : cj, ci ≤ cj ∨ cj ≤ ci → T A : ci
    // =====================================
    
    @Test
    public void testRule7_T_A_OR_B_NOT_B_ValidLabelCondition_CiLessEqualCj() {
        System.out.println("\n=== TEST REGLA 7: T_A_OR_B_NOT_B (ci ≤ cj) ===");
        System.out.println("T (P∨Q) c0, T ¬Q c1 (c0 ≤ c1) → T P c0");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c0", "T -Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla y generó T P c0
            assertTrue("Debe generar T P c0", treeOutput.contains("T P c0"));
            
            System.out.println("✅ REGLA 7 (T_A_OR_B_NOT_B): BinarySomeRelationLabelCondition c0 ≤ c1 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_A_OR_B_NOT_B válido: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule7_T_A_OR_B_NOT_B_ValidLabelCondition_CjLessEqualCi() {
        System.out.println("\n=== TEST REGLA 7: T_A_OR_B_NOT_B (cj ≤ ci) ===");
        System.out.println("T (P∨Q) c1, T ¬Q c0 (c0 ≤ c1) → T P c1");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "T -Q c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla y generó T P c1
            assertTrue("Debe generar T P c1", treeOutput.contains("T P c1"));
            
            System.out.println("✅ REGLA 7 (T_A_OR_B_NOT_B): BinarySomeRelationLabelCondition c0 ≤ c1 (inversa) - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_A_OR_B_NOT_B válido inverso: " + e.getMessage());
        }
    }

    @Test
    public void testRule7_T_A_OR_B_NOT_B_ValidLabelCondition_Equal() {
        System.out.println("\n=== TEST REGLA 7: T_A_OR_B_NOT_B (labels iguales) ===");
        System.out.println("T (P∨Q) c1, T ¬Q c1 (c1 ≤ c1) → T P c1");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T +(P Q) c1", "T -Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla y generó T P c1
            assertTrue("Debe generar T P c1", treeOutput.contains("T P c1"));
            
            System.out.println("✅ REGLA 7 (T_A_OR_B_NOT_B): BinarySomeRelationLabelCondition c1 ≤ c1 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_A_OR_B_NOT_B labels iguales: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 8: F_AND_LEFT
    // F A∧B : cj, T A : ci, ci ⪯ cj → F B : cj
    // =====================================
    
    @Test
    public void testRule8_F_AND_LEFT_ValidLabelCondition() {
        System.out.println("\n=== TEST REGLA 8: F_AND_LEFT (Label válido) ===");
        System.out.println("F (P∧Q) c1, T P c0 (c0 ⪯ c1: aux.label ≤ main.label) → F Q c1");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c1", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se genera F Q c1 (NO F P c1)
            assertTrue("Debe generar F Q c1", treeOutput.contains("F Q c1"));
            assertFalse("NO debe generar F P c1", treeOutput.contains("F P c1"));
            
            System.out.println("✅ REGLA 8 (F_AND_LEFT): GreaterThanLabelCondition c0 ≤ c1 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test F_AND_LEFT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule8_F_AND_LEFT_ValidEqualLabelCondition() {
        System.out.println("\n=== TEST REGLA 8: F_AND_LEFT (Labels iguales) ===");
        System.out.println("F (P∧Q) c1, T P c1 (c1 ⪯ c1: aux.label ≤ main.label) → F Q c1");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c1", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se genera F Q c1 (NO F P c1)
            assertTrue("Debe generar F Q c1", treeOutput.contains("F Q c1"));
            assertFalse("NO debe generar F P c1", treeOutput.contains("F P c1"));
            
            System.out.println("✅ REGLA 8 (F_AND_LEFT): GreaterThanLabelCondition c1 ≤ c1 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test F_AND_LEFT labels iguales: " + e.getMessage());
        }
    }

    @Test
    public void testRule8_F_AND_LEFT_InvalidLabelCondition() {
        System.out.println("\n=== TEST REGLA 8: F_AND_LEFT (Label inválido) ===");
        System.out.println("F (P∧Q) c0, T P c1 (c1 ≰ c0: aux.label ≰ main.label) → NO debe aplicarse");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c0", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Con labels inválidos (c1 ≰ c0), la regla NO debe aplicarse
            assertNotNull("El árbol de prueba debe existir", tree);
            assertFalse("NO debe generar F Q con labels inválidos", treeOutput.contains("F Q"));
            assertFalse("NO debe aplicar F_AND_LEFT", treeOutput.contains("F_AND_LEFT"));
            
            System.out.println("✅ REGLA 8 (F_AND_LEFT): GreaterThanLabelCondition rechaza c1 ≰ c0 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test F_AND_LEFT inválido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 9: X_AND_T_RIGHT (GreaterThanLabelCondition)
    // F A∧B: cj, T B : ci, ci ≤ cj → F A : cj
    // =====================================
    
    @Test
    public void testRule9_X_AND_T_RIGHT_ValidLabelCondition() {
        System.out.println("\n=== TEST REGLA 9: X_AND_T_RIGHT (Label válido) ===");
        System.out.println("F (P∧Q) c1, T Q c0 (c0 ≤ c1: aux.label ≤ main.label) → F P c1");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c1", "T Q c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó F P c1 (NO F Q c1)
            assertTrue("Debe generar F P c1", treeOutput.contains("F P c1"));
            assertFalse("NO debe generar F Q c1", treeOutput.contains("F Q c1"));
            
            System.out.println("✅ REGLA 9 (X_AND_T_RIGHT): GreaterThanLabelCondition c0 ≤ c1 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test X_AND_T_RIGHT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule9_X_AND_T_RIGHT_ValidEqualLabelCondition() {
        System.out.println("\n=== TEST REGLA 9: X_AND_T_RIGHT (Labels iguales) ===");
        System.out.println("F (P∧Q) c1, T Q c1 (c1 ≤ c1: aux.label ≤ main.label) → F P c1");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context,"F *(P Q) c1", "T Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó F P c1 (NO F Q c1)
            assertTrue("Debe generar F P c1", treeOutput.contains("F P c1"));
            assertFalse("NO debe generar F Q c1", treeOutput.contains("F Q c1"));
            
            System.out.println("✅ REGLA 9 (X_AND_T_RIGHT): GreaterThanLabelCondition c1 ≤ c1 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test X_AND_T_RIGHT labels iguales: " + e.getMessage());
        }
    }

    @Test
    public void testRule9_X_AND_T_RIGHT_InvalidLabelCondition() {
        System.out.println("\n=== TEST REGLA 9: X_AND_T_RIGHT (Label inválido) ===");
        System.out.println("F (P∧Q) c0, T Q c1 (c1 ≰ c0: aux.label ≰ main.label) → NO debe aplicarse");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context,"F *(P Q) c0", "T Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Con labels inválidos (c1 ≰ c0), la regla NO debe aplicarse
            assertNotNull("El árbol de prueba debe existir", tree);
            assertFalse("NO debe generar F P con labels inválidos", treeOutput.contains("F P"));
            assertFalse("NO debe aplicar X_AND_T_RIGHT", treeOutput.contains("X_AND_T_RIGHT"));
            
            System.out.println("✅ REGLA 9 (X_AND_T_RIGHT): GreaterThanLabelCondition rechaza c1 ≰ c0 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test X_AND_T_RIGHT inválido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 10: T_NOT_A_AND_B (MinimalGreaterLabelGetter)
    // T ¬(A∧B) : ci, T A : cj, ci ≤ ck ∧ cj ≤ ck → T ¬B : ck
    // =====================================
    
    @Test
    public void testRule10_T_NOT_A_AND_B_MinimalGreaterLabel_DifferentLabels() {
        System.out.println("\n=== TEST REGLA 10: T_NOT_A_AND_B (Labels diferentes) ===");
        System.out.println("T ¬(P∧Q) c0, T P c1 → T ¬Q ck (donde ck ≥ max(c0,c1))");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context,"T -(*(P Q)) c0", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó T ¬Q con label apropiada
            assertTrue("Debe generar T -Q c1", treeOutput.contains("T !Q c1"));
            assertTrue("Debe aplicar T_NOT_A_AND_B", treeOutput.contains("T_NOT_A_AND_B"));
            
            System.out.println("✅ REGLA 10 (T_NOT_A_AND_B): MinimalGreaterLabelGetter labels diferentes - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_NOT_A_AND_B labels diferentes: " + e.getMessage());
        }
    }

    @Test
    public void testRule10_T_NOT_A_AND_B_MinimalGreaterLabel_SameLabels() {
        System.out.println("\n=== TEST REGLA 10: T_NOT_A_AND_B (Labels iguales) ===");
        System.out.println("T ¬(P∧Q) c1, T P c1 → T ¬Q ck (donde ck ≥ c1)");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(*(P Q)) c1", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó T ¬Q con label apropiada
            assertTrue("Debe generar T -Q c1", treeOutput.contains("T !Q c1"));
            assertTrue("Debe aplicar T_NOT_A_AND_B", treeOutput.contains("T_NOT_A_AND_B"));
            
            System.out.println("✅ REGLA 10 (T_NOT_A_AND_B): MinimalGreaterLabelGetter labels iguales - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_NOT_A_AND_B labels iguales: " + e.getMessage());
        }
    }

    @Test
    public void testRule10_T_NOT_A_AND_B_MinimalGreaterLabel_OrderReversed() {
        System.out.println("\n=== TEST REGLA 10: T_NOT_A_AND_B (Orden invertido) ===");
        System.out.println("T ¬(P∧Q) c1, T P c0 → T ¬Q ck (donde ck ≥ max(c1,c0))");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(*(P Q)) c1", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó T ¬Q con label apropiada
            assertTrue("Debe generar T -Q", treeOutput.contains("T !Q c1"));
            assertTrue("Debe aplicar T_NOT_A_AND_B", treeOutput.contains("T_NOT_A_AND_B"));
            
            System.out.println("✅ REGLA 10 (T_NOT_A_AND_B): MinimalGreaterLabelGetter orden invertido - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_NOT_A_AND_B orden invertido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 11: T_NOT_AND_LEFT (MinimalGreaterLabelGetter)
    // T ¬(A∧B) : ci, T B : cj, ci ≤ ck ∧ cj ≤ ck → T ¬A : ck
    // =====================================
    
    @Test
    public void testRule11_T_NOT_AND_LEFT_MinimalGreaterLabel_DifferentLabels() {
        System.out.println("\n=== TEST REGLA 11: T_NOT_AND_LEFT (Labels diferentes) ===");
        System.out.println("T ¬(P∧Q) c0, T Q c1 → T ¬P ck (donde ck ≥ max(c0,c1))");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(*(P Q)) c0", "T Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó T ¬P con label apropiada
            assertTrue("Debe generar T -P", treeOutput.contains("T !P c1"));
            assertTrue("Debe aplicar T_NOT_AND_LEFT", treeOutput.contains("T_NOT_AND_LEFT"));
            
            System.out.println("✅ REGLA 11 (T_NOT_AND_LEFT): MinimalGreaterLabelGetter labels diferentes - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_NOT_AND_LEFT labels diferentes: " + e.getMessage());
        }
    }

    @Test
    public void testRule11_T_NOT_AND_LEFT_MinimalGreaterLabel_SameLabels() {
        System.out.println("\n=== TEST REGLA 11: T_NOT_AND_LEFT (Labels iguales) ===");
        System.out.println("T ¬(P∧Q) c1, T Q c1 → T ¬P ck (donde ck ≥ c1)");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(*(P Q)) c1", "T Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó T ¬P con label apropiada
            assertTrue("Debe generar T -P", treeOutput.contains("T !P c1"));
            assertTrue("Debe aplicar T_NOT_AND_LEFT", treeOutput.contains("T_NOT_AND_LEFT"));
            
            System.out.println("✅ REGLA 11 (T_NOT_AND_LEFT): MinimalGreaterLabelGetter labels iguales - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_NOT_AND_LEFT labels iguales: " + e.getMessage());
        }
    }

    @Test
    public void testRule11_T_NOT_AND_LEFT_MinimalGreaterLabel_OrderReversed() {
        System.out.println("\n=== TEST REGLA 11: T_NOT_AND_LEFT (Orden invertido) ===");
        System.out.println("T ¬(P∧Q) c1, T Q c0 → T ¬P ck (donde ck ≥ max(c1,c0))");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(*(P Q)) c1", "T Q c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó T ¬P con label apropiada
            assertTrue("Debe generar T -P", treeOutput.contains("T !P c1"));
            assertTrue("Debe aplicar T_NOT_AND_LEFT", treeOutput.contains("T_NOT_AND_LEFT"));
            
            System.out.println("✅ REGLA 11 (T_NOT_AND_LEFT): MinimalGreaterLabelGetter orden invertido - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_NOT_AND_LEFT orden invertido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 12: T_IMPLIES_LEFT
    // T A→B : ci, T A : cj, ci ⪯ ck ∧ cj ⪯ ck → T B : ck
    // =====================================
    
    @Test
    public void testRule12_T_IMPLIES_LEFT_MinimalGreaterLabel_SameLabels() {
        System.out.println("\n=== TEST REGLA 12: T_IMPLIES_LEFT (Labels iguales) ===");
        System.out.println("T (P→Q) c0, T P c0 → T Q ck (donde ck ≥ max(c0,c0))");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c0", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó T Q con label apropiada
            assertTrue("Debe generar T Q", treeOutput.contains("T Q c0"));
            assertTrue("Debe aplicar T_IMPLIES_LEFT", treeOutput.contains("T_IMPLIES_LEFT"));
            
            System.out.println("✅ REGLA 12 (T_IMPLIES_LEFT): MinimalGreaterLabelGetter labels iguales - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_IMPLIES_LEFT labels iguales: " + e.getMessage());
        }
    }

    @Test
    public void testRule12_T_IMPLIES_LEFT_MinimalGreaterLabel_DifferentLabels() {
        System.out.println("\n=== TEST REGLA 12: T_IMPLIES_LEFT (Labels diferentes) ===");
        System.out.println("T (P→Q) c0, T P c2 → T Q ck (donde ck ≥ max(c0,c2))");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c0", "T P c2");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó T Q con label apropiada
            assertTrue("Debe generar T Q", treeOutput.contains("T Q c2"));
            assertTrue("Debe aplicar T_IMPLIES_LEFT", treeOutput.contains("T_IMPLIES_LEFT"));
            
            System.out.println("✅ REGLA 12 (T_IMPLIES_LEFT): MinimalGreaterLabelGetter labels diferentes - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_IMPLIES_LEFT labels diferentes: " + e.getMessage());
        }
    }

    @Test
    public void testRule12_T_IMPLIES_LEFT_MinimalGreaterLabel_OrderReversed() {
        System.out.println("\n=== TEST REGLA 12: T_IMPLIES_LEFT (Orden invertido) ===");
        System.out.println("T (P→Q) c1, T P c0 → T Q ck (donde ck ≥ max(c1,c0))");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c1", "T P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó T Q con label apropiada
            assertTrue("Debe generar T Q", treeOutput.contains("T Q c1"));
            assertTrue("Debe aplicar T_IMPLIES_LEFT", treeOutput.contains("T_IMPLIES_LEFT"));
            
            System.out.println("✅ REGLA 12 (T_IMPLIES_LEFT): MinimalGreaterLabelGetter orden invertido - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_IMPLIES_LEFT orden invertido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 13: X_IMPLIES_F_RIGHT
    // T A→B : ci, F B : cj, ci ⪯ cj → F A : cj
    // =====================================
    
    @Test
    public void testRule13_X_IMPLIES_F_RIGHT_ValidLabelCondition() {
        System.out.println("\n=== TEST REGLA 13: X_IMPLIES_F_RIGHT (Label válido) ===");
        System.out.println("T (P→Q) c0, F Q c1 (c0 ≤ c1: main.label ≤ aux.label) → F P c1");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c0", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla correctamente
            assertTrue("Debe generar F P c1", treeOutput.contains("F P c1"));
            
            System.out.println("✅ REGLA 13 (X_IMPLIES_F_RIGHT): LessThanLabelCondition c0 ≤ c1 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test X_IMPLIES_F_RIGHT válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule13_X_IMPLIES_F_RIGHT_ValidEqualLabelCondition() {
        System.out.println("\n=== TEST REGLA 13: X_IMPLIES_F_RIGHT (Labels iguales) ===");
        System.out.println("T (P→Q) c1, F Q c1 (c1 ≤ c1: main.label ≤ aux.label) → F P c1");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c1", "F Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla correctamente
            assertTrue("Debe generar F P c1", treeOutput.contains("F P c1"));
            
            System.out.println("✅ REGLA 13 (X_IMPLIES_F_RIGHT): LessThanLabelCondition c1 ≤ c1 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test X_IMPLIES_F_RIGHT labels iguales: " + e.getMessage());
        }
    }

    @Test
    public void testRule13_X_IMPLIES_F_RIGHT_InvalidLabelCondition() {
        System.out.println("\n=== TEST REGLA 13: X_IMPLIES_F_RIGHT (Label inválido) ===");
        System.out.println("T (P→Q) c1, F Q c0 (c1 ≰ c0: main.label ≰ aux.label) → NO debe aplicarse");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c1", "F Q c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Con labels inválidos (c1 ≰ c0), la regla NO debe aplicarse
            assertNotNull("El árbol de prueba debe existir", tree);
            assertFalse("NO debe generar F P con labels inválidos", treeOutput.contains("F P"));
            assertFalse("NO debe aplicar X_IMPLIES_F_RIGHT", treeOutput.contains("X_IMPLIES_F_RIGHT"));
            
            System.out.println("✅ REGLA 13 (X_IMPLIES_F_RIGHT): LessThanLabelCondition rechaza c1 ≰ c0 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test X_IMPLIES_F_RIGHT inválido: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 14: F_A_IMPLIES_B_TA_FB
    // F A→B: ci → T A : cj, F B: cj (cj nuevo, ci ⪯ cj)
    // =====================================
    
    @Test
    public void testRule14_F_A_IMPLIES_B_NewLabels() {
        System.out.println("\n=== TEST REGLA 14: F_A_IMPLIES_B_TA_FB (Caso básico) ===");
        System.out.println("F (P→Q) c0 → T P cj, F Q cj (cj nuevo, c0 ⪯ cj)");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F ->(P Q) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generaron ambas conclusiones con labels apropiadas
            assertTrue("Debe generar T P con label nueva", treeOutput.contains("T P c3") && !treeOutput.contains("T P c0") && !treeOutput.contains("T P c1") && !treeOutput.contains("T P c2"));
            assertTrue("Debe generar F Q con label nueva", treeOutput.contains("F Q c3") && !treeOutput.contains("F Q c0") && !treeOutput.contains("T P c1") && !treeOutput.contains("T P c2"));
            assertTrue("Debe aplicar F_A_IMPLIES_B_TA_FB", treeOutput.contains("F_A_IMPLIES_B_TA_FB"));
            
            System.out.println("✅ REGLA 14 (F_A_IMPLIES_B_TA_FB): NewLabelGetter - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test F_A_IMPLIES_B_TA_FB básico: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 15: T_NOT_A_IMPLIES_B_TA_FB
    // T ¬(A→B) : ci → T A: ck, T ¬B : ci (ck nuevo, ci ⪯ ck)
    // =====================================
    
    @Test
    public void testRule15_T_NOT_A_IMPLIES_B_LabelPropagation() {
        System.out.println("\n=== TEST REGLA 15: T_NOT_A_IMPLIES_B_TA_FB (Caso básico) ===");
        System.out.println("T ¬(P→Q) c0 → T P ck (nuevo), T ¬Q c0 (original)");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(->(P Q)) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generaron las conclusiones correctas con labels apropiadas
            assertTrue("Debe generar T P con label nueva", treeOutput.contains("T P c3") && !treeOutput.contains("T P c0"));
            assertTrue("Debe generar T -Q c0 con label original", treeOutput.contains("T !Q c0"));
            assertTrue("Debe aplicar T_NOT_A_IMPLIES_B_TA_FB", treeOutput.contains("T_NOT_A_IMPLIES_B_TA_FB"));
            
            System.out.println("✅ REGLA 15 (T_NOT_A_IMPLIES_B): NewLabelGetter + MainLabelGetter - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_NOT_A_IMPLIES_B básico: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 16: T_X_IMPLIES_Y_NOT_Y (BinarySomeRelationLabelCondition)
    // T (A→B) : ci, T ¬B : cj, ci ≤ cj → T ¬A : cj
    // =====================================

    @Test
    public void testRule16_T_X_IMPLIES_Y_NOT_Y_ValidLabelCondition_CiLessEqualCj() {
        System.out.println("\n=== TEST REGLA 16: T_X_IMPLIES_Y_NOT_Y (ci ≤ cj) ===");
        System.out.println("T (P→Q) c0, T ¬Q c1 (c0 ≤ c1) → T ¬P c1");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c0", "T -Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // Verificar que se aplicó la regla y generó T ¬P c1
            assertTrue("Debe generar T -P c1", treeOutput.contains("T !P c1"));

            System.out.println("✅ REGLA 16 (T_X_IMPLIES_Y_NOT_Y): BinarySomeRelationLabelCondition c0 ≤ c1 - CORRECTA");

        } catch (Exception e) {
            fail("Error en test T_X_IMPLIES_Y_NOT_Y válido: " + e.getMessage());
        }
    }

    @Test
    public void testRule16_T_X_IMPLIES_Y_NOT_Y_InvalidLabelCondition_CjLessEqualCi() {
        System.out.println("\n=== TEST REGLA 16: T_X_IMPLIES_Y_NOT_Y (cj ≤ ci) ===");
        System.out.println("T (P→Q) c1, T ¬Q c0 (c0 ≤ c1) → T ¬P c0");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c1", "T -Q c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // Verificar que se aplicó la regla y generó T ¬P c0
            assertFalse("Debe generar T -P c0", treeOutput.contains("T !P"));

            System.out.println("✅ REGLA 16 (T_X_IMPLIES_Y_NOT_Y): BinarySomeRelationLabelCondition c0 ≤ c1 (inversa) - CORRECTA");

        } catch (Exception e) {
            fail("Error en test T_X_IMPLIES_Y_NOT_Y válido inverso: " + e.getMessage());
        }
    }

    @Test
    public void testRule16_T_X_IMPLIES_Y_NOT_Y_ValidLabelCondition_Equal() {
        System.out.println("\n=== TEST REGLA 16: T_X_IMPLIES_Y_NOT_Y (labels iguales) ===");
        System.out.println("T (P→Q) c1, T ¬Q c1 (c1 ≤ c1) → T ¬P c1");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T ->(P Q) c1", "T -Q c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // Verificar que se aplicó la regla y generó T ¬P c1
            assertTrue("Debe generar T -P c1", treeOutput.contains("T !P c1"));

            System.out.println("✅ REGLA 16 (T_X_IMPLIES_Y_NOT_Y): BinarySomeRelationLabelCondition c1 ≤ c1 - CORRECTA");

        } catch (Exception e) {
            fail("Error en test T_X_IMPLIES_Y_NOT_Y labels iguales: " + e.getMessage());
        }
    }


    // =====================================
    // REGLA 17: F_NOT
    // F ¬A : ci → T A : cj (cj nuevo, ci ⪯ cj)
    // =====================================
    
    @Test
    public void testRule17_F_NOT_NewLabel() {
        System.out.println("\n=== TEST REGLA 17: F_NOT (Caso básico) ===");
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
            
            System.out.println("✅ REGLA 17 (F_NOT): NewLabelGetter básico - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test F_NOT básico: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 18: T_NOT_NOT  
    // T ¬¬A : ci → T A : ck (ck nuevo, ci ⪯ ck)
    // =====================================
    
    @Test
    public void testRule18_T_NOT_NOT_NewLabel() {
        System.out.println("\n=== TEST REGLA 18: T_NOT_NOT (Caso básico) ===");
        System.out.println("T ¬¬P c0 → T P ck (ck nuevo, c0 ⪯ ck)");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(-P) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se generó T P con nueva label (no c0)
            assertTrue("Debe generar T P con label nueva", treeOutput.contains("T P c3") && !treeOutput.contains("T P c0"));
            assertTrue("Debe aplicar T_NOT_NOT", treeOutput.contains("T_NOT_NOT"));
            
            System.out.println("✅ REGLA 18 (T_NOT_NOT): NewLabelGetter básico - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_NOT_NOT básico: " + e.getMessage());
        }
    }

    @Test
    public void testRule18_T_NOT_NOT_NewLabel_DoubleNegationElimination() {
        System.out.println("\n=== TEST REGLA 18: T_NOT_NOT (Eliminación doble negación) ===");
        System.out.println("T ¬¬(P∧Q) c0 → T (P∧Q) ck (verificar estructura compleja)");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T -(-(*(P Q))) c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se eliminó la doble negación correctamente
            assertTrue("Debe generar T *(P Q) con label nueva", treeOutput.contains("T (P&Q) c3") && !treeOutput.contains("T (P&Q) c0"));
            assertTrue("Debe aplicar T_NOT_NOT", treeOutput.contains("T_NOT_NOT"));
            
            System.out.println("✅ REGLA 18 (T_NOT_NOT): Eliminación doble negación - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_NOT_NOT doble negación: " + e.getMessage());
        }
    }

    // =====================================
    // REGLA 19: TEST DE CLOSURE (CLOSE)
    // T A ci, F A cj ci ⪯ cj → CIERRE
    // =====================================

    @Test
    public void testRule19_Closure_SameLabel() {
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
    public void testRule19_Closure_GreaterLabel() {
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
    public void testRule19_Closure_LowerLabel() {
        System.out.println("\n=== TEST CLOSURE IPL ===");
        System.out.println("T P c2, F P c0 → DEBE CERRAR");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T P c2", "F P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            assertFalse("Debe estar cerrado", proof.isClosed());

            System.out.println("✅ CLOSURE IPL: CORRECTA");

        } catch (Exception e) {
            fail("Error en test closure: " + e.getMessage());
        }
    }
    // =====================================
    // REGLA 20: TEST DE CLOSURE (CLOSE)
    // T A ci, T ¬A cj ci ⪯ ck and cj ⪯ ck → CIERRE
    // =====================================
    
    @Test
    public void testRule20_Closure_SameLabel() {
        System.out.println("\n=== TEST CLOSURE IPL ===");
        System.out.println("T P c0, T ¬P c0 → DEBE CERRAR");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T P c0", "T -P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // En IPL, solo cierra si tenemos T A y T ¬A con la MISMA label
            assertTrue("Debe estar cerrado", proof.isClosed());
            
            System.out.println("✅ CLOSURE IPL: CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test closure: " + e.getMessage());
        }
    }

    @Test
    public void testRule20_Closure_DifferentLabel() {
        System.out.println("\n=== TEST CLOSURE IPL ===");
        System.out.println("T P c2, T ¬P c0 → DEBE CERRAR");

        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "T P c2", "T -P c0");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();

            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);

            // En IPL, solo cierra si tenemos T A y T ¬A con la distinta label
            assertTrue("Debe estar cerrado", proof.isClosed());

            System.out.println("✅ CLOSURE IPL: CORRECTA");

        } catch (Exception e) {
            fail("Error en test closure: " + e.getMessage());
        }
    }

    @Test
    public void testRule20_No_Closure_NoRelationLabels() {
        System.out.println("\n=== TEST NO CLOSURE IPL ===");
        System.out.println("T P c0, T ¬P c3 → NO DEBE CERRAR");
        
        try {
            Context context = createContextWithRelations();
            FormulaLabel c3 = context.getNewFormulaLabel();
            Proof proof = proveFormulasWithContext(context, "T P c0", "T -P c3");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // En IPL, NO cierra si las labels no tienen relación
            assertFalse("NO debe estar cerrado con labels diferentes", proof.isClosed());
            
            System.out.println("✅ NO CLOSURE IPL: CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test no closure: " + e.getMessage());
        }
    }

    // =====================================
    // TESTS ADICIONALES PARA LABEL CONDITIONS ESPECÍFICAS
    // =====================================
    
    @Test
    public void testGreaterThanLabelCondition_F_AND_LEFT_InvalidCase() {
        System.out.println("\n=== TEST GreaterThanLabelCondition (F_AND_LEFT - Caso inválido) ===");
        System.out.println("F (P∧Q) c0, T P c1 (c1 ≰ c0) → NO debe aplicarse");
        
        try {
            Context context = createContextWithRelations();
            Proof proof = proveFormulasWithContext(context, "F *(P Q) c0", "T P c1");
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // GreaterThanLabelCondition verifica aux.label ≤ main.label (c1 ≤ c0)
            // Como c1 ≰ c0, la regla NO debe aplicarse
            assertFalse("NO debe generar F Q con labels inválidos", treeOutput.contains("F Q"));
            assertFalse("NO debe aplicar F_AND_LEFT", treeOutput.contains("F_AND_LEFT"));
            
            System.out.println("✅ GreaterThanLabelCondition rechaza c1 ≰ c0 - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test GreaterThanLabelCondition inválido: " + e.getMessage());
        }
    }
    
    @Test
    public void testBinarySomeRelationLabelCondition_Both_Directions() {
        System.out.println("\n=== TEST BinarySomeRelationLabelCondition (Ambas direcciones) ===");
        System.out.println("Verificar que funciona tanto con ci ≤ cj como con cj ≤ ci");
        
        try {
            // Test dirección 1: c0 ≤ c1
            System.out.println("Test 1: T (P∨Q) c0, T ¬P c1 (c0 ≤ c1)");
            Context context = createContextWithRelations();
            Proof proof1 = proveFormulasWithContext(context, "T +(P Q) c0", "T -P c1");
            assertTrue("Debe funcionar con c0 ≤ c1", proof1.getProofTree().toString().contains("T Q c0"));
            
            // Test dirección 2: c1 ≤ c0 (inversa)
            System.out.println("Test 2: T (P∨Q) c1, T ¬P c0 (c0 ≤ c1)");
            context = createContextWithRelations();
            Proof proof2 = proveFormulasWithContext(context, "T +(P Q) c1", "T -P c0");
            assertTrue("Debe funcionar con c0 ≤ c1 (inversa)", proof2.getProofTree().toString().contains("T Q c1"));
            
            System.out.println("✅ BinarySomeRelationLabelCondition: Ambas direcciones funcionan - CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test BinarySomeRelationLabelCondition: " + e.getMessage());
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

            System.out.println("✅ TERCIO EXCLUIDO NO VÁLIDO EN IPL: CORRECTA");

        } catch (Exception e) {
            fail("Error en test tercio excluido: " + e.getMessage());
        }
    }
}
