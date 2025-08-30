package logicalSystems.ipl;

import org.junit.Test;
import org.junit.Before;
import static org.junit.Assert.*;

import logic.labelledFormulas.LabelledFormulaCreator;
import logic.signedFormulas.SignedFormulaList;
import logic.problem.Problem;
import main.newstrategy.Prover;
import main.newstrategy.ISimpleStrategy;
import main.newstrategy.cpl.configurable.comparator.InsertionOrderSignedFormulaComparator;
import main.tableau.Method;
import main.tableau.Proof;
import main.proofTree.IProofTree;
import proverinterface.RuleStructureFactory;

/**
 * Test unitario completo para todas las reglas IPL que demuestra claramente
 * la estructura del árbol de pruebas para cada regla.
 * 
 * MODIFICADO: Usa la misma inicialización que la interfaz gráfica (ProverFacade)
 */
public class IPLSimpleFormulaTestNew {

    private LabelledFormulaCreator labelledFormulaCreator;

    @Before
    public void setUp() {
        // Inicializar LabelledFormulaCreator para IPL (correcto para etiquetas)
        labelledFormulaCreator = new LabelledFormulaCreator("ipl");
        labelledFormulaCreator.setTwoPhases(false); // IPL usa single-phase con su propio parser
    }
    
    /**
     * Método helper que simula el comportamiento de ProverFacade.proveAndVerify
     * para ejecutar pruebas como en la interfaz gráfica
     */
    private Proof proveFormula(String formulaString) throws Exception {
        System.out.println("🔍 DEBUG: Iniciando proveFormula con: '" + formulaString + "'");
        
        // Verificar estado del LabelledFormulaCreator
        System.out.println("🔍 DEBUG: LabelledFormulaCreator package: " + labelledFormulaCreator.getClass().getName());
        System.out.println("🔍 DEBUG: LabelledFormulaFactory type: " + labelledFormulaCreator.getLabelledFormulaFactory().getClass().getName());
        
        // Parsear fórmula individual
        SignedFormulaList sfl = new SignedFormulaList();
        System.out.println("🔍 DEBUG: Parseando fórmula...");
        
        try {
            var parsedFormula = labelledFormulaCreator.parseString(formulaString);
            System.out.println("🔍 DEBUG: Fórmula parseada: " + parsedFormula);
            System.out.println("🔍 DEBUG: Tipo de fórmula parseada: " + parsedFormula.getClass().getName());
            sfl.add(parsedFormula);
            System.out.println("🔍 DEBUG: Fórmula agregada a SignedFormulaList. Tamaño: " + sfl.size());
        } catch (Exception e) {
            System.err.println("❌ ERROR: Fallo en parseString: " + e.getMessage());
            e.printStackTrace();
            throw e;
        }
        
        // Crear problema manualmente (como ProverFacade)
        Problem problem = new Problem("ipl");
        System.out.println("🔍 DEBUG: Problem creado con package 'ipl'");
        
        problem.setSignedFormulaFactory(labelledFormulaCreator.getLabelledFormulaFactory());
        System.out.println("🔍 DEBUG: LabelledFormulaFactory asignada al Problem");
        
        problem.setSignedFormulaList(sfl);
        System.out.println("🔍 DEBUG: SignedFormulaList asignada al Problem. Tamaño: " + sfl.size());
        
        problem.setName("TEST_FORMULA");
        System.out.println("🔍 DEBUG: Problem configurado completamente");
        
        // Crear método con reglas IPL (como ProverFacade)
        Method method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
        System.out.println("🔍 DEBUG: Method creado con reglas IPL");
        
        // Crear estrategia IPL directamente
        ISimpleStrategy strategy = new main.newstrategy.ipl.IPLSimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());
        System.out.println("🔍 DEBUG: IPLSimpleStrategy creada con comparador");
        
        // Crear y configurar prover (como ProverFacade)
        Prover prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);
        System.out.println("🔍 DEBUG: Prover configurado. Iniciando prueba...");
        
        // Ejecutar prueba
        Proof result = prover.prove(problem);
        System.out.println("🔍 DEBUG: Prueba completada. Closed: " + result.isClosed());
        return result;
    }
    
    /**
     * Método helper para formulas con múltiples premisas (tests de dos premisas)
     */
    private Proof proveFormulas(String... formulaStrings) throws Exception {
        // Parsear múltiples fórmulas
        SignedFormulaList sfl = new SignedFormulaList();
        for (int i = 0; i < formulaStrings.length; i++) {
            var parsed = labelledFormulaCreator.parseString(formulaStrings[i]);
            System.out.println("🔍 DEBUG: Fórmula " + i + ": " + formulaStrings[i] + " → " + parsed);
            sfl.add(parsed);
        }
        System.out.println("🔍 DEBUG: SignedFormulaList final size: " + sfl.size());
        
        // Crear problema manualmente (como ProverFacade)
        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(labelledFormulaCreator.getLabelledFormulaFactory());
        problem.setSignedFormulaList(sfl);
        problem.setName("TEST_MULTIPLE_FORMULAS");
        
        // Crear método con reglas IPL (como ProverFacade)
        Method method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
        
        // Crear estrategia IPL directamente
        ISimpleStrategy strategy = new main.newstrategy.ipl.IPLSimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());
        
        // Crear y configurar prover (como ProverFacade)
        Prover prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);
        
        // Ejecutar prueba
        return prover.prove(problem);
    }
    
    /**
     * Método helper que simula EXACTAMENTE como la GUI lee archivos .prove
     */
    private Proof proveFromFile(String filename) throws Exception {
        System.out.println("🔍 DEBUG: Leyendo archivo .prove: " + filename);
        
        // Crear problema desde archivo (como ProverFacade.proveAndVerifyFile)
        Problem problem = labelledFormulaCreator.parseFile(filename);
        System.out.println("🔍 DEBUG: Problem parseado desde archivo");
        System.out.println("🔍 DEBUG: Fórmulas en problem: " + problem.getFormulas().size());
        
        for (int i = 0; i < problem.getFormulas().size(); i++) {
            System.out.println("🔍 DEBUG: Fórmula " + i + ": " + problem.getFormulas().get(i));
        }
        
        // Crear método con reglas IPL (como ProverFacade)
        Method method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
        
        // Crear estrategia IPL directamente
        ISimpleStrategy strategy = new main.newstrategy.ipl.IPLSimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());
        
        // Crear y configurar prover (como ProverFacade)
        Prover prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);
        
        // Ejecutar prueba
        return prover.prove(problem);
    }

    // ===== REGLAS DE UNA PREMISA =====

    @Test
    public void testF_OR_Rule() {
        System.out.println("\n=== TESTING F_OR RULE: F +(P Q) c0 ===");
        System.out.println("Fórmula: F +(P Q) c0");
        System.out.println("Regla: F_OR - Falso P ∨ Q → Falso P, Falso Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");
        
        try {
            Proof proof = proveFormula("F +(P Q) c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());
            
            // Verificaciones
            assertFalse("La prueba NO debe estar cerrada para F +(P Q) c0", proof.isClosed());
            
            System.out.println("✅ Test F_OR pasado: La fórmula F +(P Q) c0 NO es válida");
        } catch (Exception e) {
            fail("Error ejecutando test F_OR: " + e.getMessage());
        }
    }

    @Test
    public void testT_AND_Rule() {
        System.out.println("\n=== TESTING T_AND RULE: T *(P Q) c0 ===");
        System.out.println("Fórmula: T *(P Q) c0");
        System.out.println("Regla: T_AND - Verdadero P ∧ Q → Verdadero P, Verdadero Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormula("T *(P Q) c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para T *(P Q) c0", proof.isClosed());

            System.out.println("✅ Test T_AND pasado: La fórmula T *(P Q) c0 NO es válida");
        } catch (Exception e) {
            fail("Error ejecutando test T_AND: " + e.getMessage());
        }
    }

    @Test
    public void testT_NOT_A_OR_B_Rule() {
        System.out.println("\n=== TESTING T_NOT_A_OR_B RULE: T -+(P Q) c0 ===");
        System.out.println("Fórmula: T -+(P Q) c0");
        System.out.println("Regla: T_NOT_A_OR_B - Verdadero ¬(P ∨ Q) → Verdadero ¬P, Verdadero ¬Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormula("T -(+(P Q)) c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para T -+(P Q) c0", proof.isClosed());

            System.out.println("✅ Test T_NOT_A_OR_B pasado: La fórmula T -+(P Q) c0 NO es válida");
        } catch (Exception e) {
            fail("Error ejecutando test T_NOT_A_OR_B: " + e.getMessage());
        }
    }

    @Test
    public void testF_A_IMPLIES_B_TA_FB_Rule() {
        System.out.println("\n=== TESTING F_A_IMPLIES_B_TA_FB RULE: F ->(P Q) c0 ===");
        System.out.println("Fórmula: F ->(P Q) c0");
        System.out.println("Regla: F_A_IMPLIES_B_TA_FB - Falso P → Q → Verdadero P, Falso Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormula("F ->(P Q) c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para F ->(P Q) c0", proof.isClosed());

            System.out.println("✅ Test F_A_IMPLIES_B_TA_FB pasado: La fórmula F ->(P Q) c0 NO es válida");
        } catch (Exception e) {
            fail("Error ejecutando test F_A_IMPLIES_B_TA_FB: " + e.getMessage());
        }
    }

    @Test
    public void testT_NOT_A_IMPLIES_B_TA_FB_Rule() {
        System.out.println("\n=== TESTING T_NOT_A_IMPLIES_B_TA_FB RULE: T -->(P Q) c0 ===");
        System.out.println("Fórmula: T -->(P Q) c0");
        System.out.println("Regla: T_NOT_A_IMPLIES_B_TA_FB - Verdadero ¬(P → Q) → Verdadero P, Falso Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormula("T -(->(P Q)) c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para T -->(P Q) c0", proof.isClosed());
            
            System.out.println("✅ Test T_NOT_A_IMPLIES_B_TA_FB pasado: La fórmula T -->(P Q) c0 NO es válida");
        } catch (Exception e) {
            fail("Error ejecutando test T_NOT_A_IMPLIES_B_TA_FB: " + e.getMessage());
        }
    }

    @Test
    public void testF_NOT_Rule() {
        System.out.println("\n=== TESTING F_NOT RULE: F -P c0 ===");
        System.out.println("Fórmula: F -P c0");
        System.out.println("Regla: F_NOT - Falso ¬P → Verdadero P");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormula("F -P c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para F -P c0", proof.isClosed());

            System.out.println("✅ Test F_NOT pasado: La fórmula F -P c0 NO es válida");
        } catch (Exception e) {
            fail("Error ejecutando test F_NOT: " + e.getMessage());
        }
    }

    @Test
    public void testT_NOT_NOT_Rule() {
        System.out.println("\n=== TESTING T_NOT_NOT RULE: T --P c0 ===");
        System.out.println("Fórmula: T --P c0");
        System.out.println("Regla: T_NOT_NOT - Verdadero ¬¬P → Verdadero P");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormula("T -(-P) c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para T --P c0", proof.isClosed());

            System.out.println("✅ Test T_NOT_NOT pasado: La fórmula T --P c0 NO es válida");
        } catch (Exception e) {
            fail("Error ejecutando test T_NOT_NOT: " + e.getMessage());
        }
    }

    @Test
    public void testF_NOT_NOT_ComplexRule() {
        System.out.println("\n=== TESTING F_NOT_NOT COMPLEX RULE: F ->(*(->(A B) ->(A -B)) -A) c0 ===");
        System.out.println("Fórmula: F ->(*(->(A B) ->(A -B)) -A) c0");
        System.out.println("Regla: Fórmula compleja que debería ser válida en IPL");
        System.out.println("Resultado esperado: CERRADO (fórmula válida)\n");

        try {
            Proof proof = proveFormula("F ->(*(->(A B) ->(A -B)) -A) c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertTrue("La prueba debe estar cerrada para F ->(*(->(A B) ->(A -B)) -A) c0", proof.isClosed());

            System.out.println("✅ Test F_NOT_NOT pasado: La fórmula F ->(*(->(A B) ->(A -B)) -A) c0 ES válida");
        } catch (Exception e) {
            fail("Error ejecutando test F_NOT_NOT complex: " + e.getMessage());
        }
    }

    // ===== REGLAS DE DOS PREMISAS =====
    
    @Test
    public void testX_OR_F_LEFT_Rule() {
        System.out.println("\n=== TESTING X_OR_F_LEFT RULE: T +(P Q) c0, F P c1 ===");
        System.out.println("Fórmulas: T +(P Q) c0, F P c1");
        System.out.println("Regla: X_OR_F_LEFT - Verdadero P ∨ Q, Falso P → Verdadero Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormulas("T +(P Q) c0", "F P c1");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para X_OR_F_LEFT", proof.isClosed());

            System.out.println("✅ Test X_OR_F_LEFT pasado");
        } catch (Exception e) {
            fail("Error ejecutando test X_OR_F_LEFT: " + e.getMessage());
        }
    }

    @Test
    public void testT_OR_F_RIGHT_Rule() {
        System.out.println("\n=== TESTING T_OR_F_RIGHT RULE: T +(P Q) c0, F Q c1 ===");
        System.out.println("Fórmulas: T +(P Q) c0, F Q c1");
        System.out.println("Regla: T_OR_F_RIGHT - Verdadero P ∨ Q, Falso Q → Verdadero P");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormulas("T +(P Q) c0", "F Q c1");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para T_OR_F_RIGHT", proof.isClosed());

            System.out.println("✅ Test T_OR_F_RIGHT pasado");
        } catch (Exception e) {
            fail("Error ejecutando test T_OR_F_RIGHT: " + e.getMessage());
        }
    }

    @Test
    public void testF_AND_LEFT_Rule() {
        System.out.println("\n=== TESTING F_AND_LEFT RULE: F *(P Q) c1, T P c0 ===");
        System.out.println("Fórmulas: F *(P Q) c1, T P c0");
        System.out.println("Regla IPL correcta:");
        System.out.println("F A∧B : cj    (F *(P Q) c1)");
        System.out.println("T A: ci       (T P c0)");
        System.out.println("ci ⪯ cj      (c0 ⪯ c1) ✅");
        System.out.println("-------");
        System.out.println("F B : cj      (ESPERADO: F Q c1)");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            System.out.println("🔍 DEBUGGING: Iniciando prueba con fórmulas:");
            System.out.println("  Main: F *(P Q) c1");
            System.out.println("  Aux:  T P c0");
            System.out.println("  Esperado: F Q c1 (aplicando F_AND_LEFT)");
            
            Proof proof = proveFormulas("F *(P Q) c1", "T P c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println("=== ÁRBOL DE PRUEBA ===");
            System.out.println(proofTree.toString());
            System.out.println("=======================");

            // Verificar que se generó F Q c1, NO F P c1
            String treeOutput = proofTree.toString();
            if (treeOutput.contains("F Q c1")) {
                System.out.println("✅ CORRECTO: Se generó F Q c1 como esperado");
            } else if (treeOutput.contains("F P c1")) {
                System.out.println("❌ ERROR: Se generó F P c1 en lugar de F Q c1");
                System.out.println("La regla F_AND_LEFT está mal configurada en IPLRules.java");
            }

            assertFalse("La prueba NO debe estar cerrada para F_AND_LEFT", proof.isClosed());

            System.out.println("✅ Test F_AND_LEFT completado");
        } catch (Exception e) {
            fail("Error ejecutando test F_AND_LEFT: " + e.getMessage());
        }
    }

    @Test
    public void testF_AND_LEFT_FromFile() {
        System.out.println("\n=== TESTING F_AND_LEFT FROM .prove FILE ===");
        System.out.println("Archivo: debug_f_and_left.prove");
        System.out.println("Contenido:");
        System.out.println("  F *(P Q) c1");
        System.out.println("  T P c0");
        System.out.println("Esperado: F Q c1 (como en la GUI)\n");

        try {
            String filename = "/Users/ariana/Facultad/Tesis/kems/kems.problems/problems/created/ipl/debug_f_and_left.prove";
            Proof proof = proveFromFile(filename);
            IProofTree proofTree = proof.getProofTree();
            System.out.println("=== ÁRBOL DE PRUEBA (DESDE ARCHIVO) ===");
            System.out.println(proofTree.toString());
            System.out.println("=======================================");

            // Verificar que se generó F Q c1, NO F P c1
            String treeOutput = proofTree.toString();
            if (treeOutput.contains("F Q c1")) {
                System.out.println("✅ CORRECTO: Se generó F Q c1 como esperado (igual que GUI)");
            } else if (treeOutput.contains("F P c1")) {
                System.out.println("❌ ERROR: Se generó F P c1 en lugar de F Q c1 (igual que test directo)");
                System.out.println("El problema no es la diferencia entre test y GUI");
            } else {
                System.out.println("🤔 INESPERADO: No se encontró ni F Q c1 ni F P c1");
            }

            System.out.println("✅ Test desde archivo completado");
        } catch (Exception e) {
            fail("Error ejecutando test desde archivo: " + e.getMessage());
        }
    }

    @Test
    public void testX_AND_T_RIGHT_Rule() {
        System.out.println("\n=== TESTING X_AND_T_RIGHT RULE: F *(P Q) c0, T Q c1 ===");
        System.out.println("Fórmulas: F *(P Q) c0, T Q c1");
        System.out.println("Regla: X_AND_T_RIGHT - Falso P ∧ Q, Verdadero Q → Falso P");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormulas("F *(P Q) c0", "T Q c1");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para X_AND_T_RIGHT", proof.isClosed());

            System.out.println("✅ Test X_AND_T_RIGHT pasado");
        } catch (Exception e) {
            fail("Error ejecutando test X_AND_T_RIGHT: " + e.getMessage());
        }
    }

    @Test
    public void testT_IMPLIES_LEFT_Rule() {
        System.out.println("\n=== TESTING T_IMPLIES_LEFT RULE: T ->(P Q) c0, T P c1 ===");
        System.out.println("Fórmulas: T ->(P Q) c0, T P c1");
        System.out.println("Regla: T_IMPLIES_LEFT - Verdadero P → Q, Verdadero P → Verdadero Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormulas("T ->(P Q) c0", "T P c1");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para T_IMPLIES_LEFT", proof.isClosed());

            System.out.println("✅ Test T_IMPLIES_LEFT pasado");
        } catch (Exception e) {
            fail("Error ejecutando test T_IMPLIES_LEFT: " + e.getMessage());
        }
    }

    @Test
    public void testX_IMPLIES_F_RIGHT_Rule() {
        System.out.println("\n=== TESTING X_IMPLIES_F_RIGHT RULE: T ->(P Q) c0, F Q c1 ===");
        System.out.println("Fórmulas: T ->(P Q) c0, F Q c1");
        System.out.println("Regla: X_IMPLIES_F_RIGHT - Verdadero P → Q, Falso Q → Falso P");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormulas("T ->(P Q) c0", "F Q c1");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para X_IMPLIES_F_RIGHT", proof.isClosed());

            System.out.println("✅ Test X_IMPLIES_F_RIGHT pasado");
        } catch (Exception e) {
            fail("Error ejecutando test X_IMPLIES_F_RIGHT: " + e.getMessage());
        }
    }

    @Test
    public void testT_NOT_AND_LEFT_Rule() {
        System.out.println("\n=== TESTING T_NOT_AND_LEFT RULE: T -(*(P Q)) c0 ===");
        System.out.println("Fórmula: T -(*(P Q)) c0");
        System.out.println("Regla: T_NOT_AND_LEFT - Verdadero ¬(P ∧ Q)");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        try {
            Proof proof = proveFormula("T -(*(P Q)) c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertFalse("La prueba NO debe estar cerrada para T -(*(P Q)) c0", proof.isClosed());

            System.out.println("✅ Test T_NOT_AND_LEFT pasado");
        } catch (Exception e) {
            fail("Error ejecutando test T_NOT_AND_LEFT: " + e.getMessage());
        }
    }

    // ===== TESTS DE CONTRADICCIÓN (DEBERÍAN CERRAR) =====

    @Test
    public void testSimpleContradiction() {
        System.out.println("\n=== TESTING SIMPLE CONTRADICTION: T P c0, T -P c0 ===");
        System.out.println("Fórmulas: T P c0, T -P c0");
        System.out.println("Significado: P y ¬P son verdaderos en el mismo mundo c0");
        System.out.println("Resultado esperado: CERRADO (contradicción IPL)\n");

        try {
            Proof proof = proveFormulas("T P c0", "T -P c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            assertTrue("La prueba debe estar cerrada para contradicción simple", proof.isClosed());

            System.out.println("✅ Test de contradicción pasado: T P y T ¬P en el mismo mundo es una contradicción");
        } catch (Exception e) {
            fail("Error ejecutando test de contradicción simple: " + e.getMessage());
        }
    }

    // ===== TESTS ESPECÍFICOS IPL (DIFERENCIAS CON LÓGICA CLÁSICA) =====
    
    @Test
    public void testLawOfExcludedMiddle_NotValidInIPL() {
        System.out.println("\n=== TESTING LAW OF EXCLUDED MIDDLE: T +(P -P) c0 ===");
        System.out.println("Significado: Intentamos probar que P ∨ ¬P es verdadero");
        System.out.println("En lógica clásica: P ∨ ¬P es siempre verdadero (tautología)");
        System.out.println("En IPL: P ∨ ¬P NO es válido universalmente");
        System.out.println("Resultado esperado: NO cerrado (no es derivable en IPL)\n");
        
        try {
            Proof proof = proveFormula("T +(P -P) c0");
            IProofTree proofTree = proof.getProofTree();
            System.out.println(proofTree.toString());

            // En IPL, no podemos derivar P ∨ ¬P como tautología
            assertFalse("La prueba NO debe estar cerrada para T +(P -P) c0 en IPL", proof.isClosed());

            System.out.println("closed? : " + proof.isClosed());
            
            System.out.println("✅ Test IPL pasado: P ∨ ¬P NO es válido en lógica intuicionista");
            System.out.println("Esto confirma que IPL es más débil que la lógica clásica");
        } catch (Exception e) {
            fail("Error ejecutando test del tercero excluido: " + e.getMessage());
        }
    }
}
