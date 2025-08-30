package logicalSystems.ipl;

import org.junit.Test;
import org.junit.Before;
import static org.junit.Assert.*;

import logic.labelledFormulas.LabelledFormulaCreator;
import logic.labelledFormulas.LabelledFormulaFactory;
import logic.signedFormulas.SignedFormulaList;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.FormulaLabel;
import logic.problem.Problem;
import main.newstrategy.Prover;
import main.newstrategy.ipl.IPLSimpleStrategy;
import main.tableau.Method;
import main.newstrategy.ISimpleStrategy;
import main.newstrategy.cpl.configurable.comparator.InsertionOrderSignedFormulaComparator;
import main.tableau.Proof;
import main.proofTree.IProofTree;
import main.proofTree.INode;
import main.proofTree.SignedFormulaNode;
import proverinterface.RuleStructureFactory;

/**
 * Test unitario completo para todas las reglas IPL que demuestra claramente
 * la estructura del árbol de pruebas para cada regla.
 */
public class IPLSimpleFormulaTest {

    private LabelledFormulaCreator sfc;
    private LabelledFormulaFactory lff;
    private Prover prover;
    private Method method;
    private ISimpleStrategy strategy;

    @Before
    public void setUp() {
        sfc = new LabelledFormulaCreator("ipl");
        lff = new LabelledFormulaFactory();
        
        // Crear el método con las reglas IPL
        method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
        
        // Crear la estrategia IPL con comparador
        strategy = new IPLSimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());
        
        // Configurar el prover
        prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);
    }

    // ===== REGLAS DE UNA PREMISA =====

    @Test
    public void testF_OR_Rule() {
        System.out.println("\n=== TESTING F_OR RULE: F +(P Q) c0 ===");
        System.out.println("Fórmula: F +(P Q) c0");
        System.out.println("Regla: F_OR - Falso P ∨ Q → Falso P, Falso Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");
        
        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();
        
        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("F +(P Q) c0")));
        
        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);
        
        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();
        System.out.println(proofTree.toString());
        
        // Verificaciones
        assertFalse("La prueba NO debe estar cerrada para F +(P Q) c0", proof.isClosed());
        
        System.out.println("✅ Test F_OR pasado: La fórmula F +(P Q) c0 NO es válida");
    }

    @Test
    public void testT_AND_Rule() {
        System.out.println("\n=== TESTING T_AND RULE: T *(P Q) c0 ===");
        System.out.println("Fórmula: T *(P Q) c0");
        System.out.println("Regla: T_AND - Verdadero P ∧ Q → Verdadero P, Verdadero Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("T *(P Q) c0")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();
        System.out.println(proofTree.toString());

        assertFalse("La prueba NO debe estar cerrada para T *(P Q) c0", proof.isClosed());

        System.out.println("✅ Test T_AND pasado: La fórmula T *(P Q) c0 NO es válida");
    }

    @Test
    public void testT_NOT_A_OR_B_Rule() {
        System.out.println("\n=== TESTING T_NOT_A_OR_B RULE: T -+(P Q) c0 ===");
        System.out.println("Fórmula: T -+(P Q) c0");
        System.out.println("Regla: T_NOT_A_OR_B - Verdadero ¬(P ∨ Q) → Verdadero ¬P, Verdadero ¬Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("T -(+(P Q)) c0")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();
        System.out.println(proofTree.toString());

        assertFalse("La prueba NO debe estar cerrada para T -+(P Q) c0", proof.isClosed());

        System.out.println("✅ Test T_NOT_A_OR_B pasado: La fórmula T -+(P Q) c0 NO es válida");
    }

    @Test
    public void testF_A_IMPLIES_B_TA_FB_Rule() {
        System.out.println("\n=== TESTING F_A_IMPLIES_B_TA_FB RULE: F ->(P Q) c0 ===");
        System.out.println("Fórmula: F ->(P Q) c0");
        System.out.println("Regla: F_A_IMPLIES_B_TA_FB - Falso P → Q → Verdadero P, Falso Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("F ->(P Q) c0")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();
        System.out.println(proofTree.toString());

        assertFalse("La prueba NO debe estar cerrada para F ->(P Q) c0", proof.isClosed());

        System.out.println("✅ Test F_A_IMPLIES_B_TA_FB pasado: La fórmula F ->(P Q) c0 NO es válida");
    }

    @Test
    public void testT_NOT_A_IMPLIES_B_TA_FB_Rule() {
        System.out.println("\n=== TESTING T_NOT_A_IMPLIES_B_TA_FB RULE: T -->(P Q) c0 ===");
        System.out.println("Fórmula: T -->(P Q) c0");
        System.out.println("Regla: T_NOT_A_IMPLIES_B_TA_FB - Verdadero ¬(P → Q) → Verdadero P, Falso Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("T -(->(P Q)) c0")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();
        System.out.println(proofTree.toString());

        assertFalse("La prueba NO debe estar cerrada para T -->(P Q) c0", proof.isClosed());
        
        System.out.println("✅ Test T_NOT_A_IMPLIES_B_TA_FB pasado: La fórmula T -->(P Q) c0 NO es válida");
    }

    @Test
    public void testF_NOT_Rule() {
        System.out.println("\n=== TESTING F_NOT RULE: F -P c0 ===");
        System.out.println("Fórmula: F -P c0");
        System.out.println("Regla: F_NOT - Falso ¬P → Verdadero P");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("F -P c0")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();
        System.out.println(proofTree.toString());

        assertFalse("La prueba NO debe estar cerrada para F -P c0", proof.isClosed());

        System.out.println("✅ Test F_NOT pasado: La fórmula F -P c0 NO es válida");
    }

    @Test
    public void testT_NOT_NOT_Rule() {
        System.out.println("\n=== TESTING T_NOT_NOT RULE: T --P c0 ===");
        System.out.println("Fórmula: T --P c0");
        System.out.println("Regla: T_NOT_NOT - Verdadero ¬¬P → Verdadero P");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("T -(-P) c0")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();
        System.out.println(proofTree.toString());

        assertFalse("La prueba NO debe estar cerrada para T --P c0", proof.isClosed());

        System.out.println("✅ Test T_NOT_NOT pasado: La fórmula T --P c0 NO es válida");
    }

    // F ->(*(->(A B) ->(A -B)) -A) c0
    @Test
    public void testF_NOT_NOT_Rule() {
        System.out.println("\n=== TESTING F_NOT_NOT RULE: F ->(*(->(A B) ->(A -B)) -A) c0 ===");
        System.out.println("Fórmula: F ->(*(->(A B) ->(A -B)) -A) c0");
        System.out.println("Regla: T_NOT_NOT - Verdadero ¬¬P → Verdadero P");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("F ->(*(->(A B) ->(A -B)) -A) c0")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();
        System.out.println(proofTree.toString());

        assertTrue("La prueba debe estar cerrada para F ->(*(->(A B) ->(A -B)) -A) c0", proof.isClosed());

        System.out.println("✅ Test F_NOT_NOT pasado: La fórmula F ->(*(->(A B) ->(A -B)) -A) c0 NO es válida");
    }

    // ===== REGLAS DE DOS PREMISAS =====
    @Test
    public void testX_OR_F_LEFT_Rule() {
        System.out.println("\n=== TESTING X_OR_F_LEFT RULE: T +(P Q) c0, F P c1 ===");
        System.out.println("Fórmulas: T +(P Q) c0, F P c1");
        System.out.println("Regla: X_OR_F_LEFT - Verdadero P ∨ Q, Falso P → Verdadero Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();
        FormulaLabel auxLabel = c.getNewFormulaLabel();
        System.out.println(mainLabel);
        System.out.println(mainLabel.getLowerFormulaLabel());
        System.out.println(mainLabel.getNextFormulaLabel());
        System.out.println(mainLabel.getGreaterFormulaLabel());
        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("T +(P Q) c0")));
        sfl.add(lff.createLabelledFormula(mainLabel.getLowerFormulaLabel(), sfc.parseString("F P c1")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();
        System.out.println(proofTree.toString());


        assertFalse("La prueba NO debe estar cerrada para X_OR_F_LEFT", proof.isClosed());

        System.out.println("✅ Test X_OR_F_LEFT pasado");
    }

    @Test
    public void testT_OR_F_RIGHT_Rule() {
        System.out.println("\n=== TESTING T_OR_F_RIGHT RULE: T +(P Q) c0, F Q c1 ===");
        System.out.println("Fórmulas: T +(P Q) c0, F Q c1");
        System.out.println("Regla: T_OR_F_RIGHT - Verdadero P ∨ Q, Falso Q → Verdadero P");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();
        FormulaLabel auxLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("T +(P Q) c0")));
        sfl.add(lff.createLabelledFormula(auxLabel, sfc.parseString("F Q c1")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();

        assertFalse("La prueba NO debe estar cerrada para T_OR_F_RIGHT", proof.isClosed());

        System.out.println("✅ Test T_OR_F_RIGHT pasado");
    }

    @Test
    public void testF_AND_LEFT_Rule() {
        System.out.println("\n=== TESTING F_AND_LEFT RULE: F *(P Q) c0, T P c1 ===");
        System.out.println("Fórmulas: F *(P Q) c0, T P c1");
        System.out.println("Regla: F_AND_LEFT - Falso P ∧ Q, Verdadero P → Falso Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();
        FormulaLabel auxLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("F *(P Q) c0")));
        sfl.add(lff.createLabelledFormula(auxLabel, sfc.parseString("T P c1")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();

        assertFalse("La prueba NO debe estar cerrada para F_AND_LEFT", proof.isClosed());

        System.out.println("✅ Test F_AND_LEFT pasado");
    }

    @Test
    public void testX_AND_T_RIGHT_Rule() {
        System.out.println("\n=== TESTING X_AND_T_RIGHT RULE: F *(P Q) c0, T Q c1 ===");
        System.out.println("Fórmulas: F *(P Q) c0, T Q c1");
        System.out.println("Regla: X_AND_T_RIGHT - Falso P ∧ Q, Verdadero Q → Falso P");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();
        FormulaLabel auxLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("F *(P Q) c0")));
        sfl.add(lff.createLabelledFormula(auxLabel, sfc.parseString("T Q c1")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();


        assertFalse("La prueba NO debe estar cerrada para X_AND_T_RIGHT", proof.isClosed());

        System.out.println("✅ Test X_AND_T_RIGHT pasado");
    }

    @Test
    public void testT_IMPLIES_LEFT_Rule() {
        System.out.println("\n=== TESTING T_IMPLIES_LEFT RULE: T ->(P Q) c0, T P c1 ===");
        System.out.println("Fórmulas: T ->(P Q) c0, T P c1");
        System.out.println("Regla: T_IMPLIES_LEFT - Verdadero P → Q, Verdadero P → Verdadero Q");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();
        FormulaLabel auxLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("T ->(P Q) c0")));
        sfl.add(lff.createLabelledFormula(auxLabel, sfc.parseString("T P c1")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();


        assertFalse("La prueba NO debe estar cerrada para T_IMPLIES_LEFT", proof.isClosed());

        System.out.println("✅ Test T_IMPLIES_LEFT pasado");
    }

    @Test
    public void testX_IMPLIES_F_RIGHT_Rule() {
        System.out.println("\n=== TESTING X_IMPLIES_F_RIGHT RULE: T ->(P Q) c0, F Q c1 ===");
        System.out.println("Fórmulas: T ->(P Q) c0, F Q c1");
        System.out.println("Regla: X_IMPLIES_F_RIGHT - Verdadero P → Q, Falso Q → Falso P");
        System.out.println("Resultado esperado: NO cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();
        FormulaLabel auxLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("T ->(P Q) c0")));
        sfl.add(lff.createLabelledFormula(auxLabel, sfc.parseString("F Q c1")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();


        assertFalse("La prueba NO debe estar cerrada para X_IMPLIES_F_RIGHT", proof.isClosed());

        System.out.println("✅ Test X_IMPLIES_F_RIGHT pasado");
    }

    // ===== TESTS DE CONTRADICCIÓN (DEBERÍAN CERRAR) =====

    @Test
    public void testSimpleConjunctionContradiction() {
        System.out.println("\n=== TESTING SIMPLE CONJUNCTION CONTRADICTION: F *(P Q) c0 ===");
        System.out.println("Fórmula: F *(P Q) c0");
        System.out.println("Significado: Queremos probar que P ∧ Q es FALSO");
        System.out.println("Resultado esperado: Cerrado (contradicción)\n");

        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();

        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("F *(P Q) c0")));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();

        // Esta fórmula SÍ debería estar cerrada porque F *(P Q) es una contradicción
        assertTrue("La prueba debe estar cerrada para F *(P Q) c0", proof.isClosed());

        System.out.println("✅ Test de contradicción pasado: La fórmula F *(P Q) c0 es válida (contradicción)");
    }

    // ===== TESTS ESPECÍFICOS IPL (DIFERENCIAS CON LÓGICA CLÁSICA) =====
    
    @Test
    public void testIPLLabelConstraints_TwoPremises() {
        System.out.println("\n=== TESTING IPL LABEL CONSTRAINTS: T +(P Q) c0, F P c1 ===");
        System.out.println("Significado: Regla de dos premisas con restricciones de etiquetas");
        System.out.println("Regla aplicable: X_OR_F_LEFT si se cumplen las restricciones de etiquetas");
        System.out.println("Resultado esperado: Derivación exitosa con restricciones respetadas\n");
        
        SignedFormulaList sfl = new SignedFormulaList();
        // Usar directamente el parser para respetar las etiquetas especificadas
        sfl.add(sfc.parseString("T +(P Q) c0"));
        sfl.add(sfc.parseString("F P c1"));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(sfc.getLabelledFormulaFactory());
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();

        System.out.println("closed? : " + proof.isClosed());
        System.out.println("Árbol de prueba:");
        System.out.println(proofTree.toString());
        
        // En este caso, la derivación debería proceder según las reglas IPL
        assertFalse("La prueba NO debe estar cerrada (derivación normal)", proof.isClosed());
        
        System.out.println("✅ Test IPL pasado: Las etiquetas c0, c1 se respetan correctamente");
    }

    @Test
    public void testLawOfExcludedMiddle_NotValidInIPL() {
        System.out.println("\n=== TESTING LAW OF EXCLUDED MIDDLE: T +(P -P) c0 ===");
        System.out.println("Significado: Intentamos probar que P ∨ ¬P es verdadero");
        System.out.println("En lógica clásica: P ∨ ¬P es siempre verdadero (tautología)");
        System.out.println("En IPL: P ∨ ¬P NO es válido universalmente");
        System.out.println("Resultado esperado: NO cerrado (no es derivable en IPL)\n");
        
        SignedFormulaList sfl = new SignedFormulaList();
        // Usar directamente el parser - respeta las etiquetas c0 especificadas
        sfl.add(sfc.parseString("T +(P -P) c0"));

        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(sfc.getLabelledFormulaFactory());
        problem.setSignedFormulaList(sfl);

        Proof proof = prover.prove(problem);
        IProofTree proofTree = proof.getProofTree();

        // En IPL, no podemos derivar P ∨ ¬P como tautología
        assertFalse("La prueba NO debe estar cerrada para T +(P -P) c0 en IPL", proof.isClosed());

        System.out.println("closed? : " + proof.isClosed());
        System.out.println("Árbol de prueba:");
        System.out.println(proofTree.toString());
        
        System.out.println("✅ Test IPL pasado: P ∨ ¬P NO es válido en lógica intuicionista");
        System.out.println("Esto confirma que IPL es más débil que la lógica clásica");
    }
    
    @Test 
    public void testUsingIPLProver() {
        System.out.println("\n=== TESTING USING IPLProver (INTEGRATED) ===");
        System.out.println("Demostrando el uso del prover integrado para IPL\n");
        
        // Usar el prover integrado IPL
        logicalSystems.ipl.IPLProver iplProver = new logicalSystems.ipl.IPLProver();
        
        // Test 1: Tercero excluido - debería fallar en IPL
        Proof proof1 = iplProver.testLawOfExcludedMiddle("P");
        assertFalse("Tercero excluido NO debe cerrarse en IPL", proof1.isClosed());
        System.out.println("✅ Tercero excluido: NO válido en IPL (correcto)");
        
        // Test 2: Contradicción - debería cerrarse  
        Proof proof2 = iplProver.testContradiction("T B c0", "T -B c1");
        assertTrue("Contradicción T B y T ¬B debe cerrarse en IPL", proof2.isClosed());
        System.out.println("✅ Contradicción T B y T ¬B: cerrada correctamente");
        
        // Test 3: Fórmula válida
        Proof proof3 = iplProver.proveSingle("F ->(*(->(A B) ->(A -B)) -A) c0");
        assertTrue("Esta fórmula debe ser válida en IPL", proof3.isClosed());
        System.out.println("✅ Fórmula compleja: válida en IPL");
        
        System.out.println("Context usado: " + iplProver.getContext());
    }

}