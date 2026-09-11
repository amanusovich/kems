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
 * Test comprehensivo de reglas IPL usando Context explícito para establecer
 * relaciones de orden entre etiquetas según el paper "Free-variable KE tableaux for IPL"
 * 
 * A diferencia de IPLRulesComprehensiveTest que usa parsing de strings,
 * este test crea fórmulas directamente con Context para establecer
 * explícitamente las relaciones de orden parcial entre etiquetas.
 */
public class IPLRulesContextTest {

    /**
     * Método base para crear un proof con Context explícito
     */
    private Proof proveWithContext(TestCase testCase) throws Exception {
        // Crear problema con IPLSignedFormulaFactory
        Problem problem = new Problem("ipl");
        IPLSignedFormulaFactory iplFactory = new IPLSignedFormulaFactory();
        problem.setSignedFormulaFactory(iplFactory);
        
        // Obtener el Context del factory 
        Context context = iplFactory.getContext();
        
        // Establecer las relaciones de orden según el caso de prueba
        ContextFormulaLabel[] labels = testCase.createLabelsWithOrdering(context);
        
        // Crear fórmulas usando FormulaFactory
        FormulaFactory ff = new FormulaFactory();
        
        // Crear las fórmulas del caso de prueba
        for (int i = 0; i < testCase.formulas.length; i++) {
            FormulaSpec spec = testCase.formulas[i];
            
            // Crear la fórmula
            Formula formula = createFormula(ff, spec);
            
            // Crear SignedFormula con la etiqueta correcta
            SignedFormula signedFormula = iplFactory.createSignedFormula(
                spec.sign, formula, labels[spec.labelIndex]);
            
            // Crear LabelledFormula (la factory conservará el ContextFormulaLabel)
            LabelledFormula labelledFormula = iplFactory.createLabelledFormula(
                labels[spec.labelIndex], signedFormula);
            
            problem.getFormulas().add(labelledFormula);
        }
        
        // Crear método con reglas IPL
        Method method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
        
        // Crear estrategia IPL
        IPLSimpleStrategy strategy = new IPLSimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());
        
        // Crear y configurar prover
        Prover prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);
        
        return prover.prove(problem);
    }
    
    /**
     * Crea una fórmula basada en la especificación
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
                throw new RuntimeException("Tipo de fórmula no soportado: " + spec.type);
        }
    }
    
    // =====================================
    // CLASES AUXILIARES PARA DEFINIR CASOS DE PRUEBA
    // =====================================
    
    /**
     * Especifica un caso de prueba con fórmulas y relaciones de orden
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
         * Crea las etiquetas y establece las relaciones de orden en el Context
         */
        ContextFormulaLabel[] createLabelsWithOrdering(Context context) {
            // Determinar cuántas etiquetas necesitamos
            int maxLabelIndex = 0;
            for (FormulaSpec formula : formulas) {
                if (formula.labelIndex > maxLabelIndex) {
                    maxLabelIndex = formula.labelIndex;
                }
            }
            
            ContextFormulaLabel[] labels = new ContextFormulaLabel[maxLabelIndex + 1];
            
            // Crear etiquetas base
            for (int i = 0; i <= maxLabelIndex; i++) {
                labels[i] = (ContextFormulaLabel) context.getNewFormulaLabel();
            }
            
            // Establecer relaciones de orden
            for (OrderRelation relation : labelOrdering) {
                context.setAsGreaterThan(labels[relation.smaller], labels[relation.greater]);
            }
            
            return labels;
        }
    }
    
    /**
     * Especifica una fórmula con su tipo, signo y etiqueta
     */
    static class FormulaSpec {
        FormulaType type;
        String name;
        FormulaSpec[] subformulas;
        FormulaSign sign;
        int labelIndex;
        
        // Constructor para fórmulas atómicas
        FormulaSpec(FormulaType type, String name, FormulaSign sign, int labelIndex) {
            this.type = type;
            this.name = name;
            this.sign = sign;
            this.labelIndex = labelIndex;
        }
        
        // Constructor para fórmulas compuestas
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
     * Especifica una relación de orden: smaller ≤ greater
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
    // TESTS DE REGLAS IPL
    // =====================================
    
    @Test
    public void testRule1_F_OR_BasicApplication() {
        System.out.println("\n=== TEST REGLA 1: F_OR (Context-based) ===");
        System.out.println("F (P∨Q) c0 → F P c0, F Q c0");
        
        try {
            // Definir caso de prueba: F (P∨Q) c0
            FormulaSpec P = new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.FALSE, 0);
            FormulaSpec Q = new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.FALSE, 0);
            FormulaSpec PorQ = new FormulaSpec(FormulaType.OR, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.FALSE, 0);
            
            TestCase testCase = new TestCase(
                "F_OR",
                "F (P∨Q) c0 → F P c0, F Q c0",
                new FormulaSpec[]{PorQ},
                new OrderRelation[]{}, // No se necesitan relaciones de orden específicas
                new String[]{"F P c0", "F Q c0"},
                false
            );
            
            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó F_OR
            assertTrue("Debe generar F P c0", treeOutput.contains("F P c0"));
            assertTrue("Debe generar F Q c0", treeOutput.contains("F Q c0"));
            
            System.out.println("✅ REGLA 1 (F_OR): CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test F_OR: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule3_X_OR_F_LEFT_ValidLabelCondition() {
        System.out.println("\n=== TEST REGLA 3: X_OR_F_LEFT (Context-based) ===");
        System.out.println("T (P∨Q) c0, F P c1 (c0 ⪯ c1: main.label ≤ aux.label) → T Q c0");
        
        try {
            // Definir caso de prueba: T (P∨Q) c0, F P c1 con c0 ≤ c1
            FormulaSpec PorQ = new FormulaSpec(FormulaType.OR, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.TRUE, 0);
            
            FormulaSpec FalseP = new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.FALSE, 1);
            
            TestCase testCase = new TestCase(
                "X_OR_F_LEFT",
                "T (P∨Q) c0, F P c1 (c0 ≤ c1) → T Q c0",
                new FormulaSpec[]{PorQ, FalseP},
                new OrderRelation[]{new OrderRelation(0, 1)}, // c0 ≤ c1
                new String[]{"T Q c0"},
                false
            );
            
            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla y generó T Q c0
            assertTrue("Debe generar T Q c0", treeOutput.contains("T Q c0"));
            assertFalse("NO debe estar cerrado", proof.isClosed());
            
            System.out.println("✅ REGLA 3 (X_OR_F_LEFT): CORRECTA con Context explícito");
            
        } catch (Exception e) {
            fail("Error en test X_OR_F_LEFT: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule4_X_OR_F_RIGHT_ValidLabelCondition() {
        System.out.println("\n=== TEST REGLA 4: X_OR_F_RIGHT (Context-based) ===");
        System.out.println("T (P∨Q) c0, F Q c1 (c0 ⪯ c1: main.label ≤ aux.label) → T P c0");
        
        try {
            // Definir caso de prueba: T (P∨Q) c0, F Q c1 con c0 ≤ c1
            FormulaSpec PorQ = new FormulaSpec(FormulaType.OR, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.TRUE, 0);
            
            FormulaSpec FalseQ = new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.FALSE, 1);
            
            TestCase testCase = new TestCase(
                "X_OR_F_RIGHT",
                "T (P∨Q) c0, F Q c1 (c0 ≤ c1) → T P c0",
                new FormulaSpec[]{PorQ, FalseQ},
                new OrderRelation[]{new OrderRelation(0, 1)}, // c0 ≤ c1
                new String[]{"T P c0"},
                false
            );
            
            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó la regla y generó T P c0
            assertTrue("Debe generar T P c0", treeOutput.contains("T P c0"));
            assertFalse("NO debe estar cerrado", proof.isClosed());
            
            System.out.println("✅ REGLA 4 (X_OR_F_RIGHT): CORRECTA con Context explícito");
            
        } catch (Exception e) {
            fail("Error en test X_OR_F_RIGHT: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule5_F_AND_BasicApplication() {
        System.out.println("\n=== TEST REGLA 5: F_AND (Context-based) ===");
        System.out.println("F (P∧Q) c0 → F P c0 | F Q c0");
        
        try {
            // Definir caso de prueba: F (P∧Q) c0
            FormulaSpec PandQ = new FormulaSpec(FormulaType.AND, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.FALSE, 0);
            
            TestCase testCase = new TestCase(
                "F_AND",
                "F (P∧Q) c0 → F P c0 | F Q c0",
                new FormulaSpec[]{PandQ},
                new OrderRelation[]{}, // No se necesitan relaciones de orden específicas
                new String[]{"F P c0", "F Q c0"},
                false
            );
            
            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó F_AND (produce branches)
            assertTrue("Debe contener F P c0 o F Q c0", 
                treeOutput.contains("F P c0") || treeOutput.contains("F Q c0"));
            
            System.out.println("✅ REGLA 5 (F_AND): CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test F_AND: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule7_T_AND_ValidLabelCondition() {
        System.out.println("\n=== TEST REGLA 7: T_AND (Context-based) ===");
        System.out.println("T (P∧Q) c0 → T P c0, T Q c0");
        
        try {
            // Definir caso de prueba: T (P∧Q) c0
            FormulaSpec PandQ = new FormulaSpec(FormulaType.AND, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.TRUE, 0);
            
            TestCase testCase = new TestCase(
                "T_AND",
                "T (P∧Q) c0 → T P c0, T Q c0",
                new FormulaSpec[]{PandQ},
                new OrderRelation[]{}, // No se necesitan relaciones de orden específicas
                new String[]{"T P c0", "T Q c0"},
                false
            );
            
            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó T_AND
            assertTrue("Debe generar T P c0", treeOutput.contains("T P c0"));
            assertTrue("Debe generar T Q c0", treeOutput.contains("T Q c0"));
            
            System.out.println("✅ REGLA 7 (T_AND): CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test T_AND: " + e.getMessage());
        }
    }
    
    @Test
    public void testRule11_F_IMPLICATION_BasicApplication() {
        System.out.println("\n=== TEST REGLA 11: F_IMPLICATION (Context-based) ===");
        System.out.println("F (P→Q) c0 → T P c0, F Q c0");
        
        try {
            // Definir caso de prueba: F (P→Q) c0
            FormulaSpec PimpQ = new FormulaSpec(FormulaType.IMPLICATION, new FormulaSpec[]{
                new FormulaSpec(FormulaType.ATOMIC, "P", IPLSigns.TRUE, 0),
                new FormulaSpec(FormulaType.ATOMIC, "Q", IPLSigns.TRUE, 0)
            }, IPLSigns.FALSE, 0);
            
            TestCase testCase = new TestCase(
                "F_IMPLICATION",
                "F (P→Q) c0 → T P c0, F Q c0",
                new FormulaSpec[]{PimpQ},
                new OrderRelation[]{}, // No se necesitan relaciones de orden específicas
                new String[]{"T P c0", "F Q c0"},
                false
            );
            
            Proof proof = proveWithContext(testCase);
            IProofTree tree = proof.getProofTree();
            String treeOutput = tree.toString();
            
            System.out.println("Árbol resultado:");
            System.out.println(treeOutput);
            
            // Verificar que se aplicó F_IMPLICATION
            assertTrue("Debe generar T P c0", treeOutput.contains("T P c0"));
            assertTrue("Debe generar F Q c0", treeOutput.contains("F Q c0"));
            
            System.out.println("✅ REGLA 11 (F_IMPLICATION): CORRECTA");
            
        } catch (Exception e) {
            fail("Error en test F_IMPLICATION: " + e.getMessage());
        }
    }
    
    @Test 
    public void testLabelOrderingComparisons() {
        System.out.println("\n=== TEST: VERIFICACIÓN DE ORDENAMIENTO DE ETIQUETAS ===");
        System.out.println("Verificando que las relaciones c0 ≤ c1 ≤ c2 se establecen correctamente");
        
        try {
            // Crear problema y context
            Problem problem = new Problem("ipl");
            IPLSignedFormulaFactory iplFactory = new IPLSignedFormulaFactory();
            problem.setSignedFormulaFactory(iplFactory);
            Context context = iplFactory.getContext();
            
            // Crear etiquetas con relaciones de orden: c0 ≤ c1 ≤ c2
            ContextFormulaLabel c0 = (ContextFormulaLabel) context.getNewFormulaLabel();
            ContextFormulaLabel c1 = (ContextFormulaLabel) context.getNewFormulaLabelGreaterThan(c0);
            ContextFormulaLabel c2 = (ContextFormulaLabel) context.getNewFormulaLabelGreaterThan(c1);
            
            System.out.println("Etiquetas creadas: c0=" + c0 + ", c1=" + c1 + ", c2=" + c2);
            
            // Verificar relaciones de orden
            assertTrue("c0 ≤ c0 debe ser true", c0.lowerOrEqualThan(c0));
            assertTrue("c0 ≤ c1 debe ser true", c0.lowerOrEqualThan(c1));
            assertTrue("c0 ≤ c2 debe ser true", c0.lowerOrEqualThan(c2));
            assertTrue("c1 ≤ c1 debe ser true", c1.lowerOrEqualThan(c1));
            assertTrue("c1 ≤ c2 debe ser true", c1.lowerOrEqualThan(c2));
            assertTrue("c2 ≤ c2 debe ser true", c2.lowerOrEqualThan(c2));
            
            assertFalse("c1 ≤ c0 debe ser false", c1.lowerOrEqualThan(c0));
            assertFalse("c2 ≤ c0 debe ser false", c2.lowerOrEqualThan(c0));
            assertFalse("c2 ≤ c1 debe ser false", c2.lowerOrEqualThan(c1));
            
            System.out.println("✅ ORDENAMIENTO DE ETIQUETAS: CORRECTO");
            
        } catch (Exception e) {
            fail("Error en test de ordenamiento: " + e.getMessage());
        }
    }
}
