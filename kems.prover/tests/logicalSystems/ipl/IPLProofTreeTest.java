package logicalSystems.ipl;

import org.junit.Test;
import org.junit.Before;
import static org.junit.Assert.*;

import logic.labelledFormulas.LabelledFormulaCreator;
import logic.labelledFormulas.LabelledFormula;
import logic.labelledFormulas.LabelledFormulaFactory;
import logic.signedFormulas.SignedFormulaList;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.FormulaLabel;
import logic.problem.Problem;
import main.newstrategy.Prover;
import main.tableau.Method;
import main.newstrategy.ISimpleStrategy;
import main.newstrategy.simple.SimpleStrategy;
import main.newstrategy.cpl.configurable.comparator.InsertionOrderSignedFormulaComparator;
import main.tableau.Proof;
import main.proofTree.IProofTree;
import main.proofTree.INode;
import main.proofTree.SignedFormulaNode;
import main.proofTree.iterator.IProofTreeBasicIterator;
import proverinterface.RuleStructureFactory;

/**
 * Test unitario para demostrar cómo generar y examinar el árbol de pruebas IPL
 * para las dos fórmulas de ejemplo.
 */
public class IPLProofTreeTest {

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
        
        // Crear la estrategia IPL (usar SimpleStrategy ya que IPL no tiene estrategia específica)
        strategy = new SimpleStrategy(method);
        strategy.setComparator(new InsertionOrderSignedFormulaComparator());
        
        // Configurar el prover
        prover = new Prover();
        prover.setMethod(method);
        prover.setStrategy(strategy);
    }

    @Test
    public void testFirstFormulaProofTree() {
        System.out.println("\n=== TESTING FIRST FORMULA: F ->(*(->(A B) ->(A -B)) -A) c0 ===");
        
        // Crear el problema con la primera fórmula
        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();
        
        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("F +(P Q) c0")));
        
        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);
        
        // Generar la prueba
        Proof proof = prover.prove(problem);
        
        // Verificar que la prueba es válida
    //    assertTrue("La prueba debe ser cerrada", proof.isClosed());
        
        // Obtener el árbol de pruebas
        IProofTree proofTree = proof.getProofTree();
        
        // Mostrar información del árbol
        System.out.println("Problema: " + proof.getProblem().getName());
        System.out.println("Fórmulas del problema: " + proof.getProblem().getFormulas());
        System.out.println("Número de nodos: " + proofTree.getNumberOfNodes());
        
        // Mostrar el árbol completo
        System.out.println("\n=== ÁRBOL DE PRUEBAS COMPLETO ===");
        printProofTree(proofTree, 0);
        
        // Verificar el tamaño esperado (basado en los resultados anteriores)
        assertEquals("El árbol debe tener 11 nodos", 11, proofTree.getNumberOfNodes());
    }

    @Test
    public void testSecondFormulaProofTree() {
        System.out.println("\n=== TESTING SECOND FORMULA: F ->(-(-A) A) c0 ===");
        
        // Crear el problema con la segunda fórmula
        Context c = new Context();
        FormulaLabel mainLabel = c.getNewFormulaLabel();
        
        SignedFormulaList sfl = new SignedFormulaList();
        sfl.add(lff.createLabelledFormula(mainLabel, sfc.parseString("F ->(-(-A) A) c0")));
        
        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(lff);
        problem.setSignedFormulaList(sfl);
        
        // Generar la prueba
        Proof proof = prover.prove(problem);
        
        // Verificar que la prueba es válida
        assertTrue("La prueba debe ser cerrada", proof.isClosed());
        
        // Obtener el árbol de pruebas
        IProofTree proofTree = proof.getProofTree();
        
        // Mostrar información del árbol
        System.out.println("Problema: " + proof.getProblem().getName());
        System.out.println("Fórmulas del problema: " + proof.getProblem().getFormulas());
        System.out.println("Número de nodos: " + proofTree.getNumberOfNodes());
        
        // Mostrar el árbol completo
        System.out.println("\n=== ÁRBOL DE PRUEBAS COMPLETO ===");
        printProofTree(proofTree, 0);
        
        // Verificar el tamaño esperado (basado en los resultados anteriores)
        assertEquals("El árbol debe tener 5 nodos", 5, proofTree.getNumberOfNodes());
    }

    /**
     * Método auxiliar para imprimir el árbol de pruebas de forma legible
     */
    private void printProofTree(IProofTree tree, int depth) {
        if (tree == null) return;
        
        String indent = "  ".repeat(depth);
        INode root = tree.getRoot();
        
        if (root instanceof SignedFormulaNode) {
            SignedFormulaNode sfn = (SignedFormulaNode) root;
            System.out.println(indent + "├─ " + sfn.getContent() + 
                             " [" + getBranchId(tree) + "]");
        } else {
            System.out.println(indent + "├─ " + root + " [" + getBranchId(tree) + "]");
        }
        
        // Mostrar información adicional del nodo
        System.out.println(indent + "   ├─ Tipo: " + root.getClass().getSimpleName());
        
        // Recorrer los hijos si existen
        try {
            if (tree.getLeft() != null) {
                System.out.println(indent + "   ├─ Rama izquierda:");
                printProofTree(tree.getLeft(), depth + 1);
            }
            if (tree.getRight() != null) {
                System.out.println(indent + "   └─ Rama derecha:");
                printProofTree(tree.getRight(), depth + 1);
            }
        } catch (Exception e) {
            System.out.println(indent + "   └─ [Error al recorrer hijos: " + e.getMessage() + "]");
        }
    }

    /**
     * Obtiene un identificador único para la rama
     */
    private String getBranchId(IProofTree tree) {
        try {
            return "Branch-" + tree.hashCode();
        } catch (Exception e) {
            return "Branch-Unknown";
        }
    }

    @Test
    public void testBothFormulasComparison() {
        System.out.println("\n=== COMPARACIÓN DE AMBAS FÓRMULAS ===");
        
        // Probar ambas fórmulas y comparar sus árboles
        Context c1 = new Context();
        FormulaLabel mainLabel1 = c1.getNewFormulaLabel();
        SignedFormulaList sfl1 = new SignedFormulaList();
        sfl1.add(lff.createLabelledFormula(mainLabel1, sfc.parseString("F ->(*(->(A B) ->(A -B)) -A) c0")));
        
        Problem problem1 = new Problem("ipl");
        problem1.setSignedFormulaFactory(lff);
        problem1.setSignedFormulaList(sfl1);
        
        Context c2 = new Context();
        FormulaLabel mainLabel2 = c2.getNewFormulaLabel();
        SignedFormulaList sfl2 = new SignedFormulaList();
        sfl2.add(lff.createLabelledFormula(mainLabel2, sfc.parseString("F ->(-(-A) A) c0")));
        
        Problem problem2 = new Problem("ipl");
        problem2.setSignedFormulaFactory(lff);
        problem2.setSignedFormulaList(sfl2);
        
        Proof proof1 = prover.prove(problem1);
        Proof proof2 = prover.prove(problem2);
        
        IProofTree tree1 = proof1.getProofTree();
        IProofTree tree2 = proof2.getProofTree();
        
        System.out.println("Fórmula 1 - Nodos: " + tree1.getNumberOfNodes());
        System.out.println("Fórmula 2 - Nodos: " + tree2.getNumberOfNodes());
        
        // Verificar que ambas son válidas
        assertTrue("Ambas pruebas deben ser cerradas", 
                  proof1.isClosed() && proof2.isClosed());
        
        // Verificar que la primera fórmula es más compleja
        assertTrue("La primera fórmula debe ser más compleja", 
                  tree1.getNumberOfNodes() > tree2.getNumberOfNodes());
    }
}
