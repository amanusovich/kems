package logicalSystems.ipl;

import logic.labelledFormulas.Context;
import logic.labelledFormulas.LabelledFormula;
import logic.labelledFormulas.LabelledFormulaCreator;
import logic.problem.Problem;
import logic.signedFormulas.SignedFormulaList;
import main.newstrategy.Prover;
import main.newstrategy.cpl.configurable.comparator.InsertionOrderSignedFormulaComparator;
import main.newstrategy.ipl.IPLSimpleStrategy;
import main.tableau.Method;
import main.tableau.Proof;
import proverinterface.RuleStructureFactory;

/**
 * Prover especializado para IPL que maneja automáticamente:
 * - Context y orden parcial de etiquetas
 * - IPLProofTree con detección correcta de contradicciones IPL
 * - Integración completa con el sistema KEMS
 */
public class IPLProver {
    
    private Prover prover;
    private Method method;
    private IPLSimpleStrategy strategy;
    private LabelledFormulaCreator formulaCreator;
    private IPLSignedFormulaFactory formulaFactory;
    
    /**
     * Constructor que inicializa automáticamente IPL
     */
    public IPLProver() {
        // Inicializar componentes IPL
        this.formulaCreator = new LabelledFormulaCreator("ipl");
        
        // Crear método con reglas IPL
        this.method = new Method(RuleStructureFactory.createRulesStructure(RuleStructureFactory.IPL));
        
        // Crear estrategia IPL con Context integrado
        this.strategy = new IPLSimpleStrategy(method);
        this.strategy.setComparator(new InsertionOrderSignedFormulaComparator());
        
        // Crear factory IPL con Context de la estrategia
        this.formulaFactory = strategy.createIPLFormulaFactory();
        
        // Configurar prover
        this.prover = new Prover();
        this.prover.setMethod(method);
        this.prover.setStrategy(strategy);
    }
    
    /**
     * Resuelve un problema IPL a partir de strings de fórmulas
     */
    public Proof prove(String... formulas) {
        SignedFormulaList sfl = new SignedFormulaList();
        
        // Parsear cada fórmula y agregarlá usando las etiquetas correctas
        for (String formulaString : formulas) {
            LabelledFormula lf = formulaCreator.parseString(formulaString);
            sfl.add(lf);
        }
        
        // Crear problema IPL
        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(formulaFactory);
        problem.setSignedFormulaList(sfl);
        
        // Resolver
        return prover.prove(problem);
    }
    
    /**
     * Resuelve un problema IPL a partir de una lista de fórmulas ya parseadas
     */
    public Proof prove(SignedFormulaList formulas) {
        Problem problem = new Problem("ipl");
        problem.setSignedFormulaFactory(formulaFactory);
        problem.setSignedFormulaList(formulas);
        
        return prover.prove(problem);
    }
    
    /**
     * Obtiene el Context usado por este prover
     */
    public Context getContext() {
        return strategy.getIPLContext();
    }
    
    /**
     * Obtiene la factory de fórmulas IPL
     */
    public IPLSignedFormulaFactory getFormulaFactory() {
        return formulaFactory;
    }
    
    /**
     * Obtiene el creador de fórmulas
     */
    public LabelledFormulaCreator getFormulaCreator() {
        return formulaCreator;
    }
    
    /**
     * Obtiene la estrategia IPL
     */
    public IPLSimpleStrategy getStrategy() {
        return strategy;
    }
    
    /**
     * Método de conveniencia para probar una sola fórmula
     */
    public Proof proveSingle(String formula) {
        return prove(formula);
    }
    
    /**
     * Método de conveniencia para probar el tercero excluido
     */
    public Proof testLawOfExcludedMiddle(String atomicFormula) {
        String formula = "T +(" + atomicFormula + " -" + atomicFormula + ") c0";
        return prove(formula);
    }
    
    /**
     * Método de conveniencia para test de contradicción
     */
    public Proof testContradiction(String formula1, String formula2) {
        return prove(formula1, formula2);
    }
}
