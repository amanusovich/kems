/*
 * Created on 01/11/2005
 *
 */
package main.newstrategy.ipl;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import logicalSystems.ipl.IPLRuleStructures;
import main.newstrategy.AbstractSimpleStrategy;
import main.newstrategy.ISimpleStrategy;
import main.newstrategy.cpl.configurable.comparator.ISignedFormulaComparator;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.strategy.ClassicalProofTree;
import main.strategy.IClassicalProofTree;
import main.strategy.applicator.IProofTransformation;
import main.strategy.applicator.IRuleApplicator;
import main.strategy.applicator.PBRuleApplicator;
import main.strategy.simple.FormulaReferenceClassicalProofTree;
import logicalSystems.ipl.IPLProofTree;
import logicalSystems.ipl.IPLSignedFormulaFactory;
import logic.labelledFormulas.Context;
import main.tableau.Method;
import logic.formulas.Formula;
import logic.formulas.FormulaFactory;
import logic.formulas.FormulaList;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaBuilder;
import logic.signedFormulas.SignedFormulaList;
import main.newstrategy.util.ProofSaverLoader;
import main.proofTree.origin.IOrigin;

/**
 * A simple strategy for IPL (Intuitionistic Propositional Logic).
 * It uses the IPL rule structure and implements ISimpleStrategy directly.
 * 
 * @author Adolfo Gustavo Serra Seca Neto
 * 
 */
public class IPLSimpleStrategy extends AbstractSimpleStrategy {

    private Context iplContext;
    
    /**
     * @param method
     */
    public IPLSimpleStrategy(Method method) {
        super(method);
        
        // NO crear Context aquí - será inyectado desde Problem
        // this.iplContext = new Context(); // ❌ REMOVIDO

        // initialize rule applicators
        List<IRuleApplicator> ruleApplicators = new ArrayList<IRuleApplicator>();
        ruleApplicators.add(new IPLOnePremiseRuleApplicator(this,
                IPLRuleStructures.ONE_PREMISE_RULE_LIST));
        ruleApplicators.add(new IPLTwoPremiseRuleApplicator(this,
                IPLRuleStructures.TWO_PREMISE_RULE_LIST));

        setRuleApplicators(ruleApplicators);

        // initialize proof transformations
        List<IProofTransformation> proofTransformations = new ArrayList<IProofTransformation>();
        // Deshabilitar PBRuleApplicator por ahora ya que:
        // 1. Las reglas F_AND_LEFT y T_IMPLIES_LEFT están duplicadas en PB y Two-Premise
        // 2. IPLTwoPremiseRuleApplicator ya maneja estas reglas correctamente
        // 3. Evita ClassCastException entre rules.ipl.* y rules.* 
        // IPLPBRuleApplicator pbr = new IPLPBRuleApplicator(this, IPLRuleStructures.PB_RULE_LIST);
        // proofTransformations.add(pbr);
        setProofTransformations(proofTransformations);
    }

    @Override
    public IProofTree createPTInstance(SignedFormulaNode root) {
        return new IPLProofTree(root);
    }

    @Override
    public SignedFormulaList getLocalReferences(IClassicalProofTree proofTree, Formula formula) {
        // Para IPL, implementamos una versión simplificada que no depende de FormulaReferenceClassicalProofTree
        // TODO: Implementar correctamente para IPL si es necesario
        return new SignedFormulaList();
    }

    @Override
    public FormulaList getSubformulaLocalReferences(IClassicalProofTree proofTree, Formula formula, SignedFormula sf) {
        // Para IPL, implementamos una versión simplificada que no depende de FormulaReferenceClassicalProofTree
        // TODO: Implementar correctamente para IPL si es necesario
        return new FormulaList();
    }

    @Override
    public SignedFormulaList getParentReferences(IClassicalProofTree proofTree, Formula formula) {
        // Para IPL, implementamos una versión simplificada que no depende de FormulaReferenceClassicalProofTree
        // TODO: Implementar correctamente para IPL si es necesario
        return new SignedFormulaList();
    }
    
    /**
     * Inyecta el Context IPL desde el Problem.
     * Este método debe ser llamado después de la construcción de la Strategy.
     * 
     * @param context el Context compartido del Problem
     */
    public void setIPLContext(Context context) {
        this.iplContext = context;
        System.out.println("✅ IPL: Context inyectado en IPLSimpleStrategy");
    }
    
    /**
     * Obtiene el Context usado por esta estrategia IPL
     */
    public Context getIPLContext() {
        return iplContext;
    }
    
    /**
     * Crea una IPLSignedFormulaFactory con el Context de la estrategia
     */
    public IPLSignedFormulaFactory createIPLFormulaFactory() {
        if (iplContext == null) {
            throw new IllegalStateException("IPL Context no ha sido inyectado. Llamar setIPLContext() primero.");
        }
        return new IPLSignedFormulaFactory(iplContext);
    }
    
    /**
     * Crea SignedFormulaBuilder con Context correcto para IPL
     */
    public SignedFormulaBuilder createSignedFormulaBuilderWithContext() {
        if (iplContext != null) {
            IPLSignedFormulaFactory factory = new IPLSignedFormulaFactory(iplContext);
            return new SignedFormulaBuilder(factory, new FormulaFactory());
        }
        // Fallback: crear factory básica
        return new SignedFormulaBuilder();
    }
}
