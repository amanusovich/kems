/*
 * Created on 01/11/2005
 *
 */
package main.newstrategy.ipl;

import java.util.ArrayList;
import java.util.List;

import logicalSystems.ipl.IPLRuleStructures;
import main.newstrategy.AbstractSimpleStrategy;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import logic.signedFormulas.SignedFormulaBuilder;
import main.strategy.ClassicalProofTree;
import main.strategy.IClassicalProofTree;
import main.strategy.applicator.IProofTransformation;
import main.strategy.applicator.IRuleApplicator;
import logicalSystems.ipl.IPLProofTree;
import logic.problem.Problem;
import main.proofTree.ProofTree;
import main.tableau.Method;
import logic.formulas.Formula;
import logic.formulas.FormulaList;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaList;

/**
 * A simple strategy for IPL (Intuitionistic Propositional Logic).
 * It uses the IPL rule structure and implements ISimpleStrategy directly.
 * 
 * @author Adolfo Gustavo Serra Seca Neto
 * 
 */
public class IPLSimpleStrategy extends AbstractSimpleStrategy {
    
    /**
     * @param method
     */
    public IPLSimpleStrategy(Method method) {
        super(method);

        // initialize rule applicators
        List<IRuleApplicator> ruleApplicators = new ArrayList<IRuleApplicator>();
        ruleApplicators.add(new IPLOnePremiseRuleApplicator(this,
                IPLRuleStructures.ONE_PREMISE_RULE_LIST));
        ruleApplicators.add(new IPLTwoPremiseRuleApplicator(this,
                IPLRuleStructures.TWO_PREMISE_RULE_LIST));

        setRuleApplicators(ruleApplicators);

        // initialize proof transformations
        List<IProofTransformation> proofTransformations = new ArrayList<IProofTransformation>();
        
        // ✅ HABILITADO: PBRuleApplicator específico para IPL como último recurso
        // Se aplica cuando reglas de 2 premisas no pueden aplicarse por falta de premisa menor
        IPLPBRuleApplicator pbr = new IPLPBRuleApplicator(this, IPLRuleStructures.TWO_PREMISE_RULE_LIST);
        proofTransformations.add(pbr);
        
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
     * Overrides the close method to use the canonical algorithm implementation.
     * This follows Algorithm 1 from the paper exactly:
     * - Processes formulas one at a time
     * - Tries 1-premise rules before 2-premise rules
     * - Applies PB only when minor premise is missing
     */
    @Override
    public ProofTree close(Problem p) {
        if (IPLTracer.isEnabled()) {
            IPLTracer.getInstance().logInfo("IPL: Using Canonical Algorithm Implementation (following paper)");
        }
        
        // Call parent's close method to initialize everything properly
        // But we'll use our own implementation instead of SimpleStrategyImplementation
        
        SignedFormulaBuilder sfb = new SignedFormulaBuilder(
            p.getSignedFormulaFactory(), p.getFormulaFactory());
        setSignedFormulaBuilder(sfb);
        
        ClassicalProofTree proofTree = (ClassicalProofTree) createProofTree(p, sfb);
        setProofTree(proofTree);
        
        // If already closed, return immediately
        if (proofTree.isClosed()) {
            return proofTree;
        }
        
        // Use the canonical strategy implementation instead of the default one
        IPLCanonicalStrategyImplementation canonical = new IPLCanonicalStrategyImplementation();
        return canonical.execute(this, sfb);
    }
    
}
