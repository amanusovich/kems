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
import main.proofTree.SignedFormulaNodeState;
import main.proofTree.origin.NamedOrigin;
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
     * When PB is applied relative to the selection loop; see
     * {@link IPLCanonicalStrategyImplementation.PBPolicy} for the measured trade-off.
     * Defaults to DEFERRED, which decides 113 of the 274 ILTP propositional problems
     * against IMMEDIATE's 98.
     */
    private IPLCanonicalStrategyImplementation.PBPolicy pbPolicy =
            IPLCanonicalStrategyImplementation.PBPolicy.DEFERRED;

    public void setPbPolicy(IPLCanonicalStrategyImplementation.PBPolicy pbPolicy) {
        this.pbPolicy = pbPolicy;
    }

    public IPLCanonicalStrategyImplementation.PBPolicy getPbPolicy() {
        return pbPolicy;
    }
    
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
        
        // ENABLED: PBRuleApplicator specific to IPL, used as a last resort
        // Applied when two-premise rules cannot fire because the minor premise is missing
        IPLPBRuleApplicator pbr = new IPLPBRuleApplicator(this, IPLRuleStructures.TWO_PREMISE_RULE_LIST);
        proofTransformations.add(pbr);
        
        setProofTransformations(proofTransformations);
    }

    @Override
    public IProofTree createPTInstance(SignedFormulaNode root) {
        return new IPLProofTree(root);
    }

    /**
     * Override of the parent factory method to avoid the synthetic
     * T TOP / F BOTTOM nodes that {@link AbstractSimpleStrategy#createProofTree}
     * prepends to every proof tree for classical-style strategies. Those
     * nodes are not part of the IPL system of [labeled-ke-ipl] and have
     * no functional role in the canonical procedure: since this override
     * replaces the parent factory method entirely, no TOP/BOTTOM node is
     * ever created, so {@link IPLCanonicalStrategyImplementation} does not
     * need to guard against them. The IPL proof tree starts with the input
     * problem formula as its root, with origin {@code PROBLEM}.
     */
    @Override
    protected IProofTree createProofTree(Problem p, SignedFormulaBuilder sfb) {
        if (p.getFormulas() == null || p.getFormulas().size() == 0) {
            throw new IllegalStateException("IPL problem must have at least one formula");
        }
        SignedFormula firstFormula = p.getFormulas().get(0);
        SignedFormulaNode root = new SignedFormulaNode(firstFormula,
                SignedFormulaNodeState.NOT_ANALYSED, NamedOrigin.PROBLEM);
        IProofTree pt = createPTInstance(root);
        for (int i = 1; i < p.getFormulas().size(); i++) {
            SignedFormulaNode n = new SignedFormulaNode(p.getFormulas().get(i),
                    SignedFormulaNodeState.NOT_ANALYSED, NamedOrigin.PROBLEM);
            pt.addLast(n);
        }
        return pt;
    }

    @Override
    public SignedFormulaList getLocalReferences(IClassicalProofTree proofTree, Formula formula) {
        // For IPL, we implement a simplified version that does not depend on FormulaReferenceClassicalProofTree
        // TODO: implement properly for IPL if needed
        return new SignedFormulaList();
    }

    @Override
    public FormulaList getSubformulaLocalReferences(IClassicalProofTree proofTree, Formula formula, SignedFormula sf) {
        // For IPL, we implement a simplified version that does not depend on FormulaReferenceClassicalProofTree
        // TODO: implement properly for IPL if needed
        return new FormulaList();
    }

    @Override
    public SignedFormulaList getParentReferences(IClassicalProofTree proofTree, Formula formula) {
        // For IPL, we implement a simplified version that does not depend on FormulaReferenceClassicalProofTree
        // TODO: implement properly for IPL if needed
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
        IPLCanonicalStrategyImplementation canonical =
                new IPLCanonicalStrategyImplementation(pbPolicy);
        return canonical.execute(this, sfb);
    }
    
}
