/*
 * Created on 26/10/2005
 *
 */
package main.newstrategy.ipl;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import logic.formulas.CompositeFormula;
import logic.formulas.Formula;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaBuilder;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.SignedFormulaList;
import logicalSystems.ipl.IPLConnectives;
import logicalSystems.ipl.IPLProofTree;
import logicalSystems.ipl.IPLRules;
import logicalSystems.ipl.IPLSigns;
import main.newstrategy.ISimpleStrategy;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import main.strategy.ClassicalProofTree;
import main.strategy.applicator.IRuleApplicator;
import rules.NullRule;
import rules.Rule;
import rules.structures.IPLOnePremiseRuleList;
import rules.structures.OnePremiseRuleList;

/**
 * Applies one premise rules.
 *
 * @author Adolfo Gustavo Serra Seca Neto
 *
 */
public class IPLOnePremiseRuleApplicator implements IRuleApplicator {

    private static final IPLTracer tracer = IPLTracer.getInstance();

    private ISimpleStrategy strategy;

    private String ruleListName;

    /**
     * @param strategy
     * @param sfb
     */
    public IPLOnePremiseRuleApplicator(ISimpleStrategy strategy, String ruleListName) {
        super();
        this.strategy = strategy;
        this.ruleListName = ruleListName;
    }

    /*
     * (non-Javadoc)
     *
     * @see main.strategy.applicator.IRuleApplicator#applyAll(main.strategy.
     * ClassicalProofTree, logic.signedFormulas.SignedFormulaBuilder)
     */
    public boolean applyAll(ClassicalProofTree proofTree, SignedFormulaBuilder sfb) {
        boolean hasApplied = false;

        int i = 0;
        // notice that I am using a non-recommended "i--"
        while (i < proofTree.getPBCandidates().size() && !proofTree.isClosed()) {

            // for each signed formula not used, if it accepts a one premise
            // rule, apply the rule and remove it form the list of candidates.

            SignedFormula sf = (SignedFormula) proofTree.getPBCandidates().get(i);

            if (chooseAndApplyOnePremiseRule(proofTree, sfb, sf)) {
                hasApplied = true;
                i--;
            }
            i++;
        }

        return hasApplied;
    }

    /**
     * Applies a one-premise rule to a single specific formula.
     * This method is used by the canonical algorithm implementation.
     *
     * @param proofTree the proof tree
     * @param sfb the signed formula builder
     * @param sf the specific formula to process
     * @return true if a rule was applied, false otherwise
     */
    public boolean applySingle(ClassicalProofTree proofTree, SignedFormulaBuilder sfb, SignedFormula sf) {
        return chooseAndApplyOnePremiseRule(proofTree, sfb, sf);
    }

    private boolean chooseAndApplyOnePremiseRule(ClassicalProofTree proofTree, SignedFormulaBuilder sfb,
            SignedFormula sf) {
        boolean hasApplied = false;
        // Rule r = chooseOnePremiseRule(proofTree, sf);
        List<Rule> rules = getOnePremiseRuleList(proofTree, sf);

        for (Iterator<Rule> it = rules.iterator(); it.hasNext();) {
            if (hasApplied)
                break;
            // hasApplied = true;
            Rule r = it.next();

            // TERMINATION PROVISO. Applies to both constant-introducing rules: F-> and
            // F~. They are the only two rules that mint constants, and the proviso is
            // what bounds how many they mint (Lemma 5.8).
            if ((r == IPLRules.F_A_IMPLIES_B_TA_FB || r == IPLRules.F_NOT)
                    && shouldBlockFImpliesRule(proofTree, sf)) {
                continue; // Skip this rule (shouldBlockFImpliesRule already logs the reason)
            }


            // Does this rule's side condition leave the conclusion's label free to range?
            // Ask the rule (OnePremiseOneConclusionRule.hasRangingConclusionLabel) rather
            // than inspecting the formula, so a new rule of the same shape cannot silently
            // take the wrong path. Only T~ answers true in Table 2.
            boolean isTNot = (r instanceof rules.ipl.OnePremiseOneConclusionRule)
                    && ((rules.ipl.OnePremiseOneConclusionRule) r).hasRangingConclusionLabel();

            // For regular rules (not T-not), check whether we already tried applying this rule to this formula.
            // proofTree is always an IPLProofTree: this applicator is only ever instantiated
            // by IPLSimpleStrategy, whose createPTInstance() always constructs IPLProofTree nodes.
            // Every rule (including F_NOT) tracks by formula + label: per the paper, "each
            // rule can be applied at most once for each particular choice of ls-formulas as
            // premises", and an ls-formula includes its label, so F ~p : c1 and F ~p : c5
            // are different instances. T~ is excluded here because its instances are keyed
            // by the conclusion's label instead, below.
            String baseRuleInstance = isTNot ? null : r.toString() + ":" + sf.toString();
            if (baseRuleInstance != null) {
                IPLProofTree iplTree = (IPLProofTree) proofTree;
                if (iplTree.wasRuleInstanceApplied(baseRuleInstance)) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logRuleBlocked(r.toString(), sf.toString(),
                                "rinstance exists: " + baseRuleInstance);
                    }
                    continue;
                }
            }

            SignedFormulaList sfl;

            if (isTNot) {
                // T-not is persistent, like T->: produce ONE not-yet-derived conclusion per
                // invocation (mirroring IPLTwoPremiseRuleApplicator's one-auxiliary-at-a-time
                // strategy for T->) instead of eagerly sweeping every accessible label at
                // once. Under Definition 5.3, completeness is recognized recursively from
                // atomic witnesses without requiring every F A:cj to be physically derived
                // first, so re-selection (persistence) naturally covers only the labels
                // actually still needed.
                sfl = generateNextTNotConclusion(proofTree, sfb, sf, r);
                if (IPLTracer.isEnabled()) {
                    tracer.logInfo("T\u00AC persistent: " + sfl.size()
                            + " not-yet-derived conclusion for the next accessible label");
                }
            } else {
                // Regular rule
                sfl = r.getPossibleConclusions(sfb.getSignedFormulaFactory(), sfb.getFormulaFactory(),
                        new SignedFormulaList(sf));
            }

            // TODO: "Change (check whether sfl!=null) needed for MCI, since
            // MCIRules.T_NOT_CONS is not guaranteed to be applicable"
            if (sfl != null && sfl.size() > 0) {
                boolean actuallyAddedFormula = false;

                for (int j = 0; j < sfl.size(); j++) {
                    SignedFormula newFormula = sfl.get(j);

                    // Avoid duplicates
                    if (proofTree.getNode(newFormula) != null) {
                        if (IPLTracer.isEnabled()) {
                            tracer.logInfo("Conclusion already exists: " + newFormula);
                        }
                        continue;
                    }

                    // For T-not (persistent), check rinstances of each individual conclusion,
                    // since it may generate multiple conclusions for different labels at different times
                    if (isTNot) {
                        IPLProofTree iplTree = (IPLProofTree) proofTree;
                        String ruleInstance = createRuleInstanceKey(r.toString(), sf, newFormula);
                        if (iplTree.wasRuleInstanceApplied(ruleInstance)) {
                            if (IPLTracer.isEnabled()) {
                                tracer.logRuleBlocked("T_NOT", sf.toString(),
                                        "T\u00AC rinstance exists: " + ruleInstance);
                            }
                            continue; // Do not apply, it was already applied
                        }
                        iplTree.registerRuleInstance(ruleInstance);
                    }

                    // Use SignedFormulaNode for compatibility with ClassicalProofTree
                    // The content can be a LabelledFormula (with a label) or a plain SignedFormula
                    proofTree.addLast(new SignedFormulaNode(newFormula, SignedFormulaNodeState.NOT_ANALYSED,
                            strategy.createOrigin(r, proofTree.getNode(sf), null)));

                    if (newFormula instanceof LabelledFormula) {
                        LabelledFormula lf = (LabelledFormula) newFormula;
                        if (IPLTracer.isEnabled()) {
                            tracer.logRuleApplied(r.toString(), sf.toString(), lf.toString());
                        }
                        // No eager materialization of derived formulas beyond this
                        // conclusion. Completeness (Definition 5.3) is re-checked
                        // recursively on demand by
                        // IPLCanonicalStrategyImplementation.isCompletelyAnalyzed(),
                        // never by consulting a materialized set.
                    }

                    actuallyAddedFormula = true;
                }

                // Only mark as applied if we actually added new formulas
                if (actuallyAddedFormula) {
                    // Record the instance now that the rule is known to have fired
                    // (Algorithm 1, line 13, which follows line 12's expansion of b).
                    // Registering earlier would burn an instance that produced nothing,
                    // the same defect that made tryPBAtAlternativeLabels block instances
                    // it had never actually applied.
                    if (baseRuleInstance != null) {
                        ((IPLProofTree) proofTree).registerRuleInstance(baseRuleInstance);
                    }
                    hasApplied = true;
                }
            }

        }

        /*
         * if (r != NullRule.INSTANCE) { hasApplied = true;
         *
         * SignedFormulaList sfl = r.getPossibleConclusions(sfb
         * .getSignedFormulaFactory(), sfb.getFormulaFactory(), new
         * SignedFormulaList(sf));
         *
         * // TODO: "Change (check whether sfl!=null) needed for MCI, since //
         * MCIRules.T_NOT_CONS is not guaranteed to be applicable" if (sfl != null) {
         *
         * proofTree.removeFromPBCandidates(sf, SignedFormulaNodeState.ANALYSED);
         *
         * for (int j = 0; j < sfl.size(); j++) { proofTree.addLast(new
         * SignedFormulaNode(sfl.get(j), SignedFormulaNodeState.NOT_ANALYSED, strategy
         * .createOrigin(r, proofTree.getNode(sf), null))); } } else { return false; } }
         */
        return hasApplied;
    }

    private Rule chooseOnePremiseRule(ClassicalProofTree cpt, SignedFormula sf) {

        OnePremiseRuleList onePremiseRules = (OnePremiseRuleList) strategy.getMethod().getRules().get(ruleListName);

        if (sf.getFormula() instanceof CompositeFormula) {
            return onePremiseRules.get(sf.getSign(), ((CompositeFormula) sf.getFormula()).getConnective());
        }

        return NullRule.INSTANCE;

    }

    private List<Rule> getOnePremiseRuleList(ClassicalProofTree cpt, SignedFormula sf) {

        // strategy.getMethod().getRules().get(ruleListName) is always an
        // IPLOnePremiseRuleList: ruleListName is always
        // IPLRuleStructures.ONE_PREMISE_RULE_LIST (see IPLSimpleStrategy's
        // constructor), which IPLRuleStructures always registers as one.
        IPLOnePremiseRuleList onePremiseRules =
                (IPLOnePremiseRuleList) strategy.getMethod().getRules().get(ruleListName);

        if (sf.getFormula() instanceof CompositeFormula) {
            return onePremiseRules.getMany(((CompositeFormula) sf.getFormula()).getConnective(), sf.getSign());
        }

        return new ArrayList<Rule>();

    }

    /**
     * Checks the termination proviso for the two constant-introducing rules, F-> and F~.
     *
     * Condition: do NOT apply the rule to F A->B : ci (resp. F ~A : ci) if the branch
     * already has a formula T A : ch for some constant ch such that ch <= ci.
     *
     * <p>The paper states the proviso for F->1 only, and Appendix A's note on the
     * variable-free system of Table 2 likewise names only F->. That is not an omission
     * in the theory: Section 3 defines ~A as A -> \u22A5 and says the rules for ~ "are
     * included only to improve the system's efficiency", each being "a particular
     * instance of a more general rule of ->", with F~1 an instance of F->1. So F~
     * inherits the proviso by being F-> with B = \u22A5, and there is nothing extra to
     * state. Definition 5.3 agrees: its clause for F ~A : ci is the clause for
     * F A->B : ci with the F B conjunct dropped, which is what B = \u22A5 leaves.
     *
     * <p>Here that inheritance has to be restored by hand, because F~ is reified as its
     * own {@link IPLRules#F_NOT} rather than expanded into F->. Without it the procedure
     * does not terminate: F ~A : ci mints a constant unconditionally, a universal T ~B
     * formula then fires at the new constant and derives another F ~A at it, and so on.
     * Measured on SYJ106+1 (three formulas, five atoms): constants grew past 497 without
     * the branch ever being finished; with the proviso the problem is decided in 133 ms.
     *
     * <p>No analogue of F->3 is needed for F~. F->3 concludes F B : cj, which for
     * B = \u22A5 is vacuous, so for ~ the proviso alone is the whole measure.
     *
     * @param proofTree the current proof tree
     * @param sf the formula F A->B : ci to check
     * @return true if the rule must be blocked, false if it may be applied
     */
    private boolean shouldBlockFImpliesRule(ClassicalProofTree proofTree, SignedFormula sf) {
        // Check that it is F A->B
        if (!sf.getSign().equals(IPLSigns.FALSE)) {
            return false; // Not F, do not block
        }

        if (!(sf.getFormula() instanceof CompositeFormula)) {
            return false; // Not composite, do not block
        }

        CompositeFormula comp = (CompositeFormula) sf.getFormula();
        boolean isImplies = comp.getConnective().equals(IPLConnectives.IMPLIES);
        boolean isNot = comp.getConnective().equals(IPLConnectives.NOT);
        if (!isImplies && !isNot) {
            return false; // neither -> nor ~, do not block
        }

        // It is F A->B, check the proviso
        if (!(sf instanceof LabelledFormula)) {
            return false; // No label, we cannot check
        }

        LabelledFormula lfMain = (LabelledFormula) sf;
        FormulaLabel ciLabel = lfMain.getLabel();

        // A is the left subformula of A->B, and the only subformula of ~A
        Formula aFormula = comp.getImmediateSubformulas().get(0);

        Context context = getContextFromLabel(ciLabel);
        if (context == null) {
            return false; // No Context, we cannot check; do not block, to be safe
        }

        // Look for T A : ch physically in b: the paper literally says "T A : ch
        // does not occur ... in the branch b", and since T-monotonicity only
        // propagates UPWARD (ci<=cj), there is never a witness at ch<=ci derivable
        // by monotonicity that is not already physically in b -- the search goes
        // "downward/equal", the opposite direction from where monotonicity
        // propagates. Iterating the physical branch is correct and sufficient.
        // proofTree is always an IPLProofTree: this applicator is only ever
        // instantiated by IPLSimpleStrategy, whose createPTInstance() always
        // constructs IPLProofTree nodes.
        IPLProofTree iplTree = (IPLProofTree) proofTree;
        java.util.List<SignedFormula> physicalB = iplTree.getPhysicalFormulas();

        // Look for T A : ch physically in b
        for (SignedFormula candidate : physicalB) {
            // Look for T A : ch
            if (candidate.getSign().equals(IPLSigns.TRUE) &&
                candidate.getFormula().equals(aFormula) &&
                candidate instanceof LabelledFormula) {

                LabelledFormula lfCandidate = (LabelledFormula) candidate;
                FormulaLabel chLabel = lfCandidate.getLabel();

                // Check that label ch is accessible
                if (!iplTree.isLabelAccessible(chLabel)) {
                    continue; // Skip this formula, its label is not accessible
                }

                // Check whether ch <= ci
                boolean chEqualsCI = chLabel.equals(ciLabel);
                boolean chLowerOrEqualCI = context.isLowerOrEqualTo(chLabel, ciLabel);

                if (chEqualsCI || chLowerOrEqualCI) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logRuleBlocked(isNot ? "F_NOT" : "F_IMPLIES", sf.toString(),
                                "Proviso: found T " + aFormula + " : " + chLabel + " where "
                                        + chLabel + " \u2264 " + ciLabel);
                    }
                    return true; // BLOCK the application of F->
                }
            }
        }

        if (IPLTracer.isEnabled()) {
            tracer.logInfo("Proviso (F\u2192): no T " + aFormula + " : ch where ch \u2264 " + ciLabel + " found");
        }
        return false; // Do not block
    }


    /**
     * Gets the Context from a FormulaLabel
     */
    private Context getContextFromLabel(FormulaLabel label) {
        if (label instanceof ContextFormulaLabel) {
            return ((ContextFormulaLabel) label).getContext();
        }
        return null;
    }

    /**
     * Generates at most ONE not-yet-derived conclusion F A:cj for T-A:ci, picking
     * the first accessible cj (ci <= cj, in Context label order for determinism)
     * whose F A:cj is not already physically on the branch. Returns an empty list
     * once every accessible label has already been covered.
     *
     * This mirrors {@link IPLTwoPremiseRuleApplicator#tryToApplyTwoPremiseRule}'s
     * one-auxiliary-at-a-time strategy for T->: rather than eagerly materializing
     * F A:cj for every accessible label in a single call, persistence --
     * re-selecting T-A:ci on later rounds while Definition 5.3 still finds it
     * incomplete -- naturally covers additional labels only as they are
     * actually needed, and stops as soon as they are not.
     */
    private SignedFormulaList generateNextTNotConclusion(ClassicalProofTree proofTree,
                                                         SignedFormulaBuilder sfb,
                                                         SignedFormula sf,
                                                         Rule rule) {
        SignedFormulaList result = new SignedFormulaList();

        if (!(sf instanceof LabelledFormula)) {
            return result;
        }

        LabelledFormula lf = (LabelledFormula) sf;
        FormulaLabel ciLabel = lf.getLabel();
        Context context = getContextFromLabel(ciLabel);

        if (context == null) {
            return result;
        }

        SignedFormula baseSf = lf.getSignedFormula();
        if (!(baseSf.getFormula() instanceof CompositeFormula)) {
            return result;
        }
        CompositeFormula comp = (CompositeFormula) baseSf.getFormula();
        Formula aFormula = comp.getImmediateSubformulas().get(0);

        // Get the IPLProofTree to check label accessibility (proofTree is always an
        // IPLProofTree: this applicator is only ever instantiated by IPLSimpleStrategy,
        // whose createPTInstance() always constructs IPLProofTree nodes)
        IPLProofTree iplTree = (IPLProofTree) proofTree;

        for (FormulaLabel cjLabel : context.getLabels()) {
            // FILTER: only consider labels accessible from the current branch
            if (!iplTree.isLabelAccessible(cjLabel)) {
                continue;
            }
            if (!ciLabel.equals(cjLabel) && !context.isLowerOrEqualTo(ciLabel, cjLabel)) {
                continue;
            }

            SignedFormula falseA = sfb.createSignedFormula(IPLSigns.FALSE, aFormula);
            LabelledFormula conclusion = new LabelledFormula(cjLabel, falseA);

            if (proofTree.getNode(conclusion) != null) {
                continue; // already derived for this label
            }
            if (iplTree != null) {
                String ruleInstance = createRuleInstanceKey(rule.toString(), sf, conclusion);
                if (iplTree.wasRuleInstanceApplied(ruleInstance)) {
                    continue; // already covered, even if the node was removed/renamed
                }
            }

            result.add(conclusion);
            return result; // one label per invocation; the rest wait for re-selection
        }

        return result; // every accessible label already covered
    }

    /**
     * Creates a unique key to identify a one-premise rule instance.
     *
     * @param ruleName the rule's name
     * @param premise the premise (main formula)
     * @param conclusion the generated conclusion
     * @return unique key for the rule instance
     */
    private String createRuleInstanceKey(String ruleName, SignedFormula premise, SignedFormula conclusion) {
        return ruleName + ":" + premise.toString() + "\u2192" + conclusion.toString();
    }

}
