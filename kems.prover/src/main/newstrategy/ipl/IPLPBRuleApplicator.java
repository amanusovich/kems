/*
 * Created on 2025
 */
package main.newstrategy.ipl;

import logic.formulas.CompositeFormula;
import logic.formulas.Formula;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.FormulaSign;
import logic.signedFormulas.PBCandidateList;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaBuilder;
import logicalSystems.ipl.IPLConnectives;
import logicalSystems.ipl.IPLProofTree;
import logicalSystems.ipl.IPLSignedFormulaFactory;
import logicalSystems.ipl.IPLRules;
import logicalSystems.ipl.IPLRuleStructures;
import logicalSystems.ipl.IPLSigns;
import main.newstrategy.ISimpleStrategy;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import main.strategy.ClassicalProofTree;
import main.strategy.applicator.IProofTransformation;
import rules.Rule;

/**
 * Rule applicator specific to PB in IPL, used as a last resort.
 *
 * PB is applied when:
 * 1. We have a major premise for a two-premise rule
 * 2. The required minor premise does not exist
 * 3. All other rules have been tried without success
 *
 * Process:
 * 1. Apply PB to generate the missing minor premise
 * 2. Immediately apply the corresponding two-premise rule
 */
public class IPLPBRuleApplicator implements IProofTransformation {

    private static final IPLTracer tracer = IPLTracer.getInstance();

    private ISimpleStrategy strategy;

    /**
     * Constructor for IPLPBRuleApplicator
     * @param strategy the IPL strategy
     * @param ruleListName rule list name (unused, kept for compatibility)
     */
    public IPLPBRuleApplicator(ISimpleStrategy strategy, String ruleListName) {
        super();
        this.strategy = strategy;
        // ruleListName is not used in this implementation
    }

    /**
     * Applies PB to a single specific formula.
     * This method is used by the canonical algorithm implementation.
     *
     * @param current the proof tree
     * @param sfb the signed formula builder
     * @param candidate the specific formula to try PB on
     * @return true if PB was applied, false otherwise
     */
    public boolean applySingle(ClassicalProofTree current, SignedFormulaBuilder sfb, SignedFormula candidate) {
        if (!(candidate.getFormula() instanceof CompositeFormula)) {
            return false;
        }

        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: trying for single formula: " + candidate);
        }

        PBCandidateList singleCandidateList = new PBCandidateList();
        singleCandidateList.add(candidate);

        return tryToApplyPBAsLastResort(current, sfb, singleCandidateList);
    }

    /**
     * The sole caller, {@code IPLCanonicalStrategyImplementation.processOpenBranch()},
     * only invokes this once {@code selectUnanalyzedFormula()} has already scanned the
     * whole branch (locals plus ancestors) and found no candidate: every composite
     * ls-formula there is either completely analyzed per Definition 5.3, or is one on
     * which no operational rule could fire — which is exactly the situation PB exists
     * to resolve. There is nothing left to check here before proceeding straight to PB.
     */
    @Override
    public boolean apply(ClassicalProofTree current, SignedFormulaBuilder sfb) {
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: starting as last resort");
        }

        // Instead of relying only on getPBCandidates() (which may be empty if formulas were
        // already "processed"), examine ALL composite formulas in the tree to see whether they
        // could benefit from PB
        PBCandidateList allCompositeCandidates = findAllCompositeFormulas(current);

        if (allCompositeCandidates.size() > 0) {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB: " + allCompositeCandidates.size() + " composite candidates (FIFO order)");
            }
            // Do NOT sort: keep the FIFO order (insertion order) from the top-down iterator
            // allCompositeCandidates.sort(strategy.getComparator());
            return tryToApplyPBAsLastResort(current, sfb, allCompositeCandidates);
        }

        if (IPLTracer.isEnabled()) {
            tracer.logPBSkipped("(branch)", "no composite candidates");
        }
        return false;
    }

    /**
     * Checks whether some instance of the formula already exists in the tree,
     * regardless of label. Only sign and formula are compared.
     *
     * DESIGN NOTE: This check intentionally ignores labels. Label compatibility
     * is checked by the two-premise applicator when the rule is actually applied.
     * If PB checked labels, it would apply PB for every incompatible label,
     * producing infinitely many branches (each PB enables rules that create new
     * labels via F->1, propagation, and more PB). Ignoring labels acts as a
     * termination guard: PB only applies when the auxiliary subformula does not
     * exist at ANY label, bounding the number of PB applications by the number
     * of subformulas of the initial formula -- the subformula property
     * (Definitions 3.1) is what bounds the number of branches produced by PB in
     * the termination argument (Theorem 5.9: "new branches are produced only by
     * applications of PB which ... are only applied to subformulas of the
     * formulas in a branch").
     *
     * Paper: Algorithm 1 (S5), PB application when the minor premise is missing.
     */
    private boolean formulaExistsInTree(ClassicalProofTree current, SignedFormula target) {
        main.proofTree.iterator.IProofTreeVeryBasicIterator it = current.getTopDownIterator();
        while (it.hasNext()) {
            main.proofTree.INode node = it.next();
            if (node instanceof SignedFormulaNode) {
                SignedFormulaNode sfNode = (SignedFormulaNode) node;
                SignedFormula sf = (SignedFormula) sfNode.getContent();

                if (sf.getSign().equals(target.getSign()) &&
                    sf.getFormula().equals(target.getFormula())) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logInfo("PB: formula instance found: " + sf);
                    }
                    return true;
                }
            }
        }
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: no instance found: " + target.getSign() + " " + target.getFormula());
        }
        return false;
    }

    /**
     * Finds all composite formulas in the tree that could benefit from PB.
     * Uses FIFO order: formulas are processed in the order they were added to
     * the tree (top-down iteration from the root).
     *
     * IMPORTANT: Considers formulas from the current branch AND its ancestors
     * (but not sibling branches), via getTopDownIterator(). This allows PB to
     * apply over accessible ancestor formulas.
     *
     * Tracking by accessibility group prevents infinite loops: two branches are
     * in the same group if one is an ancestor of the other. When a branch
     * applies PB over an ancestor formula, the registration happens in the
     * ancestor branch where the formula lives, and every descendant branch
     * (same group) can see that registration and will not apply PB again.
     */
    private PBCandidateList findAllCompositeFormulas(ClassicalProofTree current) {
        PBCandidateList candidates = new PBCandidateList();

        // Use a top-down iterator to consider formulas from the current branch and its
        // ancestors (but not sibling branches). This allows PB to apply over ancestor formulas.
        main.proofTree.iterator.IProofTreeVeryBasicIterator it = current.getTopDownIterator();

        // current is always an IPLProofTree: this applicator is only ever
        // instantiated by IPLSimpleStrategy, whose createPTInstance() always
        // constructs IPLProofTree nodes.
        logicalSystems.ipl.IPLProofTree iplTree = (logicalSystems.ipl.IPLProofTree) current;

        while (it.hasNext()) {
            main.proofTree.INode node = it.next();

            if (!(node instanceof SignedFormulaNode)) {
                continue;
            }

            SignedFormulaNode sfNode = (SignedFormulaNode) node;
            SignedFormula sf = (SignedFormula) sfNode.getContent();

            // Only consider composite formulas that are neither TOP nor BOTTOM
            if (!(sf.getFormula() instanceof CompositeFormula) ||
                sf.getFormula().toString().equals("TOP") ||
                sf.getFormula().toString().equals("BOTTOM")) {
                continue;
            }

            // Check that the label is accessible in the current branch (for IPL)
            if (sf instanceof logic.labelledFormulas.LabelledFormula) {
                logic.labelledFormulas.LabelledFormula lf = (logic.labelledFormulas.LabelledFormula) sf;
                if (!iplTree.isLabelAccessible(lf.getLabel())) {
                    continue; // Skip formulas whose label is not accessible
                }
            }

            if (!candidates.contains(sf)) {
                candidates.add(sf);
                if (IPLTracer.isEnabled()) {
                    tracer.logInfo("PB candidate: " + sf);
                }
            }
        }

        return candidates;
    }

    /**
     * Attempts to apply PB as a last resort for two-premise rules OR plain PB
     */
    protected boolean tryToApplyPBAsLastResort(ClassicalProofTree current, SignedFormulaBuilder sfb,
            PBCandidateList candidates) {

        // Get all IPL two-premise rules (not just PB_RULE_LIST)
        var twoPremiseRules = strategy.getMethod().getRules().get(IPLRuleStructures.TWO_PREMISE_RULE_LIST);
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: working with 2-premise rules as last resort");
        }

        // For each candidate, check whether it can be the major premise of some two-premise rule
        // IMPORTANT: Keep evaluating candidates even if some cannot apply PB
        // (a later candidate might still be able to apply it)
        for (int i = 0; i < candidates.size(); i++) {
            SignedFormula candidate = candidates.get(i);
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB: evaluating candidate: " + candidate);
            }

            // CASE 1: Find ALL two-premise rules where this candidate can be the major premise
            java.util.List<Rule> applicableRules = findAllTwoPremiseRulesForCandidate(candidate, twoPremiseRules);

            if (!applicableRules.isEmpty()) {
                if (IPLTracer.isEnabled()) {
                    tracer.logInfo("PB: " + applicableRules.size() + " applicable 2-premise rules found");
                }

                // By the time we reach this point from apply(), we already know that
                // twoPremiseApplicator.applySingle failed for this formula. That means every
                // two-premise rule was tried and none could apply. So we only apply PB when
                // there is a rule whose minor premise is NOT available. If every rule has its
                // minor premise available but still could not apply, their conclusions already
                // exist or the instances were already applied, and PB should not be applied.
                Rule ruleToApplyWithPB = null;
                SignedFormula auxToApplyWithPB = null;

                for (Rule rule : applicableRules) {
                    SignedFormula requiredAux = getIPLRuleAuxiliaryCandidate(rule, candidate, sfb);
                    if (!formulaExistsInTree(current, requiredAux)) {
                        // This rule's minor premise is not available - PB candidate
                        if (IPLTracer.isEnabled()) {
                            tracer.logInfo("PB: rule " + rule + " missing minor premise: " + requiredAux);
                        }
                        if (ruleToApplyWithPB == null) {
                            ruleToApplyWithPB = rule;
                            auxToApplyWithPB = requiredAux;
                        }
                    } else {
                        if (IPLTracer.isEnabled()) {
                            tracer.logInfo("PB: rule " + rule + " has minor premise: " + requiredAux);
                        }
                    }
                }

                // Only apply PB if we found a rule whose minor premise is not available
                if (ruleToApplyWithPB != null) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logInfo("PB: selected rule: " + ruleToApplyWithPB);
                        tracer.logInfo("PB: required minor premise: " + auxToApplyWithPB);
                        tracer.logInfo("PB: minor premise missing - applying PB");
                    }

                    // Try to apply PB and then immediately the two-premise rule
                    // If it cannot be applied (already applied), continue with the next candidate
                    boolean applied = applyPBAndTwoPremiseRule(current, sfb, candidate, ruleToApplyWithPB, auxToApplyWithPB);
                    if (applied) {
                        return true; // PB applied successfully
                    } else {
                        if (IPLTracer.isEnabled()) {
                            tracer.logPBSkipped(candidate.toString(), "already applied for this candidate");
                        }
                        // Continue with the next candidate
                    }
                } else {
                    if (IPLTracer.isEnabled()) {
                        tracer.logPBSkipped(candidate.toString(), "all rules have minor premise but couldn't apply");
                    }
                }
            }
        }

        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: no opportunity found as last resort");
        }
        return false;
    }

    /**
     * Dynamically finds ALL two-premise rules where the candidate can be the major premise.
     * Returns every applicable rule, not just the first one.
     */
    private java.util.List<Rule> findAllTwoPremiseRulesForCandidate(SignedFormula candidate, Object twoPremiseRulesList) {
        java.util.List<Rule> result = new java.util.ArrayList<>();

        // Only composite formulas can be major premises
        if (!(candidate.getFormula() instanceof CompositeFormula)) {
            return result;
        }

        CompositeFormula comp = (CompositeFormula) candidate.getFormula();

        // twoPremiseRulesList is always an IPLConnectiveRoleSignRuleList: its sole
        // caller passes strategy.getMethod().getRules().get(TWO_PREMISE_RULE_LIST),
        // which IPLRuleStructures always registers as one.
        rules.structures.IPLConnectiveRoleSignRuleList ruleList =
            (rules.structures.IPLConnectiveRoleSignRuleList) twoPremiseRulesList;

        // Look up matching rules in both roles (LEFT and RIGHT)
        java.util.List<Rule> leftRules = ruleList.getMany(comp.getConnective(), rules.KERuleRole.LEFT, candidate.getSign());
        if (leftRules != null) {
            result.addAll(leftRules);
        }

        java.util.List<Rule> rightRules = ruleList.getMany(comp.getConnective(), rules.KERuleRole.RIGHT, candidate.getSign());
        if (rightRules != null) {
            result.addAll(rightRules);
        }

        return result;
    }

    /**
     * Dynamically obtains the required auxiliary for any two-premise rule.
     * Uses the rule's own API (getAuxiliaryCandidates) to determine what it needs.
     */
    private SignedFormula getIPLRuleAuxiliaryCandidate(Rule rule, SignedFormula candidate, SignedFormulaBuilder sfb) {
        if (!(rule instanceof rules.ipl.TwoPremisesOneConclusionRule)) {
            return null;
        }

        rules.ipl.TwoPremisesOneConclusionRule twoPremiseRule =
            (rules.ipl.TwoPremisesOneConclusionRule) rule;

        // Use the rule's own getAuxiliaryCandidates method to find out what it needs
        logic.labelledFormulas.LabelledFormulaFactory labelledFactory =
            new logic.labelledFormulas.LabelledFormulaFactory();

        logic.signedFormulas.SignedFormulaList auxiliaryCandidates =
            twoPremiseRule.getAuxiliaryCandidates(
                labelledFactory,
                sfb.getSignedFormulaFactory(),
                sfb.getFormulaFactory(),
                candidate
            );

        if (auxiliaryCandidates == null || auxiliaryCandidates.size() == 0) {
            return null;
        }

        // Return the first auxiliary candidate (no specific label yet, PB will assign one)
        SignedFormula auxiliar = (SignedFormula) auxiliaryCandidates.get(0);
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: auxiliary determined for " + rule + ": " + auxiliar);
        }
        return auxiliar;
    }

    /**
     * Dynamically generates the conclusion for any two-premise rule.
     * Uses the rule's own API (getPossibleConclusions) to generate the conclusion.
     */
    private SignedFormula generateIPLRuleConclusion(Rule rule, SignedFormula mainPremise, SignedFormula auxPremise, SignedFormulaBuilder sfb) {
        if (!(rule instanceof rules.ipl.TwoPremisesOneConclusionRule)) {
            return null;
        }

        rules.ipl.TwoPremisesOneConclusionRule twoPremiseRule =
            (rules.ipl.TwoPremisesOneConclusionRule) rule;

        // Build a list with both premises (main first, aux second)
        logic.signedFormulas.SignedFormulaList premises = new logic.signedFormulas.SignedFormulaList();
        premises.add(mainPremise);
        premises.add(auxPremise);

        // Use the rule's getPossibleConclusions
        logic.signedFormulas.SignedFormulaList conclusions =
            twoPremiseRule.getPossibleConclusions(
                sfb.getSignedFormulaFactory(),
                sfb.getFormulaFactory(),
                premises
            );

        if (conclusions == null || conclusions.size() == 0) {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB: no conclusions for rule " + rule + " (main label: " + mainPremise.getLabel()
                    + ", aux label: " + auxPremise.getLabel() + ")");
            }
            return null;
        }

        // Return the first conclusion
        SignedFormula conclusion = (SignedFormula) conclusions.get(0);
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: conclusion generated for " + rule + ": " + conclusion);
        }
        return conclusion;
    }

    /**
     * Creates a SignedFormula appropriate for IPL (LabelledFormula with ContextFormulaLabel).
     * {@code sfb}'s factory is always an {@link IPLSignedFormulaFactory} here: every entry
     * point into the IPL strategy (GUI, web server, benchmark runner) constructs its
     * {@code SignedFormulaCreator} with the literal package name {@code "ipl"}, which is
     * the only condition under which that factory type is selected.
     */
    private SignedFormula createIPLSignedFormula(SignedFormulaBuilder sfb, FormulaSign sign, Formula formula) {
        IPLSignedFormulaFactory iplFactory = (IPLSignedFormulaFactory) sfb.getSignedFormulaFactory();
        return iplFactory.createLabelledFormula(sign, formula);
    }

    /**
     * Creates a SignedFormula appropriate for IPL with a specific label.
     * {@code sfb}'s factory is always an {@link IPLSignedFormulaFactory}, for the same
     * reason as {@link #createIPLSignedFormula}. {@code label} itself, however, is not
     * always already a {@code ContextFormulaLabel}: some callers pass a fresh label
     * derived via {@code FormulaLabel.getGreaterFormulaLabel()} or similar, which
     * produces a plain {@code FormulaLabel} not yet registered in the shared
     * {@code Context} — that conversion below is genuinely needed.
     */
    private SignedFormula createIPLSignedFormulaWithLabel(SignedFormulaBuilder sfb, FormulaSign sign, Formula formula, FormulaLabel label) {
        IPLSignedFormulaFactory iplFactory = (IPLSignedFormulaFactory) sfb.getSignedFormulaFactory();

        // Make sure the label is a ContextFormulaLabel
        logic.labelledFormulas.ContextFormulaLabel contextLabel;
        if (label instanceof logic.labelledFormulas.ContextFormulaLabel) {
            contextLabel = (logic.labelledFormulas.ContextFormulaLabel) label;
        } else {
            // Convert FormulaLabel to ContextFormulaLabel using the factory's Context
            contextLabel = new logic.labelledFormulas.ContextFormulaLabel(
                iplFactory.getContext(), label.getIndex());
            // Make sure it is registered in the Context
            if (!iplFactory.getContext().getLabels().contains(contextLabel)) {
                iplFactory.getContext().addElement(contextLabel);
            }
        }

        // Create the SignedFormula with ContextFormulaLabel using the IPL factory
        return iplFactory.createLabelledFormula(contextLabel,
                                iplFactory.createSignedFormula(sign, formula));
    }

    /**
     * Creates the opposite formula appropriate for IPL
     */
    private SignedFormula createOppositeIPLSignedFormula(SignedFormulaBuilder sfb, SignedFormula original) {
        FormulaSign oppositeSign = original.getSign().equals(IPLSigns.TRUE) ? (FormulaSign) IPLSigns.FALSE : (FormulaSign) IPLSigns.TRUE;
        return createIPLSignedFormula(sfb, oppositeSign, original.getFormula());
    }

    /**
     * Applies PB and then immediately the two-premise rule.
     *
     * Implements Algorithm 1 lines 14-18: applies PB to introduce the missing
     * minor premise, applies the two-premise rule on the left branch, and
     * registers the instance in the global rinstances set to prevent
     * re-application.
     */
    private boolean applyPBAndTwoPremiseRule(ClassicalProofTree current, SignedFormulaBuilder sfb,
            SignedFormula mainPremise, Rule rule, SignedFormula requiredAux) {

        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB+Rule: main=" + mainPremise + ", rule=" + rule + ", aux=" + requiredAux);
        }

        // STEP 1: Get the shared label (the same one as the major premise)
        FormulaLabel sharedLabel = mainPremise.getLabel();
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: using major premise label: " + sharedLabel);
        }

        logic.labelledFormulas.ContextFormulaLabel contextSharedLabel;
        if (sharedLabel instanceof logic.labelledFormulas.ContextFormulaLabel) {
            contextSharedLabel = (logic.labelledFormulas.ContextFormulaLabel) sharedLabel;
        } else {
            IPLSignedFormulaFactory iplFactory = (IPLSignedFormulaFactory) sfb.getSignedFormulaFactory();
            contextSharedLabel = new logic.labelledFormulas.ContextFormulaLabel(
                iplFactory.getContext(), sharedLabel.getIndex());
            if (!iplFactory.getContext().getLabels().contains(contextSharedLabel)) {
                iplFactory.getContext().addElement(contextSharedLabel);
            }
        }

        FormulaSign oppositeSign = requiredAux.getSign().equals(IPLSigns.TRUE) ?
            (FormulaSign) IPLSigns.FALSE : (FormulaSign) IPLSigns.TRUE;

        // STEP 2: Prepare the auxiliary formulas (with the shared label)
        SignedFormula auxWithSharedLabel = createIPLSignedFormulaWithLabel(sfb,
            (FormulaSign) requiredAux.getSign(), requiredAux.getFormula(), contextSharedLabel);

        SignedFormula auxOpposite = createIPLSignedFormulaWithLabel(sfb,
            oppositeSign, requiredAux.getFormula(), contextSharedLabel);

        SignedFormula mainPremiseWithContextLabel;
        if (mainPremise.getLabel() instanceof logic.labelledFormulas.ContextFormulaLabel) {
            mainPremiseWithContextLabel = mainPremise;
        } else {
            mainPremiseWithContextLabel = createIPLSignedFormulaWithLabel(sfb,
                (FormulaSign) mainPremise.getSign(), mainPremise.getFormula(), contextSharedLabel);
        }

        // STEP 3: If the minor premise already exists, the rule can fire directly -- do not apply PB
        // (current is always an IPLProofTree: see createIPLSignedFormula.)
        SignedFormula existingRequired = ((IPLProofTree) current).findFormulaWithSignAndLabel(
            requiredAux.getFormula(), requiredAux.getSign(), contextSharedLabel);
        if (existingRequired != null) {
            if (IPLTracer.isEnabled()) {
                tracer.logPBSkipped(mainPremise.toString(), "required aux already exists: " + existingRequired);
            }
            return false;
        }

        // STEP 4: Check rinstances -- if the instance was already applied, try alternative labels
        // (Algorithm 1 lines 7/10: "r not-in rinstances"). The key uses the same format as
        // IPLTwoPremiseRuleApplicator.createRuleInstanceKey for consistency.
        String ruleInstanceKey = rule.toString() + ":" + mainPremiseWithContextLabel.toString()
                + ":" + auxWithSharedLabel.toString();

        {
            IPLProofTree iplTree = (IPLProofTree) current;
            if (iplTree.wasRuleInstanceApplied(ruleInstanceKey)) {
                if (IPLTracer.isEnabled()) {
                    tracer.logPBSkipped(mainPremise.toString(), "rule instance already applied: "
                        + ruleInstanceKey + " - trying accessible labels cj > ci");
                }
                return tryPBAtAlternativeLabels(current, sfb, mainPremise, rule, requiredAux,
                        contextSharedLabel, oppositeSign, iplTree);
            }
        }

        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: minor premise missing and rule not yet applied - applying PB");
        }

        // STEP 5: Apply PB to create the missing minor premise
        ClassicalProofTree right = (ClassicalProofTree) current.addRight(new SignedFormulaNode(
                auxOpposite, SignedFormulaNodeState.NOT_ANALYSED, strategy
                        .createOrigin(IPLRules.PB, current.getNode(mainPremise), null)));

        ClassicalProofTree left = (ClassicalProofTree) current.addLeft(new SignedFormulaNode(
                auxWithSharedLabel, SignedFormulaNodeState.NOT_ANALYSED, strategy
                        .createOrigin(IPLRules.PB, current.getNode(mainPremise), null)));

        // STEP 6: Immediately apply the two-premise rule on the left branch
        SignedFormula conclusion = generateIPLRuleConclusion(rule, mainPremiseWithContextLabel, auxWithSharedLabel, sfb);

        if (conclusion == null) {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB: could not generate conclusion");
            }
            return false;
        }

        // STEP 7: Register the rule instance in the global rinstances set (Algorithm 1, line 18).
        // Register it BEFORE adding the conclusion to left (STEP 8) so the viewer's per-node
        // snapshot (recordRinstancesSnapshot in addLast) includes the rule that generated the
        // conclusion, the same way IPLOnePremiseRuleApplicator does it.
        ((IPLProofTree) current).registerRuleInstance(ruleInstanceKey);

        // STEP 8: Add the conclusion to the left branch
        left.addLast(new SignedFormulaNode(conclusion, SignedFormulaNodeState.NOT_ANALYSED, strategy
                .createOrigin(rule, current.getNode(mainPremise), left.getNode(auxWithSharedLabel))));

        if (IPLTracer.isEnabled()) {
            tracer.logRuleApplied(rule.toString(), mainPremise.toString(), auxWithSharedLabel.toString(), conclusion.toString());
            tracer.logPBApplied(mainPremise.toString(), rule.toString(), auxWithSharedLabel.toString(), "left", "right");
        }

        return true;
    }

    /**
     * When PB is blocked at label ci of the major premise (because F(aux):ci
     * already exists), looks for accessible labels cj >= ci where neither
     * T(aux):cj nor F(aux):cj exists yet, and applies PB there instead.
     *
     * For example, for T(A->B):c1 with T(A):c23 missing:
     *   - LEFT: T(A):c23 -> rule gives T(B):c23 -> T_AND -> T(p3):c23 contradicts F(p3):c23 -> CLOSES
     *   - RIGHT: F(A):c23 -> Definition 5.3's condition for T(A->B):c1 at cj=c23 is satisfied
     *
     * NOTE: iterates the physical branch directly (getPhysicalFormulas()). The
     * accessible labels cj come from the Context, which already coincides with
     * Cb = "constants occurring in b" (Definitions 3.1): the constants that
     * occur in some physical formula of the branch.
     */
    private boolean tryPBAtAlternativeLabels(ClassicalProofTree current, SignedFormulaBuilder sfb,
            SignedFormula mainPremise, Rule rule, SignedFormula requiredAux,
            logic.labelledFormulas.ContextFormulaLabel ci, FormulaSign oppositeSign,
            IPLProofTree iplTree) {

        // Collect accessible labels cj >= ci from the physical branch
        java.util.List<SignedFormula> physicalB = iplTree.getPhysicalFormulas();
        java.util.LinkedHashSet<logic.labelledFormulas.ContextFormulaLabel> labelsToTry =
                new java.util.LinkedHashSet<>();

        for (SignedFormula bsf : physicalB) {
            if (!(bsf instanceof logic.labelledFormulas.LabelledFormula)) continue;
            logic.labelledFormulas.FormulaLabel l =
                    ((logic.labelledFormulas.LabelledFormula) bsf).getLabel();
            if (!(l instanceof logic.labelledFormulas.ContextFormulaLabel)) continue;
            logic.labelledFormulas.ContextFormulaLabel cj =
                    (logic.labelledFormulas.ContextFormulaLabel) l;
            if (cj.toString().equals(ci.toString())) continue;          // skip ci
            if (!ci.getContext().isLowerOrEqualTo(ci, cj)) continue;    // need cj >= ci
            if (!iplTree.isLabelAccessible(cj)) continue;               // label must be accessible
            labelsToTry.add(cj);
        }

        for (logic.labelledFormulas.ContextFormulaLabel cj : labelsToTry) {
            // If T(aux):cj already exists, the rule should have fired directly
            SignedFormula existingReq = iplTree.findFormulaWithSignAndLabel(
                    requiredAux.getFormula(), requiredAux.getSign(), cj);
            if (existingReq != null) continue;

            // If F(aux):cj already exists, this label is blocked too
            SignedFormula existingOpp = iplTree.findFormulaWithSignAndLabel(
                    requiredAux.getFormula(), oppositeSign, cj);
            if (existingOpp != null) continue;

            // Create auxiliary formulas at cj (needed for the rinstances key)
            SignedFormula auxWithCj = createIPLSignedFormulaWithLabel(sfb,
                    (FormulaSign) requiredAux.getSign(), requiredAux.getFormula(), cj);
            SignedFormula auxOppositeCj = createIPLSignedFormulaWithLabel(sfb,
                    oppositeSign, requiredAux.getFormula(), cj);

            // Check rinstances for this combination (rule, main, aux@cj)
            String ruleKeyAlt = rule.toString() + ":" + mainPremise.toString() + ":" + auxWithCj.toString();
            if (iplTree.wasRuleInstanceApplied(ruleKeyAlt)) continue;

            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB-ALT: label ci=" + ci + " blocked, applying PB at cj=" + cj
                        + " for aux " + requiredAux.getSign() + "(" + requiredAux.getFormula() + ")");
            }

            // Create PB branches
            ClassicalProofTree right = (ClassicalProofTree) current.addRight(new SignedFormulaNode(
                    auxOppositeCj, SignedFormulaNodeState.NOT_ANALYSED, strategy
                            .createOrigin(IPLRules.PB, current.getNode(mainPremise), null)));

            ClassicalProofTree left = (ClassicalProofTree) current.addLeft(new SignedFormulaNode(
                    auxWithCj, SignedFormulaNodeState.NOT_ANALYSED, strategy
                            .createOrigin(IPLRules.PB, current.getNode(mainPremise), null)));

            // Apply the rule immediately on the left branch (conclusion at cj)
            // Make sure mainPremise has a ContextFormulaLabel (same as in applyPBAndTwoPremiseRule)
            SignedFormula mainPremiseForConclusion;
            if (mainPremise.getLabel() instanceof logic.labelledFormulas.ContextFormulaLabel) {
                mainPremiseForConclusion = mainPremise;
            } else {
                mainPremiseForConclusion = createIPLSignedFormulaWithLabel(sfb,
                        (FormulaSign) mainPremise.getSign(), mainPremise.getFormula(), ci);
            }
            SignedFormula conclusion = generateIPLRuleConclusion(rule, mainPremiseForConclusion, auxWithCj, sfb);

            // Register the rule instance in the global rinstances set BEFORE adding the
            // conclusion to left (Algorithm 1, line 18): this way the viewer's per-node
            // snapshot includes the rule that generated the conclusion.
            iplTree.registerRuleInstance(ruleKeyAlt);

            if (conclusion != null) {
                left.addLast(new SignedFormulaNode(conclusion, SignedFormulaNodeState.NOT_ANALYSED,
                        strategy.createOrigin(rule, current.getNode(mainPremise),
                                left.getNode(auxWithCj))));
            }

            if (IPLTracer.isEnabled()) {
                String concStr = conclusion != null ? conclusion.toString() : "(null)";
                tracer.logRuleApplied(rule.toString(), mainPremise.toString(),
                        auxWithCj.toString(), concStr);
                tracer.logPBApplied(mainPremise.toString(), rule.toString(),
                        auxWithCj.toString(), "left", "right");
            }

            return true;
        }

        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB-ALT: no viable alternative labels found for "
                    + requiredAux.getSign() + "(" + requiredAux.getFormula() + ")");
        }
        return false;
    }

}
