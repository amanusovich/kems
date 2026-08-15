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

        return tryToApplyPBAsLastResort(current, sfb, singleCandidateList, PBMode.FAST);
    }

    /**
     * How PB decides that the minor premise it needs is missing.
     *
     * <p>Algorithm 1, line 8, asks whether {@code min(r) ∉ b}, where {@code min(r)} is an
     * ls-formula <em>including its label</em> (§3.2: labels and constraints do matter for
     * telling two rule instances apart). {@link #EXACT} asks exactly that question.
     * {@link #FAST} asks the stronger question "does this subformula occur at <em>any</em>
     * label?", which suppresses PB applications the algorithm would make.
     *
     * <p>FAST is what keeps proof search tractable: it decides once and for all that a
     * subformula already present somewhere is never a PB target again on that path,
     * instead of locating, per formula, the state where it turns true. That is worth
     * roughly a factor of the number of constants in the derivation. Its cost is that it
     * can leave a branch with no applicable rule while Definition 5.3 still fails on it —
     * which would report a theorem as a non-theorem. EXACT is therefore consulted before
     * any branch is allowed to be declared completed
     * ({@link main.newstrategy.ipl.IPLCanonicalStrategyImplementation#processOpenBranch}).
     */
    public enum PBMode { FAST, EXACT }

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
        return apply(current, sfb, PBMode.FAST);
    }

    /**
     * Retries PB under Algorithm 1's own applicability test (see {@link PBMode}). Called
     * only when {@link #apply(ClassicalProofTree, SignedFormulaBuilder)} found no target,
     * i.e. at the exact point where the branch would otherwise be declared completed.
     * Rule instances are still filtered through {@code rinstances}, so this cannot
     * re-apply an instance the path already used.
     */
    public boolean applyExact(ClassicalProofTree current, SignedFormulaBuilder sfb) {
        return apply(current, sfb, PBMode.EXACT);
    }

    private boolean apply(ClassicalProofTree current, SignedFormulaBuilder sfb, PBMode mode) {
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: starting as last resort (mode=" + mode + ")");
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
            return tryToApplyPBAsLastResort(current, sfb, allCompositeCandidates, mode);
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
     * Whether the minor premise {@code requiredAux} counts as already available, so that
     * PB need not introduce it. See {@link PBMode}: FAST asks whether the subformula occurs
     * at any label at all; EXACT asks Algorithm 1 line 8's question, i.e. whether the
     * ls-formula occurs at the label PB would actually create it at — the major premise's
     * own label, which is what {@code applyPBAndTwoPremiseRule} uses as the shared label.
     */
    private boolean minorPremiseIsAvailable(ClassicalProofTree current, SignedFormula requiredAux,
            SignedFormula majorPremise, PBMode mode) {
        if (requiredAux == null) return true;
        if (mode == PBMode.FAST) return formulaExistsInTree(current, requiredAux);

        FormulaLabel at = majorPremise.getLabel();
        if (at == null) return formulaExistsInTree(current, requiredAux);
        return ((IPLProofTree) current).findFormulaWithSignAndLabel(
                requiredAux.getFormula(), requiredAux.getSign(), at) != null;
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
            PBCandidateList candidates, PBMode mode) {

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
                    if (!minorPremiseIsAvailable(current, requiredAux, candidate, mode)) {
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
     * When PB cannot be applied at the major premise's own label ci -- because that rule
     * instance is already in {@code rinstances} -- this looks for another label where the
     * same rule has an instance that is still available, which is just a different choice
     * of {@code r} in Algorithm 1, line 7.
     *
     * <p>For example, for T(A-&gt;B):c1 with T(A):c23 missing:
     * <ul>
     *   <li>LEFT: T(A):c23 -&gt; rule gives T(B):c23 -&gt; T_AND -&gt; T(p3):c23 contradicts
     *       F(p3):c23 -&gt; CLOSES</li>
     *   <li>RIGHT: F(A):c23 -&gt; Definition 5.3's condition for T(A-&gt;B):c1 at cj=c23 is
     *       satisfied</li>
     * </ul>
     *
     * <p>Which labels are admissible depends on the rule's own constraint, and the two
     * families point in opposite directions: F&and;<sub>1</sub>, F&and;<sub>2</sub> and
     * F&rarr;<sub>3</sub> need the minor premise at cj &#8804; ci, while T&or;<sub>1</sub>,
     * T&or;<sub>2</sub> and T&rarr;<sub>2</sub> need it at cj &#8805; ci. Rather than
     * encode that per rule, every accessible label related to ci in either direction is
     * offered to the rule, and the rule's own pattern decides: {@code generateIPLRuleConclusion}
     * returns null exactly when the label constraint is not satisfied.
     *
     * <p>The conclusion is therefore computed <em>before</em> branching. A candidate label
     * that yields no conclusion corresponds to no rule instance at all, so it must not
     * split the branch (Algorithm 1 applies PB in line 8 only to supply {@code min(r)} for
     * an instance r whose conclusion is then added in line 12) and must not be recorded in
     * {@code rinstances}, which would block the instance from ever being retried.
     *
     * <p>NOTE: iterates the physical branch directly ({@code getPhysicalFormulas()}). The
     * accessible labels cj come from the Context, which already coincides with
     * Cb = "constants occurring in b" (Definitions 3.1): the constants that occur in some
     * physical formula of the branch.
     */
    private boolean tryPBAtAlternativeLabels(ClassicalProofTree current, SignedFormulaBuilder sfb,
            SignedFormula mainPremise, Rule rule, SignedFormula requiredAux,
            logic.labelledFormulas.ContextFormulaLabel ci, FormulaSign oppositeSign,
            IPLProofTree iplTree) {

        // Accessible labels of the branch comparable with ci, in either direction.
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
            Context ctx = ci.getContext();
            if (!ctx.isLowerOrEqualTo(ci, cj) && !ctx.isLowerOrEqualTo(cj, ci)) continue;
            if (!iplTree.isLabelAccessible(cj)) continue;               // label must be accessible
            labelsToTry.add(cj);
        }

        // The major premise is the same for every candidate label.
        SignedFormula mainPremiseForConclusion;
        if (mainPremise.getLabel() instanceof logic.labelledFormulas.ContextFormulaLabel) {
            mainPremiseForConclusion = mainPremise;
        } else {
            mainPremiseForConclusion = createIPLSignedFormulaWithLabel(sfb,
                    (FormulaSign) mainPremise.getSign(), mainPremise.getFormula(), ci);
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

            // Does the rule actually have an instance with the minor premise at cj? The
            // rule's pattern checks its own label constraint, so a null conclusion means
            // this label is not admissible for this rule. Nothing has been changed yet.
            SignedFormula conclusion = generateIPLRuleConclusion(rule, mainPremiseForConclusion, auxWithCj, sfb);
            if (conclusion == null) continue;

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

            // Register the rule instance in the global rinstances set (Algorithm 1, line 13).
            // Registered before adding the conclusion so the viewer's per-node snapshot
            // includes the rule that generated it.
            iplTree.registerRuleInstance(ruleKeyAlt);

            left.addLast(new SignedFormulaNode(conclusion, SignedFormulaNodeState.NOT_ANALYSED,
                    strategy.createOrigin(rule, current.getNode(mainPremise),
                            left.getNode(auxWithCj))));

            if (IPLTracer.isEnabled()) {
                tracer.logRuleApplied(rule.toString(), mainPremise.toString(),
                        auxWithCj.toString(), conclusion.toString());
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
