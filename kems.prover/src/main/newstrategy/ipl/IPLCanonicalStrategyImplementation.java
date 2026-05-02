package main.newstrategy.ipl;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import logic.formulas.CompositeFormula;
import logic.formulas.Formula;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logicalSystems.ipl.IPLConnectives;
import logicalSystems.ipl.IPLProofTree;
import logicalSystems.ipl.IPLSigns;
import main.newstrategy.ISimpleStrategy;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import logic.signedFormulas.SignedFormulaBuilder;
import main.strategy.ClassicalProofTree;
import logic.signedFormulas.SignedFormula;

/**
 * Implementation of Algorithm 1 (Canonical procedure) from the paper.
 * 
 * This follows the exact structure specified in the paper (§5, p.16):
 * 
 *   while b is neither closed nor completed do
 *     select a φ in b which is not completely analyzed in b  [line 6]
 *     if φ is major premise of 1-rule instance r ∉ rinstances then apply r
 *     else if φ is major premise of 2-rule instance r ∉ rinstances then
 *       if minor premise ∈ b → apply r
 *       else → PB on minor premise, then apply r
 *     b* ← extend(b)  [line 21]
 *   end while
 * 
 * "Completed" is defined per Definition 5.6: a branch b is completed when for
 * every physical formula in b, the required consequences exist in b*.
 * {@link #isCompletePerDef56(IPLProofTree)} implements this check exactly.
 * 
 * Formulas are selected ONLY from the physical branch b (Algorithm 1, line 6);
 * b* is used exclusively for the completeness check (line 21 and Definition 5.6).
 * No eager or lazy materialization of b* formulas into b is performed.
 */
public class IPLCanonicalStrategyImplementation {
    
    private static final IPLTracer tracer = IPLTracer.getInstance();
    
    private ISimpleStrategy strategy;
    private SignedFormulaBuilder sfb;
    private IPLOnePremiseRuleApplicator onePremiseApplicator;
    private IPLTwoPremiseRuleApplicator twoPremiseApplicator;
    private IPLPBRuleApplicator pbApplicator;

    // Cached rule lists — fetched once per execute() call so hasOnePremiseRule /
    // hasTwoPremiseRule don't traverse the rule map on every formula selection.
    private rules.structures.OnePremiseRuleList onePremiseRules;
    private rules.structures.IPLConnectiveRoleSignRuleList twoPremiseRules;
    
    public IPLCanonicalStrategyImplementation() {
    }
    
    /**
     * Executes the canonical procedure (Algorithm 1).
     *
     * @param strategy the IPL strategy
     * @param sfb      the signed formula builder
     * @return the completed proof tree
     */
    public ClassicalProofTree execute(ISimpleStrategy strategy, SignedFormulaBuilder sfb) {
        this.strategy = strategy;
        this.sfb = sfb;
        this.onePremiseApplicator = (IPLOnePremiseRuleApplicator) strategy.getRuleApplicators().get(0);
        this.twoPremiseApplicator = (IPLTwoPremiseRuleApplicator) strategy.getRuleApplicators().get(1);
        this.pbApplicator = (IPLPBRuleApplicator) strategy.getProofTransformations().get(0);

        Object op = strategy.getMethod().getRules().get("onePremiseRules");
        this.onePremiseRules = op instanceof rules.structures.OnePremiseRuleList
                ? (rules.structures.OnePremiseRuleList) op : null;
        Object tp = strategy.getMethod().getRules().get("twoPremiseRules");
        this.twoPremiseRules = tp instanceof rules.structures.IPLConnectiveRoleSignRuleList
                ? (rules.structures.IPLConnectiveRoleSignRuleList) tp : null;

        if (IPLTracer.isEnabled()) {
            tracer.reset();
            tracer.logAlgorithmStart();
        }

        // Line 1: T ← F A : c0  (already initialised by the strategy)
        ClassicalProofTree T = strategy.getProofTree();
        if (T.isClosed()) return T;

        // Lines 3-22: process each open branch until the tree closes or all branches complete
        LinkedList<IProofTree> openBranches = new LinkedList<>();
        openBranches.addLast(T);
        strategy.setOpenBranches(openBranches);

        while (!openBranches.isEmpty() && !T.isClosed()) {
            // Every branch in an IPL proof is an IPLProofTree — cast once here.
            IPLProofTree b = (IPLProofTree) openBranches.removeFirst();
            strategy.setCurrent(b);

            if (IPLTracer.isEnabled()) {
                tracer.setCurrentBranch(b.getBranchId());
                tracer.logBranchStart(b.getBranchId());
                tracer.logInfo("Estado: closed=" + b.isClosed() + ", completed=" + b.isCompleted());
            }

            processOpenBranch(b, openBranches);

            if (b.isClosed()) {
                if (!T.isClosed()) strategy.finishBranch(b);
            } else if (b.getLeft() == null && b.getRight() == null) {
                // Leaf branch not closed — it is a completed open branch (potential countermodel)
                if (IPLTracer.isEnabled()) {
                    if (!isCompletePerDef56(b)) tracer.logInfo("WARNING: branch exited loop but Definition 5.6 not fully satisfied");
                }
                b.setCompleted(true);
                T.setOpenCompletedBranch(b);
                if (IPLTracer.isEnabled()) tracer.logBranchCompleted(b.getBranchId(), false);
            }
            // else: b has children that were already enqueued inside processOpenBranch
        }

        // Lines 23-24: end while / return T
        if (IPLTracer.isEnabled()) tracer.logAlgorithmEnd(T.isClosed());
        return T;
    }

    /**
     * Line 5: inner loop — processes branch b until it closes, completes, or can no longer
     * progress.  Any child branches created by branching rules are pushed onto openBranches.
     */
    private void processOpenBranch(IPLProofTree b, LinkedList<IProofTree> openBranches) {
        Set<SignedFormula> failedFormulas = new HashSet<>();

        // extendBranch() is O(n). We only recheck closure + completeness after the branch
        // state actually changes (rule applied). Between failed iterations nothing can change.
        boolean recheckStatus = true;

        while (!b.isClosed()) {
            if (recheckStatus && checkBranchDone(b)) break;
            recheckStatus = false;

            // Line 6: select a φ in b not yet completely analyzed
            SignedFormula phi = selectUnanalyzedFormula(b, failedFormulas);

            if (phi == null) {
                // All formulas exhausted — one final PB attempt, then stop
                if (IPLTracer.isEnabled()) tracer.logInfo("No formula to analyze — trying PB as last resort");
                pbApplicator.apply(b, sfb);
                enqueueOpenChildren(b, openBranches);
                break;
            }

            if (IPLTracer.isEnabled()) tracer.logFormulaSelected(phi.toString(), "selected for processing");

            // Lines 7-20: try 1-premise then 2-premise rules for φ
            boolean applied = processFormula(b, phi, sfb);

            if (applied) {
                failedFormulas.clear();
                recheckStatus = true;  // state changed — recheck next iteration
                if (b.getLeft() != null || b.getRight() != null) {
                    // A branching rule fired — hand children to the outer loop
                    enqueueOpenChildren(b, openBranches);
                    break;
                }
            } else {
                failedFormulas.add(phi);
            }
            // Line 21: b* ← extend(b) — closure via detectIPLContradiction is automatic;
            // the checkBranchDone call at the top of the next iteration handles everything else.
        }
    }

    /**
     * Pushes any open (non-closed) children of b onto the queue.
     */
    private void enqueueOpenChildren(IPLProofTree b, LinkedList<IProofTree> openBranches) {
        IProofTree left = b.getLeft();
        IProofTree right = b.getRight();
        if (left != null) {
            IPLProofTree lBranch = (IPLProofTree) left;
            if (!lBranch.isClosed()) {
                openBranches.addLast(lBranch);
                if (IPLTracer.isEnabled()) tracer.logInfo("Queued left branch " + lBranch.getBranchId());
            }
        }
        if (right != null) {
            IPLProofTree rBranch = (IPLProofTree) right;
            if (!rBranch.isClosed()) {
                openBranches.addLast(rBranch);
                if (IPLTracer.isEnabled()) tracer.logInfo("Queued right branch " + rBranch.getBranchId());
            }
        }
    }

    /**
     * Computes b* once and uses it for both the contradiction scan (→ closure) and
     * the Definition 5.6 completeness check.  Returns true if the branch is done —
     * either because a contradiction was found (branch closed) or because every
     * formula's required consequences are already present in b*.
     */
    private boolean checkBranchDone(IPLProofTree b) {
        // Closure check: iterate physical b directly (Lemma 5.5, equivalent to b* check via ⪯ transitivity).
        if (b.checkPhysicalBForContradiction()) return true;
        // Completeness check: requires b* (Definition 5.6 conditions reference b*).
        Set<SignedFormula> bStar = b.extendBranch();
        return isCompletePerDef56(b, bStar);
    }

    /**
     * Checks whether branch b is "completed" per Definition 5.6 of the paper.
     *
     * A branch b is completed iff for every physical formula φ ∈ b the
     * required consequences (determined by φ's sign and connective) are present
     * in b* = extend(b).
     *
     * Definition 5.6 conditions (constant-label formulas only):
     *  - T(A∧B):ci  → T A:ci ∈ b* ∧ T B:ci ∈ b*
     *  - F(A∧B):ci  → F A:ci ∈ b* ∨ F B:ci ∈ b*
     *  - T(A∨B):ci  → T A:ci ∈ b* ∨ T B:ci ∈ b*
     *  - F(A∨B):ci  → F A:ci ∈ b* ∧ F B:ci ∈ b*
     *  - T(A→B):ci  → ∀ cj ≥ ci : F A:cj ∈ b* ∨ T B:cj ∈ b*   (Def 5.6, paper p.16)
     *  - F(A→B):ci  → ∃ cj ≥ ci : T A:cj ∈ b* ∧ F B:cj ∈ b*
     *  - T(¬A):ci   → ∀ cj ≥ ci : F A:cj ∈ b*
     *  - F(¬A):ci   → ∃ cj ≥ ci : T A:cj ∈ b*
     *
     * This is used as the exit condition for the inner while loop of Algorithm 1.
     * b* is computed by {@link IPLProofTree#extendBranch()} (Definition 5.3).
     */
    private boolean isCompletePerDef56(IPLProofTree branch) {
        return isCompletePerDef56(branch, branch.extendBranch());
    }

    /**
     * Checks completeness per Definition 5.6 using a pre-computed b*.
     * Called from {@link #checkBranchDone(IPLProofTree)} to share the b* already
     * computed by the contradiction check.
     */
    private boolean isCompletePerDef56(IPLProofTree branch, Set<SignedFormula> bStar) {
        // Collect only labels that appear in this branch's b* — not the global Context,
        // which is shared across branches and includes labels from siblings/cousins.
        java.util.Set<FormulaLabel> branchLabels = new java.util.LinkedHashSet<>();
        for (SignedFormula bsf : bStar) {
            if (bsf instanceof LabelledFormula) {
                branchLabels.add(((LabelledFormula) bsf).getLabel());
            }
        }

        main.proofTree.iterator.IProofTreeVeryBasicIterator it = branch.getTopDownIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (!(node instanceof SignedFormulaNode)) continue;
            SignedFormula sf = (SignedFormula) ((SignedFormulaNode) node).getContent();
            if (!(sf instanceof LabelledFormula)) continue;
            if (!(sf.getFormula() instanceof CompositeFormula)) continue;

            LabelledFormula lf = (LabelledFormula) sf;
            if (!(lf.getLabel() instanceof ContextFormulaLabel)) continue;
            ContextFormulaLabel ci = (ContextFormulaLabel) lf.getLabel();
            logic.labelledFormulas.Context ctx = ci.getContext();

            CompositeFormula comp = (CompositeFormula) sf.getFormula();
            if (comp.getImmediateSubformulas() == null || comp.getImmediateSubformulas().isEmpty()) continue;

            if (!checkDef56Condition(sf, comp, ci, ctx, bStar, branchLabels)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Checks the Definition 5.6 condition for a single physical formula.
     *
     * @return true if the formula is "completely analyzed" per Def 5.6
     */
    private boolean checkDef56Condition(
            SignedFormula sf, CompositeFormula comp,
            FormulaLabel ci, logic.labelledFormulas.Context ctx,
            java.util.Set<SignedFormula> bStar,
            java.util.Set<FormulaLabel> branchLabels) {

        List<Formula> subs = comp.getImmediateSubformulas();
        Formula A = subs.get(0);
        Formula B = subs.size() > 1 ? subs.get(1) : null;
        // Use toString() for sign comparison: FormulaSign.equals(FormulaSign) is not an override
        // of Object.equals(Object), so direct .equals() calls use object identity and fail for
        // formula instances created by rule applicators with different FormulaSign instances.
        String signStr = sf.getSign().toString();
        Object conn = comp.getConnective();
        boolean isTrue = "T".equals(signStr);
        boolean isFalse = "F".equals(signStr);

        if (isTrue && conn.equals(IPLConnectives.AND)) {
            // T(A∧B):ci → T A:ci ∈ b* ∧ T B:ci ∈ b*
            return B != null && inBStar(IPLSigns.TRUE, A, ci, bStar) && inBStar(IPLSigns.TRUE, B, ci, bStar);
        }
        if (isFalse && conn.equals(IPLConnectives.AND)) {
            // F(A∧B):ci → F A:ci ∈ b* ∨ F B:ci ∈ b*
            return B != null && (inBStar(IPLSigns.FALSE, A, ci, bStar) || inBStar(IPLSigns.FALSE, B, ci, bStar));
        }
        if (isTrue && conn.equals(IPLConnectives.OR)) {
            // T(A∨B):ci → T A:ci ∈ b* ∨ T B:ci ∈ b*
            return B != null && (inBStar(IPLSigns.TRUE, A, ci, bStar) || inBStar(IPLSigns.TRUE, B, ci, bStar));
        }
        if (isFalse && conn.equals(IPLConnectives.OR)) {
            // F(A∨B):ci → F A:ci ∈ b* ∧ F B:ci ∈ b*
            return B != null && inBStar(IPLSigns.FALSE, A, ci, bStar) && inBStar(IPLSigns.FALSE, B, ci, bStar);
        }
        if (isTrue && conn.equals(IPLConnectives.IMPLIES)) {
            // T(A→B):ci → ∀ cj ≥ ci [in branch] : F A:cj ∈ b* ∨ T B:cj ∈ b*
            // Per Definition 5.6 (paper, p.16): the implication is "discharged" for cj when
            // either the antecedent is refuted (F A:cj) or the consequent is proved (T B:cj).
            // If neither holds, the formula is NOT analyzed → loop must continue (possibly via PB).
            for (FormulaLabel cj : branchLabels) {
                if (!(cj instanceof ContextFormulaLabel)) continue;
                if (!ctx.isLowerOrEqualTo(ci, cj)) continue;
                if (!inBStar(IPLSigns.FALSE, A, cj, bStar) && !inBStar(IPLSigns.TRUE, B, cj, bStar)) {
                    return false;
                }
            }
            return true;
        }
        if (isFalse && conn.equals(IPLConnectives.IMPLIES)) {
            // F(A→B):ci → ∃ cj ≥ ci [in branch] : T A:cj ∈ b* ∧ F B:cj ∈ b*
            for (FormulaLabel cj : branchLabels) {
                if (!(cj instanceof ContextFormulaLabel)) continue;
                if (!ctx.isLowerOrEqualTo(ci, cj)) continue;
                if (inBStar(IPLSigns.TRUE, A, cj, bStar)
                        && inBStar(IPLSigns.FALSE, B, cj, bStar)) {
                    return true;
                }
            }
            return false;
        }
        if (isTrue && conn.equals(IPLConnectives.NOT)) {
            // T(¬A):ci → ∀ cj ≥ ci [in branch] : F A:cj ∈ b*
            for (FormulaLabel cj : branchLabels) {
                if (!(cj instanceof ContextFormulaLabel)) continue;
                if (!ctx.isLowerOrEqualTo(ci, cj)) continue;
                if (!inBStar(IPLSigns.FALSE, A, cj, bStar)) {
                    return false;
                }
            }
            return true;
        }
        if (isFalse && conn.equals(IPLConnectives.NOT)) {
            // F(¬A):ci → ∃ cj ≥ ci [in branch] : T A:cj ∈ b*
            for (FormulaLabel cj : branchLabels) {
                if (!(cj instanceof ContextFormulaLabel)) continue;
                if (!ctx.isLowerOrEqualTo(ci, cj)) continue;
                if (inBStar(IPLSigns.TRUE, A, cj, bStar)) {
                    return true;
                }
            }
            return false;
        }

        // Unknown connective — conservatively consider it analyzed
        return true;
    }

    /**
     * Returns true if sign:formula:label is a member of bStar.
     * Uses toString() comparison to avoid issues with LabelledFormula vs SignedFormula
     * type hierarchies and inconsistent equals() implementations.
     */
    private boolean inBStar(Object sign, Formula formula,
            FormulaLabel label, java.util.Set<SignedFormula> bStar) {
        String target = sign.toString() + " " + formula.toString() + " " + label.toString();
        for (SignedFormula sf : bStar) {
            if (sf.toString().equals(target)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Algorithm 1, line 6: "select a φ in b which is not completely analyzed in b".
     *
     * Selection is decided exclusively by Definition 5.6: a formula is a candidate
     * iff its Def. 5.6 condition is NOT yet satisfied in b*. The internal
     * NOT_ANALYSED/ANALYSED flag is no longer consulted to decide candidacy —
     * it is kept only as an optimisation signal for {@link IPLPBRuleApplicator}
     * (which uses it to detect "no work pending" before invoking PB).
     *
     * Consequences:
     * - Universal formulas (T(A→B), T(¬A)): re-selected automatically whenever a
     *   new accessible world makes Def. 5.6 fail again — same behaviour as before.
     * - Existential formulas (F(A→B), F(¬A)): pre-checked and discarded as soon
     *   as Def. 5.6 is satisfied — same behaviour as before.
     * - T∧, F∨, T∨, F∧: now also pre-checked. If their condition was already
     *   satisfied indirectly (e.g. via monotonicity or another rule) the formula
     *   is discarded without firing its rule. If it later becomes unsatisfied
     *   again (e.g. T∨ whose only disjunct witness was on a sibling branch) it
     *   is reconsidered, avoiding unnecessary PB invocations.
     *
     * Whenever a formula is discarded because Def. 5.6 already holds, we mark
     * it ANALYSED so that {@link IPLPBRuleApplicator#hasUnanalysedFormulas} can
     * recognise that no operational work remains.
     *
     * @param failedFormulas formulas that failed to apply any rule this round
     *                       (cleared whenever any rule fires, see processOpenBranch)
     */
    private SignedFormula selectUnanalyzedFormula(IPLProofTree b, Set<SignedFormula> failedFormulas) {
        SignedFormula onePremiseCandidate = null;
        SignedFormula twoPremiseCandidate = null;

        // b* and branchLabels are computed lazily on first need and reused for the
        // entire scan. extendBranch() is O(n); doing it once per selectUnanalyzedFormula
        // call keeps per-iteration cost bounded.
        Set<SignedFormula> bStar = null;
        java.util.Set<FormulaLabel> branchLabels = null;

        main.proofTree.iterator.IProofTreeVeryBasicIterator it = b.getTopDownIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (!(node instanceof SignedFormulaNode)) continue;

            SignedFormulaNode sfNode = (SignedFormulaNode) node;
            SignedFormula sf = (SignedFormula) sfNode.getContent();

            if (failedFormulas.contains(sf)) continue;
            if (isTopOrBottom(sf)) continue;
            if (!(sf.getFormula() instanceof CompositeFormula)) continue;
            if (!(sf instanceof LabelledFormula)) continue;
            LabelledFormula lf = (LabelledFormula) sf;
            if (!(lf.getLabel() instanceof ContextFormulaLabel)) continue;

            if (bStar == null) {
                bStar = b.extendBranch();
                branchLabels = collectBranchLabels(bStar);
            }

            CompositeFormula comp = (CompositeFormula) sf.getFormula();
            ContextFormulaLabel ci = (ContextFormulaLabel) lf.getLabel();
            logic.labelledFormulas.Context ctx = ci.getContext();

            if (checkDef56Condition(sf, comp, ci, ctx, bStar, branchLabels)) {
                // Def. 5.6 already satisfied — formula is "completely analyzed".
                // Mark ANALYSED so PB last-resort can recognise no work remains.
                if (sfNode.getState() == SignedFormulaNodeState.NOT_ANALYSED) {
                    sfNode.setState(SignedFormulaNodeState.ANALYSED);
                    if (IPLTracer.isEnabled())
                        tracer.logInfo("Def.5.6 already satisfied, marking ANALYSED: " + sf);
                }
                continue;
            }

            // Def. 5.6 fails → formula is not completely analyzed → candidate.
            if (onePremiseCandidate == null && hasOnePremiseRule(sf)) {
                onePremiseCandidate = sf;
                if (IPLTracer.isEnabled()) tracer.logInfo("1-premise candidate: " + sf);
            }
            if (twoPremiseCandidate == null && hasTwoPremiseRule(sf)) {
                twoPremiseCandidate = sf;
                if (IPLTracer.isEnabled()) tracer.logInfo("2-premise candidate: " + sf);
            }
            if (onePremiseCandidate != null && twoPremiseCandidate != null) break;
        }

        if (onePremiseCandidate != null) {
            if (IPLTracer.isEnabled()) tracer.logFormulaSelected(onePremiseCandidate.toString(), "1-premise priority");
            return onePremiseCandidate;
        }
        return twoPremiseCandidate;
    }

    /** Collects the set of labels that appear in bStar (for Def. 5.6 checks). */
    private java.util.Set<FormulaLabel> collectBranchLabels(Set<SignedFormula> bStar) {
        java.util.Set<FormulaLabel> labels = new java.util.LinkedHashSet<>();
        for (SignedFormula bsf : bStar) {
            if (bsf instanceof LabelledFormula) {
                labels.add(((LabelledFormula) bsf).getLabel());
            }
        }
        return labels;
    }

    /**
     * Returns true if sf has an entry in the 1-premise rule list.
     * Precondition: sf.getFormula() is a CompositeFormula (guaranteed by the caller).
     */
    private boolean hasOnePremiseRule(SignedFormula sf) {
        if (onePremiseRules == null) return false;
        CompositeFormula comp = (CompositeFormula) sf.getFormula();
        rules.Rule rule = onePremiseRules.get(sf.getSign(), comp.getConnective());
        return rule != null && rule != rules.NullRule.INSTANCE;
    }

    /**
     * Returns true if sf has an entry in the 2-premise rule list.
     * Precondition: sf.getFormula() is a CompositeFormula (guaranteed by the caller).
     */
    private boolean hasTwoPremiseRule(SignedFormula sf) {
        if (twoPremiseRules == null) return false;
        CompositeFormula comp = (CompositeFormula) sf.getFormula();
        List<rules.Rule> left  = twoPremiseRules.getMany(comp.getConnective(), rules.KERuleRole.LEFT,  sf.getSign());
        List<rules.Rule> right = twoPremiseRules.getMany(comp.getConnective(), rules.KERuleRole.RIGHT, sf.getSign());
        return (left != null && !left.isEmpty()) || (right != null && !right.isEmpty());
    }

    /**
     * Lines 7-20: Try to apply a rule to φ. Returns true if any rule fired.
     *
     * All formulas are marked ANALYSED when no rule can fire. Universal formulas
     * (T(A→B), T(¬A)) are re-selected later by selectUnanalyzedFormula whenever
     * Definition 5.6 is not yet satisfied — no permanent NOT_ANALYSED needed.
     */
    private boolean processFormula(IPLProofTree b, SignedFormula phi, SignedFormulaBuilder sfb) {
        if (IPLTracer.isEnabled()) tracer.logInfo("Trying 1-premise rules for: " + phi);
        if (onePremiseApplicator.applySingle(b, sfb, phi)) {
            if (IPLTracer.isEnabled()) tracer.logInfo("1-premise rule applied");
            return true;
        }

        if (IPLTracer.isEnabled()) tracer.logInfo("Trying 2-premise rules for: " + phi);
        if (twoPremiseApplicator.applySingle(b, sfb, phi)) {
            if (IPLTracer.isEnabled()) tracer.logInfo("2-premise rule applied");
            return true;
        }

        // Mark ANALYSED unconditionally. Universal formulas (T(A→B), T(¬A)) will be
        // re-selected by selectUnanalyzedFormula whenever Def. 5.6 is unsatisfied for
        // new accessible worlds — no need to keep them NOT_ANALYSED permanently.
        if (IPLTracer.isEnabled()) tracer.logInfo("No rule for " + phi + " — marking ANALYSED");
        markAsAnalyzed(b, phi);
        return false;
    }
    
    /**
     * Marks a formula as analyzed in the branch.
     */
    private void markAsAnalyzed(IPLProofTree b, SignedFormula sf) {
        SignedFormulaNode node = b.getNode(sf);
        if (node != null) {
            node.setState(SignedFormulaNodeState.ANALYSED);
        }
    }

    /**
     * Checks if a formula is T⊤ or F⊥.
     */
    private boolean isTopOrBottom(SignedFormula sf) {
        String formulaStr = sf.getFormula().toString();
        return formulaStr.equals("TOP") || formulaStr.equals("BOTTOM");
    }
    
}
