package main.newstrategy.ipl;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import logic.formulas.CompositeFormula;
import logic.formulas.Formula;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logicalSystems.ipl.IPLConnectives;
import logicalSystems.ipl.IPLProofTree;
import main.newstrategy.ISimpleStrategy;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import logic.signedFormulas.SignedFormulaBuilder;
import main.strategy.ClassicalProofTree;
import logic.signedFormulas.SignedFormula;

/**
 * Implementation of Algorithm 1 (Canonical procedure) from the paper (KEIPL).
 *
 * This follows the exact structure specified in the paper (§5):
 *
 *   while b is neither closed nor completed do
 *     select a φ in b which is not completely analyzed in b  [line 6]
 *     select a rule r such that φ = maj(r) and r ∉ rinstances  [line 7]
 *     if r is a 2-rule and min(r) ∉ b then PB on min(r), then apply r  [lines 8-11]
 *     b ← (b expanded with conc(r))  [line 12]
 *     rinstances ← rinstances ∪ {r}  [line 13]
 *   end while
 *
 * Note there is no inner "while φ is not completely analyzed" loop repeating rule
 * selection for the same φ: each outer iteration selects one φ, fires at most one
 * rule instance, and loops back to selection.
 *
 * "Completed" is defined per Definition 5.3: a branch b is completed iff it is
 * open and every ls-formula φ ∈ b is "completely analyzed" (c.a.) in b — a notion
 * defined *recursively* on the structure of φ's formula, bottoming out at
 * propositional variables where ⪯b-monotonicity is checked directly against the
 * physical branch. {@link #isCompletelyAnalyzed} implements this recursion exactly;
 * {@link #isBranchCompletePerDef53(IPLProofTree)} implements the branch-level check.
 *
 * Composite subformulas are never tested for literal, physical presence in b, nor
 * in any materialized set: they are decomposed recursively all the way down to
 * atoms, so a formula can be recognized as analyzed from atomic witnesses alone,
 * without ever materializing the intermediate composite formulas — this is what
 * collapses e.g. the Scott axiom refutation to a single branch.
 *
 * Formulas are selected ONLY from the physical branch b (Algorithm 1, line 6); no
 * eager or lazy materialization of derived formulas into b is performed.
 *
 * <p><b>On the inherited node status flag.</b> {@code SignedFormulaNode} carries a
 * NOT_ANALYSED/ANALYSED/FULFILLED status used by the classical KE strategies this
 * infrastructure is shared with. The IPL strategy deliberately does not participate
 * in it: it never writes ANALYSED and never reads the status to make a decision.
 * Two invariants replace it, and together they are what make deferring PB safe:
 *
 * <ul>
 *   <li><i>Candidacy</i> is decided solely by {@link #isCompletelyAnalyzed}, i.e. by
 *       Definition 5.3 re-evaluated against the branch on every scan. Nothing is
 *       cached on the node, so a formula that stops being completely analyzed —
 *       which is exactly what happens to T(A→B) and T(¬A) when a new constant
 *       appears — becomes a candidate again on its own.</li>
 *   <li><i>Termination of the branch</i> is decided solely by {@link #checkBranchDone},
 *       i.e. closure or {@link #isBranchCompletePerDef53}: both direct re-evaluations
 *       of the paper's own predicates.</li>
 * </ul>
 *
 * Re-selecting a formula on which no rule could fire is prevented, for the current
 * round only, by the {@code failedFormulas} set in {@link #processOpenBranch} — which
 * is cleared as soon as any rule fires, so no formula is ever permanently excluded on
 * the strength of past bookkeeping. Deferring PB to the point where selection can no
 * longer make progress therefore changes only <i>when</i> a branching step happens,
 * never <i>which</i> formulas the procedure still considers analyzable.
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

        // IPLRuleStructures always registers an IPLOnePremiseRuleList (which extends
        // OnePremiseRuleList) under "onePremiseRules" and an
        // IPLConnectiveRoleSignRuleList under "twoPremiseRules" — the only rule
        // structure ever built for the IPL strategy.
        this.onePremiseRules = (rules.structures.OnePremiseRuleList)
                strategy.getMethod().getRules().get("onePremiseRules");
        this.twoPremiseRules = (rules.structures.IPLConnectiveRoleSignRuleList)
                strategy.getMethod().getRules().get("twoPremiseRules");

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
                tracer.logInfo("State: closed=" + b.isClosed() + ", completed=" + b.isCompleted());
            }

            processOpenBranch(b, openBranches);

            if (b.isClosed()) {
                if (!T.isClosed()) strategy.finishBranch(b);
            } else if (b.getLeft() == null && b.getRight() == null) {
                // Leaf branch not closed — it is a completed open branch (potential countermodel)
                if (IPLTracer.isEnabled()) {
                    if (!isBranchCompletePerDef53(b)) tracer.logInfo("WARNING: branch exited loop but Definition 5.3 not fully satisfied");
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

        // checkBranchDone() rescans b physically. We only recheck closure + completeness
        // after the branch state actually changes (rule applied). Between failed
        // iterations nothing can change.
        boolean recheckStatus = true;

        while (!b.isClosed()) {
            if (recheckStatus && checkBranchDone(b)) break;
            recheckStatus = false;

            // Line 6: select a φ in b not yet completely analyzed
            SignedFormula phi = selectUnanalyzedFormula(b, failedFormulas);

            if (phi == null) {
                // All formulas exhausted — one final PB attempt, then stop
                if (IPLTracer.isEnabled()) tracer.logInfo("No formula to analyze \u2014 trying PB as last resort");
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
            // Closure via detectIPLContradiction is automatic; the checkBranchDone
            // call at the top of the next iteration handles everything else.
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
     * Returns true if the branch is done — either because a contradiction was
     * found (branch closed) or because it is completed per Definition 5.3
     * : every ls-formula in it is completely analyzed.
     */
    private boolean checkBranchDone(IPLProofTree b) {
        // Closure check: iterate physical b directly — the closure rule (Table 2) is
        // stated directly on physical labels, no extended set is needed.
        if (b.checkPhysicalBForContradiction()) return true;
        return isBranchCompletePerDef53(b);
    }

    /**
     * Checks whether branch b is "completed" per Definition 5.3 of the paper
     * : b is completed iff every ls-formula φ ∈ b is completely
     * analyzed in b (per {@link #isCompletelyAnalyzed}). Only composite
     * ls-formulas are checked — propositional-variable ls-formulas are always
     * completely analyzed in b by reflexivity of ⪯b (see base case below).
     */
    private boolean isBranchCompletePerDef53(IPLProofTree branch) {
        List<SignedFormula> physicalB = branch.getPhysicalFormulas();
        Set<FormulaLabel> constantLabels = collectConstantLabels(physicalB);
        Context ctx = firstContext(constantLabels);
        if (ctx == null) return true; // no constant labels yet — nothing to check

        Map<String, Boolean> memo = new HashMap<>();

        main.proofTree.iterator.IProofTreeVeryBasicIterator it = branch.getTopDownIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (!(node instanceof SignedFormulaNode)) continue;
            SignedFormula sf = (SignedFormula) ((SignedFormulaNode) node).getContent();
            if (!(sf instanceof LabelledFormula)) continue;
            if (!(sf.getFormula() instanceof CompositeFormula)) continue;

            LabelledFormula lf = (LabelledFormula) sf;
            if (!(lf.getLabel() instanceof ContextFormulaLabel)) continue;

            boolean isTrue = "T".equals(sf.getSign().toString());
            if (!isCompletelyAnalyzed(isTrue, sf.getFormula(), lf.getLabel(), ctx, physicalB, constantLabels, memo)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Definition 5.3 of the paper: recursively checks whether the
     * ls-formula "sign formula : label" is completely analyzed (c.a.) in branch
     * b. Restricted to the constants-only fragment (this implementation never
     * produces variable-labeled ls-formulas — see {@code Table 2} in the paper).
     *
     * Base case (propositional variable p):
     *  - T p:label is c.a. in b iff ∃ T p:ci ∈ b with ci ⪯b label;
     *  - F p:label is c.a. in b iff ∃ F p:cj ∈ b with label ⪯b cj.
     * (Both hold reflexively when "T/F p:label" is itself physically in b.)
     *
     * Recursive cases (constants-only fragment of Def. 5.3):
     *  - T(A∧B):ci  c.a. iff A:ci c.a.(T) and B:ci c.a.(T)
     *  - F(A∧B):ci  c.a. iff A:ci c.a.(F) or  B:ci c.a.(F)
     *  - T(A∨B):ci  c.a. iff A:ci c.a.(T) or  B:ci c.a.(T)
     *  - F(A∨B):ci  c.a. iff A:ci c.a.(F) and B:ci c.a.(F)
     *  - T(A→B):ci  c.a. iff ∀cj∈Cb, ci⪯cj: A:cj c.a.(F) or B:cj c.a.(T)
     *  - F(A→B):ci  c.a. iff ∃cj∈Cb, ci⪯cj: A:cj c.a.(T) and B:cj c.a.(F)
     *  - T(¬A):ci   c.a. iff ∀cj∈Cb, ci⪯cj: A:cj c.a.(F)
     *  - F(¬A):ci   c.a. iff ∃cj∈Cb, ci⪯cj: A:cj c.a.(T)
     *
     * Composite subformulas are NOT tested for literal, physical presence in b
     * (nor in any materialized set): they are decomposed recursively until an atom
     * is reached. This is why, e.g., the Scott axiom refutation needs a single
     * branch instead of several: outer conditions can be discharged directly from
     * atomic witnesses, without ever having to physically re-derive the
     * intermediate composite ls-formulas at every accessible label.
     *
     * Well-founded: A and B are always strict subformulas of the formula being
     * checked (lower degree), so the recursion always terminates; results are
     * memoized per (sign, formula, label) for the scan that is calling this.
     */
    private boolean isCompletelyAnalyzed(boolean isTrue, Formula formula, FormulaLabel label,
            Context ctx, List<SignedFormula> physicalB, Set<FormulaLabel> constantLabels,
            Map<String, Boolean> memo) {

        String key = (isTrue ? "T|" : "F|") + formula + "|" + label;
        Boolean cached = memo.get(key);
        if (cached != null) return cached;

        boolean result;
        if (formula instanceof CompositeFormula && !((CompositeFormula) formula).getImmediateSubformulas().isEmpty()) {
            CompositeFormula comp = (CompositeFormula) formula;
            List<Formula> subs = comp.getImmediateSubformulas();
            Formula A = subs.get(0);
            Formula B = subs.size() > 1 ? subs.get(1) : null;
            Object conn = comp.getConnective();

            if (isTrue && conn.equals(IPLConnectives.AND)) {
                result = B != null
                        && isCompletelyAnalyzed(true, A, label, ctx, physicalB, constantLabels, memo)
                        && isCompletelyAnalyzed(true, B, label, ctx, physicalB, constantLabels, memo);
            } else if (!isTrue && conn.equals(IPLConnectives.AND)) {
                result = B != null
                        && (isCompletelyAnalyzed(false, A, label, ctx, physicalB, constantLabels, memo)
                            || isCompletelyAnalyzed(false, B, label, ctx, physicalB, constantLabels, memo));
            } else if (isTrue && conn.equals(IPLConnectives.OR)) {
                result = B != null
                        && (isCompletelyAnalyzed(true, A, label, ctx, physicalB, constantLabels, memo)
                            || isCompletelyAnalyzed(true, B, label, ctx, physicalB, constantLabels, memo));
            } else if (!isTrue && conn.equals(IPLConnectives.OR)) {
                result = B != null
                        && isCompletelyAnalyzed(false, A, label, ctx, physicalB, constantLabels, memo)
                        && isCompletelyAnalyzed(false, B, label, ctx, physicalB, constantLabels, memo);
            } else if (isTrue && conn.equals(IPLConnectives.IMPLIES)) {
                // ∀ cj ∈ Cb, label ⪯ cj : F A:cj c.a. or T B:cj c.a.
                result = true;
                for (FormulaLabel cj : constantLabels) {
                    if (!ctx.isLowerOrEqualTo(label, cj)) continue;
                    if (!isCompletelyAnalyzed(false, A, cj, ctx, physicalB, constantLabels, memo)
                            && !isCompletelyAnalyzed(true, B, cj, ctx, physicalB, constantLabels, memo)) {
                        result = false;
                        break;
                    }
                }
            } else if (!isTrue && conn.equals(IPLConnectives.IMPLIES)) {
                // ∃ cj ∈ Cb, label ⪯ cj : T A:cj c.a. and F B:cj c.a.
                result = false;
                for (FormulaLabel cj : constantLabels) {
                    if (!ctx.isLowerOrEqualTo(label, cj)) continue;
                    if (isCompletelyAnalyzed(true, A, cj, ctx, physicalB, constantLabels, memo)
                            && isCompletelyAnalyzed(false, B, cj, ctx, physicalB, constantLabels, memo)) {
                        result = true;
                        break;
                    }
                }
            } else if (isTrue && conn.equals(IPLConnectives.NOT)) {
                // ∀ cj ∈ Cb, label ⪯ cj : F A:cj c.a.
                result = true;
                for (FormulaLabel cj : constantLabels) {
                    if (!ctx.isLowerOrEqualTo(label, cj)) continue;
                    if (!isCompletelyAnalyzed(false, A, cj, ctx, physicalB, constantLabels, memo)) {
                        result = false;
                        break;
                    }
                }
            } else if (!isTrue && conn.equals(IPLConnectives.NOT)) {
                // ∃ cj ∈ Cb, label ⪯ cj : T A:cj c.a.
                result = false;
                for (FormulaLabel cj : constantLabels) {
                    if (!ctx.isLowerOrEqualTo(label, cj)) continue;
                    if (isCompletelyAnalyzed(true, A, cj, ctx, physicalB, constantLabels, memo)) {
                        result = true;
                        break;
                    }
                }
            } else {
                // Unknown connective — conservatively consider it analyzed
                result = true;
            }
        } else if (formula instanceof CompositeFormula) {
            // Zeroary composite (TOP/BOTTOM): proof-tree scaffolding outside the
            // object language, never a genuine subformula — trivially analyzed.
            result = true;
        } else {
            // Base case: propositional variable.
            result = existsMonotoneWitness(isTrue, formula, label, ctx, physicalB);
        }

        memo.put(key, result);
        return result;
    }

    /**
     * Base case of Definition 5.3: for a propositional variable p,
     *  - T p:label is c.a. in b iff there is T p:ci ∈ b with ci ⪯b label;
     *  - F p:label is c.a. in b iff there is F p:cj ∈ b with label ⪯b cj.
     */
    private boolean existsMonotoneWitness(boolean isTrue, Formula p, FormulaLabel label,
            Context ctx, List<SignedFormula> physicalB) {
        for (SignedFormula sf : physicalB) {
            if (!(sf instanceof LabelledFormula)) continue;
            boolean sfIsTrue = "T".equals(sf.getSign().toString());
            if (sfIsTrue != isTrue) continue;
            if (!sf.getFormula().equals(p)) continue;
            FormulaLabel other = ((LabelledFormula) sf).getLabel();
            if (other == null) continue;
            boolean related = isTrue
                    ? ctx.isLowerOrEqualTo(other, label)   // ci ⪯ label
                    : ctx.isLowerOrEqualTo(label, other);  // label ⪯ cj
            if (related) return true;
        }
        return false;
    }

    /** Collects the set of constant (ContextFormulaLabel) labels appearing in physicalB. */
    private Set<FormulaLabel> collectConstantLabels(List<SignedFormula> physicalB) {
        Set<FormulaLabel> labels = new java.util.LinkedHashSet<>();
        for (SignedFormula sf : physicalB) {
            if (sf instanceof LabelledFormula) {
                FormulaLabel l = ((LabelledFormula) sf).getLabel();
                if (l instanceof ContextFormulaLabel) labels.add(l);
            }
        }
        return labels;
    }

    /** Returns the shared {@link Context} of any constant label in the set, or null if empty. */
    private Context firstContext(Set<FormulaLabel> constantLabels) {
        for (FormulaLabel l : constantLabels) {
            if (l instanceof ContextFormulaLabel) return ((ContextFormulaLabel) l).getContext();
        }
        return null;
    }

    /**
     * Algorithm 1, line 6: "select a φ in b which is not completely analyzed in b".
     *
     * Candidacy is decided exclusively by Definition 5.3: a formula is a candidate
     * iff it is NOT completely analyzed (per {@link #isCompletelyAnalyzed}), which
     * is re-evaluated against the current branch on every scan. The node-level
     * NOT_ANALYSED/ANALYSED status inherited from the classical KE infrastructure
     * plays no part in this decision, and the IPL strategy never writes it (see the
     * class comment).
     *
     * Consequences:
     * - Universal formulas (T(A→B), T(¬A)): re-selected automatically whenever a
     *   new accessible world makes Def. 5.3 fail again.
     * - Existential formulas (F(A→B), F(¬A)): discarded as soon as Def. 5.3 holds.
     * - T∧, F∨, T∨, F∧: likewise. Because Def. 5.3 recurses through subformulas
     *   instead of requiring their literal physical presence, many of these are
     *   satisfied "for free" from atomic witnesses and their rules never need to
     *   fire — this is the source of the reduced branching.
     *
     * Re-selection of a formula on which no rule could fire is prevented by
     * {@code failedFormulas} (cleared whenever any rule fires), not by any
     * persistent per-node status.
     *
     * @param failedFormulas formulas that failed to apply any rule this round
     *                       (cleared whenever any rule fires, see processOpenBranch)
     */
    private SignedFormula selectUnanalyzedFormula(IPLProofTree b, Set<SignedFormula> failedFormulas) {
        SignedFormula onePremiseCandidate = null;
        SignedFormula twoPremiseCandidate = null;

        // physicalB/constantLabels/memo are computed lazily on first need and reused
        // for the entire scan. Building them is O(n); doing it once per
        // selectUnanalyzedFormula call keeps per-iteration cost bounded.
        List<SignedFormula> physicalB = null;
        Set<FormulaLabel> constantLabels = null;
        Context ctx = null;
        Map<String, Boolean> memo = null;

        main.proofTree.iterator.IProofTreeVeryBasicIterator it = b.getTopDownIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (!(node instanceof SignedFormulaNode)) continue;

            SignedFormulaNode sfNode = (SignedFormulaNode) node;
            SignedFormula sf = (SignedFormula) sfNode.getContent();

            if (failedFormulas.contains(sf)) continue;
            if (!(sf.getFormula() instanceof CompositeFormula)) continue;
            if (!(sf instanceof LabelledFormula)) continue;
            LabelledFormula lf = (LabelledFormula) sf;
            if (!(lf.getLabel() instanceof ContextFormulaLabel)) continue;

            if (physicalB == null) {
                physicalB = b.getPhysicalFormulas();
                constantLabels = collectConstantLabels(physicalB);
                ctx = firstContext(constantLabels);
                memo = new HashMap<>();
            }
            if (ctx == null) continue; // no constant labels yet — nothing to check

            boolean isTrue = "T".equals(sf.getSign().toString());

            if (isCompletelyAnalyzed(isTrue, sf.getFormula(), lf.getLabel(), ctx, physicalB, constantLabels, memo)) {
                // Def. 5.3 already satisfied — not a candidate for this scan. Nothing is
                // recorded on the node: the predicate is re-evaluated from the branch on
                // every scan, so it can correctly fail again once a new constant appears.
                if (IPLTracer.isEnabled())
                    tracer.logInfo("Def.5.3 already satisfied, skipping: " + sf);
                continue;
            }

            // Def. 5.3 fails → formula is not completely analyzed → candidate.
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
     * When no rule fires, the caller records φ in {@code failedFormulas} for the
     * current round; nothing is written to the node. Universal formulas
     * (T(A→B), T(¬A)) are therefore re-selected by selectUnanalyzedFormula as soon
     * as a new constant makes Definition 5.3 fail for them again.
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

        if (IPLTracer.isEnabled()) tracer.logInfo("No rule for " + phi);
        return false;
    }

}
