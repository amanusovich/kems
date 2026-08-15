package logicalSystems.ipl;

import java.util.HashSet;
import java.util.Set;
import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicInteger;

import logic.formulas.Formula;
import logic.signedFormulas.SignedFormula;
import logic.labelledFormulas.LabelledFormula;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.Context;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.proofTree.iterator.IProofTreeBasicIterator;
import main.proofTree.iterator.IProofTreeVeryBasicIterator;
import main.proofTree.origin.IOrigin;
import main.strategy.memorySaver.OptimizedClassicalProofTree;
import main.newstrategy.ipl.IPLTracer;

/**
 * ProofTree specific to IPL, implementing:
 * 1. Correct closure rule: T A: ci, F A: cj, ci <= cj -> x
 * 2. Kripke monotonicity checked on demand, with no physical propagation
 *    of formulas (see Definition 5.3 and IPLCanonicalStrategyImplementation)
 * 3. Rule instance registration (rinstances) to prevent loops
 * 4. Per-branch label isolation: each branch has its own label space
 *
 * Based on the paper: "Free-variable KE tableaux for IPL", Algorithm 1.
 *
 * DESIGN OF rinstances (operational rules):
 *   A PER-BRANCH set, searched through ancestors. Each branch has its own
 *   local set; wasRuleInstanceApplied walks the ancestor chain. This
 *   guarantees that, within a single proof path (branch -> ancestors), an
 *   instance is not applied twice (loop prevention), while branches in
 *   different subtrees can apply the same instance independently
 *   (completeness). This matches the correct meaning of "rinstances" in
 *   Algorithm 1 of the paper: global to the current path, not to the whole
 *   tree.
 */
public class IPLProofTree extends OptimizedClassicalProofTree {

    private static final IPLTracer tracer = IPLTracer.getInstance();

    /**
     * Local set of operational rule instances registered on THIS branch.
     * Each branch has its own copy. wasRuleInstanceApplied() walks the
     * ancestor chain to determine whether the instance was applied along
     * the current path.
     * Format: "rule:premise1:premise2:..." (toString of the ls-formulas with labels).
     */
    private Set<String> localRinstances;

    /**
     * Branch ID: unique identifier of this branch.
     * The main trunk has ID "root".
     * Branches created by branching (PB) get unique IDs.
     * Used for label tracking (isLabelAccessible), pbRinstances and the GUI.
     */
    private String branchId;

    /**
     * Shared map associating each label (by its toString()) with its branchId.
     * Used to determine which labels are accessible from each branch.
     */
    private Map<String, String> sharedLabelBranchMap;

    /**
     * Static counter used to generate unique branch IDs.
     */
    private static AtomicInteger branchIdCounter = new AtomicInteger(0);

    /**
     * Snapshot of the path-level rinstance count at the time each
     * {@link SignedFormulaNode} was added to this branch. Used by the GUI
     * / HTML viewer to show the rinstances panel filtered to the temporal
     * state of the selected node (i.e. only rinstances registered up to
     * and including the rule application that created that node).
     */
    private final Map<SignedFormulaNode, Integer> rinstancesAtNodeCreation = new java.util.IdentityHashMap<>();

    public IPLProofTree(SignedFormulaNode aNode) {
        super(aNode);
        this.branchId = "root";
        this.sharedLabelBranchMap = new HashMap<>();
        // LinkedHashSet preserves insertion order; useful for GUI / HTML inspection
        // where rinstances are displayed in the order they were registered.
        this.localRinstances = new java.util.LinkedHashSet<>();
        registerLabelOf(aNode);
        recordRinstancesSnapshot(aNode);
    }

    /**
     * Constructor for child branches: they share sharedLabelBranchMap but each
     * one gets its own empty localRinstances set (looked up via ancestors).
     */
    private IPLProofTree(SignedFormulaNode aNode,
                         Map<String, String> sharedLabelBranchMap,
                         String branchId) {
        super(aNode);
        this.sharedLabelBranchMap = (sharedLabelBranchMap != null) ? sharedLabelBranchMap : new HashMap<>();
        this.localRinstances = new java.util.LinkedHashSet<>();
        this.branchId = branchId;
        registerLabelOf(aNode);
        recordRinstancesSnapshot(aNode);
    }

    /**
     * Registers the label of a node that enters this branch through a constructor rather
     * than through {@code addLast}: the root ls-formula, and the ls-formula PB puts at the
     * head of each child branch. Without this, the first constant of the derivation stays
     * unowned until some later {@code addLast} claims it — and if that happens in a PB
     * child, the constant is recorded as belonging to that child, which makes it look
     * inaccessible from its sibling and silently removes every ls-formula labelled with it
     * from that sibling's PB candidates. Registration keeps the first owner, so a constant
     * an ancestor already introduced is unaffected by being repeated here.
     */
    private void registerLabelOf(INode aNode) {
        if (aNode instanceof SignedFormulaNode) {
            Object content = ((SignedFormulaNode) aNode).getContent();
            if (content instanceof LabelledFormula) {
                registerLabel(((LabelledFormula) content).getLabel());
            }
        }
    }

    /**
     * Cross-scan cache of the Definition 5.3 predicate for this branch, holding only the
     * keys that evaluated to TRUE.
     *
     * <p>Sound because the predicate is monotone in the branch's formulas as long as Cb
     * does not grow. Every existential clause (T p : cj, F p : ci, F A->B : ci, F ~A : ci)
     * can only go from false to true as formulas are added, and the conjunctive and
     * disjunctive clauses inherit that. The only clauses that can go from true to false
     * are the two that quantify over Cb -- T A->B : ci and T ~A : ci -- and they can only
     * do so when a NEW constant appears. The ordering between constants that already exist
     * never changes either: addRelation is reached only from the getNewFormulaLabel*
     * methods, which always relate a freshly minted label. So a TRUE stays TRUE until the
     * next constant is minted, which is what {@link #def53Watermark} detects.
     *
     * <p>FALSE results are deliberately not cached: adding a formula can turn them true.
     *
     * <p>Per branch, not shared: a sibling branch has different formulas, so its TRUEs do
     * not transfer. It is not inherited from the parent either, which is only a missed
     * optimisation, never a source of wrong answers.
     */
    private final java.util.Map<String, Boolean> def53TrueCache = new java.util.HashMap<>();
    private int def53Watermark = -1;

    /**
     * Returns this branch's Definition 5.3 TRUE-cache, cleared first if a constant has been
     * minted since it was last used. The label count of the shared Context is a
     * conservative witness: it only grows, and it grows exactly when some branch mints a
     * constant, so this may clear more often than strictly needed but never less.
     */
    public java.util.Map<String, Boolean> getDef53TrueCache(Context ctx) {
        int now = ctx.getLabels().size();
        if (now != def53Watermark) {
            def53TrueCache.clear();
            def53Watermark = now;
        }
        return def53TrueCache;
    }

    private void recordRinstancesSnapshot(SignedFormulaNode node) {
        // We snapshot the path-level count (ancestors + local) because the GUI
        // displays the full chain in rinstances; the count tells the viewer
        // how many of those entries already existed at the time the node was
        // added.
        rinstancesAtNodeCreation.put(node, currentPathRinstancesSize());
    }

    private int currentPathRinstancesSize() {
        int n = 0;
        IPLProofTree current = this;
        while (current != null) {
            n += current.localRinstances.size();
            IProofTree parent = current.getParent();
            current = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        }
        return n;
    }

    /**
     * Returns the path-level rinstance count captured at the moment {@code node}
     * was added to this branch, or {@code -1} if the node has no recorded
     * snapshot (e.g. legacy proof trees serialised before this field existed).
     */
    public int getRinstancesAtCreation(SignedFormulaNode node) {
        Integer v = rinstancesAtNodeCreation.get(node);
        return v != null ? v : -1;
    }

    @Override
    protected IProofTree makeInstance(INode aNode) {
        String newBranchId = "branch_" + branchIdCounter.incrementAndGet();
        return new IPLProofTree((SignedFormulaNode) aNode,
                                sharedLabelBranchMap, newBranchId);
    }

    /**
     * Hook invoked by {@link main.proofTree.ProofTree#addLeft(INode)} /
     * {@link main.proofTree.ProofTree#addRight(INode)} after the new child
     * branch has been linked to its parent.
     *
     * The child's constructor runs <em>before</em> {@code setReferences} sets
     * the parent pointer, so {@link #recordRinstancesSnapshot(SignedFormulaNode)}
     * called from the constructor sees an empty ancestor chain and records
     * a snapshot of 0. Here we re-record the snapshot now that the parent
     * linkage is in place, giving the correct path-level rinstance count for
     * the child's root node.
     */
    @Override
    protected void setOtherStructures(IProofTree pt, INode aNode) {
        super.setOtherStructures(pt, aNode);
        // pt is always an IPLProofTree (makeInstance() only ever constructs one) and
        // aNode is always a SignedFormulaNode (makeInstance() already casts it to one
        // building pt, so a mismatch would have thrown before reaching this point).
        ((IPLProofTree) pt).recordRinstancesSnapshot((SignedFormulaNode) aNode);
    }

    /**
     * Checks whether an operational rule instance was already applied along the
     * current proof path (this branch or any ancestor).
     * Implements "r not-in rinstances" from Algorithm 1 (lines 7 and 10).
     *
     * @param ruleInstance the rule instance (format: "rule:premise1:premise2")
     */
    public boolean wasRuleInstanceApplied(String ruleInstance) {
        // Search this branch and every ancestor
        IPLProofTree current = this;
        while (current != null) {
            if (current.localRinstances.contains(ruleInstance)) {
                return true;
            }
            IProofTree parent = current.getParent();
            current = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        }
        return false;
    }

    /**
     * Registers an operational rule instance in this branch's LOCAL set.
     * Implements "rinstances <- rinstances union {r}" from Algorithm 1 (lines 9, 13, 18).
     *
     * @param ruleInstance the rule instance (format: "rule:premise1:premise2")
     */
    public void registerRuleInstance(String ruleInstance) {
        localRinstances.add(ruleInstance);
        if (IPLTracer.isEnabled()) {
            tracer.logRinstanceRegistered(ruleInstance);
        }
    }

    /**
     * No-op: IPL does not use the _PBCandidates list inherited from ClassicalProofTree.
     * IPLPBRuleApplicator builds its own fresh PB candidate list with
     * findAllCompositeFormulas() every time it needs one, iterating directly over
     * the tree's nodes. Keeping the inherited list in sync would be unnecessary
     * work, and attempting to remove universal formulas that were already removed
     * (re-processed by Def. 5.3) would produce spurious DEBUG messages.
     */
    @Override
    public void removeFromPBCandidates(SignedFormula sf) { }

    /**
     * Returns this branch's ID (for label tracking and the GUI).
     */
    public String getBranchId() {
        return branchId;
    }

    /**
     * Returns an unmodifiable view of rule instances registered in this branch only.
     * Preserves insertion order (LinkedHashSet). For the full path use
     * {@link #getAllRinstances()}.
     */
    public Set<String> getLocalRinstances() {
        return java.util.Collections.unmodifiableSet(localRinstances);
    }

    /**
     * Returns all rule instances along the current path (root -> ... -> this branch)
     * in insertion order. Ancestor instances come before the local ones, which
     * matches the temporal order in which they were registered while traversing
     * the proof tree. Used by the GUI / HTML export for the "rinstances" panel.
     */
    public java.util.LinkedHashSet<String> getRinstances() {
        // Collect ancestors top-down first
        java.util.Deque<IPLProofTree> chain = new java.util.ArrayDeque<>();
        IPLProofTree current = this;
        while (current != null) {
            chain.addFirst(current);
            IProofTree parent = current.getParent();
            current = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        }
        java.util.LinkedHashSet<String> all = new java.util.LinkedHashSet<>();
        for (IPLProofTree t : chain) {
            all.addAll(t.localRinstances);
        }
        return all;
    }

    /**
     * Registers a label under the current branch ID.
     * @return true if the label was new (not registered before)
     */
    public boolean registerLabel(FormulaLabel label) {
        if (label != null && sharedLabelBranchMap != null) {
            String labelKey = label.toString();
            if (!sharedLabelBranchMap.containsKey(labelKey)) {
                sharedLabelBranchMap.put(labelKey, branchId);
                if (IPLTracer.isEnabled()) {
                    tracer.logLabelRegistered(labelKey, branchId);
                }
                return true; // New label
            }
        }
        return false; // Label already existed
    }

    /**
     * Checks whether a label is accessible from the current branch.
     * A label is accessible if:
     * - It was created in the common trunk (branchId = "root")
     * - It was created in this branch (branchId == this.branchId)
     * - It was created in some ancestor branch (parent, grandparent, etc.)
     */
    public boolean isLabelAccessible(FormulaLabel label) {
        if (label == null) {
            return true; // Null labels are always accessible
        }

        // Defensive check
        if (sharedLabelBranchMap == null) {
            return true; // With no map, every label is accessible
        }

        String labelKey = label.toString();
        String labelBranch = sharedLabelBranchMap.get(labelKey);

        if (labelBranch == null) {
            // Unregistered label, likely a system one (TOP, BOTTOM)
            return true;
        }

        // Accessible if it belongs to the common trunk
        if ("root".equals(labelBranch)) {
            return true;
        }

        // Accessible if it belongs to this branch
        if (branchId.equals(labelBranch)) {
            return true;
        }

        return isAncestorBranch(labelBranch);
    }

    /**
     * Checks whether a branch (identified by its branchId) is an ancestor of the
     * current branch. Walks up from the current branch via getParent() until it
     * finds the given branch or runs out of parents.
     *
     * Note: this method is only called when the label was NOT created in "root"
     * nor in the current branch, so we only need to search intermediate ancestor
     * branches.
     *
     * @param ancestorBranchId the branchId of the ancestor branch to check for
     * @return true if the given branch is an ancestor of the current branch
     */
    private boolean isAncestorBranch(String ancestorBranchId) {
        // Every non-null ancestor of an IPLProofTree node is itself an IPLProofTree:
        // setReferences() always sets a new child's parent to the IPLProofTree that
        // created it (IPLProofTree.makeInstance()), and the root's parent is null,
        // which ends this walk.
        IProofTree current = this.getParent();

        while (current != null) {
            IPLProofTree iplParent = (IPLProofTree) current;

            if (ancestorBranchId.equals(iplParent.getBranchId())) {
                return true;
            }

            current = current.getParent();
        }

        return false; // The ancestor branch was not found in the ancestor chain
    }

    /**
     * Override of addLast that ONLY registers labels.
     *
     * We do not physically propagate formulas by Kripke monotonicity: it is
     * checked on demand, directly against the physical branch b (Definition 5.3,
     * IPLCanonicalStrategyImplementation.isCompletelyAnalyzed).
     *
     * This prevents:
     * - An explosion of formulas in the tree
     * - Infinite loops caused by rules that generate new labels
     * - Unnecessary propagation of formulas
     */
    @Override
    public void addLast(INode aNode) {
        super.addLast(aNode);

        if (!(aNode instanceof SignedFormulaNode)) {
            return;
        }

        SignedFormulaNode sfNode = (SignedFormulaNode) aNode;
        SignedFormula sf = (SignedFormula) sfNode.getContent();

        // Register this formula's label on the current branch
        if (sf instanceof LabelledFormula) {
            LabelledFormula lf = (LabelledFormula) sf;
            registerLabel(lf.getLabel());
        }

        // Snapshot the rinstances state at the moment the node was added
        // (used by the viewer to filter the rinstances view per node).
        recordRinstancesSnapshot(sfNode);
    }

    /**
     * Only maintains the sign multimap. Closure is not tested here: it is the static
     * predicate of Definitions 3.1 (b contains T A : ci and F A : cj with ci \u2AAF cj),
     * and {@link #checkPhysicalBForContradiction()} evaluates it on every iteration of
     * the inner loop, which is what Algorithm 1 line 5 asks for. Testing it again on
     * each insertion would only detect, one iteration earlier, closures that scan
     * already finds -- and could not detect the ones that matter, since \u2AAF keeps
     * growing after a pair is inserted and an insertion-time test never revisits it.
     */
    @Override
    protected void updateMultimap(SignedFormulaNode aNode) {
        SignedFormula sf = (SignedFormula) aNode.getContent();
        getFsmm().put(sf.getFormula(), sf.getSign());
    }

    /**
     * Returns the physical ls-formulas of the current branch (this branch's locals
     * plus all ancestors), deduplicated, in insertion order.
     *
     * Used by {@link main.newstrategy.ipl.IPLCanonicalStrategyImplementation} to
     * evaluate the recursive "completely analyzed" predicate of Definition 5.3:
     * that predicate recurses directly on b, never materializing a
     * monotonic-closure set of composite ls-formulas.
     */
    public List<SignedFormula> getPhysicalFormulas() {
        return collectPhysicalFormulas();
    }

    /**
     * Checks for contradictions of the form T A:ci, F A:cj, ci <= cj by iterating
     * directly over the physical branch b (branch + ancestors) -- the Table 2
     * closure rule.
     *
     * Called at the end of every loop iteration to catch contradictions that
     * were not detected incrementally (e.g. when both formulas live only in
     * ancestors).
     *
     * The closure rule is stated directly over the physical branch b (the paper
     * defines no extended set for this), so iterating b is correct and
     * sufficient on its own.
     *
     * @return true if a contradiction was found and the branch was marked closed
     */
    public boolean checkPhysicalBForContradiction() {
        if (isLocallyClosed()) return true;

        List<SignedFormula> physicalB = collectPhysicalFormulas();

        for (SignedFormula sf1 : physicalB) {
            if (!sf1.getSign().equals(IPLSigns.TRUE)) continue;
            if (!(sf1 instanceof LabelledFormula)) continue;

            LabelledFormula lf1 = (LabelledFormula) sf1;
            FormulaLabel label1 = lf1.getLabel();
            if (!isLabelAccessible(label1)) continue;

            Context context = getContextFromLabel(label1);
            if (context == null) continue;

            for (SignedFormula sf2 : physicalB) {
                if (!sf2.getSign().equals(IPLSigns.FALSE)) continue;
                if (!(sf2 instanceof LabelledFormula)) continue;
                if (!sf2.getFormula().equals(sf1.getFormula())) continue;

                FormulaLabel label2 = ((LabelledFormula) sf2).getLabel();
                if (!isLabelAccessible(label2)) continue;

                if (isLowerOrEqual(context, label1, label2)) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logClosure(sf1.getFormula() + " " + label1,
                                sf2.getFormula() + " " + label2,
                                label1 + " \u2AAF " + label2);
                    }
                    setClosingReason(sf1);
                    setLocallyClosed(true);
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Gets the Context from a FormulaLabel (if it is a ContextFormulaLabel)
     */
    private Context getContextFromLabel(FormulaLabel label) {
        if (label instanceof ContextFormulaLabel) {
            return ((ContextFormulaLabel) label).getContext();
        }
        return null;
    }

    /**
     * Collects all physical formulas of b (current branch + ancestors), deduplicated.
     * Used by checkPhysicalBForContradiction to iterate b directly.
     */
    private List<SignedFormula> collectPhysicalFormulas() {
        List<SignedFormula> result = new ArrayList<>();
        Set<SignedFormula> seen = new HashSet<>();
        IPLProofTree current = this;
        while (current != null) {
            IProofTreeVeryBasicIterator it = current.getTopDownIterator();
            while (it.hasNext()) {
                INode node = it.next();
                if (node instanceof SignedFormulaNode) {
                    SignedFormula sf = (SignedFormula) ((SignedFormulaNode) node).getContent();
                    if (seen.add(sf)) result.add(sf);
                }
            }
            IProofTree parent = current.getParent();
            current = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        }
        return result;
    }

    /**
     * Checks whether label1 <= label2 in the given context
     */
    private boolean isLowerOrEqual(Context context, FormulaLabel label1, FormulaLabel label2) {
        if (label1.equals(label2)) {
            return true; // Reflexive: ci <= ci
        }
        return context.isLowerOrEqualTo(label1, label2);
    }

    /**
     * Looks up a formula with a specific sign, formula and label within the
     * accessibility group (current branch and its ancestors).
     *
     * Used to check whether the formulas that PB would generate already exist,
     * so as to avoid applying PB redundantly.
     *
     * @param formula the formula to look up
     * @param sign the sign (T or F)
     * @param label the specific label to look up
     * @return the SignedFormula found, or null if it does not exist
     */
    public SignedFormula findFormulaWithSignAndLabel(Formula formula, Object sign, FormulaLabel label) {
        IProofTreeVeryBasicIterator it = this.getTopDownIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (node instanceof SignedFormulaNode) {
                SignedFormula sf = (SignedFormula) node.getContent();

                // Compare sign
                boolean signMatches = sf.getSign().equals(sign) ||
                                     sf.getSign().toString().equals(sign.toString());
                if (!signMatches) continue;

                // Compare formula
                boolean formulaMatches = sf.getFormula().equals(formula) ||
                                        sf.getFormula().toString().equals(formula.toString());
                if (!formulaMatches) continue;

                // Compare label (only when both are LabelledFormula)
                if (sf instanceof logic.labelledFormulas.LabelledFormula &&
                    label instanceof logic.labelledFormulas.ContextFormulaLabel) {
                    logic.labelledFormulas.LabelledFormula lf = (logic.labelledFormulas.LabelledFormula) sf;
                    FormulaLabel sfLabel = lf.getLabel();

                    // Compare labels: they must be equal (same index and same context)
                    if (sfLabel.equals(label) || sfLabel.toString().equals(label.toString())) {
                        return sf;
                    }
                } else if (sf instanceof logic.labelledFormulas.LabelledFormula) {
                    // If sf has a label but label is not a ContextFormulaLabel, compare toString
                    logic.labelledFormulas.LabelledFormula lf = (logic.labelledFormulas.LabelledFormula) sf;
                    if (lf.getLabel().toString().equals(label.toString())) {
                        return sf;
                    }
                }
            }
        }
        return null;
    }

}
