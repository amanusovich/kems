package proverinterface.proofviewer;

import java.awt.Color;

import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.ScrollPaneConstants;

import logicalSystems.ipl.IPLProofTree;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.proofTree.origin.NamedOrigin;
import main.tableau.IProof;
import proverinterface.ProverInterface;

/**
 * IPL-specific ProofViewer that adds:
 *  - A Kripke context panel (top-right) showing the label partial order
 *  - A branch-detail panel (bottom-right) that updates when a formula is clicked,
 *    showing b* virtual extensions and rinstances for the clicked branch
 */
public class IPLProofViewer extends ProofViewer
        implements InteractiveProofPane.FormulaSelectionListener {

    private static final long serialVersionUID = 1L;

    private IPLContextPanel contextPanel;
    private IPLBranchDetailPanel detailPanel;

    /**
     * The original IPLProofTree root (before ProofVerifier wraps it into
     * ExtendedProofTree).  Used to access global rinstances and extendBranch()
     * in the detail panel.
     */
    private IPLProofTree iplRootTree;

    public IPLProofViewer(ProverInterface proverInterface) {
        super(proverInterface);

        contextPanel = new IPLContextPanel();
        detailPanel  = new IPLBranchDetailPanel();

        JScrollPane contextScroller = new JScrollPane(contextPanel);
        contextScroller.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);

        // Right column: Kripke context on top, branch detail below
        JSplitPane rightSplit = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
                contextScroller, detailPanel);
        rightSplit.setOneTouchExpandable(true);
        rightSplit.setResizeWeight(0.35);

        // Outer split: proof tree (left) + right column
        JSplitPane existingSplit = (JSplitPane) getContentPane();
        JSplitPane outerSplit = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
                existingSplit, rightSplit);
        outerSplit.setOneTouchExpandable(true);
        outerSplit.setResizeWeight(0.75);
        setContentPane(outerSplit);

        // Register as formula-selection listener on the interactive pane
        getInteractiveProofPane().setFormulaSelectionListener(this);

        // Hide PROPAGATION-origin nodes from both main tree views.
        // These formulas (Kripke monotonicity) belong conceptually to b* and are
        // shown in the IPLBranchDetailPanel's "b* Extensions" tab instead.
        java.util.function.Predicate<SignedFormulaNode> nonPropagated =
            sfn -> sfn.getOrigin() == null
                || !NamedOrigin.PROPAGATION.getName().equals(sfn.getOrigin().getName());
        getInteractiveProofPane().setNodeFilter(nonPropagated);
        getFullViewProofPane().setNodeFilter(nonPropagated);
    }

    @Override
    public void setProof(IProof proof) {
        super.setProof(proof);
        // Save original IPLProofTree before it gets wrapped by ExtendedProof/ExtendedProofTree.
        iplRootTree = IPLProofTreeExporter.extractIPLRoot(proof);
        if (contextPanel != null) {
            contextPanel.setProof(proof);
        }
        if (detailPanel != null) {
            detailPanel.clearPanel("Click a formula to see branch details");
        }
    }

    @Override
    public void onFormulaSelected(SignedFormulaNode sfn, IProofTree branch) {
        if (detailPanel == null) return;
        IPLProofTree iplBranch = resolveIPLBranch(branch);
        if (iplBranch != null) {
            detailPanel.updateForBranch(iplBranch);
        } else {
            detailPanel.clearPanel("Branch detail not available for this node");
        }
    }

    /**
     * Resolves the IPLProofTree that corresponds to the given (possibly
     * ExtendedProofTree) branch by traversing the displayed tree and the
     * original IPL tree in parallel — they share the same branching structure.
     */
    private IPLProofTree resolveIPLBranch(IProofTree branch) {
        if (branch instanceof IPLProofTree) return (IPLProofTree) branch;
        if (iplRootTree == null || branch == null) return null;
        IProofTree extRoot = getProof() != null ? getProof().getProofTree() : null;
        if (extRoot == null) return null;
        return matchIPLBranch(iplRootTree, extRoot, branch);
    }

    private IPLProofTree matchIPLBranch(IPLProofTree iplNode, IProofTree extNode,
                                         IProofTree target) {
        if (extNode == target) return iplNode;
        IProofTree extLeft = extNode.getLeft();
        IProofTree iplLeft = iplNode.getLeft();
        if (extLeft != null && iplLeft instanceof IPLProofTree) {
            IPLProofTree found = matchIPLBranch((IPLProofTree) iplLeft, extLeft, target);
            if (found != null) return found;
        }
        IProofTree extRight = extNode.getRight();
        IProofTree iplRight = iplNode.getRight();
        if (extRight != null && iplRight instanceof IPLProofTree) {
            IPLProofTree found = matchIPLBranch((IPLProofTree) iplRight, extRight, target);
            if (found != null) return found;
        }
        return null;
    }

    public Color getNodeColor(String ruleName) {
        return IPLColorScheme.getColor(ruleName);
    }
}
