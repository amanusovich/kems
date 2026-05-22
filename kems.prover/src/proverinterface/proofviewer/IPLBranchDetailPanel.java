package proverinterface.proofviewer;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Font;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import javax.swing.BorderFactory;
import javax.swing.DefaultListModel;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.ListSelectionModel;
import javax.swing.SwingConstants;

import logic.signedFormulas.SignedFormula;
import logicalSystems.ipl.IPLProofTree;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.proofTree.iterator.IProofTreeBasicIterator;
import main.proofTree.origin.IOrigin;
import main.proofTree.origin.NamedOrigin;

/**
 * Swing side panel that displays per-branch details for an IPL proof.
 *
 * When a formula node is clicked in the proof tree:
 *  - Tab "b* Extensions": virtual formulas implied by Kripke monotonicity
 *    that are in b* but not physically in the proof tree segment
 *  - Tab "rinstances":    rule instances registered for that branch,
 *    preventing the same rule from being applied twice
 *
 * Usage:
 *   IPLBranchDetailPanel panel = new IPLBranchDetailPanel();
 *   panel.updateForBranch(iplProofTree);
 */
public class IPLBranchDetailPanel extends JPanel {

    private static final Font MONO = new Font(Font.MONOSPACED, Font.PLAIN, 12);

    private final JLabel headerLabel;
    private final DefaultListModel<String> bstarModel;
    private final DefaultListModel<String> rinstancesModel;
    private final JTabbedPane tabs;

    public IPLBranchDetailPanel() {
        super(new BorderLayout(0, 0));
        setBorder(BorderFactory.createTitledBorder("Branch Detail"));

        headerLabel = new JLabel("Click a formula to see branch details", SwingConstants.CENTER);
        headerLabel.setFont(headerLabel.getFont().deriveFont(Font.ITALIC));
        headerLabel.setForeground(Color.GRAY);
        headerLabel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));

        bstarModel = new DefaultListModel<>();
        rinstancesModel = new DefaultListModel<>();

        JList<String> bstarList = buildList(bstarModel);
        JList<String> rinstancesList = buildList(rinstancesModel);

        tabs = new JTabbedPane(JTabbedPane.TOP);
        tabs.addTab("b* Extensions", new JScrollPane(bstarList));
        tabs.addTab("rinstances", new JScrollPane(rinstancesList));

        add(headerLabel, BorderLayout.NORTH);
        add(tabs, BorderLayout.CENTER);
    }

    /**
     * Updates the panel to display b* extensions and rinstances for the
     * branch that contains the given formula node.
     *
     * @param branch the IPLProofTree segment (branch) whose node was clicked
     */
    public void updateForBranch(IPLProofTree branch) {
        if (branch == null) {
            clearPanel("No branch selected");
            return;
        }

        String branchId = branch.getBranchId();
        headerLabel.setText("Branch: " + branchId
            + (branch.isClosed() ? "  [CLOSED]" : "  [open]"));
        headerLabel.setForeground(branch.isClosed() ? new Color(183, 28, 28) : new Color(27, 94, 32));

        // ---- b* extensions ----
        // b* = b + Kripke-monotonicity extensions (Definition 5.3).
        // T-composite formulas at new labels are LAZILY materialized from b* when the
        // algorithm needs to process them (Algorithm 1 §5): they are added as physical
        // PROPAGATION-origin nodes at that moment, then rule-decomposed normally.
        // "Propagated" = lazily materialized from b*; "Virtual" = in b* but still not in b.
        bstarModel.clear();

        // 1) Collect all physical formulas on the path (local iterator per level)
        Set<String> physical = new java.util.HashSet<>();
        List<String> propagatedEntries = new ArrayList<>();
        Set<String> seenPropagated = new java.util.HashSet<>();
        IPLProofTree cur = branch;
        while (cur != null) {
            IProofTreeBasicIterator lit = cur.getLocalIterator();
            while (lit.hasNext()) {
                INode node = lit.next();
                if (node instanceof SignedFormulaNode) {
                    SignedFormulaNode sfNode = (SignedFormulaNode) node;
                    String sfStr = ((SignedFormula) sfNode.getContent()).toString();
                    physical.add(sfStr);
                    IOrigin origin = sfNode.getOrigin();
                    if (origin != null && NamedOrigin.PROPAGATION.getName().equals(origin.getName())) {
                        if (seenPropagated.add(sfStr)) {
                            propagatedEntries.add(sfStr);
                        }
                    }
                }
            }
            IProofTree parent = cur.getParent();
            cur = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        }

        // 2) Virtual b* extensions (implicitly in b* but not yet physical)
        Set<SignedFormula> bStar = branch.extendBranch();
        List<String> virtualEntries = new ArrayList<>();
        for (SignedFormula sf : bStar) {
            if (!physical.contains(sf.toString())) {
                virtualEntries.add(sf.toString());
            }
        }
        virtualEntries.sort(String::compareTo);
        propagatedEntries.sort(String::compareTo);

        int bstarCount = propagatedEntries.size() + virtualEntries.size();
        if (!propagatedEntries.isEmpty()) {
            bstarModel.addElement("--- Propagated (Kripke monotonicity, materialized into b) ---");
            for (String p : propagatedEntries) bstarModel.addElement("  " + p);
        }
        if (!virtualEntries.isEmpty()) {
            bstarModel.addElement("--- Virtual (implied by Kripke but not yet in b) ---");
            for (String v : virtualEntries) bstarModel.addElement("  " + v);
        }
        if (bstarCount == 0) {
            bstarModel.addElement("(none — no Kripke extensions for this branch)");
        }

        // ---- rinstances ----
        // rinstances is local per branch with ancestor walk (Algorithm 1 line 4 of
        // the revised paper, reset per outer-loop iteration). getRinstances()
        // returns the full chain root → … → branch in insertion order, which is
        // the temporal order in which they were registered.
        rinstancesModel.clear();
        java.util.LinkedHashSet<String> rinsts = branch.getRinstances();
        if (rinsts.isEmpty()) {
            rinstancesModel.addElement("(none)");
        } else {
            for (String r : rinsts) rinstancesModel.addElement(r);
        }

        // Update tab titles with counts
        tabs.setTitleAt(0, "b* Extensions (" + bstarCount + ")");
        tabs.setTitleAt(1, "rinstances (" + rinsts.size() + ")");
    }

    /** Clears both lists and shows a placeholder message. */
    public void clearPanel(String message) {
        headerLabel.setText(message);
        headerLabel.setForeground(Color.GRAY);
        bstarModel.clear();
        rinstancesModel.clear();
        tabs.setTitleAt(0, "b* Extensions");
        tabs.setTitleAt(1, "rinstances");
    }

    // -------------------------------------------------------------------------

    private JList<String> buildList(DefaultListModel<String> model) {
        JList<String> list = new JList<>(model);
        list.setFont(MONO);
        list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        return list;
    }
}
