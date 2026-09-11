package proverinterface.proofviewer;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Font;

import javax.swing.BorderFactory;
import javax.swing.DefaultListModel;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.ListSelectionModel;
import javax.swing.SwingConstants;

import logicalSystems.ipl.IPLProofTree;

/**
 * Swing side panel that displays the rinstances registered for a branch of
 * an IPL proof, updating when a formula node is clicked in the proof tree.
 * rinstances are the rule instances registered for that branch, preventing
 * the same rule from being applied twice.
 *
 * Usage:
 *   IPLBranchDetailPanel panel = new IPLBranchDetailPanel();
 *   panel.updateForBranch(iplProofTree);
 */
public class IPLBranchDetailPanel extends JPanel {

    private static final Font MONO = new Font(Font.MONOSPACED, Font.PLAIN, 12);

    private final JLabel headerLabel;
    private final DefaultListModel<String> rinstancesModel;

    public IPLBranchDetailPanel() {
        super(new BorderLayout(0, 0));
        setBorder(BorderFactory.createTitledBorder("rinstances"));

        headerLabel = new JLabel("Click a formula to see branch details", SwingConstants.CENTER);
        headerLabel.setFont(headerLabel.getFont().deriveFont(Font.ITALIC));
        headerLabel.setForeground(Color.GRAY);
        headerLabel.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4));

        rinstancesModel = new DefaultListModel<>();
        JList<String> rinstancesList = buildList(rinstancesModel);

        add(headerLabel, BorderLayout.NORTH);
        add(new JScrollPane(rinstancesList), BorderLayout.CENTER);
    }

    /**
     * Updates the panel to display the rinstances for the branch that
     * contains the given formula node.
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

        // rinstances is local per branch with ancestor walk (Algorithm 1 line 4,
        // reset per outer-loop iteration). getRinstances() returns the full chain
        // root → … → branch in insertion order, which is the temporal order in
        // which they were registered.
        rinstancesModel.clear();
        java.util.LinkedHashSet<String> rinsts = branch.getRinstances();
        if (rinsts.isEmpty()) {
            rinstancesModel.addElement("(none)");
        } else {
            for (String r : rinsts) rinstancesModel.addElement(r);
        }
    }

    /** Clears the list and shows a placeholder message. */
    public void clearPanel(String message) {
        headerLabel.setText(message);
        headerLabel.setForeground(Color.GRAY);
        rinstancesModel.clear();
    }

    // -------------------------------------------------------------------------

    private JList<String> buildList(DefaultListModel<String> model) {
        JList<String> list = new JList<>(model);
        list.setFont(MONO);
        list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        return list;
    }
}
