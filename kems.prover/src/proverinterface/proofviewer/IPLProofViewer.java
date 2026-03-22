package proverinterface.proofviewer;

import java.awt.Color;

import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.ScrollPaneConstants;

import main.tableau.IProof;
import proverinterface.ProverInterface;

/**
 * IPL-specific ProofViewer that adds a Kripke context panel
 * showing the label partial order alongside the proof tree.
 */
public class IPLProofViewer extends ProofViewer {

    private static final long serialVersionUID = 1L;
    private IPLContextPanel contextPanel;

    public IPLProofViewer(ProverInterface proverInterface) {
        super(proverInterface);
        contextPanel = new IPLContextPanel();

        JScrollPane contextScroller = new JScrollPane(contextPanel);
        contextScroller.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);

        JSplitPane existingSplit = (JSplitPane) getContentPane();

        JSplitPane outerSplit = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
                existingSplit, contextScroller);
        outerSplit.setOneTouchExpandable(true);
        outerSplit.setResizeWeight(0.8);
        setContentPane(outerSplit);
    }

    @Override
    public void setProof(IProof proof) {
        super.setProof(proof);
        if (contextPanel != null) {
            contextPanel.setProof(proof);
        }
    }

    public Color getNodeColor(String ruleName) {
        return IPLColorScheme.getColor(ruleName);
    }
}
