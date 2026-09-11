package proverinterface.proofviewer;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.swing.BorderFactory;
import javax.swing.JPanel;

import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.SignedFormula;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.proofTree.iterator.IProofTreeVeryBasicIterator;
import main.tableau.IProof;

/**
 * Side panel for IPL proofs showing the Kripke label partial order.
 * Renders labels as nodes and ordering relations as directed edges.
 */
public class IPLContextPanel extends JPanel {

    private static final long serialVersionUID = 1L;

    private IProof proof;
    private List<String> labels = new ArrayList<>();
    private List<String[]> edges = new ArrayList<>();

    public IPLContextPanel() {
        setBackground(Color.WHITE);
        setBorder(BorderFactory.createTitledBorder("Kripke Context (label ordering)"));
        setPreferredSize(new Dimension(220, 300));
    }

    public void setProof(IProof proof) {
        this.proof = proof;
        extractContext();
        repaint();
    }

    private void extractContext() {
        labels.clear();
        edges.clear();
        if (proof == null) return;

        IProofTree tree = proof.getProofTree();
        if (tree == null) return;

        Context context = null;
        List<FormulaLabel> contextLabels = null;

        IProofTreeVeryBasicIterator it = tree.getTopDownIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (!(node instanceof SignedFormulaNode)) continue;
            SignedFormula sf = (SignedFormula) ((SignedFormulaNode) node).getContent();
            if (sf instanceof LabelledFormula) {
                FormulaLabel label = ((LabelledFormula) sf).getLabel();
                if (label instanceof ContextFormulaLabel) {
                    context = ((ContextFormulaLabel) label).getContext();
                    break;
                }
            }
        }

        if (context == null) return;
        contextLabels = context.getLabels();
        if (contextLabels == null) return;

        Map<String, FormulaLabel> labelMap = new HashMap<>();
        for (FormulaLabel fl : contextLabels) {
            String name = fl.toString();
            if (!labelMap.containsKey(name)) {
                labelMap.put(name, fl);
                labels.add(name);
            }
        }

        // Only draw covering relations (Hasse diagram): skip i-j edges for which
        // some intermediate k with i<=k<=j already exists, since those are
        // implied by transitivity and would otherwise clutter the diagram.
        for (int i = 0; i < labels.size(); i++) {
            for (int j = 0; j < labels.size(); j++) {
                if (i == j) continue;
                FormulaLabel li = labelMap.get(labels.get(i));
                FormulaLabel lj = labelMap.get(labels.get(j));
                if (li == null || lj == null || !context.isLowerOrEqualTo(li, lj)) continue;

                boolean isCovering = true;
                for (int k = 0; k < labels.size() && isCovering; k++) {
                    if (k == i || k == j) continue;
                    FormulaLabel lk = labelMap.get(labels.get(k));
                    if (lk != null && context.isLowerOrEqualTo(li, lk) && context.isLowerOrEqualTo(lk, lj)) {
                        isCovering = false;
                    }
                }
                if (isCovering) {
                    edges.add(new String[]{labels.get(i), labels.get(j)});
                }
            }
        }
    }

    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);
        if (labels.isEmpty()) {
            g.setColor(Color.GRAY);
            g.setFont(new Font("SansSerif", Font.ITALIC, 12));
            g.drawString("No context loaded", 20, 40);
            return;
        }

        Graphics2D g2 = (Graphics2D) g;
        g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);

        int panelW = getWidth();
        int topMargin = 30;
        int nodeRadius = 18;
        int verticalSpacing = 50;

        Map<String, int[]> positions = new HashMap<>();
        for (int i = 0; i < labels.size(); i++) {
            int x = panelW / 2 + (i % 2 == 0 ? -30 : 30) * ((i + 1) / 2);
            int y = topMargin + i * verticalSpacing;
            positions.put(labels.get(i), new int[]{x, y});
        }

        g2.setColor(new Color(100, 100, 100));
        for (String[] edge : edges) {
            int[] from = positions.get(edge[0]);
            int[] to = positions.get(edge[1]);
            if (from != null && to != null) {
                g2.drawLine(from[0], from[1] + nodeRadius, to[0], to[1] - nodeRadius);
                int mx = (from[0] + to[0]) / 2 + 5;
                int my = (from[1] + to[1]) / 2;
                g2.setFont(new Font("SansSerif", Font.PLAIN, 10));
                g2.drawString("\u2264", mx, my);
            }
        }

        for (Map.Entry<String, int[]> entry : positions.entrySet()) {
            int x = entry.getValue()[0];
            int y = entry.getValue()[1];
            g2.setColor(new Color(70, 130, 180));
            g2.fillOval(x - nodeRadius, y - nodeRadius, nodeRadius * 2, nodeRadius * 2);
            g2.setColor(Color.WHITE);
            g2.setFont(new Font("SansSerif", Font.BOLD, 12));
            String label = entry.getKey();
            int sw = g2.getFontMetrics().stringWidth(label);
            g2.drawString(label, x - sw / 2, y + 4);
        }
    }
}
