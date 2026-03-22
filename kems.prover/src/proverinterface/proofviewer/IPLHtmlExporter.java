package proverinterface.proofviewer;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;

import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.SignedFormula;
import main.newstrategy.ipl.IPLTracer;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.proofTree.origin.SignedFormulaNodeOrigin;
import main.proofTree.iterator.IProofTreeBasicIterator;
import main.strategy.IClassicalProofTree;
import main.tableau.IProof;

/**
 * Generates a self-contained interactive HTML file from an IPL proof.
 * Features:
 * - Tree rendered as nested expandable details elements
 * - Color coding by rule type (CSS classes)
 * - Collapsible branches (closed branches collapsed by default)
 * - Context (label ordering) shown at the top
 * - Hover tooltips with full step details
 * - Trace JSON embedded in a script tag
 */
public class IPLHtmlExporter {

    public static void export(IProof proof, String outputPath) throws IOException {
        export(proof, outputPath, null);
    }

    public static void export(IProof proof, String outputPath, IPLTracer tracer) throws IOException {
        try (PrintWriter pw = new PrintWriter(new FileWriter(outputPath))) {
            pw.println(generateHtml(proof, tracer));
        }
    }

    public static String generateHtml(IProof proof, IPLTracer tracer) {
        StringBuilder sb = new StringBuilder();
        sb.append("<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
        sb.append("<meta charset=\"UTF-8\">\n");
        sb.append("<title>IPL Proof: ").append(esc(proof.getProblem().getName())).append("</title>\n");
        appendStyles(sb);
        sb.append("</head>\n<body>\n");

        sb.append("<h1>IPL Proof: ").append(esc(proof.getProblem().getName())).append("</h1>\n");
        sb.append("<p class=\"status\">Result: <strong>")
          .append(proof.isClosed() ? "CLOSED (theorem)" : "OPEN (not a theorem)")
          .append("</strong></p>\n");

        appendContext(sb, proof);
        appendLegend(sb);

        sb.append("<h2>Proof Tree</h2>\n");
        appendTree(sb, proof.getProofTree(), 0);

        if (tracer != null && tracer.getEventCount() > 0) {
            sb.append("\n<h2>Trace</h2>\n");
            sb.append("<details><summary>Show/hide text trace (")
              .append(tracer.getEventCount()).append(" events)</summary>\n");
            sb.append("<pre class=\"trace\">").append(esc(tracer.formatText())).append("</pre>\n");
            sb.append("</details>\n");

            sb.append("<script type=\"application/json\" id=\"trace-json\">\n");
            sb.append(tracer.formatJSON());
            sb.append("</script>\n");
        }

        sb.append("</body>\n</html>\n");
        return sb.toString();
    }

    private static void appendStyles(StringBuilder sb) {
        sb.append("<style>\n");
        sb.append("body { font-family: 'Segoe UI', system-ui, sans-serif; margin: 2em; background: #fafafa; }\n");
        sb.append("h1 { color: #333; }\n");
        sb.append("h2 { color: #555; border-bottom: 1px solid #ddd; padding-bottom: 4px; }\n");
        sb.append(".status { font-size: 1.1em; }\n");
        sb.append(".context { background: #eef; border: 1px solid #aac; border-radius: 6px; padding: 12px; margin: 12px 0; }\n");
        sb.append(".context h3 { margin-top: 0; }\n");
        sb.append(".legend { display: flex; gap: 16px; flex-wrap: wrap; margin: 12px 0; }\n");
        sb.append(".legend span { padding: 2px 8px; border-radius: 4px; font-size: 0.9em; }\n");
        sb.append("details { margin-left: 20px; }\n");
        sb.append("summary { cursor: pointer; padding: 3px 0; }\n");
        sb.append("summary:hover { background: #f0f0f0; }\n");
        sb.append(".node { margin: 2px 0; padding: 4px 8px; border-left: 3px solid #ddd; }\n");
        sb.append(".node:hover { background: #f5f5f5; }\n");
        sb.append(".formula { font-family: 'Courier New', monospace; }\n");
        sb.append(".rule-tag { font-size: 0.8em; padding: 1px 5px; border-radius: 3px; margin-left: 8px; color: white; }\n");
        sb.append(".one-premise  { color: #006400; } .one-premise  .rule-tag { background: #006400; }\n");
        sb.append(".two-premise  { color: #0000A0; } .two-premise  .rule-tag { background: #0000A0; }\n");
        sb.append(".pb           { color: #B46400; } .pb           .rule-tag { background: #B46400; }\n");
        sb.append(".closure      { color: #C80000; } .closure      .rule-tag { background: #C80000; }\n");
        sb.append(".propagation  { color: #800080; } .propagation  .rule-tag { background: #800080; }\n");
        sb.append(".problem      { color: #000;    } .problem      .rule-tag { background: #666; }\n");
        sb.append(".default      { color: #555;    } .default      .rule-tag { background: #999; }\n");
        sb.append(".closed-mark  { color: #C80000; font-weight: bold; font-size: 1.2em; }\n");
        sb.append(".open-mark    { color: #006400; font-size: 1.2em; }\n");
        sb.append("pre.trace { background: #f4f4f4; border: 1px solid #ddd; padding: 12px; overflow-x: auto; font-size: 0.85em; }\n");
        sb.append("[title] { border-bottom: 1px dotted #999; }\n");
        sb.append("</style>\n");
    }

    private static void appendContext(StringBuilder sb, IProof proof) {
        Context context = extractContext(proof);
        if (context == null) return;

        List<FormulaLabel> labels = context.getLabels();
        if (labels == null || labels.isEmpty()) return;

        sb.append("<div class=\"context\">\n");
        sb.append("<h3>Kripke Context (Label Ordering)</h3>\n");
        sb.append("<p>Labels: ");
        for (int i = 0; i < labels.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append("<strong>").append(esc(labels.get(i).toString())).append("</strong>");
        }
        sb.append("</p>\n<p>Ordering: ");

        boolean first = true;
        for (int i = 0; i < labels.size(); i++) {
            for (int j = 0; j < labels.size(); j++) {
                if (i == j) continue;
                if (context.isLowerOrEqualTo(labels.get(i), labels.get(j))) {
                    if (!first) sb.append(", ");
                    sb.append(esc(labels.get(i).toString())).append(" &le; ")
                      .append(esc(labels.get(j).toString()));
                    first = false;
                }
            }
        }
        if (first) sb.append("(reflexive only)");
        sb.append("</p>\n");
        sb.append("<p class=\"context-note\"><em>Reflexivity</em> (each <code>ci</code> &le; <code>ci</code>) is not listed. ")
          .append("Pairs are every <code>ci</code> &le; <code>cj</code> with <code>i&ne;j</code> such that the Context ")
          .append("relation holds (including transitive consequences of the Kripke order).</p>\n");
        sb.append("</div>\n");
    }

    private static void appendLegend(StringBuilder sb) {
        sb.append("<div class=\"legend\">\n");
        sb.append("<span class=\"one-premise\" style=\"border:1px solid #006400\">1-premise rule</span>\n");
        sb.append("<span class=\"two-premise\" style=\"border:1px solid #0000A0\">2-premise rule</span>\n");
        sb.append("<span class=\"pb\" style=\"border:1px solid #B46400\">PB (branching)</span>\n");
        sb.append("<span class=\"closure\" style=\"border:1px solid #C80000\">Closure</span>\n");
        sb.append("<span class=\"propagation\" style=\"border:1px solid #800080\">Propagation</span>\n");
        sb.append("<span class=\"problem\" style=\"border:1px solid #666\">Problem/Definition</span>\n");
        sb.append("</div>\n");
    }

    private static void appendTree(StringBuilder sb, IProofTree tree, int depth) {
        if (tree == null) return;

        boolean isClosed = (tree instanceof IClassicalProofTree) && ((IClassicalProofTree) tree).isClosed();
        boolean hasChildren = tree.getLeft() != null || tree.getRight() != null;

        boolean collapsed = isClosed && depth > 0;
        String openAttr = collapsed ? "" : " open";

        sb.append("<details").append(openAttr).append(">\n");
        sb.append("<summary>");
        if (isClosed) {
            sb.append("<span class=\"closed-mark\">&times;</span> ");
        } else if (!hasChildren) {
            sb.append("<span class=\"open-mark\">&compfn;</span> ");
        }
        sb.append("Branch (depth ").append(depth).append(")");
        sb.append("</summary>\n");

        IProofTreeBasicIterator it = tree.getLocalIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (!(node instanceof SignedFormulaNode)) continue;
            SignedFormulaNode sfn = (SignedFormulaNode) node;
            SignedFormula sf = (SignedFormula) sfn.getContent();

            String ruleName = getRuleName(sfn);
            String cssClass = IPLColorScheme.getCssClass(ruleName);

            sb.append("<div class=\"node ").append(cssClass).append("\"");
            String tooltip = buildTooltip(sfn, sf);
            if (tooltip != null) {
                sb.append(" title=\"").append(esc(tooltip)).append("\"");
            }
            sb.append(">\n");
            sb.append("<span class=\"formula\">").append(esc(sf.toString())).append("</span>");
            if (ruleName != null && !ruleName.isEmpty()) {
                sb.append("<span class=\"rule-tag\">").append(esc(ruleName)).append("</span>");
            }
            sb.append("\n</div>\n");
        }

        if (tree.getLeft() != null) {
            sb.append("<div style=\"margin-left:10px;border-left:2px solid #B46400;padding-left:6px\">\n");
            sb.append("<em style=\"color:#B46400;font-size:0.85em\">Left branch</em>\n");
            appendTree(sb, tree.getLeft(), depth + 1);
            sb.append("</div>\n");
        }
        if (tree.getRight() != null) {
            sb.append("<div style=\"margin-left:10px;border-left:2px dashed #B46400;padding-left:6px\">\n");
            sb.append("<em style=\"color:#B46400;font-size:0.85em\">Right branch</em>\n");
            appendTree(sb, tree.getRight(), depth + 1);
            sb.append("</div>\n");
        }

        sb.append("</details>\n");
    }

    private static String getRuleName(SignedFormulaNode sfn) {
        if (sfn.getOrigin() instanceof SignedFormulaNodeOrigin) {
            return ((SignedFormulaNodeOrigin) sfn.getOrigin()).getRule().toString();
        }
        if (sfn.getOrigin() != null) {
            return sfn.getOrigin().getName();
        }
        return "";
    }

    private static String buildTooltip(SignedFormulaNode sfn, SignedFormula sf) {
        StringBuilder tip = new StringBuilder();
        tip.append("Formula: ").append(sf.toString());
        if (sf instanceof LabelledFormula) {
            tip.append("\nLabel: ").append(((LabelledFormula) sf).getLabel());
        }
        tip.append("\nSign: ").append(sf.getSign());
        if (sfn.getOrigin() instanceof SignedFormulaNodeOrigin) {
            SignedFormulaNodeOrigin origin = (SignedFormulaNodeOrigin) sfn.getOrigin();
            tip.append("\nRule: ").append(origin.getRule());
            if (origin.getMain() != null) {
                tip.append("\nMain: ").append(origin.getMain().getContent());
            }
            if (origin.getAuxiliaries() != null) {
                for (SignedFormulaNode aux : origin.getAuxiliaries()) {
                    tip.append("\nAux: ").append(aux.getContent());
                }
            }
        } else if (sfn.getOrigin() != null) {
            tip.append("\nOrigin: ").append(sfn.getOrigin().getName());
        }
        return tip.toString();
    }

    private static Context extractContext(IProof proof) {
        if (proof == null || proof.getProofTree() == null) return null;
        IProofTree tree = proof.getProofTree();
        main.proofTree.iterator.IProofTreeVeryBasicIterator it = tree.getTopDownIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (!(node instanceof SignedFormulaNode)) continue;
            SignedFormula sf = (SignedFormula) ((SignedFormulaNode) node).getContent();
            if (sf instanceof LabelledFormula) {
                FormulaLabel label = ((LabelledFormula) sf).getLabel();
                if (label instanceof ContextFormulaLabel) {
                    return ((ContextFormulaLabel) label).getContext();
                }
            }
        }
        return null;
    }

    private static String esc(String s) {
        if (s == null) return "";
        return s.replace("&", "&amp;")
                .replace("<", "&lt;")
                .replace(">", "&gt;")
                .replace("\"", "&quot;")
                .replace("'", "&#39;");
    }
}
