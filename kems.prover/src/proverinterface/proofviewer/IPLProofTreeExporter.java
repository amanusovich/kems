package proverinterface.proofviewer;

import java.util.ArrayList;
import java.util.List;

import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.SignedFormula;
import logicalSystems.ipl.IPLProofTree;
import main.newstrategy.ipl.IPLTracer;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.proofTree.iterator.IProofTreeBasicIterator;
import main.proofTree.iterator.IProofTreeVeryBasicIterator;
import main.proofTree.origin.NamedOrigin;
import main.proofTree.origin.SignedFormulaNodeOrigin;
import main.strategy.IClassicalProofTree;
import main.tableau.IProof;
import main.tableau.verifier.ExtendedProof;

/**
 * Exports a completed IPL proof as a rich JSON document for use by
 * IPLHtmlExporter and IPLBranchDetailPanel.
 *
 * JSON shape:
 * {
 *   "problem": "...",
 *   "closed": true,
 *   "kripke": { "labels": [...], "relations": [[a,b],...] },
 *   "tree": { branchNode (recursive) },
 *   "trace": { ...IPLTracer.formatJSON() content... }
 * }
 *
 * Each branchNode:
 * {
 *   "branchId": "root",
 *   "closed": true,
 *   "formulas": [ { id, text, sign, label, ruleType, rule, main, auxiliaries,
 *                   rinstancesAtCreation } ],  // rinstancesAtCreation captures the
 *                                              // path state when this node was added.
 *   "rinstances": [ "F_A_IMPLIES_B_TA_FB:F phi c0", ... ],  // this branch + all ancestors, in insertion order
 *   "left": { ... } | null,
 *   "right": { ... } | null
 * }
 */
public class IPLProofTreeExporter {

    public static String toJson(IProof proof, IPLTracer tracer) {
        if (proof == null) return "{}";
        StringBuilder sb = new StringBuilder();
        sb.append("{\n");

        // --- problem name / status ---
        String pname = (proof.getProblem() != null && proof.getProblem().getName() != null)
                ? proof.getProblem().getName() : "";
        sb.append("  \"problem\": ").append(jsonStr(pname)).append(",\n");

        boolean closed = (proof.getProofTree() instanceof IClassicalProofTree)
                && ((IClassicalProofTree) proof.getProofTree()).isClosed();
        sb.append("  \"closed\": ").append(closed).append(",\n");

        // --- Kripke context ---
        appendKripkeContext(sb, proof);

        // After ProofVerifier.verify(), proof is an ExtendedProof whose getProofTree()
        // returns an ExtendedProofTree (not IPLProofTree). Extract the original IPLProofTree
        // so we can access the global rinstances set.
        IPLProofTree iplRoot = extractIPLRoot(proof);

        // --- proof tree ---
        sb.append("  \"tree\": ");
        appendBranchNode(sb, proof.getProofTree(), iplRoot, 1);
        sb.append(",\n");

        // --- trace ---
        sb.append("  \"trace\": ");
        if (tracer != null && IPLTracer.isEnabled()) {
            // formatJSON() returns a complete {events:[...]} object
            sb.append(tracer.formatJSON().trim());
        } else {
            sb.append("null");
        }
        sb.append("\n}\n");

        return sb.toString();
    }

    /**
     * Extracts the original IPLProofTree from a proof.
     *
     * After ProofVerifier.verify(), the IProof is an ExtendedProof whose
     * getProofTree() returns an ExtendedProofTree.  The original IPLProofTree
     * (carrying global rinstances) lives in
     * ExtendedProof.getOriginalProof().getProofTree().
     */
    static IPLProofTree extractIPLRoot(IProof proof) {
        if (proof == null) return null;
        if (proof instanceof ExtendedProof) {
            IProof orig = ((ExtendedProof) proof).getOriginalProof();
            if (orig != null && orig.getProofTree() instanceof IPLProofTree) {
                return (IPLProofTree) orig.getProofTree();
            }
        }
        if (proof.getProofTree() instanceof IPLProofTree) {
            return (IPLProofTree) proof.getProofTree();
        }
        return null;
    }

    // -------------------------------------------------------------------------
    // Kripke context
    // -------------------------------------------------------------------------

    private static void appendKripkeContext(StringBuilder sb, IProof proof) {
        sb.append("  \"kripke\": ");
        Context ctx = extractContext(proof);
        if (ctx == null) {
            sb.append("null,\n");
            return;
        }
        List<FormulaLabel> labels = ctx.getLabels();
        sb.append("{\n");
        sb.append("    \"labels\": [");
        for (int i = 0; i < labels.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(jsonStr(labels.get(i).toString()));
        }
        sb.append("],\n");
        sb.append("    \"relations\": [");
        // Only emit covering relations (Hasse diagram): skip i-j edges for which
        // some intermediate k with i<=k<=j already exists, since those are
        // implied by transitivity and would otherwise clutter the graph.
        boolean first = true;
        for (int i = 0; i < labels.size(); i++) {
            for (int j = 0; j < labels.size(); j++) {
                if (i == j) continue;
                if (!ctx.isLowerOrEqualTo(labels.get(i), labels.get(j))) continue;

                boolean isCovering = true;
                for (int k = 0; k < labels.size() && isCovering; k++) {
                    if (k == i || k == j) continue;
                    if (ctx.isLowerOrEqualTo(labels.get(i), labels.get(k))
                            && ctx.isLowerOrEqualTo(labels.get(k), labels.get(j))) {
                        isCovering = false;
                    }
                }
                if (isCovering) {
                    if (!first) sb.append(", ");
                    sb.append("[").append(jsonStr(labels.get(i).toString()))
                      .append(", ").append(jsonStr(labels.get(j).toString())).append("]");
                    first = false;
                }
            }
        }
        sb.append("]\n");
        sb.append("  },\n");
    }

    // -------------------------------------------------------------------------
    // Recursive branch node serialisation
    // -------------------------------------------------------------------------

    /**
     * Serialises one branch node to JSON.
     *
     * @param tree    the displayed tree node (ExtendedProofTree after verification,
     *                or IPLProofTree when running without verification)
     * @param iplTree the corresponding original IPLProofTree, used for IPL-specific
     *                data (global rinstances).  May be null if not available.
     */
    private static void appendBranchNode(StringBuilder sb, IProofTree tree,
                                          IPLProofTree iplTree, int indent) {
        if (tree == null) {
            sb.append("null");
            return;
        }

        String pad = "  ".repeat(indent);
        String pad2 = "  ".repeat(indent + 1);

        boolean isClosed = (tree instanceof IClassicalProofTree)
                && ((IClassicalProofTree) tree).isClosed();

        // branchId: prefer from iplTree (has getBranchId); fall back to displayed tree
        String branchId = (iplTree != null) ? iplTree.getBranchId()
                : (tree instanceof IPLProofTree) ? ((IPLProofTree) tree).getBranchId()
                : "unknown";

        sb.append("{\n");
        sb.append(pad2).append("\"branchId\": ").append(jsonStr(branchId)).append(",\n");
        sb.append(pad2).append("\"closed\": ").append(isClosed).append(",\n");

        // --- physical formulas (b) ---
        sb.append(pad2).append("\"formulas\": [\n");
        // We walk the displayed tree (which carries the rule/origin metadata
        // used to render the GUI) and, in parallel, the original IPL tree.
        // The IPL nodes are needed to look up per-node rinstancesAtCreation
        // snapshots by reference identity, because ProofVerifier wraps the
        // original nodes into ExtendedNode instances when it builds the
        // displayed ExtendedProofTree.
        IProofTreeBasicIterator it = tree.getLocalIterator();
        IProofTreeBasicIterator iplIt = (iplTree != null) ? iplTree.getLocalIterator() : null;
        boolean firstFormula = true;
        int nodeId = 0;
        while (it.hasNext()) {
            INode node = it.next();
            SignedFormulaNode iplNode = nextSignedFormulaNode(iplIt);
            if (!(node instanceof SignedFormulaNode)) continue;
            SignedFormulaNode sfn = (SignedFormulaNode) node;
            SignedFormula sf = (SignedFormula) sfn.getContent();
            if (!firstFormula) sb.append(",\n");
            firstFormula = false;
            sb.append(pad2).append("  ");
            int riSnapshot = (iplTree != null && iplNode != null)
                    ? iplTree.getRinstancesAtCreation(iplNode) : -1;
            appendFormulaNode(sb, sfn, sf, nodeId++, riSnapshot);
        }
        sb.append("\n").append(pad2).append("],\n");

        // --- rinstances ---
        // rinstances is local per branch with ancestor walk (Algorithm 1, line 4).
        // getRinstances() returns the full chain root → … → branch in insertion order.
        sb.append(pad2).append("\"rinstances\": [");
        if (iplTree != null) {
            boolean firstRi = true;
            for (String r : iplTree.getRinstances()) {
                if (!firstRi) sb.append(", ");
                sb.append(jsonStr(r));
                firstRi = false;
            }
        }
        sb.append("],\n");

        // --- children: traverse displayed tree and IPL tree in parallel ---
        IProofTree leftTree = tree.getLeft();
        IPLProofTree leftIPL = (iplTree != null && iplTree.getLeft() instanceof IPLProofTree)
                ? (IPLProofTree) iplTree.getLeft() : null;
        sb.append(pad2).append("\"left\": ");
        appendBranchNode(sb, leftTree, leftIPL, indent + 1);
        sb.append(",\n");

        IProofTree rightTree = tree.getRight();
        IPLProofTree rightIPL = (iplTree != null && iplTree.getRight() instanceof IPLProofTree)
                ? (IPLProofTree) iplTree.getRight() : null;
        sb.append(pad2).append("\"right\": ");
        appendBranchNode(sb, rightTree, rightIPL, indent + 1);
        sb.append("\n");

        sb.append(pad).append("}");
    }

    private static void appendFormulaNode(StringBuilder sb, SignedFormulaNode sfn,
                                          SignedFormula sf, int id, int rinstancesAtCreation) {
        sb.append("{");
        sb.append("\"id\": ").append(id).append(", ");
        // Path-level rinstance count captured when this node was first added to
        // its branch (-1 if not available). The HTML viewer uses it to slice the
        // branch's rinstances list when displaying node detail, so the viewer
        // shows only the rule instances that already existed at the time this
        // node was created.
        sb.append("\"rinstancesAtCreation\": ").append(rinstancesAtCreation).append(", ");
        sb.append("\"text\": ").append(jsonStr(sf.toString())).append(", ");
        sb.append("\"sign\": ").append(jsonStr(sf.getSign().toString())).append(", ");

        String label = (sf instanceof LabelledFormula)
                ? ((LabelledFormula) sf).getLabel().toString()
                : "";
        sb.append("\"label\": ").append(jsonStr(label)).append(", ");

        // Rule type and name
        String ruleType = "UNKNOWN";
        String ruleName = null;
        String mainPremise = null;
        List<String> auxList = new ArrayList<>();

        if (sfn.getOrigin() == NamedOrigin.PROBLEM) {
            ruleType = "PROBLEM";
        } else if (sfn.getOrigin() == NamedOrigin.DEFINITION) {
            ruleType = "DEFINITION";
        } else if (sfn.getOrigin() instanceof SignedFormulaNodeOrigin) {
            SignedFormulaNodeOrigin origin = (SignedFormulaNodeOrigin) sfn.getOrigin();
            ruleName = origin.getRule() != null ? origin.getRule().toString() : null;
            ruleType = getRuleCategory(ruleName);
            if (origin.getMain() != null) {
                mainPremise = origin.getMain().getContent().toString();
            }
            if (origin.getAuxiliaries() != null) {
                for (SignedFormulaNode aux : origin.getAuxiliaries()) {
                    auxList.add(aux.getContent().toString());
                }
            }
        }

        sb.append("\"ruleType\": ").append(jsonStr(ruleType)).append(", ");
        sb.append("\"rule\": ").append(ruleName != null ? jsonStr(ruleName) : "null").append(", ");
        sb.append("\"main\": ").append(mainPremise != null ? jsonStr(mainPremise) : "null").append(", ");
        sb.append("\"auxiliaries\": [");
        for (int i = 0; i < auxList.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(jsonStr(auxList.get(i)));
        }
        sb.append("]}");
    }

    /**
     * Returns the next {@link SignedFormulaNode} from an iterator, or null if
     * the iterator is null or exhausted. Used to walk the IPL tree in parallel
     * with the displayed tree.
     */
    private static SignedFormulaNode nextSignedFormulaNode(IProofTreeBasicIterator it) {
        if (it == null) return null;
        while (it.hasNext()) {
            INode n = it.next();
            if (n instanceof SignedFormulaNode) return (SignedFormulaNode) n;
        }
        return null;
    }

    // -------------------------------------------------------------------------
    // Helpers
    // -------------------------------------------------------------------------

    private static Context extractContext(IProof proof) {
        if (proof == null || proof.getProofTree() == null) return null;
        IProofTreeVeryBasicIterator it = proof.getProofTree().getTopDownIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (!(node instanceof SignedFormulaNode)) continue;
            SignedFormula sf = (SignedFormula) ((SignedFormulaNode) node).getContent();
            if (sf instanceof LabelledFormula) {
                FormulaLabel lbl = ((LabelledFormula) sf).getLabel();
                if (lbl instanceof ContextFormulaLabel) {
                    return ((ContextFormulaLabel) lbl).getContext();
                }
            }
        }
        return null;
    }

    /** Maps a rule name to its display category (mirrors IPLColorScheme logic). */
    private static String getRuleCategory(String ruleName) {
        if (ruleName == null) return "default";
        String r = ruleName.toUpperCase();
        if (r.contains("CLOSE"))    return "CLOSURE";
        if (r.contains("PB"))       return "PB";
        if (r.contains("T_AND") || r.contains("F_OR") || r.contains("T_NOT")
                || r.contains("F_NOT") || r.contains("F_A_IMPLIES_B")) return "ONE_PREMISE";
        if (r.contains("T_OR_F") || r.contains("F_AND") || r.contains("T_IMPLIES")
                || r.contains("X_IMPLIES") || r.contains("F_IMPLIES_T")) return "TWO_PREMISE";
        return "default";
    }

    /** Escapes and wraps a string as a JSON string literal. */
    public static String jsonStr(String s) {
        if (s == null) return "null";
        return "\"" + s.replace("\\", "\\\\")
                       .replace("\"", "\\\"")
                       .replace("\n", "\\n")
                       .replace("\r", "\\r")
                       .replace("\t", "\\t")
               + "\"";
    }
}
