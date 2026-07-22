package rules.ipl.labels;

import java.util.List;
import java.util.stream.Collectors;

import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.FormulaLabel;
import logic.signedFormulas.SignedFormulaList;

/**
 * LabelGetter implementing the correct IPL semantics:
 * Looks for the minimal existing label that is greater than or equal to both premises.
 * Only creates a new label if none satisfies the condition.
 */
public class MinimalGreaterLabelGetter extends LabelGetter {

    @Override
    public FormulaLabel getLabel(SignedFormulaList lfl) {
        if (lfl.size() < 2) {
            // For one-premise rules, use the premise's own label
            return lfl.get(0).getLabel();
        }

        // Get the labels of both premises
        FormulaLabel label1 = lfl.get(0).getLabel();
        FormulaLabel label2 = lfl.get(1).getLabel();

        // If we are working with ContextFormulaLabel, search in the context
        if (label1 instanceof ContextFormulaLabel) {
            Context context = ((ContextFormulaLabel) label1).getContext();
            return findMinimalGreaterOrEqualLabel(context, label1, label2);
        } else {
            // Without a context, use simple index-based labels
            return findMinimalGreaterOrEqualSimple(label1, label2);
        }
    }

    /**
     * Determines which of the two labels is greater
     */
    private FormulaLabel getMaxLabel(FormulaLabel label1, FormulaLabel label2) {
        // Compare by index for simple labels
        if (label1.getIndex() >= label2.getIndex()) {
            return label1;
        } else {
            return label2;
        }
    }

    /**
     * Looks for the minimal existing label in the context that is >= both premises.
     * If none exists, throws an exception because the rule should not have been applied.
     *
     * IMPORTANT: This method assumes the existence of such a label was already
     * checked before attempting to apply the rule (e.g. via
     * GreaterBinaryRelationLabelCondition). If it does not exist, the rule simply
     * cannot be applied.
     */
    private FormulaLabel findMinimalGreaterOrEqualLabel(Context context, FormulaLabel label1, FormulaLabel label2) {
        // Find every label in the context that is >= both premises
        List<FormulaLabel> candidateLabels = context.getLabels().stream()
            .filter(label -> context.isGreaterOrEqualTo(label, label1) && context.isGreaterOrEqualTo(label, label2))
            .collect(Collectors.toList());

        if (!candidateLabels.isEmpty()) {
            // Find the minimal one among the candidates (lowest index)
            FormulaLabel minimalCandidate = candidateLabels.get(0);
            for (FormulaLabel candidate : candidateLabels) {
                if (candidate.getIndex() < minimalCandidate.getIndex()) {
                    minimalCandidate = candidate;
                }
            }
            return minimalCandidate;
        } else {
            // No label satisfies the condition.
            // This means the rule CANNOT be applied.
            // The exception signals that a rule was attempted while its condition did not hold.
            throw new RuntimeException("No candidate label found - rule condition not satisfied: " +
                "no label exists that is >= both " + label1 + " and " + label2);
        }
    }

    /**
     * For simple labels with no context, use index-based logic
     */
    private FormulaLabel findMinimalGreaterOrEqualSimple(FormulaLabel label1, FormulaLabel label2) {
        FormulaLabel maxLabel = getMaxLabel(label1, label2);

        // In this simple case, the maximum label is already the correct answer,
        // since we assume the labels are ordered and the maximum is already >= both
        return maxLabel;
    }
}
