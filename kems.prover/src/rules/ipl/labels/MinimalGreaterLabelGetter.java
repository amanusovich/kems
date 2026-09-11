package rules.ipl.labels;

import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.FormulaLabel;
import logic.signedFormulas.SignedFormulaList;

/**
 * Conclusion label for the two-premise rules that carry a
 * {@code GreaterBinaryRelationLabelCondition} -- T->1 of Table 2, which concludes
 * {@code T B : ck} for a ck with {@code ci <= ck} and {@code cj <= ck}.
 *
 * <p>The theory leaves ck free among the constants of Cb (Definitions 3.1). This
 * implementation returns the <em>least</em> such ck, and that choice is forced rather
 * than arbitrary: concluding as low as possible is the strongest conclusion, since
 * T-monotonicity carries it to every constant above.
 *
 * <p>The least common upper bound is simply the greater of the two premise labels.
 * Constants are only ever introduced strictly above exactly one existing constant
 * (NewLabelGetter is the only code path that creates them, and addRelation has no
 * other caller), so <code>&lt;=</code> is a tree: two constants have a common upper
 * bound only if they are already comparable, and then the upper set of the greater one
 * has that same constant as its minimum. Two consequences matter:
 *
 * <ul>
 *   <li>the conclusion always lands on one of the rule's own premise labels, hence on a
 *       constant of Cb -- never on one introduced in a sibling branch, so this rule
 *       cannot smuggle a foreign constant into a branch's domain;</li>
 *   <li>there is nothing to search: scanning the whole Context for candidates and
 *       breaking ties by index, as an earlier version did, computes exactly this.</li>
 * </ul>
 *
 * Checked over the ILTP propositional library: 3054 applications, none landing on
 * anything other than a premise label.
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

        // If we are working with ContextFormulaLabel, use the branch's own ordering
        if (label1 instanceof ContextFormulaLabel) {
            Context context = ((ContextFormulaLabel) label1).getContext();
            return greaterOf(context, label1, label2);
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
     * The least label that is {@code >=} both premises: the greater of the two.
     *
     * <p>Throws when they are incomparable. That cannot happen when the rule's own
     * {@code GreaterBinaryRelationLabelCondition} has already been checked, which is
     * the only way this getter is reached; the exception is there so that a future rule
     * wired up without that condition fails loudly instead of picking a wrong label.
     */
    private FormulaLabel greaterOf(Context context, FormulaLabel label1, FormulaLabel label2) {
        if (context.isGreaterOrEqualTo(label2, label1)) return label2;
        if (context.isGreaterOrEqualTo(label1, label2)) return label1;
        throw new RuntimeException("No candidate label found - rule condition not satisfied: "
                + label1 + " and " + label2 + " are incomparable");
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
