package rules.ipl.labels;

import logic.labelledFormulas.FormulaLabel;
import logic.signedFormulas.SignedFormulaList;

/**
 * Mints a fresh constant strictly above the main premise's label, which is what the two
 * constant-introducing rules of Table 2 (F-&gt; and F~) require: {@code ci \u2AAF cj, cj new}.
 *
 * <p>Minting only ever upward, and always above exactly ONE existing label, is what keeps
 * the constant ordering a tree rooted at c0. That in turn is what makes the set of common
 * upper bounds of two labels either empty or possessed of a unique minimum, which is the
 * precondition {@link MinimalGreaterLabelGetter} relies on to pick {@code ck} without an
 * arbitrary choice. Two earlier variants of this getter could break that invariant -- one
 * minting above a whole collection of labels (joining from below), the other above the
 * auxiliary premise -- and neither was ever used; they were removed so the invariant holds
 * by construction rather than by accident. The same reason removed
 * {@code LabelCondition.getAuxiliaryLabel}, which minted below an existing label.
 */
public class NewLabelGetter extends LabelGetter {

	@Override
	public FormulaLabel getLabel(SignedFormulaList lfl) {
		return lfl.get(0).getLabel().getGreaterFormulaLabel();
	}

}
