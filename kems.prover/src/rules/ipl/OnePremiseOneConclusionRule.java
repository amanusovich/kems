/*
 * Created on 10/11/2004
 *
 */
package rules.ipl;

import logic.formulas.FormulaFactory;
import logic.labelledFormulas.LabelledFormula;
import logic.labelledFormulas.LabelledFormulaFactory;
import logic.signedFormulas.SignedFormulaFactory;
import logic.signedFormulas.SignedFormulaList;
import rules.patterns.IUnarySignedFormulaPattern;

public class OnePremiseOneConclusionRule extends OneConclusionIPLRule {

	IUnarySignedFormulaPattern _premise;

	private final boolean rangingConclusionLabel;

	public OnePremiseOneConclusionRule(String name, IUnarySignedFormulaPattern premise, KELabelledAction conclusion) {
		this(name, premise, conclusion, false);
	}

	public OnePremiseOneConclusionRule(String name, IUnarySignedFormulaPattern premise, KELabelledAction conclusion,
			boolean rangingConclusionLabel) {
		super(name, conclusion);
		_premise = premise;
		this.rangingConclusionLabel = rangingConclusionLabel;
	}

	/**
	 * Whether this rule's side condition leaves the conclusion's label free to range, so
	 * that the rule has one instance per admissible label rather than one per premise.
	 *
	 * <p>T~ is the only such rule in Table 2: {@code T ~A : ci} with {@code ci \u2AAF cj}
	 * yields {@code F A : cj} for EVERY cj above ci, so each cj is a distinct instance in
	 * the sense of Algorithm 1 line 7 and of Section 3.2, where labels are said to
	 * distinguish rule instances. Rules that reuse a premise's label, or mint a fresh one,
	 * have exactly one instance per premise and answer false.
	 *
	 * <p>The applicator asks the rule instead of inspecting the formula's sign and
	 * connective, so that adding another rule with a ranging label cannot silently fall
	 * through the wrong path.
	 */
	public boolean hasRangingConclusionLabel() {
		return rangingConclusionLabel;
	}

	public SignedFormulaList getPossibleConclusions(SignedFormulaFactory sff, FormulaFactory ff,
			SignedFormulaList sfl) {
	    /*
		SignedFormula premise = sfl.get(0);
		if (_premise.matches(premise)) {
			return new SignedFormulaList(
					((KESignedFormulaGetter) getConclusion().getContent()).getSignedFormula(sff, ff, sfl));
		} else {
			return null;
		}
		*/
	    // Safe check for IPL
	    LabelledFormulaFactory lff;
	    if (sff instanceof LabelledFormulaFactory) {
	        lff = (LabelledFormulaFactory) sff;
	    } else {
	        lff = new LabelledFormulaFactory();
	    }
	    return getPossibleConclusions(lff, sff, ff, sfl);
	}

	public SignedFormulaList getPossibleConclusions(LabelledFormulaFactory lff, SignedFormulaFactory sff,
			FormulaFactory ff, SignedFormulaList lfl) {
		LabelledFormula premise = (LabelledFormula) lfl.get(0);
		if (_premise.matches(premise.getSignedFormula())) {
			LabelledFormula lf = getConclusion().getLabelledFormula(lff, ff, lfl);
			return new SignedFormulaList(lf);
		} else {
			return null;
		}
	}

}