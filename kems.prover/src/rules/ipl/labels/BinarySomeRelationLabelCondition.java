package rules.ipl.labels;

import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.SignedFormulaList;

/**
 * @author placiana
 * This class models the condition that there exists a relation between Ci and Cj, in either direction.
 * Ci <= Cj or Cj <= Ci
 *
 */
public class BinarySomeRelationLabelCondition implements LabelCondition {

    @Override
    public boolean matches(SignedFormulaList lfl) {
        LabelledFormula main = (LabelledFormula) lfl.get(0);
        LabelledFormula aux = (LabelledFormula) lfl.get(1);
        return main.getLabel().lowerOrEqualThan(aux.getLabel()) || aux.getLabel().lowerOrEqualThan(main.getLabel());
    }

	@Override
	public FormulaLabel getAuxiliaryLabel(LabelledFormula main) {
		return main.getLabel().getGreaterFormulaLabel();
	}

}
