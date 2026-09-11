package rules.ipl.labels;

import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.SignedFormulaList;

/**
 * @author generated
 * Main formula label less than or equal to aux formula (ci <= cj)
 * This is the opposite of GreaterThanLabelCondition
 */
public class LessThanLabelCondition implements LabelCondition {

    @Override
    public boolean matches(SignedFormulaList lfl) {
        LabelledFormula main = (LabelledFormula) lfl.get(0);
        LabelledFormula aux = (LabelledFormula) lfl.get(1);
        
        // main.label <= aux.label (ci <= cj)
        boolean result = main.getLabel().lowerOrEqualThan(aux.getLabel());
        return result;
    }

}
