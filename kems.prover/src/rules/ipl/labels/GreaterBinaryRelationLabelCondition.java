package rules.ipl.labels;

import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.SignedFormulaList;

import java.util.List;
import java.util.stream.Collectors;

/**
 * This class models the condition that there exists a label ck such that
 * ci <= ck and cj <= cK
 */
public class GreaterBinaryRelationLabelCondition implements LabelCondition {

    @Override
    public boolean matches(SignedFormulaList lfl) {
        LabelledFormula main = (LabelledFormula) lfl.get(0);
        LabelledFormula aux = (LabelledFormula) lfl.get(1);
        Context context = ((ContextFormulaLabel) main.getLabel()).getContext();
        // Find all labels in the context that are >= maxLabel
        List<FormulaLabel> candidateLabels = context.getLabels().stream()
            .filter(label -> context.isGreaterOrEqualTo(label, main.getLabel()) && context.isGreaterOrEqualTo(label, aux.getLabel()))
            .collect(Collectors.toList());
        return !candidateLabels.isEmpty();
    }

}
