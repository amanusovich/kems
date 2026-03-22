package rules.ipl.labels;

import java.util.List;
import java.util.stream.Collectors;

import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.signedFormulas.SignedFormulaList;

public class NewLabelGetter extends LabelGetter {

	public static final String MAIN = "MAIN";
	public static final String AUX = "AUX";
	public static final String BOTH = "BOTH";
	public static final String GLOBAL_NEW = "GLOBAL_NEW";
	

	private String getterType;
	private FormulaLabel computedLabel = null;
	
	// Constructor
	public NewLabelGetter(String getterType) {
		this.getterType = getterType;
	}

	public NewLabelGetter() { 
		this.getterType = "MAIN";
	}

		@Override
	public FormulaLabel getLabel(SignedFormulaList lfl) {
		//if (this.computedLabel != null)
		//    return this.computedLabel;
	
		if ("MAIN".equals(this.getterType)) {
			this.computedLabel = lfl.get(0).getLabel().getGreaterFormulaLabel();
			return this.computedLabel;
		} else if ("AUX".equals(this.getterType)) {
			return lfl.get(1).getLabel().getGreaterFormulaLabel();
		} else if ("GLOBAL_NEW".equals(this.getterType)) {
			// Generar una nueva etiqueta mayor que TODAS las existentes en el contexto
			FormulaLabel anyLabel = lfl.get(0).getLabel();
			if (anyLabel instanceof ContextFormulaLabel) {
				Context context = ((ContextFormulaLabel) anyLabel).getContext();
				return context.getNewFormulaLabelGreaterThanCollection(context.getLabels());
			} else {
				// Fallback: crear un nuevo Context y convertir todas las labels existentes
				Context newContext = new Context();
				for (int i = 0; i < lfl.size(); i++) {
					FormulaLabel label = lfl.get(i).getLabel();
					ContextFormulaLabel contextLabel = new ContextFormulaLabel(newContext, label.getIndex());
					newContext.addElement(contextLabel);
				}
				// Generar una nueva etiqueta mayor que todas
				return newContext.getNewFormulaLabelGreaterThanCollection(newContext.getLabels());
			}
		} else if ("BOTH".equals(this.getterType)) {
			// map labelled formula list to a collection of formula labels
			List<FormulaLabel> labels = lfl.getList().stream().map(lf -> lf.getLabel()).collect(Collectors.toList());
			
			if (labels.get(0) instanceof ContextFormulaLabel) {
				// we should do something about this cast
				return ((ContextFormulaLabel)lfl.get(0).getLabel()).getContext().getNewFormulaLabelGreaterThanCollection(labels);
			} else {
				// get max index in labels list
				int maxIndex = labels.stream().mapToInt(l -> l.getIndex()).max().getAsInt();
				return new FormulaLabel(FormulaLabel.LabelType.CONSTANT, maxIndex + 1);

			}
		} else {
			return null;
		}

	}

}
