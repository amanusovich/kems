package logicalSystems.ipl;

import logic.formulas.Formula;
import logic.formulas.FormulaFactory;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.labelledFormulas.LabelledFormulaFactory;
import logic.labelledFormulas.FormulaLabel;
import logic.signedFormulas.FormulaSign;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaFactory;
import java.util.Set;
import java.util.ArrayList;
import java.util.List;

/**
 * Factory specialized for IPL that correctly manages Context and LabelledFormula.
 * Guarantees that every IPL formula has the correct labels and order relations.
 */
public class IPLSignedFormulaFactory extends LabelledFormulaFactory {

    private Context context;

    public IPLSignedFormulaFactory() {
        super();
        this.context = new Context();
    }

    public IPLSignedFormulaFactory(Context context) {
        super();
        this.context = context;
    }

    /**
     * Creates a LabelledFormula with automatic Context handling
     */
    public LabelledFormula createLabelledFormula(FormulaSign aSign, Formula aFormula) {
        // Create a new label using the Context
        FormulaLabel label = context.getNewFormulaLabel();
        SignedFormula sf = super.createSignedFormula(aSign, aFormula);
        return new LabelledFormula(label, sf);
    }

    /**
     * Overrides the superclass method to use our Context
     */
    @Override
    public LabelledFormula createLabelledFormula(Context aContext, SignedFormula aSignedFormula) {
        // Ignore the given context and use ours instead
        return new LabelledFormula(context.getNewFormulaLabel(), aSignedFormula);
    }

    /**
     * Overrides to preserve the existing label if it is a ContextFormulaLabel,
     * otherwise creates a new ContextFormulaLabel
     */
    @Override
    public LabelledFormula createLabelledFormula(SignedFormula aSignedFormula) {
        if (aSignedFormula.getLabel() != null && aSignedFormula.getLabel() instanceof ContextFormulaLabel) {
            // Preserve the existing ContextFormulaLabel
            return new LabelledFormula(aSignedFormula.getLabel(), aSignedFormula);
        } else {
            // Create a new ContextFormulaLabel using our Context
            return new LabelledFormula(context.getNewFormulaLabel(), aSignedFormula);
        }
    }

    /**
     * Overrides to ensure a ContextFormulaLabel is always used
     */
    @Override
    public LabelledFormula createLabelledFormula(FormulaLabel aFormulaLabel, SignedFormula aSignedFormula) {
        if (aFormulaLabel instanceof ContextFormulaLabel) {
            return new LabelledFormula(aFormulaLabel, aSignedFormula);
        } else {
            // Convert a plain FormulaLabel to a ContextFormulaLabel
            ContextFormulaLabel contextLabel = new ContextFormulaLabel(context, aFormulaLabel.getIndex());
            context.addElement(contextLabel);

            // Create a new SignedFormula with the ContextFormulaLabel
            SignedFormula newSignedFormula = super.createSignedFormula(
                aSignedFormula.getSign(),
                aSignedFormula.getFormula(),
                contextLabel
            );

            return new LabelledFormula(contextLabel, newSignedFormula);
        }
    }

    /**
     * Creates a LabelledFormula whose label must be greater than another one
     */
    public LabelledFormula createLabelledFormulaGreaterThan(FormulaLabel baseLabel, FormulaSign aSign, Formula aFormula) {
        FormulaLabel newLabel = context.getNewFormulaLabelGreaterThan(baseLabel);
        SignedFormula sf = super.createSignedFormula(aSign, aFormula);
        return new LabelledFormula(newLabel, sf);
    }

    /**
     * Returns the Context used by this factory
     */
    public Context getContext() {
        return context;
    }

    /**
     * Checks whether two labels are comparable in the partial order
     */
    public boolean areLabelsComparable(FormulaLabel label1, FormulaLabel label2) {
        return context.areComparable(label1, label2);
    }

    /**
     * Checks whether label1 <= label2
     */
    public boolean isLowerOrEqual(FormulaLabel label1, FormulaLabel label2) {
        return context.isLowerOrEqualTo(label1, label2);
    }

    /**
     * IPL-specific implementation of cloneAll.
     * Automatically converts every formula to use ContextFormulaLabel and
     * registers them in the shared Context.
     */
    @Override
    public void cloneAll(SignedFormulaFactory sourceFactory, FormulaFactory ff) {
        // Get every key from the formulas in the source factory
        Set<String> keys = sourceFactory.getSignedFormulas().keySet();
        List<String> keyList = new ArrayList<String>(keys);

        for (String key : keyList) {
            // Check whether it already exists in our factory
            if (!this.getSignedFormulas().containsKey(key)) {
                SignedFormula originalFormula = sourceFactory.getSignedFormulas().get(key);

                // Convert it to IPL with ContextFormulaLabel
                LabelledFormula iplFormula = convertToIPLFormula(originalFormula, ff);

                // Add it to our factory
                this.getSignedFormulas().put(key, iplFormula);
            }
        }
    }

    /**
     * Converts a plain SignedFormula to an IPL LabelledFormula with ContextFormulaLabel
     */
    private LabelledFormula convertToIPLFormula(SignedFormula originalFormula, FormulaFactory ff) {
        FormulaLabel originalLabel = originalFormula.getLabel();

        // Determine the label's index
        int labelIndex;
        if (originalLabel == null || originalLabel.isEmpty()) {
            // No original label, create a new one
            labelIndex = context.getLabels().size();
        } else {
            // Preserve the original index
            labelIndex = originalLabel.getIndex();
        }

        // Create the equivalent ContextFormulaLabel
        ContextFormulaLabel contextLabel = new ContextFormulaLabel(context, labelIndex);

        // Register it in the Context
        if (!context.getLabels().contains(contextLabel)) {
            context.addElement(contextLabel);
        }

        // Clone the formula using FormulaFactory
        Formula clonedFormula = originalFormula.getFormula().clone(ff);

        // Create a new SignedFormula with the ContextFormulaLabel
        SignedFormula newSignedFormula = super.createSignedFormula(
            originalFormula.getSign(),
            clonedFormula,
            contextLabel
        );

        // Build the final LabelledFormula
        LabelledFormula result = new LabelledFormula(contextLabel, newSignedFormula);

        // The last-added-formula record is updated automatically when we add
        // the formula to the map in cloneAll

        return result;
    }
}
