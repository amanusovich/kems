package logicalSystems.ipl;

import logic.formulas.Formula;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.labelledFormulas.LabelledFormulaFactory;
import logic.labelledFormulas.FormulaLabel;
import logic.signedFormulas.FormulaSign;
import logic.signedFormulas.SignedFormula;

/**
 * Factory especializada para IPL que maneja correctamente Context y LabelledFormula.
 * Garantiza que todas las fórmulas IPL tengan las etiquetas y relaciones de orden correctas.
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
     * Crea una LabelledFormula con manejo automático de Context
     */
    public LabelledFormula createLabelledFormula(FormulaSign aSign, Formula aFormula) {
        // Crear nueva etiqueta usando el Context
        FormulaLabel label = context.getNewFormulaLabel();
        SignedFormula sf = super.createSignedFormula(aSign, aFormula);
        return new LabelledFormula(label, sf);
    }
    
    /**
     * Sobrescribe el método de la superclase para usar nuestro Context
     */
    @Override
    public LabelledFormula createLabelledFormula(Context aContext, SignedFormula aSignedFormula) {
        // Ignorar el context pasado y usar el nuestro
        return new LabelledFormula(context.getNewFormulaLabel(), aSignedFormula);
    }
    
    /**
     * Sobrescribe para preservar la etiqueta existente si es ContextFormulaLabel,
     * de lo contrario crear una nueva ContextFormulaLabel
     */
    @Override
    public LabelledFormula createLabelledFormula(SignedFormula aSignedFormula) {
        if (aSignedFormula.getLabel() != null && aSignedFormula.getLabel() instanceof ContextFormulaLabel) {
            // Preservar la ContextFormulaLabel existente
            return new LabelledFormula(aSignedFormula.getLabel(), aSignedFormula);
        } else {
            // Crear nueva ContextFormulaLabel usando nuestro Context
            return new LabelledFormula(context.getNewFormulaLabel(), aSignedFormula);
        }
    }
    
    /**
     * Sobrescribe para asegurar que siempre se use ContextFormulaLabel
     */
    @Override
    public LabelledFormula createLabelledFormula(FormulaLabel aFormulaLabel, SignedFormula aSignedFormula) {
        if (aFormulaLabel instanceof ContextFormulaLabel) {
            return new LabelledFormula(aFormulaLabel, aSignedFormula);
        } else {
            // Convertir FormulaLabel simple a ContextFormulaLabel
            ContextFormulaLabel contextLabel = new ContextFormulaLabel(context, aFormulaLabel.getIndex());
            context.addElement(contextLabel);
            
            // ✅ IMPORTANTE: Crear nuevo SignedFormula con ContextFormulaLabel
            SignedFormula newSignedFormula = super.createSignedFormula(
                aSignedFormula.getSign(), 
                aSignedFormula.getFormula(), 
                contextLabel
            );
            
            return new LabelledFormula(contextLabel, newSignedFormula);
        }
    }
    
    /**
     * Crea una LabelledFormula con etiqueta que debe ser mayor que otra
     */
    public LabelledFormula createLabelledFormulaGreaterThan(FormulaLabel baseLabel, FormulaSign aSign, Formula aFormula) {
        FormulaLabel newLabel = context.getNewFormulaLabelGreaterThan(baseLabel);
        SignedFormula sf = super.createSignedFormula(aSign, aFormula);
        return new LabelledFormula(newLabel, sf);
    }
    
    /**
     * Obtiene el Context usado por esta factory
     */
    public Context getContext() {
        return context;
    }
    
    /**
     * Verifica si dos etiquetas son comparables en el orden parcial
     */
    public boolean areLabelsComparable(FormulaLabel label1, FormulaLabel label2) {
        return context.areComparable(label1, label2);
    }
    
    /**
     * Verifica si label1 ≤ label2
     */
    public boolean isLowerOrEqual(FormulaLabel label1, FormulaLabel label2) {
        return context.isLowerOrEqualTo(label1, label2);
    }
}