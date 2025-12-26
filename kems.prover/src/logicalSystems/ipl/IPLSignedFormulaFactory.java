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
    
    /**
     * Implementación especializada de cloneAll para IPL.
     * Convierte automáticamente todas las fórmulas a usar ContextFormulaLabel
     * y las registra en el Context compartido.
     */
    @Override
    public void cloneAll(SignedFormulaFactory sourceFactory, FormulaFactory ff) {
        System.out.println("🔄 IPL cloneAll: Iniciando conversión de " + sourceFactory.getSize() + " fórmulas");
        
        // Obtener todas las claves de las fórmulas en la factory origen
        Set<String> keys = sourceFactory.getSignedFormulas().keySet();
        List<String> keyList = new ArrayList<String>(keys);
        
        int convertedCount = 0;
        int skippedCount = 0;
        
        for (String key : keyList) {
            // Verificar si ya existe en nuestra factory
            if (!this.getSignedFormulas().containsKey(key)) {
                SignedFormula originalFormula = sourceFactory.getSignedFormulas().get(key);
                
                // Convertir a IPL con ContextFormulaLabel
                LabelledFormula iplFormula = convertToIPLFormula(originalFormula, ff);
                
                // Agregar a nuestra factory
                this.getSignedFormulas().put(key, iplFormula);
                
                convertedCount++;
                System.out.println("✅ IPL cloneAll: " + key + " → " + iplFormula.getLabel().getClass().getSimpleName());
            } else {
                skippedCount++;
                System.out.println("⏭️  IPL cloneAll: Saltando " + key + " (ya existe)");
            }
        }
        
        System.out.println("🎯 IPL cloneAll: Convertidas " + convertedCount + " fórmulas, saltadas " + skippedCount);
        System.out.println("📊 IPL cloneAll: Context ahora tiene " + context.getLabels().size() + " etiquetas");
    }
    
    /**
     * Convierte una SignedFormula normal a LabelledFormula IPL con ContextFormulaLabel
     */
    private LabelledFormula convertToIPLFormula(SignedFormula originalFormula, FormulaFactory ff) {
        FormulaLabel originalLabel = originalFormula.getLabel();
        
        // Determinar el índice de la etiqueta
        int labelIndex;
        if (originalLabel == null || originalLabel.isEmpty()) {
            // Sin etiqueta original, crear nueva
            labelIndex = context.getLabels().size();
        } else {
            // Preservar el índice original
            labelIndex = originalLabel.getIndex();
        }
        
        // Crear ContextFormulaLabel equivalente
        ContextFormulaLabel contextLabel = new ContextFormulaLabel(context, labelIndex);
        
        // Registrar en el Context
        if (!context.getLabels().contains(contextLabel)) {
            context.addElement(contextLabel);
            System.out.println("🏷️  IPL cloneAll: Nueva etiqueta " + contextLabel + " agregada al Context");
        }
        
        // Clonar la fórmula usando FormulaFactory
        Formula clonedFormula = originalFormula.getFormula().clone(ff);
        
        // Crear nueva SignedFormula con ContextFormulaLabel
        SignedFormula newSignedFormula = super.createSignedFormula(
            originalFormula.getSign(),
            clonedFormula,
            contextLabel
        );
        
        // Crear LabelledFormula final
        LabelledFormula result = new LabelledFormula(contextLabel, newSignedFormula);
        
        // Actualizar el registro de última fórmula agregada usando el método público
        // Nota: Esto se actualiza automáticamente cuando agregamos la fórmula al mapa en cloneAll
        
        return result;
    }
}