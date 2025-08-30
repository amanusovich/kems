package logicalSystems.ipl;

import logic.formulas.Formula;
import logic.formulas.CompositeFormula;
import logic.signedFormulas.SignedFormula;

import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.Context;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.strategy.memorySaver.OptimizedClassicalProofTree;

/**
 * ProofTree específico para IPL que implementa las reglas de cierre correctas.
 * 
 * Reglas de cierre IPL:
 * 1) T A: ci, F A: cj, ci ⪯ cj → ×
 * 2) T A: ci, T¬A: cj, ci ⪯ ck and cj ⪯ ck → ×
 * 
 * Basado en el paper: "Free-variable KE tableaux for IPL"
 */
public class IPLProofTree extends OptimizedClassicalProofTree {

    public IPLProofTree(SignedFormulaNode aNode) {
        super(aNode);
    }

    @Override
    protected IProofTree makeInstance(INode aNode) {
        return new IPLProofTree((SignedFormulaNode) aNode);
    }

    @Override
    protected void updateMultimap(SignedFormulaNode aNode) {
        // Para IPL, NO ejecutar la detección clásica, solo usar reglas IPL específicas
        SignedFormula sf = (SignedFormula) aNode.getContent();
        getFsmm().put(sf.getFormula(), sf.getSign());
        
        // Debug: verificar tipo de etiqueta
        FormulaLabel label = sf.getLabel();
        System.out.println("🔄 IPL updateMultimap: " + sf + " (label type: " + label.getClass().getSimpleName() + ")");
        
        // Verificar reglas de cierre IPL
        if (detectIPLContradiction(aNode)) {
            System.out.println("🔴 IPL: CONTRADICTION DETECTED for " + sf);
            setClosingReason(sf);
            setLocallyClosed(true);
        }
    }
    
    /**
     * Detecta contradicciones según las reglas de cierre IPL:
     * 1) T A: ci, F A: cj, ci ⪯ cj → ×
     * 2) T A: ci, T¬A: cj, ci ⪯ ck and cj ⪯ ck → ×
     */
    private boolean detectIPLContradiction(SignedFormulaNode aNode) {
        SignedFormula newSf = (SignedFormula) aNode.getContent();
        FormulaLabel newLabel = newSf.getLabel();
        Formula newFormula = newSf.getFormula();
        Object newSign = newSf.getSign();
        
        System.out.println("🔍 IPL Closure: Checking " + newSign + " " + newFormula + " " + newLabel);
        
        // Obtener el Context para verificar relaciones de orden
        Context context = getContextFromLabel(newLabel);
        if (context == null) {
            System.out.println("⚠️ IPL Closure: No Context found for label " + newLabel);
            return false; // Sin Context, no podemos verificar relaciones de orden
        }
        
        System.out.println("🔍 IPL Closure: Context has " + context.getLabels().size() + " labels: " + context.getLabels());
        
        // Regla 1: T A: ci, F A: cj, ci ⪯ cj → ×
        if (newSign.equals(IPLSigns.TRUE)) {
            SignedFormula oppositeSigned = findFormulaWithSign(newFormula, IPLSigns.FALSE);
            if (oppositeSigned != null) {
                FormulaLabel oppositeLabel = oppositeSigned.getLabel();
                // Verificar si ci ⪯ cj (newLabel ⪯ oppositeLabel)
                if (isLowerOrEqual(context, newLabel, oppositeLabel)) {
                    System.out.println("🔴 IPL Closure Rule 1: T " + newFormula + " " + newLabel + 
                                     ", F " + newFormula + " " + oppositeLabel + 
                                     " with " + newLabel + " ⪯ " + oppositeLabel);
                    return true;
                }
            }
        }
        
        if (newSign.equals(IPLSigns.FALSE)) {
            SignedFormula oppositeSigned = findFormulaWithSign(newFormula, IPLSigns.TRUE);
            if (oppositeSigned != null) {
                FormulaLabel oppositeLabel = oppositeSigned.getLabel();
                // Verificar si ci ⪯ cj (oppositeLabel ⪯ newLabel)
                if (isLowerOrEqual(context, oppositeLabel, newLabel)) {
                    System.out.println("🔴 IPL Closure Rule 1: T " + newFormula + " " + oppositeLabel + 
                                     ", F " + newFormula + " " + newLabel + 
                                     " with " + oppositeLabel + " ⪯ " + newLabel);
                    return true;
                }
            }
        }
        
        // Regla 2: T A: ci, T¬A: cj, ci ⪯ ck and cj ⪯ ck → ×
        if (newSign.equals(IPLSigns.TRUE)) {
            // Caso 2a: Agregamos T A, buscamos T ¬A existente
            SignedFormula negatedSigned = findNegatedFormula(newFormula, IPLSigns.TRUE);
            if (negatedSigned != null) {
                FormulaLabel negatedLabel = negatedSigned.getLabel();
                // Verificar si existe ck tal que ci ⪯ ck y cj ⪯ ck
                if (existsCommonUpperBound(context, newLabel, negatedLabel)) {
                    System.out.println("🔴 IPL Closure Rule 2: T " + newFormula + " " + newLabel + 
                                     ", T¬" + newFormula + " " + negatedLabel + 
                                     " with common upper bound");
                    return true;
                }
            }
            
            // Caso 2b: Agregamos T ¬A, buscamos T A existente
            if (isNegation(newFormula)) {
                Formula innerFormula = getNegatedFormula(newFormula);
                SignedFormula positiveSigned = findFormulaWithSign(innerFormula, IPLSigns.TRUE);
                if (positiveSigned != null) {
                    FormulaLabel positiveLabel = positiveSigned.getLabel();
                    // Verificar si existe ck tal que ci ⪯ ck y cj ⪯ ck
                    if (existsCommonUpperBound(context, positiveLabel, newLabel)) {
                        System.out.println("🔴 IPL Closure Rule 2: T " + innerFormula + " " + positiveLabel + 
                                         ", T¬" + innerFormula + " " + newLabel + 
                                         " with common upper bound");
                        return true;
                    }
                }
            }
        }
        
        return false;
    }
    
    /**
     * Obtiene el Context desde una FormulaLabel (si es ContextFormulaLabel)
     */
    private Context getContextFromLabel(FormulaLabel label) {
        if (label instanceof ContextFormulaLabel) {
            return ((ContextFormulaLabel) label).getContext();
        }
        return null;
    }
    
    /**
     * Verifica si label1 ⪯ label2 en el contexto dado
     */
    private boolean isLowerOrEqual(Context context, FormulaLabel label1, FormulaLabel label2) {
        if (label1.equals(label2)) {
            return true; // Reflexiva: ci ⪯ ci
        }
        return context.isLowerOrEqualTo(label1, label2);
    }
    
    /**
     * Busca una fórmula con signo específico en toda la rama
     */
    private SignedFormula findFormulaWithSign(Formula formula, Object sign) {
        IPLProofTree current = this;
        while (current != null) {
            INode currentNode = current.getRoot();
            while (currentNode != null) {
                SignedFormula sf = (SignedFormula) currentNode.getContent();
                if (sf.getSign().equals(sign) && sf.getFormula().equals(formula)) {
                    return sf;
                }
                currentNode = currentNode.getNext();
            }
            current = (IPLProofTree) current.getParent();
        }
        return null;
    }
    
    /**
     * Busca T ¬formula en toda la rama
     */
    private SignedFormula findNegatedFormula(Formula formula, Object sign) {
        IPLProofTree current = this;
        while (current != null) {
            INode currentNode = current.getRoot();
            while (currentNode != null) {
                SignedFormula sf = (SignedFormula) currentNode.getContent();
                if (sf.getSign().equals(sign) && 
                    isNegation(sf.getFormula()) &&
                    getNegatedFormula(sf.getFormula()).equals(formula)) {
                    return sf;
                }
                currentNode = currentNode.getNext();
            }
            current = (IPLProofTree) current.getParent();
        }
        return null;
    }
    
    /**
     * Verifica si existe un upper bound común para dos etiquetas
     */
    private boolean existsCommonUpperBound(Context context, FormulaLabel label1, FormulaLabel label2) {
        // Para todas las etiquetas en el contexto, verificar si ambas son menores o iguales
        for (FormulaLabel candidate : context.getLabels()) {
            if (isLowerOrEqual(context, label1, candidate) && 
                isLowerOrEqual(context, label2, candidate)) {
                return true;
            }
        }
        return false;
    }
    
    /**
     * Verifica si una fórmula es una negación (¬A)
     */
    private boolean isNegation(Formula formula) {
        return formula instanceof CompositeFormula &&
               ((CompositeFormula) formula).getConnective().equals(IPLConnectives.NOT);
    }
    
    /**
     * Extrae la fórmula interna de una negación: ¬A → A
     */
    private Formula getNegatedFormula(Formula negation) {
        if (!isNegation(negation)) {
            return null;
        }
        
        CompositeFormula comp = (CompositeFormula) negation;
        return comp.getImmediateSubformulas().get(0);
    }
}
