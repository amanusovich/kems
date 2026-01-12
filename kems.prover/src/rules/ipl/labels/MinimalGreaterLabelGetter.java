package rules.ipl.labels;

import java.util.List;
import java.util.stream.Collectors;

import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.FormulaLabel;
import logic.signedFormulas.SignedFormulaList;

/**
 * LabelGetter que implementa la semántica IPL correcta:
 * Busca la etiqueta mínima existente que sea mayor o igual a ambas premisas.
 * Solo crea una nueva etiqueta si no existe ninguna que cumpla la condición.
 */
public class MinimalGreaterLabelGetter extends LabelGetter {

    @Override
    public FormulaLabel getLabel(SignedFormulaList lfl) {
        if (lfl.size() < 2) {
            // Para reglas de una premisa, usar la etiqueta de la premisa
            return lfl.get(0).getLabel();
        }

        // Obtener etiquetas de ambas premisas
        FormulaLabel label1 = lfl.get(0).getLabel();
        FormulaLabel label2 = lfl.get(1).getLabel();
        
        // Si trabajamos con ContextFormulaLabel, buscar en el contexto
        if (label1 instanceof ContextFormulaLabel) {
            Context context = ((ContextFormulaLabel) label1).getContext();
            return findMinimalGreaterOrEqualLabel(context, label1, label2);
        } else {
            // Sin contexto, usar etiquetas simples basadas en índices
            return findMinimalGreaterOrEqualSimple(label1, label2);
        }
    }
    
    /**
     * Determina cuál de las dos etiquetas es mayor
     */
    private FormulaLabel getMaxLabel(FormulaLabel label1, FormulaLabel label2) {
        // Comparar por índice para etiquetas simples
        if (label1.getIndex() >= label2.getIndex()) {
            return label1;
        } else {
            return label2;
        }
    }
    
    /**
     * Busca la etiqueta mínima existente en el contexto que sea >= ambas premisas.
     * Si no existe ninguna, lanza una excepción porque la regla no debería aplicarse.
     * 
     * IMPORTANTE: Este método asume que la condición de existencia de tal etiqueta
     * ya fue verificada antes de intentar aplicar la regla (por ejemplo, mediante
     * GreaterBinaryRelationLabelCondition). Si no existe, la regla simplemente
     * no se puede aplicar.
     */
    private FormulaLabel findMinimalGreaterOrEqualLabel(Context context, FormulaLabel label1, FormulaLabel label2) {
        // Buscar todas las etiquetas en el contexto que sean >= ambas premisas
        List<FormulaLabel> candidateLabels = context.getLabels().stream()
            .filter(label -> context.isGreaterOrEqualTo(label, label1) && context.isGreaterOrEqualTo(label, label2))
            .collect(Collectors.toList());
        
        if (!candidateLabels.isEmpty()) {
            // Encontrar la mínima entre las candidatas (menor índice)
            FormulaLabel minimalCandidate = candidateLabels.get(0);
            for (FormulaLabel candidate : candidateLabels) {
                if (candidate.getIndex() < minimalCandidate.getIndex()) {
                    minimalCandidate = candidate;
                }
            }
            return minimalCandidate;
        } else {
            // No existe ninguna etiqueta que cumpla la condición
            // Esto significa que la regla NO se puede aplicar
            // La excepción indica que se intentó aplicar una regla cuando no se cumplía la condición
            throw new RuntimeException("No candidate label found - rule condition not satisfied: " + 
                "no label exists that is >= both " + label1 + " and " + label2);
        }
    }
    
    /**
     * Para etiquetas simples sin contexto, usar lógica basada en índices
     */
    private FormulaLabel findMinimalGreaterOrEqualSimple(FormulaLabel label1, FormulaLabel label2) {
        FormulaLabel maxLabel = getMaxLabel(label1, label2);
        
        // En este caso simple, la etiqueta máxima ya es la respuesta correcta
        // porque asumimos que las etiquetas están en orden y la máxima ya es >= ambas
        return maxLabel;
    }
}
