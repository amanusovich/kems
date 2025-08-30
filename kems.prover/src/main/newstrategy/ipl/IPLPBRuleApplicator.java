package main.newstrategy.ipl;

import logic.signedFormulas.SignedFormulaBuilder;
import main.newstrategy.ISimpleStrategy;
import main.strategy.ClassicalProofTree;
import main.strategy.applicator.IProofTransformation;
import rules.structures.PBRuleList;

/**
 * IPL-specific PB Rule Applicator that handles IPL rule types correctly.
 * Since IPL currently has an empty PB rule list and uses IPLTwoPremiseRuleApplicator
 * for two-premise rules, this applicator simply returns false (no application).
 */
public class IPLPBRuleApplicator implements IProofTransformation {

    private ISimpleStrategy strategy;
    private String ruleListName;

    public IPLPBRuleApplicator(ISimpleStrategy strategy, String ruleListName) {
        this.strategy = strategy;
        this.ruleListName = ruleListName;
    }

    @Override
    public boolean apply(ClassicalProofTree current, SignedFormulaBuilder sfb) {
        // Verificar si hay reglas PB específicas para IPL
        Object ruleListObject = strategy.getMethod().getRules().get(ruleListName);
        if (!(ruleListObject instanceof PBRuleList)) {
            // No hay reglas PB para IPL, no hacer nada
            return false;
        }
        
        PBRuleList pbRuleList = (PBRuleList) ruleListObject;
        if (pbRuleList.size() == 0) {
            // Lista PB vacía para IPL, no hacer nada
            return false;
        }
        
        // IPL tiene reglas PB específicas (F_AND_LEFT, T_IMPLIES_LEFT)
        // Estas reglas requieren manejo especial ya que usan clases rules.ipl.*
        try {
            // Por ahora, delegar al sistema de dos premisas que ya maneja estas reglas
            // Las reglas F_AND_LEFT y T_IMPLIES_LEFT ya están siendo manejadas
            // por IPLTwoPremiseRuleApplicator
            return false;
        } catch (Exception e) {
            System.err.println("Error applying IPL PB rules: " + e.getMessage());
            return false;
        }
    }
}
