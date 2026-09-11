package rules.structures;

import java.util.List;

import logic.formulas.Connective;
import logic.signedFormulas.FormulaSign;
import rules.NullRule;
import rules.Rule;

public class IPLOnePremiseRuleList extends OnePremiseRuleList {

    private SignConnectiveRuleMultiMap connRules;

    public IPLOnePremiseRuleList() {
        connRules = new SignConnectiveRuleMultiMap();
    }
    
    
    public void add(FormulaSign sign, Connective conn, Rule rule) {
        add(rule);
        connRules.put(sign, conn, rule);
        
    }
    
    @Override
    public Rule get(FormulaSign fs, Connective conn) {
        // Use connRules instead of parent's _onePremiseRules
        List<Rule> rulesList = connRules.get(fs, conn);
        if (rulesList != null && !rulesList.isEmpty()) {
            return rulesList.get(0); // Return first rule
        }
        return NullRule.INSTANCE;
    }
    
    public List<Rule> getMany(Connective conn, FormulaSign sign) {
        return connRules.get(sign, conn);
    }
}
