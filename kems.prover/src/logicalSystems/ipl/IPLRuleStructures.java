/*
 * Created on 14/12/2004
 *
 */
package logicalSystems.ipl;

import logic.formulas.Connective;
import logic.logicalSystem.ISignature;
import logic.signedFormulas.FormulaSign;
import rules.KERuleRole;
import rules.Rule;
import rules.ipl.TwoPremisesOneConclusionRule;
import rules.structures.ConnectiveRoleSignRuleList;
import rules.structures.ConnectiveRuleStructureFactory;
import rules.structures.IPLConnectiveRoleSignRuleList;
import rules.structures.IPLOnePremiseRuleList;
import rules.structures.PBRuleList;
import rules.structures.RuleList;
import rules.structures.RuleType;
import rules.structures.RulesStructure;
import rules.structures.TopBottomRoleRuleList;

/**
 * Structures of rules for IPL KE with substitution
 */

public class IPLRuleStructures {

    private ISignature signature;

    private RulesStructure _rules;

    private IPLOnePremiseRuleList onePremiseRules;

    private TopBottomRoleRuleList topAndBottomRulesNew;

    private IPLConnectiveRoleSignRuleList twoPremiseRules;

    private PBRuleList PBRules;

    private ConnectiveRuleStructureFactory crsf = new ConnectiveRuleStructureFactory();

    public static final String ONE_PREMISE_RULE_LIST = "onePremiseRules";

    public static final String TOP_BOTTOM_ONE_PREMISE_RULE_LIST = "topAndBottomRulesNew";

    public static final String TWO_PREMISE_RULE_LIST = "twoPremiseRules";

    public static final String PB_RULE_LIST = "PBRules";

    public IPLRuleStructures(ISignature signature) {
        this.signature = signature;
        /** one premise rules */
        onePremiseRules = initializeOnePremiseRuleList();
        /** one premise simplification rules */
        topAndBottomRulesNew = new TopBottomRoleRuleList(); // Inicializar vacía por ahora
        //topAndBottomRulesNew = initializeTBRuleList();
        /** Two premise substitution rules */
        twoPremiseRules = initializeTwoPremiseRuleList();
        /** rules for applying PB */
        PBRules = initializePBRuleList();
        /** Order od the sets of rules */
        // the order is important!
        _rules = new RulesStructure();
        _rules.add(ONE_PREMISE_RULE_LIST, onePremiseRules);
        _rules.add(TOP_BOTTOM_ONE_PREMISE_RULE_LIST, topAndBottomRulesNew);
        _rules.add(TWO_PREMISE_RULE_LIST, twoPremiseRules);
        _rules.add(PB_RULE_LIST, PBRules);
    }

    public RulesStructure getRuleStructure() {
        return _rules;
    }

    public RuleList getRules(Connective conn) {
        return crsf.createCRS(conn).getRules();
    }

    /**
     * PB Rules: Usado solo cuando las reglas operacionales no pueden aplicarse.
     * Según el nuevo conjunto de reglas simplificado, PB se usa para:
     * - F A∧B (no tiene regla operacional)
     * - T A∨B (no tiene regla operacional)
     * - T A→B cuando falta la premisa menor (T A)
     * 
     * NOTA: El conjunto simplificado NO incluye reglas de 2 premisas para F∧ y T∨,
     * por lo que PB es la única forma de procesarlas.
     */
    private PBRuleList initializePBRuleList() {
        PBRules = new PBRuleList();

        // PB para T A→B cuando no hay T A disponible (para T_IMPLIES_LEFT)
        addToPBRules(IPLSigns.TRUE, IPLConnectives.IMPLIES,
                IPLRules.T_IMPLIES_LEFT);
        
        // NOTA: F A∧B y T A∨B NO tienen reglas operacionales en el nuevo conjunto,
        // pero PB se maneja dinámicamente en IPLPBRuleApplicator sin necesidad de registro aquí.

        return PBRules;
    }

    private IPLConnectiveRoleSignRuleList initializeTwoPremiseRuleList() {
        twoPremiseRules = new IPLConnectiveRoleSignRuleList();

        // Reglas que usan PB cuando falta premisa menor:
        
        // F A∧B : cj, T B : ci (ci ≤ cj) → F A : cj
        // PB genera T B si no existe, luego aplica esta regla
        addToTwoPremiseRules(IPLConnectives.AND, KERuleRole.RIGHT,
                IPLSigns.FALSE, IPLRules.F_AND_RIGHT);
        
        // F A∧B : cj, T A : ci (ci ≤ cj) → F B : cj
        addToTwoPremiseRules(IPLConnectives.AND, KERuleRole.LEFT,
                IPLSigns.FALSE, IPLRules.F_AND_LEFT);
        
        // (T→₁) - T-Implicación (Modus Ponens)
        // T A→B : ci, T A : cj, ci ⪯ ck and cj ⪯ ck → T B : ck
        addToTwoPremiseRules(IPLConnectives.IMPLIES, KERuleRole.LEFT,
                IPLSigns.TRUE, IPLRules.T_IMPLIES_LEFT);
        
        // (T→₂) - T-Implicación (Modus Tollens)
        // T A→B : ci, F B : cj, ci ⪯ cj → F A : cj
        addToTwoPremiseRules(IPLConnectives.IMPLIES, KERuleRole.RIGHT,
                IPLSigns.TRUE, IPLRules.X_IMPLIES_F_RIGHT);
        
        // (F→₃) - F-Implicación con T A existente
        // F A→B : cj, T A : ci, ci ⪯ cj → F B : cj
        addToTwoPremiseRules(IPLConnectives.IMPLIES, KERuleRole.LEFT,
                IPLSigns.FALSE, IPLRules.F_IMPLIES_T_LEFT);
        
        // (T∨₁) - T A∨B : ci, F A : cj, ci ⪯ cj → T B : ci
        addToTwoPremiseRules(IPLConnectives.OR, KERuleRole.LEFT,
                IPLSigns.TRUE, IPLRules.T_OR_F_LEFT);
        
        // (T∨₂) - T A∨B : ci, F B : cj, ci ⪯ cj → T A : ci
        addToTwoPremiseRules(IPLConnectives.OR, KERuleRole.RIGHT,
                IPLSigns.TRUE, IPLRules.T_OR_F_RIGHT);

        return twoPremiseRules;
    }

  

    /**
     * @return
     */
    private IPLOnePremiseRuleList initializeOnePremiseRuleList() {
        onePremiseRules = new IPLOnePremiseRuleList();

        // Regla 1
        addToOnePremiseRules(IPLSigns.FALSE, IPLConnectives.OR,
                IPLRules.F_OR);

        // Regla 2
        addToOnePremiseRules(IPLSigns.TRUE, IPLConnectives.AND,
                IPLRules.T_AND);


        // Regla 14
        addToOnePremiseRules(IPLSigns.FALSE, IPLConnectives.IMPLIES,
                IPLRules.F_A_IMPLIES_B_TA_FB);
   
        // Regla 10
        addToOnePremiseRules(IPLSigns.TRUE, IPLConnectives.NOT,
                IPLRules.T_NOT);
        // Regla 17
        addToOnePremiseRules(IPLSigns.FALSE, IPLConnectives.NOT,
                IPLRules.F_NOT);
     
        return onePremiseRules;
    }

    private void addToPBRules(FormulaSign sign, Connective conn, Rule r1) {
        if (signature.contains(conn)) {
            addConnectiveRuleType(conn, r1, RuleType.PB);
            PBRules.add(sign, conn, r1);
        }
    }

    protected void addToTwoPremiseRules(Connective conn, KERuleRole role,
            FormulaSign sign, TwoPremisesOneConclusionRule r) {
        if (signature.contains(conn)) {
            addConnectiveRuleType(conn, r, RuleType.SUBSTITUTION_2P);
            twoPremiseRules.add(conn, role, sign, r);
        }
    }



    private void addToOnePremiseRules(FormulaSign sign, Connective conn, Rule r) {
        if (signature.contains(conn)) {
            addConnectiveRuleType(conn, r, RuleType.SIMPLE_1P);
            onePremiseRules.add(sign, conn, r);
        }
    }

    protected void addConnectiveRuleType(Connective conn, Rule r, RuleType rt) {
        crsf.createCRS(conn).add(r, rt);
    }

    public ISignature getSignature() {
        return signature;
    }

    public ConnectiveRoleSignRuleList getTwoPremiseRules() {
        return twoPremiseRules;
    }

    protected void setTwoPremiseRules(ConnectiveRoleSignRuleList list) {
        twoPremiseRules = (IPLConnectiveRoleSignRuleList) list;
    }

}