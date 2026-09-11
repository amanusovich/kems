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
        topAndBottomRulesNew = new TopBottomRoleRuleList(); // Initialize empty for now
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
     * PB Rules: only used when the operational rules cannot be applied.
     * Under the simplified rule set, PB is used for:
     * - F A^B (no operational rule)
     * - T AvB (no operational rule)
     * - T A->B when the minor premise (T A) is missing
     *
     * NOTE: The simplified rule set does NOT include two-premise rules for
     * F^ and Tv, so PB is the only way to process them.
     */
    private PBRuleList initializePBRuleList() {
        PBRules = new PBRuleList();

        // PB for T A->B when no T A is available (for T_IMPLIES_LEFT)
        addToPBRules(IPLSigns.TRUE, IPLConnectives.IMPLIES,
                IPLRules.T_IMPLIES_LEFT);

        // NOTE: F A^B and T AvB have no operational rule in the new rule set,
        // but PB is handled dynamically in IPLPBRuleApplicator with no need to register here.

        return PBRules;
    }

    private IPLConnectiveRoleSignRuleList initializeTwoPremiseRuleList() {
        twoPremiseRules = new IPLConnectiveRoleSignRuleList();

        // Rules that rely on PB when the minor premise is missing:

        // F A^B : cj, T B : ci (ci <= cj) -> F A : cj
        // PB generates T B if it does not exist, then this rule applies
        addToTwoPremiseRules(IPLConnectives.AND, KERuleRole.RIGHT,
                IPLSigns.FALSE, IPLRules.F_AND_RIGHT);

        // F A^B : cj, T A : ci (ci <= cj) -> F B : cj
        addToTwoPremiseRules(IPLConnectives.AND, KERuleRole.LEFT,
                IPLSigns.FALSE, IPLRules.F_AND_LEFT);

        // (T->1) - T-Implication (Modus Ponens)
        // T A->B : ci, T A : cj, ci <= ck and cj <= ck -> T B : ck
        addToTwoPremiseRules(IPLConnectives.IMPLIES, KERuleRole.LEFT,
                IPLSigns.TRUE, IPLRules.T_IMPLIES_LEFT);

        // (T->2) - T-Implication (Modus Tollens)
        // T A->B : ci, F B : cj, ci <= cj -> F A : cj
        addToTwoPremiseRules(IPLConnectives.IMPLIES, KERuleRole.RIGHT,
                IPLSigns.TRUE, IPLRules.X_IMPLIES_F_RIGHT);

        // (F->3) - F-Implication with an existing T A
        // F A->B : cj, T A : ci, ci <= cj -> F B : cj
        addToTwoPremiseRules(IPLConnectives.IMPLIES, KERuleRole.LEFT,
                IPLSigns.FALSE, IPLRules.F_IMPLIES_T_LEFT);

        // (Tv1) - T A v B : ci, F A : cj, ci <= cj -> T B : ci
        addToTwoPremiseRules(IPLConnectives.OR, KERuleRole.LEFT,
                IPLSigns.TRUE, IPLRules.T_OR_F_LEFT);

        // (Tv2) - T A v B : ci, F B : cj, ci <= cj -> T A : ci
        addToTwoPremiseRules(IPLConnectives.OR, KERuleRole.RIGHT,
                IPLSigns.TRUE, IPLRules.T_OR_F_RIGHT);

        return twoPremiseRules;
    }

  

    /**
     * @return
     */
    private IPLOnePremiseRuleList initializeOnePremiseRuleList() {
        onePremiseRules = new IPLOnePremiseRuleList();

        // Rule 1
        addToOnePremiseRules(IPLSigns.FALSE, IPLConnectives.OR,
                IPLRules.F_OR);

        // Rule 2
        addToOnePremiseRules(IPLSigns.TRUE, IPLConnectives.AND,
                IPLRules.T_AND);


        // Rule 14
        addToOnePremiseRules(IPLSigns.FALSE, IPLConnectives.IMPLIES,
                IPLRules.F_A_IMPLIES_B_TA_FB);

        // Rule 10
        addToOnePremiseRules(IPLSigns.TRUE, IPLConnectives.NOT,
                IPLRules.T_NOT);
        // Rule 17
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