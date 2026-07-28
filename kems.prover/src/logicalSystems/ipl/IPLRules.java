/*
 * Created on 03/12/2004
 *
 */
package logicalSystems.ipl;

import rules.ActionType;
import rules.KERuleRole;
import rules.NamedRule;
import rules.getters.BinaryTwoPremisesConnectiveGetter;
import rules.getters.UnaryConnectiveGetter;
import rules.ipl.KELabelledAction;
import rules.ipl.SimpleSubformulaRoleGetter;
import rules.ipl.labels.GreaterBinaryRelationLabelCondition;
import rules.ipl.labels.GreaterThanLabelCondition;
import rules.ipl.labels.LessThanLabelCondition;
import rules.ipl.labels.LabelGetter;
import rules.ipl.labels.MinimalGreaterLabelGetter;
import rules.ipl.labels.NewLabelGetter;

/**
 * Rules (and patterns for these rules) for IPL.
 */
public class IPLRules {

	/** Rule for PB */
	public static final NamedRule PB = new NamedRule("PB");

	/** Rule for closing branches */
	public static final NamedRule CLOSE = new NamedRule("CLOSE");

	/**
	Rule (F∨) - F-Disjunction
	F A∨B : ci
	---------
	F A: ci
	F B : ci
	*/
	public static final rules.ipl.OnePremiseTwoConclusionsRule F_OR = new rules.ipl.OnePremiseTwoConclusionsRule(
			"F_OR",
			new rules.patterns.ipl.SignConnectivePattern(IPLSigns.FALSE, IPLConnectives.OR),
			new KELabelledAction(ActionType.ADD_NODE, rules.ipl.BinaryConnectiveGetter.FALSE_LEFT, LabelGetter.MAIN),
			new KELabelledAction(ActionType.ADD_NODE, rules.ipl.BinaryConnectiveGetter.FALSE_RIGHT, LabelGetter.MAIN));

	/**
	Rule (T∧) - T-Conjunction
	T A∧B : ci
	---------
	T A: ci
	T B : ci
	*/
	public static final rules.ipl.OnePremiseTwoConclusionsRule T_AND = new rules.ipl.OnePremiseTwoConclusionsRule(
		"T_AND",
		new rules.patterns.ipl.SignConnectivePattern(IPLSigns.TRUE, IPLConnectives.AND),
		new rules.ipl.KELabelledAction(
				ActionType.ADD_NODE, rules.ipl.BinaryConnectiveGetter.TRUE_LEFT, LabelGetter.MAIN),
		new rules.ipl.KELabelledAction(
				ActionType.ADD_NODE, rules.ipl.BinaryConnectiveGetter.TRUE_RIGHT, LabelGetter.MAIN));

    /**
    Rule (F ∧1):
    F A∧B : cj
    T B : ci
    ci ⪯ cj
    ----------
    F A : cj

    Used with PB: if T B does not exist, PB generates it and this rule then applies
    */
    public static final rules.ipl.TwoPremisesOneConclusionRule F_AND_RIGHT = new rules.ipl.TwoPremisesOneConclusionRule(
            "F_AND_RIGHT",
            new rules.patterns.ipl.TwoSignsConnectiveRolePattern(
                    IPLSigns.FALSE,     // main sign
                    IPLConnectives.AND, // main connective
                    IPLSigns.TRUE,      // aux sign
                    KERuleRole.RIGHT,   // aux role (T B is the right subformula)
                    new GreaterThanLabelCondition() // ci ⪯ cj
            ),
            new KELabelledAction(
                    ActionType.ADD_NODE,
                    BinaryTwoPremisesConnectiveGetter.FALSE_OTHER, // F A (the other subformula)
                    LabelGetter.MAIN // uses the label of the major premise (cj)
            ));

    /**
    Rule (T→₁) - T-Implication (Modus Ponens)
    T A→B : ci
    T A : cj
    ci ⪯ ck and cj ⪯ ck
    -----------------
    T B : ck
    */
    static final rules.patterns.ipl.SignConnectiveRoleSubformulaPattern pattern_X_IMPLIES_T_LEFT = new rules.patterns.ipl.SignConnectiveRoleSubformulaPattern(
            IPLConnectives.IMPLIES,
            IPLSigns.TRUE,
            KERuleRole.LEFT,
            new GreaterBinaryRelationLabelCondition());

    public static final rules.ipl.TwoPremisesOneConclusionRule T_IMPLIES_LEFT = new rules.ipl.TwoPremisesOneConclusionRule(
        "T_IMPLIES_LEFT",
        new rules.patterns.ipl.TwoSignsConnectiveRolePattern(
                IPLSigns.TRUE,
                IPLConnectives.IMPLIES,
                IPLSigns.TRUE,
                KERuleRole.LEFT,
                new GreaterBinaryRelationLabelCondition()), // Verify there exists ck such that ci <= ck and cj <= ck
        new KELabelledAction(ActionType.ADD_NODE,
                new rules.ipl.SubformulaRoleGetter(pattern_X_IMPLIES_T_LEFT, KERuleRole.RIGHT),
                new MinimalGreaterLabelGetter()
            )
    );


    /**
    Rule (T→₂) - T-Implication (Modus Tollens)
    T A→B : ci
    F B : cj
    ci ⪯ cj
    -----------------
    F A : cj
    */
    static final rules.patterns.ipl.SignConnectiveRoleSubformulaPattern pattern_X_IMPLIES_F_RIGHT = new rules.patterns.ipl.SignConnectiveRoleSubformulaPattern(
        IPLConnectives.IMPLIES,
        IPLSigns.FALSE,
        KERuleRole.RIGHT,
        new LessThanLabelCondition());

    public static final rules.ipl.TwoPremisesOneConclusionRule X_IMPLIES_F_RIGHT = new rules.ipl.TwoPremisesOneConclusionRule(
        "X_IMPLIES_F_RIGHT",
        pattern_X_IMPLIES_F_RIGHT,
        new KELabelledAction(
            ActionType.ADD_NODE,
            new rules.ipl.SubformulaRoleGetter(pattern_X_IMPLIES_F_RIGHT, KERuleRole.LEFT, IPLSigns.FALSE),
            LabelGetter.AUX
        )
    );

    /**
    Rule (F→₃) - F-Implication with existing T A
    F A→B : cj
    T A : ci
    ci ⪯ cj
    -----------------
    F B : cj

    This rule allows using an existing T A : ci (with ci ⪯ cj)
    to derive F B : cj without creating a new label.
    */
    public static final rules.ipl.TwoPremisesOneConclusionRule F_IMPLIES_T_LEFT = new rules.ipl.TwoPremisesOneConclusionRule(
        "F_IMPLIES_T_LEFT",
        new rules.patterns.ipl.TwoSignsConnectiveRolePattern(
            IPLSigns.FALSE,     // main sign (F A→B : cj)
            IPLConnectives.IMPLIES, // main connective
            IPLSigns.TRUE,      // aux sign (T A : ci)
            KERuleRole.LEFT,    // aux role (A is the left subformula)
            new GreaterThanLabelCondition() // ci ⪯ cj, i.e. aux <= main
        ),
        new KELabelledAction(
            ActionType.ADD_NODE,
            BinaryTwoPremisesConnectiveGetter.FALSE_OTHER, // F B (the other subformula)
            LabelGetter.MAIN // uses the label of the major premise (cj)
        ));

    /**
    Rule (F→) - F-Implication
    F A→B: ci
    ----------------- cj new
    T A : cj
    F B: cj
    ci ⪯ cj
    */
    public static final rules.ipl.OnePremiseTwoConclusionsRule F_A_IMPLIES_B_TA_FB =
    	new rules.ipl.OnePremiseTwoConclusionsLabelOverrideRule(
	        "F_A_IMPLIES_B_TA_FB",
	        new rules.patterns.ipl.SignConnectivePattern(IPLSigns.FALSE, IPLConnectives.IMPLIES),
	        new KELabelledAction(
	            ActionType.ADD_NODE,
	            new SimpleSubformulaRoleGetter(KERuleRole.LEFT, IPLSigns.TRUE),
	            LabelGetter.NEW
	        ),                     // NEW creates a label greater than ci (the premise)
	        new KELabelledAction( // without establishing relations with every label in the context
	            ActionType.ADD_NODE,
	            new SimpleSubformulaRoleGetter(KERuleRole.RIGHT, IPLSigns.FALSE),
	            LabelGetter.NEW
	        ),
	        LabelGetter.NEW  // Use NEW so both conclusions share the same new label
    );

	/**
	 Rule (T¬) - T-Negation
	 T ¬A : ci
	 ci ⪯ cj
	 -----------------
	 F A : cj
	 For any cj such that ci <= cj
	 */
	public static final rules.Rule T_NOT = new rules.ipl.OnePremiseOneConclusionRule(
		"T_NOT",
		new rules.patterns.ipl.SignConnectivePattern(
				IPLSigns.TRUE,
				IPLConnectives.NOT),
		new KELabelledAction(
				ActionType.ADD_NODE,
				UnaryConnectiveGetter.FALSE,
				// cj such that ci ⪯ cj (not necessarily new)
				new MinimalGreaterLabelGetter()));


    /**
    Rule (F¬) - F-Negation
    F ¬A : ci
    ----------------- cj new
    T A : cj
    ci ⪯ cj
    Condition: cj must be a new constant
    */
	public static final rules.Rule F_NOT = new rules.ipl.OnePremiseOneConclusionRule(
		"F_NOT",
		new rules.patterns.ipl.SignConnectivePattern(
				IPLSigns.FALSE,
				IPLConnectives.NOT),
		new KELabelledAction(
				ActionType.ADD_NODE,
				UnaryConnectiveGetter.TRUE,
				// new cj such that ci ⪯ cj
				new NewLabelGetter("MAIN")));

	/**
	Rule (T∨₁) - T-Disjunction 1
	T A∨B : ci
	F A : cj
	ci ⪯ cj
	----------
	T B : ci
	*/
	public static final rules.ipl.TwoPremisesOneConclusionRule T_OR_F_LEFT = new rules.ipl.TwoPremisesOneConclusionRule(
		"T_OR_F_LEFT",
		new rules.patterns.ipl.TwoSignsConnectiveRolePattern(
			IPLSigns.TRUE,     // main sign (T A∨B : ci)
			IPLConnectives.OR, // main connective
			IPLSigns.FALSE,    // aux sign (F A : cj)
			KERuleRole.LEFT,   // aux role (A is the left subformula)
			new LessThanLabelCondition() // ci ⪯ cj (main <= aux)
		),
		new KELabelledAction(
			ActionType.ADD_NODE,
			BinaryTwoPremisesConnectiveGetter.TRUE_OTHER, // T B (the other subformula)
			LabelGetter.MAIN // uses the label of the major premise (ci)
		));

	/**
	Rule (T∨₂) - T-Disjunction 2
	T A∨B : ci
	F B : cj
	ci ⪯ cj
	----------
	T A : ci
	*/
	public static final rules.ipl.TwoPremisesOneConclusionRule T_OR_F_RIGHT = new rules.ipl.TwoPremisesOneConclusionRule(
		"T_OR_F_RIGHT",
		new rules.patterns.ipl.TwoSignsConnectiveRolePattern(
			IPLSigns.TRUE,     // main sign (T A∨B : ci)
			IPLConnectives.OR, // main connective
			IPLSigns.FALSE,    // aux sign (F B : cj)
			KERuleRole.RIGHT,  // aux role (B is the right subformula)
			new LessThanLabelCondition() // ci ⪯ cj (main <= aux)
		),
		new KELabelledAction(
			ActionType.ADD_NODE,
			BinaryTwoPremisesConnectiveGetter.TRUE_OTHER, // T A (the other subformula)
			LabelGetter.MAIN // uses the label of the major premise (ci)
		));

	/**
	Rule (F∧₁) - F-Conjunction 1
	F A∧B : cj
	T A : ci
	ci ⪯ cj
	----------
	F B : cj
	*/
	public static final rules.ipl.TwoPremisesOneConclusionRule F_AND_LEFT = new rules.ipl.TwoPremisesOneConclusionRule(
		"F_AND_LEFT",
		new rules.patterns.ipl.TwoSignsConnectiveRolePattern(
			IPLSigns.FALSE,    // main sign (F A∧B : cj)
			IPLConnectives.AND, // main connective
			IPLSigns.TRUE,     // aux sign (T A : ci)
			KERuleRole.LEFT,   // aux role (A is the left subformula)
			new GreaterThanLabelCondition() // ci ⪯ cj, i.e. aux <= main
		),
		new KELabelledAction(
			ActionType.ADD_NODE,
			BinaryTwoPremisesConnectiveGetter.FALSE_OTHER, // F B (the other subformula)
			LabelGetter.MAIN // uses the label of the major premise (cj)
		));
}
