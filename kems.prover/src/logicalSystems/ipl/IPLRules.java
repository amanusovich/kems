/*
 * Created on 03/12/2004
 *
 */
package logicalSystems.ipl;

import rules.ActionType;
import rules.KERuleRole;
import rules.NamedRule;
import rules.getters.BinaryTwoPremisesConnectiveGetter;
import rules.getters.SubformulaRoleGetter;
import rules.getters.UnaryConnectiveGetter;
import rules.ipl.CompositeLabelledAction;
import rules.ipl.KEDecoratedRuleRole;
import rules.ipl.KELabelledAction;
import rules.ipl.SimpleSubformulaRoleGetter;
import rules.ipl.labels.BinarySomeRelationLabelCondition;
import rules.ipl.labels.GreaterBinaryRelationLabelCondition;
import rules.ipl.labels.GreaterThanLabelCondition;
import rules.ipl.labels.LessThanLabelCondition;
import rules.ipl.labels.LabelGetter;
import rules.ipl.labels.MinimalGreaterLabelGetter;
import rules.ipl.labels.MainLabelGetter;
import rules.ipl.labels.NoLabelCondition;
import rules.patterns.ipl.TwoLevelCompositeBinaryFormulaPattern;
import rules.patterns.ipl.TwoLevelCompositeFormulaPattern;

/**
 * Rules (and patterns for these rules) for IPL.
 */
public class IPLRules {

	/** Rule for PB */
	public static final NamedRule PB = new NamedRule("PB");

	/** Rule for closing branches */
	public static final NamedRule CLOSE = new NamedRule("CLOSE");

	/**
	Rule 1
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
	Rule 2
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
	Rule 3
	T A∨B : ci
	F A: cj
	ci ⪯ cj
	----------
	T B : ci
	*/
	static final rules.patterns.ipl.SignConnectiveRoleSubformulaPattern pattern_X_OR_F_LEFT = new rules.patterns.ipl.SignConnectiveRoleSubformulaPattern(
		IPLConnectives.OR, 	// connective that may appear in any subformula of the main formula.
		IPLSigns.FALSE, 	// sign of the auxiliary formula.
		KERuleRole.LEFT,
        new LessThanLabelCondition());	// ci ⪯ cj: main.label ≤ aux.label 
							// where the _mainConnective was found.

	public static final rules.ipl.TwoPremisesOneConclusionRule X_OR_F_LEFT = new rules.ipl.TwoPremisesOneConclusionRule(
			"X_OR_F_LEFT", 
			pattern_X_OR_F_LEFT,
			new KELabelledAction(
				ActionType.ADD_NODE,
				new SubformulaRoleGetter(pattern_X_OR_F_LEFT, KERuleRole.RIGHT),
				LabelGetter.MAIN
			));

	/**
    Rule 4
    T A∨B : ci
    F B: cj
    ci ⪯ cj
    ---------
    T A : ci
     */
	static final rules.patterns.ipl.SignConnectiveRoleSubformulaPattern pattern_X_OR_F_RIGHT = new rules.patterns.ipl.SignConnectiveRoleSubformulaPattern(
			IPLConnectives.OR, 
			IPLSigns.FALSE, 
			KERuleRole.RIGHT,
			new LessThanLabelCondition());	// ci ⪯ cj: main.label ≤ aux.label

	public static final rules.ipl.TwoPremisesOneConclusionRule T_OR_F_RIGHT = new rules.ipl.TwoPremisesOneConclusionRule(
			"X_OR_F_RIGHT", pattern_X_OR_F_RIGHT,
			new KELabelledAction(
				ActionType.ADD_NODE,
				new rules.ipl.SubformulaRoleGetter(pattern_X_OR_F_RIGHT, KERuleRole.LEFT),
				LabelGetter.MAIN
			));

	/**
    Rule 5
	T not(A or B): Ci
	-----------------
	T not A : Ci
	T not B : Ci
	*/
	public static final rules.ipl.OnePremiseTwoConclusionsRule T_NOT_A_OR_B = new rules.ipl.OnePremiseTwoConclusionsRule(
		"T_NOT_A_OR_B",
		new rules.patterns.ipl.TwoLevelCompositeFormulaPattern(IPLConnectives.NOT, IPLConnectives.OR),
		new KELabelledAction(
			ActionType.ADD_NODE,
			//new NotSubformulaGetter(KERuleRole.LEFT, IPLSigns.TRUE),
			new CompositeLabelledAction(IPLConnectives.NOT, new NotSubformulaGetter(KERuleRole.LEFT, IPLSigns.TRUE)),
			LabelGetter.MAIN
		),
		new KELabelledAction(
			ActionType.ADD_NODE,
			new CompositeLabelledAction(IPLConnectives.NOT, new NotSubformulaGetter(KERuleRole.RIGHT, IPLSigns.TRUE)),
			//new NotSubformulaGetter(KERuleRole.RIGHT, IPLSigns.TRUE),
			LabelGetter.MAIN
		)
	);
	
	/**
	Rule 6
	T A or B: Ci
	T not A : Cj
	Ci <= Cj or Cj <= Ci
	-----------------
	T B : Ci
	*/
	static final rules.patterns.ipl.SignConnectiveRoleSubformulaPattern pattern_T_A_OR_B = new rules.patterns.ipl.SignConnectiveRoleSubformulaPattern(
			IPLConnectives.OR, 	// connective that may appear in any subformula of the main formula.
			IPLSigns.TRUE, 	// sign of the auxiliary formula.
			new KEDecoratedRuleRole("Left", IPLConnectives.NOT),   // role of the auxiliary formula in the subformula of the main formula 
			                                                       // where the _mainConnective was found.
			new BinarySomeRelationLabelCondition());	
								

	public static final rules.ipl.TwoPremisesOneConclusionRule T_A_OR_B = new rules.ipl.TwoPremisesOneConclusionRule(
		"T_A_OR_B",
		pattern_T_A_OR_B,
		new KELabelledAction(
			ActionType.ADD_NODE,
			new rules.ipl.SubformulaRoleGetter(pattern_T_A_OR_B, KERuleRole.RIGHT),
			LabelGetter.MAIN
		)
	);
	
    /**
     * Regla 7
     * T A or B : ci
     * T not B: cj
     * ci <= cj or cj <= ci
     * --------------------
     * T A: ci
     */
    static final rules.patterns.ipl.SignConnectiveRoleSubformulaPattern pattern_T_A_OR_B_NOT_B = new rules.patterns.ipl.SignConnectiveRoleSubformulaPattern(
            IPLConnectives.OR,  // connective that may appear in any subformula of the main formula.
            IPLSigns.TRUE,  // sign of the auxiliary formula.
            new KEDecoratedRuleRole("Right", IPLConnectives.NOT),   // role of the auxiliary formula in the subformula of the main formula 
                                                                   // where the _mainConnective was found.
            new BinarySomeRelationLabelCondition());    
                    
	
	public static final rules.ipl.TwoPremisesOneConclusionRule T_A_OR_B_NOT_B = new rules.ipl.TwoPremisesOneConclusionRule(
            "T_A_OR_B_NOT_B",
            pattern_T_A_OR_B_NOT_B,
            new KELabelledAction(
                ActionType.ADD_NODE,
                new rules.ipl.SubformulaRoleGetter(pattern_T_A_OR_B_NOT_B, KERuleRole.LEFT),
                //new NotSubformulaGetter(KERuleRole.RIGHT, IPLSigns.TRUE),
                LabelGetter.MAIN
            )
        );	
	
	/**
    Rule 8
    F A and B : cj
    T A : ci
    ci ⪯ cj
    ----------
    F B : cj
    */    
	
	public static final rules.ipl.TwoPremisesOneConclusionRule F_AND_LEFT = new rules.ipl.TwoPremisesOneConclusionRule(
            "F_AND_LEFT",

            new rules.patterns.ipl.TwoSignsConnectiveRolePattern(
                    IPLSigns.FALSE,     // main sign
                    IPLConnectives.AND, // main connective
                    IPLSigns.TRUE,      // aux sign
                    KERuleRole.LEFT,    // aux role
					// cambiar por GreaterEqual y ver otros
                    new GreaterThanLabelCondition()
            ),   
            new KELabelledAction(
                    ActionType.ADD_NODE,
                    BinaryTwoPremisesConnectiveGetter.FALSE_OTHER,
                    LabelGetter.MAIN
            ));

    /**
    Rule 9
    F A and B: Cj
    T B : Ci
    Ci <= Cj
    -----------------
    F A : Cj
    */
	static final rules.patterns.ipl.SignConnectiveRoleSubformulaPattern pattern_X_AND_T_RIGHT = new rules.patterns.ipl.SignConnectiveRoleSubformulaPattern(
            IPLConnectives.AND, 
            IPLSigns.TRUE, 
            KERuleRole.RIGHT, 
            new GreaterThanLabelCondition());

    public static final rules.ipl.TwoPremisesOneConclusionRule X_AND_T_RIGHT = new rules.ipl.TwoPremisesOneConclusionRule(
        "X_AND_T_RIGHT",
        pattern_X_AND_T_RIGHT,
        new KELabelledAction(
            ActionType.ADD_NODE,
            new SubformulaRoleGetter(pattern_X_AND_T_RIGHT, KERuleRole.LEFT),
            LabelGetter.MAIN
        )
    );	
	
    /**
    Rule 10
    T not (A and B) : ci
    T A : cj
    ci <= ck and cj <= cK
    -----------------
    T not B : cK
    */
    public static final TwoLevelCompositeBinaryFormulaPattern T_NOT_AND_B_PATTERN = new TwoLevelCompositeBinaryFormulaPattern(
        IPLConnectives.NOT, 
        IPLConnectives.AND, 
        IPLSigns.TRUE,
        IPLSigns.TRUE, 
        //new KEDecoratedRuleRole("Right", IPLConnectives.NOT), 
        KERuleRole.LEFT,
        new GreaterBinaryRelationLabelCondition()
        );

    public static final rules.ipl.TwoPremisesOneConclusionRule T_NOT_A_AND_B = new rules.ipl.TwoPremisesOneConclusionRule(
        "T_NOT_A_AND_B",
        T_NOT_AND_B_PATTERN,

        new KELabelledAction(
            ActionType.ADD_NODE,
            
            new rules.ipl.SubformulaRoleGetter(T_NOT_AND_B_PATTERN, new KEDecoratedRuleRole("Right", IPLConnectives.NOT) ),
            //new rules.ipl.SubformulaRoleGetter(T_NOT_AND_B_PATTERN, KERuleRole.RIGHT ),
            new MinimalGreaterLabelGetter()
        )
    );
    
    
    /**
    Rule 11
    T not (A and B) : ci
    T B : cj
    ci ⪯ ck and cj ⪯ ck
    -----------------
    T not A : ck
    */
    public static final TwoLevelCompositeBinaryFormulaPattern pattern_T_NOT_AND_LEFT = new TwoLevelCompositeBinaryFormulaPattern(
            IPLConnectives.NOT, 
            IPLConnectives.AND, 
            IPLSigns.TRUE,
            IPLSigns.TRUE, 
            KERuleRole.RIGHT,
            //new KEDecoratedRuleRole("Right", IPLConnectives.NOT), 
            new GreaterBinaryRelationLabelCondition());
    
    public static final  rules.ipl.TwoPremisesOneConclusionRule T_NOT_AND_LEFT = new  rules.ipl.TwoPremisesOneConclusionRule(
        "T_NOT_AND_LEFT",
        pattern_T_NOT_AND_LEFT,
        new KELabelledAction(
            ActionType.ADD_NODE,
            new rules.ipl.SubformulaRoleGetter(pattern_T_NOT_AND_LEFT, new KEDecoratedRuleRole("Left", IPLConnectives.NOT) ),
            new MinimalGreaterLabelGetter()
        )
    );
            
    /**
    Rule 12
    T A imples B : ci
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
                new NoLabelCondition()), 
        new KELabelledAction(ActionType.ADD_NODE,
                new rules.ipl.SubformulaRoleGetter(pattern_X_IMPLIES_T_LEFT, KERuleRole.RIGHT),
                new MinimalGreaterLabelGetter()
            )
    );


    /**
    Rule 13
    T A imples B : ci
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
    Rule 14
    F A imples B: ci
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
	            LabelGetter.GLOBAL_NEW
	        ),
	        new KELabelledAction(
	            ActionType.ADD_NODE,
	            new SimpleSubformulaRoleGetter(KERuleRole.RIGHT, IPLSigns.FALSE),
	            LabelGetter.GLOBAL_NEW
	        ),
	        LabelGetter.GLOBAL_NEW
    );
    

    /**
    Rule 15
    T not (A implies B) : ci
    ----------------- ck new
    T A: ck
    T not B : ci
    ci ⪯ ck
    */
    public static final rules.ipl.OnePremiseTwoConclusionsRule T_NOT_A_IMPLIES_B_TA_FB = new rules.ipl.OnePremiseTwoConclusionsRule(
            "T_NOT_A_IMPLIES_B_TA_FB",
            //new rules.patterns.ipl.SignConnectivePattern(IPLSigns.FALSE, IPLConnectives.IMPLIES),
            new TwoLevelCompositeFormulaPattern(IPLConnectives.NOT, IPLConnectives.IMPLIES),
            new KELabelledAction(
                ActionType.ADD_NODE,
                new CompositeLabelledAction(IPLConnectives.NOT, new SimpleSubformulaRoleGetter(KERuleRole.LEFT, IPLSigns.TRUE)),
                LabelGetter.GLOBAL_NEW
            ),
            new KELabelledAction(
                ActionType.ADD_NODE,
                new CompositeLabelledAction(IPLConnectives.NOT, new NotSubformulaGetter(KERuleRole.RIGHT, IPLSigns.TRUE)),
                new MainLabelGetter()
            )
        );

    /**
    Rule 16
    T (A implies B) : ci
    T not B : cj
    ci ⪯ cj
    ----------------- 
    T not A : cj
    */
    static final rules.patterns.ipl.SignConnectiveRoleSubformulaPattern pattern_T_X_IMPLIES_Y_NOT_Y = new rules.patterns.ipl.SignConnectiveRoleSubformulaPattern(
        IPLConnectives.IMPLIES, 
        IPLSigns.TRUE, 
        new KEDecoratedRuleRole("Right", IPLConnectives.NOT),
        new LessThanLabelCondition());
    public static final rules.ipl.TwoPremisesOneConclusionRule T_X_IMPLIES_Y_NOT_Y = new rules.ipl.TwoPremisesOneConclusionRule(
        "T_X_IMPLIES_Y_NOT_Y", 
        pattern_T_X_IMPLIES_Y_NOT_Y,
        new KELabelledAction(
            ActionType.ADD_NODE, 
            new NotSubformulaGetter(KERuleRole.LEFT, IPLSigns.TRUE),
            LabelGetter.AUX
        )
    );
    
    /**
    Rule 17
    F not A : ci
    ----------------- cj new
    T A : cj
    ci ⪯ cj
    */
	public static final rules.Rule F_NOT = new rules.ipl.OnePremiseOneConclusionRule(
		"F_NOT",
		new rules.patterns.ipl.SignConnectivePattern(
				IPLSigns.FALSE, 
				IPLConnectives.NOT), 
		new KELabelledAction(
				ActionType.ADD_NODE, 
				UnaryConnectiveGetter.TRUE,
				LabelGetter.GLOBAL_NEW));


    /**
    Rule 18
    T not not A : ci
    ----------------- ck new
    T  A : ck
    ci ⪯ ck
    */
    public static final rules.ipl.OnePremiseOneConclusionRule T_NOT_NOT = new rules.ipl.OnePremiseOneConclusionRule(
        "T_NOT_NOT",
        new TwoLevelCompositeFormulaPattern(IPLConnectives.NOT, IPLConnectives.NOT),
        new KELabelledAction(
            ActionType.ADD_NODE,
            new CompositeLabelledAction(IPLConnectives.NOT, new SimpleSubformulaRoleGetter(KERuleRole.LEFT, IPLSigns.TRUE)),
            LabelGetter.GLOBAL_NEW
        )
    );

}