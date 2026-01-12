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
import rules.ipl.labels.NoLabelCondition;

/**
 * Rules (and patterns for these rules) for IPL.
 */
public class IPLRules {

	/** Rule for PB */
	public static final NamedRule PB = new NamedRule("PB");

	/** Rule for closing branches */
	public static final NamedRule CLOSE = new NamedRule("CLOSE");

	/**}
	Rule (F∨) - F-Disyunción
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
	Rule (T∧) - T-Conjunción
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
    Regla (F ∧1):
    F A∧B : cj
    T B : ci
    ci ⪯ cj
    ----------
    F A : cj
    
    Se usa con PB: si no existe T B, PB lo genera y luego aplica esta regla
    */
    public static final rules.ipl.TwoPremisesOneConclusionRule F_AND_RIGHT = new rules.ipl.TwoPremisesOneConclusionRule(
            "F_AND_RIGHT",
            new rules.patterns.ipl.TwoSignsConnectiveRolePattern(
                    IPLSigns.FALSE,     // main sign
                    IPLConnectives.AND, // main connective
                    IPLSigns.TRUE,      // aux sign
                    KERuleRole.RIGHT,   // aux role (T B es la subfórmula derecha)
                    new GreaterThanLabelCondition() // ci ⪯ cj
            ),   
            new KELabelledAction(
                    ActionType.ADD_NODE,
                    BinaryTwoPremisesConnectiveGetter.FALSE_OTHER, // F A (la otra subfórmula)
                    LabelGetter.MAIN // usa etiqueta de la premisa mayor (cj)
            ));

    /**
    Rule (T→₁) - T-Implicación (Modus Ponens)
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
                new GreaterBinaryRelationLabelCondition()), // ✅ CORRECCIÓN: Verificar que existe ck tal que ci ≤ ck y cj ≤ ck
        new KELabelledAction(ActionType.ADD_NODE,
                new rules.ipl.SubformulaRoleGetter(pattern_X_IMPLIES_T_LEFT, KERuleRole.RIGHT),
                new MinimalGreaterLabelGetter()
            )
    );


    /**
    Rule (T→₂) - T-Implicación (Modus Tollens)
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
    Rule (F→₃) - F-Implicación con T A existente
    F A→B : cj
    T A : ci
    ci ⪯ cj
    -----------------
    F B : cj
    
    Esta regla permite usar una T A : ci existente (con ci ⪯ cj) 
    para derivar F B : cj sin crear una nueva etiqueta.
    */
    public static final rules.ipl.TwoPremisesOneConclusionRule F_IMPLIES_T_LEFT = new rules.ipl.TwoPremisesOneConclusionRule(
        "F_IMPLIES_T_LEFT",
        new rules.patterns.ipl.TwoSignsConnectiveRolePattern(
            IPLSigns.FALSE,     // main sign (F A→B : cj)
            IPLConnectives.IMPLIES, // main connective
            IPLSigns.TRUE,      // aux sign (T A : ci)
            KERuleRole.LEFT,    // aux role (A es la subfórmula izquierda)
            new GreaterThanLabelCondition() // ci ⪯ cj, es decir aux ≤ main
        ),
        new KELabelledAction(
            ActionType.ADD_NODE,
            BinaryTwoPremisesConnectiveGetter.FALSE_OTHER, // F B (la otra subfórmula)
            LabelGetter.MAIN // usa etiqueta de la premisa mayor (cj)
        ));

    /**
    Rule (F→) - F-Implicación
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
	            LabelGetter.NEW  // ✅ CAMBIO: Usar NEW en lugar de GLOBAL_NEW
	        ),                     // NEW crea una etiqueta mayor que ci (la premisa)
	        new KELabelledAction( // sin establecer relaciones con todas las etiquetas del contexto
	            ActionType.ADD_NODE,
	            new SimpleSubformulaRoleGetter(KERuleRole.RIGHT, IPLSigns.FALSE),
	            LabelGetter.NEW
	        ),
	        LabelGetter.NEW  // ✅ CAMBIO: Usar NEW para que ambas conclusiones tengan la misma etiqueta nueva
    );

	/**
	 Rule (T¬) - T-Negación
	 T ¬A : ci
	 ci ⪯ cj
	 -----------------
	 F A : cj
	 Para cualquier cj tal que ci ≤ cj
	 */
	public static final rules.Rule T_NOT = new rules.ipl.OnePremiseOneConclusionRule(
		"T_NOT",
		new rules.patterns.ipl.SignConnectivePattern(
				IPLSigns.TRUE, 
				IPLConnectives.NOT), 
		new KELabelledAction(
				ActionType.ADD_NODE, 
				UnaryConnectiveGetter.FALSE,
				// cj tal que ci ⪯ cj (no necesariamente nuevo)
				new MinimalGreaterLabelGetter()));

    
    /**
    Rule (F¬) - F-Negación
    F ¬A : ci
    ----------------- cj new
    T A : cj
    ci ⪯ cj
    Condición: cj debe ser una constante nueva
    */
	public static final rules.Rule F_NOT = new rules.ipl.OnePremiseOneConclusionRule(
		"F_NOT",
		new rules.patterns.ipl.SignConnectivePattern(
				IPLSigns.FALSE, 
				IPLConnectives.NOT), 
		new KELabelledAction(
				ActionType.ADD_NODE, 
				UnaryConnectiveGetter.TRUE,
				// cj nuevo tal que ci ⪯ cj
				new NewLabelGetter("MAIN")));

	/**
	Regla (T∨₁) - T-Disyunción 1
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
			KERuleRole.LEFT,   // aux role (A es la subfórmula izquierda)
			new LessThanLabelCondition() // ci ⪯ cj (main ≤ aux)
		),
		new KELabelledAction(
			ActionType.ADD_NODE,
			BinaryTwoPremisesConnectiveGetter.TRUE_OTHER, // T B (la otra subfórmula)
			LabelGetter.MAIN // usa etiqueta de la premisa mayor (ci)
		));

	/**
	Regla (T∨₂) - T-Disyunción 2
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
			KERuleRole.RIGHT,  // aux role (B es la subfórmula derecha)
			new LessThanLabelCondition() // ci ⪯ cj (main ≤ aux)
		),
		new KELabelledAction(
			ActionType.ADD_NODE,
			BinaryTwoPremisesConnectiveGetter.TRUE_OTHER, // T A (la otra subfórmula)
			LabelGetter.MAIN // usa etiqueta de la premisa mayor (ci)
		));

	/**
	Regla (F∧₁) - F-Conjunción 1
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
			KERuleRole.LEFT,   // aux role (A es la subfórmula izquierda)
			new GreaterThanLabelCondition() // ci ⪯ cj, es decir aux ≤ main
		),
		new KELabelledAction(
			ActionType.ADD_NODE,
			BinaryTwoPremisesConnectiveGetter.FALSE_OTHER, // F B (la otra subfórmula)
			LabelGetter.MAIN // usa etiqueta de la premisa mayor (cj)
		));
}