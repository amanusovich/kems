/*
 * Created on 01/11/2005
 *
 */
package main.newstrategy.ipl;

import java.util.Iterator;
import java.util.List;

import logic.formulas.CompositeFormula;
import logic.formulas.Connective;
import logic.labelledFormulas.LabelledFormulaFactory;
import logic.signedFormulas.FormulaSign;
import logic.signedFormulas.PBCandidateList;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaBuilder;
import logic.signedFormulas.SignedFormulaFactory;
import logic.signedFormulas.SignedFormulaList;
import logic.formulas.Formula;
import logicalSystems.ipl.IPLConnectives;
import logicalSystems.ipl.IPLProofTree;
import logicalSystems.ipl.IPLSigns;
import main.newstrategy.ISimpleStrategy;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import main.proofTree.iterator.IProofTreeVeryBasicIterator;
import main.strategy.ClassicalProofTree;
import main.strategy.applicator.IRuleApplicator;
import rules.KERuleRole;
import rules.Rule;
import rules.ipl.TwoPremisesOneConclusionRule;
import rules.structures.IPLConnectiveRoleSignRuleList;

/**
 * A two premise rule applicator
 * 
 * @author Adolfo Gustavo Serra Seca Neto
 * 
 */
public class IPLTwoPremiseRuleApplicator implements IRuleApplicator {

	private static final IPLTracer tracer = IPLTracer.getInstance();

	private ISimpleStrategy strategy;

	private String ruleListName;

	/**
	 * @param strategy
	 * @param sfb
	 */
	public IPLTwoPremiseRuleApplicator(ISimpleStrategy strategy,
			String ruleListName) {
		super();
		this.strategy = strategy;
		this.ruleListName = ruleListName;
	}

	private PBCandidateList mainCandidates;
	private int counterMainCandidates;

	/*
	 * (non-Javadoc)
	 * 
	 * @seemain.strategy.applicator.IRuleApplicator#applyAll(main.strategy.
	 * ClassicalProofTree, logic.signedFormulas.SignedFormulaBuilder)
	 */
	/**
	 * Applies a two-premise rule to a single specific formula.
	 * This method is used by the canonical algorithm implementation.
	 * 
	 * @param current the proof tree
	 * @param sfb the signed formula builder
	 * @param mainCandidate the specific formula to process
	 * @return true if a rule was applied, false otherwise
	 */
	public boolean applySingle(ClassicalProofTree current, SignedFormulaBuilder sfb, SignedFormula mainCandidate) {
		if (!(mainCandidate.getFormula() instanceof CompositeFormula)) {
			return false;
		}
		
		Object ruleListObject = strategy.getMethod().getRules().get(ruleListName);
		if (!(ruleListObject instanceof IPLConnectiveRoleSignRuleList)) {
			return false;
		}
		
		IPLConnectiveRoleSignRuleList twoPremiseRules = (IPLConnectiveRoleSignRuleList) ruleListObject;
		
		Connective mainConnective = ((CompositeFormula) mainCandidate.getFormula()).getConnective();
		FormulaSign mainSign = mainCandidate.getSign();
		
		List<Rule> leftRules = twoPremiseRules.getMany(mainConnective, KERuleRole.LEFT, mainSign);
		List<Rule> rightRules = twoPremiseRules.getMany(mainConnective, KERuleRole.RIGHT, mainSign);
		
		// Try LEFT rules first
		for (Rule left_rule : leftRules) {
			if (left_rule != null) {
				boolean applied = tryToApplyTwoPremiseRule(current, sfb, mainCandidate, left_rule);
				if (applied) {
					return true;
				}
			}
		}
		
		// Try RIGHT rules
		for (Rule right_rule : rightRules) {
			if (right_rule != null) {
				boolean applied = tryToApplyTwoPremiseRule(current, sfb, mainCandidate, right_rule);
				if (applied) {
					return true;
				}
			}
		}
		
		// No rule was applied (likely missing auxiliary premise)
		// DON'T mark as ANALYSED here - let the canonical algorithm decide
		return false;
	}
	
	public boolean applyAll(ClassicalProofTree current, SignedFormulaBuilder sfb) {
		// faz o seguinte:
		// para cada main, procurar referencias a um dos dois possiveis
		// auxiliary candidates
		// se encontrar, entao aplicar
		boolean hasApplied = false;

		Object ruleListObject = strategy.getMethod().getRules().get(ruleListName);
		
		// Verificar que sea realmente un IPLConnectiveRoleSignRuleList
		if (!(ruleListObject instanceof IPLConnectiveRoleSignRuleList)) {
			return false;
		}
		
		IPLConnectiveRoleSignRuleList twoPremiseRules = (IPLConnectiveRoleSignRuleList) ruleListObject;

		SignedFormula mainCandidate;

		// TODO EH ISSO MESMO?
		initializeMainCandidates(current, null);

		while ((mainCandidate = nextMainCandidate(strategy.getProofTree(), null)) != null) {

			Connective mainConnective = ((CompositeFormula) mainCandidate
					.getFormula()).getConnective();
			FormulaSign mainSign = mainCandidate.getSign();

			/*
			Rule left_rule = twoPremiseRules.get(mainConnective,
					KERuleRole.LEFT, mainSign);
			Rule right_rule = twoPremiseRules.get(mainConnective,
					KERuleRole.RIGHT, mainSign);
			*/
			
			List<Rule> leftRules = twoPremiseRules.getMany(mainConnective,
					KERuleRole.LEFT, mainSign);
			List<Rule> rightRules = twoPremiseRules.getMany(mainConnective,
					KERuleRole.RIGHT, mainSign);
			
	// Procesar reglas LEFT
	boolean appliedAny = false;
	for (Iterator<Rule> it = leftRules.iterator(); it.hasNext() && !appliedAny;) {
		Rule left_rule = it.next();
		if (left_rule != null) {
			boolean appliedLeft = tryToApplyTwoPremiseRule(strategy
					.getCurrent(), sfb, mainCandidate, left_rule);
			appliedAny = appliedAny || appliedLeft;
			if (appliedLeft) {
				counterMainCandidates--;
			}
		}
	}
	
	// Procesar reglas RIGHT (solo si no se aplicó ninguna LEFT)
	if (!appliedAny) {
		for (Iterator<Rule> it2 = rightRules.iterator(); it2.hasNext() && !appliedAny;) {
			Rule right_rule = it2.next();
			if (right_rule != null) {
				boolean appliedRight = tryToApplyTwoPremiseRule(strategy
						.getCurrent(), sfb, mainCandidate, right_rule);
				appliedAny = appliedAny || appliedRight;
				if (appliedRight) {
					counterMainCandidates--;
				}
			}
		}
	}
	
	// Si no se aplicó ninguna regla (porque falta la premisa auxiliar),
	// marcar como ANALYSED para que PB pueda generar la premisa faltante
	if (!appliedAny && (leftRules.size() > 0 || rightRules.size() > 0)) {
		strategy.getCurrent().removeFromPBCandidates(mainCandidate, SignedFormulaNodeState.ANALYSED);
	}
	
	hasApplied = hasApplied || appliedAny;

			/*
			boolean appliedLeft = false;
			// verifies if left rule can be applied. If it can apply it.
			if (left_rule != null) {
				appliedLeft = tryToApplyTwoPremiseRule(strategy
						.getCurrent(), sfb, mainCandidate, left_rule);
				hasApplied = hasApplied || appliedLeft;
				if (appliedLeft)
					counterMainCandidates--;
			}

			// verifies if right rule can be applied. If it can apply it.
			if (right_rule != null) {
				boolean appliedRight = tryToApplyTwoPremiseRule(strategy
						.getCurrent(), sfb, mainCandidate, right_rule);
				hasApplied = hasApplied || appliedRight;
				if (appliedRight &!appliedLeft)
					counterMainCandidates--;
			}
			*/

		}
		
		// SEGUNDA PASADA: Procesar fórmulas ancestros accesibles
		// Esto permite que reglas de dos premisas se apliquen con nuevas premisas auxiliares
		// creadas en ramas descendientes
		boolean hasAppliedFromAncestors = processAncestorCandidates(current, sfb, twoPremiseRules);
		hasApplied = hasApplied || hasAppliedFromAncestors;

		return hasApplied;
	}
	
	/**
	 * Procesa candidatos de ramas ancestros con reglas de dos premisas.
	 * Solo procesa fórmulas que tienen reglas de dos premisas disponibles.
	 * Retorna true si se aplicó alguna regla.
	 */
	private boolean processAncestorCandidates(ClassicalProofTree proofTree, 
	                                          SignedFormulaBuilder sfb,
	                                          IPLConnectiveRoleSignRuleList twoPremiseRules) {
		boolean hasApplied = false;
		
		// Obtener candidatos ancestros (sin duplicar los de la rama actual)
		PBCandidateList ancestorCandidates = new PBCandidateList();
		collectAncestorCandidates(proofTree, twoPremiseRules, ancestorCandidates);
		
		// Procesar cada candidato ancestro
		for (int i = 0; i < ancestorCandidates.size() && !hasApplied; i++) {
			SignedFormula mainCandidate = ancestorCandidates.get(i);
			
			Connective mainConnective = ((CompositeFormula) mainCandidate.getFormula()).getConnective();
			FormulaSign mainSign = mainCandidate.getSign();
			
			List<Rule> leftRules = twoPremiseRules.getMany(mainConnective, rules.KERuleRole.LEFT, mainSign);
			List<Rule> rightRules = twoPremiseRules.getMany(mainConnective, rules.KERuleRole.RIGHT, mainSign);
			
			// Intentar aplicar reglas LEFT
			for (Iterator<Rule> it = leftRules.iterator(); it.hasNext() && !hasApplied;) {
				Rule rule = it.next();
				hasApplied = tryToApplyTwoPremiseRule(proofTree, sfb, mainCandidate, rule);
				if (hasApplied) {
					if (IPLTracer.isEnabled()) {
						tracer.logInfo("Ancestor rule applied (LEFT): " + rule);
					}
				}
			}
			
			// Intentar aplicar reglas RIGHT (solo si no se aplicó LEFT)
			if (!hasApplied) {
				for (Iterator<Rule> it = rightRules.iterator(); it.hasNext() && !hasApplied;) {
					Rule rule = it.next();
					hasApplied = tryToApplyTwoPremiseRule(proofTree, sfb, mainCandidate, rule);
					if (hasApplied) {
						if (IPLTracer.isEnabled()) {
							tracer.logInfo("Ancestor rule applied (RIGHT): " + rule);
						}
					}
				}
			}
		}
		
		return hasApplied;
	}
	
	/**
	 * Colecta fórmulas compuestas de ramas ancestros que:
	 * 1. Tienen reglas de dos premisas disponibles
	 * 2. Son accesibles en la rama actual
	 * 3. No están ya en mainCandidates (evita duplicados)
	 */
	private void collectAncestorCandidates(ClassicalProofTree proofTree,
	                                        IPLConnectiveRoleSignRuleList twoPremiseRules,
	                                        PBCandidateList ancestorCandidates) {
		// Iterar sobre todas las fórmulas en el árbol
		main.proofTree.iterator.IProofTreeVeryBasicIterator it = proofTree.getTopDownIterator();
		
		while (it.hasNext()) {
			main.proofTree.INode node = it.next();
			
			if (!(node instanceof SignedFormulaNode)) {
				continue;
			}
			
			SignedFormulaNode sfNode = (SignedFormulaNode) node;
			SignedFormula sf = (SignedFormula) sfNode.getContent();
			
			// Solo fórmulas compuestas
			if (!(sf.getFormula() instanceof logic.formulas.CompositeFormula)) {
				continue;
			}
			
			logic.formulas.CompositeFormula compFormula = (logic.formulas.CompositeFormula) sf.getFormula();
			
			if (sf.getFormula().toString().equals("TOP") || 
			    sf.getFormula().toString().equals("BOTTOM")) {
				continue;
			}
			
			// Solo agregar si tiene reglas de dos premisas
			java.util.List<Rule> leftRules = twoPremiseRules.getMany(
				compFormula.getConnective(), 
				rules.KERuleRole.LEFT, 
				sf.getSign());
			java.util.List<Rule> rightRules = twoPremiseRules.getMany(
				compFormula.getConnective(), 
				rules.KERuleRole.RIGHT, 
				sf.getSign());
			
			if (leftRules.isEmpty() && rightRules.isEmpty()) {
				continue;
			}
			
			// Verificar accesibilidad de etiqueta
			if (proofTree instanceof logicalSystems.ipl.IPLProofTree) {
				logicalSystems.ipl.IPLProofTree iplTree = (logicalSystems.ipl.IPLProofTree) proofTree;
				if (sf instanceof logic.labelledFormulas.LabelledFormula) {
					logic.labelledFormulas.LabelledFormula lf = (logic.labelledFormulas.LabelledFormula) sf;
					if (!iplTree.isLabelAccessible(lf.getLabel())) {
						continue;
					}
				}
			}
			
			// No agregar si ya está en mainCandidates
			if (mainCandidates.contains(sf)) {
				continue;
			}
			
			// No agregar duplicados
			if (!ancestorCandidates.contains(sf)) {
				ancestorCandidates.add(sf);
			}
		}
	}

	/**
	 * Inicializa los candidatos principales para reglas de dos premisas.
	 * Solo incluye candidatos de la rama actual (getPBCandidates).
	 * Los ancestros se procesan por separado después del loop principal.
	 */
	private void initializeMainCandidates(ClassicalProofTree proofTree,
			Object object) {
		// Solo candidatos de la rama actual
		mainCandidates = proofTree.getPBCandidates();
		counterMainCandidates = 0;
	}
	
	protected SignedFormula nextMainCandidate(ClassicalProofTree proofTree,
			SignedFormula auxCandidate) {
		if (counterMainCandidates < mainCandidates.size()) {
			return mainCandidates.get(counterMainCandidates++);
		}

		return null;
	}


	/**
	 * @param proofTree
	 * @param sfb
	 * @param mainCandidate
	 * @param rule
	 * @return
	 */
	private boolean tryToApplyTwoPremiseRule(ClassicalProofTree proofTree,
			SignedFormulaBuilder sfb, SignedFormula mainCandidate, Rule rule) {

		boolean hasApplied = false;

		TwoPremisesOneConclusionRule aRule = ((TwoPremisesOneConclusionRule) rule);

		// Verificar que el factory sea realmente LabelledFormulaFactory para IPL
		SignedFormulaFactory signedFactory = sfb.getSignedFormulaFactory();
		LabelledFormulaFactory labelledFactory;
		
		if (signedFactory instanceof LabelledFormulaFactory) {
			labelledFactory = (LabelledFormulaFactory) signedFactory;
		} else {
			// Para IPL, crear una LabelledFormulaFactory si no existe
			labelledFactory = new LabelledFormulaFactory();
		}
		
		SignedFormulaList sfl = aRule.getAuxiliaryCandidates(
				labelledFactory,
				sfb.getSignedFormulaFactory(), 
				sfb.getFormulaFactory(),
				mainCandidate);

		/*
		public SignedFormulaList getAuxiliaryCandidates(LabelledFormulaFactory lff, SignedFormulaFactory sff,
				FormulaFactory ff, SignedFormula sfMain) {
			return _premise.getAuxiliaryCandidates(lff, sff, ff, sfMain);
		}
		*/
		
		SignedFormulaList result = getReferences(proofTree, sfl);

		if (result.size() > 0) {
			// Iterar sobre TODOS los candidatos auxiliares encontrados
			// hasta que uno satisfaga la condición de etiquetas y la regla se aplique
			for (int i = 0; i < result.size() && !hasApplied; i++) {
				SignedFormula auxCandidate = (SignedFormula) result.get(i);

				// Crear una NUEVA lista con solo el candidato auxiliar actual
				// para evitar que se acumulen elementos en 'result'
				SignedFormulaList cleanList = new SignedFormulaList();
				cleanList.add(auxCandidate);
				
				hasApplied = applyTwoPremiseRule(proofTree, sfb, mainCandidate,
						aRule, cleanList, auxCandidate);
				
				if (hasApplied) {
					if (IPLTracer.isEnabled()) {
						tracer.logInfo("Two-premise rule applied with candidate #" + i);
					}
				}
			}

		}

		return hasApplied;

	}

	/**
	 * Applies a two premise rulem given:
	 * 
	 * @param proofTree
	 * @param sfb
	 * @param mainCandidate
	 * @param rule
	 * @param aRule
	 * @param sfl
	 * @param auxCandidate
	 */
	private boolean applyTwoPremiseRule(ClassicalProofTree proofTree,
			SignedFormulaBuilder sfb, SignedFormula mainCandidate,
			TwoPremisesOneConclusionRule aRule, SignedFormulaList sfl,
			SignedFormula auxCandidate) {
		boolean hasApplied = false;
		
		// Verificar rinstances para evitar bucles
		String ruleInstance = createRuleInstanceKey(aRule.toString(), mainCandidate, auxCandidate);
		if (proofTree instanceof IPLProofTree) {
			IPLProofTree iplTree = (IPLProofTree) proofTree;
			if (iplTree.wasRuleInstanceApplied(ruleInstance)) {
				if (IPLTracer.isEnabled()) {
					tracer.logRuleBlocked(aRule.toString(), mainCandidate.toString(),
							"rinstance exists: " + ruleInstance);
				}
				return false; // No aplicar, ya fue aplicada
			}
		}
		
		sfl.add(0, mainCandidate);
		SignedFormulaList conclusion = (aRule.getPossibleConclusions(sfb
				.getSignedFormulaFactory(), sfb.getFormulaFactory(), sfl));

		// TODO sup�e apenas uma conclus�o
		if (conclusion != null && conclusion.size() > 0) {
			SignedFormula conclusionFormula = (SignedFormula) conclusion.get(0);
			boolean conclusionExists = proofTree.getNode(conclusionFormula) != null;
			
			// Registrar en rinstances SIEMPRE que se genere una conclusión
			// (incluso si ya existe en el árbol) para evitar reintentos infinitos
			if (proofTree instanceof IPLProofTree) {
				IPLProofTree iplTree = (IPLProofTree) proofTree;
				iplTree.registerRuleInstance(ruleInstance);
			}
			
			if (!conclusionExists) {
				// Solo añadir al árbol si no existe
				proofTree.addLast(new SignedFormulaNode(conclusionFormula, 
						SignedFormulaNodeState.NOT_ANALYSED, strategy
						.createOrigin(aRule, proofTree.getNode(mainCandidate),
								proofTree.getNode(auxCandidate))));
				
				// Mark as ANALYSED unconditionally. Universal formulas (T(A→B), T(¬A))
				// are re-selected by selectUnanalyzedFormula whenever Definition 5.6 is
				// not yet satisfied for new accessible worlds.
				strategy.getCurrent().removeFromPBCandidates(mainCandidate,
						SignedFormulaNodeState.ANALYSED);

				hasApplied = true;
			}
		}

		return hasApplied;
	}
	
	/**
	 * Crea una clave única para identificar una instancia de regla
	 */
	private String createRuleInstanceKey(String ruleName, SignedFormula main, SignedFormula aux) {
		return ruleName + ":" + main.toString() + ":" + aux.toString();
	}

	/**
	 * ⚠️ CORRECCIÓN: Busca premisas auxiliares en b (NO en b*)
	 * 
	 * Según Algorithm 1 línea 771: "if the corresponding minor premise of r is in b then"
	 * Las premisas auxiliares deben estar FÍSICAMENTE en b, no solo implícitamente en b*.
	 * 
	 * La extensión b* se usa SOLO para:
	 * - Verificar cierre (contradicciones)
	 * - Verificar provisos (como F→1)
	 * - Verificar completitud
	 * 
	 * Pero NO para buscar premisas auxiliares de reglas operacionales.
	 */
	protected SignedFormulaList getReferences(ClassicalProofTree proofTree,
			SignedFormulaList sflInput) {

		SignedFormulaList sflResult = new SignedFormulaList();

		// Buscar en b (físicamente en la rama), no en b*
		IProofTreeVeryBasicIterator it = proofTree.getTopDownIterator();

		while (it.hasNext()) {
			SignedFormulaNode sfn = (SignedFormulaNode) it.next();
			SignedFormula sf = (SignedFormula) sfn.getContent();
			
			if (formulaLevelContains(sflInput,sf)) {
				// Solo agregar si no es un duplicado (misma fórmula, signo Y etiqueta)
				if (!containsExactFormula(sflResult, sf)) {
					sflResult.add(sf);
				}
			}
		}
		
		return sflResult;
	}
	
	private boolean formulaLevelContains(SignedFormulaList aList, SignedFormula aSignedFormula) {
		
		for (SignedFormula listFormula : aList.getList()) {
			if (listFormula.getFormula().equals(aSignedFormula.getFormula()) &&
				listFormula.getSign().equals(aSignedFormula.getSign())	) {
				return true;
			}
			
		}
		
		return false;
	}
	
	/**
	 * Verifica si la lista contiene una fórmula con exactamente el mismo signo, fórmula Y etiqueta.
	 * Esto es para evitar duplicados en getReferences.
	 */
	private boolean containsExactFormula(SignedFormulaList aList, SignedFormula aSignedFormula) {
		for (SignedFormula listFormula : aList.getList()) {
			// Comparar signo, fórmula Y etiqueta (si aplica)
			if (listFormula.toString().equals(aSignedFormula.toString())) {
				return true;
			}
		}
		return false;
	}

}
