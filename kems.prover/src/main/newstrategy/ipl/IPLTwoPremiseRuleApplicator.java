/*
 * Created on 01/11/2005
 *
 */
package main.newstrategy.ipl;

import java.util.Iterator;
import java.util.List;

import logic.formulas.CompositeFormula;
import logic.formulas.Connective;
import logic.formulas.FormulaFactory;
import logic.labelledFormulas.LabelledFormulaFactory;
import logic.signedFormulas.FormulaSign;
import logic.signedFormulas.PBCandidateList;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaBuilder;
import logic.signedFormulas.SignedFormulaFactory;
import logic.signedFormulas.SignedFormulaList;
import main.newstrategy.ISimpleStrategy;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import main.proofTree.iterator.IProofTreeVeryBasicIterator;
import main.strategy.ClassicalProofTree;
import main.strategy.applicator.IRuleApplicator;
import rules.KERuleRole;
import rules.Rule;
import rules.ipl.TwoPremisesOneConclusionRule;
import rules.structures.ConnectiveRoleSignRuleList;
import rules.structures.IPLConnectiveRoleSignRuleList;

/**
 * A two premise rule applicator
 * 
 * @author Adolfo Gustavo Serra Seca Neto
 * 
 */
public class IPLTwoPremiseRuleApplicator implements IRuleApplicator {

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
	public boolean applyAll(ClassicalProofTree current, SignedFormulaBuilder sfb) {
		// faz o seguinte:
		// para cada main, procurar referencias a um dos dois possiveis
		// auxiliary candidates
		// se encontrar, entao aplicar
		System.out.println("DEBUG: IPLTwoPremiseRuleApplicator.applyAll called");
		boolean hasApplied = false;

		Object ruleListObject = strategy.getMethod().getRules().get(ruleListName);
		
		// Verificar que sea realmente un IPLConnectiveRoleSignRuleList
		if (!(ruleListObject instanceof IPLConnectiveRoleSignRuleList)) {
			System.err.println("Error: Expected IPLConnectiveRoleSignRuleList but got " + 
							 (ruleListObject != null ? ruleListObject.getClass().getName() : "null"));
			return false;
		}
		
		IPLConnectiveRoleSignRuleList twoPremiseRules = (IPLConnectiveRoleSignRuleList) ruleListObject;

		SignedFormula mainCandidate;

		// TODO EH ISSO MESMO?
		initializeMainCandidates(current, null);

		while ((mainCandidate = nextMainCandidate(strategy.getProofTree(), null)) != null) {

			System.out.println("DEBUG: MAIN CANDIDATE: " + mainCandidate);

			Connective mainConnective = ((CompositeFormula) mainCandidate
					.getFormula()).getConnective();
			FormulaSign mainSign = mainCandidate.getSign();

			System.out.println("DEBUG: Main connective: " + mainConnective + ", main sign: " + mainSign);

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
			
			System.out.println("DEBUG: Left rules found: " + leftRules);
			System.out.println("DEBUG: Right rules found: " + rightRules);

			for (Iterator<Rule> it = leftRules.iterator(); it.hasNext();) {
				if (hasApplied)
					break;
				Rule left_rule = it.next();
				System.out.println("DEBUG: Trying left rule: " + left_rule);
				for (Iterator<Rule> it2 = rightRules.iterator(); it2.hasNext();) {
					if (hasApplied)
						break;


					Rule right_rule = it2.next();
					boolean appliedLeft = false;
					// verifies if left rule can be applied. If it can apply it.
					if (left_rule != null) {
						System.out.println("DEBUG: Attempting to apply left rule: " + left_rule);
						appliedLeft = tryToApplyTwoPremiseRule(strategy
								.getCurrent(), sfb, mainCandidate, left_rule);
						System.out.println("DEBUG: Left rule applied: " + appliedLeft);
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
				}
			}

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

		return hasApplied;
	}

	/**
	 * @param current
	 * @param object
	 */
	private void initializeMainCandidates(ClassicalProofTree proofTree,
			Object object) {
		mainCandidates = proofTree.getPBCandidates();
		counterMainCandidates = 0;
	}

	protected SignedFormula nextMainCandidate(ClassicalProofTree proofTree,
			SignedFormula auxCandidate) {
//		System.out.println(counterMainCandidates + ": " + mainCandidates);
		if (counterMainCandidates < mainCandidates.size()) {
//			System.out.println("Chosen:"
//					+ mainCandidates.get(counterMainCandidates));
			return mainCandidates.get(counterMainCandidates++);
		}
		// else {
		// System.out.println("Chosen: none");
		// }

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

		System.out.println("DEBUG: tryToApplyTwoPremiseRule for rule: " + rule + " with main: " + mainCandidate);
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

		System.out.println("DEBUG: Auxiliary candidates: " + sfl);

		/*
		public SignedFormulaList getAuxiliaryCandidates(LabelledFormulaFactory lff, SignedFormulaFactory sff,
				FormulaFactory ff, SignedFormula sfMain) {
			return _premise.getAuxiliaryCandidates(lff, sff, ff, sfMain);
		}
		*/
		
		SignedFormulaList result = getReferences(proofTree, sfl);
		System.out.println("DEBUG: References found: " + result);

		if (result.size() > 0) {
			SignedFormula auxCandidate = (SignedFormula) result.get(0);
			System.out.println("DEBUG: Auxiliary candidate: " + auxCandidate);

			hasApplied = applyTwoPremiseRule(proofTree, sfb, mainCandidate,
					aRule, result, auxCandidate);
			System.out.println("DEBUG: Two-premise rule applied: " + hasApplied);

		} else {
			System.out.println("DEBUG: No auxiliary references found for rule " + rule);
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
		System.out.println("DEBUG: applyTwoPremiseRule - main: " + mainCandidate + ", aux: " + auxCandidate);
		sfl.add(0, mainCandidate);
		System.out.println("DEBUG: SignedFormulaList for rule: " + sfl);
		SignedFormulaList conclusion = (aRule.getPossibleConclusions(sfb
				.getSignedFormulaFactory(), sfb.getFormulaFactory(), sfl));
		System.out.println("DEBUG: Possible conclusions: " + conclusion);

		// TODO sup�e apenas uma conclus�o
		if (conclusion!=null && conclusion.size() > 0 && proofTree.getNode(conclusion.get(0)) == null) {
			proofTree.addLast(new SignedFormulaNode((SignedFormula) conclusion
					.get(0), SignedFormulaNodeState.NOT_ANALYSED, strategy
					.createOrigin(aRule, proofTree.getNode(mainCandidate),
							proofTree.getNode(auxCandidate))));
			// System.err.println(proofTree.getBranchId()+ " " +
			// conclusion.get(0));
			// try {
			// System.in.read();
			// } catch (IOException e) {
			// e.printStackTrace();
			// }
			
//			System.out.println("rule:"+aRule);
			// removes main from the list of PB candidates
			strategy.getCurrent().removeFromPBCandidates(mainCandidate,
					SignedFormulaNodeState.ANALYSED);

			hasApplied = true;
		}

		return hasApplied;
	}

	protected SignedFormulaList getReferences(ClassicalProofTree proofTree,
			SignedFormulaList sflInput) {

		// TODO do as in simple strategy? keep it in memory?
		// TODO do it top-down?

		SignedFormulaList sflResult = new SignedFormulaList();

		// iterates (bottom up) over the branch
		IProofTreeVeryBasicIterator it = proofTree.getTopDownIterator();

		while (it.hasNext()) {

			SignedFormulaNode sfn = (SignedFormulaNode) it.next();

			SignedFormula sf = (SignedFormula) sfn.getContent();
			//if (sflInput.contains((SignedFormula) sfn.getContent())) {
			if (formulaLevelContains(sflInput,sf)) {
				sflResult.add(sf);
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

}
