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

		// strategy.getMethod().getRules().get(ruleListName) is always an
		// IPLConnectiveRoleSignRuleList: ruleListName is always
		// IPLRuleStructures.TWO_PREMISE_RULE_LIST (see IPLSimpleStrategy's
		// constructor), which IPLRuleStructures always registers as one.
		IPLConnectiveRoleSignRuleList twoPremiseRules =
				(IPLConnectiveRoleSignRuleList) strategy.getMethod().getRules().get(ruleListName);

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
		// For each main candidate, look for references to one of the two possible
		// auxiliary candidates; if found, apply the rule
		boolean hasApplied = false;

		IPLConnectiveRoleSignRuleList twoPremiseRules =
				(IPLConnectiveRoleSignRuleList) strategy.getMethod().getRules().get(ruleListName);

		SignedFormula mainCandidate;

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

	// Process LEFT rules
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

	// Process RIGHT rules (only if no LEFT rule applied)
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

	// If no rule was applied (because the auxiliary premise is missing),
	// mark it ANALYSED so PB can generate the missing premise
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

		// SECOND PASS: process accessible ancestor formulas
		// This allows two-premise rules to fire against new auxiliary premises
		// created in descendant branches
		boolean hasAppliedFromAncestors = processAncestorCandidates(current, sfb, twoPremiseRules);
		hasApplied = hasApplied || hasAppliedFromAncestors;

		return hasApplied;
	}

	/**
	 * Processes candidates from ancestor branches with two-premise rules.
	 * Only processes formulas that have two-premise rules available.
	 * Returns true if some rule was applied.
	 */
	private boolean processAncestorCandidates(ClassicalProofTree proofTree,
	                                          SignedFormulaBuilder sfb,
	                                          IPLConnectiveRoleSignRuleList twoPremiseRules) {
		boolean hasApplied = false;

		// Get ancestor candidates (without duplicating the current branch's)
		PBCandidateList ancestorCandidates = new PBCandidateList();
		collectAncestorCandidates(proofTree, twoPremiseRules, ancestorCandidates);

		// Process each ancestor candidate
		for (int i = 0; i < ancestorCandidates.size() && !hasApplied; i++) {
			SignedFormula mainCandidate = ancestorCandidates.get(i);

			Connective mainConnective = ((CompositeFormula) mainCandidate.getFormula()).getConnective();
			FormulaSign mainSign = mainCandidate.getSign();

			List<Rule> leftRules = twoPremiseRules.getMany(mainConnective, rules.KERuleRole.LEFT, mainSign);
			List<Rule> rightRules = twoPremiseRules.getMany(mainConnective, rules.KERuleRole.RIGHT, mainSign);

			// Try to apply LEFT rules
			for (Iterator<Rule> it = leftRules.iterator(); it.hasNext() && !hasApplied;) {
				Rule rule = it.next();
				hasApplied = tryToApplyTwoPremiseRule(proofTree, sfb, mainCandidate, rule);
				if (hasApplied) {
					if (IPLTracer.isEnabled()) {
						tracer.logInfo("Ancestor rule applied (LEFT): " + rule);
					}
				}
			}

			// Try to apply RIGHT rules (only if LEFT did not apply)
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
	 * Collects composite formulas from ancestor branches that:
	 * 1. Have two-premise rules available
	 * 2. Are accessible from the current branch
	 * 3. Are not already in mainCandidates (avoids duplicates)
	 */
	private void collectAncestorCandidates(ClassicalProofTree proofTree,
	                                        IPLConnectiveRoleSignRuleList twoPremiseRules,
	                                        PBCandidateList ancestorCandidates) {
		// Iterate over every formula in the tree
		main.proofTree.iterator.IProofTreeVeryBasicIterator it = proofTree.getTopDownIterator();

		while (it.hasNext()) {
			main.proofTree.INode node = it.next();

			if (!(node instanceof SignedFormulaNode)) {
				continue;
			}

			SignedFormulaNode sfNode = (SignedFormulaNode) node;
			SignedFormula sf = (SignedFormula) sfNode.getContent();

			// Composite formulas only
			if (!(sf.getFormula() instanceof logic.formulas.CompositeFormula)) {
				continue;
			}

			logic.formulas.CompositeFormula compFormula = (logic.formulas.CompositeFormula) sf.getFormula();

			if (sf.getFormula().toString().equals("TOP") ||
			    sf.getFormula().toString().equals("BOTTOM")) {
				continue;
			}

			// Only add it if it has two-premise rules
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

			// Check label accessibility (proofTree is always an IPLProofTree: this
			// applicator is only ever instantiated by IPLSimpleStrategy, whose
			// createPTInstance() always constructs IPLProofTree nodes)
			logicalSystems.ipl.IPLProofTree iplTree = (logicalSystems.ipl.IPLProofTree) proofTree;
			if (sf instanceof logic.labelledFormulas.LabelledFormula) {
				logic.labelledFormulas.LabelledFormula lf = (logic.labelledFormulas.LabelledFormula) sf;
				if (!iplTree.isLabelAccessible(lf.getLabel())) {
					continue;
				}
			}

			// Do not add it if it is already in mainCandidates
			if (mainCandidates.contains(sf)) {
				continue;
			}

			// Do not add duplicates
			if (!ancestorCandidates.contains(sf)) {
				ancestorCandidates.add(sf);
			}
		}
	}

	/**
	 * Initializes the main candidates for two-premise rules.
	 * Only includes candidates from the current branch (getPBCandidates).
	 * Ancestors are processed separately after the main loop.
	 */
	private void initializeMainCandidates(ClassicalProofTree proofTree,
			Object object) {
		// Only candidates from the current branch
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

		// Check that the factory is really a LabelledFormulaFactory for IPL
		SignedFormulaFactory signedFactory = sfb.getSignedFormulaFactory();
		LabelledFormulaFactory labelledFactory;

		if (signedFactory instanceof LabelledFormulaFactory) {
			labelledFactory = (LabelledFormulaFactory) signedFactory;
		} else {
			// For IPL, create a LabelledFormulaFactory if none exists
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
			// Iterate over ALL auxiliary candidates found until one satisfies
			// the label condition and the rule applies
			for (int i = 0; i < result.size() && !hasApplied; i++) {
				SignedFormula auxCandidate = (SignedFormula) result.get(i);

				// Build a NEW list with only the current auxiliary candidate
				// so elements do not keep accumulating in 'result'
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

		// proofTree is always an IPLProofTree: this applicator is only ever
		// instantiated by IPLSimpleStrategy, whose createPTInstance() always
		// constructs IPLProofTree nodes.
		IPLProofTree iplTree = (IPLProofTree) proofTree;

		// Check rinstances to prevent loops
		String ruleInstance = createRuleInstanceKey(aRule.toString(), mainCandidate, auxCandidate);
		if (iplTree.wasRuleInstanceApplied(ruleInstance)) {
			if (IPLTracer.isEnabled()) {
				tracer.logRuleBlocked(aRule.toString(), mainCandidate.toString(),
						"rinstance exists: " + ruleInstance);
			}
			return false; // Do not apply, it was already applied
		}

		sfl.add(0, mainCandidate);
		SignedFormulaList conclusion = (aRule.getPossibleConclusions(sfb
				.getSignedFormulaFactory(), sfb.getFormulaFactory(), sfl));

		// TODO assumes only one conclusion
		if (conclusion != null && conclusion.size() > 0) {
			SignedFormula conclusionFormula = (SignedFormula) conclusion.get(0);
			boolean conclusionExists = proofTree.getNode(conclusionFormula) != null;

			// Always register in rinstances when a conclusion is generated
			// (even if it already exists in the tree) to prevent infinite retries
			iplTree.registerRuleInstance(ruleInstance);

			if (!conclusionExists) {
				// Only add it to the tree if it does not already exist
				proofTree.addLast(new SignedFormulaNode(conclusionFormula,
						SignedFormulaNodeState.NOT_ANALYSED, strategy
						.createOrigin(aRule, proofTree.getNode(mainCandidate),
								proofTree.getNode(auxCandidate))));

				// Mark as ANALYSED unconditionally. Universal formulas (T(A->B), T(-A))
				// are re-selected by selectUnanalyzedFormula whenever Definition 5.3 is
				// not yet satisfied for new accessible worlds.
				strategy.getCurrent().removeFromPBCandidates(mainCandidate,
						SignedFormulaNodeState.ANALYSED);

				hasApplied = true;
			}
		}

		return hasApplied;
	}

	/**
	 * Creates a unique key to identify a rule instance
	 */
	private String createRuleInstanceKey(String ruleName, SignedFormula main, SignedFormula aux) {
		return ruleName + ":" + main.toString() + ":" + aux.toString();
	}

	/**
	 * Looks up auxiliary premises physically in b, never by implicit
	 * monotonicity.
	 *
	 * Per Algorithm 1 line 771: "if the corresponding minor premise of r is in b then"
	 * Auxiliary premises must be PHYSICALLY in b.
	 *
	 * No control-flow decision in the algorithm depends on implicit
	 * monotonicity: not closure checking (checkPhysicalBForContradiction
	 * iterates the physical branch directly), not completeness
	 * (isCompletelyAnalyzed is recursive, Definition 5.3), not the F->
	 * proviso (shouldBlockFImpliesRule in IPLOnePremiseRuleApplicator), not
	 * PB's alternative-label search (tryPBAtAlternativeLabels in
	 * IPLPBRuleApplicator), nor the search for auxiliary premises of
	 * operational rules here.
	 */
	protected SignedFormulaList getReferences(ClassicalProofTree proofTree,
			SignedFormulaList sflInput) {

		SignedFormulaList sflResult = new SignedFormulaList();

		// Search in b (physically in the branch), not in the monotonic extension
		IProofTreeVeryBasicIterator it = proofTree.getTopDownIterator();

		while (it.hasNext()) {
			SignedFormulaNode sfn = (SignedFormulaNode) it.next();
			SignedFormula sf = (SignedFormula) sfn.getContent();

			if (formulaLevelContains(sflInput,sf)) {
				// Only add it if it is not a duplicate (same formula, sign AND label)
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
	 * Checks whether the list contains a formula with exactly the same sign, formula AND label.
	 * This is to avoid duplicates in getReferences.
	 */
	private boolean containsExactFormula(SignedFormulaList aList, SignedFormula aSignedFormula) {
		for (SignedFormula listFormula : aList.getList()) {
			// Compare sign, formula AND label (if applicable)
			if (listFormula.toString().equals(aSignedFormula.toString())) {
				return true;
			}
		}
		return false;
	}

}
