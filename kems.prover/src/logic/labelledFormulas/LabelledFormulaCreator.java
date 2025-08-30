package logic.labelledFormulas;

import logic.formulas.FormulaFactory;
import logic.problem.Problem;
import logic.signedFormulas.SignedFormula;
import logic.labelledFormulas.FormulaLabel;
import parsers.ParserUser;
import logicalSystems.ipl.IPLSignedFormulaFactory;

public class LabelledFormulaCreator {

	private LabelledFormulaFactory _lff;

	private FormulaFactory _ff;

	private Problem _problem;

	private String _packageName;

	boolean _twoPhases = false;

	/**
	 * Creates a LabelledFormulaCreator for a default lib dir.
	 * 
	 * @param packageName
	 */
	public LabelledFormulaCreator(String packageName) {
		// Para IPL, usar IPLSignedFormulaFactory que maneja ContextFormulaLabel
		if ("ipl".equals(packageName)) {
			_lff = new IPLSignedFormulaFactory();
		} else {
			_lff = new LabelledFormulaFactory();
		}
		_ff = new FormulaFactory();
		_packageName = packageName;
	}

	public void setTwoPhases(boolean option) {
		_twoPhases = option;
	}

	private String removeUselessCharacters(String s) {
		return s.trim();
	}

	public Problem parseText(String signedFormulasAsString) {
		signedFormulasAsString = removeUselessCharacters(signedFormulasAsString);
	
		ParserUser pu1 = new ParserUser();
	
		_problem = (Problem) pu1.parseString(
			_packageName + "." + _packageName + "Lexer",
			_packageName + "." + _packageName + "Parser",
			signedFormulasAsString);
	

		
		// Clone all formulas from the problem to our factory
		if (_problem.getSignedFormulaFactory() instanceof LabelledFormulaFactory) {
			LabelledFormulaFactory problemLff = (LabelledFormulaFactory) _problem.getSignedFormulaFactory();
			_lff.cloneAll(problemLff, _ff);
		} else {
			// If the problem doesn't have a LabelledFormulaFactory, create one
			_lff.cloneAll(_problem.getSignedFormulaFactory(), _ff);
		}
	
		return _problem;
	}

	/**
	 * Converts a string to a labelled formula.
	 * 
	 * @param labelledFormulaAsString
	 * @return
	 */
	public LabelledFormula parseString(String labelledFormulaAsString) {

		this.parseText(labelledFormulaAsString);

		// Get the last signed formula added and convert it to a labelled formula
		SignedFormula lastSignedFormula = _problem.getSignedFormulaFactory().getLastSignedFormulaAdded();
		if (lastSignedFormula != null) {

			
			// Create a new labelled formula with the last signed formula
			// Preserve the label from the parsed formula
			FormulaLabel label = lastSignedFormula.getLabel();
			if (label == null || label.equals(FormulaLabel.empty())) {
				// Para IPL, usar ContextFormulaLabel desde la factory
				if (_lff instanceof IPLSignedFormulaFactory) {
					IPLSignedFormulaFactory iplFactory = (IPLSignedFormulaFactory) _lff;
					label = iplFactory.getContext().getNewFormulaLabel(); // ContextFormulaLabel
				} else {
					label = FormulaLabel.constant(0); // Fallback para otras lógicas
				}
			}
			return _lff.createLabelledFormula(lastSignedFormula);
		}
		
		return null;
	}

	public Problem parseFile(String completeFilename) {

		String s;
		if (_twoPhases) {
			ParserUser pu1 = new ParserUser();

			s = (String) pu1.parseFile(_packageName + "." + _packageName + "Lexer", _packageName + "." + _packageName + "Parser", completeFilename);

			ParserUser pu2 = new ParserUser();
			_problem = (Problem) pu2.parseString(_packageName + "."
					+ _packageName + "Lexer", _packageName + "." + _packageName
					+ "Parser", s);
			if (_problem.getSignedFormulaFactory() instanceof LabelledFormulaFactory) {
				LabelledFormulaFactory problemLff = (LabelledFormulaFactory) _problem.getSignedFormulaFactory();
				_lff.cloneAll(problemLff, _ff);
			} else {
				_lff.cloneAll(_problem.getSignedFormulaFactory(), _ff);
			}
		} else {
			ParserUser pu2 = new ParserUser();
			_problem = (Problem) pu2.parseFile(_packageName + "."
					+ _packageName + "Lexer", _packageName + "." + _packageName
					+ "Parser", completeFilename);

			if (_problem.getSignedFormulaFactory() instanceof LabelledFormulaFactory) {
				LabelledFormulaFactory problemLff = (LabelledFormulaFactory) _problem.getSignedFormulaFactory();
				_lff.cloneAll(problemLff, _ff);
			} else {
				_lff.cloneAll(_problem.getSignedFormulaFactory(), _ff);
			}
		}

		_problem.setFilename(completeFilename);
		_problem.setName(completeFilename);

		return _problem;

	}

	public LabelledFormulaFactory getLabelledFormulaFactory() {
		return _lff;
	}

	public FormulaFactory getFormulaFactory() {
		return _ff;
	}

	// Keep for backward compatibility
	public LabelledFormulaFactory getSignedFormulaFactory() {
		return _lff;
	}

}