/*
 * Created on 09/06/2004
 *
 */
package logic.signedFormulas;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import logic.formulas.FormulaFactory;
import logic.problem.Problem;
import parsers.ParserUser;
// import ConversorWagnerSATLIB.ConversorWagnerSATLIBLexer;
// import ConversorWagnerSATLIB.ConversorWagnerSATLIBParser;
import logicalSystems.ipl.IPLSignedFormulaFactory;


/**
 * Class that allows the creation of formulas from strings (using Wagner Dias's
 * syntax). Ex.: FormulaCreator fc = new FormulaCreator(); fc.parseString ("T
 * A-> B");
 */
public class SignedFormulaCreator {

	/** conversor wagner lexer and parser class names * */
	// "ConversorWagnerSATLIB.ConversorWagnerSATLIBLexer";
	private static final String CW_LEXER = "ConversorWagnerSATLIB.ConversorWagnerSATLIBLexer";

	// "ConversorWagnerSATLIB.ConversorWagnerSATLIBParser";
	private static final String CW_PARSER = "ConversorWagnerSATLIB.ConversorWagnerSATLIBParser";

	private SignedFormulaFactory _sff;

	private FormulaFactory _ff;

	private Problem _problem;

	private String _packageName;

	boolean _twoPhases = true;

	/**
	 * Creates a SignedFormulaCreator for a default lib dir.
	 * 
	 * @param packageName
	 */
	public SignedFormulaCreator(String packageName) {
		// For IPL, use IPLSignedFormulaFactory, which handles ContextFormulaLabel
		if ("ipl".equals(packageName)) {
			_sff = new IPLSignedFormulaFactory();
		} else {
			_sff = new SignedFormulaFactory();
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

		String s;

		if (_twoPhases) {

			ParserUser pu1 = new ParserUser();

			s = (String) pu1.parseString(CW_LEXER, CW_PARSER,
					signedFormulasAsString);
		} else {
			s = signedFormulasAsString;
		}

		ParserUser pu2 = new ParserUser();
		_problem = (Problem) pu2.parseString(
			_packageName + "." + _packageName + "Lexer",
			_packageName + "." + _packageName + "Parser",
			s
		);

		// Clone formulas from the parser's factory into our factory
		// For IPL: IPLSignedFormulaFactory.cloneAll() automatically converts to ContextFormulaLabel
		// For other logics: SignedFormulaFactory.cloneAll() copies normally
		_sff.cloneAll(_problem.getSignedFormulaFactory(), _ff);
		
		if ("ipl".equals(_packageName)) {
			cloneIPLContext();
		}

		return _problem;
	}

	/**
	 * Converts a string to a signed formula.
	 * 
	 * @param signedFormulaAsString
	 * @return
	 */
	public SignedFormula parseString(String signedFormulaAsString) {

		this.parseText(signedFormulaAsString);

		return (SignedFormula) _sff.getSignedFormulas().get(
				_problem.getSignedFormulaFactory().getLastSignedFormulaAdded()
						.toString());
	}

	public Problem parseFile(String completeFilename) {

		String s;
		if (_twoPhases) {
			ParserUser pu1 = new ParserUser();

			s = (String) pu1.parseFile(CW_LEXER, CW_PARSER, completeFilename);

			ParserUser pu2 = new ParserUser();
			_problem = (Problem) pu2.parseString(_packageName + "."
					+ _packageName + "Lexer", _packageName + "." + _packageName
					+ "Parser", s);
			
			// Clone formulas from the parser's factory into our factory
			// For IPL: IPLSignedFormulaFactory.cloneAll() automatically converts to ContextFormulaLabel
			// For other logics: SignedFormulaFactory.cloneAll() copies normally
			_sff.cloneAll(_problem.getSignedFormulaFactory(), _ff);
			
			if ("ipl".equals(_packageName)) {
				cloneIPLContext();
			}
		} else {
			ParserUser pu2 = new ParserUser();
			_problem = (Problem) pu2.parseFile(_packageName + "."
					+ _packageName + "Lexer", _packageName + "." + _packageName
					+ "Parser", completeFilename);

			// Clone formulas from the parser's factory into our factory
			// For IPL: IPLSignedFormulaFactory.cloneAll() automatically converts to ContextFormulaLabel
			// For other logics: SignedFormulaFactory.cloneAll() copies normally
			_sff.cloneAll(_problem.getSignedFormulaFactory(), _ff);
			
			if ("ipl".equals(_packageName)) {
				cloneIPLContext();
			}
		}

		_problem.setFilename(completeFilename);
		_problem.setName(completeFilename);

		return _problem;

	}

	public SignedFormulaFactory getSignedFormulaFactory() {
		return _sff;
	}

	public FormulaFactory getFormulaFactory() {
		return _ff;
	}

	private void cloneIPLContext() {
		if (_sff instanceof IPLSignedFormulaFactory) {
			IPLSignedFormulaFactory iplFactory = (IPLSignedFormulaFactory) _sff;
			_problem.setIPLContext(iplFactory.getContext());
			_problem.setSignedFormulaFactory(iplFactory);

			// Replace problem formulas with their ContextFormulaLabel versions.
			// The parser populates Problem.getFormulas() with plain FormulaLabel instances.
			// cloneAll() converts them to ContextFormulaLabel in the factory map, but
			// Problem.getFormulas() is not updated. Without this replacement, fillWith()
			// adds plain-FormulaLabel formulas to the proof tree, and when rules later
			// call FormulaLabel.getGreaterFormulaLabel() they get a plain label with no
			// context, so the relation c0 <= c1 (and any relation from an initial
			// formula's label) is never registered in the Context.
			SignedFormulaList formulasList = _problem.getFormulas();
			List<SignedFormula> originals = new ArrayList<>(formulasList.getList());
			while (formulasList.size() > 0) {
				formulasList.remove(0);
			}
			Map<String, SignedFormula> iplMap = iplFactory.getSignedFormulas();
			for (SignedFormula sf : originals) {
				SignedFormula iplVersion = iplMap.get(sf.toString());
				formulasList.add(iplVersion != null ? iplVersion : sf);
			}
		}
	}
	
}