/*
 * Created on 09/06/2004
 *
 */
package logic.signedFormulas;

import java.util.ArrayList;
import java.util.List;

import logic.formulas.FormulaFactory;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
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
		// Para IPL, usar IPLSignedFormulaFactory que maneja ContextFormulaLabel
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
		_problem = (Problem) pu2.parseString(_packageName + "." + _packageName
				+ "Lexer", _packageName + "." + _packageName + "Parser", s);

		// Para IPL, necesitamos que el Problem use nuestra LabelledFormulaFactory
		_sff.cloneAll(_problem.getSignedFormulaFactory(), _ff);
		
		// CRÍTICO: Reemplazar la factory del Problem con la nuestra (especialmente para IPL)
		if ("ipl".equals(_packageName)) {
			replaceFormulaFactory(_problem);
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
			_sff.cloneAll(_problem.getSignedFormulaFactory(), _ff);
			
			// CRÍTICO: Reemplazar la factory del Problem con la nuestra (especialmente para IPL)
			if ("ipl".equals(_packageName)) {
				replaceFormulaFactory(_problem);
			}
		} else {
			ParserUser pu2 = new ParserUser();
			_problem = (Problem) pu2.parseFile(_packageName + "."
					+ _packageName + "Lexer", _packageName + "." + _packageName
					+ "Parser", completeFilename);

			_sff.cloneAll(_problem.getSignedFormulaFactory(), _ff);
			
			// CRÍTICO: Reemplazar la factory del Problem con la nuestra (especialmente para IPL)
			if ("ipl".equals(_packageName)) {
				replaceFormulaFactory(_problem);
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
	
	/**
	 * Reemplaza la SignedFormulaFactory del Problem con la nuestra.
	 * Esto es crítico para IPL donde necesitamos LabelledFormulaFactory con Context compartido.
	 */
	private void replaceFormulaFactory(Problem problem) {
		// Crear Context si no existe
		if (!problem.hasIPLContext()) {
			problem.setIPLContext(new logic.labelledFormulas.Context());
			System.out.println("✅ IPL: Context creado para el Problem");
		}
		
		// Crear IPLSignedFormulaFactory con el Context del Problem
		IPLSignedFormulaFactory iplFactory = new IPLSignedFormulaFactory(problem.getIPLContext());
		
		// ✅ CRÍTICO: Convertir todas las fórmulas existentes a usar ContextFormulaLabel
		List<SignedFormula> originalFormulas = new ArrayList<SignedFormula>(problem.getFormulas().getList());
		SignedFormulaList formulasList = problem.getFormulas();
		
		// Limpiar y reconstruir la lista
		while (formulasList.size() > 0) {
			formulasList.remove(0); // Remover todas las fórmulas
		}
		
		for (SignedFormula originalFormula : originalFormulas) {
			FormulaLabel originalLabel = originalFormula.getLabel();
			
			// Crear ContextFormulaLabel equivalente
			ContextFormulaLabel contextLabel = new ContextFormulaLabel(
				problem.getIPLContext(), 
				originalLabel.getIndex()
			);
			problem.getIPLContext().addElement(contextLabel);
			
			// Crear nueva LabelledFormula con ContextFormulaLabel
			LabelledFormula newLabelledFormula = iplFactory.createLabelledFormula(
				contextLabel,
				originalFormula
			);
			
			formulasList.add(newLabelledFormula);
			System.out.println("🔄 Converted " + originalLabel + " (" + originalLabel.getClass().getSimpleName() + ") → " + contextLabel + " (ContextFormulaLabel)");
		}
		
		problem.setSignedFormulaFactory(iplFactory);
		_sff = iplFactory;

		System.out.println("✅ IPL: " + originalFormulas.size() + " fórmulas convertidas a ContextFormulaLabel");
	}

}