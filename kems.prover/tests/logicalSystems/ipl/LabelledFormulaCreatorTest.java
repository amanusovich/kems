package logicalSystems.ipl;

import org.junit.Test;
import org.junit.Before;
import static org.junit.Assert.*;

import logic.labelledFormulas.LabelledFormulaCreator;
import logic.labelledFormulas.LabelledFormula;

public class LabelledFormulaCreatorTest {

	private LabelledFormulaCreator sfc;

	@Before
	public void setUp() {
		sfc = new LabelledFormulaCreator("ipl");
	}

	@Test
	public void testParseString() {
		LabelledFormula lf = sfc.parseString("T A1 c0");
		assertNotNull(lf);
		assertEquals("T A1 c0", lf.toString());
	}

	@Test
	public void testParseStringWithComplexFormula() {
		LabelledFormula lf = sfc.parseString("F *(P Q) c1");
		assertNotNull(lf);
		assertEquals("F (P&Q) c1", lf.toString());
	}

	@Test
	public void testParseStringWithImplication() {
		LabelledFormula lf = sfc.parseString("T ->(A1 B1) c2");
		assertNotNull(lf);
		assertEquals("T (A1->B1) c2", lf.toString());
	}

	@Test
	public void testParseStringWithNegation() {
		LabelledFormula lf = sfc.parseString("F -(*(P Q)) c3");
		assertNotNull(lf);
		assertEquals("F !(P&Q) c3", lf.toString());
	}

	@Test
	public void testParseStringWithConstants() {
		LabelledFormula lf1 = sfc.parseString("T TOP c4");
		assertNotNull(lf1);
		assertEquals("T TOP c4", lf1.toString());

		LabelledFormula lf2 = sfc.parseString("F BOT c5");
		assertNotNull(lf2);
		assertEquals("F BOTTOM c5", lf2.toString());
	}

	@Test
	public void testParseStringWithDisjunction() {
		LabelledFormula lf = sfc.parseString("T +(P Q) x0");
		assertNotNull(lf);
		assertEquals("T (P|Q) x0", lf.toString());
	}

	@Test
	public void testParseStringWithXOR() {
		LabelledFormula lf = sfc.parseString("F %(P Q) x1");
		assertNotNull(lf);
		assertEquals("F (P+Q) x1", lf.toString());
	}

	@Test
	public void testParseStringWithComplexExpression() {
		LabelledFormula lf = sfc.parseString("T +(*(A C) C) x2");
		assertNotNull(lf);
		assertEquals("T ((A&C)|C) x2", lf.toString());
	}

	@Test
	public void testParseStringWithBIImplication() {
		LabelledFormula lf = sfc.parseString("F <=>(A B) x3");
		assertNotNull(lf);
		assertEquals("F (A<=>B) x3", lf.toString());
	}

	@Test
	public void testParseStringWithNestedExpressions() {
		LabelledFormula lf = sfc.parseString("T -(*(A +(B C))) c6");
		assertNotNull(lf);
		assertEquals("T !(A&(B|C)) c6", lf.toString());
	}

	@Test
	public void testParseStringWithMultipleOperators() {
		LabelledFormula lf = sfc.parseString("F *(->(P Q) +(R S)) x4");
		assertNotNull(lf);
		assertEquals("F ((P->Q)&(R|S)) x4", lf.toString());
	}

	@Test
	public void testParseStringWithSimpleVariable() {
		LabelledFormula lf = sfc.parseString("T X c7");
		assertNotNull(lf);
		assertEquals("T X c7", lf.toString());
	}

	@Test
	public void testParseStringWithMultipleVariables() {
		LabelledFormula lf = sfc.parseString("F *(X Y) x5");
		assertNotNull(lf);
		assertEquals("F (X&Y) x5", lf.toString());
	}
}
