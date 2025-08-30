package logicalSystems.ipl;

import static org.junit.Assert.*;

import java.util.Collection;

import logic.labelledFormulas.LabelledFormulaCreator;
import org.junit.Before;
import org.junit.Test;

import logic.formulas.Formula;
import logic.formulas.FormulaFactory;
import logic.labelledFormulas.LabelledFormula;
import logic.labelledFormulas.LabelledFormulaFactory;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaFactory;
import logic.signedFormulas.SignedFormulaList;
import logic.logicalSystem.ILogicalSystem;
import logicalSystems.ipl.IPLSigns;
import rules.IRule;
import rules.structures.IRulesStructure;

/**
 * Integration tests for IPL (Intuitionistic Propositional Logic) system.
 * These tests verify that the complete IPL system works correctly,
 * including rules, formulas, and logical operations.
 */
public class IPLIntegrationTest {

    private ILogicalSystem iplSystem;
    private FormulaFactory ff;
    private SignedFormulaFactory sff;
    private LabelledFormulaFactory lff;
    
    // Test formulas
    private Formula p, q, r;
    private Formula notP, notQ, notR;
    private Formula pAndQ, pOrQ, pImpliesQ, pBiimpliesQ;
    private Formula complexFormula1, complexFormula2;

    private LabelledFormulaCreator sfc;

    @Before
    public void setUp() {
        sfc = new LabelledFormulaCreator("ipl");
        // Initialize IPL system with extended signature to include BIIMPLIES
        iplSystem = new IPLLogicSystem(
            IPLSignatureFactory.getInstance().getNormalBSignature(),
            new IPLRulesStructureBuilder()
        );
        
        // Initialize factories
        ff = new FormulaFactory();
        sff = new SignedFormulaFactory();
        lff = new LabelledFormulaFactory();
        
        // Create atomic formulas
        p = ff.createAtomicFormula("P");
        q = ff.createAtomicFormula("Q");
        r = ff.createAtomicFormula("R");
        
        // Create negations
        notP = ff.createCompositeFormula(IPLConnectives.NOT, p);
        notQ = ff.createCompositeFormula(IPLConnectives.NOT, q);
        notR = ff.createCompositeFormula(IPLConnectives.NOT, r);
        
        // Create binary connectives
        pAndQ = ff.createCompositeFormula(IPLConnectives.AND, p, q);
        pOrQ = ff.createCompositeFormula(IPLConnectives.OR, p, q);
        pImpliesQ = ff.createCompositeFormula(IPLConnectives.IMPLIES, p, q);
        pBiimpliesQ = ff.createCompositeFormula(IPLConnectives.BIIMPLIES, p, q);
        
        // Create complex formulas
        complexFormula1 = ff.createCompositeFormula(IPLConnectives.AND, 
            ff.createCompositeFormula(IPLConnectives.OR, p, q),
            ff.createCompositeFormula(IPLConnectives.NOT, 
                ff.createCompositeFormula(IPLConnectives.AND, p, q))
        );
        
        complexFormula2 = ff.createCompositeFormula(IPLConnectives.IMPLIES,
            ff.createCompositeFormula(IPLConnectives.AND, p, q),
            ff.createCompositeFormula(IPLConnectives.OR, p, q)
        );
    }

    @Test
    public void testIPLSystemInitialization() {
        // Test that IPL system is properly initialized
        assertNotNull("IPL system should not be null", iplSystem);
        assertNotNull("IPL signature should not be null", iplSystem.getSignature());
        assertNotNull("IPL rules structure should not be null", iplSystem.getRulesStructure());
        
        // Test that IPL system has rules
        Collection<IRule> rules = iplSystem.getRules();
        assertNotNull("IPL rules should not be null", rules);
        assertFalse("IPL should have rules", rules.isEmpty());
        
        // Test that IPL system has connectives
        assertNotNull("IPL connectives should not be null", iplSystem.getConnectives());
        assertFalse("IPL should have connectives", iplSystem.getConnectives().isEmpty());
    }

    @Test
    public void testIPLConnectives() {
        // Test that all IPL connectives are available
        assertNotNull("IPL AND connective should exist", 
            iplSystem.getConnective(IPLSignatureFactory.AND));
        assertNotNull("IPL OR connective should exist", 
            iplSystem.getConnective(IPLSignatureFactory.OR));
        assertNotNull("IPL NOT connective should exist", 
            iplSystem.getConnective(IPLSignatureFactory.NOT));
        assertNotNull("IPL IMPLIES connective should exist", 
            iplSystem.getConnective(IPLSignatureFactory.IMPLIES));
        assertNotNull("IPL BIIMPLIES connective should exist", 
            iplSystem.getConnective(IPLSignatureFactory.BIIMPLIES));
    }

    @Test
    public void testFormulaCreationAndLabeling() {
        // Test that formulas can be created and labeled using LabelledFormulaCreator
        LabelledFormula labeledP = sfc.parseString("T P c0");
        
        assertNotNull("Labeled formula should not be null", labeledP);
        assertEquals("Formula should have correct sign", IPLSigns.TRUE, labeledP.getSign());
        assertEquals("Formula should have correct content", p, labeledP.getFormula());
        assertNotNull("Formula should have a label", labeledP.getLabel());
    }

    @Test
    public void testIPLRulesStructure() {
        IRulesStructure rulesStructure = iplSystem.getRulesStructure();
        
        // Test that rules structure contains expected rule lists
        assertNotNull("One premise rules should exist", 
            rulesStructure.get(IPLRuleStructures.ONE_PREMISE_RULE_LIST));
        assertNotNull("Two premise rules should exist", 
            rulesStructure.get(IPLRuleStructures.TWO_PREMISE_RULE_LIST));
        assertNotNull("PB rules should exist", 
            rulesStructure.get(IPLRuleStructures.PB_RULE_LIST));
    }

    @Test
    public void testBasicIPLRules() {
        // Test F_OR rule (Rule 1)
        testF_OR_Rule();
        
        // Test T_AND rule (Rule 2)
        testT_AND_Rule();
        
        // Test T_NOT rule (Rule 5)
        testT_NOT_Rule();
    }

    private void testF_OR_Rule() {
        // Test F_OR: F(P ∨ Q) → F(P), F(Q)
        LabelledFormula main = sfc.parseString("F +(P Q) c0");
        
        SignedFormulaList premises = new SignedFormulaList();
        premises.add(main);
        
        SignedFormulaList conclusions = IPLRules.F_OR.getPossibleConclusions(lff, sff, ff, premises);
        
        assertNotNull("Conclusions should not be null", conclusions);
        assertEquals("Should have 2 conclusions", 2, conclusions.size());
        
        // Both conclusions should have FALSE sign
        assertEquals("First conclusion should have FALSE sign", IPLSigns.FALSE, conclusions.get(0).getSign());
        assertEquals("Second conclusion should have FALSE sign", IPLSigns.FALSE, conclusions.get(1).getSign());
        
        // Both conclusions should have the same label as the premise
        assertEquals("First conclusion should have same label", main.getLabel(), conclusions.get(0).getLabel());
        assertEquals("Second conclusion should have same label", main.getLabel(), conclusions.get(1).getLabel());
    }

    private void testT_AND_Rule() {
        // Test T_AND: T(P ∧ Q) → T(P), T(Q)
        LabelledFormula main = sfc.parseString("T *(P Q) c0");
        
        SignedFormulaList premises = new SignedFormulaList();
        premises.add(main);
        
        SignedFormulaList conclusions = IPLRules.T_AND.getPossibleConclusions(lff, sff, ff, premises);

        assertNotNull("Conclusions should not be null", conclusions);
        assertEquals("Should have 2 conclusions", 2, conclusions.size());
        
        // Both conclusions should have TRUE sign
        assertEquals("First conclusion should have TRUE sign", IPLSigns.TRUE, conclusions.get(0).getSign());
        assertEquals("Second conclusion should have TRUE sign", IPLSigns.TRUE, conclusions.get(1).getSign());
        
        // Both conclusions should have same label as the premise
        assertEquals("First conclusion should have same label", main.getLabel(), conclusions.get(0).getLabel());
        assertEquals("Second conclusion should have same label", main.getLabel(), conclusions.get(1).getLabel());
    }

    private void testT_NOT_Rule() {
        // Test T_NOT: T(¬(P ∨ Q)) → T(¬P), T(¬Q)
        LabelledFormula main = sfc.parseString("T -(+(P Q)) c0");
        
        SignedFormulaList premises = new SignedFormulaList();
        premises.add(main);
        
        // Get conclusions using the rule
        SignedFormulaList conclusions = IPLRules.T_NOT_A_OR_B.getPossibleConclusions(lff, sff, ff, premises);
        
        assertNotNull("Conclusions should not be null", conclusions);
        assertEquals("Should have 2 conclusions", 2, conclusions.size());
        
        // Both conclusions should have TRUE sign
        assertEquals("First conclusion should have TRUE sign", IPLSigns.TRUE, conclusions.get(0).getSign());
        assertEquals("Second conclusion should have TRUE sign", IPLSigns.TRUE, conclusions.get(1).getSign());
    }

    @Test
    public void testComplexFormulaOperations() {
        // Test operations on complex formulas
        // complexFormula1 = (P ∨ Q) ∧ ¬(P ∧ Q)
        LabelledFormula labeledComplex1 = sfc.parseString("T *(+(P Q) -(*(P Q))) c0");
        
        assertNotNull("Complex labeled formula should not be null", labeledComplex1);
        assertEquals("Complex formula should have correct sign", IPLSigns.TRUE, labeledComplex1.getSign());
        assertEquals("Complex formula should have correct content", complexFormula1, labeledComplex1.getFormula());
    }

    @Test
    public void testFormulaEquality() {
        // Test that equivalent formulas are equal
        LabelledFormula labeledP1 = sfc.parseString("T P c0");
        LabelledFormula labeledP2 = sfc.parseString("T P c0");
        
        assertEquals("Equivalent formulas should be equal", labeledP1, labeledP2);
    }

    @Test
    public void testLabelManagement() {
        // Test that labels are properly managed
        LabelledFormula labeledP = sfc.parseString("T P c0");
        LabelledFormula labeledQ = sfc.parseString("T Q c1");
        
        assertNotNull("First formula should have label", labeledP.getLabel());
        assertNotNull("Second formula should have label", labeledQ.getLabel());
        assertNotEquals("Different formulas should have different labels", 
            labeledP.getLabel(), labeledQ.getLabel());
    }

    @Test
    public void testIPLSystemCompleteness() {
        // Test that IPL system can handle all basic logical operations
        Collection<IRule> rules = iplSystem.getRules();
        
        // Verify that we have rules for all major connectives
        boolean hasAndRule = false, hasOrRule = false, hasNotRule = false, hasImpliesRule = false;
        
        for (IRule rule : rules) {
            String ruleName = rule.toString();
            if (ruleName.contains("AND")) hasAndRule = true;
            if (ruleName.contains("OR")) hasOrRule = true;
            if (ruleName.contains("NOT")) hasNotRule = true;
            if (ruleName.contains("IMPLIES")) hasImpliesRule = true;
        }
        
        assertTrue("IPL should have AND rules", hasAndRule);
        assertTrue("IPL should have OR rules", hasOrRule);
        assertTrue("IPL should have NOT rules", hasNotRule);
        assertTrue("IPL should have IMPLIES rules", hasImpliesRule);
    }
}
    