/*
 * Created on 26/10/2005
 *
 */
package main.newstrategy.ipl;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import logic.formulas.CompositeFormula;
import logic.formulas.Formula;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaBuilder;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.SignedFormulaList;
import logicalSystems.ipl.IPLConnectives;
import logicalSystems.ipl.IPLProofTree;
import logicalSystems.ipl.IPLRules;
import logicalSystems.ipl.IPLSigns;
import main.newstrategy.ISimpleStrategy;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import main.strategy.ClassicalProofTree;
import main.strategy.applicator.IRuleApplicator;
import rules.NullRule;
import rules.Rule;
import rules.structures.IPLOnePremiseRuleList;
import rules.structures.OnePremiseRuleList;

/**
 * Applies one premise rules.
 * 
 * @author Adolfo Gustavo Serra Seca Neto
 * 
 */
public class IPLOnePremiseRuleApplicator implements IRuleApplicator {

    private static final IPLTracer tracer = IPLTracer.getInstance();

    private ISimpleStrategy strategy;

    private String ruleListName;

    /**
     * @param strategy
     * @param sfb
     */
    public IPLOnePremiseRuleApplicator(ISimpleStrategy strategy, String ruleListName) {
        super();
        this.strategy = strategy;
        this.ruleListName = ruleListName;
    }

    /*
     * (non-Javadoc)
     * 
     * @see main.strategy.applicator.IRuleApplicator#applyAll(main.strategy.
     * ClassicalProofTree, logic.signedFormulas.SignedFormulaBuilder)
     */
    public boolean applyAll(ClassicalProofTree proofTree, SignedFormulaBuilder sfb) {
        boolean hasApplied = false;

        int i = 0;
        // notice that I am using a non-recommended "i--"
        while (i < proofTree.getPBCandidates().size() && !proofTree.isClosed()) {

            // for each signed formula not used, if it accepts a one premise
            // rule, apply the rule and remove it form the list of candidates.

            SignedFormula sf = (SignedFormula) proofTree.getPBCandidates().get(i);

            if (chooseAndApplyOnePremiseRule(proofTree, sfb, sf)) {
                hasApplied = true;
                i--;
            }
            i++;
        }

        return hasApplied;
    }
    
    /**
     * Applies a one-premise rule to a single specific formula.
     * This method is used by the canonical algorithm implementation.
     * 
     * @param proofTree the proof tree
     * @param sfb the signed formula builder
     * @param sf the specific formula to process
     * @return true if a rule was applied, false otherwise
     */
    public boolean applySingle(ClassicalProofTree proofTree, SignedFormulaBuilder sfb, SignedFormula sf) {
        return chooseAndApplyOnePremiseRule(proofTree, sfb, sf);
    }

    private boolean chooseAndApplyOnePremiseRule(ClassicalProofTree proofTree, SignedFormulaBuilder sfb,
            SignedFormula sf) {
        boolean hasApplied = false;
        // Rule r = chooseOnePremiseRule(proofTree, sf);
        List<Rule> rules = getOnePremiseRuleList(proofTree, sf);

        for (Iterator<Rule> it = rules.iterator(); it.hasNext();) {
            if (hasApplied)
                break;
            // hasApplied = true;
            Rule r = it.next();
            
            // PROVISO DE TERMINACIÓN para regla F→
            // NO aplicar (F→) si existe T A : ch donde ch ≤ ci
            if (r == IPLRules.F_A_IMPLIES_B_TA_FB && shouldBlockFImpliesRule(proofTree, sf)) {
                continue; // Saltar esta regla (shouldBlockFImpliesRule ya loguea el motivo)
            }
            

            // Para T¬, generar conclusiones para TODAS las etiquetas mayores disponibles
            boolean isTNot = isTNotFormula(sf);
            
            // Para reglas normales (no T¬), verificar si ya intentamos aplicar esta regla a esta fórmula
            if (!isTNot && proofTree instanceof IPLProofTree) {
                IPLProofTree iplTree = (IPLProofTree) proofTree;
                
                // ✅ CORRECCIÓN: Todas las reglas (incluida F_NOT) deben trackear por fórmula + etiqueta
                // según el paper: "each rule can be applied at most once for each particular choice of ls-formulas as premises"
                // Una ls-formula incluye la etiqueta, por lo que F ¬p : c1 y F ¬p : c5 son instancias diferentes
                String baseRuleInstance = r.toString() + ":" + sf.toString();
                
                if (iplTree.wasRuleInstanceApplied(baseRuleInstance)) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logRuleBlocked(r.toString(), sf.toString(),
                                "rinstance exists: " + baseRuleInstance);
                    }
                    continue;
                }
                iplTree.registerRuleInstance(baseRuleInstance);
            }
            
            SignedFormulaList sfl;
            
            if (isTNot) {
                // T¬ es persistente: generar todas las conclusiones para etiquetas actuales
                sfl = generateAllTNotConclusions(proofTree, sfb, sf, r);
                if (IPLTracer.isEnabled()) {
                    tracer.logInfo("T¬ persistent: evaluating " + sfl.size()
                            + " conclusions for all greater labels");
                }
                
                // If ALL conclusions already exist, skip this rule application
                int existingCount = 0;
                for (int j = 0; j < sfl.size(); j++) {
                    if (proofTree.getNode(sfl.get(j)) != null) {
                        existingCount++;
                    }
                }
                
                if (existingCount == sfl.size() && sfl.size() > 0) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logInfo("T¬: all conclusions already exist, skipping");
                    }
                    continue;
                }
            } else {
                // Regla normal
                sfl = r.getPossibleConclusions(sfb.getSignedFormulaFactory(), sfb.getFormulaFactory(),
                        new SignedFormulaList(sf));
            }

            // TODO Translate: "Modificacao (ver se sfl!=null) necessaria PARA MCI
            // pois MCIRules.T_NOT_CONS não garantido ser aplicada"
            if (sfl != null && sfl.size() > 0) {
                boolean actuallyAddedFormula = false;

                for (int j = 0; j < sfl.size(); j++) {
                    SignedFormula newFormula = sfl.get(j);
                    
                    // Evitar duplicados
                    if (proofTree.getNode(newFormula) != null) {
                        if (IPLTracer.isEnabled()) {
                            tracer.logInfo("Conclusion already exists: " + newFormula);
                        }
                        continue;
                    }
                    
                    // Para T¬ (persistente), verificar rinstances de cada conclusión individual
                    // ya que puede generar múltiples conclusiones para diferentes etiquetas en diferentes momentos
                    if (isTNot && proofTree instanceof IPLProofTree) {
                        IPLProofTree iplTree = (IPLProofTree) proofTree;
                        String ruleInstance = createRuleInstanceKey(r.toString(), sf, newFormula);
                        if (iplTree.wasRuleInstanceApplied(ruleInstance)) {
                            if (IPLTracer.isEnabled()) {
                                tracer.logRuleBlocked("T_NOT", sf.toString(),
                                        "T¬ rinstance exists: " + ruleInstance);
                            }
                            continue; // No aplicar, ya fue aplicada
                        }
                        iplTree.registerRuleInstance(ruleInstance);
                    }
                    
                    // Usar SignedFormulaNode para compatibilidad con ClassicalProofTree
                    // El contenido puede ser LabelledFormula (con etiqueta) o SignedFormula regular
                    proofTree.addLast(new SignedFormulaNode(newFormula, SignedFormulaNodeState.NOT_ANALYSED,
                            strategy.createOrigin(r, proofTree.getNode(sf), null)));
                    
                    if (newFormula instanceof LabelledFormula) {
                        LabelledFormula lf = (LabelledFormula) newFormula;
                        if (IPLTracer.isEnabled()) {
                            tracer.logRuleApplied(r.toString(), sf.toString(), lf.toString());
                        }
                        // b* materialization (eager propagation) removed here.
                        // T-composite formulas at new labels are now selected lazily from b*
                        // in IPLCanonicalStrategyImplementation.selectUnanalyzedFormula(), per
                        // Algorithm 1: b* = extend(b) is built for completeness checking only.
                    }
                    
                    actuallyAddedFormula = true;
                }
                
                // Only mark as applied if we actually added new formulas
                if (actuallyAddedFormula) {
                    hasApplied = true;
                    // Mark ANALYSED unconditionally. Universal T¬ formulas are re-selected by
                    // selectUnanalyzedFormula when Def. 5.6 is unsatisfied for new accessible worlds.
                    proofTree.removeFromPBCandidates(sf, SignedFormulaNodeState.ANALYSED);
                }
            }

        }

        /*
         * if (r != NullRule.INSTANCE) { hasApplied = true;
         * 
         * SignedFormulaList sfl = r.getPossibleConclusions(sfb
         * .getSignedFormulaFactory(), sfb.getFormulaFactory(), new
         * SignedFormulaList(sf));
         * 
         * // TODO Translate: "Modificacao (ver se sfl!=null) necessaria PARA MCI //
         * pois MCIRules.T_NOT_CONS não garantido ser aplicada" if (sfl != null) {
         * 
         * proofTree.removeFromPBCandidates(sf, SignedFormulaNodeState.ANALYSED);
         * 
         * for (int j = 0; j < sfl.size(); j++) { proofTree.addLast(new
         * SignedFormulaNode(sfl.get(j), SignedFormulaNodeState.NOT_ANALYSED, strategy
         * .createOrigin(r, proofTree.getNode(sf), null))); } } else { return false; } }
         */
        return hasApplied;
    }

    private Rule chooseOnePremiseRule(ClassicalProofTree cpt, SignedFormula sf) {

        OnePremiseRuleList onePremiseRules = (OnePremiseRuleList) strategy.getMethod().getRules().get(ruleListName);

        if (sf.getFormula() instanceof CompositeFormula) {
            return onePremiseRules.get(sf.getSign(), ((CompositeFormula) sf.getFormula()).getConnective());
        }

        return NullRule.INSTANCE;

    }

    private List<Rule> getOnePremiseRuleList(ClassicalProofTree cpt, SignedFormula sf) {

        Object ruleListObject = strategy.getMethod().getRules().get(ruleListName);
        
        // Verificar que sea realmente un IPLOnePremiseRuleList
        if (!(ruleListObject instanceof IPLOnePremiseRuleList)) {
            return new ArrayList<Rule>();
        }
        
        IPLOnePremiseRuleList onePremiseRules = (IPLOnePremiseRuleList) ruleListObject;

        if (sf.getFormula() instanceof CompositeFormula) {
            return onePremiseRules.getMany(((CompositeFormula) sf.getFormula()).getConnective(), sf.getSign());
        }

        return new ArrayList<Rule>();

    }
    
    /**
     * Verifica el proviso de terminación para la regla F→.
     * 
     * Condición: NO aplicar (F→) a F A→B : ci si en la rama ya existe 
     * una fórmula T A : ch para cualquier constante ch tal que ch ≤ ci.
     * 
     * @param proofTree el árbol de prueba actual
     * @param sf la fórmula F A→B : ci a verificar
     * @return true si la regla debe ser bloqueada, false si puede aplicarse
     */
    private boolean shouldBlockFImpliesRule(ClassicalProofTree proofTree, SignedFormula sf) {
        // Verificar que sea F A→B
        if (!sf.getSign().equals(IPLSigns.FALSE)) {
            return false; // No es F, no bloquear
        }
        
        if (!(sf.getFormula() instanceof CompositeFormula)) {
            return false; // No es compuesta, no bloquear
        }
        
        CompositeFormula comp = (CompositeFormula) sf.getFormula();
        if (!comp.getConnective().equals(IPLConnectives.IMPLIES)) {
            return false; // No es →, no bloquear
        }
        
        // Es F A→B, verificar proviso
        if (!(sf instanceof LabelledFormula)) {
            return false; // Sin etiqueta, no podemos verificar
        }
        
        LabelledFormula lfMain = (LabelledFormula) sf;
        FormulaLabel ciLabel = lfMain.getLabel();
        
        // Obtener A (la subfórmula izquierda de A→B)
        Formula aFormula = comp.getImmediateSubformulas().get(0);
        
        Context context = getContextFromLabel(ciLabel);
        if (context == null) {
            return false; // Sin Context, no podemos verificar, no bloquear por seguridad
        }
        
        // ✅ EXTENSIÓN b* IMPLÍCITA: Buscar en b* (no solo en b)
        // Según el paper: "F → is applicable only when T A : ch does not occur 
        // for any ch ⪯ ci in the branch" - esto incluye fórmulas en b*
        if (!(proofTree instanceof IPLProofTree)) {
            return false; // Fallback: no bloquear
        }
        
        IPLProofTree iplTree = (IPLProofTree) proofTree;
        Set<SignedFormula> bStar = iplTree.extendBranch();
        
        // Buscar T A : ch en b*
        for (SignedFormula candidate : bStar) {
            // Buscar T A : ch
            if (candidate.getSign().equals(IPLSigns.TRUE) && 
                candidate.getFormula().equals(aFormula) &&
                candidate instanceof LabelledFormula) {
                
                LabelledFormula lfCandidate = (LabelledFormula) candidate;
                FormulaLabel chLabel = lfCandidate.getLabel();
                
                // Verificar que la etiqueta ch sea accesible
                if (!iplTree.isLabelAccessible(chLabel)) {
                    continue; // Saltar esta fórmula, su etiqueta no es accesible
                }
                
                // Verificar si ch ≤ ci
                boolean chEqualsCI = chLabel.equals(ciLabel);
                boolean chLowerOrEqualCI = context.isLowerOrEqualTo(chLabel, ciLabel);
                
                if (chEqualsCI || chLowerOrEqualCI) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logRuleBlocked("F_IMPLIES", sf.toString(),
                                "Proviso (b*): found T " + aFormula + " : " + chLabel + " where "
                                        + chLabel + " ≤ " + ciLabel);
                    }
                    return true; // BLOQUEAR la aplicación de F→
                }
            }
        }
        
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("Proviso (b*): no T " + aFormula + " : ch where ch ≤ " + ciLabel + " found");
        }
        return false; // No bloquear
    }
    
    
    /**
     * Obtiene el Context desde una FormulaLabel
     */
    private Context getContextFromLabel(FormulaLabel label) {
        if (label instanceof ContextFormulaLabel) {
            return ((ContextFormulaLabel) label).getContext();
        }
        return null;
    }
    
    /**
     * Returns true if sf is a T¬A formula (universal/γ-rule: T¬A:ci → ∀ cj ≥ ci : FA:cj ∈ b*).
     * These formulas generate conclusions for ALL accessible labels at once.
     * Re-selection is handled by selectUnanalyzedFormula via the Def. 5.6 check.
     */
    private boolean isTNotFormula(SignedFormula sf) {
        if (sf == null) return false;
        
        // Verificar que sea T-signed
        if (!sf.getSign().equals(IPLSigns.TRUE)) {
            return false;
        }
        
        // Verificar que la fórmula sea una negación (¬A)
        Formula formula = sf.getFormula();
        if (formula instanceof CompositeFormula) {
            CompositeFormula comp = (CompositeFormula) formula;
            return comp.getConnective().equals(IPLConnectives.NOT);
        }
        
        return false;
    }
    
    /**
     * Genera TODAS las conclusiones posibles para T¬A : ci aplicando sobre todas las etiquetas cj donde ci ≤ cj
     */
    private SignedFormulaList generateAllTNotConclusions(ClassicalProofTree proofTree, 
                                                         SignedFormulaBuilder sfb,
                                                         SignedFormula sf, 
                                                         Rule rule) {
        SignedFormulaList allConclusions = new SignedFormulaList();
        
        if (!(sf instanceof LabelledFormula)) {
            return allConclusions;
        }
        
        LabelledFormula lf = (LabelledFormula) sf;
        FormulaLabel ciLabel = lf.getLabel();
        Context context = getContextFromLabel(ciLabel);
        
        if (context == null) {
            return allConclusions;
        }
        
        // Obtener el IPLProofTree para verificar accesibilidad de etiquetas
        IPLProofTree iplTree = (proofTree instanceof IPLProofTree) ? (IPLProofTree) proofTree : null;
        
        // Para cada etiqueta cj en el contexto donde ci ≤ cj
        for (FormulaLabel cjLabel : context.getLabels()) {
            // FILTRO: Solo considerar etiquetas accesibles en la rama actual
            if (iplTree != null && !iplTree.isLabelAccessible(cjLabel)) {
                if (IPLTracer.isEnabled()) {
                    tracer.logInfo("T¬: label " + cjLabel + " not accessible in branch "
                            + iplTree.getBranchId() + ", skipping");
                }
                continue;
            }
            
            if (ciLabel.equals(cjLabel) || context.isLowerOrEqualTo(ciLabel, cjLabel)) {
                // Crear F A : cj
                SignedFormula baseSf = lf.getSignedFormula();
                if (!(baseSf.getFormula() instanceof CompositeFormula)) {
                    continue;
                }
                
                CompositeFormula comp = (CompositeFormula) baseSf.getFormula();
                Formula aFormula = comp.getImmediateSubformulas().get(0);
                
                // Crear F A : cj
                SignedFormula falseA = sfb.createSignedFormula(IPLSigns.FALSE, aFormula);
                LabelledFormula conclusion = new LabelledFormula(cjLabel, falseA);
                
                allConclusions.add(conclusion);
            }
        }
        
        return allConclusions;
    }
    
    /**
     * Crea una clave única para identificar una instancia de regla de una premisa.
     * 
     * @param ruleName nombre de la regla
     * @param premise la premisa (fórmula principal)
     * @param conclusion la conclusión generada
     * @return clave única para la instancia de regla
     */
    private String createRuleInstanceKey(String ruleName, SignedFormula premise, SignedFormula conclusion) {
        return ruleName + ":" + premise.toString() + "→" + conclusion.toString();
    }
    
    /**
     * Propagates T-signed composite formulas to a new label by Kripke monotonicity.
     * 
     * [REMOVED] Eager propagation of T-composite formulas to new labels.
     *
     * This method was called after F→₁ / F¬ created a new label cj to eagerly
     * copy T(A∧B):ci, T(A→B):ci, ... into b at cj.
     *
     * Per Algorithm 1 (§5 of the paper), b* = extend(b) is computed AFTER each
     * rule application for the purpose of completeness checking (Definition 5.6).
     * b* is NOT materialized into b.
     *
     * Replacement: IPLCanonicalStrategyImplementation.findAndMaterializeVirtualBStarFormula()
     * lazily selects T-composite formulas from b* and materializes them on demand,
     * which is equivalent but faithful to the algorithm structure.
     */
    // private void propagateCompositeTFormulasForNewLabel(...) { REMOVED }

}