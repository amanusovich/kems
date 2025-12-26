/*
 * Created on 26/10/2005
 *
 */
package main.newstrategy.ipl;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import logic.formulas.CompositeFormula;
import logic.formulas.Formula;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaBuilder;
import logic.signedFormulas.SignedFormulaFactory;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.SignedFormulaList;
import logicalSystems.ipl.IPLConnectives;
import logicalSystems.ipl.IPLProofTree;
import logicalSystems.ipl.IPLRules;
import logicalSystems.ipl.IPLSigns;
import logic.labelledFormulas.LabelledFormulaFactory;
import main.newstrategy.ISimpleStrategy;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import main.proofTree.iterator.IProofTreeVeryBasicIterator;
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

            // System.err.println(sf);
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

        System.out.println("hey");

        for (Iterator<Rule> it = rules.iterator(); it.hasNext();) {
            if (hasApplied)
                break;
            // hasApplied = true;
            Rule r = it.next();
            
            // PROVISO DE TERMINACIÓN para regla F→
            // NO aplicar (F→) si existe T A : ch donde ch ≤ ci
            if (r == IPLRules.F_A_IMPLIES_B_TA_FB && shouldBlockFImpliesRule(proofTree, sf)) {
                System.out.println("🛑 Proviso de Terminación: Bloqueando aplicación de F→ para " + sf);
                continue; // Saltar esta regla, no aplicarla
            }

            // Para T¬, generar conclusiones para TODAS las etiquetas mayores disponibles
            boolean isTNot = isTNotFormula(sf);
            
            // Para reglas normales (no T¬), verificar si ya intentamos aplicar esta regla a esta fórmula
            if (!isTNot && proofTree instanceof IPLProofTree) {
                IPLProofTree iplTree = (IPLProofTree) proofTree;
                
                // Para reglas que generan nuevas etiquetas (como F_NOT), rastrear por estructura de fórmula
                // sin incluir la etiqueta, para evitar loops infinitos
                String baseRuleInstance;
                if (r == IPLRules.F_NOT) {
                    // F_NOT genera nuevas etiquetas, así que rastreamos solo por signo + fórmula
                    baseRuleInstance = r.toString() + ":" + getFormulaStructureKey(sf);
                } else {
                    // Para otras reglas, incluir la etiqueta en el rastreo
                    baseRuleInstance = r.toString() + ":" + sf.toString();
                }
                
                if (iplTree.wasRuleInstanceApplied(baseRuleInstance)) {
                    System.out.println("⏭️ Regla de 1 premisa ya aplicada a esta fórmula: " + baseRuleInstance);
                    continue;
                }
                // Registrar que intentamos aplicar esta regla a esta fórmula
                iplTree.registerRuleInstance(baseRuleInstance);
                System.out.println("📝 Registrado intento de regla de 1 premisa: " + baseRuleInstance);
            }
            
            SignedFormulaList sfl;
            
            if (isTNot) {
                // T¬ es persistente: generar todas las conclusiones para etiquetas actuales
                sfl = generateAllTNotConclusions(proofTree, sfb, sf, r);
                System.out.println("🔄 T¬ persistente: Evaluando " + sfl.size() + " conclusiones para todas las etiquetas mayores");
                
                // Si TODAS ya existen, no hacer nada (pero NO marcar como ANALYSED)
                int existingCount = 0;
                for (int j = 0; j < sfl.size(); j++) {
                    if (proofTree.getNode(sfl.get(j)) != null) {
                        existingCount++;
                    }
                }
                
                if (existingCount == sfl.size() && sfl.size() > 0) {
                    System.out.println("⏭️ T¬: Todas las conclusiones ya existen para etiquetas actuales, saltando");
                    continue; // Saltar esta regla, pero NO marcarla como ANALYSED
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
                        System.out.println("⏭️ Conclusión ya existe: " + newFormula);
                        continue;
                    }
                    
                    // Para T¬ (persistente), verificar rinstances de cada conclusión individual
                    // ya que puede generar múltiples conclusiones para diferentes etiquetas en diferentes momentos
                    if (isTNot && proofTree instanceof IPLProofTree) {
                        IPLProofTree iplTree = (IPLProofTree) proofTree;
                        String ruleInstance = createRuleInstanceKey(r.toString(), sf, newFormula);
                        System.out.println("DEBUG: Checking one-premise rinstance: " + ruleInstance);
                        if (iplTree.wasRuleInstanceApplied(ruleInstance)) {
                            System.out.println("⏭️ Instancia de regla T¬ ya aplicada (rinstances): " + ruleInstance);
                            continue; // No aplicar, ya fue aplicada
                        }
                        // Registrar la instancia de regla
                        iplTree.registerRuleInstance(ruleInstance);
                        System.out.println("📝 Registrado rinstance (T¬): " + ruleInstance);
                    }
                    
                    // Usar SignedFormulaNode para compatibilidad con ClassicalProofTree
                    // El contenido puede ser LabelledFormula (con etiqueta) o SignedFormula regular
                    proofTree.addLast(new SignedFormulaNode(newFormula, SignedFormulaNodeState.NOT_ANALYSED,
                            strategy.createOrigin(r, proofTree.getNode(sf), null)));
                    
                    // Debug: Verificar si la fórmula tiene etiqueta
                    if (newFormula instanceof LabelledFormula) {
                        LabelledFormula lf = (LabelledFormula) newFormula;
                        System.out.println("✅ IPL: Fórmula con etiqueta creada: " + lf.toString());
                    }
                    
                    actuallyAddedFormula = true;
                }
                
                // Only mark as applied if we actually added new formulas
                if (actuallyAddedFormula) {
                    hasApplied = true;
                    // Solo las reglas normales se marcan como ANALYSED
                    // T¬ NUNCA se marca como ANALYSED (permanece disponible para futuras etiquetas)
                    if (!isTNot) {
                        proofTree.removeFromPBCandidates(sf, SignedFormulaNodeState.ANALYSED);
                    }
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
            System.err.println("Error: Expected IPLOnePremiseRuleList but got " + 
                             (ruleListObject != null ? ruleListObject.getClass().getName() : "null"));
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
        
        // Buscar en la rama si existe T A : ch donde ch ≤ ci
        // Según el paper: "F → is applicable only when T A : ch does not occur 
        // for any ch ⪯ ci in the branch"
        IProofTreeVeryBasicIterator it = proofTree.getTopDownIterator();
        
        Context context = getContextFromLabel(ciLabel);
        if (context == null) {
            System.out.println("⚠️ Proviso: No se pudo obtener Context para verificar");
            return false; // Sin Context, no podemos verificar, no bloquear por seguridad
        }
        
        // DEBUG: Mostrar el contenido del Context
        System.out.println("🔍 DEBUG Proviso: Context tiene " + context.getLabels().size() + " etiquetas: " + context.getLabels());
        System.out.println("🔍 DEBUG Proviso: Verificando si existe T " + aFormula + " : ch donde ch ≤ " + ciLabel);
        
        while (it.hasNext()) {
            SignedFormulaNode sfn = (SignedFormulaNode) it.next();
            SignedFormula candidate = (SignedFormula) sfn.getContent();
            
            // Buscar T A : ch
            if (candidate.getSign().equals(IPLSigns.TRUE) && 
                candidate.getFormula().equals(aFormula) &&
                candidate instanceof LabelledFormula) {
                
                LabelledFormula lfCandidate = (LabelledFormula) candidate;
                FormulaLabel chLabel = lfCandidate.getLabel();
                
                // ✅ Verificar que la etiqueta ch sea accesible en la rama actual
                // Esto asegura que solo consideramos etiquetas de la rama actual o ramas ancestras
                if (proofTree instanceof IPLProofTree) {
                    IPLProofTree iplTree = (IPLProofTree) proofTree;
                    if (!iplTree.isLabelAccessible(chLabel)) {
                        System.out.println("  ⏭️ Proviso: Etiqueta " + chLabel + " no accesible en rama " + iplTree.getBranchId() + ", saltando");
                        continue; // Saltar esta fórmula, su etiqueta no es accesible
                    }
                }
                
                // DEBUG: Verificar que ambas etiquetas usan el mismo Context
                if (chLabel instanceof ContextFormulaLabel && ciLabel instanceof ContextFormulaLabel) {
                    Context chContext = ((ContextFormulaLabel)chLabel).getContext();
                    Context ciContext = ((ContextFormulaLabel)ciLabel).getContext();
                    boolean sameContext = chContext == ciContext;
                    System.out.println("🔍 DEBUG Proviso: ch=" + chLabel + " (Context@" + System.identityHashCode(chContext) + 
                                     "), ci=" + ciLabel + " (Context@" + System.identityHashCode(ciContext) + 
                                     "), mismo Context? " + sameContext);
                    if (!sameContext) {
                        System.out.println("⚠️ WARNING: Las etiquetas usan diferentes Context - no se pueden comparar correctamente");
                    }
                }
                
                // Verificar si ch ≤ ci
                boolean chEqualsCI = chLabel.equals(ciLabel);
                boolean chLowerOrEqualCI = context.isLowerOrEqualTo(chLabel, ciLabel);
                boolean chLowerThanCI = context.isLowerThan(chLabel, ciLabel);
                boolean chGreaterThanCI = context.isGreaterThan(chLabel, ciLabel);
                
                System.out.println("🔍 DEBUG: Comparando " + chLabel + " con " + ciLabel);
                System.out.println("    ch == ci: " + chEqualsCI);
                System.out.println("    ch ≤ ci: " + chLowerOrEqualCI);
                System.out.println("    ch < ci: " + chLowerThanCI);
                System.out.println("    ch > ci: " + chGreaterThanCI);
                
                if (chEqualsCI || chLowerOrEqualCI) {
                    System.out.println("🛑 Proviso: Encontrado T " + aFormula + " : " + chLabel + 
                                     " donde " + chLabel + " ≤ " + ciLabel);
                    return true; // BLOQUEAR la aplicación de F→
                }
            }
        }
        
        System.out.println("✅ Proviso: No se encontró T " + aFormula + " : ch donde ch ≤ " + ciLabel);
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
     * Verifica si una fórmula es T ¬A donde A NO es una negación.
     * Solo estas fórmulas son "persistentes" y deben reaplicarse cuando aparecen nuevas etiquetas.
     * 
     * IMPORTANTE: T ¬¬A NO es persistente, debe tratarse como una regla normal para evitar loops.
     */
    private boolean isTNotFormula(SignedFormula sf) {
        if (!sf.getSign().equals(IPLSigns.TRUE)) {
            return false;
        }
        
        if (!(sf.getFormula() instanceof CompositeFormula)) {
            return false;
        }
        
        CompositeFormula comp = (CompositeFormula) sf.getFormula();
        if (!comp.getConnective().equals(IPLConnectives.NOT)) {
            return false;
        }
        
        // Verificar que la subfórmula NO sea una negación
        // Si es T ¬¬A, NO debe ser persistente (para evitar loop infinito)
        Formula subformula = comp.getImmediateSubformulas().get(0);
        if (subformula instanceof CompositeFormula) {
            CompositeFormula subComp = (CompositeFormula) subformula;
            if (subComp.getConnective().equals(IPLConnectives.NOT)) {
                // Es T ¬¬A, NO es persistente
                System.out.println("🔍 T¬¬: " + sf + " NO es persistente (doble negación)");
                return false;
            }
        }
        
        // Es T ¬A donde A no es negación: ES persistente
        return true;
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
                System.out.println("  ⏭️ T¬: Etiqueta " + cjLabel + " no accesible en rama " + iplTree.getBranchId() + ", saltando");
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
     * Extrae la estructura de la fórmula (signo + fórmula) sin la etiqueta.
     * Esto se usa para rastrear instancias de reglas que generan nuevas etiquetas,
     * donde queremos evitar aplicar la misma regla a la misma estructura de fórmula
     * con diferentes etiquetas.
     * 
     * @param sf la fórmula firmada (puede ser LabelledFormula o SignedFormula)
     * @return clave que identifica solo el signo y la estructura de la fórmula
     */
    private String getFormulaStructureKey(SignedFormula sf) {
        return sf.getSign().toString() + " " + sf.getFormula().toString();
    }

}
