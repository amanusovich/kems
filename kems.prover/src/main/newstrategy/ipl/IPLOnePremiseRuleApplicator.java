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
import main.proofTree.INode;
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
            
            // PROVISO DE SATURACIÓN para regla F¬ (existencial)
            // NO aplicar (F¬) si existe T A : ch donde ci ≤ ch (la fórmula ya está satisfecha)
            if (r == IPLRules.F_NOT && shouldBlockFNotRule(proofTree, sf)) {
                System.out.println("🛑 Proviso de Saturación: Bloqueando aplicación de F¬ para " + sf);
                continue; // Saltar esta regla, no aplicarla
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
                        
                        // ✅ PROPAGACIÓN FÍSICA DE MONOTONICIDAD para F→
                        // Cuando F→ crea un nuevo label cj, debemos agregar físicamente
                        // todas las fórmulas T compuestas que se propagan desde ci ≤ cj
                        // Esto permite que las reglas de 2 premisas se apliquen correctamente
                        if (r == IPLRules.F_A_IMPLIES_B_TA_FB) {
                            propagateCompositeTFormulasForNewLabel(proofTree, lf.getLabel(), strategy);
                        }
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
        
        Context context = getContextFromLabel(ciLabel);
        if (context == null) {
            System.out.println("⚠️ Proviso: No se pudo obtener Context para verificar");
            return false; // Sin Context, no podemos verificar, no bloquear por seguridad
        }
        
        // ✅ EXTENSIÓN b* IMPLÍCITA: Buscar en b* (no solo en b)
        // Según el paper: "F → is applicable only when T A : ch does not occur 
        // for any ch ⪯ ci in the branch" - esto incluye fórmulas en b*
        System.out.println("🔍 Proviso (b*): Context tiene " + context.getLabels().size() + " etiquetas: " + context.getLabels());
        System.out.println("🔍 Proviso (b*): Verificando si existe T " + aFormula + " : ch donde ch ≤ " + ciLabel + " en b*");
        
        if (!(proofTree instanceof IPLProofTree)) {
            System.out.println("⚠️ Proviso: ProofTree no es IPLProofTree, usando búsqueda en b solamente");
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
                    System.out.println("🛑 Proviso (b*): Encontrado T " + aFormula + " : " + chLabel + 
                                     " donde " + chLabel + " ≤ " + ciLabel);
                    return true; // BLOQUEAR la aplicación de F→
                }
            }
        }
        
        System.out.println("✅ Proviso (b*): No se encontró T " + aFormula + " : ch donde ch ≤ " + ciLabel);
        return false; // No bloquear
    }
    
    /**
     * Proviso de saturación para la regla F¬ (regla existencial).
     * 
     * La regla F¬ es existencial: busca crear un sucesor con T A.
     * Si ya existe algún ch tal que ci ≤ ch y T A : ch está en b*,
     * entonces la fórmula F !A : ci ya está satisfecha y NO debe aplicarse.
     * 
     * Esto previene el loop infinito:
     * T !!A (persistente) → F !A → F_NOT crea nuevo label → T !!A reaplica → ...
     * 
     * @param proofTree el árbol de prueba actual
     * @param sf la fórmula F !A : ci a verificar
     * @return true si la regla debe ser bloqueada, false si puede aplicarse
     */
    private boolean shouldBlockFNotRule(ClassicalProofTree proofTree, SignedFormula sf) {
        // Verificar que sea F !A
        if (!sf.getSign().equals(IPLSigns.FALSE)) {
            return false; // No es F, no bloquear
        }
        
        if (!(sf.getFormula() instanceof CompositeFormula)) {
            return false; // No es compuesta, no bloquear
        }
        
        CompositeFormula comp = (CompositeFormula) sf.getFormula();
        if (!comp.getConnective().equals(IPLConnectives.NOT)) {
            return false; // No es ¬, no bloquear
        }
        
        // Es F !A, verificar proviso
        if (!(sf instanceof LabelledFormula)) {
            return false; // Sin etiqueta, no podemos verificar
        }
        
        LabelledFormula lfMain = (LabelledFormula) sf;
        FormulaLabel ciLabel = lfMain.getLabel();
        
        // Obtener A (la subfórmula de !A)
        Formula aFormula = comp.getImmediateSubformulas().get(0);
        
        Context context = getContextFromLabel(ciLabel);
        if (context == null) {
            System.out.println("⚠️ Proviso F¬: No se pudo obtener Context para verificar");
            return false; // Sin Context, no podemos verificar, no bloquear por seguridad
        }
        
        // ✅ EXTENSIÓN b* IMPLÍCITA: Buscar en b* (no solo en b)
        // Según Definition 5.6: F !A : ci está saturada si existe T A : ch donde ci ≤ ch en b*
        System.out.println("🔍 Proviso F¬ (b*): Context tiene " + context.getLabels().size() + " etiquetas: " + context.getLabels());
        System.out.println("🔍 Proviso F¬ (b*): Verificando si existe T " + aFormula + " : ch donde " + ciLabel + " ≤ ch en b*");
        
        if (!(proofTree instanceof IPLProofTree)) {
            System.out.println("⚠️ Proviso F¬: ProofTree no es IPLProofTree");
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
                
                // Verificar si ci ≤ ch (opuesto a F→!)
                boolean chEqualsCI = chLabel.equals(ciLabel);
                boolean ciLowerOrEqualCH = context.isLowerOrEqualTo(ciLabel, chLabel);
                
                if (chEqualsCI || ciLowerOrEqualCH) {
                    System.out.println("🛑 Proviso F¬ (b*): Encontrado T " + aFormula + " : " + chLabel + 
                                     " donde " + ciLabel + " ≤ " + chLabel + " - Fórmula saturada");
                    return true; // BLOQUEAR la aplicación de F¬
                }
            }
        }
        
        System.out.println("✅ Proviso F¬ (b*): No se encontró T " + aFormula + " : ch donde " + ciLabel + " ≤ ch - Puede aplicarse");
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
     * ✅ ACTIVADO: T¬ ES persistente (regla gamma)
     * 
     * Las fórmulas T¬ deben reaplicarse cuando aparecen nuevos labels:
     * - Son reglas gamma que deben aplicarse a todos los mundos accesibles
     * - Cuando aparece un nuevo cj donde ci ⪯ cj, debe generarse físicamente F A : cj
     * - Por eso, T¬ nunca se marca como ANALYSED
     * 
     * @return true si es T¬A (cualquier negación), false en caso contrario
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
     * Propaga físicamente las fórmulas T compuestas por monotonicidad cuando se crea un nuevo label.
     * 
     * Cuando F→ crea un nuevo label cj, debemos agregar físicamente todas las fórmulas T compuestas
     * (especialmente T→) que tengan labels ci donde ci ≤ cj. Esto permite que las reglas de 2 premisas
     * (reglas beta) se apliquen correctamente sobre estas fórmulas propagadas.
     * 
     * Por ejemplo, si tenemos T (A→B) : c1 y se crea c3 donde c1 ≤ c3, entonces agregamos
     * físicamente T (A→B) : c3 para que X_IMPLIES_F_RIGHT pueda aplicarse con F B : c3.
     * 
     * @param proofTree el árbol de prueba actual
     * @param newLabel el nuevo label recién creado
     * @param strategy la estrategia para crear orígenes
     */
    private void propagateCompositeTFormulasForNewLabel(ClassicalProofTree proofTree, 
                                                        FormulaLabel newLabel,
                                                        ISimpleStrategy strategy) {
        if (!(proofTree instanceof IPLProofTree)) {
            return; // Solo aplicable a IPL
        }
        
        IPLProofTree iplTree = (IPLProofTree) proofTree;
        Context context = getContextFromLabel(newLabel);
        if (context == null) {
            System.out.println("⚠️ Monotonicidad: No se pudo obtener Context para propagar");
            return;
        }
        
        System.out.println("🔄 Monotonicidad: Propagando fórmulas T compuestas al nuevo label " + newLabel);
        
        // Iterar sobre todas las fórmulas en la rama actual
        IProofTreeVeryBasicIterator it = proofTree.getTopDownIterator();
        int propagatedCount = 0;
        
        while (it.hasNext()) {
            INode node = it.next();
            if (!(node instanceof SignedFormulaNode)) {
                continue;
            }
            
            SignedFormulaNode sfNode = (SignedFormulaNode) node;
            SignedFormula sf = (SignedFormula) sfNode.getContent();
            
            // Solo fórmulas T compuestas
            if (!sf.getSign().equals(IPLSigns.TRUE)) {
                continue;
            }
            
            if (!(sf.getFormula() instanceof CompositeFormula)) {
                continue; // Solo fórmulas compuestas
            }
            
            if (!(sf instanceof LabelledFormula)) {
                continue; // Debe tener label
            }
            
            LabelledFormula lf = (LabelledFormula) sf;
            FormulaLabel ciLabel = lf.getLabel();
            
            if (!iplTree.isLabelAccessible(ciLabel)) {
                continue; // Label no accesible
            }
            
            // Verificar si ci ≤ cj (nuevo label)
            boolean ciLowerOrEqualNew = ciLabel.equals(newLabel) || 
                                       context.isLowerOrEqualTo(ciLabel, newLabel);
            
            if (ciLowerOrEqualNew && !ciLabel.equals(newLabel)) {
                // Crear nueva instancia física con el nuevo label
                SignedFormula baseSf = lf.getSignedFormula();
                LabelledFormula propagated = new LabelledFormula(newLabel, baseSf);
                
                // Verificar si ya existe
                if (proofTree.getNode(propagated) != null) {
                    continue; // Ya existe, no agregar duplicado
                }
                
                // Agregar físicamente a la rama (usando NullRule para indicar propagación por monotonicidad)
                proofTree.addLast(new SignedFormulaNode(propagated, SignedFormulaNodeState.NOT_ANALYSED,
                        strategy.createOrigin(NullRule.INSTANCE, (SignedFormulaNode) node, null)));
                
                propagatedCount++;
                System.out.println("  ➕ Propagada: " + propagated + " (desde " + lf + ")");
            }
        }
        
        if (propagatedCount > 0) {
            System.out.println("✅ Monotonicidad: " + propagatedCount + " fórmulas T compuestas propagadas a " + newLabel);
        } else {
            System.out.println("⏭️ Monotonicidad: Ninguna fórmula T compuesta para propagar a " + newLabel);
        }
    }
    
}