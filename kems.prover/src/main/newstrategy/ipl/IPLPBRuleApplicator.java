/*
 * Created on 2025
 */
package main.newstrategy.ipl;

import logic.formulas.CompositeFormula;
import logic.formulas.Formula;
import logic.labelledFormulas.Context;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.LabelledFormula;
import logic.signedFormulas.FormulaSign;
import logic.signedFormulas.PBCandidateList;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.SignedFormulaBuilder;
import logicalSystems.ipl.IPLConnectives;
import logicalSystems.ipl.IPLProofTree;
import logicalSystems.ipl.IPLSignedFormulaFactory;
import logicalSystems.ipl.IPLRules;
import logicalSystems.ipl.IPLRuleStructures;
import logicalSystems.ipl.IPLSigns;
import main.newstrategy.ISimpleStrategy;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import main.strategy.ClassicalProofTree;
import main.strategy.applicator.IProofTransformation;
import rules.Rule;

/**
 * Rule applicator específico para PB en IPL como último recurso.
 * 
 * PB se aplica cuando:
 * 1. Tenemos una premisa mayor de una regla de 2 premisas
 * 2. No existe la premisa menor requerida
 * 3. Todas las otras reglas han sido intentadas sin éxito
 * 
 * Proceso:
 * 1. Aplicar PB para generar la premisa menor faltante
 * 2. Inmediatamente aplicar la regla de 2 premisas correspondiente
 */
public class IPLPBRuleApplicator implements IProofTransformation {

    private static final IPLTracer tracer = IPLTracer.getInstance();

    private ISimpleStrategy strategy;

    /**
     * Constructor para IPLPBRuleApplicator
     * @param strategy la estrategia IPL
     * @param ruleListName nombre de la lista de reglas (no se usa, por compatibilidad)
     */
    public IPLPBRuleApplicator(ISimpleStrategy strategy, String ruleListName) {
        super();
        this.strategy = strategy;
        // ruleListName no se usa en esta implementación
    }

    /**
     * Applies PB to a single specific formula.
     * This method is used by the canonical algorithm implementation.
     * 
     * @param current the proof tree
     * @param sfb the signed formula builder
     * @param candidate the specific formula to try PB on
     * @return true if PB was applied, false otherwise
     */
    public boolean applySingle(ClassicalProofTree current, SignedFormulaBuilder sfb, SignedFormula candidate) {
        if (!(candidate.getFormula() instanceof CompositeFormula)) {
            return false;
        }
        
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: trying for single formula: " + candidate);
        }
        
        PBCandidateList singleCandidateList = new PBCandidateList();
        singleCandidateList.add(candidate);
        
        return tryToApplyPBAsLastResort(current, sfb, singleCandidateList);
    }
    
    @Override
    public boolean apply(ClassicalProofTree current, SignedFormulaBuilder sfb) {
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: starting as last resort");
        }
        
        // ✅ CRUCIAL: PB solo debe aplicarse si NO hay fórmulas no analizadas (NOT_ANALYSED)
        // Si hay fórmulas NOT_ANALYSED, significa que las reglas operacionales aún tienen trabajo por hacer
        if (hasUnanalysedFormulas(current)) {
            if (IPLTracer.isEnabled()) {
                tracer.logPBSkipped("(branch)", "unanalyzed formulas remain");
            }
            return false;
        }
        
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: no unanalyzed formulas remain, PB can apply");
        }
        
        // En lugar de depender solo de getPBCandidates() (que puede estar vacío si las fórmulas ya fueron "procesadas"),
        // examinar TODAS las fórmulas compuestas en el árbol para ver si pueden beneficiarse de PB
        PBCandidateList allCompositeCandidates = findAllCompositeFormulas(current);
        
        if (allCompositeCandidates.size() > 0) {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB: " + allCompositeCandidates.size() + " composite candidates (FIFO order)");
            }
            // NO ordenar: mantener orden FIFO (orden de inserción) del iterador top-down
            // allCompositeCandidates.sort(strategy.getComparator());
            return tryToApplyPBAsLastResort(current, sfb, allCompositeCandidates);
        }
        
        if (IPLTracer.isEnabled()) {
            tracer.logPBSkipped("(branch)", "no composite candidates");
        }
        return false;
    }
    
    /**
     * Verifica si hay fórmulas no analizadas (NOT_ANALYSED) en la rama actual.
     * Si las hay, las reglas operacionales aún tienen trabajo por hacer.
     * Si NO hay fórmulas NOT_ANALYSED (todas están ANALYSED), entonces se permite PB,
     * y PB considerará fórmulas de la rama actual Y de los ancestros usando getTopDownIterator()
     * en findAllCompositeFormulas().
     * 
     * IMPORTANTE: Solo verifica la rama actual (no incluye ancestros) para determinar si hay trabajo pendiente.
     * Cuando todas las fórmulas de la rama actual están ANALYSED, se permite PB que considerará ancestros.
     * 
     * All formulas are now marked ANALYSED normally; universal formulas (T(A→B), T(¬A))
     * are re-selected via Def. 5.6 in selectUnanalyzedFormula, so no exclusion is needed.
     */
    private boolean hasUnanalysedFormulas(ClassicalProofTree current) {
        main.proofTree.iterator.IProofTreeBasicIterator it = current.getLocalIterator();
        while (it.hasNext()) {
            main.proofTree.INode node = it.next();
            if (node instanceof SignedFormulaNode) {
                SignedFormulaNode sfNode = (SignedFormulaNode) node;
                if (sfNode.getState() == SignedFormulaNodeState.NOT_ANALYSED) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logInfo("PB check: unanalyzed formula found: " + sfNode.getContent());
                    }
                    return true;
                }
            }
        }
        return false;
    }
    
    /**
     * Verifica si existe alguna instancia de la fórmula en el árbol,
     * independientemente de la etiqueta. Solo compara signo y fórmula.
     * 
     * NOTA DE DISEÑO: Esta verificación ignora labels intencionalmente.
     * La compatibilidad de labels es verificada por el applicator de dos
     * premisas al momento de aplicar la regla. Si PB verificara labels,
     * aplicaría PB para cada label incompatible, generando ramas infinitas
     * (cada PB habilita reglas que crean nuevos labels via F→₁, propagación,
     * y más PB). Ignorar labels actúa como guarda de terminación: PB solo
     * se aplica cuando la subfórmula auxiliar no existe EN NINGÚN label,
     * acotando el número de PB al número de subfórmulas de la fórmula inicial
     * (Theorem 5.11, propiedad de subfórmula).
     * 
     * Paper: Algorithm 1 líneas 14-18 (§5 p.16).
     */
    private boolean formulaExistsInTree(ClassicalProofTree current, SignedFormula target) {
        main.proofTree.iterator.IProofTreeVeryBasicIterator it = current.getTopDownIterator();
        while (it.hasNext()) {
            main.proofTree.INode node = it.next();
            if (node instanceof SignedFormulaNode) {
                SignedFormulaNode sfNode = (SignedFormulaNode) node;
                SignedFormula sf = (SignedFormula) sfNode.getContent();
                
                if (sf.getSign().equals(target.getSign()) && 
                    sf.getFormula().equals(target.getFormula())) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logInfo("PB: formula instance found: " + sf);
                    }
                    return true;
                }
            }
        }
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: no instance found: " + target.getSign() + " " + target.getFormula());
        }
        return false;
    }
    
    /**
     * Encuentra todas las fórmulas compuestas en el árbol que podrían beneficiarse de PB.
     * Usa orden FIFO: las fórmulas se procesan en el orden en que fueron agregadas al árbol
     * (iteración top-down desde la raíz).
     * 
     * IMPORTANTE: Considera fórmulas de la rama actual Y de sus ancestros (pero no de ramas hermanas),
     * usando getTopDownIterator(). Esto permite aplicar PB sobre fórmulas de ancestros que son accesibles.
     * 
     * El tracking por grupo de accesibilidad previene loops infinitos: dos ramas están en el mismo grupo
     * si una es ancestro de la otra. Cuando una rama aplica PB sobre una fórmula de ancestro, el registro
     * se hace en la rama ancestra donde está la fórmula, y todas las ramas descendientes (mismo grupo)
     * pueden ver ese registro y no aplicarán PB de nuevo.
     */
    private PBCandidateList findAllCompositeFormulas(ClassicalProofTree current) {
        PBCandidateList candidates = new PBCandidateList();
        
        // Usar iterador top-down para considerar fórmulas de la rama actual y sus ancestros
        // (pero no de ramas hermanas). Esto permite aplicar PB sobre fórmulas de ancestros.
        main.proofTree.iterator.IProofTreeVeryBasicIterator it = current.getTopDownIterator();
        
        // Verificar accesibilidad de etiquetas si es IPL
        boolean checkAccessibility = current instanceof logicalSystems.ipl.IPLProofTree;
        logicalSystems.ipl.IPLProofTree iplTree = checkAccessibility ? 
            (logicalSystems.ipl.IPLProofTree) current : null;
        
        while (it.hasNext()) {
            main.proofTree.INode node = it.next();
            
            if (!(node instanceof SignedFormulaNode)) {
                continue;
            }
            
            SignedFormulaNode sfNode = (SignedFormulaNode) node;
            SignedFormula sf = (SignedFormula) sfNode.getContent();
            
            // Solo considerar fórmulas compuestas que no son TOP ni BOTTOM
            if (!(sf.getFormula() instanceof CompositeFormula) ||
                sf.getFormula().toString().equals("TOP") || 
                sf.getFormula().toString().equals("BOTTOM")) {
                continue;
            }
            
            // Verificar que la etiqueta sea accesible en la rama actual (para IPL)
            if (checkAccessibility && sf instanceof logic.labelledFormulas.LabelledFormula) {
                logic.labelledFormulas.LabelledFormula lf = (logic.labelledFormulas.LabelledFormula) sf;
                if (!iplTree.isLabelAccessible(lf.getLabel())) {
                    continue; // Saltar fórmulas con etiquetas no accesibles
                }
            }
            
            if (!candidates.contains(sf)) {
                candidates.add(sf);
                if (IPLTracer.isEnabled()) {
                    tracer.logInfo("PB candidate: " + sf);
                }
            }
        }
        
        return candidates;
    }

    /**
     * Intenta aplicar PB como último recurso para reglas de 2 premisas O PB puro
     */
    protected boolean tryToApplyPBAsLastResort(ClassicalProofTree current, SignedFormulaBuilder sfb,
            PBCandidateList candidates) {
        
        // Obtener todas las reglas de 2 premisas de IPL (no solo PB_RULE_LIST)
        var twoPremiseRules = strategy.getMethod().getRules().get(IPLRuleStructures.TWO_PREMISE_RULE_LIST);
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: working with 2-premise rules as last resort");
        }
        
        // Para cada candidato, verificar si puede ser premisa mayor de alguna regla de 2 premisas
        // IMPORTANTE: Continuar evaluando candidatos aunque algunos no puedan aplicar PB
        // (puede ser que un candidato posterior sí pueda aplicarlo)
        for (int i = 0; i < candidates.size(); i++) {
            SignedFormula candidate = candidates.get(i);
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB: evaluating candidate: " + candidate);
            }
            
            // CASO 1: Buscar TODAS las reglas de 2 premisas donde este candidato puede ser la premisa mayor
            java.util.List<Rule> applicableRules = findAllTwoPremiseRulesForCandidate(candidate, twoPremiseRules);
            
            if (!applicableRules.isEmpty()) {
                if (IPLTracer.isEnabled()) {
                    tracer.logInfo("PB: " + applicableRules.size() + " applicable 2-premise rules found");
                }
                
                // Cuando llegamos aquí desde apply, ya sabemos que twoPremiseApplicator.applySingle falló
                // para esta fórmula. Esto significa que intentó todas las reglas de 2 premisas y ninguna pudo aplicarse.
                // Por lo tanto, solo aplicamos PB si hay una regla que NO tiene su premisa menor disponible.
                // Si todas las reglas tienen premisa menor disponible pero no pudieron aplicarse, significa que
                // sus conclusiones ya existen o las instancias ya fueron aplicadas, y no debemos aplicar PB.
                Rule ruleToApplyWithPB = null;
                SignedFormula auxToApplyWithPB = null;
                
                for (Rule rule : applicableRules) {
                    SignedFormula requiredAux = getIPLRuleAuxiliaryCandidate(rule, candidate, sfb);
                    if (!formulaExistsInTree(current, requiredAux)) {
                        // Esta regla no tiene su premisa menor disponible - candidata para PB
                        if (IPLTracer.isEnabled()) {
                            tracer.logInfo("PB: rule " + rule + " missing minor premise: " + requiredAux);
                        }
                        if (ruleToApplyWithPB == null) {
                            ruleToApplyWithPB = rule;
                            auxToApplyWithPB = requiredAux;
                        }
                    } else {
                        if (IPLTracer.isEnabled()) {
                            tracer.logInfo("PB: rule " + rule + " has minor premise: " + requiredAux);
                        }
                    }
                }
                
                // Aplicar PB solo si encontramos una regla que no tiene su premisa menor disponible
                if (ruleToApplyWithPB != null) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logInfo("PB: selected rule: " + ruleToApplyWithPB);
                        tracer.logInfo("PB: required minor premise: " + auxToApplyWithPB);
                        tracer.logInfo("PB: minor premise missing - applying PB");
                    }
                    
                    // Intentar aplicar PB y luego inmediatamente la regla de 2 premisas
                    // Si no se puede aplicar (ya fue aplicado), continuar con el siguiente candidato
                    boolean applied = applyPBAndTwoPremiseRule(current, sfb, candidate, ruleToApplyWithPB, auxToApplyWithPB);
                    if (applied) {
                        return true; // PB aplicado exitosamente
                    } else {
                        if (IPLTracer.isEnabled()) {
                            tracer.logPBSkipped(candidate.toString(), "already applied for this candidate");
                        }
                        // Continuar con el siguiente candidato
                    }
                } else {
                    if (IPLTracer.isEnabled()) {
                        tracer.logPBSkipped(candidate.toString(), "all rules have minor premise but couldn't apply");
                    }
                }
            }
        }
        
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: no opportunity found as last resort");
        }
        return false;
    }
    
    /**
     * Busca dinámicamente TODAS las reglas de 2 premisas donde el candidato puede ser la premisa mayor.
     * Retorna todas las reglas aplicables, no solo la primera.
     */
    private java.util.List<Rule> findAllTwoPremiseRulesForCandidate(SignedFormula candidate, Object twoPremiseRulesList) {
        java.util.List<Rule> result = new java.util.ArrayList<>();
        
        // Solo fórmulas compuestas pueden ser premisas mayores
        if (!(candidate.getFormula() instanceof CompositeFormula)) {
            return result;
        }
        
        CompositeFormula comp = (CompositeFormula) candidate.getFormula();
        
        // Buscar en la estructura de reglas de 2 premisas
        if (!(twoPremiseRulesList instanceof rules.structures.IPLConnectiveRoleSignRuleList)) {
            return result;
        }
        
        rules.structures.IPLConnectiveRoleSignRuleList ruleList = 
            (rules.structures.IPLConnectiveRoleSignRuleList) twoPremiseRulesList;
        
        // Buscar en ambos roles (LEFT y RIGHT) todas las reglas que coincidan
        java.util.List<Rule> leftRules = ruleList.getMany(comp.getConnective(), rules.KERuleRole.LEFT, candidate.getSign());
        if (leftRules != null) {
            result.addAll(leftRules);
        }
        
        java.util.List<Rule> rightRules = ruleList.getMany(comp.getConnective(), rules.KERuleRole.RIGHT, candidate.getSign());
        if (rightRules != null) {
            result.addAll(rightRules);
        }
        
        return result;
    }
    
    /**
     * Busca dinámicamente en TODAS las reglas de 2 premisas donde el candidato puede ser la premisa mayor.
     * Retorna solo la primera regla aplicable (método legacy para compatibilidad).
     * 
     * Cualquier regla de 2 premisas es candidata para PB cuando:
     * - El candidato coincide con el patrón de la premisa mayor
     * - La premisa menor no existe en el árbol
     * 
     * PB se aplicará para generar la premisa menor faltante.
     */
    private Rule findTwoPremiseRuleForCandidate(SignedFormula candidate, Object twoPremiseRulesList) {
        // Solo fórmulas compuestas pueden ser premisas mayores
        if (!(candidate.getFormula() instanceof CompositeFormula)) {
            return null;
        }
        
        CompositeFormula comp = (CompositeFormula) candidate.getFormula();
        
        // Buscar en la estructura de reglas de 2 premisas
        if (!(twoPremiseRulesList instanceof rules.structures.IPLConnectiveRoleSignRuleList)) {
            return null;
        }
        
        rules.structures.IPLConnectiveRoleSignRuleList ruleList = 
            (rules.structures.IPLConnectiveRoleSignRuleList) twoPremiseRulesList;
        
        // Buscar en ambos roles (LEFT y RIGHT) todas las reglas que coincidan
        java.util.List<Rule> possibleRules = new java.util.ArrayList<Rule>();
        
        java.util.List<Rule> leftRules = ruleList.getMany(comp.getConnective(), rules.KERuleRole.LEFT, candidate.getSign());
        if (leftRules != null) {
            possibleRules.addAll(leftRules);
        }
        
        java.util.List<Rule> rightRules = ruleList.getMany(comp.getConnective(), rules.KERuleRole.RIGHT, candidate.getSign());
        if (rightRules != null) {
            possibleRules.addAll(rightRules);
        }
        
        if (!possibleRules.isEmpty()) {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB: " + possibleRules.size() + " 2-premise rule candidates");
            }
            // Retornar la primera regla que coincida
            // (En el futuro se podría refinar para elegir la mejor)
            Rule selectedRule = possibleRules.get(0);
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB: selected rule: " + selectedRule);
            }
            return selectedRule;
        }

        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: no 2-premise rule found for " + candidate.getSign() + " " + comp.getConnective());
        }
        return null;
    }
    
    /**
     * Obtiene dinámicamente el auxiliar requerido para cualquier regla de 2 premisas
     * Usa la API de la regla misma (getAuxiliaryCandidates) para determinar qué necesita
     */
    private SignedFormula getIPLRuleAuxiliaryCandidate(Rule rule, SignedFormula candidate, SignedFormulaBuilder sfb) {
        if (!(rule instanceof rules.ipl.TwoPremisesOneConclusionRule)) {
            return null;
        }
        
        rules.ipl.TwoPremisesOneConclusionRule twoPremiseRule = 
            (rules.ipl.TwoPremisesOneConclusionRule) rule;
        
        // Usar el método getAuxiliaryCandidates de la regla para obtener qué necesita
        logic.labelledFormulas.LabelledFormulaFactory labelledFactory = 
            new logic.labelledFormulas.LabelledFormulaFactory();
        
        logic.signedFormulas.SignedFormulaList auxiliaryCandidates = 
            twoPremiseRule.getAuxiliaryCandidates(
                labelledFactory,
                sfb.getSignedFormulaFactory(),
                sfb.getFormulaFactory(),
                candidate
            );
        
        if (auxiliaryCandidates == null || auxiliaryCandidates.size() == 0) {
            return null;
        }
        
        // Retornar el primer candidato auxiliar (sin etiqueta específica, PB la asignará)
        SignedFormula auxiliar = (SignedFormula) auxiliaryCandidates.get(0);
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: auxiliary determined for " + rule + ": " + auxiliar);
        }
        return auxiliar;
    }
    
    /**
     * Genera dinámicamente la conclusión para cualquier regla de 2 premisas
     * Usa la API de la regla misma (getPossibleConclusions) para generar la conclusión
     */
    private SignedFormula generateIPLRuleConclusion(Rule rule, SignedFormula mainPremise, SignedFormula auxPremise, SignedFormulaBuilder sfb) {
        if (!(rule instanceof rules.ipl.TwoPremisesOneConclusionRule)) {
            return null;
        }
        
        rules.ipl.TwoPremisesOneConclusionRule twoPremiseRule = 
            (rules.ipl.TwoPremisesOneConclusionRule) rule;
        
        // Crear lista con las dos premisas (main primero, aux segundo)
        logic.signedFormulas.SignedFormulaList premises = new logic.signedFormulas.SignedFormulaList();
        premises.add(mainPremise);
        premises.add(auxPremise);
        
        // Usar getPossibleConclusions de la regla
        logic.signedFormulas.SignedFormulaList conclusions = 
            twoPremiseRule.getPossibleConclusions(
                sfb.getSignedFormulaFactory(),
                sfb.getFormulaFactory(),
                premises
            );
        
        if (conclusions == null || conclusions.size() == 0) {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB: no conclusions for rule " + rule + " (main label: " + mainPremise.getLabel()
                    + ", aux label: " + auxPremise.getLabel() + ")");
            }
            return null;
        }
        
        // Retornar la primera conclusión
        SignedFormula conclusion = (SignedFormula) conclusions.get(0);
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: conclusion generated for " + rule + ": " + conclusion);
        }
        return conclusion;
    }
    
    /**
     * Crea una SignedFormula apropiada para IPL (LabelledFormula con ContextFormulaLabel)
     */
    private SignedFormula createIPLSignedFormula(SignedFormulaBuilder sfb, FormulaSign sign, Formula formula) {
        // Para IPL, necesitamos usar el factory de LabelledFormula que crea automáticamente ContextFormulaLabel
        if (sfb.getSignedFormulaFactory() instanceof IPLSignedFormulaFactory) {
            IPLSignedFormulaFactory iplFactory = (IPLSignedFormulaFactory) sfb.getSignedFormulaFactory();
            // ✅ CORRECCIÓN: usar createLabelledFormula en lugar de createSignedFormula
            SignedFormula result = iplFactory.createLabelledFormula(sign, formula);
            return result;
        } else {
            // Fallback: crear SignedFormula normal
            SignedFormula result = sfb.createSignedFormula(sign, formula);
            return result;
        }
    }
    
    /**
     * Crea una SignedFormula apropiada para IPL con etiqueta específica
     */
    private SignedFormula createIPLSignedFormulaWithLabel(SignedFormulaBuilder sfb, FormulaSign sign, Formula formula, FormulaLabel label) {
        // Para IPL, necesitamos crear LabelledFormula con ContextFormulaLabel
        if (sfb.getSignedFormulaFactory() instanceof IPLSignedFormulaFactory) {
            IPLSignedFormulaFactory iplFactory = (IPLSignedFormulaFactory) sfb.getSignedFormulaFactory();
            
            // Asegurarnos de que la etiqueta sea ContextFormulaLabel
            logic.labelledFormulas.ContextFormulaLabel contextLabel;
            if (label instanceof logic.labelledFormulas.ContextFormulaLabel) {
                contextLabel = (logic.labelledFormulas.ContextFormulaLabel) label;
            } else {
                // Convertir FormulaLabel a ContextFormulaLabel usando el Context de la factory
                contextLabel = new logic.labelledFormulas.ContextFormulaLabel(
                    iplFactory.getContext(), label.getIndex());
                // Asegurarnos de que esté en el Context
                if (!iplFactory.getContext().getLabels().contains(contextLabel)) {
                    iplFactory.getContext().addElement(contextLabel);
                }
            }
            
            // Crear SignedFormula con ContextFormulaLabel usando la factory IPL
            SignedFormula result = iplFactory.createLabelledFormula(contextLabel, 
                                    iplFactory.createSignedFormula(sign, formula));
            return result;
        } else {
            // Fallback: crear SignedFormula normal
            return sfb.createSignedFormula(sign, formula);
        }
    }
    
    /**
     * Crea la fórmula opuesta apropiada para IPL
     */
    private SignedFormula createOppositeIPLSignedFormula(SignedFormulaBuilder sfb, SignedFormula original) {
        FormulaSign oppositeSign = original.getSign().equals(IPLSigns.TRUE) ? (FormulaSign) IPLSigns.FALSE : (FormulaSign) IPLSigns.TRUE;
        return createIPLSignedFormula(sfb, oppositeSign, original.getFormula());
    }
    
    /**
     * Aplica PB y luego inmediatamente la regla de 2 premisas.
     *
     * Implementa Algorithm 1 líneas 14-18: aplica PB para introducir la premisa menor
     * faltante, aplica la regla de 2 premisas en la rama izquierda y registra la
     * instancia en el conjunto global rinstances para evitar re-aplicación.
     */
    private boolean applyPBAndTwoPremiseRule(ClassicalProofTree current, SignedFormulaBuilder sfb,
            SignedFormula mainPremise, Rule rule, SignedFormula requiredAux) {
        
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB+Rule: main=" + mainPremise + ", rule=" + rule + ", aux=" + requiredAux);
        }
        
        // PASO 1: Obtener la etiqueta compartida (la misma que la premisa mayor)
        FormulaLabel sharedLabel = mainPremise.getLabel();
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: using major premise label: " + sharedLabel);
        }
        
        logic.labelledFormulas.ContextFormulaLabel contextSharedLabel;
        if (sharedLabel instanceof logic.labelledFormulas.ContextFormulaLabel) {
            contextSharedLabel = (logic.labelledFormulas.ContextFormulaLabel) sharedLabel;
        } else {
            IPLSignedFormulaFactory iplFactory = (IPLSignedFormulaFactory) sfb.getSignedFormulaFactory();
            contextSharedLabel = new logic.labelledFormulas.ContextFormulaLabel(
                iplFactory.getContext(), sharedLabel.getIndex());
            if (!iplFactory.getContext().getLabels().contains(contextSharedLabel)) {
                iplFactory.getContext().addElement(contextSharedLabel);
            }
        }
        
        FormulaSign oppositeSign = requiredAux.getSign().equals(IPLSigns.TRUE) ? 
            (FormulaSign) IPLSigns.FALSE : (FormulaSign) IPLSigns.TRUE;
        
        // PASO 2: Preparar las fórmulas auxiliares (con etiqueta compartida)
        SignedFormula auxWithSharedLabel = createIPLSignedFormulaWithLabel(sfb, 
            (FormulaSign) requiredAux.getSign(), requiredAux.getFormula(), contextSharedLabel);
        
        SignedFormula auxOpposite = createIPLSignedFormulaWithLabel(sfb, 
            oppositeSign, requiredAux.getFormula(), contextSharedLabel);
        
        SignedFormula mainPremiseWithContextLabel;
        if (mainPremise.getLabel() instanceof logic.labelledFormulas.ContextFormulaLabel) {
            mainPremiseWithContextLabel = mainPremise;
        } else {
            mainPremiseWithContextLabel = createIPLSignedFormulaWithLabel(sfb,
                (FormulaSign) mainPremise.getSign(), mainPremise.getFormula(), contextSharedLabel);
        }
        
        // PASO 3: Si la premisa menor ya existe, la regla puede disparar directamente — no aplicar PB
        if (current instanceof IPLProofTree) {
            IPLProofTree iplTree = (IPLProofTree) current;
            SignedFormula existingRequired = iplTree.findFormulaWithSignAndLabel(
                requiredAux.getFormula(), requiredAux.getSign(), contextSharedLabel);
            if (existingRequired != null) {
                if (IPLTracer.isEnabled()) {
                    tracer.logPBSkipped(mainPremise.toString(), "required aux already exists: " + existingRequired);
                }
                return false;
            }
        }
        
        // PASO 4: Verificar rinstances — si la instancia ya fue aplicada, intentar labels alternativos
        // (Algorithm 1 líneas 7/10: "r ∉ rinstances"). La clave usa el mismo formato que
        // IPLTwoPremiseRuleApplicator.createRuleInstanceKey para consistencia.
        String ruleInstanceKey = rule.toString() + ":" + mainPremiseWithContextLabel.toString()
                + ":" + auxWithSharedLabel.toString();
        
        if (current instanceof IPLProofTree) {
            IPLProofTree iplTree = (IPLProofTree) current;
            if (iplTree.wasRuleInstanceApplied(ruleInstanceKey)) {
                if (IPLTracer.isEnabled()) {
                    tracer.logPBSkipped(mainPremise.toString(), "rule instance already applied: "
                        + ruleInstanceKey + " - trying accessible labels cj > ci");
                }
                return tryPBAtAlternativeLabels(current, sfb, mainPremise, rule, requiredAux,
                        contextSharedLabel, oppositeSign, iplTree);
            }
        }
        
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB: minor premise missing and rule not yet applied - applying PB");
        }
        
        // PASO 5: Aplicar PB para crear la premisa menor faltante
        ClassicalProofTree right = (ClassicalProofTree) current.addRight(new SignedFormulaNode(
                auxOpposite, SignedFormulaNodeState.NOT_ANALYSED, strategy
                        .createOrigin(IPLRules.PB, current.getNode(mainPremise), null)));
        
        ClassicalProofTree left = (ClassicalProofTree) current.addLeft(new SignedFormulaNode(
                auxWithSharedLabel, SignedFormulaNodeState.NOT_ANALYSED, strategy
                        .createOrigin(IPLRules.PB, current.getNode(mainPremise), null)));
        
        // PASO 6: Inmediatamente aplicar la regla de 2 premisas en la rama izquierda
        SignedFormula conclusion = generateIPLRuleConclusion(rule, mainPremiseWithContextLabel, auxWithSharedLabel, sfb);
        
        if (conclusion == null) {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB: could not generate conclusion");
            }
            return false;
        }
        
        // PASO 7: Registrar instancia de regla en rinstances globales (Algorithm 1, línea 18).
        // Registrar ANTES de agregar la conclusión a left (PASO 8) para que el snapshot por
        // nodo del visor (recordRinstancesSnapshot en addLast) incluya la regla que generó
        // la conclusión, de la misma forma en que IPLOnePremiseRuleApplicator lo hace.
        if (current instanceof IPLProofTree) {
            ((IPLProofTree) current).registerRuleInstance(ruleInstanceKey);
        }

        // PASO 8: Agregar la conclusión a la rama izquierda
        left.addLast(new SignedFormulaNode(conclusion, SignedFormulaNodeState.NOT_ANALYSED, strategy
                .createOrigin(rule, current.getNode(mainPremise), left.getNode(auxWithSharedLabel))));

        if (IPLTracer.isEnabled()) {
            tracer.logRuleApplied(rule.toString(), mainPremise.toString(), auxWithSharedLabel.toString(), conclusion.toString());
            tracer.logPBApplied(mainPremise.toString(), rule.toString(), auxWithSharedLabel.toString(), "left", "right");
        }
        
        // Mark ANALYSED in both branches. Universal formulas (T(A→B), T(¬A)) will be
        // re-selected by selectUnanalyzedFormula when Def. 5.6 is unsatisfied for new worlds.
        left.removeFromPBCandidates(mainPremise, SignedFormulaNodeState.ANALYSED);
        right.removeFromPBCandidates(mainPremise, SignedFormulaNodeState.ANALYSED);
        
        return true;
    }

    /**
     * Cuando PB está bloqueado en la etiqueta ci de la premisa mayor (porque F(aux):ci ya existe),
     * busca etiquetas accesibles cj >= ci donde no existan ni T(aux):cj ni F(aux):cj y aplica PB ahí.
     *
     * Por ejemplo, para T(A→B):c1 con T(A):c23 faltante:
     *   - LEFT: T(A):c23 → regla da T(B):c23 → T_AND → T(p3):c23 contradice F(p3):c23 → CIERRA
     *   - RIGHT: F(A):c23 → condición Def 5.6 para T(A→B):c1 en cj=c23 satisfecha ✓
     */
    private boolean tryPBAtAlternativeLabels(ClassicalProofTree current, SignedFormulaBuilder sfb,
            SignedFormula mainPremise, Rule rule, SignedFormula requiredAux,
            logic.labelledFormulas.ContextFormulaLabel ci, FormulaSign oppositeSign,
            IPLProofTree iplTree) {

        // Recopilar etiquetas accesibles cj >= ci desde b*
        java.util.Set<SignedFormula> bStar = iplTree.extendBranch();
        java.util.LinkedHashSet<logic.labelledFormulas.ContextFormulaLabel> labelsToTry =
                new java.util.LinkedHashSet<>();

        for (SignedFormula bsf : bStar) {
            if (!(bsf instanceof logic.labelledFormulas.LabelledFormula)) continue;
            logic.labelledFormulas.FormulaLabel l =
                    ((logic.labelledFormulas.LabelledFormula) bsf).getLabel();
            if (!(l instanceof logic.labelledFormulas.ContextFormulaLabel)) continue;
            logic.labelledFormulas.ContextFormulaLabel cj =
                    (logic.labelledFormulas.ContextFormulaLabel) l;
            if (cj.toString().equals(ci.toString())) continue;          // omitir ci
            if (!ci.getContext().isLowerOrEqualTo(ci, cj)) continue;    // necesitamos cj >= ci
            if (!iplTree.isLabelAccessible(cj)) continue;               // etiqueta accesible
            labelsToTry.add(cj);
        }

        for (logic.labelledFormulas.ContextFormulaLabel cj : labelsToTry) {
            // Si T(aux):cj ya existe, la regla debería haber disparado directamente
            SignedFormula existingReq = iplTree.findFormulaWithSignAndLabel(
                    requiredAux.getFormula(), requiredAux.getSign(), cj);
            if (existingReq != null) continue;

            // Si F(aux):cj ya existe, también bloqueado en esta etiqueta
            SignedFormula existingOpp = iplTree.findFormulaWithSignAndLabel(
                    requiredAux.getFormula(), oppositeSign, cj);
            if (existingOpp != null) continue;

            // Crear fórmulas auxiliares en cj (necesarias para la clave de rinstances)
            SignedFormula auxWithCj = createIPLSignedFormulaWithLabel(sfb,
                    (FormulaSign) requiredAux.getSign(), requiredAux.getFormula(), cj);
            SignedFormula auxOppositeCj = createIPLSignedFormulaWithLabel(sfb,
                    oppositeSign, requiredAux.getFormula(), cj);

            // Verificar rinstances para esta combinación (rule, main, aux@cj)
            String ruleKeyAlt = rule.toString() + ":" + mainPremise.toString() + ":" + auxWithCj.toString();
            if (iplTree.wasRuleInstanceApplied(ruleKeyAlt)) continue;

            if (IPLTracer.isEnabled()) {
                tracer.logInfo("PB-ALT: etiqueta ci=" + ci + " bloqueada, aplicando PB en cj=" + cj
                        + " para aux " + requiredAux.getSign() + "(" + requiredAux.getFormula() + ")");
            }

            // Crear ramas PB
            ClassicalProofTree right = (ClassicalProofTree) current.addRight(new SignedFormulaNode(
                    auxOppositeCj, SignedFormulaNodeState.NOT_ANALYSED, strategy
                            .createOrigin(IPLRules.PB, current.getNode(mainPremise), null)));

            ClassicalProofTree left = (ClassicalProofTree) current.addLeft(new SignedFormulaNode(
                    auxWithCj, SignedFormulaNodeState.NOT_ANALYSED, strategy
                            .createOrigin(IPLRules.PB, current.getNode(mainPremise), null)));

            // Aplicar la regla inmediatamente en la rama izquierda (conclusión en cj)
            // Asegurarse de que mainPremise tenga ContextFormulaLabel (igual que en applyPBAndTwoPremiseRule)
            SignedFormula mainPremiseForConclusion;
            if (mainPremise.getLabel() instanceof logic.labelledFormulas.ContextFormulaLabel) {
                mainPremiseForConclusion = mainPremise;
            } else {
                mainPremiseForConclusion = createIPLSignedFormulaWithLabel(sfb,
                        (FormulaSign) mainPremise.getSign(), mainPremise.getFormula(), ci);
            }
            SignedFormula conclusion = generateIPLRuleConclusion(rule, mainPremiseForConclusion, auxWithCj, sfb);

            // Registrar instancia de regla en rinstances globales ANTES de agregar la
            // conclusión a left (Algorithm 1, línea 18): así el snapshot por nodo del
            // visor incluye la regla que generó la conclusión.
            iplTree.registerRuleInstance(ruleKeyAlt);

            if (conclusion != null) {
                left.addLast(new SignedFormulaNode(conclusion, SignedFormulaNodeState.NOT_ANALYSED,
                        strategy.createOrigin(rule, current.getNode(mainPremise),
                                left.getNode(auxWithCj))));
            }

            if (IPLTracer.isEnabled()) {
                String concStr = conclusion != null ? conclusion.toString() : "(null)";
                tracer.logRuleApplied(rule.toString(), mainPremise.toString(),
                        auxWithCj.toString(), concStr);
                tracer.logPBApplied(mainPremise.toString(), rule.toString(),
                        auxWithCj.toString(), "left", "right");
            }

            // Mark ANALYSED in both branches; Def. 5.6 re-check in selectUnanalyzedFormula
            // handles re-selection of universal formulas when new worlds appear.
            left.removeFromPBCandidates(mainPremise, SignedFormulaNodeState.ANALYSED);
            right.removeFromPBCandidates(mainPremise, SignedFormulaNodeState.ANALYSED);

            return true;
        }

        if (IPLTracer.isEnabled()) {
            tracer.logInfo("PB-ALT: no se encontraron etiquetas alternativas viables para "
                    + requiredAux.getSign() + "(" + requiredAux.getFormula() + ")");
        }
        return false;
    }

}
