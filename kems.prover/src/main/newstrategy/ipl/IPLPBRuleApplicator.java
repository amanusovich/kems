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
        
        System.out.println("🔍 IPL PBRuleApplicator: Trying PB for single formula: " + candidate);
        
        PBCandidateList singleCandidateList = new PBCandidateList();
        singleCandidateList.add(candidate);
        
        return tryToApplyPBAsLastResort(current, sfb, singleCandidateList);
    }
    
    @Override
    public boolean apply(ClassicalProofTree current, SignedFormulaBuilder sfb) {
        System.out.println("🔄 IPL PBRuleApplicator: Iniciando aplicación de PB como último recurso");
        
        // ✅ CRUCIAL: PB solo debe aplicarse si NO hay fórmulas no analizadas (NOT_ANALYSED)
        // Si hay fórmulas NOT_ANALYSED, significa que las reglas operacionales aún tienen trabajo por hacer
        if (hasUnanalysedFormulas(current)) {
            System.out.println("⏭️ IPL PBRuleApplicator: Hay fórmulas no analizadas - NO aplicar PB aún");
            return false;
        }
        
        System.out.println("✅ IPL PBRuleApplicator: No hay fórmulas no analizadas - PB puede aplicarse");
        
        // En lugar de depender solo de getPBCandidates() (que puede estar vacío si las fórmulas ya fueron "procesadas"),
        // examinar TODAS las fórmulas compuestas en el árbol para ver si pueden beneficiarse de PB
        PBCandidateList allCompositeCandidates = findAllCompositeFormulas(current);
        
        if (allCompositeCandidates.size() > 0) {
            System.out.println("🔄 IPL PBRuleApplicator: " + allCompositeCandidates.size() + " candidatos compuestos encontrados para PB (orden FIFO)");
            // NO ordenar: mantener orden FIFO (orden de inserción) del iterador top-down
            // allCompositeCandidates.sort(strategy.getComparator());
            return tryToApplyPBAsLastResort(current, sfb, allCompositeCandidates);
        }
        
        System.out.println("⚠️ IPL PBRuleApplicator: No hay candidatos compuestos para PB");
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
     * IMPORTANTE: Excluye fórmulas T¬ persistentes (T ¬A donde A no es negación),
     * ya que estas nunca se marcan como ANALYSED por diseño.
     */
    private boolean hasUnanalysedFormulas(ClassicalProofTree current) {
        main.proofTree.iterator.IProofTreeBasicIterator it = current.getLocalIterator();
        
        while (it.hasNext()) {
            main.proofTree.INode node = it.next();
            if (node instanceof SignedFormulaNode) {
                SignedFormulaNode sfNode = (SignedFormulaNode) node;
                if (sfNode.getState() == SignedFormulaNodeState.NOT_ANALYSED) {
                    SignedFormula sf = (SignedFormula) sfNode.getContent();
                    
                    // Excluir fórmulas T¬ persistentes (que nunca se marcan como ANALYSED)
                    if (isTNotFormula(sf)) {
                        System.out.println("   Fórmula T¬ persistente (excluida del check): " + sf);
                        continue; // No contar esta como "trabajo pendiente"
                    }
                    
                    System.out.println("   Fórmula no analizada encontrada: " + sf);
                    return true; // Hay trabajo pendiente para reglas operacionales
                }
            }
        }
        
        // No hay fórmulas NOT_ANALYSED en la rama actual - se permite PB
        // (PB considerará fórmulas de ancestros en findAllCompositeFormulas)
        return false;
    }
    
    /**
     * Verifica si una fórmula es T ¬A (donde A no es negación).
     * Estas son las fórmulas persistentes que nunca se marcan como ANALYSED.
     */
    private boolean isTNotFormula(SignedFormula sf) {
        if (!sf.getSign().equals(IPLSigns.TRUE)) {
            return false;
        }
        
        Formula formula = sf.getFormula();
        if (!(formula instanceof CompositeFormula)) {
            return false;
        }
        
        CompositeFormula comp = (CompositeFormula) formula;
        if (!comp.getConnective().equals(logicalSystems.ipl.IPLConnectives.NOT)) {
            return false;
        }
        
        // Verificar que la subfórmula NO sea negación (evitar T ¬¬A)
        Formula subformula = comp.getImmediateSubformulas().get(0);
        if (subformula instanceof CompositeFormula) {
            CompositeFormula subComp = (CompositeFormula) subformula;
            if (subComp.getConnective().equals(logicalSystems.ipl.IPLConnectives.NOT)) {
                return false; // T ¬¬A no es persistente
            }
        }
        
        return true; // T ¬A donde A no es negación
    }
    
    /**
     * Verifica si existe alguna instancia de la fórmula en el árbol,
     * independientemente de la etiqueta. Solo compara signo y fórmula.
     * 
     * Esto es crucial para evitar aplicar PB cuando ya existe la premisa menor
     * con una etiqueta diferente (generada por reglas operacionales).
     */
    private boolean formulaExistsInTree(ClassicalProofTree current, SignedFormula target) {
        main.proofTree.iterator.IProofTreeVeryBasicIterator it = current.getTopDownIterator();
        while (it.hasNext()) {
            main.proofTree.INode node = it.next();
            if (node instanceof SignedFormulaNode) {
                SignedFormulaNode sfNode = (SignedFormulaNode) node;
                SignedFormula sf = (SignedFormula) sfNode.getContent();
                
                // Comparar solo signo y fórmula, ignorar etiqueta
                if (sf.getSign().equals(target.getSign()) && 
                    sf.getFormula().equals(target.getFormula())) {
                    System.out.println("   ✅ Encontrada instancia de la fórmula: " + sf);
                    return true;
                }
            }
        }
        System.out.println("   ❌ No se encontró ninguna instancia de: " + target.getSign() + " " + target.getFormula());
        return false;
    }
    
    /**
     * Encuentra la rama ancestra donde está una fórmula (la raíz del grupo de accesibilidad para esa fórmula).
     * Si la fórmula está en la rama actual, retorna el branchId de la rama actual.
     * Si está en un ancestro, retorna el branchId de ese ancestro (el más cercano donde está la fórmula).
     * 
     * Esto se usa para determinar dónde registrar el tracking de PB: debe registrarse en la rama
     * donde está la fórmula, para que todas las ramas descendientes (que están en el mismo grupo)
     * puedan ver que PB ya se aplicó.
     * 
     * @param current la rama actual
     * @param formula la fórmula a buscar
     * @return el branchId donde está la fórmula, o null si no se encuentra
     */
    private String findBranchIdOfFormula(ClassicalProofTree current, SignedFormula formula) {
        // IMPORTANTE: Buscar primero en ancestros, porque si la fórmula está en un ancestro,
        // debemos registrar el PB en ese ancestro (no en la rama actual) para que todas las
        // ramas descendientes vean el registro. Solo si no está en ningún ancestro, está en la rama actual.
        
        // Buscar en ancestros (subiendo por la cadena de padres)
        if (current instanceof logicalSystems.ipl.IPLProofTree) {
            main.proofTree.IProofTree parent = current.getParent();
            while (parent != null) {
                if (parent instanceof logicalSystems.ipl.IPLProofTree) {
                    logicalSystems.ipl.IPLProofTree iplParent = (logicalSystems.ipl.IPLProofTree) parent;
                    main.proofTree.iterator.IProofTreeBasicIterator parentIt = iplParent.getLocalIterator();
                    
                    while (parentIt.hasNext()) {
                        main.proofTree.INode node = parentIt.next();
                        if (node instanceof SignedFormulaNode) {
                            SignedFormula candidate = (SignedFormula) ((SignedFormulaNode) node).getContent();
                            if (candidate.equals(formula)) {
                                String branchId = iplParent.getBranchId();
                                System.out.println("   🔍 Fórmula encontrada en rama ancestra: " + branchId);
                                return branchId;
                            }
                        }
                    }
                }
                parent = parent.getParent();
            }
        }
        
        // Si no está en ningún ancestro, buscar en la rama actual
        main.proofTree.iterator.IProofTreeBasicIterator localIt = current.getLocalIterator();
        while (localIt.hasNext()) {
            main.proofTree.INode node = localIt.next();
            if (node instanceof SignedFormulaNode) {
                SignedFormula candidate = (SignedFormula) ((SignedFormulaNode) node).getContent();
                // Comparar por signo, fórmula y etiqueta (deben ser iguales exactamente)
                if (candidate.equals(formula)) {
                    if (current instanceof logicalSystems.ipl.IPLProofTree) {
                        String branchId = ((logicalSystems.ipl.IPLProofTree) current).getBranchId();
                        System.out.println("   🔍 Fórmula encontrada en rama actual: " + branchId);
                        return branchId;
                    }
                    return null;
                }
            }
        }
        
        System.out.println("   ⚠️ Fórmula no encontrada en rama actual ni ancestros");
        return null; // No encontrada
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
                System.out.println("🎯 IPL PBRuleApplicator: Candidato compuesto agregado: " + sf);
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
        System.out.println("🔄 IPL PBRuleApplicator: Trabajando con reglas de 2 premisas como último recurso");
        
        // Para cada candidato, verificar si puede ser premisa mayor de alguna regla de 2 premisas
        // IMPORTANTE: Continuar evaluando candidatos aunque algunos no puedan aplicar PB
        // (puede ser que un candidato posterior sí pueda aplicarlo)
        for (int i = 0; i < candidates.size(); i++) {
            SignedFormula candidate = candidates.get(i);
            System.out.println("🔍 IPL PBRuleApplicator: Evaluando candidato: " + candidate);
            
            // CASO 1: Buscar TODAS las reglas de 2 premisas donde este candidato puede ser la premisa mayor
            java.util.List<Rule> applicableRules = findAllTwoPremiseRulesForCandidate(candidate, twoPremiseRules);
            
            if (!applicableRules.isEmpty()) {
                System.out.println("✅ Encontradas " + applicableRules.size() + " reglas de 2 premisas candidatas");
                
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
                        System.out.println("❌ Regla " + rule + " NO tiene premisa menor disponible: " + requiredAux);
                        if (ruleToApplyWithPB == null) {
                            ruleToApplyWithPB = rule;
                            auxToApplyWithPB = requiredAux;
                        }
                    } else {
                        System.out.println("✅ Regla " + rule + " tiene premisa menor disponible: " + requiredAux);
                        // Si tiene premisa menor disponible pero twoPremiseApplicator.applySingle falló,
                        // significa que la conclusión ya existe o la instancia ya fue aplicada.
                        // No aplicamos PB en este caso.
                    }
                }
                
                // Aplicar PB solo si encontramos una regla que no tiene su premisa menor disponible
                if (ruleToApplyWithPB != null) {
                    System.out.println("✅ Regla seleccionada para PB: " + ruleToApplyWithPB);
                    System.out.println("🎯 IPL PBRuleApplicator: Regla de 2 premisas encontrada: " + ruleToApplyWithPB);
                    System.out.println("🔍 IPL PBRuleApplicator: Premisa menor requerida: " + auxToApplyWithPB);
                    System.out.println("💡 IPL PBRuleApplicator: Premisa menor no existe - aplicando PB");
                    
                    // Intentar aplicar PB y luego inmediatamente la regla de 2 premisas
                    // Si no se puede aplicar (ya fue aplicado), continuar con el siguiente candidato
                    boolean applied = applyPBAndTwoPremiseRule(current, sfb, candidate, ruleToApplyWithPB, auxToApplyWithPB);
                    if (applied) {
                        return true; // PB aplicado exitosamente
                    } else {
                        System.out.println("⏭️ PB no se pudo aplicar para este candidato (ya aplicado), continuando con siguiente candidato");
                        // Continuar con el siguiente candidato
                    }
                } else {
                    System.out.println("⏭️ IPL PBRuleApplicator: Todas las reglas tienen premisa menor disponible pero no pueden aplicarse (conclusión existe o ya aplicada), continuando con siguiente candidato");
                }
            }
        }
        
        System.out.println("❌ IPL PBRuleApplicator: No se encontró oportunidad para PB como último recurso");
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
        
        System.out.println("🔍 Buscando regla de 2 premisas para: " + candidate.getSign() + " " + comp.getConnective());
        
        // Buscar en la estructura de reglas de 2 premisas
        if (!(twoPremiseRulesList instanceof rules.structures.IPLConnectiveRoleSignRuleList)) {
            System.out.println("❌ twoPremiseRulesList no es IPLConnectiveRoleSignRuleList");
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
        
        System.out.println("🔍 Buscando regla de 2 premisas para: " + candidate.getSign() + " " + comp.getConnective());
        
        // Buscar en la estructura de reglas de 2 premisas
        if (!(twoPremiseRulesList instanceof rules.structures.IPLConnectiveRoleSignRuleList)) {
            System.out.println("❌ twoPremiseRulesList no es IPLConnectiveRoleSignRuleList");
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
            System.out.println("✅ Encontradas " + possibleRules.size() + " reglas de 2 premisas candidatas");
            // Retornar la primera regla que coincida
            // (En el futuro se podría refinar para elegir la mejor)
            Rule selectedRule = possibleRules.get(0);
            System.out.println("✅ Regla seleccionada: " + selectedRule);
            return selectedRule;
        }

        System.out.println("❌ No se encontró regla de 2 premisas para: " + candidate.getSign() + " " + comp.getConnective());
        return null;
    }
    
    /**
     * Obtiene dinámicamente el auxiliar requerido para cualquier regla de 2 premisas
     * Usa la API de la regla misma (getAuxiliaryCandidates) para determinar qué necesita
     */
    private SignedFormula getIPLRuleAuxiliaryCandidate(Rule rule, SignedFormula candidate, SignedFormulaBuilder sfb) {
        if (!(rule instanceof rules.ipl.TwoPremisesOneConclusionRule)) {
            System.out.println("⚠️ La regla no es TwoPremisesOneConclusionRule: " + rule);
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
            System.out.println("⚠️ No se obtuvieron candidatos auxiliares para regla: " + rule);
            return null;
        }
        
        // Retornar el primer candidato auxiliar (sin etiqueta específica, PB la asignará)
        SignedFormula auxiliar = (SignedFormula) auxiliaryCandidates.get(0);
        System.out.println("✅ Auxiliar determinado para " + rule + ": " + auxiliar);
        return auxiliar;
    }
    
    /**
     * Genera dinámicamente la conclusión para cualquier regla de 2 premisas
     * Usa la API de la regla misma (getPossibleConclusions) para generar la conclusión
     */
    private SignedFormula generateIPLRuleConclusion(Rule rule, SignedFormula mainPremise, SignedFormula auxPremise, SignedFormulaBuilder sfb) {
        if (!(rule instanceof rules.ipl.TwoPremisesOneConclusionRule)) {
            System.out.println("⚠️ La regla no es TwoPremisesOneConclusionRule: " + rule);
            return null;
        }
        
        rules.ipl.TwoPremisesOneConclusionRule twoPremiseRule = 
            (rules.ipl.TwoPremisesOneConclusionRule) rule;
        
        // Crear lista con las dos premisas (main primero, aux segundo)
        logic.signedFormulas.SignedFormulaList premises = new logic.signedFormulas.SignedFormulaList();
        premises.add(mainPremise);
        premises.add(auxPremise);
        
        // DEBUG: Mostrar las premisas antes de generar conclusiones
        System.out.println("DEBUG generateConclusion: Main premise: " + mainPremise + " (label: " + mainPremise.getLabel() + ", type: " + mainPremise.getLabel().getClass().getSimpleName() + ")");
        System.out.println("DEBUG generateConclusion: Aux premise: " + auxPremise + " (label: " + auxPremise.getLabel() + ", type: " + auxPremise.getLabel().getClass().getSimpleName() + ")");
        
        // Usar getPossibleConclusions de la regla
        logic.signedFormulas.SignedFormulaList conclusions = 
            twoPremiseRule.getPossibleConclusions(
                sfb.getSignedFormulaFactory(),
                sfb.getFormulaFactory(),
                premises
            );
        
        System.out.println("DEBUG generateConclusion: Conclusions returned: " + (conclusions != null ? conclusions.size() : "null"));
        
        if (conclusions == null || conclusions.size() == 0) {
            System.out.println("⚠️ No se obtuvieron conclusiones para regla: " + rule);
            System.out.println("   Esto puede deberse a que la condición de etiquetas no se cumple");
            System.out.println("   Main label: " + mainPremise.getLabel() + ", Aux label: " + auxPremise.getLabel());
            return null;
        }
        
        // Retornar la primera conclusión
        SignedFormula conclusion = (SignedFormula) conclusions.get(0);
        System.out.println("✅ Conclusión generada para " + rule + ": " + conclusion);
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
            System.out.println("🏷️ IPL PBRuleApplicator: Creada LabelledFormula: " + result + " (" + result.getClass().getSimpleName() + ")");
            return result;
        } else {
            // Fallback: crear SignedFormula normal
            SignedFormula result = sfb.createSignedFormula(sign, formula);
            System.out.println("⚠️ IPL PBRuleApplicator: Creada SignedFormula (fallback): " + result + " (" + result.getClass().getSimpleName() + ")");
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
            System.out.println("🏷️ IPL PBRuleApplicator: Creada LabelledFormula con etiqueta específica: " + result + " (label type: " + result.getLabel().getClass().getSimpleName() + ")");
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
     * Aplica PB y luego inmediatamente la regla de 2 premisas
     */
    private boolean applyPBAndTwoPremiseRule(ClassicalProofTree current, SignedFormulaBuilder sfb,
            SignedFormula mainPremise, Rule rule, SignedFormula requiredAux) {
        
        // Verificar rinstances POR RAMA: evitar reaplicar PB al mismo candidato con la misma regla
        // en la misma rama (pero permitir aplicarlo en ramas diferentes)
        String pbInstanceKey = "PB:" + rule.toString() + ":" + mainPremise.toString() + ":" + requiredAux.toString();
        System.out.println("DEBUG: Checking PB rinstance (por rama): " + pbInstanceKey);
        
        if (current instanceof IPLProofTree) {
            IPLProofTree iplTree = (IPLProofTree) current;
            if (iplTree.wasPBRuleInstanceApplied(pbInstanceKey)) {
                System.out.println("⏭️ PB ya aplicado a este candidato con esta regla en esta rama (PB rinstances): " + pbInstanceKey);
                return false;
            }
        }
        
        System.out.println("🔥 IPL PBRuleApplicator: Aplicando PB + regla de 2 premisas");
        System.out.println("   Premisa mayor: " + mainPremise);
        System.out.println("   Regla: " + rule.toString());
        System.out.println("   Auxiliar requerido: " + requiredAux);
        
        // PASO 1: Aplicar PB para crear la premisa menor faltante
        // PB debe crear ambas ramas con la MISMA etiqueta que la premisa mayor
        
        FormulaLabel sharedLabel = mainPremise.getLabel();
        System.out.println("🏷️ IPL PBRuleApplicator: Usando etiqueta de premisa mayor para PB: " + sharedLabel + " (type: " + sharedLabel.getClass().getSimpleName() + ")");
        
        // Asegurarnos de que la etiqueta compartida sea ContextFormulaLabel
        logic.labelledFormulas.ContextFormulaLabel contextSharedLabel;
        if (sharedLabel instanceof logic.labelledFormulas.ContextFormulaLabel) {
            contextSharedLabel = (logic.labelledFormulas.ContextFormulaLabel) sharedLabel;
        } else {
            // Convertir a ContextFormulaLabel usando el Context de la factory
            IPLSignedFormulaFactory iplFactory = (IPLSignedFormulaFactory) sfb.getSignedFormulaFactory();
            contextSharedLabel = new logic.labelledFormulas.ContextFormulaLabel(
                iplFactory.getContext(), sharedLabel.getIndex());
            if (!iplFactory.getContext().getLabels().contains(contextSharedLabel)) {
                iplFactory.getContext().addElement(contextSharedLabel);
            }
            System.out.println("🔄 Convertida etiqueta a ContextFormulaLabel: " + contextSharedLabel);
        }
        
        // Crear auxiliar requerido con la etiqueta compartida (ContextFormulaLabel)
        SignedFormula auxWithSharedLabel = createIPLSignedFormulaWithLabel(sfb, 
            (FormulaSign) requiredAux.getSign(), requiredAux.getFormula(), contextSharedLabel);
        
        // Crear auxiliar opuesto con la MISMA etiqueta compartida (ContextFormulaLabel)
        FormulaSign oppositeSign = requiredAux.getSign().equals(IPLSigns.TRUE) ? 
            (FormulaSign) IPLSigns.FALSE : (FormulaSign) IPLSigns.TRUE;
        SignedFormula auxOpposite = createIPLSignedFormulaWithLabel(sfb, 
            oppositeSign, requiredAux.getFormula(), contextSharedLabel);
        
        // Crear rama derecha con auxiliar opuesto (misma etiqueta)
        ClassicalProofTree right = (ClassicalProofTree) current.addRight(new SignedFormulaNode(
                auxOpposite, SignedFormulaNodeState.NOT_ANALYSED, strategy
                        .createOrigin(IPLRules.PB, current.getNode(mainPremise), null)));
        
        System.out.println("➡️  PB Rama derecha: " + auxOpposite);
        
        // Crear rama izquierda con auxiliar requerido (misma etiqueta)
        ClassicalProofTree left = (ClassicalProofTree) current.addLeft(new SignedFormulaNode(auxWithSharedLabel,
                SignedFormulaNodeState.NOT_ANALYSED, strategy.createOrigin(IPLRules.PB, current
                        .getNode(mainPremise), null)));
        
        System.out.println("⬅️  PB Rama izquierda: " + auxWithSharedLabel);
        
        // PASO 2: Inmediatamente aplicar la regla de 2 premisas en la rama izquierda
        // Para reglas IPL, generar la conclusión usando la lógica específica de la regla
        // Asegurarnos de que mainPremise también use ContextFormulaLabel
        SignedFormula mainPremiseWithContextLabel;
        if (mainPremise.getLabel() instanceof logic.labelledFormulas.ContextFormulaLabel) {
            mainPremiseWithContextLabel = mainPremise;
        } else {
            // Crear una versión de mainPremise con ContextFormulaLabel
            mainPremiseWithContextLabel = createIPLSignedFormulaWithLabel(sfb,
                (FormulaSign) mainPremise.getSign(), mainPremise.getFormula(), contextSharedLabel);
            System.out.println("🔄 Recreada mainPremise con ContextFormulaLabel: " + mainPremiseWithContextLabel);
        }
        
        SignedFormula conclusion = generateIPLRuleConclusion(rule, mainPremiseWithContextLabel, auxWithSharedLabel, sfb);
        
        if (conclusion == null) {
            System.out.println("❌ No se pudo generar conclusión para PB");
            return false;
        }
        
        left.addLast(new SignedFormulaNode(conclusion, SignedFormulaNodeState.NOT_ANALYSED, strategy
                .createOrigin(rule, current.getNode(mainPremise), left.getNode(auxWithSharedLabel))));
        
        System.out.println("✅ Regla 2 premisas aplicada: " + conclusion);
        
        // Registrar en rinstances de la rama ACTUAL (su grupo de accesibilidad).
        // Cuando una rama aplica PB sobre una fórmula (ya sea de la rama actual o de un ancestro),
        // se registra en la rama actual. Esto permite que:
        // - Ramas hermanas apliquen PB sobre la misma fórmula ancestral (no comparten el mismo grupo)
        // - Ramas descendientes de esta rama no apliquen PB de nuevo (están en el mismo grupo)
        if (current instanceof IPLProofTree) {
            IPLProofTree iplTree = (IPLProofTree) current;
            
            // Registrar en la rama actual (su grupo de accesibilidad incluye esta rama y todos sus ancestros)
            iplTree.registerPBRuleInstance(pbInstanceKey);
        }
        
        // Actualizar estructuras de control
        // NO agregar ramas a la cola aquí - el algoritmo canónico las agregará cuando detecte que hay ramas hijas
        left.removeFromPBCandidates(mainPremise, SignedFormulaNodeState.ANALYSED);
        right.removeFromPBCandidates(mainPremise, SignedFormulaNodeState.ANALYSED);
        // NO cambiar strategy.setCurrent aquí - el algoritmo canónico maneja qué rama procesar
        
        System.out.println("🎯 IPL PBRuleApplicator: PB + regla de 2 premisas aplicado exitosamente");
        System.out.println("  ➡️ Right branch created: closed=" + right.isClosed() + ", completed=" + right.isCompleted());
        System.out.println("  ⬅️ Left branch created: closed=" + left.isClosed() + ", completed=" + left.isCompleted());
        return true;
    }

}
