package main.newstrategy.ipl;

import java.util.LinkedList;

import logic.formulas.CompositeFormula;
import logic.formulas.Formula;
import logicalSystems.ipl.IPLConnectives;
import logicalSystems.ipl.IPLProofTree;
import logicalSystems.ipl.IPLSigns;
import main.newstrategy.ISimpleStrategy;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import logic.signedFormulas.SignedFormulaBuilder;
import main.strategy.ClassicalProofTree;
import logic.signedFormulas.SignedFormula;

/**
 * Implementation of Algorithm 1 (Canonical procedure) from the paper.
 * 
 * This follows the exact order specified in the paper:
 * 1. For each formula φ not completely analyzed in branch b
 * 2. Try to apply 1-premise rule (if not in rinstances)
 * 3. Try to apply 2-premise rule (if not in rinstances)
 *    - If minor premise exists: apply rule
 *    - If minor premise missing: apply PB + rule
 * 4. Apply extend(b) after each formula processing
 * 
 * Key difference from current implementation:
 * - Processes ONE formula at a time (not all formulas of each type)
 * - Tries 1-premise rules BEFORE 2-premise rules for each formula
 * - Only marks as ANALYSED after successfully applying a rule
 */
public class IPLCanonicalStrategyImplementation {
    
    private static final IPLTracer tracer = IPLTracer.getInstance();
    
    private ISimpleStrategy strategy;
    private SignedFormulaBuilder sfb;
    private IPLOnePremiseRuleApplicator onePremiseApplicator;
    private IPLTwoPremiseRuleApplicator twoPremiseApplicator;
    private IPLPBRuleApplicator pbApplicator;
    
    public IPLCanonicalStrategyImplementation() {
    }
    
    /**
     * Executes the canonical procedure (Algorithm 1).
     * 
     * @param strategy the IPL strategy
     * @param sfb the signed formula builder
     * @return the completed proof tree
     */
    public ClassicalProofTree execute(ISimpleStrategy strategy, SignedFormulaBuilder sfb) {
        this.strategy = strategy;
        this.sfb = sfb;
        
        // Get the applicators from strategy
        this.onePremiseApplicator = (IPLOnePremiseRuleApplicator) strategy.getRuleApplicators().get(0);
        this.twoPremiseApplicator = (IPLTwoPremiseRuleApplicator) strategy.getRuleApplicators().get(1);
        this.pbApplicator = (IPLPBRuleApplicator) strategy.getProofTransformations().get(0);
        
        if (IPLTracer.isEnabled()) {
            tracer.reset();
            tracer.logAlgorithmStart();
        }
        
        // Line 1: T ← F A : c0 (already done in strategy initialization)
        ClassicalProofTree T = strategy.getProofTree();
        
        // If already closed, return immediately
        if (T.isClosed()) {
            return T;
        }
        
        // Line 3: while T is neither closed nor completed do
        LinkedList<IProofTree> openBranches = new LinkedList<>();
        openBranches.addLast(T);  // Usar addLast para consistencia con el orden FIFO
        strategy.setOpenBranches(openBranches);
        
        while (!openBranches.isEmpty() && !T.isClosed()) {
            // Line 4: select an open branch b in T
            // Usar removeFirst con addLast para procesar en orden FIFO (breadth-first)
            ClassicalProofTree b = (ClassicalProofTree) openBranches.removeFirst();
            strategy.setCurrent(b);
            
            if (IPLTracer.isEnabled()) {
                tracer.setCurrentBranch(getBranchId(b));
                tracer.logBranchStart(getBranchId(b));
            }
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("Estado: closed=" + b.isClosed() + ", completed=" + b.isCompleted());
            }
            
            // Line 5: while b is neither closed nor completed do
            java.util.Set<SignedFormula> failedFormulas = new java.util.HashSet<>();
            
            while (!b.isClosed() && !b.isCompleted()) {
                // Line 6: select a φ in b which is not completely analyzed in b
                SignedFormula phi = selectUnanalyzedFormula(b, failedFormulas);
                
                if (phi == null) {
                    // No more formulas to analyze - try PB as last resort
                    if (IPLTracer.isEnabled()) {
                        tracer.logInfo("No more formulas to analyze - trying PB as last resort");
                    }
                    boolean pbApplied = pbApplicator.apply(b, sfb);
                    
                    if (pbApplied) {
                        if (IPLTracer.isEnabled()) {
                            tracer.logInfo("PB applied as last resort");
                        }
                        
                        // PB siempre crea ramas cuando se aplica exitosamente
                        // Add child branches to the list of open branches
                        // Usar addLast para procesar en orden FIFO (breadth-first)
                        // Agregar primero izquierda, luego derecha para procesar izquierda primero
                        if (b.getLeft() != null) {
                            ClassicalProofTree leftBranch = (ClassicalProofTree) b.getLeft();
                            if (!leftBranch.isClosed()) {
                                openBranches.addLast(leftBranch);
                                if (IPLTracer.isEnabled()) {
                                    tracer.logInfo("Added left branch to queue");
                                }
                            }
                        }
                        if (b.getRight() != null) {
                            ClassicalProofTree rightBranch = (ClassicalProofTree) b.getRight();
                            if (!rightBranch.isClosed()) {
                                openBranches.addLast(rightBranch);
                                if (IPLTracer.isEnabled()) {
                                    tracer.logInfo("Added right branch to queue");
                                }
                            }
                        }
                        // Current branch now has children, stop processing it
                        // NO reactivar fórmulas ni resetear failedFormulas aquí - las ramas hijas
                        // tienen sus propias copias de las fórmulas y las procesarán independientemente
                        break;
                    } else {
                        if (IPLTracer.isEnabled()) {
                            tracer.logInfo("PB could not be applied - branch processing complete");
                        }
                        break;
                    }
                }
                
                if (IPLTracer.isEnabled()) {
                    tracer.logFormulaSelected(phi.toString(), "selected for processing");
                }
                
                // Lines 7-20: Try to apply rules to this specific formula
                boolean applied = processFormula(b, phi, sfb);
                
                if (applied) {
                    // Reset failed formulas on successful application
                    failedFormulas.clear();
                    
                    // Check if new branches were created (e.g., by PB rule)
                    if (b.getLeft() != null || b.getRight() != null) {
                        if (IPLTracer.isEnabled()) {
                            tracer.logInfo("Branching detected - adding child branches");
                        }
                        // Add child branches to the list of open branches
                        // Usar addLast para procesar en orden FIFO (breadth-first)
                        // Agregar primero izquierda, luego derecha para procesar izquierda primero
                        if (b.getLeft() != null) {
                            ClassicalProofTree leftBranch = (ClassicalProofTree) b.getLeft();
                            if (!leftBranch.isClosed()) {
                                openBranches.addLast(leftBranch);
                                if (IPLTracer.isEnabled()) {
                                    tracer.logInfo("Added left branch to queue");
                                }
                            }
                        }
                        if (b.getRight() != null) {
                            ClassicalProofTree rightBranch = (ClassicalProofTree) b.getRight();
                            if (!rightBranch.isClosed()) {
                                openBranches.addLast(rightBranch);
                                if (IPLTracer.isEnabled()) {
                                    tracer.logInfo("Added right branch to queue");
                                }
                            }
                        }
                        // Current branch now has children, stop processing it
                        break;
                    }
                } else {
                    // Remember this formula failed to apply rules
                    failedFormulas.add(phi);
                    
                    // Si hay demasiadas fórmulas fallidas, podría ser un loop
                    // Limitar el tamaño de failedFormulas para evitar loops infinitos
                    if (failedFormulas.size() > 50) {
                        if (IPLTracer.isEnabled()) {
                            tracer.logInfo("Too many failed formulas (" + failedFormulas.size() + ") - trying PB");
                        }
                        // Intentar PB como último recurso antes de que el loop continúe
                        boolean pbApplied = pbApplicator.apply(b, sfb);
                        if (pbApplied) {
                            if (IPLTracer.isEnabled()) {
                                tracer.logInfo("PB applied (loop prevention)");
                            }
                            // Check if new branches were created
                            if (b.getLeft() != null || b.getRight() != null) {
                                if (IPLTracer.isEnabled()) {
                                    tracer.logInfo("Branching detected after PB");
                                }
                                // Usar addLast para procesar en orden FIFO (breadth-first)
                                // Agregar primero izquierda, luego derecha para procesar izquierda primero
                                if (b.getLeft() != null) {
                                    ClassicalProofTree leftBranch = (ClassicalProofTree) b.getLeft();
                                    if (!leftBranch.isClosed()) {
                                        openBranches.addLast(leftBranch);
                                        if (IPLTracer.isEnabled()) {
                                            tracer.logInfo("Added left branch to queue");
                                        }
                                    }
                                }
                                if (b.getRight() != null) {
                                    ClassicalProofTree rightBranch = (ClassicalProofTree) b.getRight();
                                    if (!rightBranch.isClosed()) {
                                        openBranches.addLast(rightBranch);
                                        if (IPLTracer.isEnabled()) {
                                            tracer.logInfo("Added right branch to queue");
                                        }
                                    }
                                }
                                break;
                            } else {
                                // PB aplicado pero no creó ramas - resetear y continuar
                                failedFormulas.clear();
                                continue;
                            }
                        } else {
                            // PB no se pudo aplicar - detener para evitar loop infinito
                            if (IPLTracer.isEnabled()) {
                                tracer.logInfo("PB could not be applied - stopping branch to avoid loop");
                            }
                            break;
                        }
                    }
                }
                
                // Line 21: b* ← extend(b)
                // (closure checking is automatic in IPLProofTree)
                
                if (b.isClosed()) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logBranchCompleted(getBranchId(b), true);
                    }
                    break;
                }
            }
            
            // Line 22: end while (branch processing)
            if (!b.isClosed()) {
                // If branch has children, don't mark as completed - children will be processed
                if (b.getLeft() == null && b.getRight() == null) {
                    b.setCompleted(true);
                    T.setOpenCompletedBranch(b);
                    if (IPLTracer.isEnabled()) {
                        tracer.logBranchCompleted(getBranchId(b), false);
                    }
                    // ✅ CORREGIDO: NO hacer break aquí, continuar con la siguiente rama en la cola
                    // break; // ❌ Esto salía del bucle externo y detenía el procesamiento
                } else {
                    if (IPLTracer.isEnabled()) {
                        tracer.logInfo("Branch has children - continuing with child branches");
                    }
                }
            } else {
                if (!T.isClosed()) {
                    strategy.finishBranch(b);
                }
            }
        }
        
        // Line 23: end while (tree processing)
        // Line 24: return T
        if (IPLTracer.isEnabled()) {
            tracer.logAlgorithmEnd(T.isClosed());
        }
        return T;
    }
    
    /**
     * Line 6: Selects a formula φ in branch b which is not completely analyzed.
     * Returns null if all formulas are analyzed.
     * 
     * Strategy: Prioritize formulas with 1-premise rules over those with only 2-premise rules.
     * This ensures that auxiliary premises are generated before they're needed.
     * 
     * Important: We scan the entire tree first looking for 1-premise formulas before
     * selecting any 2-premise formula.
     * 
     * @param failedFormulas Set of formulas that failed to apply rules in this round
     */
    private SignedFormula selectUnanalyzedFormula(ClassicalProofTree b, java.util.Set<SignedFormula> failedFormulas) {
        SignedFormula firstOnePremiseCandidate = null;
        SignedFormula firstTwoPremiseCandidate = null;
        
        main.proofTree.iterator.IProofTreeVeryBasicIterator it = b.getTopDownIterator();
        
        while (it.hasNext()) {
            INode node = it.next();
            if (node instanceof SignedFormulaNode) {
                SignedFormulaNode sfNode = (SignedFormulaNode) node;
                
                // Skip already analyzed formulas
                if (sfNode.getState() == SignedFormulaNodeState.ANALYSED) {
                    continue;
                }
                
                SignedFormula sf = (SignedFormula) sfNode.getContent();
                
                // Skip formulas that failed in this round
                if (failedFormulas.contains(sf)) {
                    continue;
                }
                
                // Skip T⊤ and F⊥
                if (isTopOrBottom(sf)) {
                    continue;
                }
                
                // Skip atomic formulas (they cannot be analyzed)
                if (!(sf.getFormula() instanceof CompositeFormula)) {
                    continue;
                }
                
                // Check if this formula has a 1-premise rule
                if (firstOnePremiseCandidate == null && hasOnePremiseRule(sf)) {
                    firstOnePremiseCandidate = sf;
                    if (IPLTracer.isEnabled()) {
                        tracer.logInfo("1-premise candidate: " + sf);
                    }
                    // Don't return yet - scan the entire tree to see if there are more
                }
                
                // Save as candidate with 2-premise rule
                if (firstTwoPremiseCandidate == null && hasTwoPremiseRule(sf)) {
                    firstTwoPremiseCandidate = sf;
                    if (IPLTracer.isEnabled()) {
                        tracer.logInfo("2-premise candidate: " + sf);
                    }
                }
            }
        }
        
        // Return 1-premise candidate if found, otherwise return 2-premise candidate
        if (firstOnePremiseCandidate != null) {
            if (IPLTracer.isEnabled()) {
                tracer.logFormulaSelected(firstOnePremiseCandidate.toString(), "1-premise priority");
            }
            return firstOnePremiseCandidate;
        }
        
        return firstTwoPremiseCandidate;
    }
    
    /**
     * Checks if a formula has an applicable 1-premise rule.
     */
    private boolean hasOnePremiseRule(SignedFormula sf) {
        if (!(sf.getFormula() instanceof CompositeFormula)) {
            return false;
        }
        
        CompositeFormula comp = (CompositeFormula) sf.getFormula();
        Object ruleListObj = strategy.getMethod().getRules().get("onePremiseRules");
        
        if (ruleListObj == null) {
            return false;
        }
        
        if (!(ruleListObj instanceof rules.structures.OnePremiseRuleList)) {
            return false;
        }
        
        rules.structures.OnePremiseRuleList ruleList = (rules.structures.OnePremiseRuleList) ruleListObj;
        rules.Rule rule = ruleList.get(sf.getSign(), comp.getConnective());
        
        boolean hasRule = rule != null && rule != rules.NullRule.INSTANCE;
        
        return hasRule;
    }
    
    /**
     * Checks if a formula has an applicable 2-premise rule.
     */
    private boolean hasTwoPremiseRule(SignedFormula sf) {
        if (!(sf.getFormula() instanceof CompositeFormula)) {
            return false;
        }
        
        CompositeFormula comp = (CompositeFormula) sf.getFormula();
        Object ruleListObject = strategy.getMethod().getRules().get("twoPremiseRules");
        
        if (!(ruleListObject instanceof rules.structures.IPLConnectiveRoleSignRuleList)) {
            return false;
        }
        
        rules.structures.IPLConnectiveRoleSignRuleList ruleList = 
            (rules.structures.IPLConnectiveRoleSignRuleList) ruleListObject;
        
        // Check if there are any rules for this connective and sign
        java.util.List<rules.Rule> leftRules = ruleList.getMany(comp.getConnective(), 
            rules.KERuleRole.LEFT, sf.getSign());
        java.util.List<rules.Rule> rightRules = ruleList.getMany(comp.getConnective(), 
            rules.KERuleRole.RIGHT, sf.getSign());
        
        return (leftRules != null && !leftRules.isEmpty()) || 
               (rightRules != null && !rightRules.isEmpty());
    }
    
    /**
     * Lines 7-20: Process formula φ according to the algorithm.
     * Returns true if a rule was applied.
     */
    private boolean processFormula(ClassicalProofTree b, SignedFormula phi, SignedFormulaBuilder sfb) {
        boolean applied = false;
        boolean isTPersistent = isTNotPersistent(phi);
        
        // Line 7-9: Try 1-premise rule FIRST
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("Trying 1-premise rules for: " + phi);
        }
        applied = onePremiseApplicator.applySingle(b, sfb, phi);
        
        if (applied) {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("1-premise rule applied");
            }
            // T¬ persistent formulas should NOT be marked as ANALYSED
            // (they already handle this internally in OnePremiseRuleApplicator)
            return true;
        }
        
        // Line 10-20: Try 2-premise rule SECOND
        if (IPLTracer.isEnabled()) {
            tracer.logInfo("Trying 2-premise rules for: " + phi);
        }
        applied = twoPremiseApplicator.applySingle(b, sfb, phi);
        
        if (applied) {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("2-premise rule applied");
            }
            return true;
        }
        
        // NO intentar PB aquí - PB solo se aplica cuando se han intentado
        // reglas de 1 y 2 premisas para TODAS las fórmulas de la rama
        
        // If no rule was applied, mark as analyzed to avoid infinite loops
        // EXCEPT for T¬ persistent formulas (they should remain NOT_ANALYSED)
        if (!isTPersistent) {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("No applicable rule for " + phi + " - marking ANALYSED");
            }
            markAsAnalyzed(b, phi);
        } else {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("No applicable rule for T¬ persistent " + phi + " - keeping NOT_ANALYSED");
            }
        }
        
        return false;
    }
    
    /**
     * Marks a formula as analyzed in the branch.
     */
    private void markAsAnalyzed(ClassicalProofTree b, SignedFormula sf) {
        SignedFormulaNode node = b.getNode(sf);
        if (node != null) {
            node.setState(SignedFormulaNodeState.ANALYSED);
        }
    }
    
    /**
     * Checks if a formula is T⊤ or F⊥.
     */
    private boolean isTopOrBottom(SignedFormula sf) {
        String formulaStr = sf.getFormula().toString();
        return formulaStr.equals("TOP") || formulaStr.equals("BOTTOM");
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
    private boolean isTNotPersistent(SignedFormula sf) {
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
     * Gets a readable ID for a branch (for debugging).
     */
    private String getBranchId(ClassicalProofTree b) {
        if (b instanceof IPLProofTree) {
            return ((IPLProofTree) b).getBranchId();
        }
        return "unknown";
    }
}
