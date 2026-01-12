package logicalSystems.ipl;

import java.util.HashSet;
import java.util.Set;
import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicInteger;

import logic.formulas.Formula;
import logic.formulas.CompositeFormula;
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.FormulaSign;
import logic.signedFormulas.SignedFormulaFactory;
import logic.labelledFormulas.LabelledFormula;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.Context;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import main.proofTree.iterator.IProofTreeVeryBasicIterator;
import main.proofTree.origin.IOrigin;
import main.strategy.memorySaver.OptimizedClassicalProofTree;

/**
 * ProofTree específico para IPL que implementa:
 * 1. Reglas de cierre correctas: T A: ci, F A: cj, ci ⪯ cj → ×
 * 2. Monotonicidad explícita: cuando se añade T A : ci, propagar a todos cj donde ci ≤ cj
 * 3. Registro de instancias por grupo de accesibilidad (rinstances) para evitar bucles
 * 4. Aislamiento de etiquetas por rama: cada rama tiene su propio espacio de etiquetas
 * 
 * Basado en el paper: "Free-variable KE tableaux for IPL"
 * 
 * NOTA IMPORTANTE: rinstances es por grupo de accesibilidad (no global).
 * Esto permite que ramas hermanas apliquen la misma regla independientemente
 * (porque generan etiquetas locales diferentes), mientras previene que
 * ramas descendientes repitan aplicaciones de ancestros.
 */
public class IPLProofTree extends OptimizedClassicalProofTree {
    
    /**
     * Registro de instancias de reglas operacionales aplicadas POR RAMA (rinstances).
     * Similar a pbRinstancesByBranch, tracking por grupo de accesibilidad.
     * 
     * Mapa: branchId -> Set de instancias de reglas aplicadas en esa rama
     * 
     * Formato de instancia: "regla:premisa1:premisa2:..." (representación String)
     * 
     * IMPORTANTE: Cuando una regla genera nuevas etiquetas (como F→1, F¬1),
     * esas etiquetas son locales a la rama donde se aplica. Por eso rinstances
     * debe ser por grupo de accesibilidad, no global.
     */
    private Map<String, Set<String>> rinstancesByBranch;
    
    /**
     * Branch ID: identificador único de esta rama.
     * El tronco principal tiene ID "root".
     * Las ramas creadas por bifurcación (PB) reciben IDs únicos.
     */
    private String branchId;
    
    /**
     * Mapa compartido que asocia cada etiqueta (por su toString()) con su branchId.
     * Permite determinar qué etiquetas son accesibles en cada rama.
     */
    private Map<String, String> sharedLabelBranchMap;
    
    /**
     * Registro de instancias de PB aplicadas POR RAMA (tracking por grupo de accesibilidad).
     * Cada entrada registra que se aplicó PB en una rama específica sobre una combinación
     * (premisa mayor + regla + auxiliar requerido).
     * 
     * Mapa: branchId -> Set de instancias de PB aplicadas en esa rama
     * 
     * IMPORTANTE: Se registra en la rama DONDE SE APLICA PB, no donde está la fórmula.
     * Esto permite que ramas hermanas apliquen PB independientemente, mientras que
     * previene loops infinitos (ramas descendientes no aplicarán PB de nuevo).
     */
    private Map<String, Set<String>> pbRinstancesByBranch;
    
    /**
     * Contador estático para generar branch IDs únicos
     */
    private static AtomicInteger branchIdCounter = new AtomicInteger(0);

    public IPLProofTree(SignedFormulaNode aNode) {
        super(aNode);
        this.branchId = "root"; // El tronco principal
        this.sharedLabelBranchMap = new HashMap<>();
        this.pbRinstancesByBranch = new HashMap<>();
        this.rinstancesByBranch = new HashMap<>(); // Nuevo: rinstances por rama
    }
    
    /**
     * Constructor para ramas que comparten labelBranchMap, pbRinstancesByBranch y rinstancesByBranch de la raíz
     */
    private IPLProofTree(SignedFormulaNode aNode,
                         Map<String, String> sharedLabelBranchMap,
                         Map<String, Set<String>> pbRinstancesByBranch,
                         Map<String, Set<String>> rinstancesByBranch,
                         String branchId) {
        super(aNode);
        // ✅ Inicialización defensiva: nunca permitir mapas null
        this.sharedLabelBranchMap = (sharedLabelBranchMap != null) ? sharedLabelBranchMap : new HashMap<>();
        this.pbRinstancesByBranch = (pbRinstancesByBranch != null) ? pbRinstancesByBranch : new HashMap<>();
        this.rinstancesByBranch = (rinstancesByBranch != null) ? rinstancesByBranch : new HashMap<>();
        this.branchId = branchId;
    }

    @Override
    protected IProofTree makeInstance(INode aNode) {
        // Las ramas comparten labelBranchMap, pbRinstancesByBranch y rinstancesByBranch del árbol raíz
        // pero reciben un nuevo branch ID único
        String newBranchId = "branch_" + branchIdCounter.incrementAndGet();
        return new IPLProofTree((SignedFormulaNode) aNode, 
                                sharedLabelBranchMap, pbRinstancesByBranch, 
                                rinstancesByBranch, newBranchId);
    }
    
    /**
     * Verifica si una instancia de regla ya fue aplicada en el grupo de accesibilidad de esta rama.
     * 
     * El grupo de accesibilidad de una rama incluye esa rama y todos sus ancestros.
     * Dos ramas están en el mismo grupo si una es ancestro de la otra.
     * 
     * IMPORTANTE: Verifica en la rama actual Y en todas las ancestras (grupo de accesibilidad).
     * Esto previene loops infinitos cuando ramas descendientes intentan aplicar la misma
     * regla que ya se aplicó en una rama ancestra.
     * 
     * Sin embargo, permite que ramas hermanas (que no comparten ancestros comunes más allá de root)
     * apliquen la misma regla independientemente, porque generan etiquetas locales diferentes.
     * 
     * @param ruleInstance la instancia de regla a verificar (formato: "regla:premisa1:premisa2")
     * @return true si la regla ya fue aplicada en el grupo de accesibilidad, false en caso contrario
     */
    public boolean wasRuleInstanceApplied(String ruleInstance) {
        // Verificar en esta rama
        Set<String> branchRinstances = rinstancesByBranch.get(branchId);
        if (branchRinstances != null && branchRinstances.contains(ruleInstance)) {
            return true;
        }
        
        // Verificar en todas las ramas ancestras (están en el mismo grupo de accesibilidad)
        IProofTree current = this.getParent();
        while (current != null) {
            if (current instanceof IPLProofTree) {
                IPLProofTree iplParent = (IPLProofTree) current;
                String parentBranchId = iplParent.getBranchId();
                Set<String> parentRinstances = rinstancesByBranch.get(parentBranchId);
                if (parentRinstances != null && parentRinstances.contains(ruleInstance)) {
                    return true;
                }
            }
            current = current.getParent();
        }
        
        return false;
    }
    
    /**
     * Registra una nueva instancia de regla aplicada en esta rama.
     * 
     * IMPORTANTE: Se registra en la rama actual (donde se aplica la regla).
     * Esto permite que ramas hermanas apliquen la misma regla independientemente,
     * mientras que previene que ramas descendientes repitan la aplicación.
     * 
     * @param ruleInstance la instancia de regla a registrar (formato: "regla:premisa1:premisa2")
     */
    public void registerRuleInstance(String ruleInstance) {
        Set<String> branchRinstances = rinstancesByBranch.computeIfAbsent(branchId, k -> new HashSet<>());
        branchRinstances.add(ruleInstance);
        System.out.println("📝 Registrado en rinstances (rama " + branchId + "): " + ruleInstance);
    }
    
    /**
     * Obtiene el branch ID de esta rama
     */
    public String getBranchId() {
        return branchId;
    }
    
    /**
     * Verifica si una instancia de PB ya fue aplicada en el grupo de accesibilidad de esta rama.
     * 
     * El grupo de accesibilidad de una rama incluye esa rama y todos sus ancestros.
     * Dos ramas están en el mismo grupo si una es ancestro de la otra.
     * 
     * IMPORTANTE: Verifica en la rama actual Y en todas las ancestras (grupo de accesibilidad).
     * Esto previene loops infinitos cuando ramas descendientes intentan aplicar PB sobre
     * la misma combinación que ya se aplicó en una rama ancestra.
     * 
     * Sin embargo, permite que ramas hermanas (que no comparten ancestros comunes más allá de root)
     * apliquen PB sobre la misma combinación independientemente.
     * 
     * @param pbInstance la instancia de PB a verificar (formato: "PB:regla:premisaMayor:auxiliarRequerido")
     * @return true si PB ya fue aplicado en el grupo de accesibilidad, false en caso contrario
     */
    public boolean wasPBRuleInstanceAppliedInAccessibilityGroup(String pbInstance) {
        // Verificar en esta rama
        Set<String> branchPbRinstances = pbRinstancesByBranch.get(branchId);
        if (branchPbRinstances != null && branchPbRinstances.contains(pbInstance)) {
            return true;
        }
        
        // Verificar en todas las ramas ancestras (están en el mismo grupo de accesibilidad)
        IProofTree current = this.getParent();
        while (current != null) {
            if (current instanceof IPLProofTree) {
                IPLProofTree iplParent = (IPLProofTree) current;
                String parentBranchId = iplParent.getBranchId();
                Set<String> parentPbRinstances = pbRinstancesByBranch.get(parentBranchId);
                if (parentPbRinstances != null && parentPbRinstances.contains(pbInstance)) {
                    return true;
                }
            }
            current = current.getParent();
        }
        
        return false;
    }
    
    /**
     * Registra una nueva instancia de PB aplicada en una rama específica.
     * 
     * IMPORTANTE: Se registra en la rama DONDE SE APLICA PB (targetBranchId),
     * no donde está la fórmula. Esto permite que:
     * - Ramas hermanas apliquen PB sobre la misma combinación independientemente
     *   (no comparten el mismo branchId, así que no ven el registro de la otra)
     * - Ramas descendientes no apliquen PB de nuevo (están en el mismo grupo de accesibilidad,
     *   así que verán el registro en la rama ancestra)
     * 
     * @param pbInstance la instancia de PB a registrar (formato: "PB:regla:premisaMayor:auxiliarRequerido")
     * @param targetBranchId la rama donde registrar (donde se aplicó PB)
     */
    public void registerPBRuleInstance(String pbInstance, String targetBranchId) {
        Set<String> branchPbRinstances = pbRinstancesByBranch.computeIfAbsent(targetBranchId, k -> new HashSet<>());
        branchPbRinstances.add(pbInstance);
        System.out.println("📝 Registrado PB en rinstances (rama " + targetBranchId + "): " + pbInstance);
    }
    
    /**
     * Registra una nueva instancia de PB aplicada en esta rama.
     * Versión conveniente que registra en la rama actual.
     * 
     * @param pbInstance la instancia de PB a registrar
     */
    public void registerPBRuleInstance(String pbInstance) {
        registerPBRuleInstance(pbInstance, branchId);
    }
    
    /**
     * Registra una etiqueta con el branch ID actual.
     * @return true si la etiqueta era nueva (no estaba registrada antes)
     */
    public boolean registerLabel(FormulaLabel label) {
        if (label != null && sharedLabelBranchMap != null) {
            String labelKey = label.toString();
            if (!sharedLabelBranchMap.containsKey(labelKey)) {
                sharedLabelBranchMap.put(labelKey, branchId);
                System.out.println("🏷️  Etiqueta " + labelKey + " registrada en rama " + branchId);
                return true; // Etiqueta nueva
            }
        }
        return false; // Etiqueta ya existía
    }
    
    /**
     * Verifica si una etiqueta es accesible en la rama actual.
     * Una etiqueta es accesible si:
     * - Fue creada en el tronco común (branchId = "root")
     * - Fue creada en esta rama (branchId == this.branchId)
     * - Fue creada en alguna rama ancestra (padre, abuelo, etc.)
     */
    public boolean isLabelAccessible(FormulaLabel label) {
        if (label == null) {
            return true; // Las etiquetas nulas son siempre accesibles
        }
        
        // ✅ Verificación defensiva
        if (sharedLabelBranchMap == null) {
            return true; // Si no hay mapa, todas las etiquetas son accesibles
        }
        
        String labelKey = label.toString();
        String labelBranch = sharedLabelBranchMap.get(labelKey);
        
        if (labelBranch == null) {
            // Etiqueta no registrada, probablemente del sistema (TOP, BOTTOM)
            return true;
        }
        
        // Accesible si es del tronco común
        if ("root".equals(labelBranch)) {
            return true;
        }
        
        // Accesible si es de esta rama
        if (branchId.equals(labelBranch)) {
            return true;
        }
        
        return isAncestorBranch(labelBranch);
    }
    
    /**
     * Verifica si una rama (identificada por su branchId) es ancestra de la rama actual.
     * Recorre hacia arriba desde la rama actual usando getParent() hasta encontrar
     * la rama especificada o hasta llegar a null (sin más padres).
     * 
     * Nota: Este método se llama solo si la etiqueta NO fue creada en "root" ni en
     * la rama actual, así que solo buscamos en ramas ancestras intermedias.
     * 
     * @param ancestorBranchId el branchId de la rama ancestra a verificar
     * @return true si la rama especificada es ancestra de la rama actual
     */
    private boolean isAncestorBranch(String ancestorBranchId) {
        IProofTree current = this.getParent();
        
        // Recorrer hacia arriba en la jerarquía de ramas
        while (current != null) {
            // Solo podemos verificar branchId si el padre es un IPLProofTree
            if (current instanceof IPLProofTree) {
                IPLProofTree iplParent = (IPLProofTree) current;
                String parentBranchId = iplParent.getBranchId();
                
                // Si encontramos la rama ancestra, retornar true
                if (ancestorBranchId.equals(parentBranchId)) {
                    return true;
                }
                
                // Continuar con el siguiente ancestro
                current = current.getParent();
            } else {
                // Si el padre no es IPLProofTree, no podemos continuar
                break;
            }
        }
        
        return false; // No encontramos la rama ancestra en la cadena de ancestros
    }
    
    /**
     * ✅ EXTENSIÓN b* IMPLÍCITA: Override addLast para SOLO registrar etiquetas.
     * 
     * Ya NO propagamos fórmulas físicamente (monotonicidad explícita eliminada).
     * La monotonicidad se maneja implícitamente a través de extendBranch() y isInExtendedBranch().
     * 
     * Esto previene:
     * - Explosión de fórmulas en el árbol
     * - Loops infinitos causados por reglas que generan nuevas etiquetas
     * - Propagación innecesaria de fórmulas
     */
    @Override
    public void addLast(INode aNode) {
        super.addLast(aNode);
        
        // Solo procesar SignedFormulaNode
        if (!(aNode instanceof SignedFormulaNode)) {
            return;
        }
        
        SignedFormulaNode sfNode = (SignedFormulaNode) aNode;
        SignedFormula sf = (SignedFormula) sfNode.getContent();
        
        // Registrar la etiqueta de esta fórmula en el branch actual
        if (sf instanceof LabelledFormula) {
            LabelledFormula lf = (LabelledFormula) sf;
            registerLabel(lf.getLabel());
        }
        
        // ✅ NO MÁS MONOTONICIDAD EXPLÍCITA NI RETROACTIVA
        // La extensión b* se calcula dinámicamente cuando se necesita
    }

    @Override
    protected void updateMultimap(SignedFormulaNode aNode) {
        // Para IPL, NO ejecutar la detección clásica, solo usar reglas IPL específicas
        SignedFormula sf = (SignedFormula) aNode.getContent();
        getFsmm().put(sf.getFormula(), sf.getSign());
        
        // Debug: verificar tipo de etiqueta
        FormulaLabel label = sf.getLabel();
        System.out.println("🔄 IPL updateMultimap: " + sf + " (label type: " + label.getClass().getSimpleName() + ")");
        
        // Verificar reglas de cierre IPL
        if (detectIPLContradiction(aNode)) {
            System.out.println("🔴 IPL: CONTRADICTION DETECTED for " + sf);
            setClosingReason(sf);
            setLocallyClosed(true);
        }
    }
    
    /**
     * ✅ EXTENSIÓN b* IMPLÍCITA: Detecta contradicciones según las reglas de cierre IPL:
     * 1) T A: ci, F A: cj, ci ⪯ cj → ×
     * 
     * Ahora busca fórmulas en b* (extensión de la rama) en lugar de solo en b.
     * Esto es crucial para que el sistema funcione correctamente sin monotonicidad explícita.
     */
    private boolean detectIPLContradiction(SignedFormulaNode aNode) {
        SignedFormula newSf = (SignedFormula) aNode.getContent();
        FormulaLabel newLabel = newSf.getLabel();
        Formula newFormula = newSf.getFormula();
        FormulaSign newSign = newSf.getSign();
        
        System.out.println("🔍 IPL Closure (b*): Checking " + newSign + " " + newFormula + " " + newLabel);
        
        // Obtener el Context para verificar relaciones de orden
        Context context = getContextFromLabel(newLabel);
        if (context == null) {
            System.out.println("⚠️ IPL Closure: No Context found for label " + newLabel);
            return false; // Sin Context, no podemos verificar relaciones de orden
        }
        
        System.out.println("🔍 IPL Closure: Context has " + context.getLabels().size() + " labels: " + context.getLabels());
        
        // ✅ Calcular b* (extensión de la rama)
        Set<SignedFormula> bStar = extendBranch();
        System.out.println("🔍 IPL Closure: b* contiene " + bStar.size() + " fórmulas (b tiene " + countFormulasInB() + ")");
        System.out.println("🔍 IPL Closure (DEBUG-SIGN): newSign = " + newSign + " (class: " + (newSign != null ? newSign.getClass().getName() : "null") + ")");
        System.out.println("🔍 IPL Closure (DEBUG-SIGN): IPLSigns.TRUE = " + IPLSigns.TRUE + " (identity: " + System.identityHashCode(IPLSigns.TRUE) + ")");
        System.out.println("🔍 IPL Closure (DEBUG-SIGN): IPLSigns.FALSE = " + IPLSigns.FALSE + " (identity: " + System.identityHashCode(IPLSigns.FALSE) + ")");
        if (newSign != null) {
            System.out.println("🔍 IPL Closure (DEBUG-SIGN): newSign identity = " + System.identityHashCode(newSign));
            System.out.println("🔍 IPL Closure (DEBUG-SIGN): newSign == IPLSigns.TRUE? " + (newSign == IPLSigns.TRUE));
            System.out.println("🔍 IPL Closure (DEBUG-SIGN): newSign == IPLSigns.FALSE? " + (newSign == IPLSigns.FALSE));
        }
        
        // Regla 1: T A: ci, F A: cj, ci ⪯ cj → ×
        if (newSign.equals(IPLSigns.TRUE)) {
            System.out.println("🔍 IPL Closure: ENTERED TRUE block");

            // Buscar todas las instancias de F A en b*
            List<SignedFormula> oppositeFormulas = bStar.stream()
                .filter(sf -> sf.getSign().equals(IPLSigns.FALSE) && 
                             sf.getFormula().equals(newFormula) &&
                             sf instanceof LabelledFormula)
                .collect(java.util.stream.Collectors.toList());
                
            if (!oppositeFormulas.isEmpty()) {
                System.out.println("🔍 IPL Closure: Encontradas " + oppositeFormulas.size() + " instancias de F " + newFormula + " en b*");
                
                boolean newLabelAccessible = isLabelAccessible(newLabel);
                if (!newLabelAccessible) {
                    System.out.println("⚠️ IPL Closure: Etiqueta " + newLabel + " NO es accesible en rama " + this.branchId + ", ignorando");
                    return false;
                }
                
                // Verificar cada instancia de F A para ver si alguna cumple ci ⪯ cj
                for (SignedFormula oppositeSigned : oppositeFormulas) {
                    FormulaLabel oppositeLabel = oppositeSigned.getLabel();
                    
                    boolean oppositeLabelAccessible = isLabelAccessible(oppositeLabel);
                    if (!oppositeLabelAccessible) {
                        continue; // Saltar esta instancia si no es accesible
                    }
                    
                    // Verificar si ci ⪯ cj (newLabel ⪯ oppositeLabel)
                    boolean isLowerOrEqualResult = isLowerOrEqual(context, newLabel, oppositeLabel);
                    System.out.println("🔍 IPL Closure: Verificando " + newLabel + " ⪯ " + oppositeLabel + 
                                     " - resultado: " + isLowerOrEqualResult);
                    if (isLowerOrEqualResult) {
                        System.out.println("🔴 IPL Closure Rule 1 (b*): T " + newFormula + " " + newLabel + 
                                         ", F " + newFormula + " " + oppositeLabel + 
                                         " with " + newLabel + " ⪯ " + oppositeLabel);
                        return true;
                    }
                }
                System.out.println("❌ IPL Closure: Ninguna instancia de F " + newFormula + " en b* cumple " + newLabel + " ⪯ cj");
            } else {
                System.out.println("🔍 IPL Closure: No se encontró F " + newFormula + " en b*");
            }
        }
        
        if (newSign.equals(IPLSigns.FALSE)) {
            System.out.println("🔍 IPL Closure: ENTERED FALSE block");
            // Buscar todas las instancias de T A en b*
            System.out.println("🔍 IPL Closure (DEBUG): newFormula = " + newFormula + " (" + newFormula.getClass().getName() + ")");
            System.out.println("🔍 IPL Closure (DEBUG): bStar tiene " + bStar.size() + " fórmulas:");
            int debugCount = 0;
            for (SignedFormula sfDebug : bStar) {
                if (sfDebug.getSign().equals(IPLSigns.TRUE) && sfDebug instanceof LabelledFormula) {
                    System.out.println("  [" + (debugCount++) + "] " + sfDebug + " (formula: " + sfDebug.getFormula() + ", equals? " + sfDebug.getFormula().equals(newFormula) + ")");
                    if (debugCount > 15) {
                        System.out.println("  ... (más fórmulas)");
                        break;
                    }
                }
            }
            
            List<SignedFormula> oppositeFormulas = bStar.stream()
                .filter(sf -> sf.getSign().equals(IPLSigns.TRUE) && 
                             sf.getFormula().equals(newFormula) &&
                             sf instanceof LabelledFormula)
                .collect(java.util.stream.Collectors.toList());
                
            if (!oppositeFormulas.isEmpty()) {
                System.out.println("🔍 IPL Closure: Encontradas " + oppositeFormulas.size() + " instancias de T " + newFormula + " en b*");
                
                boolean newLabelAccessible = isLabelAccessible(newLabel);
                if (!newLabelAccessible) {
                    System.out.println("⚠️ IPL Closure: Etiqueta " + newLabel + " NO es accesible en rama " + this.branchId + ", ignorando");
                    return false;
                }
                
                // Verificar cada instancia de T A para ver si alguna cumple ci ⪯ cj
                for (SignedFormula oppositeSigned : oppositeFormulas) {
                    FormulaLabel oppositeLabel = oppositeSigned.getLabel();
                    
                    boolean oppositeLabelAccessible = isLabelAccessible(oppositeLabel);
                    if (!oppositeLabelAccessible) {
                        continue; // Saltar esta instancia si no es accesible
                    }
                    
                    // Verificar si ci ⪯ cj (oppositeLabel ⪯ newLabel)
                    boolean isLowerOrEqualResult = isLowerOrEqual(context, oppositeLabel, newLabel);
                    System.out.println("🔍 IPL Closure: Verificando " + oppositeLabel + " ⪯ " + newLabel + 
                                     " - resultado: " + isLowerOrEqualResult);
                    if (isLowerOrEqualResult) {
                        System.out.println("🔴 IPL Closure Rule 1 (b*): T " + newFormula + " " + oppositeLabel + 
                                         ", F " + newFormula + " " + newLabel + 
                                         " with " + oppositeLabel + " ⪯ " + newLabel);
                        return true;
                    }
                }
                System.out.println("❌ IPL Closure: Ninguna instancia de T " + newFormula + " en b* cumple ci ⪯ " + newLabel);
            } else {
                System.out.println("🔍 IPL Closure: No se encontró T " + newFormula + " en b*");
            }
        }
        
        
        return false;
    }
    
    /**
     * Cuenta cuántas fórmulas hay físicamente en b (no en b*)
     */
    private int countFormulasInB() {
        int count = 0;
        IProofTreeVeryBasicIterator it = this.getTopDownIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (node instanceof SignedFormulaNode) {
                count++;
            }
        }
        return count;
    }
    
    /**
     * Obtiene el Context desde una FormulaLabel (si es ContextFormulaLabel)
     */
    private Context getContextFromLabel(FormulaLabel label) {
        if (label instanceof ContextFormulaLabel) {
            return ((ContextFormulaLabel) label).getContext();
        }
        return null;
    }
    
    // ✅ ELIMINADO: propagateRetroactiveMonotonicity()
    // Ya no se necesita porque la monotonicidad se maneja implícitamente vía extendBranch()
    
    /**
     * Verifica si label1 ⪯ label2 en el contexto dado
     */
    private boolean isLowerOrEqual(Context context, FormulaLabel label1, FormulaLabel label2) {
        if (label1.equals(label2)) {
            return true; // Reflexiva: ci ⪯ ci
        }
        return context.isLowerOrEqualTo(label1, label2);
    }
    
    /**
     * Busca una fórmula con signo específico en la rama actual y sus ancestras.
     * Las ramas hijas heredan todas las fórmulas de las ramas ancestras, así que
     * debemos buscar en toda la cadena de ancestros hasta la raíz.
     * 
     * NOTA: No buscamos en ramas hermanas, solo en la cadena de ancestros.
     * Compara por equals() y toString() para manejar diferentes instancias de objetos.
     * 
     * @deprecated Usar findAllFormulasWithSign para buscar todas las instancias
     */
    private SignedFormula findFormulaWithSign(Formula formula, Object sign) {
        java.util.List<SignedFormula> results = findAllFormulasWithSign(formula, sign);
        return results.isEmpty() ? null : results.get(0);
    }
    
    /**
     * Busca TODAS las fórmulas con signo específico en la rama actual y sus ancestras.
     * Las ramas hijas heredan todas las fórmulas de las ramas ancestras, así que
     * debemos buscar en toda la cadena de ancestros hasta la raíz.
     * 
     * NOTA: No buscamos en ramas hermanas, solo en la cadena de ancestros.
     * Compara por equals() y toString() para manejar diferentes instancias de objetos.
     * 
     * @param formula la fórmula a buscar
     * @param sign el signo (T o F)
     * @return lista de todas las SignedFormula encontradas con el signo y fórmula especificados
     */
    private List<SignedFormula> findAllFormulasWithSign(Formula formula, Object sign) {
        List<SignedFormula> results = new ArrayList<>();
        IProofTreeVeryBasicIterator it = this.getTopDownIterator();
        int count = 0;
        while (it.hasNext()) {
            INode node = it.next();
            if (node instanceof SignedFormulaNode) {
                SignedFormula sf = (SignedFormula) node.getContent();
                
                // Comparar por signo y por representación de fórmula (toString)
                // Necesario porque diferentes instancias de FormulaSign pueden no ser equals()
                boolean signMatches = sf.getSign().equals(sign) || 
                                     sf.getSign().toString().equals(sign.toString());
                boolean formulaMatches = sf.getFormula().equals(formula) || 
                                        sf.getFormula().toString().equals(formula.toString());
                
                if (signMatches && formulaMatches) {
                    results.add(sf);
                    if (count < 5) {
                        System.out.println("  ✅ DEBUG: Encontrado " + sf);
                    }
                }
                count++;
            }
        }
        if (results.isEmpty()) {
            System.out.println("  ❌ DEBUG: No encontrado después de revisar " + count + " nodos");
        }
        return results;
    }
    
    /**
     * Busca una fórmula con signo, fórmula y etiqueta específica en el grupo de accesibilidad
     * (rama actual y sus ancestras).
     * 
     * Usado para verificar si las fórmulas que se generarían al aplicar PB ya existen,
     * evitando así aplicar PB redundante.
     * 
     * @param formula la fórmula a buscar
     * @param sign el signo (T o F)
     * @param label la etiqueta específica a buscar
     * @return la SignedFormula encontrada, o null si no existe
     */
    public SignedFormula findFormulaWithSignAndLabel(Formula formula, Object sign, FormulaLabel label) {
        IProofTreeVeryBasicIterator it = this.getTopDownIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (node instanceof SignedFormulaNode) {
                SignedFormula sf = (SignedFormula) node.getContent();
                
                // Comparar signo
                boolean signMatches = sf.getSign().equals(sign) || 
                                     sf.getSign().toString().equals(sign.toString());
                if (!signMatches) continue;
                
                // Comparar fórmula
                boolean formulaMatches = sf.getFormula().equals(formula) || 
                                        sf.getFormula().toString().equals(formula.toString());
                if (!formulaMatches) continue;
                
                // Comparar etiqueta (solo si ambas son LabelledFormula)
                if (sf instanceof logic.labelledFormulas.LabelledFormula && 
                    label instanceof logic.labelledFormulas.ContextFormulaLabel) {
                    logic.labelledFormulas.LabelledFormula lf = (logic.labelledFormulas.LabelledFormula) sf;
                    FormulaLabel sfLabel = lf.getLabel();
                    
                    // Comparar etiquetas: deben ser iguales (mismo índice y mismo contexto)
                    if (sfLabel.equals(label) || sfLabel.toString().equals(label.toString())) {
                        return sf;
                    }
                } else if (sf instanceof logic.labelledFormulas.LabelledFormula) {
                    // Si sf tiene etiqueta pero label no es ContextFormulaLabel, comparar toString
                    logic.labelledFormulas.LabelledFormula lf = (logic.labelledFormulas.LabelledFormula) sf;
                    if (lf.getLabel().toString().equals(label.toString())) {
                        return sf;
                    }
                }
            }
        }
        return null;
    }
    
    /**
     * ✅ EXTENSIÓN b* IMPLÍCITA: Calcula la extensión de la rama actual según Definition 5.3 del paper.
     * 
     * La extensión b* de una rama b es el conjunto de ls-formulas que incluye:
     * 1. Todas las fórmulas en b
     * 2. T A: cj ∈ b*, para cada cj ∈ Cb tal que ci ⪯b cj y T A: ci está en b
     * 3. F A: ci ∈ b*, para cada ci ∈ Cb tal que ci ⪯b cj y F A: cj está en b
     * 4. F A: cj ∈ b*, para cada cj ∈ Cb tal que ci ⪯b cj y F A: xi está en b
     * 
     * Este método calcula b* dinámicamente SIN agregar las fórmulas físicamente al árbol.
     * Esto previene la explosión de fórmulas y los loops infinitos causados por monotonicidad explícita.
     * 
     * @return Set de SignedFormula que representa b*
     */
    public Set<SignedFormula> extendBranch() {
        Set<SignedFormula> bStar = new HashSet<>();
        List<SignedFormula> formulasInB = new ArrayList<>();
        
        // Paso 1: Recolectar todas las fórmulas en b (rama actual Y ramas ancestras)
        // En el sistema de proof tree, las ramas hijas no tienen físicamente las fórmulas de las ramas padre
        // Necesitamos recorrer la rama actual y todas sus ancestras
        IPLProofTree currentTree = this;
        while (currentTree != null) {
            IProofTreeVeryBasicIterator it = currentTree.getTopDownIterator();
            while (it.hasNext()) {
                INode node = it.next();
                if (node instanceof SignedFormulaNode) {
                    SignedFormulaNode sfNode = (SignedFormulaNode) node;
                    SignedFormula sf = (SignedFormula) sfNode.getContent();
                    // Usar Set para evitar duplicados
                    if (bStar.add(sf)) {
                        formulasInB.add(sf);
                    }
                }
            }
            // Subir al padre
            IProofTree parent = currentTree.getParent();
            currentTree = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        }
        
        // Paso 2: Aplicar monotonicidad implícita según Definition 5.3
        
        // Obtener todas las etiquetas constantes en la rama (Cb)
        Set<FormulaLabel> constantLabels = new HashSet<>();
        for (SignedFormula sf : formulasInB) {
            if (sf instanceof LabelledFormula) {
                LabelledFormula lf = (LabelledFormula) sf;
                FormulaLabel label = lf.getLabel();
                // Solo etiquetas constantes (no variables)
                if (label != null && label instanceof ContextFormulaLabel) {
                    constantLabels.add(label);
                }
            }
        }
        
        Context context = null;
        if (!constantLabels.isEmpty()) {
            FormulaLabel anyLabel = constantLabels.iterator().next();
            context = getContextFromLabel(anyLabel);
        }
        
        if (context == null) {
            return bStar; // Sin Context, no hay monotonicidad
        }
        
        // Regla 2: T A: cj ∈ b*, para cada cj ∈ Cb tal que ci ⪯b cj y T A: ci está en b
        for (SignedFormula sf : formulasInB) {
            if (sf.getSign().equals(IPLSigns.TRUE) && sf instanceof LabelledFormula) {
                LabelledFormula lf = (LabelledFormula) sf;
                FormulaLabel ci = lf.getLabel();
                
                if (ci == null || !isLabelAccessible(ci)) {
                    continue;
                }
                
                // Para cada cj ∈ Cb tal que ci ⪯ cj
                for (FormulaLabel cj : constantLabels) {
                    if (!isLabelAccessible(cj)) {
                        continue;
                    }
                    
                    if (!ci.equals(cj) && context.isLowerOrEqualTo(ci, cj)) {
                        // Crear T A: cj
                        SignedFormula baseSf = lf.getSignedFormula();
                        LabelledFormula propagated = new LabelledFormula(cj, baseSf);
                        bStar.add(propagated);
                    }
                }
            }
        }
        
        // Regla 3: F A: ci ∈ b*, para cada ci ∈ Cb tal que ci ⪯b cj y F A: cj está en b
        for (SignedFormula sf : formulasInB) {
            if (sf.getSign().equals(IPLSigns.FALSE) && sf instanceof LabelledFormula) {
                LabelledFormula lf = (LabelledFormula) sf;
                FormulaLabel cj = lf.getLabel();
                
                if (cj == null || !isLabelAccessible(cj)) {
                    continue;
                }
                
                // Para cada ci ∈ Cb tal que ci ⪯ cj
                for (FormulaLabel ci : constantLabels) {
                    if (!isLabelAccessible(ci)) {
                        continue;
                    }
                    
                    if (!ci.equals(cj) && context.isLowerOrEqualTo(ci, cj)) {
                        // Crear F A: ci
                        SignedFormula baseSf = lf.getSignedFormula();
                        LabelledFormula propagated = new LabelledFormula(ci, baseSf);
                        bStar.add(propagated);
                    }
                }
            }
        }
        
        // Regla 4: F A: cj ∈ b*, para cada cj ∈ Cb tal que ci ⪯b cj y F A: xi está en b
        // Nota: Esta implementación usa Table 2 (sin variables), así que esta regla no aplica
        // Si se implementaran variables en el futuro, se agregaría aquí
        
        // Regla 5 (Definition 5.6 línea 670): Si T¬A: ci ∈ b, entonces F A: cj ∈ b* para cada cj >= ci
        // Esta es la regla que hace que las conclusiones de T¬ existan implícitamente en b*
        // Crear un factory temporal para crear las fórmulas signadas
        SignedFormulaFactory tempFactory = new SignedFormulaFactory();
        
        for (SignedFormula sf : formulasInB) {
            if (sf.getSign().equals(IPLSigns.TRUE) && sf instanceof LabelledFormula) {
                LabelledFormula lf = (LabelledFormula) sf;
                Formula formula = lf.getFormula();
                
                // Verificar si es T¬A (negación)
                if (formula instanceof CompositeFormula) {
                    CompositeFormula comp = (CompositeFormula) formula;
                    if (comp.getConnective().equals(IPLConnectives.NOT)) {
                        // Es T¬A
                        FormulaLabel ci = lf.getLabel();
                        if (ci == null || !isLabelAccessible(ci)) {
                            continue;
                        }
                        
                        // Para cada cj >= ci, agregar F A: cj a b*
                        Formula innerA = comp.getImmediateSubformulas().get(0);
                        for (FormulaLabel cj : constantLabels) {
                            if (!isLabelAccessible(cj)) {
                                continue;
                            }
                            
                            if (context.isLowerOrEqualTo(ci, cj)) {
                                // Crear F A: cj implícitamente en b*
                                // NO se agrega físicamente a b, solo está en b*
                                SignedFormula innerSigned = tempFactory.createSignedFormula(IPLSigns.FALSE, innerA);
                                LabelledFormula tneg_derived = new LabelledFormula(cj, innerSigned);
                                bStar.add(tneg_derived);
                            }
                        }
                    }
                }
            }
        }
        
        return bStar;
    }
    
    /**
     * Verifica si una fórmula existe en la extensión b* de la rama actual.
     * Esto es más eficiente que calcular toda b* cuando solo necesitamos verificar una fórmula.
     * 
     * @param formula la fórmula a buscar
     * @return true si la fórmula está en b*, false en caso contrario
     */
    public boolean isInExtendedBranch(SignedFormula formula) {
        // Primero verificar si está directamente en b
        if (getNode(formula) != null) {
            return true;
        }
        
        // Si no está en b, verificar si puede derivarse por monotonicidad
        if (!(formula instanceof LabelledFormula)) {
            return false;
        }
        
        LabelledFormula targetLf = (LabelledFormula) formula;
        FormulaLabel targetLabel = targetLf.getLabel();
        Formula targetFormula = targetLf.getFormula();
        
        if (targetLabel == null || !isLabelAccessible(targetLabel)) {
            return false;
        }
        
        Context context = getContextFromLabel(targetLabel);
        if (context == null) {
            return false;
        }
        
        // Buscar fórmulas que puedan propagarse a targetFormula por monotonicidad
        IProofTreeVeryBasicIterator it = this.getTopDownIterator();
        while (it.hasNext()) {
            INode node = it.next();
            if (!(node instanceof SignedFormulaNode)) {
                continue;
            }
            
            SignedFormulaNode sfNode = (SignedFormulaNode) node;
            SignedFormula sf = (SignedFormula) sfNode.getContent();
            
            if (!(sf instanceof LabelledFormula)) {
                continue;
            }
            
            LabelledFormula lf = (LabelledFormula) sf;
            FormulaLabel label = lf.getLabel();
            
            if (label == null || !isLabelAccessible(label)) {
                continue;
            }
            
            // Verificar si las fórmulas coinciden (sin etiqueta)
            if (!lf.getFormula().equals(targetFormula)) {
                continue;
            }
            
            // Verificar si los signos coinciden
            if (lf.getSign() != targetLf.getSign()) {
                continue;
            }
            
            // Aplicar reglas de monotonicidad según Definition 5.3
            if (targetLf.getSign().equals(IPLSigns.TRUE)) {
                // Regla 2: T A: cj ∈ b* si T A: ci ∈ b y ci ⪯ cj
                if (context.isLowerOrEqualTo(label, targetLabel)) {
                    return true;
                }
            } else if (targetLf.getSign().equals(IPLSigns.FALSE)) {
                // Regla 3: F A: ci ∈ b* si F A: cj ∈ b y ci ⪯ cj
                if (context.isLowerOrEqualTo(targetLabel, label)) {
                    return true;
                }
            }
        }
        
        return false;
    }
    
}
