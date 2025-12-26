package logicalSystems.ipl;

import java.util.HashSet;
import java.util.Set;
import java.util.Map;
import java.util.HashMap;
import java.util.concurrent.atomic.AtomicInteger;

import logic.formulas.Formula;
import logic.signedFormulas.SignedFormula;
import logic.labelledFormulas.LabelledFormula;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.Context;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import main.proofTree.iterator.IProofTreeVeryBasicIterator;
import main.strategy.memorySaver.OptimizedClassicalProofTree;

/**
 * ProofTree específico para IPL que implementa:
 * 1. Reglas de cierre correctas: T A: ci, F A: cj, ci ⪯ cj → ×
 * 2. Monotonicidad explícita: cuando se añade T A : ci, propagar a todos cj donde ci ≤ cj
 * 3. Registro global de instancias (rinstances) para evitar bucles
 * 4. Aislamiento de etiquetas por rama: cada rama tiene su propio espacio de etiquetas
 * 
 * Basado en el paper: "Free-variable KE tableaux for IPL"
 */
public class IPLProofTree extends OptimizedClassicalProofTree {
    
    /**
     * Registro global de instancias de reglas operacionales aplicadas (rinstances).
     * Compartido por todas las ramas del árbol para evitar bucles.
     * 
     * Formato: "regla:premisa1:premisa2:..." (representación String de la instancia)
     */
    private Set<String> rinstances;
    
    /**
     * Referencia al rinstances del árbol raíz (para compartir entre ramas)
     */
    private Set<String> sharedRinstances;
    
    /**
     * Registro de instancias de PB aplicadas POR RAMA.
     * Cada rama puede aplicar PB independientemente, pero no debe aplicar PB
     * múltiples veces a la misma fórmula en la misma rama.
     * 
     * Mapa: branchId -> Set de instancias de PB aplicadas en esa rama
     */
    private Map<String, Set<String>> pbRinstancesByBranch;
    
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
     * Contador estático para generar branch IDs únicos
     */
    private static AtomicInteger branchIdCounter = new AtomicInteger(0);

    public IPLProofTree(SignedFormulaNode aNode) {
        super(aNode);
        // Inicializar rinstances vacío solo en la raíz
        this.rinstances = new HashSet<String>();
        this.sharedRinstances = this.rinstances; // La raíz apunta a sí misma
        this.branchId = "root"; // El tronco principal
        this.sharedLabelBranchMap = new HashMap<>();
        // Inicializar el mapa de PB rinstances por rama
        this.pbRinstancesByBranch = new HashMap<>();
    }
    
    /**
     * Constructor para ramas que comparten el rinstances y labelBranchMap de la raíz
     */
    private IPLProofTree(SignedFormulaNode aNode, Set<String> sharedRinstances, 
                         Map<String, String> sharedLabelBranchMap, 
                         Map<String, Set<String>> pbRinstancesByBranch,
                         String branchId) {
        super(aNode);
        this.sharedRinstances = sharedRinstances;
        this.rinstances = null; // Las ramas no tienen su propio rinstances
        this.sharedLabelBranchMap = sharedLabelBranchMap;
        this.pbRinstancesByBranch = pbRinstancesByBranch; // Compartir el mapa de PB rinstances
        this.branchId = branchId;
    }

    @Override
    protected IProofTree makeInstance(INode aNode) {
        // Las ramas comparten el rinstances y labelBranchMap del árbol raíz
        // pero reciben un nuevo branch ID único
        String newBranchId = "branch_" + branchIdCounter.incrementAndGet();
        return new IPLProofTree((SignedFormulaNode) aNode, getSharedRinstances(), 
                                sharedLabelBranchMap, pbRinstancesByBranch, newBranchId);
    }
    
    /**
     * Obtiene el registro compartido de instancias
     */
    public Set<String> getSharedRinstances() {
        return sharedRinstances;
    }
    
    /**
     * Verifica si una instancia de regla ya fue aplicada
     */
    public boolean wasRuleInstanceApplied(String ruleInstance) {
        return sharedRinstances.contains(ruleInstance);
    }
    
    /**
     * Registra una nueva instancia de regla aplicada (para reglas operacionales, global)
     */
    public void registerRuleInstance(String ruleInstance) {
        sharedRinstances.add(ruleInstance);
        System.out.println("📝 Registrado en rinstances: " + ruleInstance);
    }
    
    /**
     * Verifica si una instancia de PB ya fue aplicada en el grupo de accesibilidad de esta rama.
     * 
     * El grupo de accesibilidad de una rama incluye esa rama y todos sus ancestros.
     * Dos ramas están en el mismo grupo si una es ancestro de la otra.
     * 
     * IMPORTANTE: Verifica en la rama actual Y en todas las ancestras.
     * Esto previene loops infinitos cuando múltiples ramas intentan aplicar PB sobre
     * la misma fórmula ancestral repetidamente.
     * 
     * Sin embargo, permite que ramas hermanas (que no comparten ancestros comunes más allá del root)
     * apliquen PB sobre la misma fórmula del root una vez cada una.
     */
    public boolean wasPBRuleInstanceApplied(String pbInstance) {
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
     * IMPORTANTE: Se registra en la rama donde se aplicó PB (targetBranchId).
     * El grupo de accesibilidad de esa rama incluye esa rama y todos sus ancestros,
     * por lo que todas las ramas descendientes (que están en el mismo grupo) verán este registro.
     * 
     * @param pbInstance la instancia de PB a registrar
     * @param targetBranchId la rama donde registrar (donde se aplicó PB)
     */
    public void registerPBRuleInstance(String pbInstance, String targetBranchId) {
        Set<String> branchPbRinstances = pbRinstancesByBranch.computeIfAbsent(targetBranchId, k -> new HashSet<>());
        branchPbRinstances.add(pbInstance);
        System.out.println("📝 Registrado PB en rinstances (grupo de accesibilidad, rama " + targetBranchId + "): " + pbInstance);
    }
    
    /**
     * Registra una nueva instancia de PB aplicada en esta rama.
     * Versión conveniente que registra en la rama actual.
     */
    public void registerPBRuleInstance(String pbInstance) {
        registerPBRuleInstance(pbInstance, branchId);
    }
    
    /**
     * Obtiene el branch ID de esta rama
     */
    public String getBranchId() {
        return branchId;
    }
    
    /**
     * Registra una etiqueta con el branch ID actual.
     */
    public void registerLabel(FormulaLabel label) {
        if (label != null) {
            String labelKey = label.toString();
            if (!sharedLabelBranchMap.containsKey(labelKey)) {
                sharedLabelBranchMap.put(labelKey, branchId);
                System.out.println("🏷️  Etiqueta " + labelKey + " registrada en rama " + branchId);
            }
        }
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
     * Override addLast para implementar:
     * 1. Registro de etiquetas en el branch actual
     * 2. Monotonicidad explícita: cuando se añade T A : ci, propagar T A : cj 
     *    para todos cj donde ci ≤ cj (solo etiquetas accesibles en esta rama)
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
        
        // Implementar monotonicidad explícita solo para fórmulas T-signadas
        if (sf.getSign().equals(IPLSigns.TRUE) && sf instanceof LabelledFormula) {
            LabelledFormula lf = (LabelledFormula) sf;
            FormulaLabel ciLabel = lf.getLabel();
            
            // Obtener el Context
            Context context = getContextFromLabel(ciLabel);
            if (context != null) {
                System.out.println("🔄 Monotonicidad: Procesando T " + lf.getFormula() + " : " + ciLabel);
                
                // Para cada etiqueta cj en el contexto
                for (FormulaLabel cjLabel : context.getLabels()) {
                    // FILTRO: Solo considerar etiquetas accesibles en esta rama
                    if (!isLabelAccessible(cjLabel)) {
                        System.out.println("  ⏭️ Etiqueta " + cjLabel + " no accesible en rama " + branchId + ", saltando");
                        continue;
                    }
                    
                    // Si ci ≤ cj (y no son iguales)
                    if (!ciLabel.equals(cjLabel) && context.isLowerOrEqualTo(ciLabel, cjLabel)) {
                        // Crear T A : cj
                        SignedFormula baseSf = lf.getSignedFormula();
                        LabelledFormula propagated = new LabelledFormula(cjLabel, baseSf);
                        
                        // Verificar que no exista ya
                        if (getNode(propagated) == null) {
                            System.out.println("  ➡️ Propagando a " + cjLabel + ": T " + lf.getFormula() + " : " + cjLabel);
                            
                            // Añadir la fórmula propagada (sin llamar recursivamente a addLast para evitar loops)
                            SignedFormulaNode newNode = new SignedFormulaNode(
                                propagated, 
                                SignedFormulaNodeState.NOT_ANALYSED,
                                sfNode.getOrigin() // Usar el mismo origen
                            );
                            super.addLast(newNode);
                        }
                    }
                }
            }
        }
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
     * Detecta contradicciones según las reglas de cierre IPL:
     * 1) T A: ci, F A: cj, ci ⪯ cj → ×
     */
    private boolean detectIPLContradiction(SignedFormulaNode aNode) {
        SignedFormula newSf = (SignedFormula) aNode.getContent();
        FormulaLabel newLabel = newSf.getLabel();
        Formula newFormula = newSf.getFormula();
        Object newSign = newSf.getSign();
        
        System.out.println("🔍 IPL Closure: Checking " + newSign + " " + newFormula + " " + newLabel);
        
        // Obtener el Context para verificar relaciones de orden
        Context context = getContextFromLabel(newLabel);
        if (context == null) {
            System.out.println("⚠️ IPL Closure: No Context found for label " + newLabel);
            return false; // Sin Context, no podemos verificar relaciones de orden
        }
        
        System.out.println("🔍 IPL Closure: Context has " + context.getLabels().size() + " labels: " + context.getLabels());
        
        // Regla 1: T A: ci, F A: cj, ci ⪯ cj → ×
        if (newSign.equals(IPLSigns.TRUE)) {
            SignedFormula oppositeSigned = findFormulaWithSign(newFormula, IPLSigns.FALSE);
            if (oppositeSigned != null) {
                FormulaLabel oppositeLabel = oppositeSigned.getLabel();
                System.out.println("🔍 IPL Closure: Encontrado F " + newFormula + " " + oppositeLabel + 
                                 ", verificando si " + newLabel + " ⪯ " + oppositeLabel);
                
                // ✅ CRÍTICO: Verificar que ambas etiquetas son accesibles en la rama actual
                // Las etiquetas creadas en ramas hermanas no deberían causar cierre
                boolean newLabelAccessible = isLabelAccessible(newLabel);
                boolean oppositeLabelAccessible = isLabelAccessible(oppositeLabel);
                
                if (!newLabelAccessible || !oppositeLabelAccessible) {
                    if (!newLabelAccessible) {
                        System.out.println("⚠️ IPL Closure: Etiqueta " + newLabel + " NO es accesible en rama " + this.branchId + ", ignorando");
                    }
                    if (!oppositeLabelAccessible) {
                        System.out.println("⚠️ IPL Closure: Etiqueta " + oppositeLabel + " NO es accesible en rama " + this.branchId + ", ignorando");
                    }
                    return false;
                }
                
                // Verificar si ci ⪯ cj (newLabel ⪯ oppositeLabel)
                boolean isLowerOrEqualResult = isLowerOrEqual(context, newLabel, oppositeLabel);
                System.out.println("🔍 IPL Closure: Verificando " + newLabel + " ⪯ " + oppositeLabel + 
                                 " - resultado: " + isLowerOrEqualResult);
                if (isLowerOrEqualResult) {
                    System.out.println("🔴 IPL Closure Rule 1: T " + newFormula + " " + newLabel + 
                                     ", F " + newFormula + " " + oppositeLabel + 
                                     " with " + newLabel + " ⪯ " + oppositeLabel);
                    return true;
                } else {
                    System.out.println("❌ IPL Closure: " + newLabel + " NO es ⪯ " + oppositeLabel);
                }
            } else {
                System.out.println("🔍 IPL Closure: No se encontró F " + newFormula + " en la rama");
            }
        }
        
        if (newSign.equals(IPLSigns.FALSE)) {
            SignedFormula oppositeSigned = findFormulaWithSign(newFormula, IPLSigns.TRUE);
            if (oppositeSigned != null) {
                FormulaLabel oppositeLabel = oppositeSigned.getLabel();
                System.out.println("🔍 IPL Closure: Encontrado T " + newFormula + " " + oppositeLabel + 
                                 ", verificando si " + oppositeLabel + " ⪯ " + newLabel);
                System.out.println("🔍 DEBUG: Buscando T " + newFormula + " desde rama " + this.branchId);
                
                // ✅ CRÍTICO: Verificar que ambas etiquetas son accesibles en la rama actual
                // Las etiquetas creadas en ramas hermanas no deberían causar cierre
                boolean oppositeLabelAccessible = isLabelAccessible(oppositeLabel);
                boolean newLabelAccessible = isLabelAccessible(newLabel);
                
                if (!oppositeLabelAccessible) {
                    System.out.println("⚠️ IPL Closure: Etiqueta " + oppositeLabel + " NO es accesible en rama " + this.branchId + ", ignorando");
                    return false;
                }
                if (!newLabelAccessible) {
                    System.out.println("⚠️ IPL Closure: Etiqueta " + newLabel + " NO es accesible en rama " + this.branchId + ", ignorando");
                    return false;
                }
                
                // Verificar si ci ⪯ cj (oppositeLabel ⪯ newLabel)
                boolean isLowerOrEqualResult = isLowerOrEqual(context, oppositeLabel, newLabel);
                System.out.println("🔍 IPL Closure: Verificando " + oppositeLabel + " ⪯ " + newLabel + 
                                 " - resultado: " + isLowerOrEqualResult);
                if (isLowerOrEqualResult) {
                    System.out.println("🔴 IPL Closure Rule 1: T " + newFormula + " " + oppositeLabel + 
                                     ", F " + newFormula + " " + newLabel + 
                                     " with " + oppositeLabel + " ⪯ " + newLabel);
                    return true;
                } else {
                    System.out.println("❌ IPL Closure: " + oppositeLabel + " NO es ⪯ " + newLabel);
                }
            } else {
                System.out.println("🔍 IPL Closure: No se encontró T " + newFormula + " en la rama");
                System.out.println("🔍 DEBUG: Buscando T " + newFormula + " desde rama " + this.branchId + 
                                 " usando getTopDownIterator()");
                // Debug: mostrar qué ramas estamos revisando
                IProofTreeVeryBasicIterator debugIt = this.getTopDownIterator();
                int count = 0;
                while (debugIt.hasNext() && count < 10) {
                    INode node = debugIt.next();
                    if (node instanceof SignedFormulaNode) {
                        SignedFormula sf = (SignedFormula) node.getContent();
                        System.out.println("  🔍 DEBUG: Revisando fórmula: " + sf + 
                                         " (signo: " + sf.getSign() + ", fórmula: " + sf.getFormula() + ")");
                        count++;
                    }
                }
            }
        }
        
        
        return false;
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
     */
    private SignedFormula findFormulaWithSign(Formula formula, Object sign) {
        // Buscar en la rama actual y todas sus ancestras (usando getTopDownIterator)
        // que recorre desde la rama actual hasta la raíz
        System.out.println("🔍 DEBUG findFormulaWithSign: Buscando " + sign + " " + formula + " desde rama " + branchId);
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
                
                if (count < 5) {
                    System.out.println("  🔍 DEBUG: Revisando " + sf + " (signMatches=" + signMatches + ", formulaMatches=" + formulaMatches + ")");
                }
                count++;
                
                if (signMatches && formulaMatches) {
                    System.out.println("  ✅ DEBUG: Encontrado " + sf + " después de revisar " + count + " nodos");
                    return sf;
                }
            }
        }
        System.out.println("  ❌ DEBUG: No encontrado después de revisar " + count + " nodos");
        return null;
    }
    
}
