package logicalSystems.ipl;

import java.util.HashSet;
import java.util.Set;
import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicInteger;

import logic.formulas.Formula;
// import logic.formulas.CompositeFormula;  // needed if T-NOT b* extension is re-enabled
import logic.signedFormulas.SignedFormula;
import logic.signedFormulas.FormulaSign;
// import logic.signedFormulas.SignedFormulaFactory;  // needed if T-NOT b* extension is re-enabled
import logic.labelledFormulas.LabelledFormula;
import logic.labelledFormulas.FormulaLabel;
import logic.labelledFormulas.ContextFormulaLabel;
import logic.labelledFormulas.Context;
import main.proofTree.INode;
import main.proofTree.IProofTree;
import main.proofTree.SignedFormulaNode;
import main.proofTree.SignedFormulaNodeState;
import main.proofTree.iterator.IProofTreeBasicIterator;
import main.proofTree.iterator.IProofTreeVeryBasicIterator;
import main.proofTree.origin.IOrigin;
import main.strategy.memorySaver.OptimizedClassicalProofTree;
import main.newstrategy.ipl.IPLTracer;

/**
 * ProofTree específico para IPL que implementa:
 * 1. Reglas de cierre correctas: T A: ci, F A: cj, ci ⪯ cj → ×
 * 2. Monotonicidad implícita via extendBranch() / b* extension
 * 3. Registro de instancias de reglas (rinstances) para evitar bucles
 * 4. Aislamiento de etiquetas por rama: cada rama tiene su propio espacio de etiquetas
 *
 * Basado en el paper: "Free-variable KE tableaux for IPL", Algorithm 1.
 *
 * DISEÑO DE rinstances (reglas operacionales):
 *   Conjunto POR RAMA (per-branch) con búsqueda en ancestros. Cada rama tiene su
 *   propio conjunto local; wasRuleInstanceApplied recorre la cadena de ancestros.
 *   Esto garantiza que, dentro de un mismo camino de prueba (rama → ancestros),
 *   una instancia no se aplica dos veces (prevención de bucles), pero ramas en
 *   subtrees diferentes pueden aplicar la misma instancia independientemente
 *   (completitud).  Corresponde al significado correcto de "rinstances" del
 *   Algorithm 1 del paper: global al camino actual, no a todo el árbol.
 */
public class IPLProofTree extends OptimizedClassicalProofTree {

    private static final IPLTracer tracer = IPLTracer.getInstance();

    /**
     * Conjunto local de instancias de reglas operacionales registradas en ESTA rama.
     * Cada rama tiene su propia copia. wasRuleInstanceApplied() recorre la cadena de
     * ancestros para determinar si la instancia fue aplicada en el camino actual.
     * Formato: "regla:premisa1:premisa2:..." (toString de las ls-fórmulas con labels).
     */
    private Set<String> localRinstances;

    /**
     * Branch ID: identificador único de esta rama.
     * El tronco principal tiene ID "root".
     * Las ramas creadas por bifurcación (PB) reciben IDs únicos.
     * Se usa para el tracking de etiquetas (isLabelAccessible), pbRinstances y GUI.
     */
    private String branchId;
    
    /**
     * Mapa compartido que asocia cada etiqueta (por su toString()) con su branchId.
     * Permite determinar qué etiquetas son accesibles en cada rama.
     */
    private Map<String, String> sharedLabelBranchMap;

    /**
     * Contador estático para generar branch IDs únicos.
     */
    private static AtomicInteger branchIdCounter = new AtomicInteger(0);

    /**
     * Snapshot of the path-level rinstance count at the time each
     * {@link SignedFormulaNode} was added to this branch. Used by the GUI
     * / HTML viewer to show the rinstances panel filtered to the temporal
     * state of the selected node (i.e. only rinstances registered up to
     * and including the rule application that created that node).
     */
    private final Map<SignedFormulaNode, Integer> rinstancesAtNodeCreation = new java.util.IdentityHashMap<>();

    public IPLProofTree(SignedFormulaNode aNode) {
        super(aNode);
        this.branchId = "root";
        this.sharedLabelBranchMap = new HashMap<>();
        // LinkedHashSet preserves insertion order; useful for GUI / HTML inspection
        // where rinstances are displayed in the order they were registered.
        this.localRinstances = new java.util.LinkedHashSet<>();
        recordRinstancesSnapshot(aNode);
    }
    
    /**
     * Constructor para ramas hijas: comparten sharedLabelBranchMap pero cada una
     * tiene su propio conjunto localRinstances vacío (búsqueda vía ancestros).
     */
    private IPLProofTree(SignedFormulaNode aNode,
                         Map<String, String> sharedLabelBranchMap,
                         String branchId) {
        super(aNode);
        this.sharedLabelBranchMap = (sharedLabelBranchMap != null) ? sharedLabelBranchMap : new HashMap<>();
        this.localRinstances = new java.util.LinkedHashSet<>();
        this.branchId = branchId;
        recordRinstancesSnapshot(aNode);
    }

    private void recordRinstancesSnapshot(SignedFormulaNode node) {
        // We snapshot the path-level count (ancestors + local) because the GUI
        // displays the full chain in rinstances; the count tells the viewer
        // how many of those entries already existed at the time the node was
        // added.
        rinstancesAtNodeCreation.put(node, currentPathRinstancesSize());
    }

    private int currentPathRinstancesSize() {
        int n = 0;
        IPLProofTree current = this;
        while (current != null) {
            n += current.localRinstances.size();
            IProofTree parent = current.getParent();
            current = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        }
        return n;
    }

    /**
     * Returns the path-level rinstance count captured at the moment {@code node}
     * was added to this branch, or {@code -1} if the node has no recorded
     * snapshot (e.g. legacy proof trees serialised before this field existed).
     */
    public int getRinstancesAtCreation(SignedFormulaNode node) {
        Integer v = rinstancesAtNodeCreation.get(node);
        return v != null ? v : -1;
    }

    @Override
    protected IProofTree makeInstance(INode aNode) {
        String newBranchId = "branch_" + branchIdCounter.incrementAndGet();
        return new IPLProofTree((SignedFormulaNode) aNode,
                                sharedLabelBranchMap, newBranchId);
    }

    /**
     * Hook invoked by {@link main.proofTree.ProofTree#addLeft(INode)} /
     * {@link main.proofTree.ProofTree#addRight(INode)} after the new child
     * branch has been linked to its parent.
     *
     * The child's constructor runs <em>before</em> {@code setReferences} sets
     * the parent pointer, so {@link #recordRinstancesSnapshot(SignedFormulaNode)}
     * called from the constructor sees an empty ancestor chain and records
     * a snapshot of 0. Here we re-record the snapshot now that the parent
     * linkage is in place, giving the correct path-level rinstance count for
     * the child's root node.
     */
    @Override
    protected void setOtherStructures(IProofTree pt, INode aNode) {
        super.setOtherStructures(pt, aNode);
        if (pt instanceof IPLProofTree && aNode instanceof SignedFormulaNode) {
            ((IPLProofTree) pt).recordRinstancesSnapshot((SignedFormulaNode) aNode);
        }
    }

    /**
     * Verifica si una instancia de regla operacional ya fue aplicada en el camino
     * de prueba actual (esta rama o cualquier ancestro).
     * Implementa "r ∉ rinstances" del Algorithm 1 (líneas 7 y 10).
     *
     * @param ruleInstance la instancia de regla (formato: "regla:premisa1:premisa2")
     */
    public boolean wasRuleInstanceApplied(String ruleInstance) {
        // Buscar en esta rama y en todos los ancestros
        IPLProofTree current = this;
        while (current != null) {
            if (current.localRinstances.contains(ruleInstance)) {
                return true;
            }
            IProofTree parent = current.getParent();
            current = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        }
        return false;
    }

    /**
     * Registra una instancia de regla operacional en el conjunto LOCAL de esta rama.
     * Implementa "rinstances ← rinstances ∪ {r}" del Algorithm 1 (líneas 9, 13, 18).
     *
     * @param ruleInstance la instancia de regla (formato: "regla:premisa1:premisa2")
     */
    public void registerRuleInstance(String ruleInstance) {
        localRinstances.add(ruleInstance);
        if (IPLTracer.isEnabled()) {
            tracer.logRinstanceRegistered(ruleInstance);
        }
    }

    /**
     * No-op: IPL no usa la lista _PBCandidates heredada de ClassicalProofTree.
     * IPLPBRuleApplicator construye su propia lista de candidatos PB frescos con
     * findAllCompositeFormulas() cada vez que los necesita, iterando directamente
     * sobre los nodos del árbol. Mantener sincronizada la lista heredada sería
     * trabajo innecesario, y el intento de remover fórmulas universales ya removidas
     * (re-procesadas por Def. 5.6) generaría mensajes DEBUG espurios.
     */
    @Override
    public void removeFromPBCandidates(SignedFormula sf) { }

    /**
     * Obtiene el branch ID de esta rama (para label tracking y GUI).
     */
    public String getBranchId() {
        return branchId;
    }

    /**
     * Returns an unmodifiable view of rule instances registered in this branch only.
     * Preserves insertion order (LinkedHashSet). For the full path use
     * {@link #getAllRinstances()}.
     */
    public Set<String> getLocalRinstances() {
        return java.util.Collections.unmodifiableSet(localRinstances);
    }

    /**
     * Returns all rule instances along the current path (root → … → this branch)
     * in insertion order. Ancestor instances come before the local ones, which
     * matches the temporal order in which they were registered while traversing
     * the proof tree. Used by the GUI / HTML export for the "rinstances" panel.
     */
    public java.util.LinkedHashSet<String> getRinstances() {
        // Collect ancestors top-down first
        java.util.Deque<IPLProofTree> chain = new java.util.ArrayDeque<>();
        IPLProofTree current = this;
        while (current != null) {
            chain.addFirst(current);
            IProofTree parent = current.getParent();
            current = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        }
        java.util.LinkedHashSet<String> all = new java.util.LinkedHashSet<>();
        for (IPLProofTree t : chain) {
            all.addAll(t.localRinstances);
        }
        return all;
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
                if (IPLTracer.isEnabled()) {
                    tracer.logLabelRegistered(labelKey, branchId);
                }
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

        // Snapshot del estado de rinstances al momento de agregar el nodo
        // (lo usa el visor para filtrar la vista de rinstances por nodo).
        recordRinstancesSnapshot(sfNode);

        // La extensión b* se calcula dinámicamente cuando se necesita;
        // no propagamos monotonicidad físicamente en el árbol.
    }

    @Override
    protected void updateMultimap(SignedFormulaNode aNode) {
        // Para IPL, NO ejecutar la detección clásica, solo usar reglas IPL específicas
        SignedFormula sf = (SignedFormula) aNode.getContent();
        getFsmm().put(sf.getFormula(), sf.getSign());
        
        // Verificar reglas de cierre IPL
        if (detectIPLContradiction(aNode)) {
            if (IPLTracer.isEnabled()) {
                tracer.logInfo("CONTRADICTION DETECTED for " + sf);
            }
            setClosingReason(sf);
            setLocallyClosed(true);
        }
    }
    
    /**
     * Detecta contradicciones según la regla de cierre IPL (Lemma 5.5):
     *   T A:ci, F A:cj, ci ⪯ cj → ×
     *
     * La nueva fórmula ya está en b (insertada por super.addLast antes de updateMultimap).
     * Se busca la fórmula de signo opuesto directamente en b físico (rama + ancestros),
     * aplicando la relación ⪯ sobre las etiquetas constantes.
     *
     * Esto es equivalente a chequear b* porque toda contradicción en b* se corresponde
     * con una contradicción en b via la transitividad de ⪯ (ver IMPLEMENTACION_IPL.md §5).
     * Iterar b directamente es O(n) en lugar de O(n²) de calcular b* completo.
     */
    private boolean detectIPLContradiction(SignedFormulaNode aNode) {
        SignedFormula newSf = (SignedFormula) aNode.getContent();
        if (!(newSf instanceof LabelledFormula)) return false;

        LabelledFormula newLf = (LabelledFormula) newSf;
        FormulaLabel newLabel = newLf.getLabel();
        Formula newFormula = newLf.getFormula();
        FormulaSign newSign = newSf.getSign();

        if (newLabel == null || !isLabelAccessible(newLabel)) return false;

        Context context = getContextFromLabel(newLabel);
        if (context == null) return false;

        // T A:ci (nueva) → buscar F A:cj en b con ci ⪯ cj
        // F A:cj (nueva) → buscar T A:ci en b con ci ⪯ cj
        FormulaSign oppositeSign = newSign.equals(IPLSigns.TRUE) ? IPLSigns.FALSE : IPLSigns.TRUE;

        IPLProofTree current = this;
        while (current != null) {
            IProofTreeVeryBasicIterator it = current.getTopDownIterator();
            while (it.hasNext()) {
                INode node = it.next();
                if (!(node instanceof SignedFormulaNode)) continue;
                SignedFormula sf = (SignedFormula) ((SignedFormulaNode) node).getContent();
                if (!sf.getSign().equals(oppositeSign)) continue;
                if (!sf.getFormula().equals(newFormula)) continue;
                if (!(sf instanceof LabelledFormula)) continue;

                FormulaLabel label = ((LabelledFormula) sf).getLabel();
                if (label == null || !isLabelAccessible(label)) continue;

                // ci = etiqueta de la fórmula T, cj = etiqueta de la fórmula F
                FormulaLabel ciLabel = newSign.equals(IPLSigns.TRUE) ? newLabel : label;
                FormulaLabel cjLabel = newSign.equals(IPLSigns.TRUE) ? label : newLabel;

                if (isLowerOrEqual(context, ciLabel, cjLabel)) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logClosure(newFormula + " " + ciLabel,
                                newFormula + " " + cjLabel,
                                ciLabel + " ⪯ " + cjLabel);
                    }
                    return true;
                }
            }
            IProofTree parent = current.getParent();
            current = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        }
        return false;
    }
    
    /**
     * Chequea contradicciones de la forma T A:ci, F A:cj, ci ⪯ cj iterando directamente
     * sobre b físico (rama + ancestros) — Lemma 5.5.
     *
     * Llamado al final de cada iteración del loop para capturar contradicciones que no
     * fueron detectadas incrementalmente (e.g., cuando ambas fórmulas están solo en ancestros).
     *
     * Aunque Lemma 5.5 está enunciado sobre b*, es suficiente iterar b físico:
     * la monotonía de Def. 5.3 garantiza que toda contradicción en b* tiene testigos
     * T A:ci y F A:cj con ci ⪯ cj en b (por transitividad de ⪯).
     *
     * @return true si se encontró una contradicción y la rama fue marcada cerrada
     */
    public boolean checkPhysicalBForContradiction() {
        if (isLocallyClosed()) return true;

        List<SignedFormula> physicalB = collectPhysicalFormulas();

        for (SignedFormula sf1 : physicalB) {
            if (!sf1.getSign().equals(IPLSigns.TRUE)) continue;
            if (!(sf1 instanceof LabelledFormula)) continue;

            LabelledFormula lf1 = (LabelledFormula) sf1;
            FormulaLabel label1 = lf1.getLabel();
            if (!isLabelAccessible(label1)) continue;

            Context context = getContextFromLabel(label1);
            if (context == null) continue;

            for (SignedFormula sf2 : physicalB) {
                if (!sf2.getSign().equals(IPLSigns.FALSE)) continue;
                if (!(sf2 instanceof LabelledFormula)) continue;
                if (!sf2.getFormula().equals(sf1.getFormula())) continue;

                FormulaLabel label2 = ((LabelledFormula) sf2).getLabel();
                if (!isLabelAccessible(label2)) continue;

                if (isLowerOrEqual(context, label1, label2)) {
                    if (IPLTracer.isEnabled()) {
                        tracer.logInfo("Contradiction: T " + sf1.getFormula()
                                + " " + label1 + " vs F " + sf2.getFormula() + " " + label2);
                    }
                    setLocallyClosed(true);
                    return true;
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
    
    // ✅ ELIMINADO: propagateRetroactiveMonotonicity()
    // Ya no se necesita porque la monotonicidad se maneja implícitamente vía extendBranch()
    
    /**
     * Recolecta todas las fórmulas físicas de b (rama actual + ancestros), sin duplicados.
     * Usado por detectIPLContradiction y checkPhysicalBForContradiction para iterar b directamente.
     */
    private List<SignedFormula> collectPhysicalFormulas() {
        List<SignedFormula> result = new ArrayList<>();
        Set<SignedFormula> seen = new HashSet<>();
        IPLProofTree current = this;
        while (current != null) {
            IProofTreeVeryBasicIterator it = current.getTopDownIterator();
            while (it.hasNext()) {
                INode node = it.next();
                if (node instanceof SignedFormulaNode) {
                    SignedFormula sf = (SignedFormula) ((SignedFormulaNode) node).getContent();
                    if (seen.add(sf)) result.add(sf);
                }
            }
            IProofTree parent = current.getParent();
            current = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        }
        return result;
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
                }
            }
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
     * Calcula la extension b* de la rama actual (Definition 5.3 + extension de implementacion).
     *
     * Definition 5.3 del paper define b* con estas condiciones ("nothing else is in b*"):
     *   1. Todas las formulas en b
     *   2. T A:cj in b*, para cada cj tal que ci <= cj y T A:ci in b  (monotonia T ascendente)
     *   3. F A:ci in b*, para cada ci tal que ci <= cj y F A:cj in b  (monotonia F descendente)
     *   4. (labels variables, Table 1 — no aplica en Table 2)
     *
     * Extension de implementacion (NOT en Definition 5.3, justificada por Definition 5.6):
     *   5. Si T-NOT-A:ci in b, entonces F A:cj in b* para cada cj >= ci.
     *      Permite deteccion de cierre anticipada sin esperar la aplicacion fisica de T-NOT.
     *
     * Este metodo calcula b* dinamicamente SIN agregar formulas fisicamente al arbol.
     *
     * @return Set de SignedFormula que representa b*
     */
    public Set<SignedFormula> extendBranch() {
        return computeBStarFor(collectFormulasInPath(null));
    }

    /**
     * Variante de {@link #extendBranch()} que computa b* "en el tiempo" de un
     * nodo determinado: usa solo las fórmulas físicas que existían en la rama
     * (esta + ancestros) en el momento en que {@code upTo} fue agregado, no
     * todas las que están al cierre del proceso. Pensado para la GUI / HTML
     * exporter: permite mostrar b* tal como se veía cuando el nodo seleccionado
     * fue insertado.
     *
     * @param upTo nodo límite (inclusive). Si es {@code null}, equivale a
     *             {@link #extendBranch()}.
     * @return b* restringido al estado del árbol al tiempo de {@code upTo}.
     */
    public Set<SignedFormula> extendBranchUpTo(SignedFormulaNode upTo) {
        return computeBStarFor(collectFormulasInPath(upTo));
    }

    /**
     * Recolecta b (fórmulas físicas) en orden: esta rama (hasta {@code upTo}
     * inclusive si no es null, o entera si es null), seguida de los ancestros
     * completos. Los ancestros se incluyen siempre completos porque están
     * congelados una vez que apareció la primera bifurcación.
     */
    private List<SignedFormula> collectFormulasInPath(SignedFormulaNode upTo) {
        // LinkedHashSet de-duplica y conserva orden — varios ancestros podrían
        // referenciar (por accidente) la misma instancia, lo que duplicaría la
        // monotonía si lo agregáramos dos veces.
        java.util.LinkedHashSet<SignedFormula> seen = new java.util.LinkedHashSet<>();
        List<SignedFormula> formulasInB = new ArrayList<>();

        // 1) Esta rama: iterar localmente y cortar si encontramos upTo
        IProofTreeBasicIterator localIt = getLocalIterator();
        while (localIt.hasNext()) {
            INode node = localIt.next();
            if (node instanceof SignedFormulaNode) {
                SignedFormula sf = (SignedFormula) ((SignedFormulaNode) node).getContent();
                if (seen.add(sf)) formulasInB.add(sf);
            }
            if (upTo != null && node == upTo) {
                break;
            }
        }

        // 2) Ancestros: completos
        IProofTree parent = getParent();
        IPLProofTree currentTree = (parent instanceof IPLProofTree) ? (IPLProofTree) parent : null;
        while (currentTree != null) {
            IProofTreeBasicIterator it = currentTree.getLocalIterator();
            while (it.hasNext()) {
                INode node = it.next();
                if (node instanceof SignedFormulaNode) {
                    SignedFormula sf = (SignedFormula) ((SignedFormulaNode) node).getContent();
                    if (seen.add(sf)) formulasInB.add(sf);
                }
            }
            IProofTree up = currentTree.getParent();
            currentTree = (up instanceof IPLProofTree) ? (IPLProofTree) up : null;
        }

        return formulasInB;
    }

    /**
     * Aplica las cláusulas de Definition 5.3 (monotonía) sobre una lista
     * {@code b} explícita. Usada por {@link #extendBranch()} y por
     * {@link #extendBranchUpTo(SignedFormulaNode)}.
     */
    private Set<SignedFormula> computeBStarFor(List<SignedFormula> formulasInB) {
        // LinkedHashSet preserva orden de inserción → resultado determinista.
        Set<SignedFormula> bStar = new java.util.LinkedHashSet<>(formulasInB);

        // Obtener todas las etiquetas constantes en la rama (Cb).
        Set<FormulaLabel> constantLabels = new java.util.LinkedHashSet<>();
        for (SignedFormula sf : formulasInB) {
            if (sf instanceof LabelledFormula) {
                LabelledFormula lf = (LabelledFormula) sf;
                FormulaLabel label = lf.getLabel();
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
        
        // Extension de implementacion (Definition 5.6, NOT Definition 5.3):
        // Si T-NOT-A: ci in b, entonces F A: cj in b* para cada cj >= ci.
        // Definition 5.3 dice "nothing else is in b*" y no incluye este caso.
        // Lo agregamos aqui porque Definition 5.6 requiere que T-NOT-A:ci este
        // completamente analizada solo cuando F A:cj in b* para todo cj >= ci.
        // Anticipar esto permite deteccion de cierre mas temprana sin generar
        // F A:cj fisicamente primero. T-NOT genera esas formulas por re-seleccion
        // via el chequeo de Def. 5.6 en selectUnanalyzedFormula.
        //
        // COMENTADO: esta extension va mas alla de Definition 5.3.
        // El sistema sigue siendo correcto sin ella: T-NOT re-genera F A:cj en la
        // siguiente iteracion via Def. 5.6, logrando el mismo cierre un paso despues.
        //
        // SignedFormulaFactory tempFactory = new SignedFormulaFactory();
        // for (SignedFormula sf : formulasInB) {
        //     if (sf.getSign().equals(IPLSigns.TRUE) && sf instanceof LabelledFormula) {
        //         LabelledFormula lf = (LabelledFormula) sf;
        //         Formula formula = lf.getFormula();
        //         if (formula instanceof CompositeFormula) {
        //             CompositeFormula comp = (CompositeFormula) formula;
        //             if (comp.getConnective().equals(IPLConnectives.NOT)) {
        //                 FormulaLabel ci = lf.getLabel();
        //                 if (ci == null || !isLabelAccessible(ci)) {
        //                     continue;
        //                 }
        //                 Formula innerA = comp.getImmediateSubformulas().get(0);
        //                 for (FormulaLabel cj : constantLabels) {
        //                     if (!isLabelAccessible(cj)) {
        //                         continue;
        //                     }
        //                     if (context.isLowerOrEqualTo(ci, cj)) {
        //                         SignedFormula innerSigned = tempFactory.createSignedFormula(IPLSigns.FALSE, innerA);
        //                         LabelledFormula tneg_derived = new LabelledFormula(cj, innerSigned);
        //                         bStar.add(tneg_derived);
        //                     }
        //                 }
        //             }
        //         }
        //     }
        // }
        
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
