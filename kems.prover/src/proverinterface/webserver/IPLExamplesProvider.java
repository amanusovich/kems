package proverinterface.webserver;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * Single source of truth for the IPL formula presets shown in both
 * {@code ProblemEditor} (Swing GUI) and {@link IPLWebServer} (web UI).
 *
 * <p>Each {@link Example} is the same three-tuple used by the legacy GUI
 * menu: a human-readable name, the formula in the internal Polish notation
 * accepted by {@code SignedFormulaCreator}, and a textual validity tag
 * ({@code "Valid"} or {@code "Not valid"}).</p>
 */
public final class IPLExamplesProvider {

    public static final class Example {
        public final String name;
        public final String formula;
        public final String validity;

        public Example(String name, String formula, String validity) {
            this.name = name;
            this.formula = formula;
            this.validity = validity;
        }
    }

    private static final List<Example> EXAMPLES = Collections.unmodifiableList(Arrays.asList(
        new Example("Paper 1: ((A->B)\u2227(A->\u00ACB))->\u00ACA",
                    "F ->(*(->(A B) ->(A -B)) -A) c0", "Valid"),
        new Example("Paper 2: \u00AC\u00AC(\u00AC\u00ACA->A)",
                    "F -(-(->(-(-A) A))) c0", "Valid"),
        new Example("Paper 3: \u00AC(A->B)->(\u00AC\u00ACA\u2227\u00ACB)",
                    "F ->(-(->(A B)) *(-(-A) -B)) c0", "Valid"),
        new Example("Paper 4: (((p->q)->p)->p->q)->q",
                    "F ->(->(->(->(->(p q) p) p) q) q) c0", "Valid"),
        new Example("F-Not Propagation: (P->Q)\u2227\u00AC\u00ACP->\u00AC\u00ACQ",
                    "F ->(*(->(P Q) -(-(P))) -(-(Q))) c0", "Valid"),
        new Example("Long PB: symmetric equiv p1,p2,p3",
                    "F ->(*(*(->(*(->(p1 p2) ->(p2 p1)) *(p1 *(p2 p3))) "
                  + "->(*(->(p2 p3) ->(p3 p2)) *(p1 *(p2 p3)))) "
                  + "->(*(->(p3 p1) ->(p1 p3)) *(p1 *(p2 p3)))) "
                  + "*(p1 *(p2 p3))) c0",
                    "Valid"),
        new Example("LEM: P\u2228\u00ACP (NOT valid in IPL)",
                    "F +(P -P) c0", "Not valid"),
        new Example("DN Elim: \u00AC\u00ACA->A (NOT valid in IPL)",
                    "F ->(-(-A) A) c0", "Not valid"),
        new Example("Peirce: ((p->q)->p)->p (NOT valid)",
                    "F ->(->(->(p q) p) p) c0", "Not valid"),
        new Example("Peirce variant: ((q->p)->p)->p (NOT valid)",
                    "F ->(->(->(q p) p) p) c0", "Not valid"),
        new Example("Scott axiom: ((\u00AC\u00ACp->p)->(p\u2228\u00ACp))->(\u00ACp\u2228\u00AC\u00ACp) (NOT valid)",
                    "F ->(->(->(-(-p) p) +(p -p)) +(-p -(-p))) c0", "Not valid"),
        new Example("ILTP SYJ201+1.001: 3-way sym. equiv \u2192 p1\u2227p2\u2227p3 (Table 1: closed, ~1.2s/2573 nodes)",
                    "T ->(*(->(p1 p2)(->(p2 p1))) *(p1 *(p2 p3))) c0\n"
                  + "T ->(*(->(p2 p3)(->(p3 p2))) *(p1 *(p2 p3))) c0\n"
                  + "T ->(*(->(p3 p1)(->(p1 p3))) *(p1 *(p2 p3))) c0\n"
                  + "F *(p1 *(p2 p3)) c0",
                    "Valid"),
        new Example("ILTP SYJ207+1.001: 2-way sym. equiv \u2192 p1\u2227p2 (Table 1: open, ~3ms/77 nodes)",
                    "T ->(*(->(p1 p2)(->(p2 p1))) *(p1 p2)) c0\n"
                  + "T ->(*(->(p2 p1)(->(p1 p2))) *(p1 p2)) c0\n"
                  + "F +(p0 +(*(p1 p2) -(p0))) c0",
                    "Not valid"),
        new Example("ILTP SYN001+1: \u00AC\u00ACp<->p (Table 1: open, NOT valid in IPL)",
                    "F *(->(-(-(p)) p)(->(p -(-(p))))) c0", "Not valid"),
        new Example("ILTP SYN041+1: \u00AC(p->q)->(q->p) (Table 1: closed, valid)",
                    "F ->(-(->(p q)) ->(q p)) c0", "Valid"),
        new Example("ILTP SYN046+1: (p->q)<->(\u00ACp\u2228q) (Table 1: open, NOT valid in IPL)",
                    "F *(->(->(p q) +(-(p) q))(->(+(-(p) q) ->(p q)))) c0", "Not valid"),
        new Example("ILTP LCL181+1: (\u00ACp->q)<->(\u00ACq->p) (Table 1: open, NOT valid in IPL)",
                    "F *(->(->(-(p) q) ->(-(q) p))(->(->(-(q) p) ->(-(p) q)))) c0", "Not valid")
    ));

    private IPLExamplesProvider() {}

    public static List<Example> getExamples() {
        return EXAMPLES;
    }
}
