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
        new Example("Paper 1: ((A->B)^(A->~B))->~A",
                    "F ->(*(->(A B) ->(A -B)) -A) c0", "Valid"),
        new Example("Paper 2: ~~(~~A->A)",
                    "F -(-(->(-(-A) A))) c0", "Valid"),
        new Example("Paper 3: ~(A->B)->(~~A^~B)",
                    "F ->(-(->(A B)) *(-(-A) -B)) c0", "Valid"),
        new Example("Paper 4: (((p->q)->p)->p->q)->q",
                    "F ->(->(->(->(->(p q) p) p) q) q) c0", "Valid"),
        new Example("F-Not Propagation: (P->Q)^~~P->~~Q",
                    "F ->(*(->(P Q) -(-(P))) -(-(Q))) c0", "Valid"),
        new Example("Long PB: symmetric equiv p1,p2,p3",
                    "F ->(*(*(->(*(->(p1 p2) ->(p2 p1)) *(p1 *(p2 p3))) "
                  + "->(*(->(p2 p3) ->(p3 p2)) *(p1 *(p2 p3)))) "
                  + "->(*(->(p3 p1) ->(p1 p3)) *(p1 *(p2 p3)))) "
                  + "*(p1 *(p2 p3))) c0",
                    "Valid"),
        new Example("LEM: P v ~P (NOT valid in IPL)",
                    "F +(P -P) c0", "Not valid"),
        new Example("DN Elim: ~~A->A (NOT valid in IPL)",
                    "F ->(-(-A) A) c0", "Not valid"),
        new Example("Peirce: ((p->q)->p)->p (NOT valid)",
                    "F ->(->(->(p q) p) p) c0", "Not valid"),
        new Example("Peirce variant: ((q->p)->p)->p (NOT valid)",
                    "F ->(->(->(q p) p) p) c0", "Not valid"),
        new Example("Scott axiom: ((~~p->p)->(pv~p))->(~pv~~p) (NOT valid)",
                    "F ->(->(->(-(-p) p) +(p -p)) +(-p -(-p))) c0", "Not valid")
    ));

    private IPLExamplesProvider() {}

    public static List<Example> getExamples() {
        return EXAMPLES;
    }
}
