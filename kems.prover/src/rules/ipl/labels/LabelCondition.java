package rules.ipl.labels;

import logic.signedFormulas.SignedFormulaList;

/**
 * The label constraint attached to a rule's premises (the {@code ci \u2AAF cj} side
 * conditions of Table 2). It only decides whether a given pair of premises satisfies
 * the constraint; it never derives a label. Deriving one is the job of
 * {@link LabelGetter}, and keeping it out of here is what guarantees that no rule can
 * mint a constant below an existing one -- the invariant that makes the constant
 * ordering a tree, and hence makes the minimal upper bound of two labels unique
 * whenever it exists (see {@link MinimalGreaterLabelGetter}).
 */
public interface LabelCondition {

    public boolean matches(SignedFormulaList lfl);
}
