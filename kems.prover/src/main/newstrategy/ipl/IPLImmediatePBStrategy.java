package main.newstrategy.ipl;

import main.tableau.Method;

/**
 * The IPL canonical strategy running PB under
 * {@link IPLCanonicalStrategyImplementation.PBPolicy#IMMEDIATE} instead of the default
 * DEFERRED: PB is applied to the first selected formula for which no rule fires, rather
 * than only once the whole selection is exhausted.
 *
 * <p>Exists as a separate class because the desktop prover picks strategies by class name
 * (see {@code ProverConfigurator.IPL_STRATEGY_NAMES}), so registering it there is what
 * puts the choice in front of the user. Everything else is inherited unchanged.
 *
 * <p>Both policies are sound and terminating -- footnote 8 of the paper makes the
 * placement of PB a free choice and Theorem 5.9 does not depend on it -- so this only
 * trades proof size. Neither dominates: see {@link IPLCanonicalStrategyImplementation.PBPolicy}
 * for the measurements over the 274 ILTP propositional problems.
 */
public class IPLImmediatePBStrategy extends IPLSimpleStrategy {

    public IPLImmediatePBStrategy(Method method) {
        super(method);
        setPbPolicy(IPLCanonicalStrategyImplementation.PBPolicy.IMMEDIATE);
    }
}
