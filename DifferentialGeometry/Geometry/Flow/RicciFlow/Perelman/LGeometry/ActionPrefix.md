# Prefix minimality

## Goal

`lReg_prefix_min` is the cut-and-paste principle needed before the minimizing
L-exponential domain can be shown downward closed.  It says that a global
fixed-endpoint minimizer of the regularized L-action minimizes every proper
prefix among competitors that are C1 on that closed prefix and have the same
prefix endpoints.

`lRegCostC1_eq_on` is the companion cost-identification theorem.  A curve that
is C1 on a closed interval and beats every global fixed-endpoint C1 competitor
realizes `lRegCostC1`, even when the curve itself is not presented globally.

## Native route

The proof joins an arbitrary prefix competitor to the unchanged minimizing
tail with `exists_chartH1_join`.  The finite chart realization is approximated
by global fixed-endpoint C1 curves through `lAction_c1_dense`; global
minimality passes to the action limit.  `lRegAction_add` and
`lRegAction_congr` then cancel the unchanged tail.  No new compactness,
geodesic, tensor, or frontier assumption is introduced.

For `lRegCostC1_eq_on`, the curve is joined to itself at an interior point and
the same density theorem supplies global C1 approximants.  The upper bound is
passed through their action limit; the reverse bound is the defining `sInf`
inequality.  This avoids strengthening the public theorem to global C1.

## Verification

Focused verification and targeted module refresh pass without warnings.  The
proofs contain no project placeholders and add no new assumptions beyond the
compact finite-chart density theorem they consume.  Axiom audits of both
public endpoints report only `propext`, classical choice, and quotient
soundness.

## Project position

Both prefix transfer and closed-interval cost identification are complete
(100%).  `CutDomain.lMinDomain_down` now consumes them, so downward closure is
also complete.  `CutStrict.lMinVec_unique_lt` now consumes this splice route
to prove strict pre-cut uniqueness.  The remaining L5 frontier is the
nonconjugacy-before-cut theorem and the limiting cut alternative needed to
separate the open injectivity domain from its cut boundary.  `redVolume_anti`
remains 0% until its theorem is proved.
