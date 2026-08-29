# CutMinimizer

## Purpose

`lMinVec_reg_min` exposes the global fixed-endpoint regularized-action
minimality carried by membership in `lMinDomain`.  Its competitors are global
`C¹` curves on the same square-root-time interval.

## Route

The proof converts minimizing raw L-length to `lRegCostC1` using
`lLength_sqrt` and `lCost_eq_reg`, obtains regularity and the backward-time
window from `lExpPosDom_reg`, and closes with `lRegCostC1_le`.  This is the
small reusable producer extracted from the corresponding local argument in
`CutDomain.lMinDomain_down`.

## Verification

Focused verification passed without errors or warnings.

The public theorem assumes only the ambient compact fixed-manifold setting,
`IsSolutionOn`, minimizing-domain membership, and the competitor's global
`C¹`/endpoint data.  Positivity of `tau`, the regular square-root-time
segment, and the containing backward-time interval are derived internally.

## Project accounting

This producer is one supporting input for strict pre-cut nonconjugacy.  The
nonconjugacy theorem itself remains 0%; its dedicated negative-index machinery
is separate.  `redVolume_anti` remains 0%.
