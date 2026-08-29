# ActionCapstone

## Role

`lAction_chart_lsc` is the finite-chart direct-method assembly for a
fixed-endpoint, uniformly regularized-action-bounded sequence of `C¹` curves.
It produces a strictly monotone subsequence, a continuous raw curve, a finite
ordered chart subdivision, and one chart-valued `timeH1` limit on each piece.
The final inequality is the finite generalized chart action bounded by the
liminf of the subsequence actions.

`lAction_liminf` is the final raw-action endpoint.  It retains the same weakest
inputs, hides the finite chart realization, and concludes that the continuous
limit's actual `lRegAction` is bounded by the subsequence liminf.

Neither theorem introduces a path-space object, states an admissibility
predicate, or claims `exists_lMinimizer`.  The chart theorem's limiting kinetic
terms are the weak derivatives of the local `timeH1` representatives; the raw
endpoint identifies their finite sum with `lRegAction` but does not supply the
separate global regularity upgrade needed for minimizer existence.

## Assembly route

`lAction_subseq_fix` first supplies the continuous compact-interval limit and
preserves the endpoints.  `Set.IccExtend` gives its continuous raw extension.
`exists_cpt_split` supplies compact chart buffers and an eventually constant
natural subdivision; restricting it to `Fin (m + 1)` supplies the finite
ordered subdivision used below.

`exists_chartH1_fin` discards one common initial tail and constructs the
canonical shifted coordinate representatives.  `lChartH1_fin` then extracts a
common subsequence with local weak derivative convergence and uniform
coordinate convergence.  The final limit coordinate equality is proved by
pointwise uniqueness of limits: the local uniform representative limit agrees
with the chart image of the globally uniform manifold limit.  Finally,
`lRegAction_fin_lsc` supplies the generalized lower-semicontinuity inequality.

For `lAction_liminf`, `IsSolutionOn` supplies the smooth metric family and
continuous scalar curvature inputs.  `lRegAction_chart` then rewrites the raw
action of the limit curve exactly as the finite generalized chart action, so
the chart inequality closes the endpoint without a new assumption or analytic
frontier.

## Verification and boundary

Focused verification passes without warnings or placeholders.

`lAction_liminf` and the raw-action lower-semicontinuity stage are complete
(100%).  The endpoint `exists_lMinimizer` remains unstated and unproved (0%);
its dedicated direct-method machinery is about 72--78%.  The exact next
producer is `lAction_c1_dense` in `ActionDensity.lean`: fixed-endpoint C1
approximation of the finite chart-H1 limit, with strong local derivative and
action convergence.  Existing manifold smooth approximation controls only C0
error, while the current `timeH1` API has no endpoint-preserving smooth-density
and chart-gluing theorem.  A separate Tonelli/Euler--Lagrange upgrade remains
after this density result.  Dedicated L-geometry machinery is about 73--77%
overall; this endpoint does not move `redVolume_anti` (0%).  P2 remains below
1%, and the whole Poincaré program remains about 3--5%.
