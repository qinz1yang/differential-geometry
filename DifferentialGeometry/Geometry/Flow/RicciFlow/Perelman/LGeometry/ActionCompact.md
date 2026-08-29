# ActionCompact

## Implemented capstone

`ActionCompact.lean` proves `lAction_subseq`: a sequence of regularized L-curves on a fixed compact
parameter interval and compact target manifold has a uniformly convergent subsequence whenever
all curves share one regularized-action upper bound and the natural differentiability and
integrability hypotheses.

The conclusion provides a strictly monotone subsequence and a genuine continuous map
`g : C(Set.Icc a b, M)`, with `TendstoUniformly` on the entire parameter interval. No endpoint
condition is imposed because it is not needed for this weakest compactness theorem.

`lAction_subseq_fix` is the fixed-endpoint corollary needed by a minimizing sequence. If every
curve joins the same two points, pointwise convergence at the two endpoint subtypes and uniqueness
of limits show that the C0 limit joins those points as well.

`lChartH1_subseq` is the fixed-chart weak compactness producer. Starting only
from one common upper bound for the original full `lRegAction`, it returns one
strictly monotone subsequence, a `timeH1` limit, weak convergence of the chart
derivatives against every `timeL2` test, and uniform convergence of the
continuous chart representatives. The scalar lower constant, scalar and
kinetic integrability, and the resulting chart kinetic budget are all produced
inside the proof.

Focused verification passes without warnings or placeholders. The `lAction_subseq` and
`lAction_subseq_fix` theorems and this C0 compactness capstone are 100% complete.
`exists_lMinimizer` remains unstated and unproved
(0%): compactness of minimizing sequences is now available, but closure of the intended competitor
conditions and lower semicontinuity of the complete regularized action still have to be assembled.
Its dedicated direct-method machinery is approximately 75--80% complete. Dedicated L-geometry
machinery is approximately 72--76% complete; reusable generic prerequisites are approximately
99% complete. `redVolume_anti` remains unstated and unproved (0%), P2 remains below 1%, and the
whole Poincare program remains approximately 3--5% complete.

## Proof route

The action-to-energy theorem `lRefEnergy_bound` is invoked once, outside the sequence quantifier.
Consequently one pair of compact-slab constants and one fixed-reference `curveEnergy` budget work
for every curve in the family.

For each ordered subinterval, `curveEnergy_mono` restricts that global budget and
`edistOf_le_budget` gives the intrinsic reference-metric square-root estimate. The function
`r ↦ sqrt r * sqrt B` tends to zero at zero. Combining this filter statement with
`dist_lt_of_riedist` proves uniform equicontinuity in the ambient pseudometric. Reversely ordered
points are handled by swapping the ordered intrinsic estimate and using ambient `dist_comm`; this
avoids comparing whole Riemannian-bundle instances.

Each curve is then restricted to a continuous map on `Set.Icc a b`, and `arzela_subseq_cpt` is
applied with the compact target set `Set.univ`. The fixed-endpoint corollary uses
`TendstoUniformly.tendsto_at` at the two endpoint subtypes and Hausdorff uniqueness of limits.

For `lChartH1_subseq`, `curve_cont_local` first derives continuity of every
manifold curve from its local `timeH1` representative. `lScalar_lower` and
`lScalar_int` give a uniform lower bound for the scalar-potential integrals;
`lKinetic_int_local` makes the kinetic term integrable. The resulting honest
action split converts the full-action bound into a common manifold kinetic
bound, and `lKinetic_local` identifies it with the exact fixed-chart Gram
quadratic integral. `chartH1_subseq` then supplies the common weak/uniform
subsequence. A private helper isolates this action-to-kinetic calculation and
keeps the public theorem inexpensive to elaborate.

## Boundary

The implementation introduces no admissibility or minimizer class, no path-space foundation, no
`IsMetricNorm` or `CompleteSpace` assumption, and no supplied equicontinuity hypothesis. It does not
edit the action, Arzela--Ascoli, or Riemannian-distance producer files.

The chart-H1 theorem additionally introduces no supplied scalar lower
constant, integrability hypothesis, kinetic bound, or path-space wrapper. Its
fresh model-space section avoids the older C0 theorem section's redundant
normed-space instance, so the public assumptions are exactly finite-dimensional
real Hilbert chart data, chart containment, metric/scalar regularity, and the
full action bound.
