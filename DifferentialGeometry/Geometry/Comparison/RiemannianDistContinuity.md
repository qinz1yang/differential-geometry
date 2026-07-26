# RiemannianDistContinuity

## 2026-07-16 pairwise chart-distance producer

Mathlib's `eventually_riemannianEDist_le_edist_extChartAt` controls the
Riemannian distance from the chart center to one nearby point. That one-fixed-
endpoint statement does not imply the pairwise Lipschitz estimate needed by
Euclidean difference quotients or a chart-pushed distance cutoff.

`chart_symm_edist_le` generalizes the same path-length proof to arbitrary
endpoints in one sufficiently small convex ball in the extended chart range.
It uses only the local derivative bound for `extChartAt.symm`, the Euclidean
line segment, and `riemannianEDist_le_pathELength`. It does not use an
exponential chart, injectivity radius, `HasLocallyConstantChartAt`, or any
noncollapsing input, so the route is non-circular.

This producer gives a metric-dependent local constant. Compactness can make
it uniform over the finitely many fixed chart supports for one fixed metric;
it does not by itself make the constant uniform along flow times approaching
a singular endpoint.

`chart_inv_edist_le` removes the remaining fixed-center restriction for a
single chosen chart. At an arbitrary target point it switches locally to the
chart centered at the corresponding manifold point, applies
`chart_symm_edist_le`, and composes with the smooth chart transition. This is
the local statement needed to treat a POU-weighted distance tent throughout
the support of a fixed chart, rather than only near that chart's center.

Focused verification passed without warnings.

## 2026-07-23 fixed-parametrization distance producer

`diffeo_edist_le` gives a pairwise Riemannian extended-distance bound on a
positive model ball for any fixed `C¹` partial diffeomorphism from the model
space into the manifold.  Its conclusion also records that the whole model
ball lies in the partial diffeomorphism's source, so later change-of-variables
and density arguments can use the same ball without reconstructing domain
membership.

The proof reuses `chart_symm_edist_le` at the image of the source point and
composes it with the locally Lipschitz coordinate transition
`extChartAt ∘ Ψ`.  This avoids any normal-coordinate choice, exponential-map
continuity, or tensor-instance import at this layer.

For the fixed normal-chart volume route, instantiate the theorem with
`Ψ := expMapDiffeo g p` and the source point `0`; this directly bounds the
Riemannian distance between the corresponding normal-chart inverse images.
A normal-chart-specific wrapper was deliberately not added because it would be
a thin duplicate of this canonical producer.

Focused verification passed without warnings.  `diffeo_edist_le` itself is
complete (100%).  The fixed-chart spatial distance-control subproblem is
complete (100%); `family_vol_low` remains unproved (theorem 0%), while its
dedicated direct-route machinery is roughly 65% complete pending uniform
small-time scalar density and speed control in each fixed parametrization.

## 2026-07-23 parametrized segment control

`param_edist_le` converts a pointwise tangent-speed bound along one model-space
segment into a Riemannian extended-distance bound between its parametrized
endpoints.  It uses the straight line, the manifold chain rule, and the
path-length characterization directly; no metric-space realization, global
frame, or whole-tensor equality is introduced.

Focused verification passed without warnings.  This closes the reusable
speed-to-distance producer needed by `FamilySmallBall`; the remaining work
there is measure algebra and compact finite-cover assembly.  `family_vol_low`
itself remains theorem-level 0% until that assembly is checked.
