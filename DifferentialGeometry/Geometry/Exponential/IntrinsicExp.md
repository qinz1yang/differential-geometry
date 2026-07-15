# IntrinsicExp.lean notes

## 2026-07-08 radial endpoint germ

Added and verified the small-velocity bridge `exp_eq_intr_of_small`, which
packages the existing intrinsic foot-in-source producer into the existing
`expMapIntrinsic = expMap` theorem.

Also added `exp_radial_eq_intr`: near `0`, the chart-fixed radial curve
`s |-> expMap g q (s • u)` agrees with the single intrinsic geodesic
`intrinsicGeodesic g hEnorm q u`.  This is the two-sided germ missing from the
endpoint route for `s = 0`.

The checked endpoint producers are:

- `exp_radial_geo_zero`: under the intrinsic completeness hypotheses, the
  chart-fixed radial exponential curve satisfies `HasGeodesicEquationAt` at `0`.
- `exp_radial_d2_zero`: the same radial curve has zero covariant acceleration at
  `0`.  The `C²` input comes from `radialCurve_contMDiffAt2` at `0`, so no new
  intrinsic-geodesic regularity theorem was needed.

The remaining V1c bridge is downstream: use this slice acceleration result in
the radial Jacobi variation endpoint proof to close the concrete
`D_t^2 J(0)=0` input.  Verification passed for the file.

## 2026-07-10 moving-chart interval uniqueness

Added `geo_eqOn_of_init`, the open-preconnected-domain form of geodesic
uniqueness.  It propagates equality by moving to the chart centered at each
cluster point, so neither curve must remain in one fixed chart.  The producer
only assumes continuity and the geodesic equation on the common open time
domain, together with matching foot and tangent vector at time zero.

Added `geo_end_eq_intr`, which applies that producer on `(-1,1)` and then uses
continuity on `[-1,1]` to pass to the right endpoint.  Thus a segment launched
from `(q,v)` has value `expMapIntrinsic g hEnorm q v` at time `1` without any
fixed-chart confinement hypothesis.  Focused verification passed without
warnings, and the targeted module build passed; replayed upstream warnings do
not affect these declarations.

This closes the endpoint-uniqueness producer itself (100%).  It remains one
supporting brick for the moving inverse route: that final theorem is still
unstated (0%), while its dedicated infrastructure remains only partially
complete; the HCG project map remains the authoritative source for aggregate
percentages.
