# `Naturality.lean`

## Status

Verified warning-free.  The file is the native fixed-diffeomorphism naturality
layer above `Exp.lean`; it contains no placeholders or new assumptions.

## Intended chain

- `lRegAccel_pull` transports the regularized acceleration using scalar,
  gradient, Ricci, and pullback-metric naturality.
- `isLRegCurve_pull` transports a single regularized-curve witness using
  `chartRep_map_diff` and `covAlong_natMDiff`.
- `lRegDomain_pull` uses both directions of the diffeomorphism and the native
  pullback composition law to identify maximal witness domains.
- `lRegCurve_pull`, `lExpDomain_pull`, and `lExp_pull` use witness uniqueness to
  identify the chosen totalized curve and L-exponential map.

No new class, wrapper assumption, or parallel geometric definition is
introduced.  The single-witness theorem is directional; maximal-domain equality
uses the inverse diffeomorphism genuinely.

## Proof record

The acceleration proof pairs both sides with the target metric.  Pullback-metric
evaluation, scalar pullback, gradient pullback, and Ricci pullback reduce the
identity to the existing `lRegAccel_inner` formula.  This avoids introducing a
new metric-sharp transport wrapper.

The mapped velocity identity is proved without a differentiability hypothesis:
the chain rule handles differentiable points, while a hypothetical
differentiable mapped curve pulls back through the inverse diffeomorphism and
contradicts source nondifferentiability.  Consequently `chartRep_map_diff` can
be applied to the exact L-velocity field, not merely an eventually equal
surrogate.

For maximality, pulling the pulled-back solution through the inverse
diffeomorphism recovers the original solution by `pullbackMetric_trans` and
`pullbackMetric_refl`.  This supplies both witness directions.  The totalized
curve is then identified on witness intervals by `lRegCurve_eqOn`; outside the
common maximal domain both curves reduce to their base points.

Focused verification passed without warnings.  No mathematical, API,
coercion, or tooling blocker remains.

## Project position

The six requested naturality declarations are complete (100%), and their
dedicated generic pullback infrastructure is complete (100%).  This closes the
fixed-diffeomorphism naturality lane for `lRegCurve` and `lExp`; it does not
advance the later L-Jacobi, cut-domain, reduced-length, or reduced-volume
phases.  Together with `Scaling.lean`, this closes L3.  Dedicated Perelman
L-geometry machinery is about 30--32%, generic prerequisites about 75--80%,
and reduced-volume monotonicity remains at 0%.
