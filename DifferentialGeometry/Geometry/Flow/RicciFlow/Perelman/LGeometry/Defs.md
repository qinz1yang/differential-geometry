# `Defs.lean`

## Status

Focused verification passes without local warnings.  The migrated
`arxiv-preprint` module uses the current `Solution/Basic` and curvature
namespaces and is consumed by all later L0--L3 modules.

## Checked content

- `lVelocity` is the manifold derivative of a raw curve applied to unit
  backward-time velocity.
- `lSpeedSq` uses the total family metric at forward time `T - tau`.
- `lDensity` has the Morgan--Tian normalization
  `sqrt tau * (R + |X|^2)`; no nonnegativity theorem is claimed for it.
- `lLength` is the oriented interval integral of `lDensity`.
- Zero intervals, adjacent-interval additivity, speed-square nonnegativity,
  germ-level curve congruence, moving-metric/scalar continuity, and interval
  integrability are checked.

The continuity proof reuses the native tangent-bundle velocity lift and the
native moving-metric quadratic evaluation.  It fully applies the metric before
comparing values, so it does not unfold dependent tangent bundles or Hom
representations.  The scalar hypothesis is kept separate from metric
smoothness, and the carrier condition is imposed only on the theorems that use
solution-time regularity.

Curve congruence intentionally assumes equality of germs at each integration
point.  Pointwise or almost-everywhere equality of curves alone does not imply
equality of their manifold derivatives.

## Progress and next target

L0 is complete and consumed through the focused-green local regularized
L-geodesic existence/uniqueness stage.  `redVolume_anti` remains **0%**;
dedicated L-geometry machinery is about **16--18%**, and reusable generic
prerequisites are about **60--70%**.  P2 remains below **1%**.

The next stage is the L-exponential map.  It first needs a canonical maximal
regularized-solution domain and an explicit domain-exterior totalization, not
another definition-level L-length wrapper.
