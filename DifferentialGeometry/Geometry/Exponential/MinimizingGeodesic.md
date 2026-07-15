# MinimizingGeodesic

## 2026-07-10 — named intrinsic/realized exponential agreement radius

- Added `expDiffeoRadius`, a named positive pointwise radius obtained by
  intersecting the intrinsic/realized agreement radius with `expRadiusGp`.
- Added `expDiffeo_mem_of_lt` and `expDiffeo_eq_intr`.  Below the named radius,
  a tangent vector lies in the source of `NormalCoordinates.expMapDiffeo`, and
  the realized exponential equals `expMapIntrinsic`.
- Focused verification and the targeted module build passed.
- Scope limitation: this is a fixed-base, pointwise producer.  It gives no
  continuity or uniform positive lower bound for `p ↦ expDiffeoRadius g hEnorm p`.
  Consequently the common moving-base `C^infty` domain and finite-hat
  containment remain separate Step-C frontiers.

