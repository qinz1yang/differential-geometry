# StepCNormalBump notes

## 2026-07-09: intrinsic quadratic-radius bump core

- Added the checked `quadNormal` core and its evaluation, range, inner-ball,
  support, and global-smoothness lemmas.  The support proof uses the closed
  ellipsoid `g_p(v,v) ≤ rOut`, compactness from finite dimensionality, and
  `norm_lt_expMapC2Radius_of_sqrt_inner_lt`; it never identifies the model norm
  with the metric norm.
- The focused file verification and targeted module build passed.
- A generic realized-metric `oneOn` / support-in-ball wrapper was attempted in
  three shapes but was not retained.  Its exact blocker is the tangent-fibre
  norm instance diamond: the explicit `hEnorm`, `riemannianEDist`, and
  `ProperMetricOn.realizes` terms elaborate with non-definitionally-equal
  `Tensor0SBundle` and `RiemannianBundle` norm/topology instances.
- Smallest next bridge: prove the realized-ball wrappers in the already
  RiemannianBundle-aligned producer context (as in `StepCProducers`), or expose
  a single norm-aligned radial-distance adapter there; do not add a metric/model
  norm equivalence assumption.
- Honest scale: the final explicit intrinsic atom producer theorem is still
  unstated (0%); its dedicated normal-bump core is about 65%; Step-C machinery
  remains about 75%; the conditional Theorem 3.9 endpoint remains 0%.
