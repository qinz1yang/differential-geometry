# HamiltonBaseProducer

## Role

This file supplies the arbitrary-dimensional level-zero Hamilton curvature
evolution used by the later StarSum/Uhlenbeck tower.  It remains below the
StarSum consumer layer and does not import a dimension-three or Weyl-flat
specialization.

## Current status

- `rm04Deriv_of_coord` transports coordinate-frame component derivatives to
  arbitrary fixed tangent vectors.
- `rm04Base_of_solution_any` is proved directly from `IsSolutionOn` for every
  finite orthonormal basis.  Its derivative is the metric trace of
  `nablaKRm04Field` at level two plus `hamiltonRmReact`.
- The proof uses the canonical chain
  `coordMetricDeriv -> coordMetricMix -> coordGammaEvol -> coordGammaMix`, then
  the curvature-coefficient product rule and `gammaCovNab2Core`.
- The earlier conditional route through a supplied
  `MetricFrameSpacetimeRegularityInFrameOnLocal` package was removed.  Positive
  tail restriction and `localFrameInv` transport are unnecessary here.
- Focused verification passes, and the exact module refresh is GREEN
  `3771/3771`.  The file contains no `sorry`, `admit`, or declared axiom.

## Progress accounting

- `rm04Base_of_solution_any`: 100%, focused+exact current.
- Dedicated arbitrary-dimensional Hamilton base machinery: 100%.
- `residualStarCosted`: 0%; it is the next theorem-level producer and must not
  be counted as completed by this base identity.
- Direct `towerHeatSol`: 0%.
- Unconditional MSM135 Theorem 3.10: 0%; dedicated P4 consumer machinery is
  approximately 97%.

## Next target

Wire this public base theorem into the arbitrary-dimensional residual producer
without adding a wrapper assumption.
