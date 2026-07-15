# CrossMetricEnergy

## Role

This module proves a support-independent cross-metric scalar energy bound.
For fixed smooth metrics `q` and `k`, the `k`-Hessian and `k`-differential
energies of a finite `q`-spectral representative are integrated against the
fixed `q` volume and controlled by its spectral `H²(q)` norm.

No comparison of Riemannian volume measures is used.  The proof compares the
two fiber norms on the compact manifold and writes `Hess_k` as `Hess_q` plus
the connection-difference output applied to `du`.

## Verification status

`cross_energy_le` is verified without `sorry`.  Both its focused check and its
targeted module build passed.

An initial monolithic pointwise proof exceeded the local heartbeat budget.
Moving the invariant pointwise comparison into `cross_point_le` closed the
performance issue; increasing heartbeats was not needed.

## Progress accounting

- `cross_energy_le`: 100% theorem and 100% dedicated machinery.
- Pairwise moving-Laplacian energy producer: 100% after its downstream use in
  `MetricLapDiffPair` was verified.
- `lapDiffA20_short`: verified (100% theorem and dedicated A2 machinery).
- Full geometric nonautonomous input package: about 50% machinery; its final
  assembly theorem is 0%.
- Moving conjugate-heat theorem: 0%.
- Perelman no-local-collapsing theorem: 0%; dedicated machinery about 8%.
