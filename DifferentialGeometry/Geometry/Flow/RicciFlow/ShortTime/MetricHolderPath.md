# MetricHolderPath

## Status

Source-written on 2026-07-19; focused Lean verification is pending because a
shared named build still owns the build lane.

## Producer

- `metricChartIdx` is the finite product of the existing active POU chart set
  and the finite `(0,2)` component set.
- `metricCompPath` reuses the canonical POU-weighted `tensorChartComp` model.
- `metricParGauge` and `MetricInHolderBall` instantiate the analytic
  `HolderPath` gauge without introducing a new atlas or tensor
  representation.
- `metricConst_ball` proves that the order-at-most-three intrinsic family
  hypothesis selects one finite-chart parabolic Holder ball for all family
  members and all horizons.  Its spatial input is the global
  `metricDiff_c2half` theorem; the time seminorm vanishes because the initial
  path is constant.

This is initial-data packaging, not yet the variable-coefficient Schauder
self-map or the local Ricci--DeTurck solver.  The exact endpoint theorem
`ricci_flow_unif_existence` remains unproved.
