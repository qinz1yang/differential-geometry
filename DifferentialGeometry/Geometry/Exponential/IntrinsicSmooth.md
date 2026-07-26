# IntrinsicSmooth.lean

## 2026-07-19 created (option-1 lane, brick R2-corollary)

`intrinsicGeodesic_contMDiffOn_infty`: the intrinsic geodesic of a complete
manifold is `C^∞` in time on all of `ℝ` — the `C^∞` upgrade of
`intrinsicGeodesic_contMDiffOn` (C¹, `IntrinsicExp.lean`).  Three-line
application of `isGeodesicOn_contMDiffOn_infty`
(`Geodesic/ChartRegularity.lean`).

Focused check PASSED, no `sorry`.  Placed as a new leaf file (not appended to
`IntrinsicExp.lean`) to avoid re-elaborating and staling the hot 1450-line
file in the multi-agent tree.

Consequence for the Route B frontier: the TIME-regularity half of the
`expMapC2Radius`-type caps is dissolved — the radial geodesic `t ↦ exp_p(t·x)`
in intrinsic form is `C^∞` on every compact window for every launch vector.
Still open on the option-1 lane (see VOLUME_COMPARISON_PLAN.md ledger): the
Volume-lane consumers still use the chart-based `radialCurve`; re-target to
the intrinsic radial curve, then Jacobi along it (parallel-frame linear ODE),
no-conjugate-from-minimizing, comparison continuation, change-of-variables on
strictly injective balls, packing.
