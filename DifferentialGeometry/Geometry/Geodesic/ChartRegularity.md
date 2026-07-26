# ChartRegularity.lean

## 2026-07-19 created (option-1 lane, bricks R1b + R2-engine)

Fixed-chart and chart-free `C^∞` regularity of moving-foot geodesics.  Part of
the option-1 route for the Route B packing-radius frontier
(`Geometry/Comparison/VOLUME_COMPARISON_PLAN.md`, 2026-07-19 ruling entry).

Proved, all focused-check green, no `sorry`:

- `chartCurve_contDiffOn` (R1b): on an open window `O` with continuity,
  foot-in-source, and `HasGeodesicEquationAt` pointwise, the fixed-chart
  reading `chartCurve q γ` AND its derivative are `C^∞` on `O`.  Assembly of
  the existing bridges `hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt`
  + `hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity`
  (`CrossVFReduction.lean`) with the new ODE bootstrap `contDiffOn_ode2_inf`
  (`Analysis/ODE/SecondOrderBootstrap.lean`); coefficient smoothness from
  `chartChristoffelContraction_contDiffOn` (`SmoothFlow.lean`).
- `isGeodesicOn_contMDiffAt_infty` / `isGeodesicOn_contMDiffOn_infty`
  (R2-engine): a geodesic continuous on an open time set is
  `ContMDiff… I ∞` there — the `C^∞` upgrade of
  `isGeodesicOn_contMDiff{At,On}_one` (`Comparison/HopfRinow.lean`), proof
  mirrored with the window supplied by `chartCurve_contDiffOn`.  No chart
  confinement, no small-radius cap.

Names exceed the 20-letter budget deliberately, for API symmetry with the
existing `_one` siblings.

Route source: frenzymath/Poincare-Conjecture
`MorganTian/PoincareLib/Ch01/GeodesicRegularity.lean` (route/decomposition
reference only; the Lean content here is assembled from our own bridges).

Membership brick simplification vs the C¹ proof: `interior target` handled by
`isOpen_extChartAt_target` (Mathlib, needs `I.Boundaryless`) instead of the
Integration-layer `extChartAt_target_subset_interior_of_boundaryless`.

Consumer so far: `Exponential/IntrinsicSmooth.lean`
(`intrinsicGeodesic_contMDiffOn_infty`).  Module built (olean available).
