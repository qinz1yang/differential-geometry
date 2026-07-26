# NormalPhaseRealization

## Role

This is the geometric realization layer between the quantitative phase ODE in
`NormalPhase.lean` and the intrinsic geodesic/exponential-map endpoint.

## Current state

- `normalPhaseVF_eq` identifies the chart geodesic vector field of
  `normalTotal`, at any self-model chart anchor, with
  `PhaseFlow.phaseField normalAccel`.
- `normalGeoOn_of_phase` turns an ordinary phase trajectory into a geodesic
  first component on any open time set.
- `normalGeoOn_of_right` combines the reusable right-derivative upgrade with
  the public one-sided phase ODE interface, yielding a geodesic on the open
  interior of the time interval.
- `normalFlow_contDiff` upgrades the same public one-sided trajectory directly
  to `C^∞` regularity on the open interior.
- `normalFlow_geoOn` discharges the required right-hand-side continuity from
  the checked `normalAccel_lip` and phase-box confinement, so each trajectory
  produced by `exists_normalFlow` has a geodesic first component on `(0, 1)`.

Focused verification and the targeted module build passed after refreshing the
concurrently completed `NormalPhase` producer module; no local proof or style
warning remains.

## Frontier

This layer is now consumed by `NormalPhaseEndpoint.normal_end_eq_intr` and
`normal_end_eq_diag`; endpoint transport and uniqueness are closed.  The live
frontier is not regularity of each time trajectory.  It is joint
`C^infinity` dependence of the retained time-one endpoint on the initial phase
point, needed before `PhaseFlow.quantInv_smooth` can supply a smooth inverse on
the explicit quantitative target.

## 2026-07-18 framed-radius migration

`normalFlow_geoOn` now consumes the same `expRadiusGp / 4` fence as
`normalAccel_lip`.  Focused verification and the module refresh passed.  No
new geometric assumption or wrapper was introduced.
