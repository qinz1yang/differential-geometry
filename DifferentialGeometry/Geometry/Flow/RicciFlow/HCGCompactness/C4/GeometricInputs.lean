-- Chapter 4 honest geometric inputs, split by step:
--   * Step A inputs (`PointedSeqDistance`, `InjRadiusDecayInput` = A0/`lbl384`,
--     `VolumeComparisonInput` = A0'): `StepAInputs.lean`.
--   * Step B input (`normalTransition`, `NormalTransitionDerivBound`,
--     `ExpInverseDerivBoundInput` = S6/`lbl418`): `StepBInputs.lean`, rebuilt on the
--     native `Geometry.Riemannian.NormalCoordinates` API.  (The former in-file S6
--     section referenced the nonexistent `RicciFlower.Coordinates.NormalChartData`
--     and never compiled; it was removed on 2026-06-09.)
-- This file remains as the umbrella import path for older callers.
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepAInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs
