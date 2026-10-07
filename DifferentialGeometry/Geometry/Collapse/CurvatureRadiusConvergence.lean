import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusConvergencePortHGI2

/-!
Shim (S-HG-INTAKE-2, suffix `_HGI2`): the donor file
`Geometry/Collapse/CurvatureRadiusConvergence.lean` needs
`curvatureRadius_le_of_sectionalCurvature_le`, absent from the tracked
`CurvatureRadiusBounds.lean` (see `CurvatureRadiusBoundsHGI2`).  The donor text (with one extra
`import`) lives in `CurvatureRadiusConvergencePortHGI2.lean`; this file only re-exports it, so that
`CurvatureRadiusPullback` stays byte-identical to the donor.
-/
