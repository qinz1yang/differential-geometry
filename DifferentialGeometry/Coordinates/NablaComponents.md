# NablaComponents Compatibility Import

## 2026-05-12: Mixed tensor exports

- Added compatibility imports for
  `DifferentialGeometry.Coordinates.NablaComponents.TensorRS` and
  `DifferentialGeometry.Coordinates.NablaComponents.TensorRS12`.
- This preserves the existing public split-import structure while exposing the
  new mixed tensor coordinate derivative layer to downstream users.

## 2026-05-13: Coordinate Ricci identity experiment

- Added the compatibility import for
  `DifferentialGeometry.Coordinates.NablaComponents.RicciIdentity`.
- The new module is an experiment for the LaTeX-style coordinate proof of the
  `(0,s)` Ricci identity.  It does not replace the invariant theorem and keeps
  the remaining proof frontier as one total finite-sum comparison.
- Compatibility verification passed with the expected single `sorry` in the
  experimental theorem.
