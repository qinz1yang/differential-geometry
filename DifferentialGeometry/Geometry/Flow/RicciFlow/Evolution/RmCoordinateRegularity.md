# RmCoordinateRegularity

## 2026-07-13

- The chosen route factors coordinate curvature through the existing smooth
  metric two-jet operator jetRiemann.
- The original `realizedRmBase` target used `coordinateFrameAt`, whose
  `Module.finBasis` is not definitionally the `chartModelBasis` used by the
  chart Christoffel and Riemann formulas. Treating them as the same basis is
  invalid; the arbitrary-frame result needs a later finite-dimensional change
  of frame.

## 2026-07-14

- `coordRmSmoothInf` now proves joint spacetime `C-infinity` regularity of the
  canonical lowered Riemann tensor evaluated on `chartBasisVecFiber` at every
  regular spacetime point in `chartLeviCivitaGoodSet`.
- The proof lowers the coordinate Riemann tensor with the chart Gram matrix and
  composes through the extended chart. The product-model and bundled-section
  boundaries use the existing `contMDiffAt_prod_module_iff`,
  `metricRm04_apply`, and `rm04_coord_eq` bridges.
- Focused verification passed without warnings. This closes the chart-basis
  base case only; transfer to a supplied smooth frame, and hence the all-level
  moving-frame swap needed by `movingShi_of_soln`, remains open.
- `coordRmFinSmooth` closes the immediate `chartModelBasis` versus
  `Module.finBasis` mismatch for the canonical coordinate frame. Both frames
  come from the same tangent trivialization, so each coordinate-frame vector
  is a finite sum of chart-frame vectors with constant model-space
  change-of-basis coefficients. Four-linearity expands `realizedRmBase` into a
  finite sum of `coordRmSmoothInf` components. Focused verification passed
  without warnings.
- This constant change of basis is enough for the coordinate tower. A later
  transfer from coordinate components to an arbitrary smooth orthonormal frame
  is still required by the local-frame Shi consumer.
