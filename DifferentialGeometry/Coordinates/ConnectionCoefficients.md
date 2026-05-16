# Connection Coefficients Notes

## 2026-05-10 coordinate abstraction

- Worked: split the fixed-chart connection-endomorphism to coordinate
  Christoffel bridge out of `NablaComponents.Basic`.
- Worked: `connCoeff_eq_christoffelAlong_coord` now reuses
  `coordinateFrameAt_coeff_eq_toBasis_coord`; the remaining base-point chart
  identification is handled by `TangentBundle.continuousLinearMapAt_trivializationAt`
  and `mfderiv_extChartAt_self`.
- Failed: a direct `simp` after rewriting the coordinate-frame basis left an
  identity continuous-linear-map application unsolved. The robust endpoint was
  to rewrite the tangent trivialization to `mfderiv extChartAt`, then rewrite
  the base-point derivative to `ContinuousLinearMap.id`.
- Verification passed.
## 2026-05-10 scalar genericity

- Worked: generalized the fixed-chart connection-endomorphism/Christoffel
  bridge to generic `ð•œ`.
- Failed: no proof obstruction appeared once `CoordinateFrame` and the tensor
  component layer were rebuilt with scalar-generic declarations.
## 2026-05-11: Smooth coefficient bridge

- Replaced the ambient `top` manifold assumptions with `infty` / `infty + 1`.
- This theorem is only the fixed-chart connection coefficient to coordinate Christoffel bridge; no analytic regularity is mathematically needed here.
- Verification passed.
