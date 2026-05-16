# Coordinate Frame Notes

## 2026-05-10

- Added `coordinateFrameAt_mdifferentiableAt` as a reusable coordinate-frame
  differentiability handle at the base point.
- This removes repeated local-frame smoothness scaffolding from downstream
  coordinate proofs, especially the Levi-Civita torsion proof.
- Verification passed.
## 2026-05-10 coordinate abstraction

- Worked: moved the C1 coordinate local-frame handle and the base-point
  coordinate-basis equality into this file, so downstream coordinate proofs no
  longer need `NablaComponents.Basic` for pure frame facts.
- Worked: added `coordinateFrameAt_coeff_eq_toBasis_coord` as the public
  version of the recurring base-point coefficient calculation.
- Verification passed.
## 2026-05-10 scalar genericity

- Worked: generalized the coordinate frame and coordinate component API from
  `Real` to an explicit scalar field `ð•œ` with
  `[NontriviallyNormedField ð•œ] [CompleteSpace ð•œ]`.
- Worked: `CoordinateIdx` is now scalar-parametric. Generic downstream files
  must write `CoordinateIdx (ð•œ := ð•œ) E`; Real consumers should write
  `CoordinateIdx (ð•œ := Real) E` when inference is otherwise stuck.
- Failed: the first check exposed a stale dependency boundary and a Real-only
  tensor component layer. Generalizing `CoordinateBasis` and `Components`, then
  rebuilding those modules, resolved the issue.
- Verification passed.

## 2026-05-12 fixed-chart pullback

- Worked: added the private generic helper
  `coordinateFrame_pullback_eq_const_of_mem`, showing that a coordinate-frame
  field has constant model pullback coordinates at any point of the same fixed
  coordinate frame set.
- This is the local-coordinate input needed if the LC Christoffel smoothness
  route later proves bracket-zero or coefficient formulas throughout a fixed
  chart, not only at the chart center.
- Verification passed with
  `.\scripts\lake-locked.ps1 check -Token 3b106275-e9d0-406e-8bbf-ebf6fe50f323 -Files DifferentialGeometry\Coordinates\CoordinateFrame.lean`.

## 2026-05-14 off-center bracket

- Worked: proved `coordinateFrameAt_bracket_zero_of_mem`, the fixed-chart
  bracket vanishing statement at any point of the coordinate-frame base set.
- The proof uses the existing fixed-chart model pullback equality, Mathlib's
  pullback compatibility for Lie brackets, and the zero bracket of constant
  model vector fields.
- Learned: this off-center theorem needs an `IsRCLikeNormedField` assumption.
  The Mathlib Lie-bracket pullback API requires `minSmoothness 𝕜 2`, which
  does not follow from `C∞` over arbitrary non-real fields.
- Verification passed.
