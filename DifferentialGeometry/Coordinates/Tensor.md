# Tensor Notes

## 2026-05-10 scalar genericity

- Worked: kept local-frame tensor component definitions generic over `ð•œ`.
- The file now follows the scalar-generic coordinate layer and returns `ð•œ`
  components rather than Real components.

## 2026-05-14 component API wrappers

- Worked: added domain-aware local-frame wrappers over `component0S` and
  `componentRS`, so new coordinate proofs can use `hframe.toBasisAt hx` instead
  of unfolding local-frame values, Hom inputs, or `basisTensor0S`.
- Worked: added common slot/index helpers and readable `(0,2)`, `(0,4)`,
  `(1,2)`, and `(1,3)` component wrappers.
- Verification passed for this file and the direct coordinate/curvature
  consumers.  The only observed warning is the pre-existing upstream `sorry` in
  `Coordinates/NablaComponents/TensorRS.lean`.
