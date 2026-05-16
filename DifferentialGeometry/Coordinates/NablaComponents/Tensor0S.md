# Tensor0S Nabla Component Notes

## Goal

Generalize the one-form local-frame smoothness route to arbitrary covariant
valence `(0,s)`.

## Current pass

- Added a focused `Tensor0S.lean` module so the general route does not further
  grow `OneForm.lean`.
- Added smoothness of `alpha` evaluated on coordinate-frame slots.
- Added smoothness of a single correction term where one coordinate-frame slot
  is replaced by its covariant derivative along `X`.
- Added the local-frame reconstruction consumer:
  if every coordinate-frame evaluation of `nabla0SFun s cov X alpha` is smooth
  at the chart center, then the full `(0,s)` tensor section is smooth.
- Proved the finite-dimensional derivative bridge
  `covariantDerivative_modelInChart_center_eq_fderiv_plus_connection`, turning
  the existing finite-basis connection formula into the fixed-chart identity
  `model(nabla_X V) = D(V_model)[X_model] + Gamma_X(V_model)`.
- Proved the general pointwise moving-slot formula
  `nabla0SFun_eval_coordFrame_moving_raw`:

```text
(nabla_X alpha)(V_1,...,V_s)
= X(alpha(V_1,...,V_s))
  - sum_a alpha(V_1,...,nabla_X V_a,...,V_s).
```

- Proved the scalar-generic local-coordinate smoothness consumer
  `nabla0SFun_eval_coordinateFrame_contMDiffAt`.
- Proved the final scalar-generic finite-dimensional local-frame theorem
  `nabla0SFun_contMDiff` for arbitrary covariant valence `(0,s)`.

## What worked

The successful route was intrinsic/local-frame rather than arbitrary chart
change:

1. Convert the finite-basis vector-field connection formula into a direct
   `fderiv + Gamma` theorem.
2. Bridge chart scalar derivatives to `extDerivFun`.
3. Use the model product rule `fderivWithin_tensor0SModel_eval_slots`.
4. Convert model-slot correction terms back to intrinsic tensor evaluations.
5. Reconstruct smoothness from coordinate-frame evaluations with
   `contMDiff_multilinearSection_iff_coord`.

No arbitrary-`Gamma` chart-change naturality theorem was introduced.

## 2026-05-11 cleanup

The final smoothness theorem in this coordinate module now delegates to the
tensor-layer theorem:

```lean
Tensor0SBundle.nabla0S_reg
```

So this file remains useful for coordinate-frame/component-facing statements,
but it no longer owns the generic `(0,s)` smoothness proof.  The proof route
that was developed here has been copied down into
`DifferentialGeometry/Tensor/RSTensor/NablaOnTensors/Regularity.lean`.

Remaining boundary:

- Mixed `(r,s)` raw regularity is still a tensor-layer frontier.
- Coordinate-frame component formulas remain here because they depend on the
  coordinate-frame and Christoffel coefficient APIs.

## 2026-05-11 status check

- Verified that the `(0,s)` connection smoothness gap is closed in this
  coordinate/local-frame layer by `nabla0SFun_contMDiff` and the bundled
  wrapper `nabla0SCoord`.
- Verified `DifferentialGeometry/Coordinates/NablaComponents/Tensor0S.lean` and the
  compatibility wrapper `DifferentialGeometry/Coordinates/NablaComponents.lean`.
- The remaining sorries are not in this coordinate theorem: they are the lower
  bundle-level fixed-chart `âŠ¤` regularity frontier in
  `NablaOnTensors/Raw.lean`, the mixed `(r,s)` raw regularity theorem, and an
  unrelated tangent-constant connection regularity helper in
  `NablaOnTensors/Connection.lean`.

## 2026-05-10 scalar genericity

- Worked: lifted the general `(0,s)` coordinate/Nabla component stack and the
  local-frame smoothness theorem from `Real` to generic `ð•œ`.
- Worked: the earlier `nabla0SReal` compatibility alias was removed in favor
  of the generic `nabla0SCoord` wrapper.
- Worked: generic smoothness required lifting the reusable helpers
  `TensorMultilinear.contMDiffAt_section_apply` and
  `extDerivFun_apply_contMDiffAt`, not adding an `RCLike` assumption here.
- Failed: after replacing `CoordinateIdx E` by a scalar-parametric abbreviation,
  Real consumers had to spell `CoordinateIdx (ð•œ := Real) E` explicitly.
## 2026-05-11: Smooth `(0,s)` coordinate consumers

- Lowered the coordinate-facing `(0,s)` `nabla0SFun` smoothness and component consumers to smooth regularity.
- No new chart-center argument was introduced; the file continues to consume the local-frame smoothness theorem from `NablaOnTensors`.
- Verification passed.
