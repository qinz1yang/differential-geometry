# TensorRS Nabla Components

## 2026-05-12: Mixed coordinate derivative bridge

- Added `coordDerivRSAt`, `modelDerivRSAt`, and
  `ModelDerivEqCoordDerivRSAt` for mixed `(r,s)` tensor fields.
- Proved `tensorRSModelAt_coordComponentRSAt` by using the fixed
  `TensorRSSpace.trivializationAt_basis_coord` theorem. The nontrivial input
  slot was the base-point identity for the fixed `(0,r)` tensor
  trivialization; `tensor0SModelAt_trivializationAt_symm` plus
  `tensor0SModelAt_apply` was the robust route.
- Proved the fixed-chart model/scalar derivative bridge by copying the
  established `(0,s)` pattern and using `fderivWithin_clm_apply` for the Hom
  input evaluation, then `fderivWithin_continuousMultilinear_apply_const_apply`
  for the output slots.
- Exposed `nablaRS_coordFrame_slots` and
  `nablaRS_coordFrame_slots_of_smooth`. These keep the derivative slots pure
  coordinate calculus and do not import Ricci-flow evolution.

## 2026-05-14: Coordinate first-product producer

Worked:

- Added `applyInput_coordFrame_eventually`, the local coordinate-frame
  expansion for applying a smooth mixed `(r,s)` tensor field to a smooth
  covariant `(0,r)` input field.
- Added `tensorRS_eval_constInChart_coordinateFrame_contMDiffAt`, supplying the
  smoothness needed to differentiate mixed components with a fixed-chart
  upper input and coordinate lower slots.
- Added `coordDeriv0SAt_applyInput_eq_sum`, the concrete coordinate Leibniz
  rule for the derivative of `tensorRSField_applyInput T theta`.

Verification passed with the expected local frontier warning.

Remaining frontier:

- `constInChart_basisTensor0S_coordFrame` is still the exact proof frontier.
  It should identify the fixed tensor-bundle `constInChart` basis input with
  the coordinate local-frame tensor basis on the chart domain.

Frontier assessment:

- This is a missing coordinate/local-frame normalization lemma, not a
  mathematical obstruction.  I expect it is solvable without user intervention,
  probably by proving the tensor-basis extensional equality from the tangent
  trivialization inverse/forward identity and the coordinate-frame basis
  theorem.

## 2026-05-14: Pro consultation on `constInChart_basisTensor0S_coordFrame`

Learned:

- The obstruction is a missing local-frame/trivialization normalization lemma,
  not curvature, Ricci-identity algebra, or a coordinate-Christoffel issue.
- The recommended route is to avoid unfolding chart derivatives and prove the
  target by `Tensor0SBundle.ext0S_basis` against
  `coordinateFrameAt_basis x0 hx`.
- The smallest useful helpers are:
  - `Tensor0SSpace.constInChart_apply_of_mem`, evaluating a fixed-chart
    constant covariant tensor by first applying the tangent
    `continuousLinearMapAt` to each slot.
  - `coordinateFrameAt_basis_continuousLinearMapAt`, saying the fixed tangent
    trivialization coordinates of `(coordinateFrameAt_basis x0 hx) i` are
    exactly `(Module.finBasis k E) i`.
  - If needed, a tiny wrapper for evaluating
    `continuousMultilinearMap_basis` on `Module.finBasis` slots as a
    Kronecker delta.
- Once those helpers exist, the main theorem should reduce both sides to the
  same basis-component delta using `basisTensor0S_component`.

Failure signal:

- Stop if the proof exposes raw chart-derivative goals such as `fderivWithin`
  of chart inverses, or if the tangent helper cannot be obtained from
  `coordinateFrameAt_apply_of_mem` plus the trivialization inverse/forward
  identity.  That would mean the proof has dropped below the intended
  vector-bundle abstraction layer.

Verification:

- Not run in this consultation pass; no Lean source was edited in this step.

## 2026-05-14: `constInChart_basisTensor0S_coordFrame` attempt stopped

Learned:

- The direct fixed-trivialization route gets the theorem down to a single
  tangent-coordinate normalization after rewriting `Tensor0SSpace.constInChart`
  with `Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap`
  and comparing `coordinateFrameAt_basis x0 hx` with the tangent
  trivialization basis.
- This confirms the frontier is not mixed Ricci algebra and should not be
  pushed into `MixedComponents.lean` or lower finite-sum tensor algebra.

Failed:

- Verification failed. The remaining blocker was the raw chart-coordinate goal
  identifying the product of `Module.finBasis.repr` applied to the
  `fderivWithin` chart-coordinate expression with the product of
  `Module.finBasis.repr` applied to the tangent trivialization coordinate
  `(trivializationAt E (TangentSpace I) x0 ⟨x, v i⟩).2`.
- This is exactly the previous failure signal: the proof dropped below the
  intended vector-bundle abstraction layer into raw chart derivative
  normalization.

Next:

- Prove the tangent helper
  `coordinateFrameAt_basis_continuousLinearMapAt`: the fixed tangent
  trivialization coordinates of `(coordinateFrameAt_basis x0 hx) i` are
  `(Module.finBasis k E) i`.
- Then prove `constInChart_basisTensor0S_coordFrame` by `ext0S_basis` and
  `basisTensor0S_component`, without unfolding chart derivatives in the final
  mixed Ricci path.

Verification failed; the Lean source is restored to the intentional single
`sorry` frontier.

## 2026-05-14: `constInChart_basisTensor0S_coordFrame` closed

Worked:

- Added the local tangent normalization
  `coordinateFrameAt_basis_continuousLinearMapAt`, using
  `coordinateFrameAt_apply_of_mem`, `TangentBundle.symmL_trivializationAt`,
  and the forward/inverse trivialization identity.
- Added the arbitrary-vector coordinate helper
  `coordinateFrameAt_basis_repr_eq_trivializationAt` by expanding a tangent
  vector in the coordinate-frame basis and transporting the expansion through
  the tangent trivialization.
- Proved `constInChart_basisTensor0S_coordFrame` by rewriting fixed-chart
  tensor `constInChart` through the multilinear-bundle trivialization and
  using the coordinate-frame `repr` helper.

Verification passed.

Remaining:

- The local 14.13 normalization `sorry` is discharged.  Further work should
  stay at the presentation or geometric-assembly layer, not in lower finite-sum
  tensor algebra.
