# NablaOnTensors.lean notes

## 2026-05-11 smooth wrappers and mixed coordinate attempt

Worked:

- Added the post-regularity convenience wrappers `nabla0S_smooth` and
  `nablaRS_smooth` in `NablaOnTensors/Smooth.lean`.
- Updated `NablaOnTensors/Raw.lean` so downstream imports of the raw API also
  see the smooth bundled wrappers.
- Verified `+DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Smooth` and
  `+DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Raw`.

Blocked:

- The planned mixed coordinate component API needs the model formula
  `covariantDeriv_tensorRSModelAt_apply_basis_slots`.
- A direct proof attempt in `Model/Christoffel.lean` got stuck on the finite
  coordinate lemma for the upper/Hom input correction:
  `lieDeriv_correctionL r Î“X (continuousMultilinearMapBasis basis r upper)`.
  The lower/output correction is the existing `(0,s)` formula, but the upper
  correction needs a clean reusable statement saying the covariant tensor basis
  transforms by
  `sum a k, Î“^upper[a]_k * basis (upper[a := k])`.
- The broken partial proof was removed; no coordinate/Ricci-flow file was
  changed in this pass.

## 2026-05-11 `nablaRS_reg` closed by local `(0,r)` regularity

Worked:

- Proved the local `(0,r)` raw derivation theorem
  `localCovariantDerivTensor0SAt_eval_moving_raw`.
- Proved the fixed-trivialization constant-input scalar smoothness helper
  `localCovariantDerivTensor0SAt_constInChart_eval_tangentConstInChart_contMDiffAt`.
- Proved the section-level local input-correction helper
  `localCovariantDerivTensor0SAt_constInChart_contMDiffAt` by reconstructing
  from `continuousMultilinearMap_basis` coordinates.
- Used these helpers in `nablaRS_reg`; the final Hom coordinate proof now
  follows the self-chart mixed derivation formula, with the input correction
  handled by the new local `(0,r)` regularity helper and output corrections by
  tangent-constant vector-field connection smoothness.

Verified:

- Verification result recorded without command details.
- Verification result recorded without command details.
- Scan shows `nablaRS_reg` has no `sorry`; the only remaining `sorry` in the
  `NablaOnTensors` folder is the pre-existing tangent-constant connection
  frontier in `Connection.lean`.

Reflection:

- The successful route stayed on the local-section path.  No arbitrary
  connection-coordinate chart-change theorem was introduced, and
  `fixedChartNablaRSModel` was not revived.
- The key missing layer was exactly the local version of `(0,s)` regularity for
  `localCovariantDerivTensor0SAt`, not another mixed-tensor coordinate theorem.

## 2026-05-11 mixed RS route correction

Worked:

- Removed the mixed fixed-chart RS route.  The fixed-chart model expression was
  the wrong analytic core for `nablaRS_reg` because it compared raw
  `nablaRSFun` to a model centered at `xâ‚€`, reintroducing the moving-center
  connection-coordinate problem.
- Kept the useful Hom-coordinate layer in `Tensor.RSTensor.Basis`.
- `nablaRS_reg` now reduces through explicit Hom coordinates and the
  fixed-trivialization evaluation theorem to one intrinsic scalar smoothness
  goal:

```lean
(nablaRSFun r s cov X T p)
  (Tensor0SSpace.constInChart r xâ‚€ Î²Ï p)
  (fun a => (trivializationAt E (TangentSpace I) xâ‚€).symmL ð•œ p (vÏƒ a))
```

Remaining:

- The remaining proof is the local moving-section derivation theorem for
  `nablaRSFun`.  If proving that theorem again forces a comparison between
  pointwise `tensorRSSpace_continuousLinearEquiv` and a fixed trivialization,
  the raw RS definition likely needs to be aligned with the `(0,s)` fixed
  trivialization style before regularity can close cleanly.

## 2026-05-11 RS alignment with `(0,s)`

Worked:

- Added mixed fixed-trivialization representatives
  `tensorRSModelAt`, `tensorRSModelAt_trivializationAt_symm`, and
  `tensorRSModelInChart`.
- Updated `mcovariantDeriv_tensorRSWithin` so the raw RS definition uses
  `tensorRSModelInChart` and returns through the mixed tensor-bundle
  trivialization at the center, matching the `(0,s)` route.
- Proved the centered scalar derivative bridge
  `fderivWithin_tensorRS_eval_modelSlots_center_eq_extDerivFun`.
  This removes the old pointwise-equivalence mismatch for the self-chart
  derivative calculation.

Remaining:

- `nablaRS_reg` still has one explicit scalar smoothness `sorry`.
- The next proof should use the aligned self-chart mixed derivation theorem to
  prove smoothness of the intrinsic Hom coordinate in `Regularity.lean`.

## 2026-05-11 local Hom derivation reflection

Worked:

- Proved the local self-chart Hom derivation theorem
  `nablaRSFun_eval_moving_raw`.
- This confirms the route is mathematically coherent at the pointwise level:
  raw `nablaRSFun` evaluated on a local input tensor and local output vector
  fields equals the scalar directional derivative minus the input correction
  and output-slot corrections.
- The proof used the aligned RS model representative and did not fall back to
  fixed-chart RS naturality.

Remaining:

- The final `nablaRS_reg` smoothness proof now needs one more local regularity
  theorem: smoothness of
  `localCovariantDerivTensor0SAt` for fixed-chart constant `(0,r)` input
  sections, plus smooth evaluation of `T` on that input correction and the
  fixed tangent slots.
- This is the honest next frontier; it is smaller than the old moving-center
  problem but still not a one-line closure.

## 2026-05-11 `(0,s)` regularity cleanup

Worked:

- Split the public raw API one layer further:
  - `NablaOnTensors/RawDefs.lean` now owns `nabla0SFun`, `nablaRSFun`,
    `Nabla0SRegular`, `NablaRSRegular`, `nabla0S`, and `nablaRS`.
  - `NablaOnTensors/Regularity.lean` owns the regularity proofs.
  - `NablaOnTensors/Raw.lean` is now a compatibility import of `Regularity`.
- Moved the reusable `(0,s)` moving-slot derivation and local-frame coefficient
  route into the tensor layer.
- Closed `Tensor0SBundle.nabla0S_reg` for `âˆž`-smooth bundled output by evaluating
  `nabla0SFun` on the tangent frame from `trivializationAt E (TangentSpace I) xâ‚€`
  and reconstructing with `contMDiff_multilinearSection_iff_coord`.
- Removed the old dependency of `nabla0S_reg` on
  `nabla0SFun_fixedChart_eventuallyEq`; that fixed-chart theorem and the
  consumer `nabla0S_reg_of_fixedChart_eventuallyEq` are gone.
- `Coordinates/NablaComponents/Tensor0S.lean` now delegates its final
  `nabla0SFun_contMDiff` theorem to `Tensor0SBundle.nabla0S_reg`.

Important adjustment:

- The closed regularity target is `âˆž`, not the stronger `âŠ¤` target. The
  available smooth multilinear evaluation and scalar directional derivative
  APIs are currently stated at `âˆž`; proving the former `âŠ¤` target would require
  generalizing those foundational smooth-evaluation lemmas first.

Remaining:

- `nablaRS_reg` is still the explicit mixed `(r,s)` frontier.
- `Connection.lean` still has the pre-existing `tangentConst_cov_mdiffAt` sorry.

## Regularity statement correction

The previous end-of-file theorem fronts
`nabla0S_reg` and `nablaRS_reg` were mathematically too strong: they claimed
smoothness of the induced tensor covariant derivative from an arbitrary raw
`CovariantDerivative`.

Mathlib's `CovariantDerivative` structure is total and algebraic on raw
sections.  It does not by itself assert that the connection coefficients vary
smoothly in local charts.  Over a generic scalar field, the global-section
predicate is not enough to recover local chart-constant section smoothness
without a local-to-global extension theorem.  The corrected regularity theorem
therefore uses the local predicate
`CovariantDerivative.ContMDiffCovariantDerivativeLocally cov âˆž`.

## What changed

- Added `CovariantDerivative.ContMDiffCovariantDerivativeLocally`.
- Replaced the smooth-connection hypotheses of `nabla0S_reg` and
  `nablaRS_reg` by the local predicate.
- Kept the existing explicit `Nabla0SRegular` and `NablaRSRegular` predicates:
  these remain the bundled-section smoothness targets.

## Remaining proof frontier

Both regularity theorems are still the analytic bridge:
trivialize the tensor bundle, unfold `nabla0SFun` / `nablaRSFun`, use the
chart formula for `mcovariantDeriv_*FromConnection`, and combine
the local smooth-connection predicate with the model-space derivative and slot
correction smoothness lemmas.

## 2026-05-09 progress

The fixed model-space calculus part is now proved in Lean:

- `contDiffWithinAt_covariantDeriv_tensor0SModelWithin`
- `contDiffWithinAt_covariantDeriv_tensorRSModelWithin`

These lemmas prove the smoothness of
`DÎ±(X) - C(Î“X) Î±` and `DT(X) - C_s(Î“X) âˆ˜ T + T âˆ˜ C_r(Î“X)` on a fixed model
set, assuming smoothness of the tensor components, the model vector field, and
the supplied model connection endomorphism.

## Current obstruction

The remaining `nabla0S_reg` / `nablaRS_reg` goals are not reachable by the
model lemmas alone.  The current `nabla0SFun` and `nablaRSFun` definitions
compute pointwise using a chart/trivialization centered at the output point.
Regularity of a section, however, reduces through `contMDiffAt_section` to a
fixed trivialization centered at a chosen base point `xâ‚€`.

So the missing bridge identified at that point was a fixed-chart representation
theorem plus smoothness of the extracted connection:

1. near `xâ‚€`, rewrite the moving-center definition of `nabla*Fun x` in the
   fixed tensor-bundle trivialization at `xâ‚€`;
2. prove the extracted `connectionEndomorphismInChart cov X xâ‚€` is smooth in
   that fixed chart.

The second item is now discharged by the local smooth-connection predicate
described below; the first item remains open.

## 2026-05-10 fixed-trivialization abstraction

The repeated section-smoothness recentering pattern is now packaged in
`DifferentialGeometry.VectorBundle.Section`:

- `contMDiffAt_section_of_trivializationAt_eventuallyEq`
- `contMDiffAt_section_of_chart_model_eventuallyEq`

Both wrappers checked.  They let a future `nabla0S_reg` / `nablaRS_reg` proof
reduce a section smoothness goal to:

1. a fixed trivialization or fixed `extChartAt` model smoothness theorem;
2. an eventual equality between that model expression and the actual section
   coordinates.

This removes the boilerplate `contMDiffAt_section` plus `congr_of_eventuallyEq`
step from the tensor-nabla proof.

## 2026-05-10 local smooth-connection progress

The local smooth-connection route now proves the fixed-chart smoothness of the
extracted connection endomorphism

```lean
connectionEndomorphismInChart cov X xâ‚€ : E â†’ E â†’L[ð•œ] E
```

from the local predicate.  The checked lemmas are:

```lean
tangentConstInChart_contMDiffOn_baseSet
covariantDerivative_tangentConst_apply_contMDiffOn_baseSet
connectionEndomorphismInChart_apply_contDiffWithinAt
connectionEndomorphismInChart_contDiffWithinAt
```

The last lemma uses the finite-dimensional calculus bridge
`contDiffWithinAt_clm_of_apply`, which packages pointwise smoothness after
applying a CLM-valued function to every fixed vector into smoothness of the
CLM-valued function itself.

## 2026-05-10 remaining obstruction

The remaining `nabla0S_reg` and `nablaRS_reg` sorries are now isolated to the
fixed-chart naturality/equality bridge:

1. reduce section smoothness at `xâ‚€` through the fixed tensor-bundle
   trivialization at `xâ‚€`;
2. unfold `nabla0SFun` / `nablaRSFun`, which currently compute pointwise using
   a chart/trivialization centered at the output point `x`;
3. prove that near `xâ‚€`, those moving-center values agree in the fixed
   trivialization with the fixed-chart model expression
   `mcovariantDeriv_tensor*WithinFromConnection`.

This is a geometric/vector-bundle naturality theorem, not a smoothness-of-Î“
problem anymore.  Once that eventual equality is available, the existing
fixed-trivialization wrappers in `DifferentialGeometry.VectorBundle.Section`, the model
smoothness lemmas, and `connectionEndomorphismInChart_contDiffWithinAt` should
assemble the two regularity proofs.
## 2026-05-10 fixed-chart model helper

Added the private `(0,s)` fixed-chart model expression
`fixedChartNabla0SModel` and proved
`fixedChartNabla0SModel_contDiffWithinAt`.  This proof combines:

- `tensor0SModelInChart_contMDiffWithinAt` for the fixed tensor components;
- `VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm` plus the
  model tangent-bundle trivialization to get smoothness of the pulled-back
  model vector field;
- `connectionEndomorphismInChart_contDiffWithinAt` for the extracted
  connection coefficients;
- `contDiffWithinAt_covariantDeriv_tensor0SModelWithin` for the model formula.

The proof requires the expected derivative-loss hypothesis
`n + 1 <= n`; downstream `nabla0S_reg` will use it at `n = infinity`.

## 2026-05-10 naturality attempt

Tried the planned `(0,s)` eventual equality
`nabla0SFun_fixedChart_eventuallyEq`.  Unfolding reduces the goal to:

```lean
((trivializationAt ... x0)
  <x, ((trivializationAt ... x).symm x
    (covariantDeriv_tensor0SModelWithin ... centered_at_x ...))>).2
=
covariantDeriv_tensor0SModelWithin ... centered_at_x0 ... (extChartAt I x0 x)
```

The direct round-trip lemma `Bundle.Trivialization.apply_mk_symm` does not
apply because the inner and outer tensor-bundle trivializations are centered at
different points.  Rewriting through `coordChange_apply_snd` exposes the right
shape but then the remaining theorem is exactly the missing chart-change
naturality of `covariantDeriv_tensor0SModelWithin`: the tensor-bundle
coordinate change must transport the moving-center model derivative to the
fixed-center model derivative.

That naturality theorem is broader than a local rewrite and should be planned
as a reusable tensor-bundle chart-change theorem before trying to close
`nabla0S_reg` / `nablaRS_reg`.

## 2026-05-10 specialized naturality frontier

The fixed-chart model helper is now public because the useful frontier needs to
name it directly:

```lean
fixedChartNabla0SModel
fixedChartNabla0SModel_contDiffWithinAt
```

The broad arbitrary-`Î“` chart-change theorem is intentionally not stated.  It
would be false unless the two model connection coefficients satisfy the
inhomogeneous connection coordinate-change law.

The separate fixed-chart naturality predicate was removed.  The file now states
the direct eventual-equality theorem:

```lean
nabla0SFun_fixedChart_eventuallyEq
```

`nabla0SFun_fixedChart_eventuallyEq` is still the remaining `(0,s)`
structural gap. It now follows the intended slot-evaluation shape directly:
work near `x0`, ext the fixed-chart model tensor on arbitrary model slots, and
rewrite the moving side with `tensor0SModelAt_apply`.

The consumer theorem

```lean
nabla0S_reg_of_fixedChart_eventuallyEq
```

assembles fixed-chart model smoothness plus the direct eventual equality into
`Nabla0SRegular`.  The public `nabla0S_reg` now routes through this consumer.

## 2026-05-10 slot-evaluation attempt

Worked:

- Added arbitrary-slot model formulas:
  `covariantDeriv_tensor0SModelAt_apply_slots` and
  `covariantDeriv_tensor0SModelWithin_apply_slots`.
- Added the pure model variable-slot product rule
  `fderivWithin_tensor0SModel_eval_linear_slots`. This proves the calculus
  identity for a model `(0,s)` tensor evaluated on variable slots represented
  by continuous linear maps from `ð•œ`, using mathlib's
  `fderivWithin_continuousMultilinearMapCompContinuousLinearMap`.
- Added fixed-chart tensor evaluation helpers:
  `tensor0SModelAt_apply` and `tensor0SModelInChart_apply`.
- Added fixed-chart covariant-derivative evaluation helpers:
  `fixedChartNabla0SModel_apply_slots` and
  `fixedChartNabla0SModel_apply_slots_of_mem`.
- Added the arbitrary-slot transported chart formula
  `mcovariantDeriv_tensor0SWithin_apply_slots`.
- Added the self-chart checkpoint
  `nabla0SFun_apply_selfChart_slots`: when the evaluation slots are constant in
  the same chart centered at the output point, `nabla0SFun` agrees with
  `fixedChartNabla0SModel` directly.

Failed / remaining:

- The direct proof of `nabla0SFun_fixedChart_eventuallyEq` reduces to the
  missing moving-slot derivation theorem for `nabla0SFun`:

  ```lean
  (nabla0SFun s cov X Î± x)
    (fun a => tangentConstInChart x0 (slots a) x)
  =
  -- directional derivative of the scalar tensor evaluation
  -- minus the connection corrections in each moving slot
  ```

- Unfolding `nabla0SFun` at that point immediately returns to the
  moving-center chart at `x`, while the target expression is written in the
  fixed chart at `x0`.  That is the stop signal from the plan: the next theorem
  should be a genuine tensor derivation formula for `nabla0SFun`, not an
  arbitrary-`Î“` chart-change theorem.
- The model product rule alone is not enough to close this.  The remaining
  geometric bridge is the vector/tensor derivation theorem connecting the raw
  bundle-level `nabla0SFun` definition to the scalar rule
  `X(Î±(V_i)) - Î£ Î±(..., âˆ‡_X V_i, ...)`.
- The self-chart lemma shows the raw definition is coherent at its own center;
  the unresolved step is specifically transporting slot constancy from the
  moving center `x` to a separate fixed center `x0`.

## 2026-05-10 warning cleanup

- Worked: removed the easy linter warnings by replacing an unnecessary `simpa`
  with `simp` and by locally disabling `unusedSectionVars` on four tiny simp
  wrapper theorems whose public context is intentionally inherited.
- Failed: direct `omit` attempts for the top-manifold instances did not match
  the scoped variables even though the linter printed them in schematic form.
  A local `set_option linter.unusedSectionVars false in` preserved the theorem
  shapes without fighting that binder elaboration.
- Remaining risk: the final `+DifferentialGeometry` build still reports the two existing
  `sorry` frontiers in this file, at the direct fixed-chart eventual equality
  and mixed-tensor regularity endpoints.

## 2026-05-10 vector-field chart formula progress

Worked:

- Added `tangentFieldModelInChart`, the fixed tangent-trivialization model
  representative of a tangent field.
- Proved fixed-chart constants really have constant model representatives:
  `tangentFieldModelInChart_tangentConstInChart_apply_of_mem`.
- Proved the finite-basis local expansion of any tangent field in a fixed
  tangent chart:
  `tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem`, with the
  center-point wrapper `tangentField_eq_sum_modelCoord_tangentConst_eventually`.
- Added a private finite-sum helper for `CovariantDerivative` and proved the
  centered vector-field chart formula
  `covariantDerivative_modelInChart_center_eq_sum`.

This formula is the intended finite-basis/Leibniz calculation:

```lean
model_x0 ((cov V x0) (X x0))
=
sum_i extDerivFun (model coefficient i of V) x0 (X x0) â€¢ e_i
  + Gamma_X(model_x0 V)
```

Failed / remaining:

- This is still centered at the chart center.  Closing
  `nabla0SFun_fixedChart_eventuallyEq` also needs the same vector-field chart
  formula at arbitrary nearby `p âˆˆ (trivializationAt ... x0).baseSet`, stated
  in model coordinates as a `fderivWithin` formula at `y = extChartAt I x0 p`.
- The next precise bridge is:

```lean
extDerivFun (fun p => coord_i (tangentFieldModelInChart x0 V (extChartAt I x0 p)))
  p (X p)
=
fderivWithin ð•œ (fun y => coord_i (tangentFieldModelInChart x0 V y))
  (Set.range I) (extChartAt I x0 p)
  (mpullbackWithin ð“˜(ð•œ, E) I (extChartAt I x0).symm X (Set.range I)
    (extChartAt I x0 p))
```

That bridge is not arbitrary connection-coordinate naturality, but it is a
separate chart derivative conversion.  After it is available, the centered proof
should generalize to arbitrary chart points, and the tensor product-rule theorem
can use the existing model slot product rule to finish the fixed-chart equality.

## 2026-05-10 derivation-route correction

The previous recentering route was too low-level for the main mathematical
issue.  The smoothness of a vector-field covariant derivative is already
provided by mathlib's smooth-connection assumption:

```lean
CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply
```

This checked theorem says that if `cov` is a smooth tangent-bundle connection,
`X` is a `C^n` vector field, and `Y` is a `C^(n+1)` vector field, then

```lean
fun p => (cov Y p) (X p)
```

is a `C^n` tangent section.  Thus the remaining `nabla0S_reg` obstruction is
not vector-field regularity and not the tensoriality of the map
`v â†¦ âˆ‡_v Y`; that part is solved.

The actual remaining bridge is the induced tensor derivation rule tying the
raw model-defined `nabla0SFun` to the textbook formula

```text
(âˆ‡_X Î±)(Yâ‚,...,Y_s)
= X(Î±(Yâ‚,...,Y_s))
  - Î£_a Î±(Yâ‚,...,âˆ‡_X Y_a,...,Y_s).
```

Once that equality is available, smoothness should be proved from existing
bundle-evaluation smoothness plus the new vector-field regularity lemma,
rather than by continuing to unfold moving-center trivializations.

## 2026-05-10 correction-term smoothness

Worked:

- Added the reusable bundle-evaluation wrapper
  `TensorMultilinear.contMDiff_tensor0SField_apply` in
  `DifferentialGeometry/Tensor/Multilinear/BundleSmoothEval.lean`.
- Proved
  `Tensor0SBundle.tensor0S_eval_covariantDerivative_slot_contMDiff`.

This closes the smoothness of each correction term in the tensor derivation
formula:

```text
p â†¦ Î±_p(Y_1(p), ..., (âˆ‡_X Y_a)(p), ..., Y_s(p)).
```

The proof uses two already-correct ingredients: smooth vector-field covariant
derivatives from `ContMDiffCovariantDerivative.contMDiff_apply`, and smooth
evaluation of a smooth `(0,s)` tensor field on smooth vector fields.

Remaining:

- The derivative term

```text
p â†¦ X(Î±(Y_1,...,Y_s))(p)
```

still needs a smoothness/derivation bridge.
- The central theorem still to build is the equality between `nabla0SFun` and
  the textbook derivation formula.  After that, `nabla0S_reg` can be assembled
  from the derivative-term smoothness and the correction-term theorem above.

## 2026-05-10 why `nabla0S_reg` is not closed yet

Attempt:

- Tried to replace the current proof of `nabla0S_reg`, which routes through
  `nabla0SFun_fixedChart_eventuallyEq`, by the new smoothness route:

```text
smooth vector-field covariant derivatives
+ smooth tensor evaluation
+ smooth scalar directional derivative
```

Result:

- The correction terms are now covered by
  `tensor0S_eval_covariantDerivative_slot_contMDiff`.
- This is not enough to prove `Nabla0SRegular` directly, because
  `Nabla0SRegular` is smoothness of the bundled tensor section

```lean
fun x => âŸ¨x, nabla0SFun s cov X Î± xâŸ©
```

  in the tensor-bundle topology.

Exact remaining Lean goal in the current fixed-chart proof:

```lean
tensor0SModelAt s xâ‚€ x (nabla0SFun s cov X Î± x) slots =
  fixedChartNabla0SModel s cov X Î± xâ‚€ (extChartAt I xâ‚€ x) slots
```

after `rw [tensor0SModelAt_apply]`.  This is precisely the missing
derivation-formula equality for `nabla0SFun` evaluated on fixed-chart slots.

Conclusion:

- We cannot honestly prove the current `nabla0S_reg` from correction-term
  smoothness alone.
- The next useful theorem is not another smoothness lemma; it is the equality

```text
(âˆ‡_X Î±)(Y_1,...,Y_s)
= X(Î±(Y_1,...,Y_s))
  - Î£_a Î±(Y_1,...,âˆ‡_X Y_a,...,Y_s).
```

  Once this derivation formula is proved for `nabla0SFun`, `nabla0S_reg` can
  be proved by local-frame coefficients from the derivative term and correction
  term smoothness.

## 2026-05-10 extraction refactor

The large `NablaOnTensors.lean` file has been split into focused layers while
preserving the public import path:

- `NablaOnTensors/Model.lean`: pure model-space tensor covariant derivative
  formulas, slot-evaluation lemmas, Christoffel/basis model formulas, and model
  smoothness lemmas.
- `NablaOnTensors/Connection.lean`: local smooth-connection predicate,
  smooth-connection application theorem, tangent-field chart model, and
  extracted connection endomorphism plus smoothness/apply lemmas.
- `NablaOnTensors/FixedChart.lean`: fixed-chart tensor representatives,
  fixed-chart apply lemmas, and fixed-chart model smoothness.
- `NablaOnTensors/Raw.lean`: raw `mcovariantDeriv_*` definitions,
  `nabla0SFun` / `nablaRSFun`, bundled APIs, and the two explicit regularity
  frontiers.
- `NablaOnTensors.lean`: compatibility wrapper importing `Raw`.

What succeeded:

- The mechanical extraction preserved theorem names and namespaces.
- Focused checks succeeded for `Model`, `Connection`, `FixedChart`, `Raw`, and
  the compatibility wrapper.
- The only Lean sorries in the split stack are still the intended frontiers:
  `nabla0SFun_fixedChart_eventuallyEq` and `nablaRS_reg`.

Remaining obstruction:

- The next non-refactor target is still the derivation formula for
  `nabla0SFun`.  The split makes the likely proof route clearer: model algebra
  in `Model`, vector-field/connection chart facts in `Connection`, fixed-chart
  representatives in `FixedChart`, and public assembly in `Raw`.

## 2026-05-10 attempt to close the two regularity sorries

Worked:

- Added and checked the pure model product rule
  `fderivWithin_tensor0SModel_eval_slots`, a wrapper around the existing
  linear-slot product rule for genuinely `E`-valued variable slots.
- Added and checked
  `covariantDerivative_modelInChart_eq_sum`, the non-centered finite-basis
  fixed-chart formula for `model(âˆ‡_X V)` at any point in the fixed
  trivialization domain.

Still blocked:

- These two lemmas are not yet enough to close
  `nabla0SFun_fixedChart_eventuallyEq`.
- The exact missing bridge is the scalar/model derivative comparison:

```lean
fderivWithin ð•œ
  (fun y => tensor0SModelInChart s xâ‚€ (fun x => Î± x) y slots)
  (Set.range I) (extChartAt I xâ‚€ p)
  (VectorField.mpullbackWithin ð“˜(ð•œ, E) I
    (extChartAt I xâ‚€).symm (fun x => X x) (Set.range I)
    (extChartAt I xâ‚€ p))
=
extDerivFun (I := I)
  (fun q => Î± q
    (fun a => tangentConstInChart (ð•œ := ð•œ) (I := I) xâ‚€ (slots a) q))
  p (X p)
```

Once this bridge is proved, `fixedChartNabla0SModel_apply_slots_of_mem` can be
rewritten to the intrinsic derivation expression. The analogous bridge at the
self-chart center is then the remaining input for the raw `nabla0SFun`
derivation theorem.

Stop reason:

- Continuing directly from `nabla0SFun_fixedChart_eventuallyEq` falls back to
  comparing moving-center and fixed-center tensor trivializations. That is the
  chart-change/naturality route the plan explicitly ruled out.
- The next safe implementation step is therefore the scalar/model derivative
  bridge above, not another attempt to unfold `nabla0SFun` inside the final
  theorem.

## 2026-05-11 mixed `(r,s)` regularity attempt

Worked:

- Lowered `NablaRSRegular` and the bundled `nablaRS` output from `âŠ¤` to `âˆž`,
  matching the accepted `(0,s)` regularity level.
- Added the pure model product rule
  `fderivWithin_tensorRSModel_eval_slots`, combining `fderivWithin_clm_apply`
  with the existing `(0,s)` variable-slot product rule. This is the right
  algebraic input for a local Hom-derivation proof.
- Rebuilt `RawDefs` and rechecked `Regularity`; the current stack still
  typechecks with one explicit `nablaRS_reg` proof frontier.

Remaining obstruction:

- The attempted generic local-frame proof reduces `nablaRS_reg` to smoothness
  of fixed-trivialization coordinates
  `(Module.finBasis ð•œ (TensorRSModel r s ð•œ E)).equivFunL (G p) i`, where
  `G p` is the fixed-trivialization representative of `nablaRSFun ... p`.
  This is still the fixed-chart representative problem in disguise.
- The next viable proof should replace the opaque generic `finBasis`
  coordinate with a Hom-basis coordinate: apply the mixed tensor to a fixed
  local `(0,r)` tensor-basis column and then evaluate the resulting `(0,s)`
  tensor on fixed tangent-frame slots.
- The missing lemma is the local Hom derivation formula, at coefficient level:
  `(âˆ‡_X T)(B) = âˆ‡_X(T B) - T(âˆ‡_X B)` for local `(0,r)` input sections `B`.
  It must be stated locally, not by packaging fixed-chart basis sections as
  global `Tensor0SField`s.

Stop reason:

- Filling the generic coordinate goal directly would re-enter the old
  moving-center versus fixed-center trivialization argument.
- The safe next step is a Hom-basis local coefficient theorem plus the local
  Hom derivation formula, using `fderivWithin_tensorRSModel_eval_slots` as the
  model-space algebraic core.

## 2026-05-11 Hom-basis frontier for mixed regularity

Worked:

- Added `continuousLinearMap_homBasis` and
  `continuousLinearMap_homBasis_repr` in `Model.lean`.  These give explicit
  coordinates on a finite-dimensional Hom space by applying a basis vector in
  the domain and reading a basis coordinate in the codomain.
- Added `tensorRSModel_basis` and `tensorRSModel_basis_repr`, specializing the
  Hom basis to
  `TensorRSModel r s ð•œ E = Tensor0SModel r ð•œ E â†’L[ð•œ] Tensor0SModel s ð•œ E`.
  The coordinate `(Ï, Ïƒ)` is now meaningful: input `(0,r)` basis tensor `Ï`,
  then output `(0,s)` basis-slot evaluation `Ïƒ`.
- Added `contMDiffAt_tensorRSModel_of_apply_basis_eval_basis` in
  `Regularity.lean`, replacing the opaque `Module.finBasis` coordinate route
  in `nablaRS_reg` with the Hom-basis criterion.
- Added `lieDeriv_correctionL_apply_slots` and
  `covariantDeriv_tensorRSModelWithin_eval_derivation` in `Model.lean`.  The
  latter is the pure model Hom-derivation formula:
  scalar derivative minus the covariant derivative of the input tensor and
  minus the covariant derivatives of the output slots.

Verified:

- Verification passed.
- Verification passed.
Remaining obstruction:

- The remaining `nablaRS_reg` hole is now the manifold-layer scalar coefficient
  bridge for the Hom-basis coordinate:

```lean
ContMDiffAt I ð“˜(ð•œ, ð•œ) âˆž
  (fun p =>
    (G p ((continuousMultilinearMap_basis bE r) Ï))
      (fun a => bE (Ïƒ a))) xâ‚€
```

- Proving this needs the local/fiber evaluation bridge from the fixed
  trivialization coordinate above to the intrinsic expression
  `(nablaRSFun ... p) (BÏ p) (VÏƒ p)`, followed by the raw mixed derivation rule
  `(âˆ‡_X T)(B) = âˆ‡_X(T B) - T(âˆ‡_X B)`.
- This should reuse the new model theorem
  `covariantDeriv_tensorRSModelWithin_eval_derivation`; it should not unfold
  unrelated chart transitions or package the fixed local basis columns as
  global fields.

## 2026-05-11 RS coordinate extraction and transition layer

Worked:

- Extracted the Hom-coordinate layer from `NablaOnTensors/Model.lean` into
  `DifferentialGeometry.Tensor.RSTensor.Basis`.
- Added `TensorRSSpace.trivializationAt_basis_coord`, translating fixed
  trivialization coordinates of `(r,s)` tensors into intrinsic application to a
  fixed-chart `(0,r)` input tensor and fixed-chart output tangent slots.
- Updated `nablaRS_reg` to use the extracted Hom-coordinate criterion and this
  transition theorem.

Verified:

- Verification passed.
- Verification passed.
Remaining obstruction:

- `nablaRS_reg` still has the single intentional scalar smoothness `sorry`.
  After the transition rewrite, the goal is smoothness of the intrinsic local
  Hom coordinate. The next proof should use the mixed Hom derivation rule, not
  a chart-change theorem or global extension of local basis sections.

## 2026-05-11 fixed-chart mixed model smoothness

Worked:

- Added the fixed-chart mixed tensor representatives:
  `tensorRSModelAt`, `tensorRSModelInChart`, and `fixedChartNablaRSModel`.
- Proved fixed-chart mixed model smoothness:
  `tensorRSModelInChart_contMDiffWithinAt`,
  `fixedChartNablaRSModel_contDiffWithinAt`, and the scalar Hom-coordinate
  smoothness helper `fixedChartNablaRSModel_basis_coord_contDiffWithinAt`.
- Updated `nablaRS_reg` so each Hom coordinate is compared against the smooth
  fixed-model scalar coordinate, after lowering the analytic/top inputs `X` and
  `T` to `âˆž` locally.

Blocked:

- The remaining equality is no longer a model-smoothness or coordinate-basis
  problem.  Restricting to the fixed tangent chart still leaves
  `mcovariantDeriv_tensorRSFromConnection` centered at the running point `p`
  on the left and `fixedChartNablaRSModel` centered at `xâ‚€` on the right.
- The smallest next theorem is a raw mixed derivation lemma in scalar
  Hom-coordinates, proving both sides equal the intrinsic derivation formula
  for `(âˆ‡_X T)(BÏ,VÏƒ)`.

## 2026-05-11 local Hom smoothness reflection

Worked:

- Kept the mixed regularity route aligned with the `(0,s)` local-section
  strategy, not the fixed-chart center-change strategy.
- Added local smoothness helpers in `NablaOnTensors/Regularity.lean`:
  `tensor0SConstInChart_contMDiffAt_of_mem`,
  `tensor0SConstInChart_contMDiffAt`,
  `tensor0SModelInChart_contDiffWithinAt_center_of_contMDiffAt`,
  `tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt`, and
  `tensorRS_eval_contMDiffAt`.
- Restored `nablaRS_reg` to a compile-clean Hom-coordinate skeleton. The
  fixed-trivialization Hom coordinate is rewritten to the intrinsic local
  expression using `TensorRSSpace.trivializationAt_basis_coord`.

Verified:

- Verification passed.
- Verification passed.
- The current scan shows no `fixedChartNablaRSModel`; the remaining sorries in
  this folder are `nablaRS_reg` and the pre-existing tangent-constant
  connection smoothness frontier in `Connection.lean`.

Current obstruction:

- The remaining `nablaRS_reg` hole is:

```lean
ContMDiffAt I ð“˜(ð•œ, ð•œ) âˆž
  (fun p =>
    (nablaRSFun r s cov X T p)
      (Tensor0SSpace.constInChart r xâ‚€ Î²Ï p)
      (fun a => eTan.symmL ð•œ p (vÏƒ a))) xâ‚€
```

- The model Hom derivation theorem already gives the right scalar identity.
  The term-by-term smoothness proof is blocked only at the input-correction
  section:

```lean
fun p =>
  localCovariantDerivTensor0SAt r cov X
    (Tensor0SSpace.constInChart r xâ‚€ Î²Ï) p
```

- This is a local `(0,r)` regularity theorem for a locally smooth tensor-input
  section. It should be proved by the same local-frame coefficient method as
  `nabla0S_reg`, but stated for local sections instead of global
  `Tensor0SField`s.

Reflection:

- The route remains mathematically feasible, but the missing theorem is not an
  RS-specific Hom-coordinate fact anymore. It is the local version of the
  already-proved `(0,s)` regularity result.
- Trying to prove the remaining scalar smoothness directly would either repeat
  the `(0,s)` local-frame proof inline or drift back into comparing chart
  centers. The next reusable helper should therefore be
  `localCovariantDerivTensor0SAt_contMDiffAt` or a coefficient-level version
  for locally smooth `(0,r)` input sections.

## 2026-05-11 NablaOnTensors extraction cleanup

Completed:

- Split the overgrown `NablaOnTensors` implementation into focused wrapper
  layers without changing the public import path
  `DifferentialGeometry.Tensor.RSTensor.NablaOnTensors`.
- `Model.lean` is now a wrapper for:
  `Model/Tensor0S.lean`, `Model/TensorRS.lean`,
  `Model/Christoffel.lean`, and `Model/Smoothness.lean`.
- `Connection.lean` is now a wrapper for:
  `Connection/Smooth.lean`, `Connection/Tangent.lean`, and
  `Connection/Endomorphism.lean`.
- `FixedChart.lean`, `RawDefs.lean`, and `Regularity.lean` are now wrappers
  over their respective proof-family submodules.
- During extraction, moved
  `TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet` into the tangent
  layer so `CovariantDerivative.tangentConst_cov_mdiffAt` no longer depends on
  the connection-endomorphism layer.

Verified:

- Targeted builds succeeded for all new `Model`, `Connection`, `FixedChart`,
  `RawDefs`, `Regularity`, `Raw`, `HigherOrder`, and top-level
  `NablaOnTensors` modules.
- `DifferentialGeometry.Coordinates.NablaComponents` builds through the compatibility
  wrapper.
- The scan
  returns no matches.

Consumer note:

- `DifferentialGeometry.LeviCivita.Curvature` does not currently build because it
  reaches pre-existing unsolved goals in `DifferentialGeometry.Realized.TensorRicciIdentity`.
  The NablaOnTensors-dependent prerequisites in that build completed before
  those unrelated goals.
