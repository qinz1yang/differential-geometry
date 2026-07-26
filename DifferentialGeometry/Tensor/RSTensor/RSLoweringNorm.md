# RSLoweringNorm.lean — the metric index-lowering fiber-norm isometry (G1)

## Status: COMPLETE, sorry-free, persisted (build green, no warnings)

`normSqRS_eq_normSq0S_lowerAllSpace` :
`normSqRS g x r s A = normSq0S g x (r+s) (lowerAllSpace g r s x A)`
(taking a `gRef`-ON basis at `x` via `hinv : MetricInverseInBasis_gen g x basis identityInvMetric`).

`lowerAllSpace g r s x A := Tensor0SSpace.ofModel (lowerAllUpperIndices g r s x (TensorRSSpace.toModel A))`
is the space-level all-upper-index metric lowering `(r,s) → (0,r+s)`.

This is the foundation of the LOWERING route for `ric_bound` Claim 1: it lets the proven
`(0,s)` analytic core (`iterCov_product_sqrtNormSq_le`) bound the `(1,2)` object `A_k` by
working on `lowerAll A_k`.

## Key findings (what made the proof tractable)

1. **`toModel`/`ofModel` are the IDENTITY** (`tensor0SSpace_continuousLinearEquiv_apply`/`_coe = rfl`/`id`;
   `tensorRSSpace_continuousLinearEquiv = arrowCongr id id`). So `lowerAllSpace A` evaluates as the bare
   model `lowerAllUpperIndices ... A` — NO fiber transport. This dissolved the feared "deep model-transport
   plumbing"; the final assembly closes by `rfl`.
2. **`hinv` for `identityInvMetric` gives the FORWARD Gram directly.** `MetricInverseInBasis_gen` is
   `∑ₖ gInv i k · Gₖⱼ = δᵢⱼ`; with `gInv = identityInvMetric = δ` (`= diagonalInvMetric (fun _ => 1)`) this
   collapses (`Finset.sum_eq_single` + `identityInvMetric_apply_self` + `diagonalInvMetric_eq_zero_of_ne`) to
   `g.inner x (basis i)(basis j) = δᵢⱼ`. No extra ON hypothesis needed.
3. **`exists_gOrthonormalBasis`** (`Geometry/Curvature/RicciOperatorNormBound.lean:38`) supplies a `gRef`-ON
   basis at ANY `x` with forward Gram `= δ` (via `stdOrthonormalBasis` on the metric's inner-product core).
   So the basis-parametrised isometry can be applied at any point (and could be made basis-free later).

## Proof skeleton
- `normSqRS_identity_eq_componentL2SqRS` (LHS = `∑_{up,low} componentRS²`) +
  `normSq0S_identity_eq_sum_sq` (RHS = `∑_slots component0S²`).
- Index bijection `slots ↔ (up,low)` via `Fin.append` (`Fintype.sum_equiv` + `Fintype.sum_prod_type`,
  `Fin.append_left`/`_right`).
- Per-term component match: `componentRS_apply_gen` (= `A (basisTensor up) (basis∘low)`) vs
  `lowerAllUpperIndices_apply` (= `A (separableFormAt g x r (basis∘up)) (basis∘low)`); then the ON-basis
  sublemma `separableFormAt g x r (basis∘up) = basisTensor0S basis up` (`ext0S_basis` +
  `basisTensor0S_component = δ` + `separableFormAt_apply = ∏ g.inner` + forward Gram = δ).

## Pitfalls
- `separableFormAt_apply`/`component0S_apply` did NOT fire by `rw`/`simp only` on the `Tensor0SSpace`-coerced
  application (coe vs CMM-coe). Fix: `change` to the `∏ g.inner` form (it is DEFEQ via the `separableFormAt`
  def chain `compContinuousLinearMap`→`mkPiAlgebra`→`∏`). The `change` (not `show`) avoids a linter warning.
- file-level `set_option maxHeartbeats` is linted; not needed here (default heartbeats suffice). Keep only
  `synthInstance.maxHeartbeats`.

## Namespace/header
In `namespace DifferentialGeometry.Integral.Connection` with `open ... Tensor0SBundle` +
`open DifferentialGeometry.Integral.L2` (for `lowerAllUpperIndices`) + `TensorMetricLowering Tensor0SNabla
TensorRSNabla`; variable block mirrors `TensorLoweringParallel.lean` (InnerProductSpace + CompleteSpace +
NeZero finrank + IsManifold ∞ + SigmaCompact + T2 + Boundaryless).

## CORRECTION — "∇-commutes-lowering" is NOT a frontier; it is already proven in the component layer
I initially scoped this (call it G2) as an abstract section-level theorem (generalise the rank-0
`loweredCovDerivAt_eq_lower_tensorCovDerivAt` in `TensorLoweringParallel.lean` to r ≥ 1, needing
"`separableFormAt` is ∇-parallel"). **That was the wrong representation.** In the component/realizer
layer the fact is already done:
- `nabla_metricPow_zero` (`Tensor/RSTensor/ContractionLeibniz.lean:428`) — `∇(g^{⊗r}) = 0`;
- `nabla0SFun_metricPow_contraction_eval` (`:480`) — `∇(A ⊗ g^{⊗r})` passes the metric factor untouched.
These are in the SAME `TotalNabla0SRealizes` framework as `iterCov`, so they compose directly with the
proven `(0,s)` m-fold core. Do NOT build the abstract `loweredCovDerivAt` generalisation. (See
`important_lesson.md` → "∇ commutes with the metric is a component fact".)

## Role of this file (G1) in the stable Claim-1 route (ii)
G1 (this isometry) is the `|A| = |lowerAll A|` bridge. Stable route (ii) for `ric_bound` Claim 1
`|∇^m A_k| ≤ C_m(1+|∇^{m+1}g_k|)`: lower `A_k`(1,2)→`Ǎ_k`(0,3); `|∇^m A_k| = |lowerAll ∇^m A_k|` (G1) and
`∇^m` passes the metric factor (`nabla0SFun_metricPow_contraction_eval`) → reduces to the `(0,s)` m-fold
(`iterCov_product_sqrtNormSq_le`, proven) on `Ǎ_k`; base relation `∇g_k = A_k∗g_k` = `connDiffCompEq`
(eq 3.7); then invert `|g_k⁻¹|≤C` + (A_N)/(B_N) double induction. All hard pieces proven; only the
assembly remains. (Whether G1's exact equality or the existing `metricGammaEquiv` 3/2-bound is used in the
final assembly is a wiring detail.)
