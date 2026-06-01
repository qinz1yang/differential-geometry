import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.NormComparison
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerCovDiagonalBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerPointwiseUpperBound

/-!
# Sum-over-directions bound on the chart-twist-inverted covariant derivative

For a closed Riemannian manifold `(M, g)` and a chart base point `α`, this
file controls the sum over directions of the squared Euclidean norm of the
inverse chart-`(α, b)`-twist applied to the model-fibre image of the
covariant derivative of a smooth compactly-supported `(r, s)`-tensor section
along the chart-`α` basis fibres. The bound's right-hand side is the
intrinsic pointwise gradient inner product
`tensorCovDerivPointwiseInner g r s S S b` of the section against itself.

## Strategy

Let `cov_i := tensorCovDerivAt g r s S b (chartBasisVecFiber α i b)`. For each
`i`, set `T_i := chartRSTwistInv α b r s (TensorRSSpace.toModel cov_i)`. The
chart-frame quadratic norm bound (Group A's primary headline) gives
`‖T_i‖^2 ≤ K * chartTensorInnerPointwise_rs_model g r s α b T_i T_i`. The
bridge identity rewrites the chart-frame diagonal value as a bundle-fibre
diagonal value on the chart-twisted tensor, and the round-trip
`chartRSTwist ∘ chartRSTwistInv = id` (valid on the chart base set) collapses
the twisted argument to `TensorRSSpace.toModel cov_i`. Summing over `i` and
chaining with `TensorInnerCovDiagonalBound` (the diagonal-sum bound for the
covariant-derivative inner product) yields the headline.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Per-direction chart-trivialisation norm bound on an arbitrary compact
subset of the chart base set.** For a compact set `K_M` contained in the
chart-`α` base set, every `b ∈ K_M`, and any model `(r, s)`-tensor `X`,
`‖chartRSTwistInv α b r s X‖^2 ≤ K * tensorInnerPointwise g r s b X X`. -/
theorem chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ K_M →
        ∀ X : TensorRSModel r s ℝ E,
          ‖chartRSTwistInv (I := I) (M := M) α b r s X‖ ^ 2 ≤
            K * tensorInnerPointwise (I := I) (M := M) g r s b X X := by
  classical
  obtain ⟨K, hK_nn, h_chart⟩ :=
    chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_compact
      (I := I) (M := M) (E := E) g r s α hK_M_compact hK_M_sub_baseSet
  refine ⟨K, hK_nn, ?_⟩
  intro b hb X
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    hK_M_sub_baseSet hb
  set T : TensorRSModel r s ℝ E :=
    chartRSTwistInv (I := I) (M := M) α b r s X with hT_def
  have h_T : ‖T‖ ^ 2 ≤ K *
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T :=
    h_chart b hb T
  have h_bridge :
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T =
        tensorInnerPointwise (I := I) (M := M) g r s b
          (chartRSTwist (I := I) (M := M) α b r s T)
          (chartRSTwist (I := I) (M := M) α b r s T) :=
    chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r s α hb_base T T
  have h_round : chartRSTwist (I := I) (M := M) α b r s T = X := by
    rw [hT_def]
    exact chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb_base r s X
  rw [h_bridge, h_round] at h_T
  exact h_T

/-- **Sum-over-directions bound on the chart-twist-inverted covariant
derivative on an arbitrary compact subset of the chart base set.** For a closed
Riemannian manifold `(M, g)`, a chart base point `α`, ranks `(r, s)`, and a
compact set `K_M` contained in the chart-`α` base set, there exists a
non-negative constant `C` such that for every smooth compactly-supported
`(r, s)`-tensor section `S` and every base point `b ∈ K_M`, the sum over `i`
of the squared Euclidean norm of
`chartRSTwistInv α b r s (TensorRSSpace.toModel (∇S(b)(e_i')))` is bounded
by `C` times the intrinsic gradient inner product
`tensorCovDerivPointwiseInner g r s S S b`, where
`e_i' = chartBasisVecFiber α i b` is the chart-`α` basis fibre at `b`.

The constant `C` decomposes as `K * C'`, where `K` is the chart-frame norm
comparison constant and `C'` is the diagonal-sum control constant from the
chart-Gram inverse Rayleigh-quotient lower bound. -/
theorem exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ K_M →
        ∑ i : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (chartBasisVecFiber (I := I) α i b)))‖ ^ 2 ≤
          C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
  classical
  obtain ⟨K, hK_nn, h_per⟩ :=
    chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact
      (I := I) (M := M) g r s α hK_M_compact hK_M_sub_baseSet
  obtain ⟨C', hC'_nn, h_diag⟩ :=
    exists_sum_tensorInnerPointwise_cov_chartBasis_diagonal_le_const_mul_tensorCovDerivPointwiseInner_on_compact
      (I := I) (M := M) g r s α hK_M_compact hK_M_sub_baseSet
  refine ⟨K * C', mul_nonneg hK_nn hC'_nn, ?_⟩
  intro S b hb
  set cov : Fin (Module.finrank ℝ E) → TensorRSModel r s ℝ E := fun i =>
    TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b)) with hcov_def
  set D : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g r s b (cov i) (cov i) with hD_def
  have h_D_le : D ≤ C' * tensorCovDerivPointwiseInner
      (I := I) (M := M) g r s S S b := by
    rw [hD_def]
    exact h_diag S hb
  have h_sum_le_KD :
      ∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s (cov i)‖ ^ 2 ≤
        K * D := by
    rw [hD_def, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    exact h_per hb (cov i)
  have h_KD_le : K * D ≤
      K * (C' * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b) :=
    mul_le_mul_of_nonneg_left h_D_le hK_nn
  have h_assoc :
      K * (C' * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b) =
        (K * C') *
          tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
    ring
  calc ∑ i : Fin (Module.finrank ℝ E),
        ‖chartRSTwistInv (I := I) (M := M) α b r s (cov i)‖ ^ 2
      ≤ K * D := h_sum_le_KD
    _ ≤ K * (C' * tensorCovDerivPointwiseInner
              (I := I) (M := M) g r s S S b) := h_KD_le
    _ = (K * C') *
          tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := h_assoc

/-- **Per-direction chart-trivialisation norm bound.** For `b` in the closed
support of the chart-atlas partition-of-unity weight at `α`, and any model
`(r, s)`-tensor `X`,
`‖chartRSTwistInv α b r s X‖^2 ≤ K * tensorInnerPointwise g r s b X X`.

This is the specialisation of
`chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact` to the
compact closed support of the chart-atlas partition-of-unity weight. -/
theorem chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∀ X : TensorRSModel r s ℝ E,
          ‖chartRSTwistInv (I := I) (M := M) α b r s X‖ ^ 2 ≤
            K * tensorInnerPointwise (I := I) (M := M) g r s b X X :=
  chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact
    (I := I) (M := M) g r s α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

/-- **Sum-over-directions bound on the chart-twist-inverted covariant
derivative.** For a closed Riemannian manifold `(M, g)`, a chart base point
`α`, and ranks `(r, s)`, there exists a non-negative constant `C` such that
for every smooth compactly-supported `(r, s)`-tensor section `S` and every
base point `b` in the closed support of the chart-atlas partition-of-unity
weight at `α`, the sum over `i` of the squared Euclidean norm of
`chartRSTwistInv α b r s (TensorRSSpace.toModel (∇S(b)(e_i')))` is bounded
by `C` times the intrinsic gradient inner product
`tensorCovDerivPointwiseInner g r s S S b`.

This is the specialisation of
`exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact`
to the compact closed support of the chart-atlas partition-of-unity weight. -/
theorem exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∑ i : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (chartBasisVecFiber (I := I) α i b)))‖ ^ 2 ≤
          C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b :=
  exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact
    (I := I) (M := M) g r s α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
