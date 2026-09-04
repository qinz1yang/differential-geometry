import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.CovariantTensorBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem lower_jet_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (Φ₀ : SmoothCcTensor g 2 2) (Φ₁ : SmoothCcTensor g 3 2)
          (U : SmoothCcTensor g 0 2) (A₀ A₁ : ℝ),
          0 ≤ A₀ → 0 ≤ A₁ →
          (∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g 2 2 j Φ₀‖ ^ 2) ≤ A₀ ^ 2 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 3 2 j Φ₁‖ ^ 2) ≤ A₁ ^ 2 →
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (operatorFieldApply (I := I) (M := M) g 2 2 Φ₀ U +
                operatorFieldApply (I := I) (M := M) g 3 2 Φ₁
                  (covGrad (I := I) (M := M) g 0 2 U))‖ ≤
            C * (A₀ + A₁) *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  obtain ⟨C₀, hC₀, hzero⟩ :=
    operatorFieldApplication_h1_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨C₁, hC₁, hone⟩ :=
    operatorFieldApplication_h2cov_uniform (I := I) (M := M) hDim gBase hΛ
  refine ⟨C₀ + C₁, add_nonneg hC₀ hC₁, ?_⟩
  intro g hEq hjet Φ₀ Φ₁ U A₀ A₁ hA₀ hA₁ hΦ₀ hΦ₁
  have hzero' := hzero g hEq hjet Φ₀ U A₀ hA₀ hΦ₀
  have hone' := hone g hEq hjet Φ₁ U A₁ hA₁ hΦ₁
  have hnorm : 0 ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := norm_nonneg _
  rw [ccTensorToHs_add]
  calc
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g 2 2 Φ₀ U)‖ +
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g 3 2 Φ₁
              (covGrad (I := I) (M := M) g 0 2 U))‖ := norm_add_le _ _
    _ ≤ C₀ * A₀ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        C₁ * A₁ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ :=
      add_le_add hzero' hone'
    _ ≤ C₀ * (A₀ + A₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        C₁ * (A₀ + A₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hC₀) hnorm
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hC₁) hnorm
    _ = (C₀ + C₁) * (A₀ + A₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
