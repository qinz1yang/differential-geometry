import DifferentialGeometry.Geometry.Metric.CompactDerivative
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients

noncomputable section
open Manifold Set
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem norm_sq_le_pullbackMetricCoefficients_of_fixed_derivative
    (g : SmoothRiemannianMetric I M) {Φ : M → F} {r : F → M} {y : F}
    (hΦ : MDifferentiableAt I 𝓘(ℝ, F) Φ (r y))
    (hr : MDifferentiableAt 𝓘(ℝ, F) I r y) {C : ℝ≥0}
    (hC : ∀ v : TangentSpace I (r y),
      ‖(mfderiv I 𝓘(ℝ, F) Φ (r y) v : F)‖ ≤ C * Real.sqrt (g.inner (r y) v v))
    {v : F} (hv : fderiv ℝ (Φ ∘ r) y v = v) :
    ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * pullbackMetricCoefficients g r y v v := by
  have hchain : fderiv ℝ (Φ ∘ r) y =
      (mfderiv I 𝓘(ℝ, F) Φ (r y)).comp (mfderiv 𝓘(ℝ, F) I r y) := by
    have h := mfderiv_comp y hΦ hr
    rw [mfderiv_eq_fderiv] at h
    apply ContinuousLinearMap.ext
    intro w
    have hw := congrArg (fun D => NormedSpace.fromTangentSpace (𝕜 := ℝ) (Φ (r y))
      (D ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm w))) h
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using! hw
  have hnorm := hC (mfderiv 𝓘(ℝ, F) I r y v)
  have heq : (mfderiv I 𝓘(ℝ, F) Φ (r y)) (mfderiv 𝓘(ℝ, F) I r y v) = v := by
    rw [hchain] at hv
    exact hv
  rw [heq] at hnorm
  have hs := pow_le_pow_left₀ (norm_nonneg v) hnorm 2
  simpa only [mul_pow, Real.sq_sqrt (metric_inner_self_nonneg g (r y) _),
    pullbackMetricCoefficients_apply] using hs

theorem exists_norm_sq_le_pullbackMetricCoefficients_of_fixed_derivative
    [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {Φ : M → F}
    (hΦ : ContMDiff I 𝓘(ℝ, F) 1 Φ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (r : F → M) (y : F),
      MDifferentiableAt 𝓘(ℝ, F) I r y → ∀ v : F,
      fderiv ℝ (Φ ∘ r) y v = v →
        ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * pullbackMetricCoefficients g r y v v := by
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound g hΦ
  refine ⟨B + 1, by positivity, ?_⟩
  intro r y hr v hv
  apply norm_sq_le_pullbackMetricCoefficients_of_fixed_derivative g
    (hΦ.mdifferentiableAt one_ne_zero) hr _ hv
  intro w
  exact (hB (r y) w).trans
    (mul_le_mul_of_nonneg_right (by simp) (Real.sqrt_nonneg _))

end DifferentialGeometry.Geometry

end
