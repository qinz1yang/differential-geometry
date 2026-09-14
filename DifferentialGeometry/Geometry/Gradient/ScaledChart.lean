import DifferentialGeometry.Geometry.Gradient.ScaledChartDifferential
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Operator.Gradient.Basic

noncomputable section

open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Gradient

variable {E F H H' M N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [TopologicalSpace H] [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem gradFun_scaled_chart_coordinate
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (f : M → ℝ) (c : ℝ) (hc : 0 < c) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    gradFun g (fun y ↦ (Real.sqrt c)⁻¹ * f (Φ.symm y)) (Φ x) =
      Real.sqrt c • mfderiv I J Φ x
        (gradFun (Diffeomorph.pullbackMetricCross (scaleMetric c hc g) Φ) f x) := by
  apply metricFlatLinear_injective g (Φ x)
  ext v
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  let e := Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have he (w : TangentSpace I x) : e w = mfderiv I J Φ x w := by
    exact congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) ↦ A w)
      (Φ.mfderivToContinuousLinearEquiv_coe (by decide))
  obtain ⟨w, hw⟩ := e.surjective ((Real.sqrt c)⁻¹ • v)
  have hv : v = Real.sqrt c • mfderiv I J Φ x w := by
    rw [← he, hw, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hc).ne', one_smul]
  rw [hv, inner_gradFun, Diffeomorph.inner_sqrt_smul_mfderiv g Φ c hc x, inner_gradFun]
  exact mvfderiv_scaled_chart_coordinate_of_mdifferentiableAt Φ f c hc x hf w

theorem sqrt_inner_sub_gradFun_scaled_chart
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (f : M → ℝ) (c : ℝ) (hc : 0 < c) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (w : TangentSpace I x) :
    let gC := Diffeomorph.pullbackMetricCross (scaleMetric c hc g) Φ
    let u := fun y ↦ (Real.sqrt c)⁻¹ * f (Φ.symm y)
    Real.sqrt (g.inner (Φ x)
      (Real.sqrt c • mfderiv I J Φ x w - gradFun g u (Φ x))
      (Real.sqrt c • mfderiv I J Φ x w - gradFun g u (Φ x))) =
        Real.sqrt (gC.inner x (w - gradFun gC f x) (w - gradFun gC f x)) := by
  dsimp only
  rw [gradFun_scaled_chart_coordinate g Φ f c hc x hf,
    ← smul_sub, ← map_sub, Diffeomorph.inner_sqrt_smul_mfderiv g Φ c hc x]

end DifferentialGeometry.Geometry.Gradient
