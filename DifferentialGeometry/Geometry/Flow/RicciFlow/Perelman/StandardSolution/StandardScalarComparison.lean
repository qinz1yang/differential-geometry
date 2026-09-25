import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureComparison
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false
noncomputable section
open Set Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_scalar_bound_of_standard_metric_close_on_opens
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ ε A : ℝ, 0 < ε ∧ 0 < A ∧
      ∀ (U : Opens E3) (g : SmoothRiemannianMetric (𝓡 3) U)
        (S : StandardSolution) (τ : ℝ), τ ∈ Icc 0 θ → ∀ x : U,
        (∀ j ≤ 2, metricDerivNorm j g ((S.val.metric τ).restrictOpen U)
          (metric.restrictOpen U) x ≤ ε) →
        |metricScalarAt g x| ≤ A := by
  obtain ⟨ε, P, hε, hP, hcurv⟩ :=
    exists_uniform_curvature_bound_of_standard_metric_close_on_opens θ hθ hθ1
  refine ⟨ε, 9 * P, hε, by positivity, ?_⟩
  intro U g S τ hτ x hclose
  have hscalar := scalar_abs_le_rm g x
  change |metricScalarAt g x| ≤ (Module.finrank ℝ E3 : ℝ) ^ 2 *
    Real.sqrt (normSq0S g x 4 (metricRm04 g x)) at hscalar
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
    show (3 : ℝ) ^ 2 = 9 by norm_num] at hscalar
  exact hscalar.trans (mul_le_mul_of_nonneg_left (hcurv U g S τ hτ x hclose) (by norm_num))

end DifferentialGeometry.PDE.RicciFlow.StandardCap
