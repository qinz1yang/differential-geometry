import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardActionComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLower

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature

theorem exists_scalar_metric_comparison_of_standard_close (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1) :
    ∃ η Cup Lc : ℝ, 0 < η ∧ 0 < Cup ∧ 0 < Lc ∧
      ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)))
        (g : SmoothRiemannianMetric (𝓡 3) U), ∀ τ ∈ Icc 0 T, ∀ x : U,
        (∀ j : ℕ, j ≤ 2 → metricDerivNorm j g ((Q.val.metric τ).restrictOpen U)
          (StandardCap.metric.restrictOpen U) x ≤ η) →
        1 / 2 ≤ metricScalarAt g x ∧ metricScalarAt g x ≤ Cup ∧
        ∀ v : TangentSpace (𝓡 3) x,
          (StandardCap.metric.restrictOpen U).inner x v v ≤ Lc ^ 2 * g.inner x v v := by
  obtain ⟨η₁, hη₁, hlower⟩ := exists_uniform_standard_metric_scalar_lower_comparison T hT hT1
  obtain ⟨η₂, Cup, _, hη₂, hCup, _, hupper⟩ :=
    exists_uniform_standard_metric_scalar_upper_comparison T hT hT1
  have hTl : ENNReal.ofReal T < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr hT1
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab T hT hTl
  obtain ⟨Λ, hΛ, _, _, _, _, hmetric⟩ := standard_metric_bounds_on_shorter_windows T K hT hK
  refine ⟨min η₁ η₂, Cup, 2 * Λ, lt_min hη₁ hη₂, hCup, by linarith, ?_⟩
  intro Q U g τ hτ x hjets
  obtain ⟨hmet, hsc⟩ := hlower Q U g τ hτ x fun j hj => (hjets j hj).trans (min_le_left _ _)
  obtain ⟨hup, _⟩ := hupper Q U g τ hτ x fun j hj => (hjets j hj).trans (min_le_right _ _)
  have hdom : τ ∈ Q.val.domain :=
    (Icc_subset_lifetimeInterval_iff Q.val.lifetime Q.val.lifetime_pos T hT).mpr (hlife Q) hτ
  have hone : 1 ≤ metricScalarAt ((Q.val.metric τ).restrictOpen U) x := by
    rw [metricScalarAt_restrictOpen]
    exact Q.val.one_le_scalar τ hdom x.val
  refine ⟨by linarith, hup, ?_⟩
  intro v
  have hcap := ((hmetric Q.val T hT le_rfl (hlife Q) (hRm Q)).1 τ hτ).2 x.val (mem_univ _) v
  have hcap' : (StandardCap.metric.restrictOpen U).inner x v v ≤
      Λ * ((Q.val.metric τ).restrictOpen U).inner x v v := by
    have h1 := hcap.1
    simp only [SmoothRiemannianMetric.restrictOpen_inner] at h1 ⊢
    have hΛ0 : 0 < Λ := by linarith
    rw [inv_mul_le_iff₀ hΛ0] at h1
    exact h1
  have hn := metric_inner_self_nonneg ((Q.val.metric τ).restrictOpen U) x v
  have hm := hmet v
  have hcoef : 2 * Λ ≤ (2 * Λ) ^ 2 := by nlinarith
  have hgn : 0 ≤ g.inner x v v := by nlinarith
  calc (StandardCap.metric.restrictOpen U).inner x v v
      ≤ Λ * ((Q.val.metric τ).restrictOpen U).inner x v v := hcap'
    _ ≤ Λ * (2 * g.inner x v v) := by nlinarith
    _ = 2 * Λ * g.inner x v v := by ring
    _ ≤ (2 * Λ) ^ 2 * g.inner x v v := mul_le_mul_of_nonneg_right hcoef hgn

end DifferentialGeometry.PDE.RicciFlow
