import DifferentialGeometry.Geometry.Comparison.FiniteEuclideanComparison
import DifferentialGeometry.Geometry.Comparison.DenseEuclideanTangents
import DifferentialGeometry.Geometry.Comparison.CompleteFourPointComparison
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_finite_euclidean_comparison_of_local_comparison_zero_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ x y : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + ε))
    {n : ℕ} (hdim : dimH (univ : Set X) ≤ n)
    (hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 0 Ω ∧ p ∈ Ω) :
    ∃ m : ℕ, m ≤ n ∧ dimH (univ : Set X) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → dimH V = m) ∧
      ∀ (ι : Type*) [Finite ι], ∀ p : X, ∀ a : ι → X, ∃ v : ι → EuclideanSpace ℝ (Fin m),
        (∀ i, ‖v i‖ = dist p (a i)) ∧
        ∀ i j, dist (a i) (a j) ≤ dist (v i) (v j) := by
  have hlocalOne : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω := by
    intro p
    obtain ⟨Ω, hΩ, hc, hp⟩ := hlocal p
    exact ⟨Ω, hΩ, hc.of_zero (by norm_num), hp⟩
  let : ProperSpace X := properSpace_of_local_comparison_and_dimH hcurves
    (by norm_num : (0 : ℝ) ≤ 0) hdim hlocal
  have hsegments := exists_metric_segment_of_locallyCompact_of_arbitrarily_short_curves hcurves
  have hisosegments : ∀ x y : X, ∃ γ : Icc (0 : ℝ) (dist x y) → X,
      Isometry γ ∧ γ ⟨0, le_rfl, dist_nonneg⟩ = x ∧
        γ ⟨dist x y, dist_nonneg, le_rfl⟩ = y := by
    intro x y
    obtain ⟨f, _, hf0, hf1, hfd⟩ := hsegments x y
    exact exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
  have hcomp : fourPointComparison 0 (univ : Set X) :=
    fourPointComparison_of_complete_local_comparison (by norm_num) hisosegments hlocal
  obtain ⟨m, hmn, hglobal, hopen, S, _, hS, hregular⟩ :=
    exists_dense_euclidean_tangents_of_local_comparison_and_dimH hcurves hdim hlocalOne
  let : ∀ q : X, HasAnglesAt q := fun q => by
    obtain ⟨Ω, hΩ, hc, hq⟩ := hlocalOne q
    exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hc hq
  exact ⟨m, hmn, hglobal, hopen, fun ι _ p a =>
    exists_finite_euclidean_comparison_of_dense_tangent_isometries hcomp hisosegments
      hS hregular p a⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
