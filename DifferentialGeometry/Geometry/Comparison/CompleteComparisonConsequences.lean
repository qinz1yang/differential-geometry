import DifferentialGeometry.Geometry.Comparison.CompleteFourPointComparison
import DifferentialGeometry.Geometry.Comparison.PointOnSideModel

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem point_on_side_comparison_of_complete_local_comparison
    {X : Type*} [MetricSpace X] [CompleteSpace X] {κ : ℝ} (hκ : 0 ≤ κ)
    (hsegments : ∀ x y : X, ∃ σ : Icc (0 : ℝ) (dist x y) → X,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hlocal : ∀ z : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    {q u x z : X} (hparts : dist q x = dist q u + dist u x) :
    modelSideNegCurvature κ (dist q u) (dist q z)
      (comparisonAngleNegCurvature κ (dist q x) (dist q z) (dist x z)) ≤ dist u z :=
  modelSideNegCurvature_point_on_side_le_dist hκ
    (fourPointComparison_of_complete_local_comparison hκ hsegments hlocal)
    (mem_univ q) (mem_univ u) (mem_univ x) (mem_univ z) hparts

theorem independent_radial_monotonicity_of_complete_local_comparison
    {X : Type*} [MetricSpace X] [CompleteSpace X] {κ R S : ℝ} (hκ : 0 ≤ κ)
    (hsegments : ∀ x y : X, ∃ σ : Icc (0 : ℝ) (dist x y) → X,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hlocal : ∀ z : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    {p : X} {γ β : ℝ → X}
    (hγrad : ∀ s ∈ Ioc (0 : ℝ) R, dist p (γ s) = s)
    (hβrad : ∀ t ∈ Ioc (0 : ℝ) S, dist p (β t) = t)
    (hγmin : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
      dist (γ s) (γ t) = |s - t|)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (β s) (β t) = |s - t|) :
    DifferentialGeometry.Toponogov.CoordinatewiseNonincreasingOn R S
      (fun s t => comparisonAngleNegCurvature κ s t (dist (γ s) (β t))) :=
  comparisonAngleNegCurvature_antitone_on_segments hκ
    (fourPointComparison_of_complete_local_comparison hκ hsegments hlocal)
    (mem_univ p) hγrad hβrad hγmin hβmin (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)

end DifferentialGeometry.Geometry.Comparison.Toponogov
