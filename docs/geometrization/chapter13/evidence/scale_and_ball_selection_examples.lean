import DifferentialGeometry.Analysis.Calculus.FirstPositiveLevel
import DifferentialGeometry.Topology.MetricSpace.VariableRadiusCover
import DifferentialGeometry.Geometry.Metric.Approximation.ConeRadialExtension
import DifferentialGeometry.Geometry.Metric.Approximation.FixedTargetTransfer
import DifferentialGeometry.Geometry.Metric.Approximation.BoundedRescaling
import DifferentialGeometry.Geometry.Metric.Approximation.LowDimensionalModels
import Mathlib.Tactic

set_option autoImplicit false
open Set Metric Filter
open scoped Topology
open GC.MetricGeometry

namespace LocalCollapseExamples

theorem nonmonotone_profile_first_level :
    let f : ℝ → ℝ := fun r => if r ≤ 2 then (r - 1) ^ 2 else 1 / (r - 1)
    Real.firstPositiveLevel f (1 / 4) = 1 / 2 ∧
      f (3 / 2) = 1 / 4 ∧ f 5 = 1 / 4 ∧ f 1 < f 2 := by
  dsimp only
  let f : ℝ → ℝ := fun r => if r ≤ 2 then (r - 1) ^ 2 else 1 / (r - 1)
  have hleast : IsLeast {r : ℝ | 0 < r ∧ f r = 1 / 4} (1 / 2) := by
    refine ⟨by norm_num [f], ?_⟩
    intro r hr
    by_contra! h
    have hr2 : r ≤ 2 := by linarith
    have hf := hr.2
    simp only [f, ite_eq_left hr2] at hf
    nlinarith [sq_nonneg (r - 1 / 2)]
  exact ⟨hleast.csInf_eq, by norm_num [f], by norm_num [f], by norm_num [f]⟩

theorem closed_inner_boundary_is_needed :
    ({(1 / 10 : ℝ)} : Set ℝ) ⊆ ⋃ i ∈ ({0} : Set ℝ), ball i (5 * 1) ∧
      ¬ ({(1 / 10 : ℝ)} : Set ℝ) ⊆ ⋃ i ∈ ({0} : Set ℝ), ball i (1 / 10) := by
  norm_num [Set.singleton_subset_iff, Metric.mem_ball, Real.dist_eq]

theorem finite_selection_on_nonclosed_interval :
    ∃ I : Set ℝ, I ⊆ Ioo (0 : ℝ) 1 ∧ I.Finite ∧
      I.PairwiseDisjoint (fun p => ball p (1 : ℝ)) ∧
      ∀ p ∈ Ioo (0 : ℝ) 1, ∃ i ∈ I,
        (ball p (1 : ℝ) ∩ ball i 1).Nonempty ∧ (1 : ℝ) ≤ 2 * 1 ∧
        dist p i < 3 * 1 ∧ ball p 1 ⊆ ball i (5 * 1) :=
  exists_finite_disjoint_ball_selection
    (isCompact_Icc.totallyBounded.subset Ioo_subset_Icc_self) (fun _ => 1)
    (rmin := 1) (R := 1) (by norm_num) (fun _ _ => le_rfl) (fun _ _ => le_rfl)

theorem empty_center_selection :
    ∃ I : Set ℝ, I ⊆ ∅ ∧ I.Finite ∧ I.PairwiseDisjoint (fun p => ball p (1 : ℝ)) ∧
      ∀ p ∈ (∅ : Set ℝ), ∃ i ∈ I, (ball p (1 : ℝ) ∩ ball i 1).Nonempty ∧
        (1 : ℝ) ≤ 2 * 1 ∧ dist p i < 3 * 1 ∧ ball p 1 ⊆ ball i (5 * 1) :=
  exists_finite_disjoint_ball_selection totallyBounded_empty (fun _ => 1)
    (rmin := 1) (R := 1) (by norm_num) (fun _ _ => le_rfl) (fun _ _ => le_rfl)

theorem original_three_splitting_exclusion :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
      ∀ (Z : Type) [MetricSpace Z] (z : Z)
        (C : Type) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∀ e : ℝ, 0 < e →
        ∃ γ : unitInterval → C, Continuous γ ∧ γ 0 = x ∧ γ 1 = y ∧
          eVariationOn γ univ < ENNReal.ofReal (dist x y + e)) →
      dimH (univ : Set C) ≤ 2 →
      DifferentialGeometry.Geometry.Comparison.Toponogov.fourPointComparison 0 (univ : Set C) →
      ∀ (A : Type) [MetricSpace A] (a : A) (σ β : ℝ), σ ≤ η → β ≤ η →
        KleinerLottApprox z c σ →
        KleinerLottApprox z (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 3)), a)) β → False :=
  exists_no_higher_rank_splitting_parameter (by norm_num : 1 ≤ 2) (by norm_num : 2 < 3)

#print axioms nonmonotone_profile_first_level
#print axioms closed_inner_boundary_is_needed
#print axioms finite_selection_on_nonclosed_interval
#print axioms empty_center_selection
#print axioms original_three_splitting_exclusion

end LocalCollapseExamples
