import DifferentialGeometry.Geometry.Metric.Approximation.LowDimensionalModels
import DifferentialGeometry.Geometry.Collapse.RankStrata
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves

/-!
# Geodesic low-dimensional models and the uniform three-rank obstruction

LC17 and LC18 retain arbitrary metric sources and arbitrary transverse factors.
The rank application consumes actual approximation maps, without a curvature-volume producer.
-/

set_option autoImplicit false

open Set Metric Filter
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v w

theorem exists_common_pointed_limit_of_two_dimensional_geodesic_models
    {C : ℕ → Type u} [∀ i, MetricSpace (C i)] [∀ i, CompleteSpace (C i)]
    {Z : ℕ → Type v} [∀ i, MetricSpace (Z i)]
    (c : ∀ i, C i) (z : ∀ i, Z i)
    (hseg : ∀ i, ∀ x y : C i, ∃ γ : Icc (0 : ℝ) 1 → C i, Continuous γ ∧
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (γ s) (γ t) = dist x y * dist s t)
    (hdim : ∀ i, dimH (univ : Set (C i)) ≤ 2)
    (hcomp : ∀ i, fourPointComparison 0 (univ : Set (C i)))
    {σ : ℕ → ℝ} (f : ∀ i, KleinerLottApprox (z i) (c i) (σ i))
    (hσ : Tendsto σ atTop (𝓝 0)) :
    ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
      ∃ (q : Y) (a : ℕ → ℕ), StrictMono a ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => c (a i)) q ∧
        PointedGHConverges (fun i => z (a i)) q ∧
        dimH (univ : Set Y) ≤ 2 ∧ fourPointComparison 0 (univ : Set Y) ∧
        ∀ x y : Y, ∃ γ : Icc (0 : ℝ) 1 → Y, Continuous γ ∧
          γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (γ s) (γ t) = dist x y * dist s t := by
  exact exists_common_pointed_limit_of_nonnegative_models c z (by norm_num)
    (fun i => arbitrarily_short_curves_of_metric_segments (hseg i)) hdim hcomp f hσ

theorem exists_uniform_three_splitting_exclusion :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
      ∀ (Z : Type u) [MetricSpace Z] (z : Z)
        (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∃ γ : Icc (0 : ℝ) 1 → C, Continuous γ ∧
        γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (γ s) (γ t) = dist x y * dist s t) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ σ β : ℝ, σ ≤ η → β ≤ η → KleinerLottApprox z c σ →
        ¬ HasEuclideanSplitting.{u, w} z 3 β := by
  obtain ⟨η, hη, hηsmall, hex⟩ :=
    exists_no_higher_rank_splitting_parameter.{u, v, w} (n := 2) (k := 3)
      (by norm_num) (by norm_num)
  refine ⟨η, hη, hηsmall, ?_⟩
  intro Z mZ z C mC hc c hseg hdim hcomp σ β hσ hβ f hs
  obtain ⟨Y, mY, y, ⟨g⟩⟩ := hs
  let := mY
  exact hex Z z C c (arbitrarily_short_curves_of_metric_segments hseg)
    hdim hcomp Y y σ β hσ hβ f g

theorem exists_uniform_rank_bound_of_model :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
      ∀ (Z : Type u) [MetricSpace Z] (z : Z)
        (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∃ γ : Icc (0 : ℝ) 1 → C, Continuous γ ∧
        γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (γ s) (γ t) = dist x y * dist s t) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ (σ : ℝ) (β : ℕ → ℝ), σ ≤ η → β 3 ≤ η → KleinerLottApprox z c σ →
        splittingRank.{u, w} z β 3 ≤ 2 := by
  obtain ⟨η, hη, hηsmall, hex⟩ := exists_uniform_three_splitting_exclusion.{u, v, w}
  refine ⟨η, hη, hηsmall, ?_⟩
  intro Z mZ z C mC hc c hseg hdim hcomp σ β hσ hβ f
  exact splittingRank_le_two_of_no_three z β
    (hex Z z C c hseg hdim hcomp σ (β 3) hσ hβ f)

theorem exists_uniform_three_splitting_exclusion_of_model_itself :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
      ∀ (C : Type u) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∃ γ : Icc (0 : ℝ) 1 → C, Continuous γ ∧
        γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (γ s) (γ t) = dist x y * dist s t) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ β : ℝ, β ≤ η → ¬ HasEuclideanSplitting.{u, w} c 3 β := by
  obtain ⟨η, hη, hηsmall, hex⟩ := exists_uniform_three_splitting_exclusion.{u, u, w}
  refine ⟨η, hη, hηsmall, ?_⟩
  intro C mC hc c hseg hdim hcomp β hβ
  exact hex C c C c hseg hdim hcomp η β le_rfl hβ
    ((IsometryEquiv.refl C).toKleinerLottApprox rfl hη (by linarith))

theorem exists_point_model_rank_consumer :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
      ∀ (Z : Type u) [MetricSpace Z] (z : Z) (σ : ℝ) (β : ℕ → ℝ),
        σ ≤ η → β 3 ≤ η → KleinerLottApprox z (PUnit.unit : PUnit.{1}) σ →
          splittingRank.{u, w} z β 3 ≤ 2 := by
  obtain ⟨η, hη, hηsmall, hex⟩ := exists_uniform_rank_bound_of_model.{u, 0, w}
  refine ⟨η, hη, hηsmall, ?_⟩
  intro Z mZ z σ β hσ hβ f
  apply hex Z z PUnit PUnit.unit ?_ ?_ ?_ σ β hσ hβ f
  · intro x y
    refine ⟨fun t => x, continuous_const, rfl, Subsingleton.elim x y, ?_⟩
    intro s t
    simp [Subsingleton.elim x y]
  · rw [Set.Subsingleton.dimH_zero (subsingleton_univ : (univ : Set PUnit).Subsingleton)]
    norm_num
  · intro x hx a ha b hb c hc hax hbx hcx
    exact (hax (Subsingleton.elim a x)).elim

end GC.MetricGeometry
