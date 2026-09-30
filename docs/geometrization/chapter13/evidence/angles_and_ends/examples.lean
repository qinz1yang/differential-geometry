import DifferentialGeometry.Geometry.Comparison.AlmostOppositeAngle
import DifferentialGeometry.Topology.MetricSpace.GeodesicLine
import DifferentialGeometry.Topology.MetricSpace.ProductEnds
import DifferentialGeometry.Geometry.Metric.Approximation.MultipleEndsBlowdown

set_option autoImplicit false

open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace Chapter13Examples

theorem straight_euclidean_angle :
    1 + Real.cos (comparisonAngleNegCurvature 0 1 1 2) = 0 := by
  have h := one_add_cos_comparisonAngle_double_le
    (κ := 0) (r := 1) (ℓ := 1) (μ := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith [h.1, h.2]

theorem hyperbolic_angle_at_curvature_bound :
    1 + Real.cos (comparisonAngleNegCurvature (1 / 9) 1 (6 / 5) 2) ≤ 6 / 5 := by
  have h := (one_add_cos_comparisonAngle_double_le
    (κ := 1 / 3) (r := 1) (ℓ := 6 / 5) (μ := 1 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).2
  norm_num at h ⊢
  exact h

theorem line_with_alternating_centers :
    ∃ f : ℝ → ℝ, Isometry f ∧ f 0 ∈ ({-1, 1} : Set ℝ) := by
  let g (n : ℕ) (t : ℝ) := t + if Even n then 1 else -1
  have hb (n : ℕ) : g n 0 ∈ ({-1, 1} : Set ℝ) := by
    by_cases hn : Even n <;> simp [g, hn]
  apply exists_isometry_of_local_distortion 0 (isCompact_singleton.insert (-1))
    g hb (ε := fun _ => 0) tendsto_const_nhds
  intro S
  exact Eventually.of_forall fun n s t _ _ => by simp [g, dist_add_right]

theorem line_through_compact_singleton :
    ∃ f : ℝ → ℝ, Isometry f ∧ f 0 = 0 := by
  have h := exists_isometric_line_of_compact_centers
    (K := ({0} : Set ℝ)) isCompact_singleton (fun R hR =>
      ⟨Subtype.val, isometry_subtype_coe, by simp⟩)
  simpa using h

theorem plane_unbounded_components_agree {K : Set (ℝ × ℝ)} (hK : Bornology.IsBounded K)
    {a b : ℝ × ℝ} (ha : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b)) :
    connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b := by
  have hR : ¬ Bornology.IsBounded (univ : Set ℝ) := by
    intro h
    obtain ⟨R, hR⟩ := h.subset_closedBall 0
    have hh : |R| + 1 ≤ R := by
      have hh := hR (mem_univ (|R| + 1))
      simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ |R| + 1)] using hh
    linarith [le_abs_self R]
  exact connectedComponentIn_compl_prod_eq_of_unbounded hR hK ha hb

theorem bounded_open_factor_blowdown :
    let c (n : ℕ) := ((n : ℝ) + 1)⁻¹
    @PointedGHConverges (fun _ : ℕ => WithLp 2 (ℝ × Ioo (0 : ℝ) 1))
      (fun n => (inferInstance : MetricSpace (WithLp 2 (ℝ × Ioo (0 : ℝ) 1))).rescale
        (c n) (by dsimp [c]; positivity)) ℝ _
      (fun _ => WithLp.toLp 2 (5, (⟨1 / 2, by norm_num⟩ : Ioo (0 : ℝ) 1))) 0 := by
  dsimp only
  refine pointedGHConverges_rescaled_normed_product
    (5 : ℝ) (⟨1 / 2, by norm_num⟩ : Ioo (0 : ℝ) 1) ?_
    (fun n => by positivity) ?_
  · apply Metric.isBounded_iff.mpr
    refine ⟨1, fun x _ y _ => ?_⟩
    change |(x : ℝ) - (y : ℝ)| ≤ 1
    exact abs_le.mpr ⟨by linarith [x.property.1, y.property.2],
      by linarith [x.property.2, y.property.1]⟩
  · simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

end Chapter13Examples

#print axioms Chapter13Examples.straight_euclidean_angle
#print axioms Chapter13Examples.hyperbolic_angle_at_curvature_bound
#print axioms Chapter13Examples.line_with_alternating_centers
#print axioms Chapter13Examples.line_through_compact_singleton
#print axioms Chapter13Examples.plane_unbounded_components_agree
#print axioms Chapter13Examples.bounded_open_factor_blowdown
