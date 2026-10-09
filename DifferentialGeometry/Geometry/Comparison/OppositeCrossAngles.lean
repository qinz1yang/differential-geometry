import DifferentialGeometry.Geometry.Comparison.CrossingLineCoordinates

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {γ β : ℝ → X}

theorem germComparisonAngle_eq_pi_div_two_of_opposite_cross_lower_bounds
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ) (hβ : Isometry β)
    (hbase : γ 0 = β 0) {T : ℝ} (hT : 0 < T)
    (hplus : Real.pi / 2 ≤ comparisonAngle T T (dist (γ T) (β T)))
    (hminus : Real.pi / 2 ≤ comparisonAngle T T (dist (γ T) (β (-T)))) :
    germComparisonAngle 0 γ β = Real.pi / 2 := by
  have hreverse : Isometry (fun t : ℝ => β (-t)) := by
    apply Isometry.of_dist_eq
    intro s t
    rw [hβ.dist_eq]
    exact dist_neg_neg s t
  rw [comparisonAngle_crossing_isometries hs hγ hβ hbase hT hT] at hplus
  have hminus' : Real.pi / 2 ≤
      comparisonAngle T T (dist (γ T) ((fun t : ℝ => β (-t)) T)) := hminus
  rw [comparisonAngle_crossing_isometries hs hγ hreverse
    (by simpa only [neg_zero] using hbase) hT hT] at hminus'
  change Real.pi / 2 ≤ Real.arccos (lineCoordinate γ (β (-1))) at hminus'
  rw [lineCoordinate_crossing_isometry hs hγ hβ hbase, neg_one_mul] at hminus'
  have hnonpos := Real.pi_div_two_le_arccos.mp hplus
  have hnonneg := Real.pi_div_two_le_arccos.mp hminus'
  have hzero : lineCoordinate γ (β 1) = 0 := by linarith
  rw [germComparisonAngle_crossing_isometries hs hγ hβ hbase, hzero, Real.arccos_zero]

theorem sq_dist_crossing_isometries_of_opposite_cross_lower_bounds
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ) (hβ : Isometry β)
    (hbase : γ 0 = β 0) {T : ℝ} (hT : 0 < T)
    (hplus : Real.pi / 2 ≤ comparisonAngle T T (dist (γ T) (β T)))
    (hminus : Real.pi / 2 ≤ comparisonAngle T T (dist (γ T) (β (-T)))) (s t : ℝ) :
    dist (γ s) (β t) ^ 2 = s ^ 2 + t ^ 2 := by
  have hangle := germComparisonAngle_eq_pi_div_two_of_opposite_cross_lower_bounds
    hs hγ hβ hbase hT hplus hminus
  rw [sq_dist_crossing_isometries hs hγ hβ hbase,
    lineCoordinate_crossing_isometry_eq_zero_of_right_angle hs hγ hβ hbase hangle,
    mul_zero, sub_zero]

end DifferentialGeometry.Geometry.Comparison.Toponogov
