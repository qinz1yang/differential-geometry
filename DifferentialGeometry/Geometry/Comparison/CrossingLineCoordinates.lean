import DifferentialGeometry.Geometry.Comparison.LineDistance
import DifferentialGeometry.Geometry.Comparison.CanonicalGermAngle

set_option autoImplicit false

open Set Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]
variable {γ β : ℝ → X}

theorem lineCoordinate_crossing_isometries_reciprocity
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ) (hβ : Isometry β)
    (hbase : γ 0 = β 0) (s t : ℝ) :
    s * lineCoordinate γ (β t) = t * lineCoordinate β (γ s) := by
  have hleft := sq_dist_isometry_line hs hγ (β t) s
  have hright := sq_dist_isometry_line hs hβ (γ s) t
  rw [hbase, hβ.dist_eq, Real.dist_eq, sub_zero, sq_abs, dist_comm (β t) (γ s)] at hleft
  rw [← hbase, hγ.dist_eq, Real.dist_eq, sub_zero, sq_abs] at hright
  nlinarith

theorem lineCoordinate_crossing_isometry
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ) (hβ : Isometry β)
    (hbase : γ 0 = β 0) (t : ℝ) :
    lineCoordinate γ (β t) = t * lineCoordinate γ (β 1) := by
  have hsym := lineCoordinate_crossing_isometries_reciprocity hs hγ hβ hbase 1 1
  have ht := lineCoordinate_crossing_isometries_reciprocity hs hγ hβ hbase 1 t
  simp only [one_mul] at hsym ht
  rwa [← hsym] at ht

theorem sq_dist_crossing_isometries
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ) (hβ : Isometry β)
    (hbase : γ 0 = β 0) (s t : ℝ) :
    dist (γ s) (β t) ^ 2 = s ^ 2 + t ^ 2 - 2 * s * t * lineCoordinate γ (β 1) := by
  have hh := sq_dist_isometry_line hs hγ (β t) s
  rw [hbase, hβ.dist_eq, Real.dist_eq, sub_zero, sq_abs, dist_comm (β t) (γ s),
    lineCoordinate_crossing_isometry hs hγ hβ hbase] at hh
  nlinarith

theorem comparisonAngle_crossing_isometries
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ) (hβ : Isometry β)
    (hbase : γ 0 = β 0) {s t : ℝ} (hspos : 0 < s) (htpos : 0 < t) :
    comparisonAngle s t (dist (γ s) (β t)) = Real.arccos (lineCoordinate γ (β 1)) := by
  rw [comparisonAngle, comparisonCosine, sq_dist_crossing_isometries hs hγ hβ hbase]
  congr 1
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num) hspos.ne') htpos.ne')).mpr
  ring

theorem germComparisonAngle_crossing_isometries
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ) (hβ : Isometry β)
    (hbase : γ 0 = β 0) :
    germComparisonAngle 0 γ β = Real.arccos (lineCoordinate γ (β 1)) := by
  apply germComparisonAngle_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  filter_upwards [hpos.prod_inl (𝓝[>] (0 : ℝ)), hpos.prod_inr (𝓝[>] (0 : ℝ))] with z hz₁ hz₂
  rw [comparisonAngleNegCurvature_zero,
    comparisonAngle_crossing_isometries hs hγ hβ hbase hz₁ hz₂]

theorem lineCoordinate_crossing_isometry_eq_zero_of_right_angle
    (hs : fourPointComparison 0 (univ : Set X)) (hγ : Isometry γ) (hβ : Isometry β)
    (hbase : γ 0 = β 0) (hangle : germComparisonAngle 0 γ β = Real.pi / 2) (t : ℝ) :
    lineCoordinate γ (β t) = 0 := by
  rw [germComparisonAngle_crossing_isometries hs hγ hβ hbase] at hangle
  rw [lineCoordinate_crossing_isometry hs hγ hβ hbase,
    Real.arccos_eq_pi_div_two.mp hangle, mul_zero]

end DifferentialGeometry.Geometry.Comparison.Toponogov
