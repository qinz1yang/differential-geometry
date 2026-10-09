import DifferentialGeometry.Geometry.Comparison.AngleShortening
import DifferentialGeometry.Geometry.Comparison.ModelSide

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem modelSideNegCurvature_point_on_side_le_dist
    {X : Type*} [MetricSpace X] {κ : ℝ} (hκ : 0 ≤ κ) {Ω : Set X}
    (hcomp : fourPointComparison κ Ω) {q u x z : X}
    (hq : q ∈ Ω) (hu : u ∈ Ω) (hx : x ∈ Ω) (hz : z ∈ Ω)
    (hparts : dist q x = dist q u + dist u x) :
    modelSideNegCurvature κ (dist q u) (dist q z)
      (comparisonAngleNegCurvature κ (dist q x) (dist q z) (dist x z)) ≤ dist u z := by
  by_cases huq : u = q
  · subst u
    rw [dist_self, modelSideNegCurvature_zero_left hκ dist_nonneg]
  by_cases hzq : z = q
  · subst z
    rw [dist_self, modelSideNegCurvature_zero_right hκ dist_nonneg, dist_comm u q]
  have ha : 0 < dist q u := dist_pos.mpr (Ne.symm huq)
  have hb : 0 < dist q z := dist_pos.mpr (Ne.symm hzq)
  have hangle := comparisonAngleNegCurvature_le_of_shortening_left hκ hcomp hq hu hx hz ha hzq hparts
  have hlo := abs_dist_sub_le u z q
  rw [dist_comm u q, dist_comm z q] at hlo
  have hhi := dist_triangle u q z
  rw [dist_comm u q] at hhi
  calc
    modelSideNegCurvature κ (dist q u) (dist q z)
        (comparisonAngleNegCurvature κ (dist q x) (dist q z) (dist x z)) ≤
      modelSideNegCurvature κ (dist q u) (dist q z)
        (comparisonAngleNegCurvature κ (dist q u) (dist q z) (dist u z)) :=
      modelSideNegCurvature_mono_angle hκ ha.le hb.le
        (comparisonAngleNegCurvature_mem_Icc _ _ _ _).1
        (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2 hangle
    _ = dist u z := modelSideNegCurvature_comparisonAngle hκ ha hb hlo hhi

end DifferentialGeometry.Geometry.Comparison.Toponogov
