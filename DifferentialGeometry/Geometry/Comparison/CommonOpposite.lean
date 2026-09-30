import DifferentialGeometry.Geometry.Comparison.FourPoint
import DifferentialGeometry.Geometry.Comparison.ModelSide

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem dist_eq_abs_sub_of_common_opposite {κ : ℝ} (hκ : 0 ≤ κ) {S : Set X}
    (hcomp : fourPointComparison κ S) {p x y z : X}
    (hp : p ∈ S) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hzp : z ≠ p)
    (hxz : dist x z = dist x p + dist p z)
    (hyz : dist y z = dist y p + dist p z) :
    dist x y = |dist x p - dist y p| := by
  by_cases hxp : x = p
  · subst x
    simp [dist_comm]
  by_cases hyp : y = p
  · subst y
    simp
  have hpx : 0 < dist p x := dist_pos.mpr (Ne.symm hxp)
  have hpy : 0 < dist p y := dist_pos.mpr (Ne.symm hyp)
  have hpz : 0 < dist p z := dist_pos.mpr hzp.symm
  have hangle_yz : comparisonAngleNegCurvature κ (dist p y) (dist p z) (dist y z) = Real.pi := by
    rw [hyz, dist_comm y p]
    exact comparisonAngleNegCurvature_add hκ hpy hpz
  have hangle_zx : comparisonAngleNegCurvature κ (dist p z) (dist p x) (dist z x) = Real.pi := by
    rw [dist_comm z x, hxz, dist_comm x p, add_comm]
    exact comparisonAngleNegCurvature_add hκ hpz hpx
  have hsum := hcomp p hp x hx y hy z hz hxp hyp hzp
  rw [hangle_yz, hangle_zx] at hsum
  have hzero : comparisonAngleNegCurvature κ (dist p x) (dist p y) (dist x y) = 0 := by
    have hnonneg := (comparisonAngleNegCurvature_mem_Icc κ (dist p x) (dist p y) (dist x y)).1
    linarith
  have hm := modelSideNegCurvature_comparisonAngle hκ hpx hpy
    (show |dist p x - dist p y| ≤ dist x y by
      simpa only [dist_comm p x, dist_comm p y] using abs_dist_sub_le x y p)
    (show dist x y ≤ dist p x + dist p y by
      simpa only [dist_comm x p] using dist_triangle x p y)
  rw [hzero, modelSideNegCurvature_zero_angle hκ] at hm
  simpa only [dist_comm p x, dist_comm p y] using hm.symm

end DifferentialGeometry.Geometry.Comparison.Toponogov
