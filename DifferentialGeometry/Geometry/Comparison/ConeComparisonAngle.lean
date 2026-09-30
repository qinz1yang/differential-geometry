import DifferentialGeometry.Geometry.Metric.EuclideanCone
import DifferentialGeometry.Geometry.Comparison.FourPoint

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Metric.EuclideanCone

variable {Y : Type*} [MetricSpace Y]

theorem comparisonAngle_tip_mk {r s : ℝ≥0} (hr : 0 < (r : ℝ)) (hs : 0 < (s : ℝ))
    (a b : Y) :
    comparisonAngle (dist tip (mk r a)) (dist tip (mk s b))
      (dist (mk r a) (mk s b)) = min Real.pi (dist a b) := by
  rw [tip_dist, radius_mk, tip_dist, radius_mk, dist_mk, comparisonAngle, comparisonCosine]
  have hd := coneDistance_sq (x := ((r : ℝ), a)) (y := ((s : ℝ), b)) hr.le hs.le
  dsimp only [Prod.fst, Prod.snd] at hd
  rw [hd]
  have he : ((r : ℝ) ^ 2 + (s : ℝ) ^ 2 -
      ((r : ℝ) ^ 2 + (s : ℝ) ^ 2 - 2 * r * s * Real.cos (min Real.pi (dist a b)))) /
      (2 * r * s) = Real.cos (min Real.pi (dist a b)) := by
    field_simp
    ring
  rw [he]
  exact Real.arccos_cos (le_min Real.pi_pos.le dist_nonneg) (min_le_left _ _)

theorem dist_add_eq_pi_of_cone_comparison
    (hdiam : ∀ a b : Y, dist a b ≤ Real.pi)
    (hcomp : fourPointComparison 0 (univ : Set (EuclideanCone Y)))
    {a b : Y} (hab : dist a b = Real.pi) (c : Y) :
    dist a c + dist c b = Real.pi := by
  have hn (u : Y) : mk (1 : ℝ≥0) u ≠ tip := by simp
  have h := hcomp tip (mem_univ _) (mk 1 a) (mem_univ _)
    (mk 1 b) (mem_univ _) (mk 1 c) (mem_univ _) (hn a) (hn b) (hn c)
  simp only [comparisonAngleNegCurvature_zero] at h
  rw [comparisonAngle_tip_mk (by norm_num) (by norm_num),
    comparisonAngle_tip_mk (by norm_num) (by norm_num),
    comparisonAngle_tip_mk (by norm_num) (by norm_num),
    min_eq_right (hdiam a b), min_eq_right (hdiam b c), min_eq_right (hdiam c a), hab,
    dist_comm b c, dist_comm c a] at h
  have ht := dist_triangle a c b
  rw [hab] at ht
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
