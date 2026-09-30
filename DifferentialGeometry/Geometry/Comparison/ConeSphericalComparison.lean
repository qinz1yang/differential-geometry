import DifferentialGeometry.Geometry.Comparison.SphericalFourPointComparison
import DifferentialGeometry.Geometry.Comparison.ConeSecantLift
import DifferentialGeometry.Geometry.Comparison.FourPoint

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Metric.EuclideanCone

variable {Y : Type*} [MetricSpace Y]

theorem sphericalComparisonAngle_sum_le_of_cone_comparison
    (hcone : fourPointComparison 0 (univ : Set (EuclideanCone Y)))
    {p a b c : Y} (hpa : 0 < dist p a) (hpb : 0 < dist p b) (hpc : 0 < dist p c)
    (ha : dist p a < Real.pi / 2) (hb : dist p b < Real.pi / 2)
    (hc : dist p c < Real.pi / 2) :
    sphericalComparisonAngle (dist p a) (dist p b) (dist a b) +
      sphericalComparisonAngle (dist p b) (dist p c) (dist b c) +
      sphericalComparisonAngle (dist p c) (dist p a) (dist c a) ≤ 2 * Real.pi := by
  have h := hcone (mk 1 p) (mem_univ _) (secLift p a ha) (mem_univ _)
    (secLift p b hb) (mem_univ _) (secLift p c hc) (mem_univ _)
    (dist_pos.mp (dist_mk_one_secLift_pos hpa ha)).symm
    (dist_pos.mp (dist_mk_one_secLift_pos hpb hb)).symm
    (dist_pos.mp (dist_mk_one_secLift_pos hpc hc)).symm
  simp only [comparisonAngleNegCurvature_zero] at h
  rw [comparisonAngle_secLift hpa hpb ha hb, comparisonAngle_secLift hpb hpc hb hc,
    comparisonAngle_secLift hpc hpa hc ha] at h
  exact h

theorem fourPointSphericalComparison_ball_of_cone_comparison
    (hcone : fourPointComparison 0 (univ : Set (EuclideanCone Y))) (o : Y) :
    fourPointSphericalComparison (ball o (Real.pi / 4)) := by
  have hsmall (x y : Y) (hx : x ∈ ball o (Real.pi / 4))
      (hy : y ∈ ball o (Real.pi / 4)) : dist x y < Real.pi / 2 := by
    have hxo : dist x o < Real.pi / 4 := hx
    have hyo : dist y o < Real.pi / 4 := hy
    have htri := dist_triangle x o y
    rw [dist_comm o y] at htri
    linarith
  intro p hp a ha b hb c hc hpa hpb hpc _ _ _
  exact sphericalComparisonAngle_sum_le_of_cone_comparison hcone
    (dist_pos.mpr hpa.symm) (dist_pos.mpr hpb.symm) (dist_pos.mpr hpc.symm)
    (hsmall p a hp ha) (hsmall p b hp hb) (hsmall p c hp hc)

end DifferentialGeometry.Geometry.Comparison.Toponogov
