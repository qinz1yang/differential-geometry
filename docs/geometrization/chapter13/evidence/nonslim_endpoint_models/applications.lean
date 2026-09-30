import DifferentialGeometry.Geometry.Metric.Approximation.NonslimEndpointRecognition
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open Set Metric GC.MetricGeometry
namespace LocalChartRegression

private def exactApprox {X : Type*} [MetricSpace X] (p : X) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) : KleinerLottApprox p p ε where
  error_pos := hε
  error_lt_one := hε1
  toFun := id
  basepoint := rfl
  distortion _ _ _ _ := by simp; exact hε.le
  coverage y hy := by
    have hm : y ∈ id '' ball p ε⁻¹ := ⟨y, by change dist y p < ε⁻¹; linarith, rfl⟩
    exact (infDist_le_dist_of_mem hm).trans (by simpa using hε.le)

private noncomputable def charted :=
  (exactApprox (0 : ℝ) (ε := 1 / 1000) (by norm_num) (by norm_num)).mapTargetBallIsometry
    (R := 20) (by norm_num) (IsometryEquiv.refl (ball (0 : ℝ) 20)) rfl
    (δ := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem chart_keeps_tested_points : charted.toFun (99 / 10) = 99 / 10 := by
  apply KleinerLottApprox.mapTargetBallIsometry_apply
  norm_num [exactApprox, Real.dist_eq]

theorem chart_extends_outside : charted.toFun 100 = 0 := by
  norm_num [charted, KleinerLottApprox.mapTargetBallIsometry, exactApprox, Real.dist_eq]

theorem chart_covers_near_test_radius :
    ∃ x ∈ ball (0 : ℝ) 10, dist (989 / 100) (charted.toFun x) < 1 / 5 := by
  have h := charted.coverage_witness (989 / 100) (by norm_num [Real.dist_eq])
  norm_num at h
  simpa only [mem_ball, Real.dist_eq, sub_zero] using h

theorem reflection_keeps_positive_height :
    (IsometryEquiv.reflectIcc 1000 (⟨999, by norm_num⟩ : Icc (0 : ℝ) 1000)).val = 1 := by
  norm_num

theorem circle_chart_preserves_pair_distances_at_boundary
    (x y : ball (0 : ℝ) 1) :
    dist ((AddCircle.realBallIsometry (L := 4) (by norm_num) (by norm_num)) x)
      ((AddCircle.realBallIsometry (L := 4) (by norm_num) (by norm_num)) y) = dist x y :=
  (AddCircle.realBallIsometry (L := 4) (by norm_num) (by norm_num)).dist_eq x y

theorem product_retains_first_coordinate {Y Z : Type*} [MetricSpace Y] [MetricSpace Z]
    {q : Y} {z : Z} (e : ball q 2 ≃ᵢ ball z 2)
    (he : (e ⟨q, mem_ball_self (by norm_num)⟩).val = z)
    (x : ball (WithLp.toLp 2 ((3 : ℝ), q)) 2) :
    ((e.l2ProductBall (by norm_num) he 3) x).val.fst = x.val.fst := rfl

#print axioms chart_keeps_tested_points
#print axioms chart_extends_outside
#print axioms chart_covers_near_test_radius
#print axioms reflection_keeps_positive_height
#print axioms circle_chart_preserves_pair_distances_at_boundary
#print axioms product_retains_first_coordinate
end LocalChartRegression
