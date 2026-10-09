import DifferentialGeometry.Geometry.Comparison.SphericalModelAngle
import DifferentialGeometry.Geometry.Comparison.ConeSineInterpolation

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem sphericalComparisonAngle_le_of_weighted_cosine
    {a b B C c : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : a + b < Real.pi)
    (hB : 0 < B) (hBπ : B < Real.pi)
    (hweighted : Real.sin (a + b) * Real.cos c ≤
      Real.sin b * Real.cos B + Real.sin a * Real.cos C) :
    sphericalComparisonAngle (a + b) B C ≤ sphericalComparisonAngle a B c := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hsA : 0 < Real.sin (a + b) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) hA
  have hsB : 0 < Real.sin B := Real.sin_pos_of_pos_of_lt_pi hB hBπ
  have hid : Real.sin b = Real.sin (a + b) * Real.cos a -
      Real.cos (a + b) * Real.sin a := by
    calc
      Real.sin b = (Real.sin a ^ 2 + Real.cos a ^ 2) * Real.sin b := by
        rw [Real.sin_sq_add_cos_sq]; ring
      _ = _ := by rw [Real.sin_add, Real.cos_add]; ring
  have hquot : (Real.cos c - Real.cos a * Real.cos B) / Real.sin a ≤
      (Real.cos C - Real.cos (a + b) * Real.cos B) / Real.sin (a + b) := by
    apply (div_le_div_iff₀ hsa hsA).mpr
    rw [hid] at hweighted
    nlinarith
  unfold sphericalComparisonAngle
  apply Real.arccos_le_arccos
  simpa only [div_div] using div_le_div_of_nonneg_right hquot hsB.le


theorem sphericalComparisonAngle_le_of_shortening_left
    {Y : Type*} [MetricSpace Y]
    (hdiam : ∀ v w : Y, dist v w ≤ Real.pi)
    (hcone : fourPointComparison 0 (Set.univ : Set (Metric.EuclideanCone Y)))
    {q u x z : Y} (ha : 0 < dist q u) (hzq : z ≠ q)
    (hparts : dist q x = dist q u + dist u x)
    (hperimeter : dist q x + dist q z + dist x z < 2 * Real.pi) :
    sphericalComparisonAngle (dist q x) (dist q z) (dist x z) ≤
      sphericalComparisonAngle (dist q u) (dist q z) (dist u z) := by
  by_cases hux : u = x
  · subst u; exact le_rfl
  have hb : 0 < dist u x := dist_pos.mpr hux
  have hxπ : dist q x < Real.pi := by
    have htri := dist_triangle q z x
    rw [dist_comm z x] at htri
    linarith
  have hzπ : dist q z < Real.pi := by linarith [dist_triangle q x z]
  have hweighted := sine_weighted_cosine_comparison_of_cone_comparison
    hdiam hcone (z := z) ha hb hparts hxπ
  rw [hparts] at hweighted
  simpa only [← hparts] using sphericalComparisonAngle_le_of_weighted_cosine
    ha hb (by rwa [← hparts]) (dist_pos.mpr hzq.symm) hzπ hweighted

theorem sphericalComparisonAngle_le_of_shortening_right
    {Y : Type*} [MetricSpace Y]
    (hdiam : ∀ v w : Y, dist v w ≤ Real.pi)
    (hcone : fourPointComparison 0 (Set.univ : Set (Metric.EuclideanCone Y)))
    {q u x z : Y} (ha : 0 < dist q u) (hzq : z ≠ q)
    (hparts : dist q x = dist q u + dist u x)
    (hperimeter : dist q x + dist q z + dist x z < 2 * Real.pi) :
    sphericalComparisonAngle (dist q z) (dist q x) (dist z x) ≤
      sphericalComparisonAngle (dist q z) (dist q u) (dist z u) := by
  have h := sphericalComparisonAngle_le_of_shortening_left
    hdiam hcone ha hzq hparts hperimeter
  simpa only [sphericalComparisonAngle_comm (dist q x),
    sphericalComparisonAngle_comm (dist q u), dist_comm x z, dist_comm u z] using h

end DifferentialGeometry.Geometry.Comparison.Toponogov
