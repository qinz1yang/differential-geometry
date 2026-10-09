import DifferentialGeometry.Geometry.Comparison.FourPoint

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem metricComparisonAngle_le_of_shortening_right
    {X : Type*} [MetricSpace X] {s : Set X} (hs : fourPointComparison 0 s)
    {p x y z : X} (hp : p ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    (hxp : x ≠ p) (hyp : y ≠ p) {t : ℝ} (ht : t ∈ Ioc 0 1)
    (hpz : dist p z = t * dist p y) (hzy : dist z y = (1 - t) * dist p y) :
    metricComparisonAngle x p y ≤ metricComparisonAngle x p z := by
  have htpos := ht.1
  have hA : 0 < dist p x := dist_pos.mpr hxp.symm
  have hB : 0 < dist p y := dist_pos.mpr hyp.symm
  have hq := quadratic_side_comparison_of_fourPointComparison hs hp hy hz hx
    ⟨ht.1.le, ht.2⟩ hpz hzy
  rw [dist_comm x p] at hq
  unfold metricComparisonAngle comparisonAngle
  apply Real.arccos_le_arccos
  rw [hpz]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * dist p x * (t * dist p y))
    (by positivity : 0 < 2 * dist p x * dist p y)).2
  have h := mul_nonneg
    (show 0 ≤ dist x z ^ 2 - ((1 - t) * dist p x ^ 2 + t * dist x y ^ 2 -
      t * (1 - t) * dist p y ^ 2) by linarith)
    (show 0 ≤ 2 * dist p x * dist p y by positivity)
  nlinarith

theorem metricComparisonAngle_le_of_shortening_left
    {X : Type*} [MetricSpace X] {s : Set X} (hs : fourPointComparison 0 s)
    {p x y z : X} (hp : p ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    (hxp : x ≠ p) (hyp : y ≠ p) {t : ℝ} (ht : t ∈ Ioc 0 1)
    (hpz : dist p z = t * dist p x) (hzx : dist z x = (1 - t) * dist p x) :
    metricComparisonAngle x p y ≤ metricComparisonAngle z p y := by
  have h := metricComparisonAngle_le_of_shortening_right hs hp hy hx hz hyp hxp ht hpz hzx
  simpa only [metricComparisonAngle, comparisonAngle_comm (dist p y), dist_comm y x,
    dist_comm y z] using h

end DifferentialGeometry.Geometry.Comparison.Toponogov
