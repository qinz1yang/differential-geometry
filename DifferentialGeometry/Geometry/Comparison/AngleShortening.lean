import DifferentialGeometry.Geometry.Comparison.AngleMonotonicity
import DifferentialGeometry.Geometry.Comparison.HyperbolicSideComparison
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem comparisonAngleNegCurvature_eq_one_sqrt_mul {κ : ℝ} (hκ : κ ≠ 0)
    (a b c : ℝ) :
    comparisonAngleNegCurvature κ a b c =
      comparisonAngleNegCurvature 1 (sqrt κ * a) (sqrt κ * b) (sqrt κ * c) := by
  simp only [comparisonAngleNegCurvature, hκ, one_ne_zero, ite_false, sqrt_one, one_mul]

theorem comparisonAngleNegCurvature_le_of_shortening_left
    {X : Type*} [MetricSpace X] {κ : ℝ} (hκ : 0 ≤ κ) {Ω : Set X}
    (hcomp : fourPointComparison κ Ω) {q u x z : X}
    (hq : q ∈ Ω) (hu : u ∈ Ω) (hx : x ∈ Ω) (hz : z ∈ Ω)
    (ha : 0 < dist q u) (hzq : z ≠ q)
    (hparts : dist q x = dist q u + dist u x) :
    comparisonAngleNegCurvature κ (dist q x) (dist q z) (dist x z) ≤
      comparisonAngleNegCurvature κ (dist q u) (dist q z) (dist u z) := by
  by_cases hux : u = x
  · subst u
    exact le_rfl
  have hb : 0 < dist u x := dist_pos.mpr hux
  have hL : 0 < dist q x := by rw [hparts]; positivity
  by_cases hk : κ = 0
  · subst κ
    have ht : dist q u / dist q x ∈ Ioc (0 : ℝ) 1 :=
      ⟨div_pos ha hL, (div_le_one hL).mpr (by linarith)⟩
    have h := metricComparisonAngle_le_of_shortening_left hcomp hq hx hz hu
      (dist_pos.mp hL).symm hzq ht
      (by field_simp)
      (by rw [sub_mul, div_mul_cancel₀ _ hL.ne', one_mul]; linarith)
    simpa only [comparisonAngleNegCurvature_zero, metricComparisonAngle] using h
  have hs : 0 < sqrt κ := sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hk))
  let d : X → X → ℝ := dist
  let m : MetricSpace X := inferInstance
  let m' : MetricSpace X := m.rescale (sqrt κ) hs
  have hc : @fourPointComparison X m' 1 Ω := by
    intro p hp a ha b hb c hc hap hbp hcp
    change comparisonAngleNegCurvature 1 (sqrt κ * d p a) (sqrt κ * d p b)
        (sqrt κ * d a b) +
      comparisonAngleNegCurvature 1 (sqrt κ * d p b) (sqrt κ * d p c)
        (sqrt κ * d b c) +
      comparisonAngleNegCurvature 1 (sqrt κ * d p c) (sqrt κ * d p a)
        (sqrt κ * d c a) ≤ 2 * Real.pi
    simp only [← comparisonAngleNegCurvature_eq_one_sqrt_mul hk]
    exact hcomp p hp a ha b hb c hc hap hbp hcp
  have h := @comparisonAngleNegCurvature_one_le_of_shortening_left X m' Ω hc q u x z
    hq hu hx hz (mul_pos hs ha) (mul_pos hs hb) hzq
    (by change sqrt κ * d q x = sqrt κ * d q u + sqrt κ * d u x
        dsimp only [d]
        rw [hparts, mul_add])
  change comparisonAngleNegCurvature 1 (sqrt κ * d q x) (sqrt κ * d q z)
      (sqrt κ * d x z) ≤
    comparisonAngleNegCurvature 1 (sqrt κ * d q u) (sqrt κ * d q z)
      (sqrt κ * d u z) at h
  simpa only [← comparisonAngleNegCurvature_eq_one_sqrt_mul hk] using h


theorem comparisonAngleNegCurvature_le_of_shortening_right
    {X : Type*} [MetricSpace X] {κ : ℝ} (hκ : 0 ≤ κ) {Ω : Set X}
    (hcomp : fourPointComparison κ Ω) {q u x z : X}
    (hq : q ∈ Ω) (hu : u ∈ Ω) (hx : x ∈ Ω) (hz : z ∈ Ω)
    (ha : 0 < dist q u) (hzq : z ≠ q)
    (hparts : dist q x = dist q u + dist u x) :
    comparisonAngleNegCurvature κ (dist q z) (dist q x) (dist z x) ≤
      comparisonAngleNegCurvature κ (dist q z) (dist q u) (dist z u) := by
  have h := comparisonAngleNegCurvature_le_of_shortening_left hκ hcomp hq hu hx hz ha hzq hparts
  simpa only [comparisonAngleNegCurvature_comm κ (dist q x),
    comparisonAngleNegCurvature_comm κ (dist q u), dist_comm x z, dist_comm u z] using h

end DifferentialGeometry.Geometry.Comparison.Toponogov
