import DifferentialGeometry.Geometry.Comparison.FourPoint

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem cos_add_cos_nonneg_of_sum_le_pi {θ φ : ℝ}
    (hθ : θ ∈ Icc 0 Real.pi) (hφ : φ ∈ Icc 0 Real.pi)
    (hsum : θ + φ ≤ Real.pi) : 0 ≤ cos θ + cos φ := by
  have h := cos_le_cos_of_nonneg_of_le_pi hφ.1
    (by linarith [hθ.1] : Real.pi - θ ≤ Real.pi) (by linarith : φ ≤ Real.pi - θ)
  rw [cos_pi_sub] at h
  linarith

private theorem sinh_weighted_cosh_le_of_cosine_sum {a b l S C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hl : 0 < l)
    (hsum : 0 ≤ (cosh a * cosh l - cosh S) / (sinh a * sinh l) +
      (cosh l * cosh b - cosh C) / (sinh l * sinh b)) :
    sinh b * cosh S + sinh a * cosh C ≤ sinh (a + b) * cosh l := by
  have hsa := sinh_pos_iff.mpr ha
  have hsb := sinh_pos_iff.mpr hb
  have hsl := sinh_pos_iff.mpr hl
  have h := mul_nonneg hsum (show 0 ≤ sinh a * sinh b * sinh l by positivity)
  have heq : ((cosh a * cosh l - cosh S) / (sinh a * sinh l) +
      (cosh l * cosh b - cosh C) / (sinh l * sinh b)) * (sinh a * sinh b * sinh l) =
      sinh b * (cosh a * cosh l - cosh S) + sinh a * (cosh l * cosh b - cosh C) := by
    field_simp
  rw [heq] at h
  rw [sinh_add]
  nlinarith

theorem hyperbolic_side_comparison_of_fourPointComparison
    {X : Type*} [MetricSpace X] {Ω : Set X} (hcomp : fourPointComparison 1 Ω)
    {q u x z : X} (hq : q ∈ Ω) (hu : u ∈ Ω) (hx : x ∈ Ω) (hz : z ∈ Ω)
    (ha : 0 < dist q u) (hb : 0 < dist u x)
    (hparts : dist q x = dist q u + dist u x) :
    sinh (dist u x) * cosh (dist q z) + sinh (dist q u) * cosh (dist x z) ≤
      sinh (dist q x) * cosh (dist u z) := by
  by_cases hzu : z = u
  · subst z
    rw [dist_self, cosh_zero, mul_one, hparts, sinh_add, dist_comm x u]
    ring_nf
    exact le_rfl
  have hl : 0 < dist u z := dist_pos.mpr (Ne.symm hzu)
  have hau : 0 < dist u q := by rwa [dist_comm]
  have hang := hcomp u hu q hq x hx z hz (dist_pos.mp hau).symm
    (dist_pos.mp hb).symm hzu
  have hstraight : comparisonAngleNegCurvature 1 (dist u q) (dist u x) (dist q x) = Real.pi := by
    rw [hparts, dist_comm q u]
    exact comparisonAngleNegCurvature_add (by norm_num) hau hb
  rw [hstraight] at hang
  have hcos : 0 ≤ cos (comparisonAngleNegCurvature 1 (dist u x) (dist u z) (dist x z)) +
      cos (comparisonAngleNegCurvature 1 (dist u z) (dist u q) (dist z q)) := by
    apply cos_add_cos_nonneg_of_sum_le_pi (comparisonAngleNegCurvature_mem_Icc _ _ _ _)
      (comparisonAngleNegCurvature_mem_Icc _ _ _ _)
    linarith
  have hcos1 := cos_comparisonAngleNegCurvature_of_pos (by norm_num : (0 : ℝ) < 1) hb hl
    (by simpa only [dist_comm u x, dist_comm u z] using abs_dist_sub_le x z u) (dist_triangle_left x z u)
  have hcos2 := cos_comparisonAngleNegCurvature_of_pos (by norm_num : (0 : ℝ) < 1) hl hau
    (by simpa only [dist_comm u z, dist_comm u q] using abs_dist_sub_le z q u) (dist_triangle_left z q u)
  simp only [sqrt_one, one_mul] at hcos1 hcos2
  rw [hcos1, hcos2] at hcos
  have h := sinh_weighted_cosh_le_of_cosine_sum hb hau hl hcos
  simpa only [dist_comm u q, dist_comm z q, dist_comm x z, add_comm (dist u x), ← hparts,
    add_comm] using h

theorem comparisonAngleNegCurvature_one_le_of_shortening_left
    {X : Type*} [MetricSpace X] {Ω : Set X} (hcomp : fourPointComparison 1 Ω)
    {q u x z : X} (hq : q ∈ Ω) (hu : u ∈ Ω) (hx : x ∈ Ω) (hz : z ∈ Ω)
    (ha : 0 < dist q u) (hb : 0 < dist u x) (hzq : z ≠ q)
    (hparts : dist q x = dist q u + dist u x) :
    comparisonAngleNegCurvature 1 (dist q x) (dist q z) (dist x z) ≤
      comparisonAngleNegCurvature 1 (dist q u) (dist q z) (dist u z) := by
  have hw := hyperbolic_side_comparison_of_fourPointComparison hcomp hq hu hx hz ha hb hparts
  have hS : 0 < dist q z := dist_pos.mpr hzq.symm
  have hL : 0 < dist q x := by rw [hparts]; positivity
  have hsa : 0 < sinh (dist q u) := sinh_pos_iff.mpr ha
  have hsS : 0 < sinh (dist q z) := sinh_pos_iff.mpr hS
  have hsL : 0 < sinh (dist q x) := sinh_pos_iff.mpr hL
  have hid : sinh (dist q x) * cosh (dist q u) - sinh (dist q u) * cosh (dist q x) =
      sinh (dist u x) := by
    have heq : dist q x - dist q u = dist u x := by linarith
    rw [mul_comm (sinh (dist q u)) (cosh (dist q x)), ← sinh_sub, heq]
  simp only [comparisonAngleNegCurvature, one_ne_zero, ite_false, sqrt_one, one_mul]
  apply arccos_le_arccos
  apply (div_le_div_iff₀ (mul_pos hsa hsS) (mul_pos hsL hsS)).mpr
  have h := mul_nonneg (sub_nonneg.mpr hw) hsS.le
  nlinarith [congrArg (fun w => w * cosh (dist q z) * sinh (dist q z)) hid]

end DifferentialGeometry.Geometry.Comparison.Toponogov
