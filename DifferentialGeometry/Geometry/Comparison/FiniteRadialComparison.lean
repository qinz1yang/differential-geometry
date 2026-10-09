import DifferentialGeometry.Geometry.Comparison.HyperbolicSideComparison
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.RadialModel

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem dist_radial_points_lower_of_fourPointComparison
    {Ω : Set X} (hcomp : fourPointComparison 1 Ω)
    {q x y u v : X} (hq : q ∈ Ω) (hx : x ∈ Ω) (hy : y ∈ Ω) (hu : u ∈ Ω) (hv : v ∈ Ω)
    {D t : ℝ} (hr : 0 < dist q x) (hs : 0 < dist q y)
    (hrD : dist q x ≤ D) (hsD : dist q y ≤ D) (ht : t ∈ Ioo 0 1)
    (hqu : dist q u = t * dist q x) (hux : dist u x = (1 - t) * dist q x)
    (hqv : dist q v = t * dist q y) (hvy : dist v y = (1 - t) * dist q y) :
    (t * D / sinh D) * dist x y ≤ dist u v := by
  have hqu0 : 0 < dist q u := by rw [hqu]; exact mul_pos ht.1 hr
  have hux0 : 0 < dist u x := by rw [hux]; exact mul_pos (sub_pos.mpr ht.2) hr
  have hqv0 : 0 < dist q v := by rw [hqv]; exact mul_pos ht.1 hs
  have hvy0 : 0 < dist v y := by rw [hvy]; exact mul_pos (sub_pos.mpr ht.2) hs
  have h1 := comparisonAngleNegCurvature_one_le_of_shortening_left hcomp hq hu hx hy
    hqu0 hux0 (dist_pos.mp hs).symm (by rw [hqu, hux]; ring)
  have h2 := comparisonAngleNegCurvature_one_le_of_shortening_left hcomp hq hv hy hu
    hqv0 hvy0 (dist_pos.mp hqu0).symm (by rw [hqv, hvy]; ring)
  have h2' : comparisonAngleNegCurvature 1 (dist q u) (dist q y) (dist u y) ≤
      comparisonAngleNegCurvature 1 (dist q u) (dist q v) (dist u v) := by
    simpa only [comparisonAngleNegCurvature_comm 1 (dist q u), dist_comm u y, dist_comm u v] using h2
  let C := cos (comparisonAngleNegCurvature 1 (dist q x) (dist q y) (dist x y))
  have hcos : cos (comparisonAngleNegCurvature 1 (dist q u) (dist q v) (dist u v)) ≤ C :=
    cos_le_cos_of_nonneg_of_le_pi (comparisonAngleNegCurvature_mem_Icc _ _ _ _).1
      (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2 (h1.trans h2')
  have hbig := cos_comparisonAngleNegCurvature_of_pos (by norm_num : (0 : ℝ) < 1) hr hs
    (by simpa only [dist_comm q x, dist_comm q y] using abs_dist_sub_le x y q)
    (dist_triangle_left x y q)
  have hsmall := cos_comparisonAngleNegCurvature_of_pos (by norm_num : (0 : ℝ) < 1) hqu0 hqv0
    (by simpa only [dist_comm q u, dist_comm q v] using abs_dist_sub_le u v q)
    (dist_triangle_left u v q)
  simp only [sqrt_one, one_mul] at hbig hsmall
  have hden : 0 < sinh (dist q x) * sinh (dist q y) :=
    mul_pos (sinh_pos_iff.mpr hr) (sinh_pos_iff.mpr hs)
  have hcLaw : cosh (dist x y) = cosh (dist q x) * cosh (dist q y) -
      sinh (dist q x) * sinh (dist q y) * C := by
    have hh := (eq_div_iff hden.ne').mp hbig
    dsimp [C]
    nlinarith
  have hsmallDen : 0 < sinh (dist q u) * sinh (dist q v) :=
    mul_pos (sinh_pos_iff.mpr hqu0) (sinh_pos_iff.mpr hqv0)
  rw [hsmall] at hcos
  have hdLaw : cosh (t * dist q x) * cosh (t * dist q y) -
      sinh (t * dist q x) * sinh (t * dist q y) * C ≤ cosh (dist u v) := by
    have hh := (div_le_iff₀ hsmallDen).mp hcos
    rw [hqu, hqv] at hh
    nlinarith
  exact radial_side_lower_of_cosine_laws hr.le hs.le hrD hsD dist_nonneg dist_nonneg
    (hr.trans_le hrD) ⟨ht.1.le, ht.2.le⟩ (cos_le_one _) hcLaw hdLaw

end DifferentialGeometry.Geometry.Comparison.Toponogov
