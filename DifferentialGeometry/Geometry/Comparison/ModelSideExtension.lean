import DifferentialGeometry.Geometry.Comparison.ModelSide

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem hyperbolic_cosine_extension_identity {A H B C : ℝ}
    (hA : sinh A ≠ 0) (hH : sinh H ≠ 0) (hC : sinh C ≠ 0) :
    cosh A * cosh B - sinh A * sinh B *
      ((cosh A * cosh H - cosh C) / (sinh A * sinh H)) =
    cosh C * cosh (B - H) + sinh C * sinh (B - H) *
      ((cosh C * cosh H - cosh A) / (sinh C * sinh H)) := by
  rw [show B = (B - H) + H by ring, cosh_add, sinh_add]
  have heq : B - H + H - H = B - H := by ring
  rw [heq]
  field_simp
  ring_nf
  rw [cosh_sq]
  ring

theorem modelSideNegCurvature_extension_identity {κ a b h c : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hh : 0 < h) (hc : 0 < c) (hhb : h < b)
    (hlower : |a - h| ≤ c) (hupper : c ≤ a + h) :
    modelSideNegCurvature κ a b (comparisonAngleNegCurvature κ a h c) =
      modelSideNegCurvature κ c (b - h)
        (Real.pi - comparisonAngleNegCurvature κ c h a) := by
  have hb : 0 < b := hh.trans hhb
  have hbh : 0 < b - h := sub_pos.mpr hhb
  have hlow := abs_le.mp hlower
  have hrotate : |c - h| ≤ a := abs_le.mpr ⟨by linarith, by linarith⟩
  have hrotate' : a ≤ c + h := by linarith
  by_cases hk : κ = 0
  · subst κ
    apply (sq_eq_sq₀ (modelSideNegCurvature_nonneg ha.le hb.le)
      (modelSideNegCurvature_nonneg hc.le hbh.le)).mp
    rw [modelSideNegCurvature_zero_sq ha.le hb.le,
      modelSideNegCurvature_zero_sq hc.le hbh.le,
      comparisonAngleNegCurvature_zero, comparisonAngleNegCurvature_zero,
      cos_pi_sub, cos_comparisonAngle ha hh hlower hupper,
      cos_comparisonAngle hc hh hrotate hrotate']
    field_simp
    ring
  · have hkpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hk)
    have hs : 0 < sqrt κ := sqrt_pos.mpr hkpos
    apply mul_left_cancel₀ hs.ne'
    apply cosh_injOn
      (mul_nonneg hs.le (modelSideNegCurvature_nonneg ha.le hb.le))
      (mul_nonneg hs.le (modelSideNegCurvature_nonneg hc.le hbh.le))
    rw [cosh_sqrt_mul_modelSideNegCurvature hkpos ha.le hb.le,
      cosh_sqrt_mul_modelSideNegCurvature hkpos hc.le hbh.le,
      cos_pi_sub, cos_comparisonAngleNegCurvature_of_pos hkpos ha hh hlower hupper,
      cos_comparisonAngleNegCurvature_of_pos hkpos hc hh hrotate hrotate', mul_sub]
    have hA : sinh (sqrt κ * a) ≠ 0 := (sinh_pos_iff.mpr (mul_pos hs ha)).ne'
    have hH : sinh (sqrt κ * h) ≠ 0 := (sinh_pos_iff.mpr (mul_pos hs hh)).ne'
    have hC : sinh (sqrt κ * c) ≠ 0 := (sinh_pos_iff.mpr (mul_pos hs hc)).ne'
    simpa only [mul_neg, sub_neg_eq_add] using
      hyperbolic_cosine_extension_identity (B := sqrt κ * b) hA hH hC

theorem modelSideNegCurvature_le_of_adjacent_comparisons {κ a b h c α β : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hh : 0 < h) (hc : 0 < c) (hhb : h < b)
    (hlower : |a - h| ≤ c) (hupper : c ≤ a + h)
    (hα : α ∈ Icc (0 : ℝ) Real.pi) (hβ : β ∈ Icc (0 : ℝ) Real.pi)
    (hfirst : comparisonAngleNegCurvature κ a h c ≤ α)
    (hsecond : β + comparisonAngleNegCurvature κ c h a ≤ Real.pi) :
    modelSideNegCurvature κ c (b - h) β ≤ modelSideNegCurvature κ a b α := by
  have hθ := comparisonAngleNegCurvature_mem_Icc κ c h a
  calc
    modelSideNegCurvature κ c (b - h) β ≤ modelSideNegCurvature κ c (b - h)
        (Real.pi - comparisonAngleNegCurvature κ c h a) :=
      modelSideNegCurvature_mono_angle hκ hc.le (sub_nonneg.mpr hhb.le)
        hβ.1 (by linarith [hθ.1]) (by linarith)
    _ = modelSideNegCurvature κ a b (comparisonAngleNegCurvature κ a h c) :=
      (modelSideNegCurvature_extension_identity hκ ha hh hc hhb hlower hupper).symm
    _ ≤ modelSideNegCurvature κ a b α := modelSideNegCurvature_mono_angle hκ ha.le
      (hh.trans hhb).le (comparisonAngleNegCurvature_mem_Icc κ a h c).1 hα.2 hfirst

end DifferentialGeometry.Geometry.Comparison.Toponogov
