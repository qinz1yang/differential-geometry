import DifferentialGeometry.Geometry.Comparison.ModelAngle
import Mathlib.Analysis.SpecialFunctions.Arcosh

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

noncomputable def modelSideNegCurvature (κ a b θ : ℝ) : ℝ :=
  if κ = 0 then sqrt (a ^ 2 + b ^ 2 - 2 * a * b * cos θ) else
    arcosh (cosh (sqrt κ * a) * cosh (sqrt κ * b) -
      sinh (sqrt κ * a) * sinh (sqrt κ * b) * cos θ) / sqrt κ

private theorem hyperbolic_cosine_law_ge_one {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 ≤ cosh a * cosh b - sinh a * sinh b * cos θ := by
  have hmul := mul_le_mul_of_nonneg_left (cos_le_one θ)
    (mul_nonneg (sinh_nonneg_iff.mpr ha) (sinh_nonneg_iff.mpr hb))
  have h := one_le_cosh (a - b)
  rw [cosh_sub] at h
  linarith

theorem modelSideNegCurvature_nonneg {κ a b θ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ modelSideNegCurvature κ a b θ := by
  by_cases hk : κ = 0
  · rw [modelSideNegCurvature, ite_eq_left hk]
    exact sqrt_nonneg _
  · rw [modelSideNegCurvature, ite_eq_right hk]
    exact div_nonneg (arcosh_nonneg (hyperbolic_cosine_law_ge_one
      (mul_nonneg (sqrt_nonneg κ) ha) (mul_nonneg (sqrt_nonneg κ) hb))) (sqrt_nonneg κ)

theorem cosh_sqrt_mul_modelSideNegCurvature {κ a b θ : ℝ}
    (hκ : 0 < κ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cosh (sqrt κ * modelSideNegCurvature κ a b θ) =
      cosh (sqrt κ * a) * cosh (sqrt κ * b) -
        sinh (sqrt κ * a) * sinh (sqrt κ * b) * cos θ := by
  rw [modelSideNegCurvature, ite_eq_right hκ.ne']
  have hs : sqrt κ ≠ 0 := (sqrt_pos.mpr hκ).ne'
  rw [mul_div_cancel₀ _ hs]
  exact cosh_arcosh (hyperbolic_cosine_law_ge_one
    (mul_nonneg (sqrt_nonneg κ) ha) (mul_nonneg (sqrt_nonneg κ) hb))

theorem modelSideNegCurvature_pi {κ a b : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    modelSideNegCurvature κ a b Real.pi = a + b := by
  by_cases hk : κ = 0
  · rw [modelSideNegCurvature, ite_eq_left hk, cos_pi]
    have heq : a ^ 2 + b ^ 2 - 2 * a * b * (-1) = (a + b) ^ 2 := by ring
    rw [heq, sqrt_sq (add_nonneg ha hb)]
  · have hs : 0 < sqrt κ := sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hk))
    rw [modelSideNegCurvature, ite_eq_right hk, cos_pi, mul_neg_one, sub_neg_eq_add,
      ← cosh_add, ← mul_add, arcosh_cosh (mul_nonneg hs.le (add_nonneg ha hb))]
    exact mul_div_cancel_left₀ _ hs.ne'

theorem modelSideNegCurvature_zero_angle {κ a b : ℝ} (hκ : 0 ≤ κ) :
    modelSideNegCurvature κ a b 0 = |a - b| := by
  by_cases hk : κ = 0
  · rw [modelSideNegCurvature, ite_eq_left hk, cos_zero, mul_one]
    have heq : a ^ 2 + b ^ 2 - 2 * a * b = (a - b) ^ 2 := by ring
    rw [heq, sqrt_sq_eq_abs]
  · have hs : 0 < sqrt κ := sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hk))
    rw [modelSideNegCurvature, ite_eq_right hk, cos_zero, mul_one, ← cosh_sub,
      ← mul_sub, ← cosh_abs (sqrt κ * (a - b)), arcosh_cosh (abs_nonneg _),
      abs_mul, abs_of_pos hs]
    exact mul_div_cancel_left₀ _ hs.ne'

theorem modelSideNegCurvature_mono_angle {κ a b θ φ : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hθ : 0 ≤ θ) (hφ : φ ≤ Real.pi) (hle : θ ≤ φ) :
    modelSideNegCurvature κ a b θ ≤ modelSideNegCurvature κ a b φ := by
  have hcos := cos_le_cos_of_nonneg_of_le_pi hθ hφ hle
  by_cases hk : κ = 0
  · simp only [modelSideNegCurvature, ite_eq_left hk]
    apply sqrt_le_sqrt
    have h := mul_le_mul_of_nonneg_left hcos (show 0 ≤ 2 * a * b by positivity)
    linarith
  · have hs : 0 < sqrt κ := sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hk))
    simp only [modelSideNegCurvature, ite_eq_right hk]
    apply div_le_div_of_nonneg_right _ hs.le
    apply (arcosh_le_arcosh
      (lt_of_lt_of_le zero_lt_one (hyperbolic_cosine_law_ge_one (mul_nonneg hs.le ha) (mul_nonneg hs.le hb)))
      (lt_of_lt_of_le zero_lt_one (hyperbolic_cosine_law_ge_one (mul_nonneg hs.le ha) (mul_nonneg hs.le hb)))).mpr
    have h := mul_le_mul_of_nonneg_left hcos
      (mul_nonneg (sinh_nonneg_iff.mpr (mul_nonneg hs.le ha))
        (sinh_nonneg_iff.mpr (mul_nonneg hs.le hb)))
    linarith

theorem modelSideNegCurvature_mem_Icc {κ a b θ : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    modelSideNegCurvature κ a b θ ∈ Icc |a - b| (a + b) := by
  constructor
  · rw [← modelSideNegCurvature_zero_angle (a := a) (b := b) hκ]
    exact modelSideNegCurvature_mono_angle hκ ha hb le_rfl hθ.2 hθ.1
  · rw [← modelSideNegCurvature_pi (a := a) (b := b) hκ ha hb]
    exact modelSideNegCurvature_mono_angle hκ ha hb hθ.1 le_rfl hθ.2

theorem modelSideNegCurvature_zero_sq {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    modelSideNegCurvature 0 a b θ ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * cos θ := by
  rw [modelSideNegCurvature, ite_eq_left rfl]
  apply sq_sqrt
  have h := mul_le_mul_of_nonneg_left (cos_le_one θ) (show 0 ≤ 2 * a * b by positivity)
  nlinarith [sq_nonneg (a - b)]

theorem modelSideNegCurvature_comparisonAngle {κ a b c : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b)
    (hlower : |a - b| ≤ c) (hupper : c ≤ a + b) :
    modelSideNegCurvature κ a b (comparisonAngleNegCurvature κ a b c) = c := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hlower
  by_cases hk : κ = 0
  · subst κ
    rw [modelSideNegCurvature, ite_eq_left rfl, comparisonAngleNegCurvature_zero,
      cos_comparisonAngle ha hb hlower hupper,
      mul_div_cancel₀ _ (show 2 * a * b ≠ 0 by positivity), sub_sub_cancel, sqrt_sq hc]
  · have hkpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hk)
    have hs : 0 < sqrt κ := sqrt_pos.mpr hkpos
    have hden : sinh (sqrt κ * a) * sinh (sqrt κ * b) ≠ 0 :=
      (mul_pos (sinh_pos_iff.mpr (mul_pos hs ha)) (sinh_pos_iff.mpr (mul_pos hs hb))).ne'
    rw [modelSideNegCurvature, ite_eq_right hk,
      cos_comparisonAngleNegCurvature_of_pos hkpos ha hb hlower hupper,
      mul_div_cancel₀ _ hden, sub_sub_cancel, arcosh_cosh (mul_nonneg hs.le hc)]
    exact mul_div_cancel_left₀ _ hs.ne'

theorem comparisonAngleNegCurvature_modelSide {κ a b θ : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    comparisonAngleNegCurvature κ a b (modelSideNegCurvature κ a b θ) = θ := by
  by_cases hk : κ = 0
  · subst κ
    rw [comparisonAngleNegCurvature_zero, comparisonAngle, comparisonCosine, modelSideNegCurvature_zero_sq ha.le hb.le,
      sub_sub_cancel, mul_div_cancel_left₀ _ (show 2 * a * b ≠ 0 by positivity), arccos_cos hθ.1 hθ.2]
  · have hkpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hk)
    have hs : 0 < sqrt κ := sqrt_pos.mpr hkpos
    have hden : sinh (sqrt κ * a) * sinh (sqrt κ * b) ≠ 0 :=
      (mul_pos (sinh_pos_iff.mpr (mul_pos hs ha)) (sinh_pos_iff.mpr (mul_pos hs hb))).ne'
    rw [comparisonAngleNegCurvature, ite_eq_right hk,
      cosh_sqrt_mul_modelSideNegCurvature hkpos ha.le hb.le,
      sub_sub_cancel, mul_div_cancel_left₀ _ hden, arccos_cos hθ.1 hθ.2]

theorem modelSideNegCurvature_comm (κ a b θ : ℝ) :
    modelSideNegCurvature κ a b θ = modelSideNegCurvature κ b a θ := by
  unfold modelSideNegCurvature
  split
  · congr 1
    ring
  · congr 2
    ring

theorem modelSideNegCurvature_zero_left {κ b θ : ℝ} (hκ : 0 ≤ κ) (hb : 0 ≤ b) :
    modelSideNegCurvature κ 0 b θ = b := by
  by_cases hk : κ = 0
  · simp only [modelSideNegCurvature, ite_eq_left hk, zero_pow (by decide : 2 ≠ 0),
      zero_add, mul_zero, zero_mul, sub_zero]
    exact sqrt_sq hb
  · have hs : 0 < sqrt κ := sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hk))
    simp only [modelSideNegCurvature, ite_eq_right hk, mul_zero, cosh_zero, one_mul,
      sinh_zero, zero_mul, sub_zero, arcosh_cosh (mul_nonneg hs.le hb)]
    exact mul_div_cancel_left₀ _ hs.ne'

theorem modelSideNegCurvature_zero_right {κ a θ : ℝ} (hκ : 0 ≤ κ) (ha : 0 ≤ a) :
    modelSideNegCurvature κ a 0 θ = a := by
  rw [modelSideNegCurvature_comm]
  exact modelSideNegCurvature_zero_left hκ ha

theorem tendsto_modelSideNegCurvature {I : Type*} {l : Filter I}
    {a b θ : I → ℝ} {κ a₀ b₀ θ₀ : ℝ} (hκ : 0 ≤ κ)
    (ha : Filter.Tendsto a l (nhds a₀)) (hb : Filter.Tendsto b l (nhds b₀))
    (hθ : Filter.Tendsto θ l (nhds θ₀)) (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) :
    Filter.Tendsto (fun i => modelSideNegCurvature κ (a i) (b i) (θ i)) l
      (nhds (modelSideNegCurvature κ a₀ b₀ θ₀)) := by
  by_cases hk : κ = 0
  · have h := (((ha.pow 2).add (hb.pow 2)).sub
      (((ha.const_mul 2).mul hb).mul ((continuous_cos.tendsto _).comp hθ))).sqrt
    simpa only [modelSideNegCurvature, ite_eq_left hk, Function.comp_def] using h
  · have hs : 0 < sqrt κ := sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hk))
    have hka := ha.const_mul (sqrt κ)
    have hkb := hb.const_mul (sqrt κ)
    have hnum := ((continuous_cosh.tendsto _).comp hka).mul ((continuous_cosh.tendsto _).comp hkb)
    have hprod := (((continuous_sinh.tendsto _).comp hka).mul
      ((continuous_sinh.tendsto _).comp hkb)).mul ((continuous_cos.tendsto _).comp hθ)
    have hinner := hnum.sub hprod
    have hge := hyperbolic_cosine_law_ge_one (θ := θ₀)
      (mul_nonneg hs.le ha₀) (mul_nonneg hs.le hb₀)
    have hlog := (hinner.add ((hinner.pow 2).sub tendsto_const_nhds).sqrt).log
      (show cosh (sqrt κ * a₀) * cosh (sqrt κ * b₀) -
        sinh (sqrt κ * a₀) * sinh (sqrt κ * b₀) * cos θ₀ +
        sqrt ((cosh (sqrt κ * a₀) * cosh (sqrt κ * b₀) -
          sinh (sqrt κ * a₀) * sinh (sqrt κ * b₀) * cos θ₀) ^ 2 - 1) ≠ 0 by
        have hp := zero_lt_one.trans_le hge
        positivity)
    simpa only [modelSideNegCurvature, ite_eq_right hk, arcosh, Function.comp_def] using
      hlog.div_const (sqrt κ)

end DifferentialGeometry.Geometry.Comparison.Toponogov
