import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem integral_mul_bilinear_sub_translate
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B)
    {f : ℝ → X} (hf : MemLp f 2 volume)
    {ζ : ℝ → ℝ} (hζ : MemLp ζ ∞ volume) (s : ℝ) :
    2 * (∫ t, ζ t * B (f t) (f (t + s) - f t)) =
      (∫ t, (ζ (t - s) - ζ t) * B (f t) (f t)) -
        ∫ t, ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
  have hfshift : MemLp (fun t => f (t + s)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume s)
  have hζshift : MemLp (fun t => ζ (t - s)) ∞ volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hζ.comp_measurePreserving (measurePreserving_add_right volume (-s))
  have hint {u v : ℝ → X} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
      Integrable (fun t => B (u t) (v t)) volume :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable (fun _ : ℝ => B)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl) hu hv
  have hζsq : Integrable (fun t => ζ t * B (f t) (f t)) volume :=
    (hint hf hf).mul_of_top_right hζ
  have hζsqs : Integrable (fun t => ζ t * B (f (t + s)) (f (t + s))) volume :=
    (hint hfshift hfshift).mul_of_top_right hζ
  have hζsqd : Integrable (fun t => ζ t * B (f (t + s) - f t) (f (t + s) - f t)) volume :=
    (hint (hfshift.sub hf) (hfshift.sub hf)).mul_of_top_right hζ
  have hζshsq : Integrable (fun t => ζ (t - s) * B (f t) (f t)) volume :=
    (hint hf hf).mul_of_top_right hζshift
  have hζsub : Integrable (fun t => ζ t * B (f (t + s)) (f (t + s)) - ζ t * B (f t) (f t))
      volume := hζsqs.sub hζsq
  have hsymm (x y : X) : B y x = B x y := by
    exact congrArg (fun L : X →L[ℝ] X →L[ℝ] ℝ => L x y) hB
  have hnorm : ∀ t, 2 * (ζ t * B (f t) (f (t + s) - f t)) =
      ζ t * B (f (t + s)) (f (t + s)) - ζ t * B (f t) (f t) -
        ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
    intro t
    simp only [map_sub, sub_apply]
    rw [hsymm (f t) (f (t + s))]
    ring
  have htranslate : (∫ t, ζ t * B (f (t + s)) (f (t + s))) =
      ∫ t, ζ (t - s) * B (f t) (f t) := by
    conv_lhs =>
      rw [← integral_add_right_eq_self (fun t => ζ t * B (f (t + s)) (f (t + s))) (-s)]
    simp only [neg_add_cancel_right, sub_eq_add_neg]
  rw [← integral_const_mul]
  calc
    _ = ∫ t, ζ t * B (f (t + s)) (f (t + s)) - ζ t * B (f t) (f t) -
        ζ t * B (f (t + s) - f t) (f (t + s) - f t) :=
      integral_congr_ae (Eventually.of_forall hnorm)
    _ = (∫ t, ζ t * B (f (t + s)) (f (t + s))) - (∫ t, ζ t * B (f t) (f t)) -
        ∫ t, ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
      rw [integral_sub hζsub hζsqd, integral_sub hζsqs hζsq]
    _ = _ := by
      rw [htranslate, ← integral_sub hζshsq hζsq]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      ring

theorem integral_mul_bilinear_sub_translate_le
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    {f : ℝ → X} (hf : MemLp f 2 volume)
    {ζ : ℝ → ℝ} (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t, 0 ≤ ζ t) (s : ℝ) :
    (∫ t, ζ t * B (f t) (f (t + s) - f t)) ≤
      (1 / 2) * ∫ t, (ζ (t - s) - ζ t) * B (f t) (f t) := by
  have hid := integral_mul_bilinear_sub_translate B hB hf hζ s
  have hn : 0 ≤ ∫ t, ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
    apply integral_nonneg_of_ae
    filter_upwards [hζpos] with t ht
    exact mul_nonneg ht (hBpos _)
  linarith

theorem integral_mul_bilinear_diffQuot_le
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    {f : ℝ → X} (hf : MemLp f 2 volume)
    {ζ : ℝ → ℝ} (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) {s : ℝ} (hs : 0 < s) :
    (∫ t, ζ t * B (f t) (s⁻¹ • (f (t + s) - f t))) ≤
      ((K : ℝ) / 2) * ∫ t, B (f t) (f t) := by
  have hbase := integral_mul_bilinear_sub_translate_le B hB hBpos hf hζ hζpos s
  have hdiag : Integrable (fun t => B (f t) (f t)) volume :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable (fun _ : ℝ => B)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl) hf hf
  have hζshift : MemLp (fun t => ζ (t - s)) ∞ volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hζ.comp_measurePreserving (measurePreserving_add_right volume (-s))
  have hdiff : Integrable (fun t => (ζ (t - s) - ζ t) * B (f t) (f t)) volume :=
    hdiag.mul_of_top_right (hζshift.sub hζ)
  have hb : (∫ t, (ζ (t - s) - ζ t) * B (f t) (f t)) ≤
      (K : ℝ) * s * ∫ t, B (f t) (f t) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hdiff (hdiag.const_mul _)
    filter_upwards [] with t
    apply mul_le_mul_of_nonneg_right _ (hBpos _)
    have h := hζlip.dist_le_mul (t - s) t
    simp only [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hs] at h
    exact (le_abs_self _).trans h
  have hid : (∫ t, ζ t * B (f t) (s⁻¹ • (f (t + s) - f t))) =
      s⁻¹ * ∫ t, ζ t * B (f t) (f (t + s) - f t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [map_smul, smul_eq_mul]
    ring
  rw [hid]
  have hbound : (∫ t, ζ t * B (f t) (f (t + s) - f t)) ≤
      s * (((K : ℝ) / 2) * ∫ t, B (f t) (f t)) := by nlinarith
  exact (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hs.le)).trans_eq
    (by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul])

theorem integral_mul_bilinear_diffQuot_ge
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBneg : ∀ x, B x x ≤ 0)
    {f : ℝ → X} (hf : MemLp f 2 volume)
    {ζ : ℝ → ℝ} (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) {s : ℝ} (hs : 0 < s) :
    ((K : ℝ) / 2) * (∫ t, B (f t) (f t)) ≤
      ∫ t, ζ t * B (f t) (s⁻¹ • (f (t + s) - f t)) := by
  have hsym : (-B).flip = -B := by
    ext x y
    have h := congrArg (fun L : X →L[ℝ] X →L[ℝ] ℝ => L x y) hB
    change -B y x = -B x y
    exact congrArg Neg.neg h
  have hpos : ∀ x, 0 ≤ (-B) x x := by
    intro x
    change 0 ≤ -B x x
    exact neg_nonneg.mpr (hBneg x)
  have h := integral_mul_bilinear_diffQuot_le (-B) hsym hpos hf hζ hζpos hζlip hs
  simp only [neg_apply, mul_neg, integral_neg] at h
  linarith

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
