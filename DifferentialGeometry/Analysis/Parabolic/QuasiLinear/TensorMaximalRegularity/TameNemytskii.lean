import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem timeL2_norm_le_of_ae_three_bound
    {T : ℝ} {X Y Z W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (h : timeL2 X T) (p : timeL2 Y T) (q : timeL2 Z T) (r : timeL2 W T)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbound : ∀ᵐ t ∂(timeMeasure T), ‖h t‖ ≤ A * ‖p t‖ + B * ‖q t‖ + C * ‖r t‖) :
    ‖h‖ ≤ A * ‖p‖ + B * ‖q‖ + C * ‖r‖ := by
  set Pf : ℝ → ℝ := fun t => ‖(p : ℝ → Y) t‖ with hPf
  set Qf : ℝ → ℝ := fun t => ‖(q : ℝ → Z) t‖ with hQf
  set Rf : ℝ → ℝ := fun t => ‖(r : ℝ → W) t‖ with hRf
  have hPm : AEStronglyMeasurable Pf (timeMeasure T) :=
    (Lp.aestronglyMeasurable p).norm
  have hQm : AEStronglyMeasurable Qf (timeMeasure T) :=
    (Lp.aestronglyMeasurable q).norm
  have hRm : AEStronglyMeasurable Rf (timeMeasure T) :=
    (Lp.aestronglyMeasurable r).norm
  have hAPm : AEStronglyMeasurable (A • Pf) (timeMeasure T) := hPm.const_smul A
  have hBQm : AEStronglyMeasurable (B • Qf) (timeMeasure T) := hQm.const_smul B
  have hCRm : AEStronglyMeasurable (C • Rf) (timeMeasure T) := hRm.const_smul C
  have hmono : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hbound] with t ht
    have happ : (A • Pf + B • Qf + C • Rf) t = A * ‖p t‖ + B * ‖q t‖ + C * ‖r t‖ := by
      simp [hPf, hQf, hRf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hge : 0 ≤ (A • Pf + B • Qf + C • Rf) t := by
      rw [happ]
      exact add_nonneg
        (add_nonneg (mul_nonneg hA (norm_nonneg _)) (mul_nonneg hB (norm_nonneg _)))
        (mul_nonneg hC (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hge, happ]
    exact ht
  have htri : eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf) 2 (timeMeasure T) + eLpNorm (B • Qf) 2 (timeMeasure T)
        + eLpNorm (C • Rf) 2 (timeMeasure T) := by
    have step1 : eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) ≤
        eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) + eLpNorm (C • Rf) 2 (timeMeasure T) :=
      eLpNorm_add_le (hAPm.add hBQm) hCRm (by norm_num)
    have step2 : eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) ≤
        eLpNorm (A • Pf) 2 (timeMeasure T) + eLpNorm (B • Qf) 2 (timeMeasure T) :=
      eLpNorm_add_le hAPm hBQm (by norm_num)
    exact le_trans step1 (add_le_add step2 le_rfl)
  have hscaleP : eLpNorm (A • Pf) 2 (timeMeasure T) =
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA]
  have hscaleQ : eLpNorm (B • Qf) 2 (timeMeasure T) =
      ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hB]
  have hscaleR : eLpNorm (C • Rf) 2 (timeMeasure T) =
      ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hC]
  have hp_top : eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp p).2.ne
  have hq_top : eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp q).2.ne
  have hr_top : eLpNorm (r : ℝ → W) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp r).2.ne
  have hAp_ne : ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top
  have hBq_ne : ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top
  have hCr_ne : ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hr_top
  have hfinal : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
        ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) +
        ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) := by
    calc eLpNorm (h : ℝ → X) 2 (timeMeasure T)
        ≤ eLpNorm (A • Pf) 2 (timeMeasure T) + eLpNorm (B • Qf) 2 (timeMeasure T)
            + eLpNorm (C • Rf) 2 (timeMeasure T) := hmono.trans htri
      _ = _ := by rw [hscaleP, hscaleQ, hscaleR]
  have hrhs_ne : ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
      ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) +
      ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hAp_ne, hBq_ne⟩, hCr_ne⟩
  have hnormh : ‖h‖ = (eLpNorm (h : ℝ → X) 2 (timeMeasure T)).toReal := rfl
  have hnormp : ‖p‖ = (eLpNorm (p : ℝ → Y) 2 (timeMeasure T)).toReal := rfl
  have hnormq : ‖q‖ = (eLpNorm (q : ℝ → Z) 2 (timeMeasure T)).toReal := rfl
  have hnormr : ‖r‖ = (eLpNorm (r : ℝ → W) 2 (timeMeasure T)).toReal := rfl
  rw [hnormh, hnormp, hnormq, hnormr]
  refine le_trans (ENNReal.toReal_mono hrhs_ne hfinal) ?_
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hAp_ne, hBq_ne⟩) hCr_ne,
    ENNReal.toReal_add hAp_ne hBq_ne,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hB, ENNReal.toReal_ofReal hC]

variable {T : ℝ}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem nemytskiiTame_time_bound
    (ι : X →L[ℝ] H) {N : X → Y} {K : ℝ≥0} {Minf Dinf : ℝ}
    (hMinf : 0 ≤ Minf) (hDinf : 0 ≤ Dinf)
    (htame : ∀ (x x' : X),
      ‖N x - N x'‖ ≤
        (K : ℝ) * ((1 + max ‖ι x‖ ‖ι x'‖) * ‖x - x'‖ + max ‖x‖ ‖x'‖ * ‖ι (x - x')‖))
    (u v : timeL2 X T) (w w' : timeL2 Y T)
    (hw : w =ᵐ[timeMeasure T] fun t => N (u t))
    (hw' : w' =ᵐ[timeMeasure T] fun t => N (v t))
    (huM : ∀ᵐ t ∂(timeMeasure T), ‖ι (u t)‖ ≤ Minf)
    (hvM : ∀ᵐ t ∂(timeMeasure T), ‖ι (v t)‖ ≤ Minf)
    (hdiff : ∀ᵐ t ∂(timeMeasure T), ‖ι (u t - v t)‖ ≤ Dinf) :
    ‖w - w'‖ ≤
      (K : ℝ) * (1 + Minf) * ‖u - v‖ + (K : ℝ) * Dinf * ‖u‖ + (K : ℝ) * Dinf * ‖v‖ := by
  have hbound : ∀ᵐ t ∂(timeMeasure T),
      ‖(w - w') t‖ ≤
        ((K : ℝ) * (1 + Minf)) * ‖(u - v) t‖
          + ((K : ℝ) * Dinf) * ‖u t‖ + ((K : ℝ) * Dinf) * ‖v t‖ := by
    filter_upwards [Lp.coeFn_sub w w', hw, hw', Lp.coeFn_sub u v, huM, hvM, hdiff]
      with t htw htwu htwv htuv htuM htvM htdiff
    have huvnorm : ‖(u - v) t‖ = ‖u t - v t‖ := by rw [htuv, Pi.sub_apply]
    rw [htw, Pi.sub_apply, htwu, htwv, huvnorm]
    have h1 : (1 + max ‖ι (u t)‖ ‖ι (v t)‖) * ‖u t - v t‖ ≤ (1 + Minf) * ‖u t - v t‖ :=
      mul_le_mul_of_nonneg_right (by linarith [max_le htuM htvM]) (norm_nonneg _)
    have hmaxsum : max ‖u t‖ ‖v t‖ ≤ ‖u t‖ + ‖v t‖ :=
      max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
    have h2 : max ‖u t‖ ‖v t‖ * ‖ι (u t - v t)‖ ≤ (‖u t‖ + ‖v t‖) * Dinf :=
      mul_le_mul hmaxsum htdiff (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    calc ‖N (u t) - N (v t)‖
        ≤ (K : ℝ) * ((1 + max ‖ι (u t)‖ ‖ι (v t)‖) * ‖u t - v t‖
            + max ‖u t‖ ‖v t‖ * ‖ι (u t - v t)‖) := htame (u t) (v t)
      _ ≤ (K : ℝ) * ((1 + Minf) * ‖u t - v t‖ + (‖u t‖ + ‖v t‖) * Dinf) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) K.coe_nonneg
      _ = ((K : ℝ) * (1 + Minf)) * ‖u t - v t‖
            + ((K : ℝ) * Dinf) * ‖u t‖ + ((K : ℝ) * Dinf) * ‖v t‖ := by ring
  have hA : 0 ≤ (K : ℝ) * (1 + Minf) := mul_nonneg K.coe_nonneg (by linarith)
  have hBC : 0 ≤ (K : ℝ) * Dinf := mul_nonneg K.coe_nonneg hDinf
  exact timeL2_norm_le_of_ae_three_bound (w - w') (u - v) u v hA hBC hBC hbound

theorem nemytskiiTame_time_bound_L2
    (ι : X →L[ℝ] H) {N : X → Y} {K : ℝ≥0} {Minf Dinf M₂ : ℝ}
    (hMinf : 0 ≤ Minf) (hDinf : 0 ≤ Dinf)
    (htame : ∀ (x x' : X),
      ‖N x - N x'‖ ≤
        (K : ℝ) * ((1 + max ‖ι x‖ ‖ι x'‖) * ‖x - x'‖ + max ‖x‖ ‖x'‖ * ‖ι (x - x')‖))
    (u v : timeL2 X T) (w w' : timeL2 Y T)
    (hw : w =ᵐ[timeMeasure T] fun t => N (u t))
    (hw' : w' =ᵐ[timeMeasure T] fun t => N (v t))
    (huM : ∀ᵐ t ∂(timeMeasure T), ‖ι (u t)‖ ≤ Minf)
    (hvM : ∀ᵐ t ∂(timeMeasure T), ‖ι (v t)‖ ≤ Minf)
    (hdiff : ∀ᵐ t ∂(timeMeasure T), ‖ι (u t - v t)‖ ≤ Dinf)
    (hu2 : ‖u‖ ≤ M₂) (hv2 : ‖v‖ ≤ M₂) :
    ‖w - w'‖ ≤ (K : ℝ) * (1 + Minf) * ‖u - v‖ + 2 * ((K : ℝ) * Dinf * M₂) := by
  refine le_trans
    (nemytskiiTame_time_bound ι hMinf hDinf htame u v w w' hw hw' huM hvM hdiff) ?_
  have hKD : 0 ≤ (K : ℝ) * Dinf := mul_nonneg K.coe_nonneg hDinf
  have hu : (K : ℝ) * Dinf * ‖u‖ ≤ (K : ℝ) * Dinf * M₂ := mul_le_mul_of_nonneg_left hu2 hKD
  have hv : (K : ℝ) * Dinf * ‖v‖ ≤ (K : ℝ) * Dinf * M₂ := mul_le_mul_of_nonneg_left hv2 hKD
  linarith

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
