import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem timeL2_coeFn_ae_eq_of_eq
    {T : ℝ} {X : Type*} [NormedAddCommGroup X] {f g : timeL2 X T} (h : f = g) :
    ⇑f =ᵐ[timeMeasure T] ⇑g := by
  cases h
  exact Filter.EventuallyEq.rfl

theorem timeL2_norm_le_of_ae_mixed_bound
    {T : ℝ} {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z] (h : timeL2 X T) (p : timeL2 Y T) (q : timeL2 Z T) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ᵐ t ∂(timeMeasure T), ‖h t‖ ≤ A * ‖p t‖ + B * ‖q t‖) :
    ‖h‖ ≤ A * ‖p‖ + B * ‖q‖ := by
  set Pf : ℝ → ℝ := fun t => ‖(p : ℝ → Y) t‖ with hPf
  set Qf : ℝ → ℝ := fun t => ‖(q : ℝ → Z) t‖ with hQf
  have hPm : AEStronglyMeasurable Pf (timeMeasure T) :=
    (Lp.aestronglyMeasurable p).norm
  have hQm : AEStronglyMeasurable Qf (timeMeasure T) :=
    (Lp.aestronglyMeasurable q).norm
  have hAPm : AEStronglyMeasurable (A • Pf) (timeMeasure T) := hPm.const_smul A
  have hBQm : AEStronglyMeasurable (B • Qf) (timeMeasure T) := hQm.const_smul B
  have hmono : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hbound] with t ht
    have happ : (A • Pf + B • Qf) t = A * ‖p t‖ + B * ‖q t‖ := by
      simp [hPf, hQf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hge : 0 ≤ (A • Pf + B • Qf) t := by
      rw [happ]
      exact add_nonneg (mul_nonneg hA (norm_nonneg _)) (mul_nonneg hB (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hge, happ]
    exact ht
  have htri : eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf) 2 (timeMeasure T) + eLpNorm (B • Qf) 2 (timeMeasure T) :=
    eLpNorm_add_le hAPm hBQm (by norm_num)
  have hscaleP : eLpNorm (A • Pf) 2 (timeMeasure T) =
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA]
  have hscaleQ : eLpNorm (B • Qf) 2 (timeMeasure T) =
      ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hB]
  have hfinal : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
        ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    calc
      eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
          eLpNorm (A • Pf) 2 (timeMeasure T) + eLpNorm (B • Qf) 2 (timeMeasure T) :=
        hmono.trans htri
      _ = _ := by rw [hscaleP, hscaleQ]
  have hp_top : eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp p).2.ne
  have hq_top : eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp q).2.ne
  have hnormh : ‖h‖ = (eLpNorm (h : ℝ → X) 2 (timeMeasure T)).toReal := rfl
  have hnormp : ‖p‖ = (eLpNorm (p : ℝ → Y) 2 (timeMeasure T)).toReal := rfl
  have hnormq : ‖q‖ = (eLpNorm (q : ℝ → Z) 2 (timeMeasure T)).toReal := rfl
  have hrhs_ne : ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
      ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top⟩
  rw [hnormh, hnormp, hnormq]
  refine le_trans (ENNReal.toReal_mono hrhs_ne hfinal) ?_
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
    ENNReal.toReal_ofReal hB]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
