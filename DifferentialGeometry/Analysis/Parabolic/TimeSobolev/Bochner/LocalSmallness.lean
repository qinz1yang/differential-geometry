import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Approximation.Slice
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped ENNReal NNReal

private theorem exists_pos_eLpNorm_two_Icc_lt {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hf : MemLp f 2 (volume.restrict (Icc 0 T))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ T ∧ ∀ s t : ℝ, Icc s t ⊆ Icc 0 T → t - s ≤ δ →
      eLpNorm f 2 (volume.restrict (Icc s t)) < ENNReal.ofReal ε := by
  obtain ⟨η, hη, hsmall⟩ := hf.eLpNorm_indicator_le
    (by norm_num) (by norm_num) (half_pos hε)
  refine ⟨min η T, lt_min hη hT, min_le_right _ _, ?_⟩
  intro s t hsub hlength
  have hmeasure : (volume.restrict (Icc 0 T)) (Icc s t) ≤ ENNReal.ofReal η := by
    calc
      (volume.restrict (Icc 0 T)) (Icc s t) ≤ volume (Icc s t) :=
        Measure.restrict_apply_le _ _
      _ = ENNReal.ofReal (t - s) := Real.volume_Icc
      _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal
        (hlength.trans (min_le_left _ _))
  have hnorm := hsmall (Icc s t) measurableSet_Icc hmeasure
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc,
    Measure.restrict_restrict_of_subset hsub] at hnorm
  exact hnorm.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε))

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem exists_pos_l2_slice_contraction_lt {X : Type*} [NormedAddCommGroup X]
    {T : ℝ} (hT : 0 < T) (f : timeL2 X T) (C : ℝ≥0) (hC : (C : ℝ) < 1) :
    ∃ δ > 0, δ ≤ T ∧ ∀ a b : ℝ, ∀ ha : 0 ≤ a, ∀ hbT : b ≤ T,
      0 ≤ b - a → b - a ≤ δ →
        (C : ℝ) * (1 + (b - a)) + Real.sqrt (1 + (b - a)) *
          ‖timeL2.slice f a b ha hbT‖ < 1 := by
  let ε := (1 - (C : ℝ)) / 4
  have hgap : 0 < 1 - (C : ℝ) := sub_pos.mpr hC
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨η, hη, hηT, hsmall⟩ :=
    exists_pos_eLpNorm_two_Icc_lt hT (Lp.memLp f) hε
  let δ := min η (min 1 ((1 - (C : ℝ)) / (4 * ((C : ℝ) + 1))))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨δ, hδ, (min_le_left _ _).trans hηT, ?_⟩
  intro a b ha hbT hd hdδ
  have hsub : Icc a b ⊆ Icc (0 : ℝ) T :=
    fun _ ht => ⟨ha.trans ht.1, ht.2.trans hbT⟩
  have hnorm := hsmall a b hsub (hdδ.trans (min_le_left _ _))
  have hmem : MemLp f 2 (volume.restrict (Icc a b)) :=
    (Lp.memLp f).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hn : ‖timeL2.slice f a b ha hbT‖ < ε := by
    rw [timeL2.norm_slice_eq]
    have h := (ENNReal.toReal_lt_toReal hmem.2.ne ENNReal.ofReal_ne_top).2 hnorm
    simpa only [ENNReal.toReal_ofReal hε.le] using h
  have hd1 : b - a ≤ 1 :=
    hdδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdC : b - a ≤ (1 - (C : ℝ)) / (4 * ((C : ℝ) + 1)) :=
    hdδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCd : (C : ℝ) * (b - a) ≤ ε := by
    have hden : 0 < 4 * ((C : ℝ) + 1) := by positivity
    have hprod := (le_div_iff₀ hden).mp hdC
    have hCnonneg : 0 ≤ (C : ℝ) := C.coe_nonneg
    have hmulnonneg : 0 ≤ (C : ℝ) * (b - a) := mul_nonneg hCnonneg hd
    dsimp only [ε]
    nlinarith
  have hsqrt : Real.sqrt (1 + (b - a)) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> linarith
  have hmul := mul_le_mul_of_nonneg_right hsqrt
    (norm_nonneg (timeL2.slice f a b ha hbT))
  dsimp only [ε] at hn hCd
  nlinarith

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
