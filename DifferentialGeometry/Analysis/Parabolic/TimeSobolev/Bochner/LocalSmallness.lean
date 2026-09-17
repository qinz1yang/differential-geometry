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

theorem exists_pos_l2_slice_contraction_lt_of_norm_sub_lt
    {X : Type*} [NormedAddCommGroup X] {T : ℝ} (hT : 0 < T)
    (f : timeL2 X T) (C : ℝ≥0) (hC : (C : ℝ) < 1) :
    ∃ δ > 0, δ ≤ T ∧ ∃ ε > 0, ∃ q ∈ Ico (0 : ℝ) 1,
      ∀ g : timeL2 X T, ‖g - f‖ < ε →
        ∀ a b : ℝ, ∀ ha : 0 ≤ a, ∀ hbT : b ≤ T,
          0 ≤ b - a → b - a ≤ δ →
            (C : ℝ) * (1 + (b - a)) + Real.sqrt (1 + (b - a)) *
              ‖timeL2.slice g a b ha hbT‖ ≤ q := by
  let D : ℝ≥0 := (1 + C) / 2
  have hD : (D : ℝ) = (1 + (C : ℝ)) / 2 := by simp [D]
  have hD1 : (D : ℝ) < 1 := by rw [hD]; linarith
  obtain ⟨η, hη, hηT, hsmall⟩ := exists_pos_l2_slice_contraction_lt hT f D hD1
  let δ := min η 1
  let ε := (1 - (C : ℝ)) / 8
  let q := (3 + (C : ℝ)) / 4
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hq : q ∈ Ico (0 : ℝ) 1 := by
    have hC0 := C.coe_nonneg
    dsimp only [q]
    constructor <;> linarith
  refine ⟨δ, lt_min hη zero_lt_one, (min_le_left _ _).trans hηT,
    ε, hε, q, hq, ?_⟩
  intro g hg a b ha hbT hd hdδ
  have hdη : b - a ≤ η := hdδ.trans (min_le_left _ _)
  have hd1 : b - a ≤ 1 := hdδ.trans (min_le_right _ _)
  have hbase := hsmall a b ha hbT hd hdη
  have hsub : Icc a b ⊆ Icc (0 : ℝ) T :=
    fun _ ht => ⟨ha.trans ht.1, ht.2.trans hbT⟩
  have hrestrict : volume.restrict (Icc a b) ≤ timeMeasure T :=
    Measure.restrict_mono hsub le_rfl
  have hnorm : ‖timeL2.slice (g - f) a b ha hbT‖ ≤ ‖g - f‖ := by
    rw [timeL2.norm_slice_eq, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.memLp (g - f)).2.ne
      (eLpNorm_mono_measure (g - f) hrestrict)
  have hsplit : timeL2.slice g a b ha hbT =
      timeL2.slice f a b ha hbT + timeL2.slice (g - f) a b ha hbT := by
    rw [← timeL2.slice_add, add_sub_cancel]
  have hgnorm : ‖timeL2.slice g a b ha hbT‖ ≤
      ‖timeL2.slice f a b ha hbT‖ + ‖g - f‖ := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hnorm)
  have hsqrt : Real.sqrt (1 + (b - a)) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> linarith
  have hmul : Real.sqrt (1 + (b - a)) * ‖timeL2.slice g a b ha hbT‖ ≤
      Real.sqrt (1 + (b - a)) *
        (‖timeL2.slice f a b ha hbT‖ + ‖g - f‖) :=
    mul_le_mul_of_nonneg_left hgnorm (Real.sqrt_nonneg _)
  have herror : Real.sqrt (1 + (b - a)) * ‖g - f‖ ≤ 2 * ‖g - f‖ :=
    mul_le_mul_of_nonneg_right hsqrt (norm_nonneg (g - f))
  have hgap : 0 ≤ (1 - (C : ℝ)) * (b - a) := by
    exact mul_nonneg (sub_pos.mpr hC).le hd
  rw [hD] at hbase
  dsimp only [ε] at hg
  dsimp only [q]
  nlinarith [hbase, hmul, herror]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
