import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

theorem exists_cover_by_positive_radii_of_hausdorffMeasure_zero
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {s : ℝ} (hs : 0 < s) {A : Set Y} (hzero : hausdorffMeasure s A = 0)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ U : ℕ → Set Y, ∃ r : ℕ → ℝ,
      A ⊆ ⋃ i, U i ∧
      (∀ i, 0 < r i ∧ r i ≤ δ ∧ ediam (U i) ≤ ENNReal.ofReal (r i)) ∧
      (∑' i, (ENNReal.ofReal (r i)) ^ s) ≤ ENNReal.ofReal ε := by
  have hhalf : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (half_pos hε)
  have hcontent : (⨅ (U : ℕ → Set Y) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, ediam (U i) ≤ ENNReal.ofReal δ),
      ∑' i, ⨆ _ : (U i).Nonempty, ediam (U i) ^ s) < ENNReal.ofReal (ε / 2) := by
    have hle := le_iSup₂ (f := fun (r : ENNReal) (_ : 0 < r) =>
      ⨅ (U : ℕ → Set Y) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, ediam (U i) ^ s)
      (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
    rw [← hausdorffMeasure_apply, hzero] at hle
    exact hle.trans_lt hhalf
  obtain ⟨U, hcover, hdiam, hsum⟩ := (by simpa only [iInf_lt_iff] using hcontent)
  have hsum' : (∑' i, ediam (U i) ^ s) < ENNReal.ofReal (ε / 2) := by
    convert hsum using 1
    apply tsum_congr
    intro i
    by_cases hi : (U i).Nonempty
    · simp only [iSup_pos hi]
    · simp [Set.not_nonempty_iff_eq_empty.mp hi, hs]
  obtain ⟨b, hb, hbsum⟩ := ENNReal.exists_pos_sum_of_countable hhalf.ne' ℕ
  let ρ : ℕ → ENNReal := fun i =>
    max (ediam (U i)) (min (ENNReal.ofReal δ) ((b i : ENNReal) ^ s⁻¹))
  have hρle (i : ℕ) : ρ i ≤ ENNReal.ofReal δ :=
    max_le (hdiam i) (min_le_left _ _)
  have hρfinite (i : ℕ) : ρ i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hρle i)
  have hρpos (i : ℕ) : 0 < ρ i :=
    (lt_min (ENNReal.ofReal_pos.mpr hδ)
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr (hb i)) ENNReal.coe_ne_top)).trans_le
        (le_max_right _ _)
  have hρpow (i : ℕ) : (ρ i) ^ s ≤ ediam (U i) ^ s + (b i : ENNReal) := by
    dsimp only [ρ]
    rw [ENNReal.max_rpow hs.le]
    refine max_le (le_add_right le_rfl) ?_
    have h := ENNReal.rpow_le_rpow (min_le_right (ENNReal.ofReal δ)
      ((b i : ENNReal) ^ s⁻¹)) hs.le
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hs.ne', ENNReal.rpow_one] at h
    exact h.trans (le_add_left le_rfl)
  refine ⟨U, fun i => (ρ i).toReal, hcover, ?_, ?_⟩
  · intro i
    refine ⟨ENNReal.toReal_pos (hρpos i).ne' (hρfinite i), ?_, ?_⟩
    · exact (ENNReal.toReal_le_toReal (hρfinite i) ENNReal.ofReal_ne_top).mpr
        (hρle i) |>.trans (ENNReal.toReal_ofReal hδ.le).le
    · rw [ENNReal.ofReal_toReal (hρfinite i)]
      exact le_max_left _ _
  · simp only [ENNReal.ofReal_toReal (hρfinite _)]
    calc
      (∑' i, ρ i ^ s) ≤ ∑' i, (ediam (U i) ^ s + (b i : ENNReal)) :=
        ENNReal.tsum_le_tsum hρpow
      _ = (∑' i, ediam (U i) ^ s) + ∑' i, (b i : ENNReal) := ENNReal.tsum_add
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        add_le_add hsum'.le hbsum.le
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
        congr 1
        ring

end MeasureTheory.Measure
