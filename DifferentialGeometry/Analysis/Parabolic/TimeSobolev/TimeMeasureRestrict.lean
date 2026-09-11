import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem timeMeasure_restrict_Icc_eq_volume_restrict_Icc
    {T t₀ t₁ : ℝ} (hI : Icc t₀ t₁ ⊆ Icc (0 : ℝ) T) :
    (timeMeasure T).restrict (Icc t₀ t₁) = volume.restrict (Icc t₀ t₁) := by
  exact Measure.restrict_restrict_of_subset hI

theorem measurePreserving_add_right_timeMeasure_restrict
    {T t₀ t₁ : ℝ} (hI : Icc t₀ t₁ ⊆ Icc (0 : ℝ) T) :
    MeasurePreserving (fun s : ℝ => t₀ + s) (timeMeasure (t₁ - t₀))
      ((timeMeasure T).restrict (Icc t₀ t₁)) := by
  rw [timeMeasure_restrict_Icc_eq_volume_restrict_Icc hI]
  have h := (measurePreserving_add_right volume t₀).restrict_image_emb
    (Homeomorph.addRight t₀).isClosedEmbedding.measurableEmbedding
      (Icc (0 : ℝ) (t₁ - t₀))
  simpa only [timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel, add_comm t₀] using h

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
