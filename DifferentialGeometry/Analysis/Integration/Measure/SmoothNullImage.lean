import DifferentialGeometry.Analysis.Calculus.Compactness.Lipschitz
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

section

noncomputable section
open Set MeasureTheory
open scoped MeasureTheory NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem volume_image_eq_zero_of_lipschitzOn {f : E → E} {K : ℝ≥0} {s : Set E}
    (hf : LipschitzOnWith K f s) (hs : volume s = 0) : volume (f '' s) = 0 := by
  let H : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have hHv : H ≪ volume := Measure.absolutelyContinuous_isAddHaarMeasure H volume
  have hvH : volume ≪ H := Measure.absolutelyContinuous_isAddHaarMeasure volume H
  apply hvH
  have hh := hf.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (Nat.cast_nonneg _)
  change H (f '' s) ≤ _ at hh
  rw [show H s = 0 from hHv hs, mul_zero] at hh
  exact le_zero_iff.mp hh

theorem volume_image_compact_eq_zero_of_contDiffOn
    {f : E → E} {Ω K : Set E} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hnull : volume K = 0) : volume (f '' K) = 0 := by
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith_of_isCompact hΩ hK hKΩ
  exact volume_image_eq_zero_of_lipschitzOn hL hnull

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set MeasureTheory

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem volume_image_sphere_eq_zero_of_contDiffOn
    {W : E → E} {Ω : Set E} (hΩ : IsOpen Ω) (hW : ContDiffOn ℝ 1 W Ω)
    (c : E) (R : ℝ) (hsub : Metric.sphere c R ⊆ Ω) :
    volume (W '' Metric.sphere c R) = 0 :=
  volume_image_compact_eq_zero_of_contDiffOn hΩ hW (isCompact_sphere c R) hsub
    (Measure.addHaar_sphere volume c R)

theorem volume_image_subset_sphere_eq_zero_of_contDiffOn
    {W : E → E} {Ω : Set E} (hΩ : IsOpen Ω) (hW : ContDiffOn ℝ 1 W Ω)
    (c : E) (R : ℝ) (hsub : Metric.sphere c R ⊆ Ω) {S : Set E}
    (hS : S ⊆ Metric.sphere c R) : volume (W '' S) = 0 :=
  measure_mono_null (image_mono hS) (volume_image_sphere_eq_zero_of_contDiffOn hΩ hW c R hsub)

end DifferentialGeometry.Analysis

end

end
