import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff









noncomputable section

open MeasureTheory Set Filter
open scoped NNReal Topology ENNReal MeasureTheory

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]



theorem volume_image_eq_zero_of_lipschitz {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set E} (hs : volume s = 0) :
    volume (f '' s) = 0 := by
  let H : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have hHv : H ≪ volume := Measure.absolutelyContinuous_isAddHaarMeasure H volume
  have hvH : volume ≪ H := Measure.absolutelyContinuous_isAddHaarMeasure volume H
  apply hvH
  have h := hf.hausdorffMeasure_image_le
    (d := (Module.finrank ℝ E : ℝ)) (Nat.cast_nonneg _) s
  have hzero : H s = 0 := hHv hs
  change H (f '' s) ≤ _ at h
  rw [hzero, mul_zero] at h
  exact le_zero_iff.mp h




theorem ae_comp_of_lipschitz_leftInverse_on {f k : E → E} {K : ℝ≥0}
    (hk : LipschitzWith K k) {s : Set E} (hki : ∀ x ∈ s, k (f x) = x)
    {P : E → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ x ∂volume, x ∈ s → P (f x) := by
  have hz := volume_image_eq_zero_of_lipschitz hk (ae_iff.mp hP)
  have ha : ∀ᵐ x ∂volume, x ∉ k '' {y | ¬ P y} := by
    apply ae_iff.mpr
    convert hz using 1
    congr 1
    ext x
    simp
  filter_upwards [ha] with x hx
  intro hxs
  by_contra hp
  exact hx ⟨f x, hp, hki x hxs⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem integral_image_eq_integral_abs_det_of_lipschitz {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set E} (hs : MeasurableSet s) (hi : InjOn f s)
    (g : E → F) :
    ∫ x in f '' s, g x =
      ∫ x in s, |(fderiv ℝ f x).toLinearMap.det| • g (f x) := by
  let t : Set E := s ∩ {x | DifferentiableAt ℝ f x}
  have ht : MeasurableSet t := hs.inter (measurableSet_of_differentiableAt ℝ f)
  have hts : t =ᵐ[volume] s := by
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
    apply propext
    change (x ∈ s ∧ DifferentiableAt ℝ f x) ↔ x ∈ s
    exact and_iff_left hx
  have hnull : volume (s \ t) = 0 := by
    apply measure_mono_null (show s \ t ⊆ {x | ¬ DifferentiableAt ℝ f x} from
      fun x hx hd => hx.2 ⟨hx.1, hd⟩)
    exact ae_iff.mp (hf.ae_differentiableAt (μ := volume))
  have himage : f '' t =ᵐ[volume] f '' s := by
    have hz := volume_image_eq_zero_of_lipschitz hf hnull
    have he : volume (f '' s \ f '' t) = 0 := measure_mono_null
      (by
        rintro x ⟨⟨y, hy, rfl⟩, hxt⟩
        exact ⟨y, ⟨hy, fun hyt => hxt ⟨y, hyt, rfl⟩⟩, rfl⟩) hz
    have ha : ∀ᵐ x ∂volume, x ∉ f '' s \ f '' t := by
      apply ae_iff.mpr
      convert he using 1
      congr 1
      ext x
      simp only [mem_ofPred_eq, not_not]
    filter_upwards [ha] with x hx
    apply propext
    change x ∈ f '' t ↔ x ∈ f '' s
    exact ⟨fun hxt => image_mono (show t ⊆ s from inter_subset_left) hxt, fun hxs =>
      not_not.mp (fun hxt => hx ⟨hxs, hxt⟩)⟩
  rw [← setIntegral_congr_set himage, ← setIntegral_congr_set hts]
  exact integral_image_eq_integral_abs_det_fderiv_smul volume ht
    (fun x hx => hx.2.hasFDerivAt.hasFDerivWithinAt) (hi.mono inter_subset_left) g

end DifferentialGeometry.Analysis
