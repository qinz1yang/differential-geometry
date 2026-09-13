/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Codex
-/
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Function MeasureTheory.Measure Set

namespace MeasureTheory

theorem addHaar_image_eq_zero_of_not_surjective_fderivWithin
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {s : Set E} {f : E → F} {f' : E → E →L[ℝ] F}
    (ν : Measure F) [IsAddHaarMeasure ν]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hcrit : ∀ x ∈ s, ¬ Surjective (f' x)) : ν (f '' s) = 0 := by
  borelize E
  let e : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim.symm
  let g : E → E := fun x => e (f x)
  let g' : E → E →L[ℝ] E := fun x => (e : F →L[ℝ] E).comp (f' x)
  have hg' : ∀ x ∈ s, HasFDerivWithinAt g (g' x) s x := by
    intro x hx
    exact e.hasFDerivAt.comp_hasFDerivWithinAt x (hf' x hx)
  have hdet : ∀ x ∈ s, (g' x).det = 0 := by
    intro x hx
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    intro hinj
    apply hcrit x hx
    intro y
    obtain ⟨z, hz⟩ := LinearMap.injective_iff_surjective.mp hinj (e y)
    refine ⟨z, e.injective ?_⟩
    simpa only [g', ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using hz
  have hnull : (addHaar : Measure E) (g '' s) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero addHaar hg' hdet
  have hqm : QuasiMeasurePreserving e ν (addHaar : Measure E) :=
    ⟨e.continuous.measurable, absolutelyContinuous_isAddHaarMeasure (ν.map e) addHaar⟩
  have hpreimage : ν (e ⁻¹' (g '' s)) = 0 := hqm.preimage_null hnull
  have himage : g '' s = e '' (f '' s) := by rw [image_image]
  rw [himage, Set.preimage_image_eq _ e.injective] at hpreimage
  exact hpreimage

end MeasureTheory
